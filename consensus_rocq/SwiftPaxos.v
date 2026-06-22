(** * SwiftPaxos fast-path adopt-commit analysis

    Scope.  This file will model one command/value in one stable ballot.  It
    deliberately omits dependency graphs, execution, the ordinary Paxos slow
    quorum, ballot changes, and recovery.  The paper's FastAck/SlowAck names
    are represented here as ordinary and leader-choice acknowledgements.

    Differences from FastPaxos.v:
    - SwiftPaxos has a distinguished leader and every direct fast quorum
      contains it.  Agreement should therefore use the leader's immutable
      first accepted value, rather than only a generic quorum-intersection
      argument.
    - There are two explicit direct-quorum configurations.  C1 accepts any
      duplicate-free valid set containing the leader with
      [4 * length Q > 3 * n].  C2 accepts only one predetermined,
      duplicate-free valid quorum of size [f + 1] containing the leader.
    - A replica may replace its tentative ordinary vote after receiving the
      leader's forwarded value.  Thus tentative acceptance is not globally
      stable as it is in FastPaxos.
    - Acknowledgements have two distinct meanings: an ordinary vote and a
      leader-choice vote.  The latter records knowledge that the value came
      from the leader.
    - A commit certificate is disjunctive: either ordinary acknowledgements
      cover a direct C1/C2 quorum, or [f + 1] distinct leader-choice
      acknowledgements have been collected.

    Differences from EPaxos.v:
    - The leader is fixed for the modeled ballot rather than being the
      proposer/owner of each command.
    - Commit is not restricted to the value's proposer process.
    - The proof does not rely on EPaxos's proposer-specific quorum
      intersection.  Direct agreement is anchored by the leader member, and
      leader-choice acknowledgements are anchored by knowledge of that same
      leader value.

    State/evidence plan:
    - Local state records a tentative/current accepted value, optional
      knowledge of the leader's choice, persistent histories of ordinary and
      leader-choice acknowledgements sent, the two received certificate
      lists, and an optional output.
    - The leader accepts the first proposal it processes, records it as its
      immutable choice, sends an ordinary acknowledgement, and forwards the
      choice to all replicas.
    - A nonleader may ordinarily acknowledge its tentative value.  On a
      leader-forward message it overrides that tentative value, records the
      leader choice, and sends a distinct leader-choice acknowledgement.
    - Persistent sent-ack histories are required by Recoverability: equal
      survivor local states must expose the evidence used by certificates
      even after a tentative value was overridden.

    Arithmetic/model assumptions justified by Section 2 of the paper:
    [n = 2*f+1] and [0 < f].  The fixed C2 quorum has exactly [f+1]
    members.  Small cases to audit before counting lemmas are:
      f=1, n=3: C1 minimum 3; C2/leader-choice size 2.
      f=2, n=5: C1 minimum 4; C2/leader-choice size 3.
      f=3, n=7: C1 minimum 6; C2/leader-choice size 4.
      f=4, n=9: C1 minimum 7; C2/leader-choice size 5.
    These checks show every certificate has more than [f] members.  For C1,
    two direct quorums have intersection larger than [f] in these cases;
    for C2, both direct certificates use the same fixed quorum.  These facts
    are intended for cross-state Recoverability only, while same-state
    Agreement is based on the SwiftPaxos leader facts above.
*)

From Stdlib Require Import List Arith Bool Classical ClassicalDescription Lia.
Import ListNotations.

Require Import AdoptCommit.

(* ================================================================
   Messages, certificates, and local state
   ================================================================ *)

Inductive SPConfig :=
  | C1
  | C2.

Inductive SPAckKind :=
  | OrdinaryAck
  | LeaderChoiceAck.

Inductive SPMsg :=
  | SPProposal : ProcessId -> SPMsg
  | SPLeaderForward : ProcessId -> SPMsg
  | SPAck : ProcessId -> ProcessId -> SPAckKind -> SPMsg.

Record SPState := mkSPState {
  sp_accepted      : option ProcessId;
  sp_leader_choice : option ProcessId;
  sp_sent_ordinary : option ProcessId;
  sp_sent_leader   : option ProcessId;
  sp_ordinary_acks : list ProcessId;
  sp_leader_acks   : list ProcessId;
  sp_output        : option ACOutput;
}.

Section SP.

Variable n : nat.
Hypothesis n_pos : 0 < n.
Variable f : nat.
Hypothesis f_lt_n : f < n.

(** SwiftPaxos Section 2 assumes [N = 2f+1].  Positive [f] excludes
    the degenerate one-replica case from the quorum arithmetic. *)
Hypothesis sp_n_eq : n = 2 * f + 1.
Hypothesis sp_f_pos : 0 < f.

Variable leader : ProcessId.
Hypothesis sp_leader_valid : leader < n.

Variable is_proposer : ProcessId -> Prop.
Hypothesis exists_proposer : exists p, p < n /\ is_proposer p.
(** Process identifiers stand for command proposers in this abstraction;
    the distinguished replica leader is not itself a command proposer. *)
Hypothesis sp_leader_not_proposer : ~ is_proposer leader.

Variable config : SPConfig.
Variable c2_quorum : list ProcessId.
Hypothesis sp_c2_nodup : NoDup c2_quorum.
Hypothesis sp_c2_valid :
  forall p, In p c2_quorum -> p < n.
Hypothesis sp_c2_size : length c2_quorum = f + 1.
Hypothesis sp_c2_has_leader : In leader c2_quorum.

Definition sp_C1_fast_quorum (Q : list ProcessId) : Prop :=
  NoDup Q /\
  (forall p, In p Q -> p < n) /\
  In leader Q /\
  3 * n < 4 * length Q.

Definition sp_C2_fast_quorum (Q : list ProcessId) : Prop :=
  Q = c2_quorum.

Definition sp_direct_fast_quorum (Q : list ProcessId) : Prop :=
  match config with
  | C1 => sp_C1_fast_quorum Q
  | C2 => sp_C2_fast_quorum Q
  end.

Definition sp_leader_certificate (Q : list ProcessId) : Prop :=
  NoDup Q /\
  (forall p, In p Q -> p < n) /\
  f + 1 <= length Q.

Definition sp_direct_certificate (A : list ProcessId) : Prop :=
  exists Q,
    sp_direct_fast_quorum Q /\
    incl Q A.

Definition sp_add (p : ProcessId) (xs : list ProcessId) : list ProcessId :=
  if existsb (Nat.eqb p) xs then xs else p :: xs.

Definition sp_record_choice
    (v : ProcessId) (old : option ProcessId) : option ProcessId :=
  match old with
  | Some w => Some w
  | None => Some v
  end.

Definition sp_maybe_commit (ls : SPState) : option ACOutput :=
  match sp_accepted ls with
  | None => None
  | Some v =>
      if excluded_middle_informative
           (is_proposer v /\
            sp_leader_choice ls = Some v /\
            (sp_direct_certificate (sp_ordinary_acks ls) \/
             sp_leader_certificate (sp_leader_acks ls)))
      then Some (Commit v)
      else None
  end.

Definition sp_step_fn
    (p : ProcessId) (ls : SPState) (m : SPMsg)
    : SPState * (ProcessId -> list SPMsg) :=
  match sp_output ls with
  | Some _ => (ls, fun _ => [])
  | None =>
      match m with
      | SPProposal v =>
          if Nat.eqb p leader then
            match sp_leader_choice ls with
            | Some _ => (ls, fun _ => [])
            | None =>
                let ls' :=
                  mkSPState (Some v) (Some v)
                    (sp_record_choice v (sp_sent_ordinary ls))
                    (sp_sent_leader ls)
                    [] [] None in
                (ls',
                 fun dst =>
                   if Nat.eqb dst v
                   then [SPAck leader v OrdinaryAck; SPLeaderForward v]
                   else [SPLeaderForward v])
            end
          else
            match sp_accepted ls with
            | Some _ => (ls, fun _ => [])
            | None =>
                (mkSPState (Some v) (sp_leader_choice ls)
                   (sp_record_choice v (sp_sent_ordinary ls))
                   (sp_sent_leader ls)
                   [] [] None,
                 fun dst =>
                   if Nat.eqb dst v
                   then [SPAck p v OrdinaryAck]
                   else [])
            end
      | SPLeaderForward v =>
          if Nat.eqb p leader then (ls, fun _ => [])
          else
            match sp_leader_choice ls with
            | Some _ => (ls, fun _ => [])
            | None =>
                let base :=
                  mkSPState (Some v) (Some v)
                    (sp_sent_ordinary ls)
                    (sp_record_choice v (sp_sent_leader ls))
                    [] [] None in
                (base,
                 fun dst =>
                   if Nat.eqb dst v
                   then [SPAck p v LeaderChoiceAck]
                   else [])
            end
      | SPAck src v kind =>
          match sp_accepted ls with
          | Some w =>
              if Nat.eqb v w then
                let base :=
                  match kind with
                  | OrdinaryAck =>
                      mkSPState (Some w)
                        (if Nat.eqb src leader
                         then sp_record_choice w (sp_leader_choice ls)
                         else sp_leader_choice ls)
                        (sp_sent_ordinary ls) (sp_sent_leader ls)
                        (sp_add src (sp_ordinary_acks ls))
                        (sp_leader_acks ls) None
                  | LeaderChoiceAck =>
                      mkSPState (Some w)
                        (sp_record_choice w (sp_leader_choice ls))
                        (sp_sent_ordinary ls) (sp_sent_leader ls)
                        (sp_ordinary_acks ls)
                        (sp_add src (sp_leader_acks ls)) None
                  end in
                (mkSPState (sp_accepted base) (sp_leader_choice base)
                   (sp_sent_ordinary base) (sp_sent_leader base)
                   (sp_ordinary_acks base) (sp_leader_acks base)
                   (sp_maybe_commit base),
                 fun _ => [])
              else (ls, fun _ => [])
          | None => (ls, fun _ => [])
          end
      end
  end.

Definition sp_init (s : GlobalState SPMsg SPState) : Prop :=
  (forall p, sp_output (local s p) = None) /\
  (forall p, sp_leader_choice (local s p) = None) /\
  (forall p,
      if excluded_middle_informative (p < n /\ is_proposer p)
      then sp_accepted (local s p) = Some p /\
           sp_sent_ordinary (local s p) = Some p /\
           sp_ordinary_acks (local s p) = [p]
      else sp_accepted (local s p) = None /\
           sp_sent_ordinary (local s p) = None /\
           sp_ordinary_acks (local s p) = []) /\
  (forall p, sp_sent_leader (local s p) = None) /\
  (forall p, sp_leader_acks (local s p) = []) /\
  ((forall src dst,
      src < n -> dst < n -> src <> dst -> is_proposer src ->
      network s src dst = [SPProposal src]) /\
   (forall src dst,
      ~ (src < n /\ dst < n /\ src <> dst /\ is_proposer src) ->
      network s src dst = [])).

Definition sp_instance : ACProtocol :=
  mkACProtocol sp_output is_proposer sp_init sp_step_fn.

Definition SP_GlobalState := GlobalState SPMsg SPState.
Definition SP_Reachable := Reachable n sp_instance.

(* ================================================================
   Proofs
   ================================================================ *)

Lemma sp_output_stable :
  forall p ls m o,
    sp_output ls = Some o ->
    sp_output (fst (sp_step_fn p ls m)) = Some o.
Proof.
  intros p ls m o Hout.
  unfold sp_step_fn. rewrite Hout. simpl. exact Hout.
Qed.

Lemma sp_output_facts :
  forall s,
    SP_Reachable s ->
    forall p o,
      sp_output (local s p) = Some o ->
      exists v,
        o = Commit v /\
        is_proposer v /\
        sp_accepted (local s p) = Some v /\
        sp_leader_choice (local s p) = Some v /\
        (sp_direct_certificate (sp_ordinary_acks (local s p)) \/
         sp_leader_certificate (sp_leader_acks (local s p))).
Proof.
  intros s Hreach.
  induction Hreach as [s Hinit | recv src s s' Hreach IH Hstep].
  - unfold sp_init in Hinit. destruct Hinit as [Hnone _].
    intros p o Hout. rewrite (Hnone p) in Hout. discriminate.
  - unfold step, sp_instance in Hstep; simpl in Hstep.
    destruct Hstep as [[_ [_ Hrecv]] Hstep].
    destruct (network s src recv) as [|m rest] eqn:Hqueue.
    + unfold state_eq in Hstep. destruct Hstep as [Hlocal _].
      intros p o Hout. rewrite Hlocal in Hout.
      rewrite Hlocal. exact (IH p o Hout).
    + destruct Hstep as [[Hstate Hothers] _].
      intros p o Hout.
      destruct (classic (p = recv)) as [-> | Hneq].
      * rewrite Hstate in Hout.
        destruct (sp_output (local s recv)) as [old|] eqn:Hprev.
        -- unfold sp_step_fn in Hout. rewrite Hprev in Hout. simpl in Hout.
           rewrite Hstate. unfold sp_step_fn. rewrite Hprev. simpl.
           exact (IH recv o Hout).
        -- unfold sp_step_fn in Hout. rewrite Hprev in Hout.
           destruct m as [v | v | ack_src v kind].
           ++ destruct (recv =? leader); simpl in Hout.
              ** destruct (sp_leader_choice (local s recv)); simpl in Hout.
                 --- rewrite Hprev in Hout. discriminate.
                 --- discriminate.
              ** destruct (sp_accepted (local s recv)); simpl in Hout.
                 --- rewrite Hprev in Hout. discriminate.
                 --- discriminate.
           ++ destruct (recv =? leader); simpl in Hout.
              ** rewrite Hprev in Hout. discriminate.
              ** destruct (sp_leader_choice (local s recv)); simpl in Hout.
                 --- rewrite Hprev in Hout. discriminate.
                 --- discriminate.
           ++ destruct (sp_accepted (local s recv)) as [w|] eqn:Hacc.
              ** destruct (v =? w) eqn:Heq.
                 --- apply Nat.eqb_eq in Heq. subst v.
                     destruct kind; simpl in Hout.
                     +++ destruct (ack_src =? leader) eqn:Hsrc.
                         { simpl in Hout.
                           unfold sp_maybe_commit in Hout; simpl in Hout.
                           destruct (excluded_middle_informative _)
                             as [Hfacts | Hfacts].
                           { simpl in Hout. injection Hout as Ho. subst o.
                             rewrite Hstate. unfold sp_step_fn.
                             rewrite Hprev, Hacc, Nat.eqb_refl. simpl.
                             rewrite Hsrc. simpl.
                             exists w; intuition. }
                           { simpl in Hout. discriminate. } }
                         { simpl in Hout.
                           unfold sp_maybe_commit in Hout; simpl in Hout.
                           destruct (excluded_middle_informative _)
                             as [Hfacts | Hfacts].
                           { simpl in Hout. injection Hout as Ho. subst o.
                             rewrite Hstate. unfold sp_step_fn.
                             rewrite Hprev, Hacc, Nat.eqb_refl. simpl.
                             rewrite Hsrc. simpl.
                             exists w; intuition. }
                           { simpl in Hout. discriminate. } }
                     +++ unfold sp_maybe_commit in Hout; simpl in Hout.
                         destruct (excluded_middle_informative _)
                           as [Hfacts | Hfacts].
                         { simpl in Hout. injection Hout as Ho. subst o.
                           rewrite Hstate. unfold sp_step_fn.
                           rewrite Hprev, Hacc, Nat.eqb_refl. simpl.
                           exists w; intuition. }
                         { simpl in Hout. discriminate. }
                 --- simpl in Hout. rewrite Hprev in Hout. discriminate.
              ** simpl in Hout. congruence.
      * rewrite (Hothers p Hneq) in Hout.
        rewrite (Hothers p Hneq).
        exact (IH p o Hout).
Qed.

Theorem SwiftPaxos_Validity : Validity n sp_instance.
Proof.
  unfold Validity, sp_instance, output_of, valid_pid; simpl.
  intros s p v Hreach Hp [Hout | Hout].
  - destruct (sp_output_facts s Hreach p (Commit v) Hout)
      as [w [Heq [Hvalid _]]].
    injection Heq as Heq. subst w. exact Hvalid.
  - destruct (sp_output_facts s Hreach p (Adopt v) Hout)
      as [w [Heq _]].
    discriminate.
Qed.

Theorem SwiftPaxos_Convergence : Convergence n sp_instance.
Proof.
  unfold Convergence, sp_instance, output_of, valid_pid; simpl.
  intros s p q o Hreach Hp Hq Hprop Hunique Hout.
  destruct (sp_output_facts s Hreach q o Hout)
    as [v [Ho [Hvalid _]]].
  subst o. f_equal. apply Hunique. exact Hvalid.
Qed.

Definition sp_choice_msg_ok (lc : option ProcessId) (m : SPMsg) : Prop :=
  match m with
  | SPProposal _ => True
  | SPLeaderForward v => lc = Some v
  | SPAck src v OrdinaryAck => src = leader -> lc = Some v
  | SPAck _ v LeaderChoiceAck => lc = Some v
  end.

Definition sp_choice_invariant (s : SP_GlobalState) : Prop :=
  (forall p v,
      sp_leader_choice (local s p) = Some v ->
      sp_leader_choice (local s leader) = Some v) /\
  (forall src dst,
      Forall
        (sp_choice_msg_ok (sp_leader_choice (local s leader)))
        (network s src dst)).

Lemma sp_choice_msg_monotone :
  forall old new m,
    (old = None \/ new = old) ->
    sp_choice_msg_ok old m ->
    sp_choice_msg_ok new m.
Proof.
  intros old new m Hmono Hok.
  destruct Hmono as [-> | ->]; [|exact Hok].
  destruct m as [v | v | src v kind]; simpl in *; auto.
  - discriminate.
  - destruct kind; simpl in *.
    + intros Hsrc. specialize (Hok Hsrc). discriminate.
    + discriminate.
Qed.

Lemma sp_local_choice_monotone :
  forall p ls m,
    sp_leader_choice ls = None \/
    sp_leader_choice (fst (sp_step_fn p ls m)) =
      sp_leader_choice ls.
Proof.
  intros p ls m.
  unfold sp_step_fn.
  destruct (sp_output ls) eqn:Hout; simpl; [right; reflexivity |].
  destruct m as [v | v | src v kind].
  - destruct (p =? leader); simpl.
    + destruct (sp_leader_choice ls) eqn:Hchoice; simpl.
      * right. exact Hchoice.
      * left. reflexivity.
    + destruct (sp_accepted ls); simpl; right; reflexivity.
  - destruct (p =? leader); simpl.
    + right. reflexivity.
    + destruct (sp_leader_choice ls) eqn:Hchoice; simpl.
      * right. exact Hchoice.
      * left. reflexivity.
  - destruct (sp_accepted ls) as [w|]; simpl.
    + destruct (v =? w); simpl.
      * destruct kind; simpl.
        -- destruct (src =? leader); simpl.
           ++ unfold sp_record_choice.
              destruct (sp_leader_choice ls) eqn:Hchoice; simpl.
               ** right. reflexivity.
              ** left. reflexivity.
           ++ right. reflexivity.
        -- unfold sp_record_choice.
           destruct (sp_leader_choice ls) eqn:Hchoice; simpl.
           ++ right. reflexivity.
           ++ left. reflexivity.
      * right. reflexivity.
    + right. reflexivity.
Qed.

Lemma sp_step_choice_anchor :
  forall lc p ls m,
    (forall v, sp_leader_choice ls = Some v -> lc = Some v) ->
    sp_choice_msg_ok lc m ->
    forall v,
      sp_leader_choice (fst (sp_step_fn p ls m)) = Some v ->
      (if Nat.eqb p leader
       then sp_leader_choice (fst (sp_step_fn p ls m))
       else lc) = Some v.
Proof.
  intros lc p ls m Hanchor Hmsg v Hnew.
  destruct (Nat.eqb p leader) eqn:Hp.
  - exact Hnew.
  - unfold sp_step_fn in Hnew.
    destruct (sp_output ls) eqn:Hout; simpl in Hnew.
    + exact (Hanchor v Hnew).
    + destruct m as [x | x | src x kind].
      * rewrite Hp in Hnew. simpl in Hnew.
        destruct (sp_accepted ls); simpl in Hnew;
          exact (Hanchor v Hnew).
      * rewrite Hp in Hnew. simpl in Hnew.
        destruct (sp_leader_choice ls) eqn:Hchoice; simpl in Hnew.
        -- rewrite Hchoice in Hnew. exact (Hanchor v Hnew).
        -- injection Hnew as ->. exact Hmsg.
      * destruct (sp_accepted ls) as [w|] eqn:Hacc; simpl in Hnew.
        -- destruct (x =? w) eqn:Hx; simpl in Hnew.
           ++ apply Nat.eqb_eq in Hx. subst x.
              destruct kind; simpl in Hnew.
              ** destruct (src =? leader) eqn:Hsrc; simpl in Hnew.
                 --- unfold sp_record_choice in Hnew.
                     destruct (sp_leader_choice ls) eqn:Hchoice;
                       simpl in Hnew.
                     +++ exact (Hanchor v Hnew).
                     +++ injection Hnew as ->.
                         apply Nat.eqb_eq in Hsrc. subst src.
                         exact (Hmsg eq_refl).
                 --- exact (Hanchor v Hnew).
              ** unfold sp_record_choice in Hnew.
                 destruct (sp_leader_choice ls) eqn:Hchoice;
                   simpl in Hnew.
                 --- exact (Hanchor v Hnew).
                 --- injection Hnew as ->. exact Hmsg.
           ++ exact (Hanchor v Hnew).
        -- exact (Hanchor v Hnew).
Qed.

Lemma sp_step_new_messages_ok :
  forall lc p ls m,
    sp_choice_msg_ok lc m ->
    forall dst,
      Forall
        (sp_choice_msg_ok
           (if Nat.eqb p leader
            then sp_leader_choice (fst (sp_step_fn p ls m))
            else lc))
        (snd (sp_step_fn p ls m) dst).
Proof.
  intros lc p ls m Hmsg dst.
  unfold sp_step_fn.
  destruct (sp_output ls); simpl.
  - constructor.
  - destruct m as [v | v | src v kind].
    + destruct (p =? leader) eqn:Hp; simpl.
      * destruct (sp_leader_choice ls); simpl; [constructor |].
      destruct (dst =? v); simpl; repeat constructor; simpl; auto.
      * destruct (sp_accepted ls); simpl; [constructor |].
      destruct (dst =? v); simpl; [|constructor].
      constructor; [|constructor]. simpl.
      intro Heq. apply Nat.eqb_neq in Hp. contradiction.
    + destruct (p =? leader) eqn:Hp; simpl; [constructor |].
      destruct (sp_leader_choice ls); simpl; [constructor |].
      destruct (dst =? v); simpl; [|constructor].
      constructor; [exact Hmsg | constructor].
    + destruct (sp_accepted ls); simpl; [|constructor].
      destruct (v =? p0); simpl; constructor.
Qed.

Lemma sp_choice_invariant_reachable :
  forall s,
    SP_Reachable s ->
    sp_choice_invariant s.
Proof.
  intros s Hreach.
  induction Hreach as [s Hinit | recv src s s' Hreach IH Hstep].
  - unfold sp_choice_invariant, sp_init in *.
    destruct Hinit as [_ [Hchoices [_ [_ [_ [Hpropnet Hemptynet]]]]]].
    split.
    + intros p v Hchoice. rewrite (Hchoices p) in Hchoice. discriminate.
    + intros src dst.
      destruct (classic
        (src < n /\ dst < n /\ src <> dst /\ is_proposer src))
        as [[Hsrc [Hdst [Hneq Hprop]]] | Hnone].
      * rewrite (Hpropnet src dst Hsrc Hdst Hneq Hprop).
        constructor; simpl; constructor.
      * rewrite (Hemptynet src dst Hnone). constructor.
  - unfold sp_choice_invariant in IH.
    destruct IH as [Hlocal_inv Hnetwork_inv].
    unfold step, sp_instance in Hstep; simpl in Hstep.
    destruct Hstep as [[Hneq [Hsrc Hrecv]] Hstep].
    destruct (network s src recv) as [|m rest] eqn:Hqueue.
    + unfold state_eq in Hstep. destruct Hstep as [Hlocal Hnetwork].
      split.
      * intros p v Hchoice. rewrite Hlocal in Hchoice.
        rewrite Hlocal. exact (Hlocal_inv p v Hchoice).
      * intros a b. rewrite Hnetwork.
        rewrite (Hlocal leader).
        exact (Hnetwork_inv a b).
    + destruct Hstep as
        [[Hstate Hothers] [Hconsume [Hsend Hunchanged]]].
      pose proof (Hnetwork_inv src recv) as Hhead.
      rewrite Hqueue in Hhead.
      apply Forall_inv in Hhead.
      set (oldlc := sp_leader_choice (local s leader)).
      set (newlc :=
        if Nat.eqb recv leader
        then sp_leader_choice (fst (sp_step_fn recv (local s recv) m))
        else oldlc).
      assert (Hleader_new :
        sp_leader_choice (local s' leader) = newlc).
      { unfold newlc, oldlc.
        destruct (Nat.eqb recv leader) eqn:Heq.
        - apply Nat.eqb_eq in Heq. subst recv.
          rewrite Hstate. reflexivity.
        - apply Nat.eqb_neq in Heq.
          rewrite (Hothers leader ltac:(intro H; apply Heq; symmetry; exact H)).
          reflexivity. }
      assert (Hlcmono : oldlc = None \/
              sp_leader_choice (local s' leader) = oldlc).
      { destruct (classic (recv = leader)) as [-> | Hnot].
        - rewrite Hstate.
          exact (sp_local_choice_monotone
                   leader (local s leader) m).
        - right.
          rewrite (Hothers leader
            ltac:(intro H; apply Hnot; symmetry; exact H)).
          reflexivity. }
      assert (Hnewmono : oldlc = None \/ newlc = oldlc).
      { destruct Hlcmono as [Hnone | Hsame].
        - left. exact Hnone.
        - right. rewrite <- Hleader_new. exact Hsame. }
      split.
      * intros p v Hchoice.
        destruct (classic (p = recv)) as [-> | Hp].
        -- rewrite Hstate in Hchoice.
           rewrite Hleader_new.
           apply (sp_step_choice_anchor
                    oldlc recv (local s recv) m).
           ++ intros w Hw. unfold oldlc.
              exact (Hlocal_inv recv w Hw).
           ++ exact Hhead.
           ++ exact Hchoice.
        -- rewrite (Hothers p Hp) in Hchoice.
           pose proof (Hlocal_inv p v Hchoice) as Hold.
           destruct Hlcmono as [Hnone | Hsame].
           ++ unfold oldlc in Hnone. rewrite Hnone in Hold. discriminate.
           ++ rewrite Hsame. exact Hold.
      * intros a b.
        rewrite Hleader_new.
        destruct (classic (a = recv)) as [-> | Ha].
        -- rewrite Hsend. apply Forall_app. split.
           ++ eapply Forall_impl.
              2: exact (Hnetwork_inv recv b).
              intros x Hx.
              exact (sp_choice_msg_monotone
                       oldlc newlc x Hnewmono Hx).
           ++ unfold newlc.
              exact (sp_step_new_messages_ok
                       oldlc recv (local s recv) m Hhead b).
        -- destruct (classic (b = recv)) as [-> | Hb].
           ++ destruct (classic (a = src)) as [-> | Hasrc].
              ** rewrite Hconsume.
                 pose proof (Hnetwork_inv src recv) as Hold.
                 rewrite Hqueue in Hold.
                 apply Forall_inv_tail in Hold.
                 eapply Forall_impl.
                 2: exact Hold.
                 intros x Hx.
                 exact (sp_choice_msg_monotone
                          oldlc newlc x Hnewmono Hx).
              ** rewrite Hunchanged; auto.
                 eapply Forall_impl.
                 2: exact (Hnetwork_inv a recv).
                 intros x Hx.
                 exact (sp_choice_msg_monotone
                          oldlc newlc x Hnewmono Hx).
           ++ rewrite Hunchanged; auto.
              eapply Forall_impl.
              2: exact (Hnetwork_inv a b).
              intros x Hx.
              exact (sp_choice_msg_monotone
                       oldlc newlc x Hnewmono Hx).
Qed.

Theorem SwiftPaxos_Agreement : Agreement n sp_instance.
Proof.
  unfold Agreement, sp_instance, output_of, valid_pid; simpl.
  intros s p q v w Hreach Hp Hq Hpout [Hqout | Hqout].
  - destruct (sp_output_facts s Hreach p (Commit v) Hpout)
      as [v' [Hv' [_ [_ [Hchoicev _]]]]].
    injection Hv' as ->.
    destruct (sp_output_facts s Hreach q (Commit w) Hqout)
      as [w' [Hw' [_ [_ [Hchoicew _]]]]].
    injection Hw' as ->.
    destruct (sp_choice_invariant_reachable s Hreach)
      as [Hanchor _].
    pose proof (Hanchor p v' Hchoicev) as Hvleader.
    pose proof (Hanchor q w' Hchoicew) as Hwleader.
    congruence.
  - destruct (sp_output_facts s Hreach q (Adopt w) Hqout)
      as [x [Hx _]].
    discriminate.
Qed.

Lemma sp_sent_ordinary_stable :
  forall p ls m v,
    sp_sent_ordinary ls = Some v ->
    sp_sent_ordinary (fst (sp_step_fn p ls m)) = Some v.
Proof.
  intros p ls m v Hsent.
  unfold sp_step_fn.
  destruct (sp_output ls); simpl; auto.
  destruct m as [x | x | src x kind].
  - destruct (p =? leader); simpl.
    + destruct (sp_leader_choice ls); simpl; auto.
      unfold sp_record_choice. rewrite Hsent. reflexivity.
    + destruct (sp_accepted ls); simpl; auto.
      unfold sp_record_choice. rewrite Hsent. reflexivity.
  - destruct (p =? leader); simpl; auto.
    destruct (sp_leader_choice ls); simpl; auto.
  - destruct (sp_accepted ls); simpl; auto.
    destruct (x =? p0); simpl; auto.
    destruct kind; simpl; exact Hsent.
Qed.

Lemma sp_leader_empty_vote_preserved :
  forall ls m,
    sp_leader_choice ls = None ->
    sp_sent_ordinary ls = None ->
    sp_leader_choice (fst (sp_step_fn leader ls m)) = None ->
    sp_sent_ordinary (fst (sp_step_fn leader ls m)) = None.
Proof.
  intros ls m Hchoice Hsent Hnew.
  unfold sp_step_fn in *.
  destruct (sp_output ls); simpl in *; auto.
  destruct m as [v | v | src v kind].
  - rewrite Nat.eqb_refl in *. rewrite Hchoice in *. simpl in *.
    discriminate.
  - rewrite Nat.eqb_refl in *. exact Hsent.
  - destruct (sp_accepted ls); simpl in *; auto.
    destruct (v =? p); simpl in *; auto.
    destruct kind; simpl in *; exact Hsent.
Qed.

Lemma sp_add_in :
  forall x y xs,
    In x (sp_add y xs) ->
    x = y \/ In x xs.
Proof.
  intros x y xs Hin.
  unfold sp_add in Hin.
  destruct (existsb (Nat.eqb y) xs).
  - right. exact Hin.
  - simpl in Hin. destruct Hin as [-> | Hin]; auto.
Qed.

Definition sp_evidence_msg_ok
    (s : SP_GlobalState) (queue_src : ProcessId) (m : SPMsg) : Prop :=
  match m with
  | SPAck src v OrdinaryAck =>
      src = queue_src /\
      sp_sent_ordinary (local s src) = Some v
  | SPAck src v LeaderChoiceAck =>
      src = queue_src /\
      sp_leader_choice (local s src) = Some v
  | _ => True
  end.

Definition sp_evidence_invariant (s : SP_GlobalState) : Prop :=
  (forall p,
      sp_accepted (local s p) = None ->
      sp_ordinary_acks (local s p) = [] /\
      sp_leader_acks (local s p) = [] /\
      sp_sent_ordinary (local s p) = None) /\
  (sp_leader_choice (local s leader) = None ->
   sp_sent_ordinary (local s leader) = None) /\
  (forall owner v src,
      sp_accepted (local s owner) = Some v ->
      In src (sp_ordinary_acks (local s owner)) ->
      sp_sent_ordinary (local s src) = Some v) /\
  (forall owner v src,
      sp_accepted (local s owner) = Some v ->
      In src (sp_leader_acks (local s owner)) ->
      sp_leader_choice (local s src) = Some v) /\
  (forall src dst,
      Forall (sp_evidence_msg_ok s src) (network s src dst)).

Lemma sp_evidence_msg_preserved :
  forall s s' queue_src m,
    (forall p v,
      sp_sent_ordinary (local s p) = Some v ->
      sp_sent_ordinary (local s' p) = Some v) ->
    (forall p v,
      sp_leader_choice (local s p) = Some v ->
      sp_leader_choice (local s' p) = Some v) ->
    sp_evidence_msg_ok s queue_src m ->
    sp_evidence_msg_ok s' queue_src m.
Proof.
  intros s s' queue_src m Hsent Hchoice Hok.
  unfold sp_evidence_msg_ok in *.
  destruct m as [v | v | src v kind]; auto.
  destruct kind.
  - destruct Hok as [-> Hok]. split; [reflexivity |].
    exact (Hsent queue_src v Hok).
  - destruct Hok as [-> Hok]. split; [reflexivity |].
    exact (Hchoice queue_src v Hok).
Qed.

Lemma sp_evidence_invariant_reachable :
  forall s,
    SP_Reachable s ->
    sp_evidence_invariant s.
Proof.
  intros s Hreach.
  induction Hreach as [s Hinit | recv qsrc s s' Hreach IH Hstep].
  - unfold sp_evidence_invariant, sp_init in *.
    destruct Hinit as
      [Hout [Hchoice [Haccepted [Hsentleader [Hleaderacks Hnetwork]]]]].
    split.
    + intros p Hnone.
      specialize (Haccepted p).
      destruct (excluded_middle_informative (p < n /\ is_proposer p)).
      * destruct Haccepted as [Hacc _]. rewrite Hacc in Hnone. discriminate.
      * destruct Haccepted as [_ [Hsent Hacks]].
        split; [exact Hacks |].
        split; [exact (Hleaderacks p) | exact Hsent].
    + split.
      * intros _. specialize (Haccepted leader).
        destruct (excluded_middle_informative
          (leader < n /\ is_proposer leader)).
        -- exfalso. destruct a as [_ Hprop].
           exact (sp_leader_not_proposer Hprop).
        -- tauto.
      * split.
        -- intros owner v src Hacc Hin.
           specialize (Haccepted owner).
           destruct (excluded_middle_informative
             (owner < n /\ is_proposer owner)).
           ++ destruct Haccepted as [Howner [Hsent Hacks]].
              rewrite Howner in Hacc. injection Hacc as ->.
              rewrite Hacks in Hin. simpl in Hin.
              destruct Hin as [-> | []]. exact Hsent.
           ++ destruct Haccepted as [Howner _].
              rewrite Howner in Hacc. discriminate.
        -- split.
           ++ intros owner v src Hacc Hin.
              rewrite (Hleaderacks owner) in Hin. contradiction.
           ++ intros src dst.
              destruct Hnetwork as [Hpropnet Hemptynet].
              destruct (classic
                (src < n /\ dst < n /\ src <> dst /\ is_proposer src))
                as [[Hs [Hd [Hneq Hp]]] | Hnone].
              ** rewrite (Hpropnet src dst Hs Hd Hneq Hp).
                 constructor; simpl; constructor.
              ** rewrite (Hemptynet src dst Hnone). constructor.
  - unfold sp_evidence_invariant in IH.
    destruct IH as
      [Hnone [Hleaderempty [Hord [Hlead Hnet]]]].
    unfold step, sp_instance in Hstep; simpl in Hstep.
    destruct Hstep as [[Hneq [Hqsrc Hrecv]] Hstep].
    destruct (network s qsrc recv) as [|m rest] eqn:Hqueue.
    + unfold state_eq in Hstep. destruct Hstep as [Hlocal Hnetwork].
      unfold sp_evidence_invariant.
      split.
      * intros p Hp. rewrite Hlocal in Hp. rewrite Hlocal.
        exact (Hnone p Hp).
      * split.
        -- intros Hl. rewrite Hlocal in Hl. rewrite Hlocal.
           exact (Hleaderempty Hl).
        -- split.
           ++ intros owner v src Hacc Hin.
              rewrite Hlocal in Hacc, Hin. rewrite Hlocal.
              exact (Hord owner v src Hacc Hin).
           ++ split.
              ** intros owner v src Hacc Hin.
                 rewrite Hlocal in Hacc, Hin. rewrite Hlocal.
                 exact (Hlead owner v src Hacc Hin).
              ** intros src dst. rewrite Hnetwork.
                 eapply Forall_impl.
                 2: exact (Hnet src dst).
                 intros x Hx. unfold sp_evidence_msg_ok in *.
                 destruct x as [v | v | a v kind]; auto.
                 destruct kind; destruct Hx as [-> Hx]; split; auto;
                   rewrite Hlocal; exact Hx.
    + destruct Hstep as
        [[Hstate Hothers] [Hconsume [Hsend Hunchanged]]].
      pose proof (Hnet qsrc recv) as Hhead.
      rewrite Hqueue in Hhead. apply Forall_inv in Hhead.
      assert (Hsent_preserved :
        forall p v,
          sp_sent_ordinary (local s p) = Some v ->
          sp_sent_ordinary (local s' p) = Some v).
      { intros p v Hsent.
        destruct (classic (p = recv)) as [-> | Hp].
        - rewrite Hstate.
          exact (sp_sent_ordinary_stable
                   recv (local s recv) m v Hsent).
        - rewrite (Hothers p Hp). exact Hsent. }
      assert (Hchoice_preserved :
        forall p v,
          sp_leader_choice (local s p) = Some v ->
          sp_leader_choice (local s' p) = Some v).
      { intros p v Hchoice.
        destruct (classic (p = recv)) as [-> | Hp].
        - rewrite Hstate.
          destruct (sp_local_choice_monotone recv (local s recv) m)
            as [Hnonechoice | Hsame].
          + rewrite Hnonechoice in Hchoice. discriminate.
          + rewrite Hsame. exact Hchoice.
        - rewrite (Hothers p Hp). exact Hchoice. }
      unfold sp_evidence_invariant.
      split.
      * intros p Haccnone.
        destruct (classic (p = recv)) as [-> | Hp].
        -- rewrite Hstate in Haccnone.
           unfold sp_step_fn in Haccnone.
           destruct (sp_output (local s recv)) eqn:Hout; simpl in Haccnone.
           ++ rewrite Hstate. unfold sp_step_fn. rewrite Hout. simpl.
              exact (Hnone recv Haccnone).
           ++ destruct m as [v | v | src v kind].
              ** destruct (recv =? leader) eqn:Hrl; simpl in Haccnone.
                 --- destruct (sp_leader_choice (local s recv)) eqn:Hlc;
                       simpl in Haccnone.
                     +++ rewrite Hstate. unfold sp_step_fn.
                         rewrite Hout. simpl. rewrite Hrl, Hlc. simpl.
                         exact (Hnone recv Haccnone).
                     +++ congruence.
                 --- destruct (sp_accepted (local s recv)) eqn:Hacc;
                       simpl in Haccnone; congruence.
              ** destruct (recv =? leader) eqn:Hrl; simpl in Haccnone.
                 --- rewrite Hstate. unfold sp_step_fn.
                     rewrite Hout. simpl. rewrite Hrl. simpl.
                     exact (Hnone recv Haccnone).
                 --- destruct (sp_leader_choice (local s recv)) eqn:Hlc;
                       simpl in Haccnone.
                     +++ rewrite Hstate. unfold sp_step_fn.
                         rewrite Hout. simpl. rewrite Hrl, Hlc. simpl.
                         exact (Hnone recv Haccnone).
                     +++ discriminate.
               ** destruct (sp_accepted (local s recv)) eqn:Hacc.
                 --- destruct (v =? p); simpl in Haccnone.
                     +++ destruct kind; simpl in Haccnone; try discriminate.
                     +++ congruence.
                 --- rewrite Hstate. unfold sp_step_fn.
                     rewrite Hout. simpl. rewrite Hacc. simpl.
                     exact (Hnone recv Haccnone).
        -- rewrite (Hothers p Hp) in Haccnone.
           rewrite (Hothers p Hp). exact (Hnone p Haccnone).
      * split.
        -- intros Hlc.
           destruct (classic (leader = recv)) as [Heq | Hlr].
           ++ subst recv. rewrite Hstate in Hlc.
              assert (Holdchoice :
                sp_leader_choice (local s leader) = None).
              { destruct (sp_local_choice_monotone
                  leader (local s leader) m) as [Hnonec | Hsame].
                - exact Hnonec.
                - rewrite Hsame in Hlc. exact Hlc. }
              rewrite Hstate.
              eapply sp_leader_empty_vote_preserved.
              ** exact Holdchoice.
              ** exact (Hleaderempty Holdchoice).
              ** exact Hlc.
           ++ rewrite (Hothers leader Hlr) in Hlc.
              rewrite (Hothers leader Hlr). exact (Hleaderempty Hlc).
        -- split.
           ++ intros owner v src Hacc Hin.
              destruct (classic (owner = recv)) as [-> | Howner].
              ** rewrite Hstate in Hacc, Hin.
                 unfold sp_step_fn in Hacc, Hin.
                 destruct (sp_output (local s recv)) eqn:Hout; simpl in *.
                 --- eapply Hsent_preserved. eapply Hord; eauto.
                 --- destruct m as [x | x | acksrc x kind].
                     +++ destruct (recv =? leader); simpl in *.
                         *** destruct (sp_leader_choice (local s recv));
                               simpl in *.
                             ---- eapply Hsent_preserved.
                                  eapply Hord; eauto.
                             ---- contradiction.
                         *** destruct (sp_accepted (local s recv)); simpl in *.
                             ---- eapply Hsent_preserved.
                                  eapply Hord; eauto.
                             ---- contradiction.
                     +++ destruct (recv =? leader); simpl in *.
                         *** eapply Hsent_preserved. eapply Hord; eauto.
                         *** destruct (sp_leader_choice (local s recv));
                               simpl in *.
                             ---- eapply Hsent_preserved.
                                  eapply Hord; eauto.
                             ---- contradiction.
                     +++ destruct (sp_accepted (local s recv))
                           as [p|] eqn:Haccepted.
                         *** simpl in *.
                             destruct (x =? p) eqn:Hx; simpl in *.
                             ---- destruct kind; simpl in *.
                                  ++++ apply sp_add_in in Hin as [Heq | Hin].
                                       **** subst src.
                                            destruct Hhead as
                                              [Hacksrc Hevidence].
                                            subst acksrc.
                                            pose proof (Hsent_preserved
                                              qsrc x Hevidence) as Hpres.
                                            apply Nat.eqb_eq in Hx.
                                            congruence.
                                       **** eapply Hsent_preserved.
                                            eapply Hord;
                                              [exact (eq_trans Haccepted Hacc)
                                              | exact Hin].
                                  ++++ eapply Hsent_preserved.
                                       eapply Hord;
                                         [exact (eq_trans Haccepted Hacc)
                                         | exact Hin].
                             ---- eapply Hsent_preserved.
                                  eapply Hord;
                                    [exact Hacc
                                    | exact Hin].
                         *** simpl in Hacc. congruence.
              ** rewrite (Hothers owner Howner) in Hacc, Hin.
                 eapply Hsent_preserved.
                 eapply Hord; [exact Hacc | exact Hin].
           ++ split.
              ** intros owner v src Hacc Hin.
                 destruct (classic (owner = recv)) as [-> | Howner].
                 --- rewrite Hstate in Hacc, Hin.
                     unfold sp_step_fn in Hacc, Hin.
                     destruct (sp_output (local s recv)) eqn:Hout; simpl in *.
                     +++ eapply Hchoice_preserved. eapply Hlead; eauto.
                     +++ destruct m as [x | x | acksrc x kind].
                         *** destruct (recv =? leader); simpl in *.
                             ---- destruct (sp_leader_choice (local s recv));
                                  simpl in *.
                                  ++++ eapply Hchoice_preserved.
                                       eapply Hlead; eauto.
                                  ++++ contradiction.
                             ---- destruct (sp_accepted (local s recv));
                                  simpl in *.
                                  ++++ eapply Hchoice_preserved.
                                       eapply Hlead; eauto.
                                  ++++ contradiction.
                         *** destruct (recv =? leader); simpl in *.
                             ---- eapply Hchoice_preserved.
                                  eapply Hlead; eauto.
                             ---- destruct (sp_leader_choice (local s recv));
                                  simpl in *.
                                  ++++ eapply Hchoice_preserved.
                                       eapply Hlead; eauto.
                                  ++++ contradiction.
                         *** destruct (sp_accepted (local s recv))
                               as [p|] eqn:Haccepted.
                             ---- simpl in *.
                                  destruct (x =? p) eqn:Hx; simpl in *.
                                  ++++ destruct kind; simpl in *.
                                       **** eapply Hchoice_preserved.
                                            eapply Hlead;
                                              [exact (eq_trans Haccepted Hacc)
                                              | exact Hin].
                                       **** apply sp_add_in in Hin
                                              as [Heq | Hin].
                                            { subst src.
                                              destruct Hhead as
                                                [Hacksrc Hevidence].
                                              subst acksrc.
                                              pose proof
                                                (Hchoice_preserved
                                                  qsrc x Hevidence) as Hpres.
                                              apply Nat.eqb_eq in Hx.
                                              congruence. }
                                            { eapply Hchoice_preserved.
                                              eapply Hlead;
                                                [exact
                                                  (eq_trans Haccepted Hacc)
                                                | exact Hin]. }
                                  ++++ eapply Hchoice_preserved.
                                       eapply Hlead;
                                         [exact Hacc | exact Hin].
                             ---- simpl in Hacc. congruence.
                  --- rewrite (Hothers owner Howner) in Hacc, Hin.
                     eapply Hchoice_preserved.
                     eapply Hlead; [exact Hacc | exact Hin].
              ** intros src dst.
                 destruct (classic (src = recv)) as [-> | Hsrcneq].
                 --- rewrite Hsend. apply Forall_app. split.
                     +++ eapply Forall_impl.
                         2: exact (Hnet recv dst).
                         intros x Hx.
                          unfold sp_evidence_msg_ok in *.
                          destruct x as [x | x | a x kind]; auto.
                          destruct kind.
                          { destruct Hx as [-> Hx]. split; [reflexivity |].
                            exact (Hsent_preserved recv x Hx). }
                          { destruct Hx as [-> Hx]. split; [reflexivity |].
                            exact (Hchoice_preserved recv x Hx). }
                     +++ unfold sp_step_fn.
                         destruct (sp_output (local s recv)) eqn:Houtput;
                           simpl.
                         { constructor. }
                         destruct m as [x | x | a x kind].
                         *** destruct (recv =? leader) eqn:Hrl; simpl.
                             ---- destruct (sp_leader_choice (local s recv))
                                    eqn:Hchoice;
                                  simpl; [constructor |].
                                   destruct (dst =? x); simpl;
                                     repeat constructor; simpl; auto.
                                   { apply Nat.eqb_eq in Hrl.
                                     symmetry. exact Hrl. }
                                   { apply Nat.eqb_eq in Hrl. subst recv.
                                     rewrite Hstate. unfold sp_step_fn. simpl.
                                     rewrite Houtput, Nat.eqb_refl, Hchoice.
                                     simpl.
                                     unfold sp_record_choice.
                                     rewrite (Hleaderempty Hchoice).
                                     reflexivity. }
                             ---- destruct (sp_accepted (local s recv)) eqn:Hacc;
                                  simpl; [constructor |].
                                  destruct (dst =? x); simpl; [|constructor].
                                   constructor; [|constructor]. simpl.
                                   split; [reflexivity |].
                                   rewrite Hstate. unfold sp_step_fn.
                                   rewrite Houtput. simpl. rewrite Hrl, Hacc.
                                   simpl. unfold sp_record_choice.
                                   rewrite (proj2 (proj2 (Hnone recv Hacc))).
                                   reflexivity.
                         *** destruct (recv =? leader) eqn:Hrl;
                               simpl; [constructor |].
                             destruct (sp_leader_choice (local s recv))
                               eqn:Hchoice;
                               simpl; [constructor |].
                             destruct (dst =? x); simpl; [|constructor].
                             constructor; [|constructor]. simpl.
                             split; [reflexivity |].
                             rewrite Hstate. unfold sp_step_fn.
                             rewrite Houtput. simpl. rewrite Hrl, Hchoice.
                             reflexivity.
                         *** destruct (sp_accepted (local s recv));
                               simpl; [|constructor].
                             destruct (x =? p); simpl; constructor.
                 --- destruct (classic (dst = recv)) as [-> | Hdstneq].
                     +++ destruct (classic (src = qsrc)) as [-> | Hsrcq].
                          *** rewrite Hconsume.
                              pose proof (Hnet qsrc recv) as Hold.
                              rewrite Hqueue in Hold.
                              eapply Forall_impl.
                              2: exact (Forall_inv_tail Hold).
                              intros msg Hmsg.
                              eapply sp_evidence_msg_preserved; eauto.
                          *** rewrite Hunchanged; auto.
                              eapply Forall_impl.
                              2: exact (Hnet src recv).
                              intros msg Hmsg.
                              eapply sp_evidence_msg_preserved; eauto.
                      +++ rewrite Hunchanged; auto.
                          eapply Forall_impl.
                          2: exact (Hnet src dst).
                          intros msg Hmsg.
                          eapply sp_evidence_msg_preserved; eauto.
Qed.

Definition sp_node_records (s : SP_GlobalState)
    (p v : ProcessId) : Prop :=
  sp_sent_ordinary (local s p) = Some v \/
  sp_leader_choice (local s p) = Some v.

Lemma sp_C1_quorum_large :
  forall Q,
    sp_C1_fast_quorum Q ->
    f + 1 <= length Q.
Proof.
  intros Q [_ [_ [_ Hsize]]].
  rewrite sp_n_eq in Hsize. lia.
Qed.

Lemma sp_commit_certificate :
  forall s,
    SP_Reachable s ->
    forall owner v,
      sp_output (local s owner) = Some (Commit v) ->
      exists cert,
        NoDup cert /\
        (forall p, In p cert -> p < n) /\
        f + 1 <= length cert /\
        (forall p, In p cert -> sp_node_records s p v).
Proof.
  intros s Hreach owner v Hout.
  destruct (sp_output_facts s Hreach owner (Commit v) Hout)
    as [w [Heq [_ [Haccepted [_ Hcert]]]]].
  injection Heq as ->.
  destruct (sp_evidence_invariant_reachable s Hreach)
    as [_ [_ [Hord [Hlead _]]]].
  destruct Hcert as [Hdirect | Hleadercert].
  - destruct Hdirect as [Q [HQ Hincl]].
    exists Q.
    unfold sp_direct_fast_quorum in HQ.
    destruct config.
    + simpl in HQ.
      destruct HQ as [Hnd [Hvalid [Hleader Hsize]]].
      repeat split; auto.
      * apply sp_C1_quorum_large.
        repeat split; auto.
      * intros p Hp. left.
        eapply Hord; [exact Haccepted |].
        exact (Hincl p Hp).
    + simpl in HQ.
      unfold sp_C2_fast_quorum in HQ.
      subst Q. split; [exact sp_c2_nodup |].
      split; [exact sp_c2_valid |].
      split.
      * rewrite <- sp_c2_size. apply Nat.le_refl.
      * intros p Hp. left.
        eapply Hord; [exact Haccepted |].
        exact (Hincl p Hp).
  - exists (sp_leader_acks (local s owner)).
    destruct Hleadercert as [Hnd [Hvalid Hsize]].
    repeat split; auto.
    intros p Hp. right.
    eapply Hlead; eauto.
Qed.

Definition sp_intersection (A B : list ProcessId) : list ProcessId :=
  filter (fun x => existsb (Nat.eqb x) B) A.

Lemma sp_intersection_spec :
  forall x A B,
    In x (sp_intersection A B) <-> In x A /\ In x B.
Proof.
  intros x A B. unfold sp_intersection.
  rewrite filter_In. split.
  - intros [HxA Htest]. split; [exact HxA |].
    apply existsb_exists in Htest as [y [Hy Heq]].
    apply Nat.eqb_eq in Heq. subst y. exact Hy.
  - intros [HxA HxB]. split; [exact HxA |].
    apply existsb_exists. exists x.
    split; [exact HxB | apply Nat.eqb_refl].
Qed.

Lemma sp_intersection_length_lower_bound :
  forall A B : list ProcessId,
    NoDup A -> (forall x, In x A -> x < n) ->
    NoDup B -> (forall x, In x B -> x < n) ->
    length A + length B <= n + length (sp_intersection A B).
Proof.
  intros A B HndA HvalA HndB HvalB.
  set (inside := fun x => existsb (Nat.eqb x) B).
  set (D := filter (fun x => negb (inside x)) A).
  assert (Hpartition : length (filter inside A) + length D = length A).
  { unfold D. exact (filter_length inside A). }
  assert (HndD : NoDup D) by (apply NoDup_filter; exact HndA).
  assert (HinclD :
    incl D (filter (fun x => negb (inside x)) (seq 0 n))).
  { intros x Hx. apply filter_In in Hx as [HxA Hnot].
    apply filter_In. split.
    - apply in_seq. split; [lia | exact (HvalA x HxA)].
    - exact Hnot. }
  assert (HlenD :
    length D <= length (filter (fun x => negb (inside x)) (seq 0 n)))
    by exact (NoDup_incl_length HndD HinclD).
  assert (Hinside_seq : length (filter inside (seq 0 n)) = length B).
  { apply Nat.le_antisymm.
    - apply NoDup_incl_length; [apply NoDup_filter, seq_NoDup |].
      intros x Hx. apply filter_In in Hx as [_ Htest].
      unfold inside in Htest.
      apply existsb_exists in Htest as [y [Hy Heq]].
      apply Nat.eqb_eq in Heq. subst y. exact Hy.
    - apply NoDup_incl_length; [exact HndB |].
      intros x Hx. apply filter_In. split.
      + apply in_seq. split; [lia | exact (HvalB x Hx)].
      + unfold inside. apply existsb_exists.
        exists x. split; [exact Hx | apply Nat.eqb_refl]. }
  pose proof (filter_length inside (seq 0 n)) as Hseqpartition.
  rewrite length_seq, Hinside_seq in Hseqpartition.
  change (length A + length B <= n + length (filter inside A)).
  lia.
Qed.

(** Arithmetic audit for [f=1,2,3,4], hence [n=3,5,7,9]:
    the minimum C1 sizes are [3,4,6,7], and pairwise intersection
    lower bounds are [3,3,5,5], all strictly larger than [f]. *)
Lemma sp_C1_intersection_large :
  forall A B,
    sp_C1_fast_quorum A ->
    sp_C1_fast_quorum B ->
    f < length (sp_intersection A B).
Proof.
  intros A B [HndA [HvalA [_ HsizeA]]]
             [HndB [HvalB [_ HsizeB]]].
  pose proof (sp_intersection_length_lower_bound
    A B HndA HvalA HndB HvalB) as Hinter.
  rewrite sp_n_eq in HsizeA, HsizeB, Hinter.
  lia.
Qed.

Lemma sp_large_sets_intersect :
  forall A B,
    NoDup A -> (forall x, In x A -> x < n) ->
    NoDup B -> (forall x, In x B -> x < n) ->
    n < length A + length B ->
    exists x, In x A /\ In x B.
Proof.
  intros A B HndA HvalA HndB HvalB Hlarge.
  apply Classical_Pred_Type.not_all_not_ex.
  intro Hnone.
  assert (Hdisj : forall x, In x A -> ~ In x B).
  { intros x HxA HxB. exact (Hnone x (conj HxA HxB)). }
  assert (Hnd : NoDup (A ++ B)).
  { apply NoDup_app; auto. }
  assert (Hincl : incl (A ++ B) (seq 0 n)).
  { intros x Hx. apply in_app_iff in Hx. apply in_seq.
    split; [lia |].
    destruct Hx as [Hx | Hx];
      [exact (HvalA x Hx) | exact (HvalB x Hx)]. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hbound.
  rewrite length_app, length_seq in Hbound. lia.
Qed.

Lemma sp_direct_quorums_common_alive :
  forall A B alive,
    sp_direct_fast_quorum A ->
    sp_direct_fast_quorum B ->
    NoDup alive ->
    n - f <= length alive ->
    (forall x, In x alive -> x < n) ->
    exists x, In x A /\ In x B /\ In x alive.
Proof.
  intros A B alive HA HB Hndalive Hlenalive Hvalalive.
  unfold sp_direct_fast_quorum in HA, HB.
  destruct config.
  - simpl in HA, HB.
    set (I := sp_intersection A B).
    assert (HndI : NoDup I).
    { unfold I, sp_intersection. apply NoDup_filter.
      exact (proj1 HA). }
    assert (HvalI : forall x, In x I -> x < n).
    { intros x Hx. apply sp_intersection_spec in Hx as [HxA _].
      exact (proj1 (proj2 HA) x HxA). }
    assert (HlenI : f < length I).
    { unfold I. exact (sp_C1_intersection_large A B HA HB). }
    assert (Hlarge : n < length I + length alive).
    { rewrite sp_n_eq in Hlenalive |- *. lia. }
    destruct (sp_large_sets_intersect
      I alive HndI HvalI Hndalive Hvalalive Hlarge)
      as [x [HxI Hxalive]].
    apply sp_intersection_spec in HxI as [HxA HxB].
    exists x. auto.
  - simpl in HA, HB.
    unfold sp_C2_fast_quorum in HA, HB. subst A. subst B.
    assert (Hlarge : n < length c2_quorum + length alive).
    { rewrite sp_n_eq in Hlenalive |- *.
      rewrite sp_c2_size. lia. }
    destruct (sp_large_sets_intersect c2_quorum alive
      sp_c2_nodup sp_c2_valid Hndalive Hvalalive Hlarge)
      as [x [HxQ Hxalive]].
    exists x. auto.
Qed.

Lemma sp_leader_certificate_has_alive :
  forall cert alive,
    sp_leader_certificate cert ->
    NoDup alive ->
    n - f <= length alive ->
    (forall x, In x alive -> x < n) ->
    exists x, In x cert /\ In x alive.
Proof.
  intros cert alive [Hndcert [Hvalcert Hlencert]]
    Hndalive Hlenalive Hvalalive.
  assert (Hlarge : n < length cert + length alive).
  { rewrite sp_n_eq in Hlenalive |- *. lia. }
  exact (sp_large_sets_intersect cert alive
    Hndcert Hvalcert Hndalive Hvalalive Hlarge).
Qed.

Theorem SwiftPaxos_Recoverability : Recoverability n f sp_instance.
Proof.
  unfold Recoverability, sp_instance, output_of, valid_pid; simpl.
  intros s s' alive v w Hs Hs' Hndalive Hlenalive Hvalalive Hequal
    [owner Hout] [owner' Hout'].
  destruct (sp_output_facts s Hs owner (Commit v) Hout)
    as [v0 [Hv0 [_ [Haccv [Hchoicev Hcertv]]]]].
  injection Hv0 as Heqv. subst v0.
  destruct (sp_output_facts s' Hs' owner' (Commit w) Hout')
    as [w0 [Hw0 [_ [Haccw [Hchoicew Hcertw]]]]].
  injection Hw0 as Heqw. subst w0.
  destruct (sp_evidence_invariant_reachable s Hs)
    as [_ [_ [Hordv [Hleadv _]]]].
  destruct (sp_evidence_invariant_reachable s' Hs')
    as [_ [_ [Hordw [Hleadw _]]]].
  destruct (sp_choice_invariant_reachable s Hs)
    as [Hanchorv _].
  destruct (sp_choice_invariant_reachable s' Hs')
    as [Hanchorw _].
  destruct Hcertv as [Hdirectv | Hleadcertv];
    destruct Hcertw as [Hdirectw | Hleadcertw].
  - destruct Hdirectv as [A [HA HinclA]].
    destruct Hdirectw as [B [HB HinclB]].
    destruct (sp_direct_quorums_common_alive A B alive
      HA HB Hndalive Hlenalive Hvalalive)
      as [x [HxA [HxB Hxalive]]].
    pose proof (Hordv owner v x Haccv (HinclA x HxA)) as Hxv.
    pose proof (Hordw owner' w x Haccw (HinclB x HxB)) as Hxw.
    rewrite (Hequal x Hxalive) in Hxv. congruence.
  - destruct (sp_leader_certificate_has_alive
      (sp_leader_acks (local s' owner')) alive
      Hleadcertw Hndalive Hlenalive Hvalalive)
      as [x [Hxcert Hxalive]].
    pose proof (Hleadw owner' w x Haccw Hxcert) as Hxw.
    assert (Hxw_s : sp_leader_choice (local s x) = Some w).
    { rewrite (Hequal x Hxalive). exact Hxw. }
    pose proof (Hanchorv owner v Hchoicev) as Hvleader.
    pose proof (Hanchorv x w Hxw_s) as Hwleader.
    congruence.
  - destruct (sp_leader_certificate_has_alive
      (sp_leader_acks (local s owner)) alive
      Hleadcertv Hndalive Hlenalive Hvalalive)
      as [x [Hxcert Hxalive]].
    pose proof (Hleadv owner v x Haccv Hxcert) as Hxv.
    assert (Hxv_s' : sp_leader_choice (local s' x) = Some v).
    { rewrite <- (Hequal x Hxalive). exact Hxv. }
    pose proof (Hanchorw x v Hxv_s') as Hvleader.
    pose proof (Hanchorw owner' w Hchoicew) as Hwleader.
    congruence.
  - destruct (sp_leader_certificate_has_alive
      (sp_leader_acks (local s owner)) alive
      Hleadcertv Hndalive Hlenalive Hvalalive)
      as [x [Hxcert Hxalive]].
    pose proof (Hleadv owner v x Haccv Hxcert) as Hxv.
    assert (Hxv_s' : sp_leader_choice (local s' x) = Some v).
    { rewrite <- (Hequal x Hxalive). exact Hxv. }
    pose proof (Hanchorw x v Hxv_s') as Hvleader.
    pose proof (Hanchorw owner' w Hchoicew) as Hwleader.
    congruence.
Qed.

End SP.
