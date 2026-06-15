(** * Adopt-Commit emulating SwiftPaxos's Fast-Path
    This file instantiates the abstract adopt-commit framework from
    AdoptCommit.v with a simplified fast path inspired by SwiftPaxos.

    SwiftPaxos (USENIX NSDI 2021) is a leaderless consensus protocol
    designed for geo-distributed systems with low tail latency.

    This file formalizes only a fast-path SwiftPaxos-style
    adopt-commit abstraction.

    It is NOT a full formalization of SwiftPaxos.

    Modeled:
    - one command/value proposed through a fast-path quorum
    - the protocol's fast-path quorum-intersection idea
    - adopt-commit-level Validity, Agreement, Convergence, and Recoverability

    Not modeled:
    - slow path
    - Accept / AcceptReply
    - recovery protocol
    - multi-instance execution
    - dynamic dependency graph execution
    - liveness or performance behavior

    Fast path overview:
    - Each proposer p broadcasts its proposal to all other processes.
      This broadcast is part of the initial state rather than a step.
      A proposer also pre-accepts its own value.
    - When a process receives a proposal and has not yet accepted any value,
      it accepts the proposer's value and replies to the proposer.
    - When a process has already accepted value v and receives an acceptance
      acknowledgment, it records sender as a new acceptor of v and commits
      once a fast quorum is reached.
    - Messages about a proposer other than the one already accepted are ignored.

    Mapping to adopt-commit framework:
    - ProcessId serves as both process identifier and proposed value
    - Each proposer proposes its own ID
    - Output is Commit v when fast quorum is reached
    - No Adopt is produced (fast-path only)
    - Fast quorum size ensures intersection for Agreement
    - Recoverability requires n-f survivors to retain commit evidence *)

From Stdlib Require Import List Arith Bool Classical Lia.
Import ListNotations.

Require Import AdoptCommit.

(* ================================================================
   Messages and Local State
   ================================================================ *)

(** Messages encode both a proposer's request to accept and
    the acknowledgment that a process accepted. *)
Record SPMsg := mkSPMsg {
  sp_source   : ProcessId; (* sender of the message *)
  sp_proposer : ProcessId; (* Value (=proposer) the source accepted *)
}.

Record SPState := mkSPState {
  sp_accepted  : option ProcessId;   (* Value (=proposer) that p accepted *)
  sp_acceptors : list ProcessId;     (* processes that acknowledged accepting *)
  sp_output    : option ACOutput;
}.

(* ================================================================
   Protocol Instantiation
   ================================================================ *)

Section SP.

Variable n : nat.
Hypothesis n_pos : 0 < n.
Variable f : nat.
Hypothesis f_lt_n : f < n.

(** SwiftPaxos assumes n = 2f + 1 for the fast path.
    This is the standard assumption for EPaxos-style protocols. *)
Hypothesis n_eq_2f_plus_1 : n = 2 * f + 1.

Variable is_proposer : ProcessId -> Prop.
Hypothesis exists_proposer : exists p, p < n /\ is_proposer p.

(** Fast quorum size for SwiftPaxos.
    Based on the paper, we need fast quorums to intersect in at least
    one process. For n = 2f + 1, the fast quorum size is f + (f+1)/2 + 1.

    With n = 2f + 1:
    - We need: for any two fast quorums Q1 and Q2, |Q1 ∩ Q2| >= 1
    - This requires: 2 * sp_quorum > n
    - With sp_quorum = f + (f+1)/2 + 1, we get:
      2 * (f + (f+1)/2 + 1) = 2f + (f+1) + 2 >= 2f + f + 2 = 3f + 2 > 2f + 1 = n

    This formula ensures quorum intersection. *)
Definition sp_quorum : nat := f + (f + 1) / 2 + 1.

(** Local transition function.
    When process p receives a message (sender, proposer):
    - If already decided, the message is ignored (output stable).
    - If p has not accepted any value yet, p accepts the value and
      acknowledges the acceptance to the proposer.
    - If p already accepted value v:
        - if the message is also about v: record sender as a new acceptor;
          commit if sp_quorum acceptors have been collected.
        - if the message is not about v, ignore. *)
Definition sp_step_fn
    (p : ProcessId) (ls : SPState) (m : SPMsg)
    : SPState * (ProcessId -> list SPMsg) :=
  match sp_output ls with
  | Some _ => (ls, fun _ => [])
  | None => match sp_accepted ls with
      | None =>
          (mkSPState (Some (sp_proposer m)) [] None,
            fun dst => if Nat.eqb dst (sp_proposer m) then [mkSPMsg p (sp_proposer m)] else [])
      | Some v =>
          if Nat.eqb (sp_proposer m) v then
            let new_acceptors :=
              if existsb (Nat.eqb (sp_source m)) (sp_acceptors ls)
              then sp_acceptors ls
              else (sp_source m) :: sp_acceptors ls
            in
            let new_output :=
              if sp_quorum <=? List.length new_acceptors then Some (Commit v)
              else None
            in
            (mkSPState (Some v) new_acceptors new_output, fun _ => [])
          else
            (ls, fun _ => [])
      end
  end.

(** Initial state predicate.
    - All processes start undecided.
    - Each proposer p has accepted its own value and lists itself as the
      sole acceptor.
    - Non-proposers start with no accepted value and no acceptors.
    - Each proposer has broadcasted its proposal to everyone.
    - Non-proposers have no outgoing messages. *)
Definition sp_init (s : GlobalState SPMsg SPState) : Prop :=
  ((forall p,
      sp_output (local s p) = None) /\
  ((forall p, p < n -> is_proposer p ->
      sp_accepted  (local s p) = Some p) /\
  (forall p, p < n -> ~ is_proposer p ->
      sp_accepted  (local s p) = None)) /\
  ((forall p, p < n -> is_proposer p ->
      sp_acceptors (local s p) = [p]) /\
  (forall p, p < n -> ~ is_proposer p ->
      sp_acceptors (local s p) = []))) /\
  (((forall p q, p < n -> q < n -> p <> q -> is_proposer p ->
      network s p q = [mkSPMsg p p]) /\
  (forall p q, p < n -> q < n -> ~ is_proposer p ->
      network s p q = [])) /\
  (forall p, p < n -> network s p p = [])).

(** Bundle of all protocol-specific parameters for this instantiation. *)
Definition sp_instance : ACProtocol :=
  mkACProtocol sp_output is_proposer sp_init sp_step_fn.

(* ================================================================
   Shorthands for the Instantiated Definitions
   ================================================================ *)

Definition SP_GlobalState := GlobalState SPMsg SPState.
Definition SP_Reachable   := Reachable n sp_instance.

(* ================================================================
   Proofs
   ================================================================ *)

(** Processes never discard an existing output. *)
Lemma output_stable :
  forall p ls m o,
    sp_output ls = Some o ->
    sp_output (fst (sp_step_fn p ls m)) = Some o.
Proof.
  intros p ls m o H.
  unfold sp_step_fn. rewrite H. simpl. exact H.
Qed.

Lemma all_message_values_valid :
  forall s,
    SP_Reachable s ->
    (forall src dest,
      src < n -> dest < n -> Forall (fun msg => is_proposer (sp_proposer msg)) (network s src dest)).
Proof.
  intros s Hs. induction Hs; simpl in H.
  - (* init-case: only proposers have sent messages with their own value. *)
    unfold sp_init in H; destruct H as [_ [[init_net_prop init_net_nonprop] init_net_self]].
    intros src dest src_valid dest_valid. destruct (classic (is_proposer src)) as [Hprop | Hprop].
    + destruct (classic (src = dest)) as [Heq | Hneq].
      * (* no messages are sent to self *)
        destruct Heq. rewrite (init_net_self src src_valid). constructor.
      * (* proposer sending to others *)
        rewrite (init_net_prop src dest src_valid dest_valid Hneq Hprop). constructor; auto.
    + (* non-proposers send nothing initially *)
      rewrite (init_net_nonprop src dest src_valid dest_valid Hprop). constructor; auto.
  - (* step-case: try to dequeue a message and potentially send new ones *)
    intros src0 dest. unfold step, sp_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p_valid]] H].
    destruct (network s src p) as [| msg rest] eqn:src_net.
    + (* empty queue: nothing was done. *)
      unfold state_eq in H. destruct H as [state_eq net_eq].
      rewrite net_eq. auto.
    + destruct H as [_ [H_net_p_in [H_net_p_out H_net_other]]].
      intros src0_valid dest_valid.
      destruct (classic (src = src0)).
      * destruct H. destruct (classic (dest = p)).
        -- (* Queue from which p consumed the message. *)
          destruct H.
          pose (IHHs src dest src0_valid dest_valid) as H.
          rewrite src_net in H.
          apply Forall_inv_tail in H.
          destruct H_net_p_in. auto.
        -- (* Other queues from the same source: unchanged. *)
          rewrite H_net_other; auto.
      * destruct (classic (p = src0)).
        -- (* p's outgoing queues: gained the replies from sp_step_fn. *)
          destruct H0.
          rewrite H_net_p_out.
          apply Forall_app. split.
          ++ (* Pre-existing messages: valid by IHHs. *)
            auto.
          ++ (* New messages emitted by sp_step_fn: *)
            unfold sp_step_fn.
            destruct (sp_output (local s p)); auto. (* output already set: no new messages *)
            destruct (sp_accepted (local s p)).
            ** (* Already accepted: no new messages (or sends nothing new). *)
              destruct (sp_proposer msg =? p0); simpl; auto.
            ** (* Not yet accepted: sends replies to proposer (with same value). *)
              simpl. destruct (dest =? sp_proposer msg); auto.
              rewrite Forall_cons_iff; split; auto.
              simpl.
              pose (IHHs src p src_valid p_valid) as Hmsg.
              rewrite src_net in Hmsg.
              apply Forall_inv in Hmsg.
              apply Hmsg.
        -- (* All the other queues: unchanged. *)
          rewrite H_net_other; auto.
Qed.

Lemma all_accepted_values_valid :
  forall s,
    SP_Reachable s ->
    (forall p, p < n -> match sp_accepted (local s p) with
        | None => True
        | Some(value) => is_proposer value
      end).
Proof.
  intros s Hs p p_valid. induction Hs; simpl in H.
  - (* init case *)
    unfold sp_init in H; destruct H as [[_ [[prop_acc nonprop_acc] _]] _].
    destruct (classic (is_proposer p)) as [prop | not_prop].
    + rewrite (prop_acc p p_valid prop). auto.
    + rewrite (nonprop_acc p p_valid not_prop). auto.
  - (* step case *)
    unfold step, sp_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) as [| f0 ] eqn:src_net.
    + (* no message from src: no-op *)
      unfold state_eq in H. destruct H as [local_eq _].
      rewrite local_eq. exact IHHs.
    + destruct H as [[p0_state other_state] _].
      destruct (classic (p = p0)).
      * (* state of the stepping process *)
        destruct H. rewrite p0_state.
        unfold sp_step_fn.
        destruct (sp_output (local s p)); auto.
        destruct (sp_accepted (local s p)) eqn:prev_acc.
        -- (* already accepted value before: Use IHHs *)
          destruct (Nat.eqb (sp_proposer f0) p0); simpl.
          ++ exact IHHs.
          ++ rewrite prev_acc. exact IHHs.
        -- (* will accept the message's value. *)
          simpl.
          pose proof (all_message_values_valid s Hs src p src_valid p_valid) as Hmsg.
          rewrite src_net in Hmsg.
          exact (Forall_inv Hmsg).
      * (* p != p0: other processes local state are unchanged *)
        rewrite (other_state p H).
        exact IHHs.
Qed.

Lemma all_output_values_valid :
  forall s,
    SP_Reachable s ->
    forall p, p < n ->
      match sp_output (local s p) with
      | None => True
      | Some (Commit v) => is_proposer v
      | Some (Adopt v) => is_proposer v
      end.
Proof.
  intros s Hs p p_valid. induction Hs; simpl in H.
  - (* Init: all outputs are None. *)
    unfold sp_init in H. destruct H as [[init_noout _] _].
    rewrite (init_noout p). auto.
  - (* Step: p0 receives the head message f0 from src. *)
    unfold step, sp_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) as [| f0 ] eqn:src_net.
    + (* Empty queue: no message delivered, local states unchanged. *)
      unfold state_eq in H. destruct H as [local_eq _].
      rewrite local_eq. exact IHHs.
    + destruct H as [[p0_state other_state] _].
      destruct (classic (p = p0)).
      * (* p = p0: p's local state was updated by sp_step_fn. *)
        destruct H. rewrite p0_state.
        destruct (sp_output (local s p)) as [o|] eqn:prev_out.
        -- (* Output already set: sp_step_fn leaves local state unchanged. *)
          rewrite (output_stable p (local s p) f0 o prev_out).
          exact IHHs.
        -- (* No output yet: inspect accepted value. *)
          unfold sp_step_fn. rewrite prev_out.
          destruct (sp_accepted (local s p)) as [v|] eqn:prev_acc.
          ++ destruct (Nat.eqb (sp_proposer f0) v).
            ** (* Accepted value matches: might commit. *)
              simpl.
              pose proof (all_accepted_values_valid s Hs p p_valid) as Hacc.
              rewrite prev_acc in Hacc.
              destruct (sp_quorum <=? _); auto.
            ** (* Accepted value does not match: state unchanged. *)
              simpl. rewrite prev_out. auto.
          ++ (* Not yet accepted: will accept proposer f0, output stays None. *)
            simpl. auto.
      * (* p != p0: p's local state is unchanged. *)
        rewrite (other_state p H).
        exact IHHs.
Qed.

Theorem SwiftPaxos_Validity : Validity n sp_instance.
Proof.
  unfold Validity, sp_instance, output_of, valid_pid; simpl.
  intros s p v Hs p_valid [Hout | Hout];
    pose proof (all_output_values_valid s Hs p p_valid) as Hvalid;
    rewrite Hout in Hvalid; exact Hvalid.
Qed.

(** sp_step_fn never changes an already-accepted value. *)
Lemma accepted_stable :
  forall p ls m v,
    sp_accepted ls = Some v ->
    sp_accepted (fst (sp_step_fn p ls m)) = Some v.
Proof.
  intros p ls m v Hacc.
  unfold sp_step_fn.
  destruct (sp_output ls); [simpl; exact Hacc |].
  rewrite Hacc. simpl.
  destruct (Nat.eqb (sp_proposer m) v); simpl; [reflexivity | exact Hacc].
Qed.

(** The source of every message has accepted the value. *)
Lemma msg_src_has_accepted :
  forall s,
    SP_Reachable s ->
    forall src dest,
      src < n -> dest < n ->
      Forall (fun msg => sp_source msg = src /\
                         sp_accepted (local s src) = Some (sp_proposer msg))
             (network s src dest).
Proof.
  intros s Hs. induction Hs; simpl in H.
  - unfold sp_init in H.
    destruct H as [[_ [[prop_acc _] _]] [[prop_net nonprop_net] net_self]].
    intros src dest src_valid dest_valid.
    destruct (classic (is_proposer src)) as [Hprop | Hprop].
    + destruct (classic (src = dest)) as [Heq | Hneq].
      * destruct Heq. rewrite (net_self src src_valid). constructor.
      * rewrite (prop_net src dest src_valid dest_valid Hneq Hprop).
        constructor; [| constructor]. simpl. split.
        -- reflexivity.
        -- rewrite (prop_acc src src_valid Hprop). reflexivity.
    + rewrite (nonprop_net src dest src_valid dest_valid Hprop). constructor.
  - unfold step, sp_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p_valid]] H].
    destruct (network s src p) as [| f0 ] eqn:src_net.
    + (* No message delivered. *)
      unfold state_eq in H. destruct H as [local_eq net_eq].
      intros src0 dest src0_valid dest_valid.
      rewrite net_eq.
      eapply Forall_impl.
      2: exact (IHHs src0 dest src0_valid dest_valid).
      intros msg [Hsrc Hacc]. split; [exact Hsrc | rewrite local_eq; exact Hacc].
    + destruct H as [[p0_state other_state] [H_net_p_in [H_net_p_out H_net_other]]].
      intros src0 dest src0_valid dest_valid.
      destruct (classic (src0 = src)) as [Hsrc0 | Hsrc0].
      * subst src0.
        destruct (classic (dest = p)) as [Hdest | Hdest].
        -- (* src -> p: head consumed, rest unchanged. *)
           subst dest. rewrite H_net_p_in.
           pose proof (IHHs src p src_valid p_valid) as Hold.
           rewrite src_net in Hold. apply Forall_inv_tail in Hold.
           eapply Forall_impl.
           2: exact Hold.
           intros msg [Hsrc Hacc]. split; [exact Hsrc |].
           rewrite (other_state src p_not_src). exact Hacc.
        -- (* src -> other dest: queue unchanged. *)
           rewrite (H_net_other src dest p_not_src (or_introl Hdest)).
           eapply Forall_impl.
           2: exact (IHHs src dest src_valid dest_valid).
           intros msg [Hsrc Hacc]. split; [exact Hsrc |].
           rewrite (other_state src p_not_src). exact Hacc.
      * destruct (classic (src0 = p)) as [Hsp | Hsp].
        -- (* p's outgoing queues: new messages from sp_step_fn. *)
           subst src0. rewrite H_net_p_out. rewrite Forall_app. split.
           ++ (* Old messages. *)
              eapply Forall_impl.
              2: exact (IHHs p dest p_valid dest_valid).
              intros msg [Hsrcmsg Hacc]. split; [exact Hsrcmsg |].
              rewrite p0_state.
              exact (accepted_stable p (local s p) f0 (sp_proposer msg) Hacc).
           ++ (* New messages. *)
              unfold sp_step_fn.
              destruct (sp_output (local s p)) as [o|] eqn:Hout; [simpl; constructor |].
              destruct (sp_accepted (local s p)) as [v|] eqn:Hacc_eq.
              ** destruct (Nat.eqb (sp_proposer f0) v); simpl; constructor.
              ** simpl. destruct (dest =? sp_proposer f0) eqn:Hdest_eq; [| constructor].
                 apply Nat.eqb_eq in Hdest_eq. subst dest.
                 constructor; [| constructor]. simpl. split.
                 { reflexivity. }
                 { rewrite p0_state. unfold sp_step_fn. rewrite Hout. rewrite Hacc_eq.
                   simpl. reflexivity. }
        -- (* Other queues unchanged. *)
           rewrite (H_net_other src0 dest Hsp (or_intror Hsrc0)).
           eapply Forall_impl.
           2: exact (IHHs src0 dest src0_valid dest_valid).
           intros msg [Hsrc Hacc]. split; [exact Hsrc |].
           rewrite (other_state src0 Hsp). exact Hacc.
Qed.

Lemma nodup_in_acceptors :
  forall s,
    SP_Reachable s ->
    forall p, p < n -> NoDup (sp_acceptors (local s p)).
Proof.
  intros s Hs p p_valid. induction Hs; simpl in H.
  - (* Init *)
    unfold sp_init in H. destruct H as [[_ [_ [init_prop_acc init_nonprop_acc]]] _].
    destruct (classic (is_proposer p)) as [Hprop | Hprop].
    + (* Proposers. *)
      rewrite (init_prop_acc p p_valid Hprop).
      apply NoDup_cons; [intro Hin; exact Hin | constructor].
    + (* Non-proposers. *)
      rewrite (init_nonprop_acc p p_valid Hprop). constructor.
  - (* Step *)
    unfold step, sp_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) as [| f0 ] eqn:src_net.
    + (* No message delivered. *)
      unfold state_eq in H. destruct H as [local_eq _].
      rewrite local_eq. exact IHHs.
    + destruct H as [[p0_state other_state] _].
      destruct (classic (p = p0)).
      * (* state of the running process. *)
        destruct H. rewrite p0_state. unfold sp_step_fn.
        destruct (sp_output (local s p)).
        -- (* Output already set. *)
           simpl. exact IHHs.
        -- destruct (sp_accepted (local s p)) eqn:prev_acc.
          ++ destruct (Nat.eqb (sp_proposer f0) p0).
            ** (* Proposer matches. *)
              simpl.
              destruct (existsb (Nat.eqb (sp_source f0)) (sp_acceptors (local s p))) eqn:Hexists; try exact IHHs.
              apply NoDup_cons; try exact IHHs.
              intro Hin.
              assert (existsb (Nat.eqb (sp_source f0)) (sp_acceptors (local s p)) = true)
                as Hcontra
                by (apply existsb_exists; exists (sp_source f0);
                    split; [exact Hin | apply Nat.eqb_refl]).
              rewrite Hexists in Hcontra. discriminate.
            ** (* Proposer doesn't match. *)
                simpl. exact IHHs.
          ++ (* Not yet accepted: new acceptors list is []. *)
            simpl. constructor.
      * (* other process states are unchanged. *)
        rewrite (other_state p H). exact IHHs.
Qed.

(** Every process in p's acceptor list has also accepted p's value. *)
Lemma all_acceptors_have_accepted :
  forall s,
    SP_Reachable s ->
    forall p v, p < n ->
      sp_accepted (local s p) = Some v ->
      forall r, In r (sp_acceptors (local s p)) ->
        sp_accepted (local s r) = Some v.
Proof.
  intros s Hs p. induction Hs; simpl in H.
  - unfold sp_init in H.
    destruct H as [[_ [[prop_acc nonprop_acc] [prop_accs nonprop_accs]]] _].
    intros v p_valid Hacc r Hr.
    destruct (classic (is_proposer p)) as [Hprop | Hprop].
    + rewrite (prop_accs p p_valid Hprop) in Hr.
      simpl in Hr. destruct Hr as [Heq | []]. subst r. exact Hacc.
    + rewrite (nonprop_accs p p_valid Hprop) in Hr. destruct Hr.
  - unfold step, sp_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) as [| f0 ] eqn:src_net.
    + unfold state_eq in H. destruct H as [local_eq _].
      intros v p_valid Hacc r Hr.
      rewrite (local_eq p) in Hacc, Hr. rewrite (local_eq r).
      exact (IHHs v p_valid Hacc r Hr).
    + destruct H as [[p0_state other_state] _].
      pose proof (msg_src_has_accepted s Hs src p0 src_valid p0_valid) as Hmsg.
      rewrite src_net in Hmsg. apply Forall_inv in Hmsg.
      destruct Hmsg as [Hsrc_f0 Hacc_src].
      intros v p_valid Hacc r Hr.
      destruct (classic (p = p0)) as [Hpp0 | Hpp0].
      * subst p0. rewrite p0_state in Hacc, Hr.
        unfold sp_step_fn in Hacc, Hr.
        destruct (sp_output (local s p)) as [o|] eqn:Hout.
        -- simpl in Hacc, Hr.
           pose proof (IHHs v p_valid Hacc r Hr) as Hrfp.
           destruct (classic (r = p)) as [Hrp | Hrp].
           ++ subst r. rewrite p0_state.
              exact (accepted_stable p (local s p) f0 v Hrfp).
           ++ rewrite (other_state r Hrp). exact Hrfp.
        -- destruct (sp_accepted (local s p)) as [w|] eqn:Hacc_p.
          ++ destruct (Nat.eqb (sp_proposer f0) w) eqn:Hprop.
            ** apply Nat.eqb_eq in Hprop.
              simpl in Hacc. injection Hacc as Hwv. subst v.
              simpl in Hr.
              destruct (existsb (Nat.eqb (sp_source f0)) (sp_acceptors (local s p))) eqn:Hexists.
              { simpl in Hr.
                pose proof (IHHs w p_valid eq_refl r Hr) as Hrfp.
                destruct (classic (r = p)) as [Hrp | Hrp].
                - subst r. rewrite p0_state.
                  exact (accepted_stable p (local s p) f0 w Hrfp).
                - rewrite (other_state r Hrp). exact Hrfp. }
              { simpl in Hr. destruct Hr as [Heq | Hr_old].
                - rewrite <- Heq. rewrite Hsrc_f0.
                  rewrite (other_state src p_not_src). congruence.
                - pose proof (IHHs w p_valid eq_refl r Hr_old) as Hrfp.
                  destruct (classic (r = p)) as [Hrp | Hrp].
                  + subst r. rewrite p0_state.
                    exact (accepted_stable p (local s p) f0 w Hrfp).
                  + rewrite (other_state r Hrp). exact Hrfp. }
            ** simpl in Hacc, Hr.
              assert (Hvw : w = v) by congruence.
              subst v.
              pose proof (IHHs w p_valid eq_refl r Hr) as Hrfp.
              destruct (classic (r = p)) as [Hrp | Hrp].
              { subst r. rewrite p0_state.
                exact (accepted_stable p (local s p) f0 w Hrfp). }
              { rewrite (other_state r Hrp). exact Hrfp. }
          ++ simpl in Hr. destruct Hr.
      * rewrite (other_state p Hpp0) in Hacc, Hr.
        pose proof (IHHs v p_valid Hacc r Hr) as Hrfp.
        destruct (classic (r = p0)) as [Hrp0 | Hrp0].
        -- subst r. rewrite p0_state.
          exact (accepted_stable p0 (local s p0) f0 v Hrfp).
        -- rewrite (other_state r Hrp0). exact Hrfp.
Qed.

Lemma commit_implies_accepted :
  forall s, SP_Reachable s ->
  forall p v, p < n ->
    sp_output (local s p) = Some (Commit v) ->
    sp_accepted (local s p) = Some v.
Proof.
  intros s Hs p. induction Hs; simpl in H.
  - unfold sp_init in H. destruct H as [[init_noout _] _].
    intros v p_valid Hout. rewrite (init_noout p) in Hout. discriminate.
  - unfold step, sp_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) as [| f0 ] eqn:src_net.
    + unfold state_eq in H. destruct H as [local_eq _].
      intros v p_valid Hout. rewrite (local_eq p) in Hout.
      rewrite (local_eq p). exact (IHHs v p_valid Hout).
    + destruct H as [[p0_state other_state] _].
      intros v p_valid Hout.
      destruct (classic (p = p0)) as [Hpp0 | Hpp0].
      * subst p0. rewrite p0_state in Hout.
        unfold sp_step_fn in Hout.
        destruct (sp_output (local s p)) as [o|] eqn:Hprev_out.
        -- simpl in Hout.
          assert (Ho : Some o = Some (Commit v)) by congruence.
          rewrite p0_state. unfold sp_step_fn. rewrite Hprev_out. simpl.
          exact (IHHs v p_valid Ho).
        -- destruct (sp_accepted (local s p)) as [w|] eqn:Hacc_p.
          ++ destruct (Nat.eqb (sp_proposer f0) w) eqn:Hprop.
            ** apply Nat.eqb_eq in Hprop. subst w.
              simpl in Hout.
              destruct (sp_quorum <=? length _) eqn:Hle.
              { injection Hout as Hveq. subst v.
                rewrite p0_state. unfold sp_step_fn. rewrite Hprev_out. rewrite Hacc_p.
                rewrite Nat.eqb_refl. simpl. reflexivity. }
              { discriminate. }
            ** simpl in Hout. rewrite Hprev_out in Hout. discriminate.
          ++ simpl in Hout. discriminate.
      * rewrite (other_state p Hpp0) in Hout.
        rewrite (other_state p Hpp0).
        exact (IHHs v p_valid Hout).
Qed.

Lemma commit_implies_quorum :
  forall s, SP_Reachable s ->
  forall p v, p < n ->
    sp_output (local s p) = Some (Commit v) ->
    sp_quorum <= length (sp_acceptors (local s p)).
Proof.
  intros s Hs p. induction Hs; simpl in H.
  - unfold sp_init in H. destruct H as [[init_noout _] _].
    intros v p_valid Hout. rewrite (init_noout p) in Hout. discriminate.
  - unfold step, sp_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) as [| f0 ] eqn:src_net.
    + unfold state_eq in H. destruct H as [local_eq _].
      intros v p_valid Hout. rewrite (local_eq p) in Hout.
      rewrite (local_eq p). exact (IHHs v p_valid Hout).
    + destruct H as [[p0_state other_state] _].
      intros v p_valid Hout.
      destruct (classic (p = p0)) as [Hpp0 | Hpp0].
      * subst p0. rewrite p0_state in Hout.
        unfold sp_step_fn in Hout.
        destruct (sp_output (local s p)) as [o|] eqn:Hprev_out.
        -- simpl in Hout.
          assert (Ho : Some o = Some (Commit v)) by congruence.
          rewrite p0_state. unfold sp_step_fn. rewrite Hprev_out. simpl.
          exact (IHHs v p_valid Ho).
        -- destruct (sp_accepted (local s p)) as [w|] eqn:Hacc_p.
          ++ destruct (Nat.eqb (sp_proposer f0) w) eqn:Hprop.
            ** apply Nat.eqb_eq in Hprop. subst w.
              simpl in Hout.
              destruct (sp_quorum <=? length _) eqn:Hle.
              { rewrite p0_state. unfold sp_step_fn. rewrite Hprev_out. rewrite Hacc_p.
                rewrite Nat.eqb_refl. simpl.
                apply Nat.leb_le. exact Hle. }
              { discriminate. }
            ** simpl in Hout. rewrite Hprev_out in Hout. discriminate.
          ++ simpl in Hout. discriminate.
      * rewrite (other_state p Hpp0) in Hout.
        rewrite (other_state p Hpp0).
        exact (IHHs v p_valid Hout).
Qed.

Lemma all_acceptors_are_valid :
  forall s, SP_Reachable s ->
  forall p, p < n ->
  forall r, In r (sp_acceptors (local s p)) -> r < n.
Proof.
  intros s Hs p. induction Hs; simpl in H.
  - unfold sp_init in H.
    destruct H as [[_ [_ [prop_accs nonprop_accs]]] _].
    intros p_valid r Hr.
    destruct (classic (is_proposer p)) as [Hprop | Hprop].
    + rewrite (prop_accs p p_valid Hprop) in Hr.
      simpl in Hr. destruct Hr as [Heq | []]. subst r. exact p_valid.
    + rewrite (nonprop_accs p p_valid Hprop) in Hr. destruct Hr.
  - unfold step, sp_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) as [| f0 ] eqn:src_net.
    + unfold state_eq in H. destruct H as [local_eq _].
      intros p_valid r Hr. rewrite (local_eq p) in Hr.
      exact (IHHs p_valid r Hr).
    + destruct H as [[p0_state other_state] _].
      pose proof (msg_src_has_accepted s Hs src p0 src_valid p0_valid) as Hmsg.
      rewrite src_net in Hmsg. apply Forall_inv in Hmsg.
      destruct Hmsg as [Hsrc_f0 _].
      intros p_valid r Hr.
      destruct (classic (p = p0)) as [Hpp0 | Hpp0].
      * subst p0. rewrite p0_state in Hr. unfold sp_step_fn in Hr.
        destruct (sp_output (local s p)).
        -- simpl in Hr. exact (IHHs p_valid r Hr).
        -- destruct (sp_accepted (local s p)) as [w|] eqn:Hacc_p.
          ++ destruct (Nat.eqb (sp_proposer f0) w) eqn:Hprop.
            ** simpl in Hr.
              destruct (existsb (Nat.eqb (sp_source f0)) (sp_acceptors (local s p))) eqn:Hexists.
              { simpl in Hr. exact (IHHs p_valid r Hr). }
              { simpl in Hr. destruct Hr as [Heq | Hr_old].
                - subst r. rewrite Hsrc_f0. exact src_valid.
                - exact (IHHs p_valid r Hr_old). }
            ** simpl in Hr. exact (IHHs p_valid r Hr).
          ++ simpl in Hr. destruct Hr.
      * rewrite (other_state p Hpp0) in Hr.
        exact (IHHs p_valid r Hr).
Qed.

(** Key lemma: two fast quorums must intersect. *)
Lemma sp_quorum_gt_half : n < 2 * sp_quorum.
Proof.
  unfold sp_quorum.
  rewrite n_eq_2f_plus_1.
  pose proof (Nat.div_mod (f + 1) 2 ltac:(lia)) as H1.
  pose proof (Nat.mod_upper_bound (f + 1) 2 ltac:(lia)) as H2.
  lia.
Qed.

Lemma quorum_intersection :
  forall (A B : list ProcessId),
    NoDup A -> (forall a, In a A -> a < n) ->
    NoDup B -> (forall b, In b B -> b < n) ->
    sp_quorum <= length A -> sp_quorum <= length B ->
    exists r, In r A /\ In r B.
Proof.
  intros A B Hnd_A Hval_A Hnd_B Hval_B Hlen_A Hlen_B.
  apply Classical_Pred_Type.not_all_not_ex.
  intro Hall.
  assert (Hdisj : forall r, In r A -> ~ In r B).
  { intros r Hr HrB. exact (Hall r (conj Hr HrB)). }
  assert (Hnd_AB : NoDup (A ++ B)).
  { apply NoDup_app; auto. }
  assert (Hincl : incl (A ++ B) (seq 0 n)).
  { intros x Hx. apply in_app_iff in Hx.
    apply in_seq. split; [lia |].
    destruct Hx as [Hx | Hx]; [exact (Hval_A x Hx) | exact (Hval_B x Hx)]. }
  pose proof (NoDup_incl_length Hnd_AB Hincl) as Hle.
  rewrite length_app, length_seq in Hle.
  pose proof sp_quorum_gt_half.
  lia.
Qed.

Lemma no_adopt :
  forall s, SP_Reachable s ->
  forall q w, q < n ->
    sp_output (local s q) <> Some (Adopt w).
Proof.
  intros s Hs q. induction Hs; simpl in H.
  - unfold sp_init in H. destruct H as [[init_noout _] _].
    intros w q_valid Hq. rewrite (init_noout q) in Hq. discriminate.
  - unfold step, sp_instance in H; simpl in H.
    destruct H as [[_ [_ p_valid]] H].
    intros w q_valid Hq.
    destruct (network s src p) as [| f0 ] eqn:src_net.
    + unfold state_eq in H. destruct H as [local_eq _].
      rewrite (local_eq q) in Hq. exact (IHHs w q_valid Hq).
    + destruct H as [[p_state other_state] _].
      destruct (classic (q = p)) as [Hqp | Hqp].
      * subst p. rewrite p_state in Hq. unfold sp_step_fn in Hq.
        destruct (sp_output (local s q)) as [o|] eqn:Hprev.
        -- simpl in Hq. exact (IHHs w q_valid (eq_trans (eq_sym Hprev) Hq)).
        -- destruct (sp_accepted (local s q)).
          ++ destruct (Nat.eqb _ _).
            ** simpl in Hq. destruct (sp_quorum <=? _); discriminate.
            ** simpl in Hq. exact (IHHs w q_valid (eq_trans (eq_sym Hprev) Hq)).
          ++ simpl in Hq. discriminate.
      * rewrite (other_state q Hqp) in Hq. exact (IHHs w q_valid Hq).
Qed.

Theorem SwiftPaxos_Agreement : Agreement n sp_instance.
Proof.
  unfold Agreement, sp_instance, output_of, valid_pid, acp_proc_output; simpl.
  intros s p q v w Hs p_valid q_valid Hp Hq.
  destruct Hq as [Hq | Hq].
  - pose proof (commit_implies_accepted s Hs p v p_valid Hp) as Hacc_p.
    pose proof (commit_implies_quorum s Hs p v p_valid Hp) as Hquorum_p.
    pose proof (commit_implies_accepted s Hs q w q_valid Hq) as Hacc_q.
    pose proof (commit_implies_quorum s Hs q w q_valid Hq) as Hquorum_q.
    pose proof (nodup_in_acceptors s Hs p p_valid) as Hnd_p.
    pose proof (nodup_in_acceptors s Hs q q_valid) as Hnd_q.
    pose proof (fun r Hr => all_acceptors_are_valid s Hs p p_valid r Hr) as Hval_p.
    pose proof (fun r Hr => all_acceptors_are_valid s Hs q q_valid r Hr) as Hval_q.
    destruct (quorum_intersection
                (sp_acceptors (local s p)) (sp_acceptors (local s q))
                Hnd_p Hval_p Hnd_q Hval_q Hquorum_p Hquorum_q)
      as [r [HrA HrB]].
    pose proof (all_acceptors_have_accepted s Hs p v p_valid Hacc_p r HrA) as Hrv.
    pose proof (all_acceptors_have_accepted s Hs q w q_valid Hacc_q r HrB) as Hrw.
    congruence.
  - destruct (no_adopt s Hs q w q_valid Hq).
Qed.

Theorem SwiftPaxos_Convergence : Convergence n sp_instance.
Proof.
  unfold Convergence, sp_instance, output_of, valid_pid, acp_proc_output, acp_is_proposer; simpl.
  intros s p q o Hs p_valid q_valid Hprop Huniq Hout.
  pose proof (all_output_values_valid s Hs q q_valid) as Hvalid.
  rewrite Hout in Hvalid.
  destruct o as [v | v].
  - f_equal. exact (Huniq v Hvalid).
  - destruct (no_adopt s Hs q v q_valid Hout).
Qed.

(** Any committed process has a valid PID (< n). *)
Lemma sp_commit_pid_valid :
  forall s, SP_Reachable s ->
  forall p v, sp_output (local s p) = Some (Commit v) -> p < n.
Proof.
  intros s Hs p v. induction Hs; simpl in H.
  - unfold sp_init in H. destruct H as [[init_noout _] _].
    intro Hout. rewrite (init_noout p) in Hout. discriminate.
  - unfold step, sp_instance in H; simpl in H.
    destruct H as [[_ [_ p0_valid]] H].
    intro Hout.
    destruct (network s src p0) as [| f0 ] eqn:src_net.
    + unfold state_eq in H. destruct H as [local_eq _].
      rewrite (local_eq p) in Hout. exact (IHHs Hout).
    + destruct H as [[p0_state other_state] _].
      destruct (classic (p = p0)) as [Hpp0 | Hpp0].
      * subst p0. exact p0_valid.
      * rewrite (other_state p Hpp0) in Hout. exact (IHHs Hout).
Qed.

(** General pigeonhole: two NoDup lists over {0..m-1} whose sizes sum to > m must share an element. *)
Lemma list_intersection :
  forall (A B : list ProcessId) (m : nat),
    NoDup A -> (forall a, In a A -> a < m) ->
    NoDup B -> (forall b, In b B -> b < m) ->
    m < length A + length B ->
    exists r, In r A /\ In r B.
Proof.
  intros A B m Hnd_A Hval_A Hnd_B Hval_B Hlt.
  apply Classical_Pred_Type.not_all_not_ex.
  intro Hall.
  assert (Hdisj : forall r, In r A -> ~ In r B).
  { intros r Hr HrB. exact (Hall r (conj Hr HrB)). }
  assert (Hnd_AB : NoDup (A ++ B)) by (apply NoDup_app; auto).
  assert (Hincl : incl (A ++ B) (seq 0 m)).
  { intros x Hx. apply in_app_iff in Hx.
    apply in_seq. split; [lia |].
    destruct Hx; [exact (Hval_A x H) | exact (Hval_B x H)]. }
  pose proof (NoDup_incl_length Hnd_AB Hincl) as Hle.
  rewrite length_app, length_seq in Hle. lia.
Qed.

(** The intersection of two NoDup bounded-nat lists has size at least |A| + |B| - m. *)
Lemma filter_inter_lb :
  forall (A B : list ProcessId) (m : nat),
    NoDup A -> (forall a, In a A -> a < m) ->
    NoDup B -> (forall b, In b B -> b < m) ->
    length A + length B <= m + length (filter (fun a => existsb (Nat.eqb a) B) A).
Proof.
  intros A B m Hnd_A Hval_A Hnd_B Hval_B.
  set (f_in := fun a => existsb (Nat.eqb a) B).
  set (D := filter (fun a => negb (f_in a)) A).
  assert (H_part : length (filter f_in A) + length D = length A).
  { unfold D. exact (filter_length f_in A). }
  assert (Hnd_D : NoDup D) by (apply NoDup_filter; exact Hnd_A).
  assert (Hincl_D : incl D (filter (fun x => negb (f_in x)) (seq 0 m))).
  { intros x Hx. apply filter_In in Hx as [HxA HxnB].
    apply filter_In. split.
    - apply in_seq. split; [lia | exact (Hval_A x HxA)].
    - exact HxnB. }
  assert (Hlen_D : length D <= length (filter (fun x => negb (f_in x)) (seq 0 m)))
    by exact (NoDup_incl_length Hnd_D Hincl_D).
  assert (Hseq_B : length (filter f_in (seq 0 m)) = length B).
  { apply Nat.le_antisymm.
    - apply NoDup_incl_length; [apply NoDup_filter, seq_NoDup |].
      intros x Hx. apply filter_In in Hx as [_ HxB].
      unfold f_in in HxB. apply existsb_exists in HxB as [y [HyB Heq]].
      apply Nat.eqb_eq in Heq. subst y. exact HyB.
    - apply NoDup_incl_length; [exact Hnd_B |].
      intros b Hb. apply filter_In. split.
      + apply in_seq. split; [lia | exact (Hval_B b Hb)].
      + unfold f_in. apply existsb_exists. exists b. split; [exact Hb | apply Nat.eqb_refl]. }
  pose proof (filter_length f_in (seq 0 m)) as H_seq_part.
  rewrite length_seq, Hseq_B in H_seq_part.
  lia.
Qed.

Theorem SwiftPaxos_Recoverability : Recoverability n f sp_instance.
Proof.
  unfold Recoverability, sp_instance, output_of, valid_pid, acp_proc_output; simpl.
  intros s s' alive v w Hs Hs' Hnd_alive Hlen_alive Hval_alive Hlocal_eq [p Hp] [q Hq].
  pose proof (sp_commit_pid_valid s Hs p v Hp) as p_valid.
  pose proof (sp_commit_pid_valid s' Hs' q w Hq) as q_valid.
  pose proof (commit_implies_accepted s Hs p v p_valid Hp) as Hacc_p.
  pose proof (commit_implies_quorum s Hs p v p_valid Hp) as Hquorum_p.
  pose proof (nodup_in_acceptors s Hs p p_valid) as Hnd_Ap.
  pose proof (fun r Hr => all_acceptors_are_valid s Hs p p_valid r Hr) as Hval_Ap.
  pose proof (fun r Hr => all_acceptors_have_accepted s Hs p v p_valid Hacc_p r Hr) as Hacc_Ap.
  pose proof (commit_implies_accepted s' Hs' q w q_valid Hq) as Hacc_q.
  pose proof (commit_implies_quorum s' Hs' q w q_valid Hq) as Hquorum_q.
  pose proof (nodup_in_acceptors s' Hs' q q_valid) as Hnd_Aq.
  pose proof (fun r Hr => all_acceptors_are_valid s' Hs' q q_valid r Hr) as Hval_Aq.
  pose proof (fun r Hr => all_acceptors_have_accepted s' Hs' q w q_valid Hacc_q r Hr) as Hacc_Aq.
  (* B = alive processes that are in q's acceptor list in s' *)
  set (B := filter (fun r => existsb (Nat.eqb r) alive) (sp_acceptors (local s' q))).
  assert (Hnd_B : NoDup B) by (apply NoDup_filter; exact Hnd_Aq).
  assert (Hval_B : forall r, In r B -> r < n).
  { intros r Hr. apply filter_In in Hr as [Hr _]. exact (Hval_Aq r Hr). }
  (* Every r in B has sp_accepted(s, r) = Some w *)
  assert (Hacc_B : forall r, In r B -> sp_accepted (local s r) = Some w).
  { intros r Hr.
    apply filter_In in Hr as [HrAq Hr_alive].
    apply existsb_exists in Hr_alive as [r' [Hr'alive Heq]].
    apply Nat.eqb_eq in Heq. subst r'.
    rewrite (Hlocal_eq r Hr'alive). exact (Hacc_Aq r HrAq). }
  (* |A_q(s')| + |alive| <= n + |B|, so |B| is large *)
  pose proof (filter_inter_lb (sp_acceptors (local s' q)) alive n
                Hnd_Aq Hval_Aq Hnd_alive Hval_alive) as Hlen_B.
  fold B in Hlen_B.
  (* n < |A_p(s)| + |B| by arithmetic on quorum sizes *)
  assert (Hsum : n < length (sp_acceptors (local s p)) + length B).
  { unfold sp_quorum in *.
    rewrite n_eq_2f_plus_1 in *.
    pose proof (Nat.div_mod (f + 1) 2 ltac:(lia)) as Hdiv.
    pose proof (Nat.mod_upper_bound (f + 1) 2 ltac:(lia)) as Hmod.
    lia. }
  (* Get witness r in A_p(s) inter B *)
  destruct (list_intersection (sp_acceptors (local s p)) B n
              Hnd_Ap Hval_Ap Hnd_B Hval_B Hsum) as [r [HrAp HrB]].
  pose proof (Hacc_Ap r HrAp) as Hrv.
  pose proof (Hacc_B r HrB) as Hrw.
  congruence.
Qed.

End SP.
