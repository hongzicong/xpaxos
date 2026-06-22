(** * Fast-path-only adopt-commit model for EPaxos

    Protocol-specific analysis:

    - A value [v] denotes the command led by replica [v].  Every proposer
      initially pre-accepts its own command and sends PreAccept messages.
    - A replica that has not pre-accepted a command may pre-accept the first
      command it receives and acknowledge that command to its command leader.
      Pre-accepted values are stable, so a replica acknowledges at most one
      command in this abstraction.
    - Unlike Fast Paxos, an EPaxos command is committed only by its command
      leader.  Thus only process [v] may output [Commit v]; acknowledgers never
      commit another leader's command and this fast-path-only model has no
      [Adopt] transition.
    - The certificate stored by leader [v] contains the leader itself plus the
      replicas whose matching PreAccept acknowledgments it received.  A commit
      requires [f + floor ((f + 1) / 2)] certificate members, under
      [n = 2 * f + 1].
    - Because leader [p] starts pre-accepted on [p] and acceptance is stable,
      it can never acknowledge a different value.  Consequently, for distinct
      committed values [v] and [w], neither leader belongs to the intersection
      of their certificates.
    - Validity follows from message-value preservation.  Agreement follows
      from intersection of two fast certificates and stable pre-acceptance.
      Convergence follows because the model emits no [Adopt] outputs.
    - Recoverability cannot use the FastPaxos live-quorum intersection proof:
      the optimized fast quorum may leave too few live certificate members.
      Instead, if distinct values are committed in states equal on [alive],
      both leaders and every member of the certificate intersection are
      non-alive.  The full witness list
        [leader v; leader w] ++ (Av intersect Aw)
      is duplicate-free and has size at least
        2 + (2 * ep_quorum - n)
      which equals [2 * floor ((f + 1) / 2) + 1] and is greater than [f].

    This deliberately omits dependency/sequence attributes, the slow path,
    execution, and recovery protocol; it captures only the fast-path quorum
    evidence needed by the adopt-commit framework. *)

From Stdlib Require Import List Arith Bool Classical Lia.
Import ListNotations.

Require Import AdoptCommit.

Record EPMsg := mkEPMsg {
  ep_source : ProcessId;
  ep_value  : ProcessId
}.

Record EPState := mkEPState {
  ep_accepted : option ProcessId;
  ep_acceptors : list ProcessId;
  ep_output : option ACOutput
}.

Section EP.

Variable n : nat.
Hypothesis n_pos : 0 < n.
Variable f : nat.
Hypothesis f_lt_n : f < n.

(** EPaxos assumes [N = 2F + 1].  We also exclude the degenerate
    zero-failure configuration; the paper's optimized quorum and the
    intended distributed setting both start with at least three replicas. *)
Hypothesis ep_n_eq : n = 2 * f + 1.
Hypothesis ep_f_pos : 0 < f.

Variable is_proposer : ProcessId -> Prop.
Hypothesis exists_proposer : exists p, p < n /\ is_proposer p.

Definition ep_quorum : nat := f + (f + 1) / 2.

Definition ep_step_fn
    (p : ProcessId) (ls : EPState) (m : EPMsg)
    : EPState * (ProcessId -> list EPMsg) :=
  match ep_output ls with
  | Some _ => (ls, fun _ => [])
  | None =>
      match ep_accepted ls with
      | None =>
          (mkEPState (Some (ep_value m)) [] None,
           fun dst =>
             if Nat.eqb dst (ep_value m)
             then [mkEPMsg p (ep_value m)]
             else [])
      | Some v =>
          if andb (Nat.eqb p v) (Nat.eqb (ep_value m) v) then
            let new_acceptors :=
              if existsb (Nat.eqb (ep_source m)) (ep_acceptors ls)
              then ep_acceptors ls
              else ep_source m :: ep_acceptors ls in
            let new_output :=
              if ep_quorum <=? length new_acceptors
              then Some (Commit v)
              else None in
            (mkEPState (Some v) new_acceptors new_output, fun _ => [])
          else (ls, fun _ => [])
      end
  end.

Definition ep_init (s : GlobalState EPMsg EPState) : Prop :=
  ((forall p, ep_output (local s p) = None) /\
   ((forall p, p < n -> is_proposer p ->
       ep_accepted (local s p) = Some p) /\
    (forall p, p < n -> ~ is_proposer p ->
       ep_accepted (local s p) = None)) /\
   ((forall p, p < n -> is_proposer p ->
       ep_acceptors (local s p) = [p]) /\
    (forall p, p < n -> ~ is_proposer p ->
       ep_acceptors (local s p) = []))) /\
  (((forall p q, p < n -> q < n -> p <> q -> is_proposer p ->
       network s p q = [mkEPMsg p p]) /\
    (forall p q, p < n -> q < n -> ~ is_proposer p ->
       network s p q = [])) /\
   (forall p, p < n -> network s p p = [])).

Definition ep_instance : ACProtocol :=
  mkACProtocol ep_output is_proposer ep_init ep_step_fn.

Definition EP_GlobalState := GlobalState EPMsg EPState.
Definition EP_Reachable := Reachable n ep_instance.

(** Small-case arithmetic audit for [f = 1,2,3,4]:
    [n] is [3,5,7,9], [ep_quorum] is [2,3,5,6],
    and [2 * ep_quorum - n] is [1,1,3,3].
    Hence two fast certificates intersect, but their intersection alone is
    not larger than [f] (notably [f=2]); Recoverability must count both
    leaders in addition to the intersection. *)

Lemma ep_output_stable :
  forall p ls m o,
    ep_output ls = Some o ->
    ep_output (fst (ep_step_fn p ls m)) = Some o.
Proof.
  intros p ls m o Hout.
  unfold ep_step_fn. rewrite Hout. simpl. exact Hout.
Qed.

Lemma ep_all_message_values_valid :
  forall s,
    EP_Reachable s ->
    forall src dst,
      src < n -> dst < n ->
      Forall (fun m => is_proposer (ep_value m)) (network s src dst).
Proof.
  intros s Hreach. induction Hreach; simpl in H.
  - unfold ep_init in H.
    destruct H as [_ [[Hprop Hnonprop] Hself]].
    intros src dst Hsrc Hdst.
    destruct (classic (is_proposer src)) as [Hp | Hp].
    + destruct (classic (src = dst)) as [Heq | Hneq].
      * subst dst. rewrite (Hself src Hsrc). constructor.
      * rewrite (Hprop src dst Hsrc Hdst Hneq Hp).
        constructor; [exact Hp | constructor].
    + rewrite (Hnonprop src dst Hsrc Hdst Hp). constructor.
  - unfold step, ep_instance in H; simpl in H.
    destruct H as [[Hpneq [Hsrc Hp]] H].
    destruct (network s src p) as [|m rest] eqn:Hqueue.
    + unfold state_eq in H. destruct H as [_ Hnet].
      intros src0 dst Hsrc0 Hdst. rewrite Hnet.
      exact (IHHreach src0 dst Hsrc0 Hdst).
    + destruct H as [_ [Hin [Hout Hother]]].
      intros src0 dst Hsrc0 Hdst.
      destruct (classic (src0 = src)) as [Heqsrc | Hsrc0src].
      * subst src0. destruct (classic (dst = p)) as [Heqdst | Hdstp].
        -- subst dst.
           rewrite Hin.
           pose proof (IHHreach src p Hsrc Hp) as Hmsgs.
           rewrite Hqueue in Hmsgs. exact (Forall_inv_tail Hmsgs).
        -- rewrite Hother; [exact (IHHreach src dst Hsrc Hdst) | exact Hpneq |].
           left; exact Hdstp.
      * destruct (classic (src0 = p)) as [Heqsrc0 | Hsrc0p].
        -- subst src0. rewrite Hout, Forall_app. split.
           ++ exact (IHHreach p dst Hp Hdst).
           ++ unfold ep_step_fn.
              destruct (ep_output (local s p)) eqn:Houtprev;
                [constructor |].
              destruct (ep_accepted (local s p)) as [v|].
              ** destruct (andb (Nat.eqb p v) (Nat.eqb (ep_value m) v));
                   constructor.
              ** simpl. destruct (dst =? ep_value m) eqn:Heq; [|constructor].
                 apply Nat.eqb_eq in Heq. subst dst.
                 constructor; [|constructor].
                 pose proof (IHHreach src p Hsrc Hp) as Hmsgs.
                 rewrite Hqueue in Hmsgs. exact (Forall_inv Hmsgs).
        -- rewrite Hother; [exact (IHHreach src0 dst Hsrc0 Hdst) | exact Hsrc0p |].
           right; exact Hsrc0src.
Qed.

Lemma ep_all_accepted_values_valid :
  forall s,
    EP_Reachable s ->
    forall p, p < n ->
      match ep_accepted (local s p) with
      | None => True
      | Some v => is_proposer v
      end.
Proof.
  intros s Hreach p Hp. induction Hreach; simpl in H.
  - unfold ep_init in H.
    destruct H as [[_ [[Hprop Hnonprop] _]] _].
    destruct (classic (is_proposer p)) as [Hisp | Hn].
    + rewrite (Hprop p Hp Hisp). exact Hisp.
    + rewrite (Hnonprop p Hp Hn). exact I.
  - unfold step, ep_instance in H; simpl in H.
    destruct H as [[_ [Hsrc Hp0]] H].
    destruct (network s src p0) as [|m rest] eqn:Hqueue.
    + unfold state_eq in H. destruct H as [Hlocal _].
      rewrite Hlocal. exact IHHreach.
    + destruct H as [[Hstate Hothers] _].
      destruct (classic (p = p0)) as [-> | Hneq].
      * rewrite Hstate. unfold ep_step_fn.
        destruct (ep_output (local s p0)); [simpl; exact IHHreach |].
        destruct (ep_accepted (local s p0)) as [v|] eqn:Hacc.
        -- destruct (andb (Nat.eqb p0 v) (Nat.eqb (ep_value m) v))
             eqn:Hcond.
           ++ simpl. exact IHHreach.
           ++ simpl. rewrite Hacc. exact IHHreach.
        -- simpl.
           pose proof (ep_all_message_values_valid s Hreach src p0 Hsrc Hp0)
             as Hmsgs.
           rewrite Hqueue in Hmsgs. exact (Forall_inv Hmsgs).
      * rewrite (Hothers p Hneq). exact IHHreach.
Qed.

Lemma ep_accepted_stable :
  forall p ls m v,
    ep_accepted ls = Some v ->
    ep_accepted (fst (ep_step_fn p ls m)) = Some v.
Proof.
  intros p ls m v Hacc.
  unfold ep_step_fn.
  destruct (ep_output ls); [simpl; exact Hacc |].
  rewrite Hacc.
  destruct (andb (Nat.eqb p v) (Nat.eqb (ep_value m) v));
    simpl; [reflexivity | exact Hacc].
Qed.

Lemma ep_msg_source_accepted :
  forall s,
    EP_Reachable s ->
    forall src dst,
      src < n -> dst < n ->
      Forall (fun m => ep_source m = src /\
                       ep_accepted (local s src) = Some (ep_value m))
             (network s src dst).
Proof.
  intros s Hreach. induction Hreach; simpl in H.
  - unfold ep_init in H.
    destruct H as [[_ [[Hpropacc _] _]] [[Hprop Hnonprop] Hself]].
    intros src dst Hsrc Hdst.
    destruct (classic (is_proposer src)) as [Hp | Hp].
    + destruct (classic (src = dst)) as [Heq | Hneq].
      * subst dst. rewrite (Hself src Hsrc). constructor.
      * rewrite (Hprop src dst Hsrc Hdst Hneq Hp).
        constructor; [|constructor]. simpl. split; [reflexivity |].
        exact (Hpropacc src Hsrc Hp).
    + rewrite (Hnonprop src dst Hsrc Hdst Hp). constructor.
  - unfold step, ep_instance in H; simpl in H.
    destruct H as [[Hpneq [Hsrc Hp]] H].
    destruct (network s src p) as [|m rest] eqn:Hqueue.
    + unfold state_eq in H. destruct H as [Hlocal Hnet].
      intros src0 dst Hsrc0 Hdst. rewrite Hnet.
      eapply Forall_impl.
      2: exact (IHHreach src0 dst Hsrc0 Hdst).
      intros msg [Hs Ha]. split; [exact Hs | rewrite Hlocal; exact Ha].
    + destruct H as [[Hstate Hothers] [Hin [Hout Hother]]].
      intros src0 dst Hsrc0 Hdst.
      destruct (classic (src0 = src)) as [Heqsrc | Hsrcneq].
      * subst src0. destruct (classic (dst = p)) as [Heqdst | Hdstneq].
        -- subst dst. rewrite Hin.
           pose proof (IHHreach src p Hsrc Hp) as Hold.
           rewrite Hqueue in Hold. apply Forall_inv_tail in Hold.
           eapply Forall_impl; [|exact Hold].
           intros msg [Hs Ha]. split; [exact Hs |].
           rewrite (Hothers src Hpneq). exact Ha.
        -- rewrite (Hother src dst Hpneq (or_introl Hdstneq)).
           eapply Forall_impl; [|exact (IHHreach src dst Hsrc Hdst)].
           intros msg [Hs Ha]. split; [exact Hs |].
           rewrite (Hothers src Hpneq). exact Ha.
      * destruct (classic (src0 = p)) as [Heqsrc0 | Hsrc0neq].
        -- subst src0. rewrite Hout, Forall_app. split.
           ++ eapply Forall_impl; [|exact (IHHreach p dst Hp Hdst)].
              intros msg [Hs Ha]. split; [exact Hs |].
              rewrite Hstate. exact (ep_accepted_stable p (local s p) m _ Ha).
           ++ unfold ep_step_fn.
              destruct (ep_output (local s p)) eqn:Houtprev;
                [constructor |].
              destruct (ep_accepted (local s p)) as [v|] eqn:Hacc.
              ** destruct (andb (Nat.eqb p v) (Nat.eqb (ep_value m) v));
                   constructor.
              ** simpl. destruct (dst =? ep_value m) eqn:Heq;
                   [|constructor].
                 constructor; [|constructor]. simpl. split; [reflexivity |].
                 rewrite Hstate. unfold ep_step_fn.
                 rewrite Houtprev.
                 rewrite Hacc. reflexivity.
        -- rewrite (Hother src0 dst Hsrc0neq (or_intror Hsrcneq)).
           eapply Forall_impl; [|exact (IHHreach src0 dst Hsrc0 Hdst)].
           intros msg [Hs Ha]. split; [exact Hs |].
           rewrite (Hothers src0 Hsrc0neq). exact Ha.
Qed.

Lemma ep_acceptors_nodup :
  forall s,
    EP_Reachable s ->
    forall p, p < n -> NoDup (ep_acceptors (local s p)).
Proof.
  intros s Hreach p Hp. induction Hreach; simpl in H.
  - unfold ep_init in H.
    destruct H as [[_ [_ [Hprop Hnonprop]]] _].
    destruct (classic (is_proposer p)) as [Hisp | Hn].
    + rewrite (Hprop p Hp Hisp). repeat constructor; auto.
    + rewrite (Hnonprop p Hp Hn). constructor.
  - unfold step, ep_instance in H; simpl in H.
    destruct H as [[_ [_ Hp0]] H].
    destruct (network s src p0) as [|m rest] eqn:Hqueue.
    + unfold state_eq in H. destruct H as [Hlocal _].
      rewrite Hlocal. exact IHHreach.
    + destruct H as [[Hstate Hothers] _].
      destruct (classic (p = p0)) as [-> | Hneq].
      * rewrite Hstate. unfold ep_step_fn.
        destruct (ep_output (local s p0)); [simpl; exact IHHreach |].
        destruct (ep_accepted (local s p0)) as [v|].
        -- destruct (andb (Nat.eqb p0 v) (Nat.eqb (ep_value m) v)).
           ++ simpl.
              destruct (existsb (Nat.eqb (ep_source m))
                        (ep_acceptors (local s p0))) eqn:Hex.
              ** exact IHHreach.
              ** apply NoDup_cons; [|exact IHHreach].
                 intro Hin.
                 assert (existsb (Nat.eqb (ep_source m))
                           (ep_acceptors (local s p0)) = true) as Htrue.
                 { apply existsb_exists. exists (ep_source m).
                   split; [exact Hin | apply Nat.eqb_refl]. }
                 congruence.
           ++ simpl. exact IHHreach.
        -- simpl. constructor.
      * rewrite (Hothers p Hneq). exact IHHreach.
Qed.

Lemma ep_all_acceptors_accepted :
  forall s,
    EP_Reachable s ->
    forall p v, p < n ->
      ep_accepted (local s p) = Some v ->
      forall r, In r (ep_acceptors (local s p)) ->
        ep_accepted (local s r) = Some v.
Proof.
  intros s Hreach p. induction Hreach; simpl in H.
  - unfold ep_init in H.
    destruct H as [[_ [[_ _] [Hprop Hnonprop]]] _].
    intros v Hp Hacc r Hin.
    destruct (classic (is_proposer p)) as [Hisp | Hn].
    + rewrite (Hprop p Hp Hisp) in Hin.
      simpl in Hin. destruct Hin as [-> | []]. exact Hacc.
    + rewrite (Hnonprop p Hp Hn) in Hin. contradiction.
  - unfold step, ep_instance in H; simpl in H.
    destruct H as [[Hpneq [Hsrc Hp0]] H].
    destruct (network s src p0) as [|m rest] eqn:Hqueue.
    + unfold state_eq in H. destruct H as [Hlocal _].
      intros v Hp Hacc r Hin.
      rewrite Hlocal in Hacc, Hin. rewrite Hlocal.
      exact (IHHreach v Hp Hacc r Hin).
    + destruct H as [[Hstate Hothers] _].
      pose proof (ep_msg_source_accepted s Hreach src p0 Hsrc Hp0) as Hmsg.
      rewrite Hqueue in Hmsg. apply Forall_inv in Hmsg.
      destruct Hmsg as [Hsource Hsource_acc].
      intros v Hp Hacc r Hin.
      destruct (classic (p = p0)) as [Heq | Hneq].
      * subst p0. rewrite Hstate in Hacc, Hin.
        unfold ep_step_fn in Hacc, Hin.
        destruct (ep_output (local s p)) as [o|] eqn:Hout.
        -- simpl in Hacc, Hin.
           pose proof (IHHreach v Hp Hacc r Hin) as Hold.
           destruct (classic (r = p)) as [-> | Hr].
           ++ rewrite Hstate. exact (ep_accepted_stable p (local s p) m v Hold).
           ++ rewrite (Hothers r Hr). exact Hold.
        -- destruct (ep_accepted (local s p)) as [w|] eqn:Hpacc.
           ++ destruct (andb (Nat.eqb p w) (Nat.eqb (ep_value m) w))
                eqn:Hcond.
              ** simpl in Hacc, Hin. injection Hacc as Hwv. subst v.
                 apply andb_true_iff in Hcond as [_ Hvalue].
                 apply Nat.eqb_eq in Hvalue.
                 destruct (existsb (Nat.eqb (ep_source m))
                           (ep_acceptors (local s p))) eqn:Hex.
                 { pose proof (IHHreach w Hp eq_refl r Hin) as Hold.
                   destruct (classic (r = p)) as [-> | Hr].
                   - rewrite Hstate.
                     exact (ep_accepted_stable p (local s p) m w Hold).
                   - rewrite (Hothers r Hr). exact Hold. }
                 { simpl in Hin. destruct Hin as [Heqr | Hin].
                   - subst r. rewrite Hsource.
                     rewrite (Hothers src Hpneq).
                     rewrite Hvalue in Hsource_acc. exact Hsource_acc.
                   - pose proof (IHHreach w Hp eq_refl r Hin) as Hold.
                     destruct (classic (r = p)) as [-> | Hr].
                     + rewrite Hstate.
                       exact (ep_accepted_stable p (local s p) m w Hold).
                     + rewrite (Hothers r Hr). exact Hold. }
              ** simpl in Hacc, Hin.
                 assert (w = v) by congruence. subst v.
                 pose proof (IHHreach w Hp eq_refl r Hin) as Hold.
                 destruct (classic (r = p)) as [-> | Hr].
                 { rewrite Hstate.
                   exact (ep_accepted_stable p (local s p) m w Hold). }
                 { rewrite (Hothers r Hr). exact Hold. }
           ++ simpl in Hin. contradiction.
      * rewrite (Hothers p Hneq) in Hacc, Hin.
        pose proof (IHHreach v Hp Hacc r Hin) as Hold.
        destruct (classic (r = p0)) as [-> | Hr].
        -- rewrite Hstate.
           exact (ep_accepted_stable p0 (local s p0) m v Hold).
        -- rewrite (Hothers r Hr). exact Hold.
Qed.

Lemma ep_all_acceptors_valid :
  forall s,
    EP_Reachable s ->
    forall p, p < n ->
    forall r, In r (ep_acceptors (local s p)) -> r < n.
Proof.
  intros s Hreach p. induction Hreach; simpl in H.
  - unfold ep_init in H.
    destruct H as [[_ [_ [Hprop Hnonprop]]] _].
    intros Hp r Hin.
    destruct (classic (is_proposer p)) as [Hisp | Hn].
    + rewrite (Hprop p Hp Hisp) in Hin.
      simpl in Hin. destruct Hin as [-> | []]. exact Hp.
    + rewrite (Hnonprop p Hp Hn) in Hin. contradiction.
  - unfold step, ep_instance in H; simpl in H.
    destruct H as [[_ [Hsrc Hp0]] H].
    destruct (network s src p0) as [|m rest] eqn:Hqueue.
    + unfold state_eq in H. destruct H as [Hlocal _].
      intros Hp r Hin. rewrite Hlocal in Hin.
      exact (IHHreach Hp r Hin).
    + destruct H as [[Hstate Hothers] _].
      pose proof (ep_msg_source_accepted s Hreach src p0 Hsrc Hp0) as Hmsg.
      rewrite Hqueue in Hmsg. apply Forall_inv in Hmsg.
      destruct Hmsg as [Hsource _].
      intros Hp r Hin.
      destruct (classic (p = p0)) as [-> | Hneq].
      * rewrite Hstate in Hin. unfold ep_step_fn in Hin.
        destruct (ep_output (local s p0)); [exact (IHHreach Hp r Hin) |].
        destruct (ep_accepted (local s p0)) as [v|].
        -- destruct (andb (Nat.eqb p0 v) (Nat.eqb (ep_value m) v)).
           ++ simpl in Hin.
              destruct (existsb (Nat.eqb (ep_source m))
                        (ep_acceptors (local s p0))).
              ** exact (IHHreach Hp r Hin).
              ** simpl in Hin. destruct Hin as [Heq | Hin].
                 { subst r. rewrite Hsource. exact Hsrc. }
                 { exact (IHHreach Hp r Hin). }
           ++ exact (IHHreach Hp r Hin).
        -- contradiction.
      * rewrite (Hothers p Hneq) in Hin.
        exact (IHHreach Hp r Hin).
Qed.

Lemma ep_commit_only_at_leader :
  forall s,
    EP_Reachable s ->
    forall p v,
      ep_output (local s p) = Some (Commit v) -> p = v.
Proof.
  intros s Hreach p. induction Hreach; simpl in H.
  - unfold ep_init in H. destruct H as [[Hnone _] _].
    intros v Hout. rewrite (Hnone p) in Hout. discriminate.
  - unfold step, ep_instance in H; simpl in H.
    destruct H as [[_ [_ Hp0]] H].
    destruct (network s src p0) as [|m rest] eqn:Hqueue.
    + unfold state_eq in H. destruct H as [Hlocal _].
      intros v Hout. rewrite Hlocal in Hout.
      exact (IHHreach v Hout).
    + destruct H as [[Hstate Hothers] _].
      intros v Hout.
      destruct (classic (p = p0)) as [Heq | Hneq].
      * subst p0. rewrite Hstate in Hout. unfold ep_step_fn in Hout.
        destruct (ep_output (local s p)) as [o|] eqn:Hprev.
        -- simpl in Hout.
           apply (IHHreach v). congruence.
        -- destruct (ep_accepted (local s p)) as [w|] eqn:Hacc.
           ++ destruct (andb (Nat.eqb p w) (Nat.eqb (ep_value m) w))
                eqn:Hcond.
              ** simpl in Hout.
                 destruct (ep_quorum <=? length _) eqn:Hq;
                   [|discriminate].
                 injection Hout as Hvw. subst v.
                 apply andb_true_iff in Hcond as [Hpw _].
                 apply Nat.eqb_eq in Hpw. exact Hpw.
              ** simpl in Hout. rewrite Hprev in Hout. discriminate.
           ++ discriminate.
      * rewrite (Hothers p Hneq) in Hout.
        exact (IHHreach v Hout).
Qed.

Lemma ep_commit_pid_valid :
  forall s,
    EP_Reachable s ->
    forall p v,
      ep_output (local s p) = Some (Commit v) -> p < n.
Proof.
  intros s Hreach p. induction Hreach; simpl in H.
  - unfold ep_init in H. destruct H as [[Hnone _] _].
    intros v Hout. rewrite (Hnone p) in Hout. discriminate.
  - unfold step, ep_instance in H; simpl in H.
    destruct H as [[_ [_ Hp0]] H].
    destruct (network s src p0) as [|m rest] eqn:Hqueue.
    + unfold state_eq in H. destruct H as [Hlocal _].
      intros v Hout. rewrite Hlocal in Hout.
      exact (IHHreach v Hout).
    + destruct H as [[_ Hothers] _].
      intros v Hout.
      destruct (classic (p = p0)) as [-> | Hneq].
      * exact Hp0.
      * rewrite (Hothers p Hneq) in Hout.
        exact (IHHreach v Hout).
Qed.

Lemma ep_commit_implies_accepted :
  forall s,
    EP_Reachable s ->
    forall p v, p < n ->
      ep_output (local s p) = Some (Commit v) ->
      ep_accepted (local s p) = Some v.
Proof.
  intros s Hreach p. induction Hreach; simpl in H.
  - unfold ep_init in H. destruct H as [[Hnone _] _].
    intros v Hp Hout. rewrite (Hnone p) in Hout. discriminate.
  - unfold step, ep_instance in H; simpl in H.
    destruct H as [[_ [_ Hp0]] H].
    destruct (network s src p0) as [|m rest] eqn:Hqueue.
    + unfold state_eq in H. destruct H as [Hlocal _].
      intros v Hp Hout. rewrite Hlocal in Hout.
      rewrite Hlocal. exact (IHHreach v Hp Hout).
    + destruct H as [[Hstate Hothers] _].
      intros v Hp Hout.
      destruct (classic (p = p0)) as [Heq | Hneq].
      * subst p0. rewrite Hstate in Hout.
        unfold ep_step_fn in Hout.
        destruct (ep_output (local s p)) as [o|] eqn:Hprev.
        -- simpl in Hout. rewrite Hstate.
           exact (ep_accepted_stable p (local s p) m v
                    (IHHreach v Hp ltac:(congruence))).
        -- destruct (ep_accepted (local s p)) as [w|] eqn:Hacc.
           ++ destruct (andb (Nat.eqb p w) (Nat.eqb (ep_value m) w))
                eqn:Hcond.
              ** simpl in Hout. destruct (ep_quorum <=? length _);
                   [|discriminate].
                 injection Hout as Hwv. subst w.
                 rewrite Hstate. unfold ep_step_fn.
                 rewrite Hprev, Hacc, Hcond. simpl. reflexivity.
              ** simpl in Hout. rewrite Hprev in Hout. discriminate.
           ++ discriminate.
      * rewrite (Hothers p Hneq) in Hout.
        rewrite (Hothers p Hneq).
        exact (IHHreach v Hp Hout).
Qed.

Lemma ep_commit_implies_quorum :
  forall s,
    EP_Reachable s ->
    forall p v, p < n ->
      ep_output (local s p) = Some (Commit v) ->
      ep_quorum <= length (ep_acceptors (local s p)).
Proof.
  intros s Hreach p. induction Hreach; simpl in H.
  - unfold ep_init in H. destruct H as [[Hnone _] _].
    intros v Hp Hout. rewrite (Hnone p) in Hout. discriminate.
  - unfold step, ep_instance in H; simpl in H.
    destruct H as [[_ [_ Hp0]] H].
    destruct (network s src p0) as [|m rest] eqn:Hqueue.
    + unfold state_eq in H. destruct H as [Hlocal _].
      intros v Hp Hout. rewrite Hlocal in Hout.
      rewrite Hlocal. exact (IHHreach v Hp Hout).
    + destruct H as [[Hstate Hothers] _].
      intros v Hp Hout.
      destruct (classic (p = p0)) as [Heq | Hneq].
      * subst p0. rewrite Hstate in Hout.
        unfold ep_step_fn in Hout.
        destruct (ep_output (local s p)) as [o|] eqn:Hprev.
        -- simpl in Hout. rewrite Hstate. unfold ep_step_fn.
           rewrite Hprev. simpl. apply (IHHreach v Hp). congruence.
        -- destruct (ep_accepted (local s p)) as [w|] eqn:Hacc.
           ++ destruct (andb (Nat.eqb p w) (Nat.eqb (ep_value m) w))
                eqn:Hcond.
              ** simpl in Hout.
                 destruct (ep_quorum <=? length _) eqn:Hq;
                   [|discriminate].
                 rewrite Hstate. unfold ep_step_fn.
                 rewrite Hprev, Hacc, Hcond. simpl.
                 apply Nat.leb_le in Hq. exact Hq.
              ** simpl in Hout. rewrite Hprev in Hout. discriminate.
           ++ discriminate.
      * rewrite (Hothers p Hneq) in Hout.
        rewrite (Hothers p Hneq).
        exact (IHHreach v Hp Hout).
Qed.

Lemma ep_no_adopt :
  forall s,
    EP_Reachable s ->
    forall p v, p < n ->
      ep_output (local s p) <> Some (Adopt v).
Proof.
  intros s Hreach p. induction Hreach; simpl in H.
  - unfold ep_init in H. destruct H as [[Hnone _] _].
    intros v Hp Hout. rewrite (Hnone p) in Hout. discriminate.
  - unfold step, ep_instance in H; simpl in H.
    destruct H as [[_ [_ Hp0]] H].
    destruct (network s src p0) as [|m rest] eqn:Hqueue.
    + unfold state_eq in H. destruct H as [Hlocal _].
      intros v Hp Hout. rewrite Hlocal in Hout.
      exact (IHHreach v Hp Hout).
    + destruct H as [[Hstate Hothers] _].
      intros v Hp Hout.
      destruct (classic (p = p0)) as [Heq | Hneq].
      * subst p0. rewrite Hstate in Hout. unfold ep_step_fn in Hout.
        destruct (ep_output (local s p)) as [o|] eqn:Hprev.
        -- simpl in Hout. exact (IHHreach v Hp ltac:(congruence)).
        -- destruct (ep_accepted (local s p)) as [w|].
           ++ destruct (andb (Nat.eqb p w) (Nat.eqb (ep_value m) w)).
              ** simpl in Hout. destruct (ep_quorum <=? length _);
                   discriminate.
              ** simpl in Hout. rewrite Hprev in Hout. discriminate.
           ++ discriminate.
      * rewrite (Hothers p Hneq) in Hout.
        exact (IHHreach v Hp Hout).
Qed.

Lemma ep_commit_value_valid :
  forall s,
    EP_Reachable s ->
    forall p v,
      ep_output (local s p) = Some (Commit v) ->
      is_proposer v.
Proof.
  intros s Hreach p v Hout.
  pose proof (ep_commit_pid_valid s Hreach p v Hout) as Hp.
  pose proof (ep_commit_implies_accepted s Hreach p v Hp Hout) as Hacc.
  pose proof (ep_all_accepted_values_valid s Hreach p Hp) as Hvalid.
  rewrite Hacc in Hvalid. exact Hvalid.
Qed.

Theorem EPaxos_Validity : Validity n ep_instance.
Proof.
  unfold Validity, ep_instance, output_of, valid_pid; simpl.
  intros s p v Hreach Hp [Hout | Hout].
  - exact (ep_commit_value_valid s Hreach p v Hout).
  - exfalso. exact (ep_no_adopt s Hreach p v Hp Hout).
Qed.

(** Arithmetic audit: for [f=1,2,3,4], [2*ep_quorum] is [4,6,10,12]
    while [n] is [3,5,7,9], so strict majority holds in every checked case. *)
Lemma ep_quorum_gt_half : n < 2 * ep_quorum.
Proof.
  unfold ep_quorum.
  pose proof (Nat.div_mod (f + 1) 2 ltac:(lia)) as Hdiv.
  pose proof (Nat.mod_upper_bound (f + 1) 2 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma ep_quorum_intersection :
  forall A B : list ProcessId,
    NoDup A -> (forall x, In x A -> x < n) ->
    NoDup B -> (forall x, In x B -> x < n) ->
    ep_quorum <= length A -> ep_quorum <= length B ->
    exists x, In x A /\ In x B.
Proof.
  intros A B HndA HvalA HndB HvalB HlenA HlenB.
  apply Classical_Pred_Type.not_all_not_ex.
  intro Hnone.
  assert (Hdisj : forall x, In x A -> ~ In x B).
  { intros x HxA HxB. exact (Hnone x (conj HxA HxB)). }
  assert (Hnd : NoDup (A ++ B)).
  { apply NoDup_app; auto. }
  assert (Hincl : incl (A ++ B) (seq 0 n)).
  { intros x Hx. apply in_app_iff in Hx. apply in_seq.
    split; [lia |]. destruct Hx as [Hx | Hx];
      [exact (HvalA x Hx) | exact (HvalB x Hx)]. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hbound.
  rewrite length_app, length_seq in Hbound.
  pose proof ep_quorum_gt_half. lia.
Qed.

Theorem EPaxos_Agreement : Agreement n ep_instance.
Proof.
  unfold Agreement, ep_instance, output_of, valid_pid; simpl.
  intros s p q v w Hreach Hp Hq Hpout [Hqout | Hqout].
  - pose proof (ep_commit_implies_accepted s Hreach p v Hp Hpout) as Haccp.
    pose proof (ep_commit_implies_quorum s Hreach p v Hp Hpout) as Hlenp.
    pose proof (ep_commit_implies_accepted s Hreach q w Hq Hqout) as Haccq.
    pose proof (ep_commit_implies_quorum s Hreach q w Hq Hqout) as Hlenq.
    destruct (ep_quorum_intersection
                (ep_acceptors (local s p)) (ep_acceptors (local s q))
                (ep_acceptors_nodup s Hreach p Hp)
                (ep_all_acceptors_valid s Hreach p Hp)
                (ep_acceptors_nodup s Hreach q Hq)
                (ep_all_acceptors_valid s Hreach q Hq)
                Hlenp Hlenq) as [r [Hrp Hrq]].
    pose proof (ep_all_acceptors_accepted s Hreach p v Hp Haccp r Hrp)
      as Hrv.
    pose proof (ep_all_acceptors_accepted s Hreach q w Hq Haccq r Hrq)
      as Hrw.
    congruence.
  - exfalso. exact (ep_no_adopt s Hreach q w Hq Hqout).
Qed.

Theorem EPaxos_Convergence : Convergence n ep_instance.
Proof.
  unfold Convergence, ep_instance, output_of, valid_pid; simpl.
  intros s p q o Hreach Hp Hq Hprop Hunique Hout.
  destruct o as [v | v].
  - f_equal.
    apply Hunique. exact (ep_commit_value_valid s Hreach q v Hout).
  - exfalso. exact (ep_no_adopt s Hreach q v Hq Hout).
Qed.

Lemma ep_proposer_accepts_self :
  forall s,
    EP_Reachable s ->
    forall p, p < n -> is_proposer p ->
      ep_accepted (local s p) = Some p.
Proof.
  intros s Hreach p Hp Hprop. induction Hreach; simpl in H.
  - unfold ep_init in H.
    destruct H as [[_ [[Hinit _] _]] _].
    exact (Hinit p Hp Hprop).
  - unfold step, ep_instance in H; simpl in H.
    destruct H as [[_ [_ Hp0]] H].
    destruct (network s src p0) as [|m rest] eqn:Hqueue.
    + unfold state_eq in H. destruct H as [Hlocal _].
      rewrite Hlocal. exact IHHreach.
    + destruct H as [[Hstate Hothers] _].
      destruct (classic (p = p0)) as [-> | Hneq].
      * rewrite Hstate.
        exact (ep_accepted_stable p0 (local s p0) m p0 IHHreach).
      * rewrite (Hothers p Hneq). exact IHHreach.
Qed.

Lemma ep_leader_never_acknowledges_other :
  forall s,
    EP_Reachable s ->
    forall leader owner v,
      leader < n ->
      is_proposer leader ->
      owner < n ->
      ep_accepted (local s owner) = Some v ->
      leader <> v ->
      ~ In leader (ep_acceptors (local s owner)).
Proof.
  intros s Hreach leader owner v Hleader Hprop Howner Howneracc Hneq Hin.
  pose proof (ep_proposer_accepts_self s Hreach leader Hleader Hprop)
    as Hself.
  pose proof (ep_all_acceptors_accepted
                s Hreach owner v Howner Howneracc leader Hin) as Hack.
  congruence.
Qed.

Definition ep_intersection (A B : list ProcessId) : list ProcessId :=
  filter (fun x => existsb (Nat.eqb x) B) A.

Definition ep_nonalive_witness
    (v w : ProcessId) (A B : list ProcessId) : list ProcessId :=
  v :: w :: ep_intersection A B.

Lemma ep_intersection_spec :
  forall x A B,
    In x (ep_intersection A B) <-> In x A /\ In x B.
Proof.
  intros x A B. unfold ep_intersection.
  rewrite filter_In. split.
  - intros [HxA Htest]. split; [exact HxA |].
    apply existsb_exists in Htest as [y [Hy Heq]].
    apply Nat.eqb_eq in Heq. subst y. exact Hy.
  - intros [HxA HxB]. split; [exact HxA |].
    apply existsb_exists. exists x. split; [exact HxB | apply Nat.eqb_refl].
Qed.

(** Arithmetic audit: certificate intersections have lower bounds
    [1,1,3,3] for [f=1,2,3,4].  This lemma intentionally proves only
    [|A|+|B| <= n+|A inter B|], not the false claim [|A inter B| > f]. *)
Lemma ep_intersection_length_lower_bound :
  forall A B : list ProcessId,
    NoDup A -> (forall x, In x A -> x < n) ->
    NoDup B -> (forall x, In x B -> x < n) ->
    length A + length B <= n + length (ep_intersection A B).
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
            length D <=
            length (filter (fun x => negb (inside x)) (seq 0 n)))
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

Lemma ep_intersection_nodes_nonalive :
  forall (s s' : EP_GlobalState) alive A B v w,
    (forall r, In r alive -> local s r = local s' r) ->
    (forall r, In r A -> ep_accepted (local s r) = Some v) ->
    (forall r, In r B -> ep_accepted (local s' r) = Some w) ->
    v <> w ->
    forall r, In r (ep_intersection A B) -> ~ In r alive.
Proof.
  intros s s' alive A B v w Heq HaccA HaccB Hneq r Hinter Halive.
  apply ep_intersection_spec in Hinter as [HinA HinB].
  pose proof (HaccA r HinA) as Hv.
  pose proof (HaccB r HinB) as Hw.
  rewrite (Heq r Halive) in Hv. congruence.
Qed.

Lemma ep_first_leader_nonalive :
  forall s s' alive v w,
    EP_Reachable s -> EP_Reachable s' ->
    (forall r, In r alive -> local s r = local s' r) ->
    ep_output (local s v) = Some (Commit v) ->
    ep_output (local s' w) = Some (Commit w) ->
    v <> w ->
    ~ In v alive.
Proof.
  intros s s' alive v w Hs Hs' Heq Hv Hw Hneq Halive.
  pose proof (ep_commit_pid_valid s Hs v v Hv) as Hvalidv.
  pose proof (ep_commit_pid_valid s' Hs' w w Hw) as Hvalidw.
  assert (Hv' : ep_output (local s' v) = Some (Commit v)).
  { rewrite <- (Heq v Halive). exact Hv. }
  pose proof (EPaxos_Agreement
                s' w v w v Hs' Hvalidw Hvalidv Hw (or_introl Hv')) as Hagree.
  exact (Hneq Hagree).
Qed.

Lemma ep_second_leader_nonalive :
  forall s s' alive v w,
    EP_Reachable s -> EP_Reachable s' ->
    (forall r, In r alive -> local s r = local s' r) ->
    ep_output (local s v) = Some (Commit v) ->
    ep_output (local s' w) = Some (Commit w) ->
    v <> w ->
    ~ In w alive.
Proof.
  intros s s' alive v w Hs Hs' Heq Hv Hw Hneq Halive.
  pose proof (ep_commit_pid_valid s Hs v v Hv) as Hvalidv.
  pose proof (ep_commit_pid_valid s' Hs' w w Hw) as Hvalidw.
  assert (Hw' : ep_output (local s w) = Some (Commit w)).
  { rewrite (Heq w Halive). exact Hw. }
  pose proof (EPaxos_Agreement
                s v w v w Hs Hvalidv Hvalidw Hv (or_introl Hw')) as Hagree.
  exact (Hneq (eq_sym Hagree)).
Qed.

Lemma ep_nonalive_witness_nodup :
  forall v w A B,
    v <> w ->
    NoDup A ->
    ~ In v B ->
    ~ In w A ->
    NoDup (ep_nonalive_witness v w A B).
Proof.
  intros v w A B Hvw HndA HvB HwA.
  unfold ep_nonalive_witness.
  repeat constructor.
  - intro Hin. destruct Hin as [Heq | Hin].
    + exact (Hvw (eq_sym Heq)).
    + apply ep_intersection_spec in Hin as [_ HinB].
      exact (HvB HinB).
  - intro Hin. apply ep_intersection_spec in Hin as [HinA _].
    exact (HwA HinA).
  - unfold ep_intersection. apply NoDup_filter. exact HndA.
Qed.

Lemma ep_nonalive_witness_valid :
  forall v w A B,
    v < n -> w < n ->
    (forall r, In r A -> r < n) ->
    forall r, In r (ep_nonalive_witness v w A B) -> r < n.
Proof.
  intros v w A B Hv Hw Hval r Hin.
  unfold ep_nonalive_witness in Hin. simpl in Hin.
  destruct Hin as [-> | [-> | Hin]]; [exact Hv | exact Hw |].
  apply ep_intersection_spec in Hin as [HinA _].
  exact (Hval r HinA).
Qed.

Lemma ep_nonalive_witness_all_nonalive :
  forall v w A B alive,
    ~ In v alive ->
    ~ In w alive ->
    (forall r, In r (ep_intersection A B) -> ~ In r alive) ->
    forall r, In r (ep_nonalive_witness v w A B) -> ~ In r alive.
Proof.
  intros v w A B alive Hv Hw Hinter r Hin.
  unfold ep_nonalive_witness in Hin. simpl in Hin.
  destruct Hin as [-> | [-> | Hin]];
    [exact Hv | exact Hw | exact (Hinter r Hin)].
Qed.

(** Arithmetic audit for [f=1,2,3,4]:
    witness lower bounds are [3,3,5,5], respectively, all strictly above
    [f].  The leaders are essential when [f=2], where the intersection
    lower bound is only one. *)
Lemma ep_nonalive_witness_length_gt_f :
  forall v w A B,
    NoDup A -> (forall r, In r A -> r < n) ->
    NoDup B -> (forall r, In r B -> r < n) ->
    ep_quorum <= length A ->
    ep_quorum <= length B ->
    f < length (ep_nonalive_witness v w A B).
Proof.
  intros v w A B HndA HvalA HndB HvalB HlenA HlenB.
  pose proof (ep_intersection_length_lower_bound
                A B HndA HvalA HndB HvalB) as Hinter.
  assert (Hcert :
            2 * ep_quorum <= n + length (ep_intersection A B)).
  { replace (2 * ep_quorum) with (ep_quorum + ep_quorum) by lia.
    eapply Nat.le_trans with (m := length A + length B).
    - apply Nat.add_le_mono; [exact HlenA | exact HlenB].
    - exact Hinter. }
  unfold ep_nonalive_witness. simpl.
  pose proof (Nat.div_mod (f + 1) 2 ltac:(lia)) as Hdiv.
  pose proof (Nat.mod_upper_bound (f + 1) 2 ltac:(lia)) as Hmod.
  assert (Hfloor : f <= 2 * ((f + 1) / 2)) by lia.
  unfold ep_quorum in Hcert.
  lia.
Qed.

Lemma ep_nonalive_witness_disjoint_alive :
  forall v w A B alive,
    NoDup (ep_nonalive_witness v w A B) ->
    NoDup alive ->
    (forall r, In r (ep_nonalive_witness v w A B) -> ~ In r alive) ->
    NoDup (ep_nonalive_witness v w A B ++ alive).
Proof.
  intros v w A B alive Hndw Hnda Hdisj.
  apply NoDup_app; auto.
Qed.

Theorem EPaxos_Recoverability : Recoverability n f ep_instance.
Proof.
  unfold Recoverability, ep_instance, output_of, valid_pid; simpl.
  intros s s' alive v w Hs Hs' Hndalive Hlenalive Hvalalive Hequal
         [p Hpout] [q Hqout].
  pose proof (ep_commit_only_at_leader s Hs p v Hpout) as Hp_leader.
  pose proof (ep_commit_only_at_leader s' Hs' q w Hqout) as Hq_leader.
  subst p. subst q.
  destruct (classic (v = w)) as [Heq | Hneq]; [exact Heq |].
  pose proof (ep_commit_pid_valid s Hs v v Hpout) as Hvalidv.
  pose proof (ep_commit_pid_valid s' Hs' w w Hqout) as Hvalidw.
  pose proof (ep_commit_value_valid s Hs v v Hpout) as Hpropv.
  pose proof (ep_commit_value_valid s' Hs' w w Hqout) as Hpropw.
  pose proof (ep_commit_implies_accepted s Hs v v Hvalidv Hpout) as Haccv.
  pose proof (ep_commit_implies_accepted s' Hs' w w Hvalidw Hqout) as Haccw.
  pose proof (ep_commit_implies_quorum s Hs v v Hvalidv Hpout) as Hquorumv.
  pose proof (ep_commit_implies_quorum s' Hs' w w Hvalidw Hqout) as Hquorumw.
  set (A := ep_acceptors (local s v)).
  set (B := ep_acceptors (local s' w)).
  assert (HndA : NoDup A).
  { unfold A. exact (ep_acceptors_nodup s Hs v Hvalidv). }
  assert (HndB : NoDup B).
  { unfold B. exact (ep_acceptors_nodup s' Hs' w Hvalidw). }
  assert (HvalA : forall r, In r A -> r < n).
  { unfold A. exact (ep_all_acceptors_valid s Hs v Hvalidv). }
  assert (HvalB : forall r, In r B -> r < n).
  { unfold B. exact (ep_all_acceptors_valid s' Hs' w Hvalidw). }
  assert (HaccA : forall r, In r A ->
            ep_accepted (local s r) = Some v).
  { unfold A. exact (ep_all_acceptors_accepted
                       s Hs v v Hvalidv Haccv). }
  assert (HaccB : forall r, In r B ->
            ep_accepted (local s' r) = Some w).
  { unfold B. exact (ep_all_acceptors_accepted
                       s' Hs' w w Hvalidw Haccw). }
  assert (Hv_not_B : ~ In v B).
  { unfold B. eapply ep_leader_never_acknowledges_other;
      eauto. }
  assert (Hw_not_A : ~ In w A).
  { unfold A. eapply ep_leader_never_acknowledges_other;
      eauto. }
  assert (Hinter_nonalive :
            forall r, In r (ep_intersection A B) -> ~ In r alive).
  { eapply ep_intersection_nodes_nonalive; eauto. }
  assert (Hv_nonalive : ~ In v alive).
  { exact (ep_first_leader_nonalive
             s s' alive v w Hs Hs' Hequal Hpout Hqout Hneq). }
  assert (Hw_nonalive : ~ In w alive).
  { exact (ep_second_leader_nonalive
             s s' alive v w Hs Hs' Hequal Hpout Hqout Hneq). }
  set (W := ep_nonalive_witness v w A B).
  assert (HndW : NoDup W).
  { unfold W. apply ep_nonalive_witness_nodup; auto. }
  assert (HvalW : forall r, In r W -> r < n).
  { unfold W. eapply ep_nonalive_witness_valid; eauto. }
  assert (HnonaliveW : forall r, In r W -> ~ In r alive).
  { unfold W. eapply ep_nonalive_witness_all_nonalive; eauto. }
  assert (HlenW : f < length W).
  { unfold W, A, B in *.
    eapply ep_nonalive_witness_length_gt_f; eauto. }
  assert (Hnd_all : NoDup (W ++ alive)).
  { unfold W. eapply ep_nonalive_witness_disjoint_alive; eauto. }
  assert (Hincl : incl (W ++ alive) (seq 0 n)).
  { intros r Hr. apply in_app_iff in Hr. apply in_seq. split; [lia |].
    destruct Hr as [Hr | Hr].
    - exact (HvalW r Hr).
    - exact (Hvalalive r Hr). }
  pose proof (NoDup_incl_length Hnd_all Hincl) as Hdomain.
  rewrite length_app, length_seq in Hdomain.
  lia.
Qed.

End EP.
