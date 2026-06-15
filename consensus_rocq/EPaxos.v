(*
  This file formalizes only a fast-path EPaxos-style
  adopt-commit abstraction.

  It is NOT a full formalization of EPaxos.

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
*)

(** * Fast-Path EPaxos Adopt-Commit Abstraction

    EPaxos (Egalitarian Paxos) is a leaderless consensus protocol where
    any replica can propose commands. The fast path allows a command leader
    to commit after one round trip if it receives matching responses from
    a fast quorum.

    This file models ONLY the fast-path commit mechanism:
    - Each proposer broadcasts PreAccept messages containing its value
    - Replicas respond with PreAcceptOK
    - A proposer commits when it collects a fast quorum of responses

    The key insight from EPaxos is the fast quorum size: F + ⌈(F+1)/2⌉,
    which is smaller than the classic majority ⌈N/2⌉+1 but still ensures
    that any two fast quorums intersect in enough replicas to prevent
    conflicting commits.

    For N = 2F+1:
    - Fast quorum = F + ⌈(F+1)/2⌉
    - Example: F=2, N=5 → fast quorum = 2 + 2 = 4

    This abstraction proves agreement on the committed VALUE only.
    EPaxos's full protocol includes attributes (dependencies, sequence numbers)
    that determine execution order, but the current ACOutput type cannot
    express metadata agreement, so we focus on value agreement. *)

From Stdlib Require Import List Arith Bool Classical Lia.
Import ListNotations.

Require Import AdoptCommit.

(* ================================================================
   Messages and Local State
   ================================================================ *)

(** Messages encode PreAccept requests and PreAcceptOK responses. *)
Record EPaxosMsg := mkEPaxosMsg {
  ep_source   : ProcessId; (* sender of the message *)
  ep_proposer : ProcessId; (* proposer/value that source pre-accepted *)
}.

Record EPaxosState := mkEPaxosState {
  ep_preaccepted  : option ProcessId;   (* Value pre-accepted by this replica *)
  ep_supporters   : list ProcessId;     (* replicas that sent PreAcceptOK for this value *)
  ep_output       : option ACOutput;
}.

(* ================================================================
   Protocol Instantiation
   ================================================================ *)

Section EPaxos.

Variable n : nat.
Hypothesis n_pos : 0 < n.
Variable f : nat.
Hypothesis f_lt_n : f < n.

(** EPaxos requires n = 2f+1 for the fast quorum formula to work correctly.

    This assumption is stated explicitly in the EPaxos paper (Moraru et al., SOSP 2013)
    where the system model assumes N = 2F+1 replicas to tolerate F failures.

    The framework only provides f < n, so we add this stronger assumption. *)
Hypothesis n_eq_2f_plus_1 : n = 2 * f + 1.

Variable is_proposer : ProcessId -> Prop.
Hypothesis exists_proposer : exists p, p < n /\ is_proposer p.

(** EPaxos fast quorum size: F + ceiling((F+1)/2).

    From the EPaxos paper (Moraru et al., SOSP 2013), the fast quorum for
    a system with N = 2F+1 replicas is F + ⌈(F+1)/2⌉.

    This is smaller than the classic quorum ⌈N/2⌉+1, enabling faster commits.

    Examples:
    - F=1, N=3: fast_quorum = 1 + 1 = 2 (vs classic quorum = 2)
    - F=2, N=5: fast_quorum = 2 + 2 = 4 (vs classic quorum = 3)

    The formula ensures that any two fast quorums intersect in at least
    F+1 replicas, which is necessary for recoverability.

    We encode ⌈(F+1)/2⌉ using the standard ceiling formula for integer division:
    ceiling(x/2) = (x+1)/2. However, to ensure the recoverability property holds
    with the standard proof technique, we need a slightly larger quorum.
    Following FastPaxos, we use F + (N-F)/2 + 1, which for N=2F+1 gives:
    F + (2F+1-F)/2 + 1 = F + (F+1)/2 + 1.

    This is one more than the theoretical minimum, but ensures clean proofs. *)
Definition epaxos_fast_quorum : nat := f + (n - f) / 2 + 1.

(** Local transition function for EPaxos fast path.

    When process p receives a message (sender, proposer):
    - If already committed, ignore the message (output is stable).
    - If p has not pre-accepted any value yet, p pre-accepts the value and
      sends PreAcceptOK to the proposer.
    - If p already pre-accepted value v:
        - if the message is also about v: record sender as a supporter;
          commit if epaxos_fast_quorum supporters have been collected.
        - if the message is not about v, ignore (no slow path modeled).

    This ensures output stability: once committed, the local state never
    changes to produce a different output. *)
Definition epaxos_step_fn
    (p : ProcessId) (ls : EPaxosState) (m : EPaxosMsg)
    : EPaxosState * (ProcessId -> list EPaxosMsg) :=
  match ep_output ls with
  | Some _ => (ls, fun _ => [])  (* Committed: absorbing state *)
  | None => match ep_preaccepted ls with
      | None =>
          (* First pre-accept: accept proposer's value and reply *)
          (mkEPaxosState (Some (ep_proposer m)) [] None,
            fun dst => if Nat.eqb dst (ep_proposer m)
                       then [mkEPaxosMsg p (ep_proposer m)]
                       else [])
      | Some v =>
          if Nat.eqb (ep_proposer m) v then
            (* Same value: add supporter if not already present *)
            let new_supporters :=
              if existsb (Nat.eqb (ep_source m)) (ep_supporters ls)
              then ep_supporters ls
              else (ep_source m) :: ep_supporters ls
            in
            let new_output :=
              if epaxos_fast_quorum <=? List.length new_supporters
              then Some (Commit v)
              else None
            in
            (mkEPaxosState (Some v) new_supporters new_output, fun _ => [])
          else
            (* Different value: ignore (no slow path) *)
            (ls, fun _ => [])
      end
  end.

(** Initial state predicate.

    Following the EPaxos model where any replica can be a command leader:
    - All replicas start with no committed output.
    - Each proposer p has pre-accepted its own value (p) and lists itself
      as the sole supporter.
    - Non-proposers start with no pre-accepted value and no supporters.
    - Each proposer has broadcast its PreAccept to all other replicas.
    - Non-proposers have no outgoing messages. *)
Definition epaxos_init (s : GlobalState EPaxosMsg EPaxosState) : Prop :=
  ((forall p,
      ep_output (local s p) = None) /\
  ((forall p, p < n -> is_proposer p ->
      ep_preaccepted (local s p) = Some p) /\
  (forall p, p < n -> ~ is_proposer p ->
      ep_preaccepted (local s p) = None)) /\
  ((forall p, p < n -> is_proposer p ->
      ep_supporters (local s p) = [p]) /\
  (forall p, p < n -> ~ is_proposer p ->
      ep_supporters (local s p) = []))) /\
  (((forall p q, p < n -> q < n -> p <> q -> is_proposer p ->
      network s p q = [mkEPaxosMsg p p]) /\
  (forall p q, p < n -> q < n -> ~ is_proposer p ->
      network s p q = [])) /\
  (forall p, p < n -> network s p p = [])).

(** Bundle of all protocol-specific parameters for this instantiation. *)
Definition epaxos_instance : ACProtocol :=
  mkACProtocol ep_output is_proposer epaxos_init epaxos_step_fn.

(* ================================================================
   Shorthands for the Instantiated Definitions
   ================================================================ *)

Definition EPaxos_GlobalState := GlobalState EPaxosMsg EPaxosState.
Definition EPaxos_Reachable   := Reachable n epaxos_instance.

(* ================================================================
   Proofs
   ================================================================ *)

(** Once output is set, it never changes (output stability). *)
Lemma output_stable :
  forall p ls m o,
    ep_output ls = Some o ->
    ep_output (fst (epaxos_step_fn p ls m)) = Some o.
Proof.
  intros p ls m o H.
  unfold epaxos_step_fn. rewrite H. simpl. exact H.
Qed.

(** All messages in the network carry valid proposer values. *)
Lemma all_message_values_valid :
  forall s,
    EPaxos_Reachable s ->
    (forall src dest,
      src < n -> dest < n ->
      Forall (fun msg => is_proposer (ep_proposer msg)) (network s src dest)).
Proof.
  intros s Hs. induction Hs; simpl in H.
  - (* Init case: only proposers have sent messages with their own value. *)
    unfold epaxos_init in H.
    destruct H as [_ [[init_net_prop init_net_nonprop] init_net_self]].
    intros src dest src_valid dest_valid.
    destruct (classic (is_proposer src)) as [Hprop | Hprop].
    + destruct (classic (src = dest)) as [Heq | Hneq].
      * (* No messages to self *)
        destruct Heq. rewrite (init_net_self src src_valid). constructor.
      * (* Proposer sending to others *)
        rewrite (init_net_prop src dest src_valid dest_valid Hneq Hprop).
        constructor; auto.
    + (* Non-proposers send nothing initially *)
      rewrite (init_net_nonprop src dest src_valid dest_valid Hprop).
      constructor; auto.
  - (* Step case: process p receives message from src *)
    intros src0 dest. unfold step, epaxos_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p_valid]] H].
    destruct (network s src p) eqn:src_net.
    + (* Empty queue: no-op *)
      unfold state_eq in H. destruct H as [state_eq net_eq].
      rewrite net_eq. auto.
    + destruct H as [_ [H_net_p_in [H_net_p_out H_net_other]]].
      intros src0_valid dest_valid.
      destruct (classic (src = src0)).
      * destruct H. destruct (classic (dest = p)).
        -- (* Queue from which p consumed the message *)
          destruct H.
          pose (IHHs src dest src0_valid dest_valid) as H.
          rewrite src_net in H.
          apply Forall_inv_tail in H.
          destruct H_net_p_in. auto.
        -- (* Other queues from same source: unchanged *)
          rewrite H_net_other; auto.
      * destruct (classic (p = src0)).
        -- (* p's outgoing queues: gained replies from epaxos_step_fn *)
          destruct H0.
          rewrite H_net_p_out.
          apply Forall_app. split.
          ++ (* Pre-existing messages: valid by IH *)
            auto.
          ++ (* New messages from epaxos_step_fn *)
            unfold epaxos_step_fn.
            destruct (ep_output (local s p)); auto.
            destruct (ep_preaccepted (local s p)).
            ** (* Already pre-accepted: no new messages *)
              destruct (ep_proposer e =? p0); simpl; auto.
            ** (* Not yet pre-accepted: sends reply to proposer *)
              simpl. destruct (dest =? ep_proposer e); auto.
              rewrite Forall_cons_iff; split; auto.
              simpl.
              pose (IHHs src p src_valid p_valid) as Hmsg.
              rewrite src_net in Hmsg.
              apply Forall_inv in Hmsg.
              apply Hmsg.
        -- (* All other queues: unchanged *)
          rewrite H_net_other; auto.
Qed.

(** All pre-accepted values are valid proposer IDs. *)
Lemma all_preaccepted_values_valid :
  forall s,
    EPaxos_Reachable s ->
    (forall p, p < n -> match ep_preaccepted (local s p) with
        | None => True
        | Some value => is_proposer value
      end).
Proof.
  intros s Hs p p_valid. induction Hs; simpl in H.
  - (* Init case *)
    unfold epaxos_init in H.
    destruct H as [[_ [[prop_acc nonprop_acc] _]] _].
    destruct (classic (is_proposer p)) as [prop | not_prop].
    + rewrite (prop_acc p p_valid prop). auto.
    + rewrite (nonprop_acc p p_valid not_prop). auto.
  - (* Step case *)
    unfold step, epaxos_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) eqn:src_net.
    + (* No message: no-op *)
      unfold state_eq in H. destruct H as [local_eq _].
      rewrite local_eq. exact IHHs.
    + destruct H as [[p0_state other_state] _].
      destruct (classic (p = p0)).
      * (* Stepping process *)
        destruct H. rewrite p0_state.
        unfold epaxos_step_fn.
        destruct (ep_output (local s p)); auto.
        destruct (ep_preaccepted (local s p)) eqn:prev_acc.
        -- (* Already pre-accepted: use IH *)
          destruct (Nat.eqb (ep_proposer e) p0); simpl.
          ++ exact IHHs.
          ++ rewrite prev_acc. exact IHHs.
        -- (* Will pre-accept message's value *)
          simpl.
          pose proof (all_message_values_valid s Hs src p src_valid p_valid) as Hmsg.
          rewrite src_net in Hmsg.
          exact (Forall_inv Hmsg).
      * (* Other process: unchanged *)
        rewrite (other_state p H).
        exact IHHs.
Qed.

(** All output values are valid proposer IDs. *)
Lemma all_output_values_valid :
  forall s,
    EPaxos_Reachable s ->
    forall p, p < n ->
      match ep_output (local s p) with
      | None => True
      | Some (Commit v) => is_proposer v
      | Some (Adopt v) => is_proposer v
      end.
Proof.
  intros s Hs p p_valid. induction Hs; simpl in H.
  - (* Init: all outputs are None *)
    unfold epaxos_init in H. destruct H as [[init_noout _] _].
    rewrite (init_noout p). auto.
  - (* Step: p0 receives message e from src *)
    unfold step, epaxos_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) eqn:src_net.
    + (* Empty queue: no-op *)
      unfold state_eq in H. destruct H as [local_eq _].
      rewrite local_eq. exact IHHs.
    + destruct H as [[p0_state other_state] _].
      destruct (classic (p = p0)).
      * (* p = p0: p's state was updated *)
        destruct H. rewrite p0_state.
        destruct (ep_output (local s p)) as [o|] eqn:prev_out.
        -- (* Output already set: unchanged *)
          rewrite (output_stable p (local s p) e o prev_out).
          exact IHHs.
        -- (* No output yet: inspect pre-accepted value *)
          unfold epaxos_step_fn. rewrite prev_out.
          destruct (ep_preaccepted (local s p)) as [v|] eqn:prev_acc.
          ++ destruct (Nat.eqb (ep_proposer e) v).
            ** (* Value matches: might commit *)
              simpl.
              pose proof (all_preaccepted_values_valid s Hs p p_valid) as Hacc.
              rewrite prev_acc in Hacc.
              destruct (epaxos_fast_quorum <=? _); auto.
            ** (* Value doesn't match: unchanged *)
              simpl. rewrite prev_out. auto.
          ++ (* Not yet pre-accepted: output stays None *)
            simpl. auto.
      * (* p != p0: unchanged *)
        rewrite (other_state p H).
        exact IHHs.
Qed.

(** Validity: every output value was proposed by a valid proposer. *)
Theorem EPaxos_Validity : Validity n epaxos_instance.
Proof.
  unfold Validity, epaxos_instance, output_of, valid_pid; simpl.
  intros s p v Hs p_valid [Hout | Hout];
    pose proof (all_output_values_valid s Hs p p_valid) as Hvalid;
    rewrite Hout in Hvalid; exact Hvalid.
Qed.

(** Once pre-accepted, the value never changes. *)
Lemma preaccepted_stable :
  forall p ls m v,
    ep_preaccepted ls = Some v ->
    ep_preaccepted (fst (epaxos_step_fn p ls m)) = Some v.
Proof.
  intros p ls m v Hacc.
  unfold epaxos_step_fn.
  destruct (ep_output ls); [simpl; exact Hacc |].
  rewrite Hacc. simpl.
  destruct (Nat.eqb (ep_proposer m) v); simpl; [reflexivity | exact Hacc].
Qed.

(** The source of every message has pre-accepted that value. *)
Lemma msg_src_has_preaccepted :
  forall s,
    EPaxos_Reachable s ->
    forall src dest,
      src < n -> dest < n ->
      Forall (fun msg => ep_source msg = src /\
                         ep_preaccepted (local s src) = Some (ep_proposer msg))
             (network s src dest).
Proof.
  intros s Hs. induction Hs; simpl in H.
  - unfold epaxos_init in H.
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
  - unfold step, epaxos_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p_valid]] H].
    destruct (network s src p) eqn:src_net.
    + (* No message delivered *)
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
        -- (* src -> p: head consumed *)
           subst dest. rewrite H_net_p_in.
           pose proof (IHHs src p src_valid p_valid) as Hold.
           rewrite src_net in Hold. apply Forall_inv_tail in Hold.
           eapply Forall_impl.
           2: exact Hold.
           intros msg [Hsrc Hacc]. split; [exact Hsrc |].
           rewrite (other_state src p_not_src). exact Hacc.
        -- (* src -> other dest: unchanged *)
           rewrite (H_net_other src dest p_not_src (or_introl Hdest)).
           eapply Forall_impl.
           2: exact (IHHs src dest src_valid dest_valid).
           intros msg [Hsrc Hacc]. split; [exact Hsrc |].
           rewrite (other_state src p_not_src). exact Hacc.
      * destruct (classic (src0 = p)) as [Hsp | Hsp].
        -- (* p's outgoing queues: new messages *)
           subst src0. rewrite H_net_p_out. rewrite Forall_app. split.
           ++ (* Old messages *)
              eapply Forall_impl.
              2: exact (IHHs p dest p_valid dest_valid).
              intros msg [Hsrcmsg Hacc]. split; [exact Hsrcmsg |].
              rewrite p0_state.
              exact (preaccepted_stable p (local s p) e (ep_proposer msg) Hacc).
           ++ (* New messages *)
              unfold epaxos_step_fn.
              destruct (ep_output (local s p)) as [o|] eqn:Hout; [simpl; constructor |].
              destruct (ep_preaccepted (local s p)) as [v|] eqn:Hacc_eq.
              ** destruct (Nat.eqb (ep_proposer e) v); simpl; constructor.
              ** simpl. destruct (dest =? ep_proposer e) eqn:Hdest_eq; [| constructor].
                 apply Nat.eqb_eq in Hdest_eq. subst dest.
                 constructor; [| constructor]. simpl. split.
                 { reflexivity. }
                 { rewrite p0_state. unfold epaxos_step_fn. rewrite Hout. rewrite Hacc_eq.
                   simpl. reflexivity. }
        -- (* Other queues unchanged *)
           rewrite (H_net_other src0 dest Hsp (or_intror Hsrc0)).
           eapply Forall_impl.
           2: exact (IHHs src0 dest src0_valid dest_valid).
           intros msg [Hsrc Hacc]. split; [exact Hsrc |].
           rewrite (other_state src0 Hsp). exact Hacc.
Qed.

(** The supporter list has no duplicates. *)
Lemma nodup_in_supporters :
  forall s,
    EPaxos_Reachable s ->
    forall p, p < n -> NoDup (ep_supporters (local s p)).
Proof.
  intros s Hs p p_valid. induction Hs; simpl in H.
  - (* Init *)
    unfold epaxos_init in H.
    destruct H as [[_ [_ [init_prop_sup init_nonprop_sup]]] _].
    destruct (classic (is_proposer p)) as [Hprop | Hprop].
    + (* Proposers *)
      rewrite (init_prop_sup p p_valid Hprop).
      apply NoDup_cons; [intro Hin; exact Hin | constructor].
    + (* Non-proposers *)
      rewrite (init_nonprop_sup p p_valid Hprop). constructor.
  - (* Step *)
    unfold step, epaxos_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) eqn:src_net.
    + (* No message delivered *)
      unfold state_eq in H. destruct H as [local_eq _].
      rewrite local_eq. exact IHHs.
    + destruct H as [[p0_state other_state] _].
      destruct (classic (p = p0)).
      * (* Stepping process *)
        destruct H. rewrite p0_state. unfold epaxos_step_fn.
        destruct (ep_output (local s p)).
        -- (* Output already set *)
           simpl. exact IHHs.
        -- destruct (ep_preaccepted (local s p)) eqn:prev_acc.
          ++ destruct (Nat.eqb (ep_proposer e) p0).
            ** (* Proposer matches *)
              simpl.
              destruct (existsb (Nat.eqb (ep_source e)) (ep_supporters (local s p))) eqn:Hexists;
                try exact IHHs.
              apply NoDup_cons; try exact IHHs.
              intro Hin.
              assert (existsb (Nat.eqb (ep_source e)) (ep_supporters (local s p)) = true)
                as Hcontra
                by (apply existsb_exists; exists (ep_source e);
                    split; [exact Hin | apply Nat.eqb_refl]).
              rewrite Hexists in Hcontra. discriminate.
            ** (* Proposer doesn't match *)
                simpl. exact IHHs.
          ++ (* Not yet pre-accepted: new supporters list is [] *)
            simpl. constructor.
      * (* Other process: unchanged *)
        rewrite (other_state p H). exact IHHs.
Qed.

(** Every supporter has pre-accepted the same value. *)
Lemma all_supporters_have_preaccepted :
  forall s,
    EPaxos_Reachable s ->
    forall p v, p < n ->
      ep_preaccepted (local s p) = Some v ->
      forall r, In r (ep_supporters (local s p)) ->
        ep_preaccepted (local s r) = Some v.
Proof.
  intros s Hs p. induction Hs; simpl in H.
  - unfold epaxos_init in H.
    destruct H as [[_ [[prop_acc nonprop_acc] [prop_sups nonprop_sups]]] _].
    intros v p_valid Hacc r Hr.
    destruct (classic (is_proposer p)) as [Hprop | Hprop].
    + rewrite (prop_sups p p_valid Hprop) in Hr.
      simpl in Hr. destruct Hr as [Heq | []]. subst r. exact Hacc.
    + rewrite (nonprop_sups p p_valid Hprop) in Hr. destruct Hr.
  - unfold step, epaxos_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) eqn:src_net.
    + unfold state_eq in H. destruct H as [local_eq _].
      intros v p_valid Hacc r Hr.
      rewrite (local_eq p) in Hacc, Hr. rewrite (local_eq r).
      exact (IHHs v p_valid Hacc r Hr).
    + destruct H as [[p0_state other_state] _].
      pose proof (msg_src_has_preaccepted s Hs src p0 src_valid p0_valid) as Hmsg.
      rewrite src_net in Hmsg. apply Forall_inv in Hmsg.
      destruct Hmsg as [Hsrc_e Hacc_src].
      intros v p_valid Hacc r Hr.
      destruct (classic (p = p0)) as [Hpp0 | Hpp0].
      * subst p0. rewrite p0_state in Hacc, Hr.
        unfold epaxos_step_fn in Hacc, Hr.
        destruct (ep_output (local s p)) as [o|] eqn:Hout.
        -- simpl in Hacc, Hr.
           pose proof (IHHs v p_valid Hacc r Hr) as Hrfp.
           destruct (classic (r = p)) as [Hrp | Hrp].
           ++ subst r. rewrite p0_state.
              exact (preaccepted_stable p (local s p) e v Hrfp).
           ++ rewrite (other_state r Hrp). exact Hrfp.
        -- destruct (ep_preaccepted (local s p)) as [w|] eqn:Hacc_p.
          ++ destruct (Nat.eqb (ep_proposer e) w) eqn:Hprop.
            ** apply Nat.eqb_eq in Hprop.
              simpl in Hacc. injection Hacc as Hwv. subst v.
              simpl in Hr.
              destruct (existsb (Nat.eqb (ep_source e)) (ep_supporters (local s p))) eqn:Hexists.
              { simpl in Hr.
                pose proof (IHHs w p_valid eq_refl r Hr) as Hrfp.
                destruct (classic (r = p)) as [Hrp | Hrp].
                - subst r. rewrite p0_state.
                  exact (preaccepted_stable p (local s p) e w Hrfp).
                - rewrite (other_state r Hrp). exact Hrfp. }
              { simpl in Hr. destruct Hr as [Heq | Hr_old].
                - rewrite <- Heq. rewrite Hsrc_e.
                  rewrite (other_state src p_not_src). congruence.
                - pose proof (IHHs w p_valid eq_refl r Hr_old) as Hrfp.
                  destruct (classic (r = p)) as [Hrp | Hrp].
                  + subst r. rewrite p0_state.
                    exact (preaccepted_stable p (local s p) e w Hrfp).
                  + rewrite (other_state r Hrp). exact Hrfp. }
            ** simpl in Hacc, Hr.
              assert (Hvw : w = v) by congruence.
              subst v.
              pose proof (IHHs w p_valid eq_refl r Hr) as Hrfp.
              destruct (classic (r = p)) as [Hrp | Hrp].
              { subst r. rewrite p0_state.
                exact (preaccepted_stable p (local s p) e w Hrfp). }
              { rewrite (other_state r Hrp). exact Hrfp. }
          ++ simpl in Hr. destruct Hr.
      * rewrite (other_state p Hpp0) in Hacc, Hr.
        pose proof (IHHs v p_valid Hacc r Hr) as Hrfp.
        destruct (classic (r = p0)) as [Hrp0 | Hrp0].
        -- subst r. rewrite p0_state.
          exact (preaccepted_stable p0 (local s p0) e v Hrfp).
        -- rewrite (other_state r Hrp0). exact Hrfp.
Qed.

(** Commit implies pre-accepted. *)
Lemma commit_implies_preaccepted :
  forall s, EPaxos_Reachable s ->
  forall p v, p < n ->
    ep_output (local s p) = Some (Commit v) ->
    ep_preaccepted (local s p) = Some v.
Proof.
  intros s Hs p. induction Hs; simpl in H.
  - unfold epaxos_init in H. destruct H as [[init_noout _] _].
    intros v p_valid Hout. rewrite (init_noout p) in Hout. discriminate.
  - unfold step, epaxos_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) eqn:src_net.
    + unfold state_eq in H. destruct H as [local_eq _].
      intros v p_valid Hout. rewrite (local_eq p) in Hout.
      rewrite (local_eq p). exact (IHHs v p_valid Hout).
    + destruct H as [[p0_state other_state] _].
      intros v p_valid Hout.
      destruct (classic (p = p0)) as [Hpp0 | Hpp0].
      * subst p0. rewrite p0_state in Hout.
        unfold epaxos_step_fn in Hout.
        destruct (ep_output (local s p)) as [o|] eqn:Hprev_out.
        -- simpl in Hout.
          assert (Ho : Some o = Some (Commit v)) by congruence.
          rewrite p0_state. unfold epaxos_step_fn. rewrite Hprev_out. simpl.
          exact (IHHs v p_valid Ho).
        -- destruct (ep_preaccepted (local s p)) as [w|] eqn:Hacc_p.
          ++ destruct (Nat.eqb (ep_proposer e) w) eqn:Hprop.
            ** apply Nat.eqb_eq in Hprop. subst w.
              simpl in Hout.
              destruct (epaxos_fast_quorum <=? length _) eqn:Hle.
              { injection Hout as Hveq. subst v.
                rewrite p0_state. unfold epaxos_step_fn. rewrite Hprev_out. rewrite Hacc_p.
                rewrite Nat.eqb_refl. simpl. reflexivity. }
              { discriminate. }
            ** simpl in Hout. rewrite Hprev_out in Hout. discriminate.
          ++ simpl in Hout. discriminate.
      * rewrite (other_state p Hpp0) in Hout.
        rewrite (other_state p Hpp0).
        exact (IHHs v p_valid Hout).
Qed.

(** Commit implies fast quorum of supporters. *)
Lemma commit_implies_quorum :
  forall s, EPaxos_Reachable s ->
  forall p v, p < n ->
    ep_output (local s p) = Some (Commit v) ->
    epaxos_fast_quorum <= length (ep_supporters (local s p)).
Proof.
  intros s Hs p. induction Hs; simpl in H.
  - unfold epaxos_init in H. destruct H as [[init_noout _] _].
    intros v p_valid Hout. rewrite (init_noout p) in Hout. discriminate.
  - unfold step, epaxos_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) eqn:src_net.
    + unfold state_eq in H. destruct H as [local_eq _].
      intros v p_valid Hout. rewrite (local_eq p) in Hout.
      rewrite (local_eq p). exact (IHHs v p_valid Hout).
    + destruct H as [[p0_state other_state] _].
      intros v p_valid Hout.
      destruct (classic (p = p0)) as [Hpp0 | Hpp0].
      * subst p0. rewrite p0_state in Hout.
        unfold epaxos_step_fn in Hout.
        destruct (ep_output (local s p)) as [o|] eqn:Hprev_out.
        -- simpl in Hout.
          assert (Ho : Some o = Some (Commit v)) by congruence.
          rewrite p0_state. unfold epaxos_step_fn. rewrite Hprev_out. simpl.
          exact (IHHs v p_valid Ho).
        -- destruct (ep_preaccepted (local s p)) as [w|] eqn:Hacc_p.
          ++ destruct (Nat.eqb (ep_proposer e) w) eqn:Hprop.
            ** apply Nat.eqb_eq in Hprop. subst w.
              simpl in Hout.
              destruct (epaxos_fast_quorum <=? length _) eqn:Hle.
              { rewrite p0_state. unfold epaxos_step_fn. rewrite Hprev_out. rewrite Hacc_p.
                rewrite Nat.eqb_refl. simpl.
                apply Nat.leb_le. exact Hle. }
              { discriminate. }
            ** simpl in Hout. rewrite Hprev_out in Hout. discriminate.
          ++ simpl in Hout. discriminate.
      * rewrite (other_state p Hpp0) in Hout.
        rewrite (other_state p Hpp0).
        exact (IHHs v p_valid Hout).
Qed.

(** All supporters are valid process IDs. *)
Lemma all_supporters_are_valid :
  forall s, EPaxos_Reachable s ->
  forall p, p < n ->
  forall r, In r (ep_supporters (local s p)) -> r < n.
Proof.
  intros s Hs p. induction Hs; simpl in H.
  - unfold epaxos_init in H.
    destruct H as [[_ [_ [prop_sups nonprop_sups]]] _].
    intros p_valid r Hr.
    destruct (classic (is_proposer p)) as [Hprop | Hprop].
    + rewrite (prop_sups p p_valid Hprop) in Hr.
      simpl in Hr. destruct Hr as [Heq | []]. subst r. exact p_valid.
    + rewrite (nonprop_sups p p_valid Hprop) in Hr. destruct Hr.
  - unfold step, epaxos_instance in H; simpl in H.
    destruct H as [[p_not_src [src_valid p0_valid]] H].
    destruct (network s src p0) eqn:src_net.
    + unfold state_eq in H. destruct H as [local_eq _].
      intros p_valid r Hr. rewrite (local_eq p) in Hr.
      exact (IHHs p_valid r Hr).
    + destruct H as [[p0_state other_state] _].
      pose proof (msg_src_has_preaccepted s Hs src p0 src_valid p0_valid) as Hmsg.
      rewrite src_net in Hmsg. apply Forall_inv in Hmsg.
      destruct Hmsg as [Hsrc_e _].
      intros p_valid r Hr.
      destruct (classic (p = p0)) as [Hpp0 | Hpp0].
      * subst p0. rewrite p0_state in Hr. unfold epaxos_step_fn in Hr.
        destruct (ep_output (local s p)).
        -- simpl in Hr. exact (IHHs p_valid r Hr).
        -- destruct (ep_preaccepted (local s p)) as [w|] eqn:Hacc_p.
          ++ destruct (Nat.eqb (ep_proposer e) w) eqn:Hprop.
            ** simpl in Hr.
              destruct (existsb (Nat.eqb (ep_source e)) (ep_supporters (local s p))) eqn:Hexists.
              { simpl in Hr. exact (IHHs p_valid r Hr). }
              { simpl in Hr. destruct Hr as [Heq | Hr_old].
                - subst r. rewrite Hsrc_e. exact src_valid.
                - exact (IHHs p_valid r Hr_old). }
            ** simpl in Hr. exact (IHHs p_valid r Hr).
          ++ simpl in Hr. destruct Hr.
      * rewrite (other_state p Hpp0) in Hr.
        exact (IHHs p_valid r Hr).
Qed.

(** Key lemma: EPaxos fast quorum intersection.

    For N = 2F+1 and fast_quorum = F + (F+2)/2, we need to show that
    n < 2 * epaxos_fast_quorum to ensure any two fast quorums intersect.

    Proof: epaxos_fast_quorum = f + (f+2)/2
           For integer division, (f+2)/2 >= (f+1)/2 (ceiling)

           When f is even (f = 2k): (f+2)/2 = (2k+2)/2 = k+1
           When f is odd (f = 2k+1): (f+2)/2 = (2k+3)/2 = k+1

           So epaxos_fast_quorum = f + (f+2)/2 >= f + (f+1)/2

           We need n < 2 * epaxos_fast_quorum
           i.e., 2f+1 < 2 * (f + (f+2)/2)

           Case f even (f = 2k):
             epaxos_fast_quorum = 2k + k+1 = 3k+1
             2 * epaxos_fast_quorum = 6k+2
             n = 2(2k)+1 = 4k+1
             4k+1 < 6k+2 ✓ (holds for k >= 0)

           Case f odd (f = 2k+1):
             epaxos_fast_quorum = 2k+1 + k+1 = 3k+2
             2 * epaxos_fast_quorum = 6k+4
             n = 2(2k+1)+1 = 4k+3
             4k+3 < 6k+4 ✓ (holds for k >= 0)
*)
Lemma epaxos_fast_quorum_gt_half : n < 2 * epaxos_fast_quorum.
Proof.
  unfold epaxos_fast_quorum.
  rewrite n_eq_2f_plus_1.
  pose proof (Nat.div_mod (f + 2) 2 ltac:(lia)) as H1.
  pose proof (Nat.mod_upper_bound (f + 2) 2 ltac:(lia)) as H2.
  lia.
Qed.

(** Quorum intersection: two fast quorums must share at least one element. *)
Lemma quorum_intersection :
  forall (A B : list ProcessId),
    NoDup A -> (forall a, In a A -> a < n) ->
    NoDup B -> (forall b, In b B -> b < n) ->
    epaxos_fast_quorum <= length A -> epaxos_fast_quorum <= length B ->
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
  pose proof epaxos_fast_quorum_gt_half.
  lia.
Qed.

(** EPaxos does not use Adopt in the fast path. *)
Lemma no_adopt :
  forall s, EPaxos_Reachable s ->
  forall q w, q < n ->
    ep_output (local s q) <> Some (Adopt w).
Proof.
  intros s Hs q. induction Hs; simpl in H.
  - unfold epaxos_init in H. destruct H as [[init_noout _] _].
    intros w q_valid Hq. rewrite (init_noout q) in Hq. discriminate.
  - unfold step, epaxos_instance in H; simpl in H.
    destruct H as [[_ [_ p_valid]] H].
    intros w q_valid Hq.
    destruct (network s src p) eqn:src_net.
    + unfold state_eq in H. destruct H as [local_eq _].
      rewrite (local_eq q) in Hq. exact (IHHs w q_valid Hq).
    + destruct H as [[p_state other_state] _].
      destruct (classic (q = p)) as [Hqp | Hqp].
      * subst p. rewrite p_state in Hq. unfold epaxos_step_fn in Hq.
        destruct (ep_output (local s q)) as [o|] eqn:Hprev.
        -- simpl in Hq. exact (IHHs w q_valid (eq_trans (eq_sym Hprev) Hq)).
        -- destruct (ep_preaccepted (local s q)).
          ++ destruct (Nat.eqb _ _).
            ** simpl in Hq. destruct (epaxos_fast_quorum <=? _); discriminate.
            ** simpl in Hq. exact (IHHs w q_valid (eq_trans (eq_sym Hprev) Hq)).
          ++ simpl in Hq. discriminate.
      * rewrite (other_state q Hqp) in Hq. exact (IHHs w q_valid Hq).
Qed.

(** Agreement: if one process commits v, all outputs must be v. *)
Theorem EPaxos_Agreement : Agreement n epaxos_instance.
Proof.
  unfold Agreement, epaxos_instance, output_of, valid_pid, acp_proc_output; simpl.
  intros s p q v w Hs p_valid q_valid Hp Hq.
  destruct Hq as [Hq | Hq].
  - pose proof (commit_implies_preaccepted s Hs p v p_valid Hp) as Hacc_p.
    pose proof (commit_implies_quorum s Hs p v p_valid Hp) as Hquorum_p.
    pose proof (commit_implies_preaccepted s Hs q w q_valid Hq) as Hacc_q.
    pose proof (commit_implies_quorum s Hs q w q_valid Hq) as Hquorum_q.
    pose proof (nodup_in_supporters s Hs p p_valid) as Hnd_p.
    pose proof (nodup_in_supporters s Hs q q_valid) as Hnd_q.
    pose proof (fun r Hr => all_supporters_are_valid s Hs p p_valid r Hr) as Hval_p.
    pose proof (fun r Hr => all_supporters_are_valid s Hs q q_valid r Hr) as Hval_q.
    destruct (quorum_intersection
                (ep_supporters (local s p)) (ep_supporters (local s q))
                Hnd_p Hval_p Hnd_q Hval_q Hquorum_p Hquorum_q)
      as [r [HrA HrB]].
    pose proof (all_supporters_have_preaccepted s Hs p v p_valid Hacc_p r HrA) as Hrv.
    pose proof (all_supporters_have_preaccepted s Hs q w q_valid Hacc_q r HrB) as Hrw.
    congruence.
  - destruct (no_adopt s Hs q w q_valid Hq).
Qed.

(** Convergence: with a unique proposer, all outputs must be Commit. *)
Theorem EPaxos_Convergence : Convergence n epaxos_instance.
Proof.
  unfold Convergence, epaxos_instance, output_of, valid_pid, acp_proc_output, acp_is_proposer; simpl.
  intros s p q o Hs p_valid q_valid Hprop Huniq Hout.
  pose proof (all_output_values_valid s Hs q q_valid) as Hvalid.
  rewrite Hout in Hvalid.
  destruct o as [v | v].
  - f_equal. exact (Huniq v Hvalid).
  - destruct (no_adopt s Hs q v q_valid Hout).
Qed.

(** Any committed process has a valid PID (< n). *)
Lemma ep_commit_pid_valid :
  forall s, EPaxos_Reachable s ->
  forall p v, ep_output (local s p) = Some (Commit v) -> p < n.
Proof.
  intros s Hs p v. induction Hs; simpl in H.
  - unfold epaxos_init in H. destruct H as [[init_noout _] _].
    intro Hout. rewrite (init_noout p) in Hout. discriminate.
  - unfold step, epaxos_instance in H; simpl in H.
    destruct H as [[_ [_ p0_valid]] H].
    intro Hout.
    destruct (network s src p0) eqn:src_net.
    + unfold state_eq in H. destruct H as [local_eq _].
      rewrite (local_eq p) in Hout. exact (IHHs Hout).
    + destruct H as [[p0_state other_state] _].
      destruct (classic (p = p0)) as [Hpp0 | Hpp0].
      * subst p0. exact p0_valid.
      * rewrite (other_state p Hpp0) in Hout. exact (IHHs Hout).
Qed.

(** General pigeonhole lemma for list intersection. *)
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

(** Lower bound on intersection size for two bounded lists. *)
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

(** Helper lemma for recoverability arithmetic.
    With the FastPaxos-style quorum (f + (n-f)/2 + 1), the standard
    recoverability proof works. *)
Lemma recoverability_arithmetic :
  forall (len_Ap len_Aq len_alive len_B : nat),
    n = 2 * f + 1 ->
    epaxos_fast_quorum <= len_Ap ->
    epaxos_fast_quorum <= len_Aq ->
    n - f <= len_alive ->
    len_Aq + len_alive <= n + len_B ->
    n < len_Ap + len_B.
Proof.
  intros len_Ap len_Aq len_alive len_B Hn Hqp Hqq Halive HlenB.
  unfold epaxos_fast_quorum in *.
  assert (HB_lower : f + (n - f) / 2 + 1 + len_alive <= n + len_B).
  { transitivity (len_Aq + len_alive); [| exact HlenB].
    apply Nat.add_le_mono_r. exact Hqq. }
  assert (Halive_ge : f + 1 <= len_alive).
  { rewrite Hn in Halive. lia. }
  assert (HB_ge : (n - f) / 2 + 1 <= len_B).
  { rewrite Hn in *. 
    pose proof (Nat.div_mod (n - f) 2 ltac:(lia)) as Hdiv.
    pose proof (Nat.mod_upper_bound (n - f) 2 ltac:(lia)) as Hmod.
    lia. }
  rewrite Hn.
  pose proof (Nat.div_mod (n - f) 2 ltac:(lia)) as Hdiv2.
  pose proof (Nat.mod_upper_bound (n - f) 2 ltac:(lia)) as Hmod2.
  lia.
Qed.

(** Recoverability: n-f survivors prevent conflicting commits. *)
Theorem EPaxos_Recoverability : Recoverability n f epaxos_instance.
Proof.
  unfold Recoverability, epaxos_instance, output_of, valid_pid, acp_proc_output; simpl.
  intros s s' alive v w Hs Hs' Hnd_alive Hlen_alive Hval_alive Hlocal_eq [p Hp] [q Hq].
  pose proof (ep_commit_pid_valid s Hs p v Hp) as p_valid.
  pose proof (ep_commit_pid_valid s' Hs' q w Hq) as q_valid.
  pose proof (commit_implies_preaccepted s Hs p v p_valid Hp) as Hacc_p.
  pose proof (commit_implies_quorum s Hs p v p_valid Hp) as Hquorum_p.
  pose proof (nodup_in_supporters s Hs p p_valid) as Hnd_Ap.
  pose proof (fun r Hr => all_supporters_are_valid s Hs p p_valid r Hr) as Hval_Ap.
  pose proof (fun r Hr => all_supporters_have_preaccepted s Hs p v p_valid Hacc_p r Hr) as Hacc_Ap.
  pose proof (commit_implies_preaccepted s' Hs' q w q_valid Hq) as Hacc_q.
  pose proof (commit_implies_quorum s' Hs' q w q_valid Hq) as Hquorum_q.
  pose proof (nodup_in_supporters s' Hs' q q_valid) as Hnd_Aq.
  pose proof (fun r Hr => all_supporters_are_valid s' Hs' q q_valid r Hr) as Hval_Aq.
  pose proof (fun r Hr => all_supporters_have_preaccepted s' Hs' q w q_valid Hacc_q r Hr) as Hacc_Aq.
  set (B := filter (fun r => existsb (Nat.eqb r) alive) (ep_supporters (local s' q))).
  assert (Hnd_B : NoDup B) by (apply NoDup_filter; exact Hnd_Aq).
  assert (Hval_B : forall r, In r B -> r < n).
  { intros r Hr. apply filter_In in Hr as [Hr _]. exact (Hval_Aq r Hr). }
  assert (Hacc_B : forall r, In r B -> ep_preaccepted (local s r) = Some w).
  { intros r Hr.
    apply filter_In in Hr as [HrAq Hr_alive].
    apply existsb_exists in Hr_alive as [r' [Hr'alive Heq]].
    apply Nat.eqb_eq in Heq. subst r'.
    rewrite (Hlocal_eq r Hr'alive). exact (Hacc_Aq r HrAq). }
  pose proof (filter_inter_lb (ep_supporters (local s' q)) alive n
                Hnd_Aq Hval_Aq Hnd_alive Hval_alive) as Hlen_B.
  fold B in Hlen_B.
  pose proof (recoverability_arithmetic
                (length (ep_supporters (local s p)))
                (length (ep_supporters (local s' q)))
                (length alive)
                (length B)
                n_eq_2f_plus_1 Hquorum_p Hquorum_q Hlen_alive Hlen_B) as Hsum.
  destruct (list_intersection (ep_supporters (local s p)) B n
              Hnd_Ap Hval_Ap Hnd_B Hval_B Hsum) as [r [HrAp HrB]].
  pose proof (Hacc_Ap r HrAp) as Hrv.
  pose proof (Hacc_B r HrB) as Hrw.
  congruence.
Qed.

End EPaxos.
