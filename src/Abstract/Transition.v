From DAnalyzer.Abstract Require Export Domain.
From DAnalyzer.Language Require Export ControlFlow.
Require Export DAnalyzer.Foundations.Fixpoint.
Import ListNotations.
Set Implicit Arguments.

Section AbstractTransitions.
Context {M : AddressMap} (P : Program) (D : AbstractDomain M).
Local Notation L := (memory_cpo D).
Definition AbstractState := point -> carrier L.
Definition state_cpo := map_cpo point L.
Definition gamma_state (a : AbstractState) : set (point * Memory) :=
  fun s => gamma D (a (fst s)) (snd s).
Definition alpha_state (X : set (point * Memory)) : AbstractState :=
  fun p => alpha D (fun m => X (p, m)).
Theorem state_galois X a :
  @le state_cpo (alpha_state X) a <-> subset X (gamma_state a).
Proof.
  split.
  - intros H [p m] Hm. apply (proj1 (galois D _ _) (H p)), Hm.
  - intros H p. apply (proj2 (galois D _ _)). intros m Hm. apply (H (p, m)), Hm.
Qed.
Lemma gamma_state_mono a b :
  @le state_cpo a b -> subset (gamma_state a) (gamma_state b).
Proof. intros H [p m] Hm. eapply gamma_mono; [apply H|exact Hm]. Qed.

(* Syntax-directed local transitions, matching the concrete rule cases. *)
Inductive local_step : point -> carrier L -> point -> carrier L -> Prop :=
| LocalAssign l x e q a :
    command_at P l = Some (CAssign l x e) -> next P l = Some q ->
    local_step (At l) a q (assign_sharp D x e a)
| LocalStore l x e q a :
    command_at P l = Some (CStore l x e) -> next P l = Some q ->
    local_step (At l) a q (store_sharp D x e a)
| LocalSeq l c1 c2 q a :
    command_at P l = Some (CSeq l c1 c2) -> next P l = Some q ->
    local_step (At l) a q a
| LocalIfTrue l e c1 c2 q a :
    command_at P l = Some (CIf l e c1 c2) -> nextTrue P l = Some q ->
    local_step (At l) a q (assume_sharp D e true a)
| LocalIfFalse l e c1 c2 q a :
    command_at P l = Some (CIf l e c1 c2) -> nextFalse P l = Some q ->
    local_step (At l) a q (assume_sharp D e false a)
| LocalRepeatTrue l c e q a :
    command_at P l = Some (CRepeat l c e) -> nextTrue P l = Some q ->
    local_step (At l) a q (assume_sharp D e true a)
| LocalRepeatFalse l c e q a :
    command_at P l = Some (CRepeat l c e) -> nextFalse P l = Some q ->
    local_step (At l) a q (assume_sharp D e false a)
| LocalGoto l e t a :
    command_at P l = Some (CGoto l e) -> In t (labels (root P)) ->
    local_step (At l) a (At t) (target_sharp D e t a).

Lemma local_step_mono p a q b a' :
  local_step p a q b -> le a a' ->
  exists b', local_step p a' q b' /\ le b b'.
Proof.
  intros H Ha. destruct H.
  - eexists. split; [eapply LocalAssign; eauto|apply assign_monotone, Ha].
  - eexists. split; [eapply LocalStore; eauto|apply store_monotone, Ha].
  - eexists. split; [eapply LocalSeq; eauto|exact Ha].
  - eexists. split; [eapply LocalIfTrue; eauto|apply assume_monotone, Ha].
  - eexists. split; [eapply LocalIfFalse; eauto|apply assume_monotone, Ha].
  - eexists. split; [eapply LocalRepeatTrue; eauto|apply assume_monotone, Ha].
  - eexists. split; [eapply LocalRepeatFalse; eauto|apply assume_monotone, Ha].
  - eexists. split; [eapply LocalGoto; eauto|apply target_monotone, Ha].
Qed.

(* Apply the domain's abstract union to all local results at each destination. *)
Definition Step_sharp (a : AbstractState) : AbstractState :=
  fun q => unions_sharp D (fun b => exists p, local_step p (a p) q b).

(* A derived characterization by graph, partition, and join. *)
Definition Graph (a : AbstractState) : set (point * carrier L) :=
  fun s => snd s = a (fst s).
Definition Post (X : set (point * carrier L)) : set (point * carrier L) :=
  fun t => exists s, X s /\ local_step (fst s) (snd s) (fst t) (snd t).
Definition partition (X : set (point * carrier L)) p : set (carrier L) :=
  fun a => X (p, a).
Definition join_partition (X : point -> set (carrier L)) : AbstractState :=
  fun p => unions_sharp D (X p).

Theorem partition_join a p :
  @equiv L (Step_sharp a p) (join_partition (partition (Post (Graph a))) p).
Proof.
  split; apply unions_monotone.
  - intros b [q Hstep]. exists b. split; [|apply le_refl].
    exists (q, a q). split; [reflexivity|exact Hstep].
  - intros b [[q v] [Hv Hstep]]. unfold Graph in Hv. simpl in *. subst v.
    exists b. split; [exists q; exact Hstep|apply le_refl].
Qed.
Lemma Step_sharp_covers a p q b :
  local_step p (a p) q b ->
  subset (gamma D b) (gamma D (Step_sharp a q)).
Proof.
  intros H. apply unions_sound. exists p. exact H.
Qed.
Lemma Step_sharp_mono : @monotone state_cpo state_cpo Step_sharp.
Proof.
  intros a a' Ha q. apply unions_monotone.
  intros b [p Hstep].
  destruct (local_step_mono (a' p) Hstep (Ha p)) as [b' [Hstep' Hb]].
  exists b'. split; [exists p; exact Hstep'|exact Hb].
Qed.

Definition initial_sharp (a0 : carrier L) : AbstractState :=
  fun p => if point_eq_dec p (entry P) then a0 else bottom.
Definition F_sharp (a0 : carrier L) (a : AbstractState) : AbstractState :=
  fun p => union_sharp D (initial_sharp a0 p) (Step_sharp a p).
Lemma F_sharp_mono a0 : @monotone state_cpo state_cpo (F_sharp a0).
Proof.
  intros a b H p. apply union_sharp_mono; [apply le_refl|apply Step_sharp_mono, H].
Qed.
Definition Reach_sharp (a0 : carrier L) : AbstractState :=
  @iteration_limit state_cpo (F_sharp a0).

(* Continuity additionally establishes that this limit is a fixed point. *)
Lemma Reach_sharp_fixed a0 :
  @omega_continuous state_cpo (F_sharp a0) ->
  @equiv state_cpo (F_sharp a0 (Reach_sharp a0)) (Reach_sharp a0).
Proof. intros Hcont. apply lfp_fixed; [apply F_sharp_mono|exact Hcont]. Qed.
End AbstractTransitions.

(* Public definitions keep the selected domain visible at call sites. *)
Arguments gamma_state {M} D a _.
Arguments alpha_state {M} D X _.
Arguments Step_sharp {M} P D a _.
Arguments initial_sharp {M} P D a0 _.
Arguments F_sharp {M} P D a0 a _.
