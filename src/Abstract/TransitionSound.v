From DAnalyzer.Abstract Require Export Transition.
From DAnalyzer.Language Require Export Semantics.
Set Implicit Arguments.

Section Soundness.
Context {M : AddressMap} (P : Program) (D : AbstractDomain M).
Local Notation L := (memory_cpo D).

(* Each concrete syntax rule is covered by the matching abstract rule. *)
Theorem local_simulation p a q m m' :
  gamma D a m -> step M P (p, m) (q, m') ->
  exists b, @local_step M P D p a q b /\ gamma D b m'.
Proof.
  intros Hm Hstep. inversion Hstep; subst.
  - eexists. split; [eapply LocalAssign; eauto|].
    apply assign_sound. exists m, v. auto.
  - eexists. split; [eapply LocalStore; eauto|].
    apply store_sound. exists m, v. auto.
  - exists a. split; [eapply LocalSeq; eauto|exact Hm].
  - eexists. split; [eapply LocalIfTrue; eauto|].
    apply assume_sound. split; [exact Hm|]. exists v. auto.
  - eexists. split; [eapply LocalIfFalse; eauto|].
    apply assume_sound. split; [exact Hm|]. exists v. auto.
  - eexists. split; [eapply LocalRepeatTrue; eauto|].
    apply assume_sound. split; [exact Hm|]. exists v. auto.
  - eexists. split; [eapply LocalRepeatFalse; eauto|].
    apply assume_sound. split; [exact Hm|]. exists v. auto.
  - eexists. split; [eapply LocalGoto; eauto|].
    apply target_sound. split; assumption.
Qed.

Theorem Step_sound a :
  subset (Step M P (gamma_state D a)) (gamma_state D (Step_sharp P D a)).
Proof.
  intros [q m'] [[p m] [Hm Hstep]].
  unfold gamma_state in *. simpl in *.
  destruct (local_simulation (a p) Hm Hstep) as [b [Hb Hm']].
  eapply Step_sharp_covers; [exact Hb|exact Hm'].
Qed.

Lemma initial_sound M0 a0 : subset M0 (gamma D a0) ->
  subset (initial P M0) (gamma_state D (initial_sharp P D a0)).
Proof.
  intros H [p m] [Hp Hm]. simpl in *. subst p.
  change (gamma D (if point_eq_dec (entry P) (entry P) then a0 else bottom) m).
  destruct (point_eq_dec (entry P) (entry P)); [apply H, Hm|congruence].
Qed.

Theorem F_sound M0 a0 a : subset M0 (gamma D a0) ->
  subset (F M P M0 (gamma_state D a)) (gamma_state D (F_sharp P D a0 a)).
Proof.
  intros H [p m] [Hi|Hs].
  - apply gamma_union_left. eapply initial_sound; eauto.
  - apply gamma_union_right. apply Step_sound, Hs.
Qed.

(* A closed abstract invariant suffices; it need not be the least one. *)
Theorem invariant_sound M0 a0 a :
  subset M0 (gamma D a0) -> @le (state_cpo D) (F_sharp P D a0 a) a ->
  subset (Reach M P M0) (gamma_state D a).
Proof.
  intros Hin Hclosed. apply (@lfp_least (set_cpo state) (F M P M0));
    [apply F_mono|].
  intros s Hs. eapply gamma_state_mono; [exact Hclosed|].
  eapply F_sound; eauto.
Qed.

Theorem reachability_sound M0 a0 : subset M0 (gamma D a0) ->
  subset (Reach M P M0) (gamma_state D (Reach_sharp P D a0)).
Proof.
  intros H. apply (@iteration_limit_sound (set_cpo state) (state_cpo D)
    (F M P M0) (F_sharp P D a0) (gamma_state D)).
  - apply F_mono.
  - apply F_sharp_mono.
  - intros a b Hab. apply gamma_state_mono, Hab.
  - intros a. apply F_sound, H.
Qed.

Corollary alpha_reachability_sound M0 :
  subset (Reach M P M0) (gamma_state D (Reach_sharp P D (alpha D M0))).
Proof. apply reachability_sound, alpha_covers. Qed.
End Soundness.
