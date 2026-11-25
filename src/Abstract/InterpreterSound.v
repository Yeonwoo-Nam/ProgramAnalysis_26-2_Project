From DAnalyzer.Abstract Require Export Interpreter.
Set Implicit Arguments.

Section InterpreterSoundness.
Context {M : AddressMap} (P : Program) (D : AbstractDomain M).

(* Quantify over all represented concrete inputs, so recursive calls can use
   the over-approximation returned by a primitive abstract transfer. *)
Definition interpreter_env_sound (J : InterpreterEnv) (K : AbstractInterpreterEnv D) :=
  forall c X a, subset X (gamma D a) -> subset (J c X) (gamma D (K c a)).
Lemma resume_sound J K : interpreter_env_sound J K ->
  forall q X a, subset X (gamma D a) ->
    subset (resume P J q X) (gamma D (resume_sharp P D K q a)).
Proof.
  intros H [|l] X a HX; simpl; [exact HX|].
  destruct (lookup P l) as [[c k]|]; [apply H, HX|apply empty_subset].
Qed.
Lemma follow_sound J K : interpreter_env_sound J K ->
  forall q X a, subset X (gamma D a) ->
    subset (follow P J q X) (gamma D (follow_sharp P D K q a)).
Proof. intros H [p|] X a HX; [apply resume_sound; assumption|apply empty_subset]. Qed.

Theorem interpreter_body_sound J K : interpreter_env_sound J K ->
  interpreter_env_sound (interpreter_body M P J) (interpreter_body_sharp P D K).
Proof.
  intros H c X a HX.
  assert (HB : forall e b, subset (assume M e b X) (gamma D (assume_sharp D e b a))).
  { intros e b. eapply subset_trans; [apply assume_mono, HX|apply assume_sound]. }
  destruct c; cbn [interpreter_body interpreter_body_sharp].
  - apply follow_sound; [exact H|].
    eapply subset_trans; [apply assign_mono, HX|apply assign_sound].
  - apply follow_sound; [exact H|].
    eapply subset_trans; [apply store_mono, HX|apply store_sound].
  - apply follow_sound; assumption.
  - intros m [Hm|Hm]; [apply gamma_union_left|apply gamma_union_right];
      eapply follow_sound; eauto.
  - intros m [Hm|Hm]; [apply gamma_union_left|apply gamma_union_right];
      eapply follow_sound; eauto.
  - intros m [t [Ht Hm]].
    eapply (unions_sound D); [exists t; split; [exact Ht|reflexivity]|].
    eapply resume_sound; [exact H| |exact Hm].
    eapply subset_trans; [apply target_mono, HX|apply target_sound].
Qed.

Lemma interpreter_iterate_sound n :
  interpreter_env_sound (@iterate interpreter_cpo (interpreter_body M P) n)
    (@iterate (interpreter_sharp_cpo D) (interpreter_body_sharp P D) n).
Proof.
  induction n as [|n IH]; [intros c X a HX; apply empty_subset|].
  apply interpreter_body_sound, IH.
Qed.
Theorem interpreter_node_sound c X a : subset X (gamma D a) ->
  subset (interpret_node M P c X) (gamma D (interpret_node_sharp P D c a)).
Proof.
  intros HX m H. apply env_sup in H. destruct H as [n H].
  eapply gamma_mono.
  - exact (@iteration_limit_upper (interpreter_sharp_cpo D)
      (interpreter_body_sharp P D) (@interpreter_body_sharp_mono M P D) n c a).
  - eapply interpreter_iterate_sound; eauto.
Qed.
Theorem interpreter_sound c X a : subset X (gamma D a) ->
  subset (interpret M P c X) (gamma D (interpret_sharp P D c a)).
Proof.
  intros HX. apply resume_sound; [intros d Y b HY; apply interpreter_node_sound, HY|exact HX].
Qed.
Corollary interpreter_gamma_sound c a :
  subset (interpret M P c (gamma D a)) (gamma D (interpret_sharp P D c a)).
Proof. apply interpreter_sound, subset_refl. Qed.
Corollary outputs_sound X a : subset X (gamma D a) ->
  subset (outputs M P X) (gamma D (outputs_sharp P D a)).
Proof. apply interpreter_sound. Qed.
Corollary alpha_outputs_sound X :
  subset (outputs M P X) (gamma D (outputs_sharp P D (alpha D X))).
Proof. apply outputs_sound, alpha_covers. Qed.
End InterpreterSoundness.
