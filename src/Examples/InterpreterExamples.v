From DAnalyzer.Abstract Require Import InterpreterSound.
From DAnalyzer.Examples Require Import Examples TrivialDomain.
Set Implicit Arguments.

Example interpreter_interior_jump : outputs example_memory nested (fun m => m = m0) m2.
Proof. apply outputs_reach, nested_final_reachable. Qed.
Example interpreter_divergence X m : ~ outputs example_memory true_loop X m.
Proof. rewrite outputs_reach. apply true_loop_no_final_memory. Qed.

Lemma halt_path_identity (M : AddressMap) P m n :
  path M P (Halt, m) (Halt, n) -> m = n.
Proof.
  intros H. inversion H; subst; [reflexivity|]. exfalso. eapply halt_stuck; eauto.
Qed.
Example interpreter_false_repeat X m : outputs example_memory false_loop X m <-> X m.
Proof.
  unfold outputs. split.
  - intros H. apply (proj1 (interpret_returns example_memory false_loop _ (command_self _) X)) in H.
    destruct H as [n [HX Hp]]. inversion Hp; subst. destruct t as [q u].
    match goal with Hs : step _ _ _ _ |- _ =>
      apply false_repeat_does_not_enter in Hs; destruct Hs as [Hq Hn]; subst end.
    match goal with Hpath : path _ _ (Halt, _) (Halt, _) |- _ =>
      apply halt_path_identity in Hpath; subst end. exact HX.
  - intros H. apply (proj2 (interpret_returns example_memory false_loop _ (command_self _) X)).
    exists m. split; [exact H|]. econstructor; [apply repeat_tests_before_body|constructor].
Qed.
Example interpreter_missing_target X m : ~ outputs example_memory missing_target X m.
Proof.
  unfold outputs. intros H.
  apply (proj1 (interpret_returns example_memory missing_target _ (command_self _) X)) in H.
  destruct H as [n [HX Hp]]. inversion Hp; subst.
  match goal with Hs : step _ _ _ _ |- _ =>
    inversion Hs; subst; cbn in *; try discriminate end.
  match goal with H : Some _ = Some (CGoto _ _) |- _ => inversion H; subst end.
  match goal with H : _ = _ \/ False |- _ => destruct H as [H|[]]; subst end.
  match goal with H : eval _ _ (EInt _) _ |- _ =>
    apply (eval_int_iff example_memory) in H; discriminate end.
Qed.

(* readInt can jump directly into a branch whose guard is false. The branch
   then uses its lexical continuation, which terminates this program. *)
Definition input_jump : Program.
Proof.
  refine {| root := CSeq 1 (CGoto 2 ERead)
    (CIf 3 (EInt 0) (CAssign 4 X (EInt 7)) (CAssign 5 X (EInt 9))) |}.
  repeat constructor; simpl; intuition discriminate.
Defined.
Example interpreter_input_jump m :
  outputs example_memory input_jump (fun n => n = m) (update m (addr example_memory X) 7).
Proof.
  apply outputs_reach, Reach_finite, reachable_path.
  exists (entry input_jump, m). split; [split; reflexivity|].
  eapply PathCons with (t := (At 2, m)).
  - eapply StepSeq; reflexivity.
  - eapply PathCons with (t := (At 4, m)).
    + eapply StepGoto; [reflexivity|constructor|cbn; auto 10].
    + econstructor; [eapply StepAssign; try reflexivity; constructor|constructor].
Qed.
Example instantiated_interpreter_soundness X :
  subset (outputs example_memory nested X)
    (gamma (trivial_domain example_memory)
      (outputs_sharp nested (trivial_domain example_memory) tt)).
Proof. apply outputs_sound. intros m H. exact I. Qed.
