From Stdlib Require Import Lia Ascii.
From DAnalyzer.Abstract Require Import TransitionSound.
From DAnalyzer.Examples Require Import TrivialDomain.
Import ListNotations.
Set Implicit Arguments.

(* A concrete injection is needed only to run examples. The analysis remains
   parameterized by an arbitrary injective address map. *)
Fixpoint name_code (s : string) : nat :=
  match s with
  | EmptyString => 1%nat
  | String ch tail => (nat_of_ascii ch + 256 * name_code tail)%nat
  end.
Lemma name_code_positive s : (0 < name_code s)%nat.
Proof. induction s; simpl; lia. Qed.
Lemma name_code_injective s t : name_code s = name_code t -> s = t.
Proof.
  revert t. induction s as [|a s IH]; intros [|b t] Heq; simpl in Heq; auto.
  - pose proof (name_code_positive t). lia.
  - pose proof (name_code_positive s). lia.
  - pose proof (nat_ascii_bounded a) as Ha.
    pose proof (nat_ascii_bounded b) as Hb.
    assert (Htail : name_code s = name_code t) by lia.
    assert (Hchar : nat_of_ascii a = nat_of_ascii b) by lia.
    apply IH in Htail. subst t.
    apply (f_equal ascii_of_nat) in Hchar.
    rewrite !ascii_nat_embedding in Hchar. now subst b.
Qed.
Definition example_memory : AddressMap.
Proof.
  refine {| addr := fun x => Z.of_nat (name_code x) |}.
  intros x y H. apply name_code_injective, Nat2Z.inj, H.
Defined.
Definition X : Var := "x"%string.
Definition Y : Var := "y"%string.
Definition Zvar : Var := "z"%string.
Definition Ptr : Var := "p"%string.
Definition mem (x y z p : Z) : Memory :=
  fun a => if Z.eq_dec a (addr example_memory X) then x
           else if Z.eq_dec a (addr example_memory Y) then y
           else if Z.eq_dec a (addr example_memory Zvar) then z
           else if Z.eq_dec a (addr example_memory Ptr) then p else 0.

Example arithmetic m : @eval example_memory m
  (ELt (ENeg (EMul (EInt 2) (EInt 3))) (EInt 0)) 1.
Proof. change (@eval example_memory m (ELt (ENeg (EMul (EInt 2) (EInt 3))) (EInt 0))
  (if Z.ltb (- (2 * 3)) 0 then 1 else 0)). repeat constructor. Qed.
Example arbitrary_input_sum m n : @eval example_memory m (EAdd ERead ERead) n.
Proof. replace n with (n + 0)%Z by lia. repeat constructor. Qed.
Example input_guard_both m :
  @assume example_memory ERead true (fun m' => m' = m) m /\
  @assume example_memory ERead false (fun m' => m' = m) m.
Proof.
  split; split; try reflexivity.
  - exists 1. split; [constructor|discriminate].
  - exists 0. split; [constructor|reflexivity].
Qed.

Definition two_inputs : set Memory :=
  fun m => m = mem 0 0 0 0 \/ m = mem 10 10 0 0.
Definition increment := EAdd (EVar X) (EInt 1).
Example correlated_assignment_zero :
  @assign example_memory X increment two_inputs (update (mem 0 0 0 0) (addr example_memory X) 1).
Proof.
  exists (mem 0 0 0 0), 1. split; [left; reflexivity|].
  split; [apply (EvalAdd (M := example_memory)) with (u := 0) (v := 1); constructor|reflexivity].
Qed.
Example correlated_assignment_ten :
  @assign example_memory X increment two_inputs (update (mem 10 10 0 0) (addr example_memory X) 11).
Proof.
  exists (mem 10 10 0 0), 11. split; [right; reflexivity|].
  split; [apply (EvalAdd (M := example_memory)) with (u := 10) (v := 1); constructor|reflexivity].
Qed.
Example no_cross_memory_assignment : ~ @assign example_memory X increment two_inputs (mem 1 10 0 0).
Proof.
  intros [m [v [[Hm|Hm] [He Hu]]]]; subst m.
  - pose proof (f_equal (fun m => m (addr example_memory Y)) Hu) as H. discriminate H.
  - inversion He; subst.
    repeat match goal with
    | H : @eval example_memory _ (EVar _) _ |- _ => inversion H; clear H; subst
    | H : @eval example_memory _ (EInt _) _ |- _ => inversion H; clear H; subst
    end.
    pose proof (f_equal (fun m => m (addr example_memory X)) Hu) as H. discriminate H.
Qed.

Example aliased_store :
  @store example_memory Ptr (EAdd (EDeref Ptr) (EInt 1))
    (fun m => m = mem 5 0 0 (addr example_memory X))
    (update (mem 5 0 0 (addr example_memory X)) (addr example_memory X) 6).
Proof.
  exists (mem 5 0 0 (addr example_memory X)), 6. repeat split; auto.
  apply (EvalAdd (M := example_memory)) with (u := 5) (v := 1).
  - apply EvalDeref.
  - constructor.
Qed.
Example address_expression m : @eval example_memory m (EAddr X) (addr example_memory X).
Proof. exact (@EvalAddr example_memory m X). Qed.
Example integer_dereference :
  eval example_memory (mem 5 0 0 (-7)) (EDeref Ptr) 0.
Proof. apply EvalDeref. Qed.
Example integer_store :
  store example_memory Ptr (EInt 42) (fun m => m = mem 5 0 0 (-7))
    (update (mem 5 0 0 (-7)) (-7) 42).
Proof. exists (mem 5 0 0 (-7)), 42. repeat split; constructor. Qed.
Definition missing_target : Program.
Proof.
  refine {| root := CGoto 50 (EInt 999) |}.
  repeat constructor; simpl; intuition discriminate.
Defined.
Example invalid_goto q m' :
  ~ @step example_memory missing_target (At 50, mem 0 0 0 0) (q, m').
Proof.
  intros H. inversion H; subst; cbn in *; try discriminate.
  match goal with H : Some _ = Some (CGoto _ _) |- _ => inversion H; subst end.
  match goal with H : _ = _ \/ False |- _ => destruct H as [H|[]]; subst end.
  match goal with H : @eval example_memory _ (EInt _) _ |- _ =>
    apply (eval_int_iff example_memory) in H; discriminate end.
Qed.

Definition false_loop : Program.
Proof.
  refine {| root := CRepeat 20 (CAssign 40 X (EInt 9)) (EInt 0) |}.
  repeat constructor; simpl; intuition discriminate.
Defined.
Definition true_loop : Program.
Proof.
  refine {| root := CRepeat 20 (CAssign 40 X (EVar X)) (EInt 1) |}.
  repeat constructor; simpl; intuition discriminate.
Defined.

Example repeat_entry_is_body : entry false_loop = At 40 /\
  label (root false_loop) = 40%nat /\ node_label (root false_loop) = 20%nat.
Proof. repeat split; reflexivity. Qed.
Example repeat_body_runs_before_false_test m :
  @step example_memory false_loop (entry false_loop, m)
    (At 20, update m (addr example_memory X) 9).
Proof. eapply StepAssign; try reflexivity. constructor. Qed.
Example false_repeat_body_step m q m' :
  @step example_memory false_loop (entry false_loop, m) (q, m') ->
  q = At 20 /\ m' = update m (addr example_memory X) 9.
Proof.
  intros H. inversion H; subst; cbn in *; try discriminate.
  match goal with H : Some _ = Some (CAssign _ _ _) |- _ => inversion H; subst end.
  match goal with H : @eval example_memory _ (EInt _) _ |- _ =>
    apply (eval_int_iff example_memory) in H; subst end.
  split; [congruence|reflexivity].
Qed.
Example repeat_false_exits_after_test m : @step example_memory false_loop (At 20, m) (Halt, m).
Proof.
  eapply StepRepeatFalse with (v := 0); try reflexivity. constructor.
Qed.
Example false_repeat_test_exits m q m' :
  @step example_memory false_loop (At 20, m) (q, m') -> q = Halt /\ m' = m.
Proof.
  intros H. inversion H; subst; cbn in *; try discriminate;
    match goal with H : Some _ = Some (CRepeat _ _ _) |- _ => inversion H; subst end.
  - match goal with H : @eval example_memory _ (EInt _) _ |- _ =>
      apply (eval_int_iff example_memory) in H; subst end.
    contradiction.
  - split; congruence.
Qed.
Example true_repeat_reenters_body m : @step example_memory true_loop (At 20, m) (At 40, m).
Proof.
  eapply StepRepeatTrue with (v := 1); try reflexivity; [constructor|discriminate].
Qed.
Example body_returns_to_test m :
  @step example_memory true_loop (At 40, m) (At 20, update m (addr example_memory X) (m (addr example_memory X))).
Proof. eapply StepAssign; try reflexivity. constructor. Qed.
Lemma true_loop_cannot_halt s m' : ~ @step example_memory true_loop s (Halt, m').
Proof.
  destruct s as [p m]. intros H.
  pose proof (proj1 (step_points H)) as Hp.
  cbn in Hp. destruct Hp as [<-|[<-|[<-|[]]]].
  - eapply halt_stuck; eauto.
  - inversion H; subst; cbn in *; try discriminate.
    match goal with H : Some _ = Some (CRepeat _ _ _) |- _ => inversion H; subst end.
    match goal with H : @eval example_memory _ (EInt _) _ |- _ =>
      apply (eval_int_iff example_memory) in H; subst end.
    discriminate.
  - inversion H; subst; cbn in *; discriminate.
Qed.
Example true_loop_no_final_memory M0 m : ~ @Reach example_memory true_loop M0 (Halt, m).
Proof.
  intros H. apply Reach_finite in H. inversion H; subst.
  - destruct H0 as [Hentry _]. discriminate Hentry.
  - eapply true_loop_cannot_halt; eauto.
Qed.

(* The nested example in the solution: an interior jump escapes the repeat. *)
Definition nested : Program.
Proof.
  refine {| root := CSeq 10
    (CRepeat 20 (CIf 30 (EVar Y)
      (CAssign 40 X (EAdd (EVar X) (ENeg (EInt 1))))
      (CGoto 50 (EInt 70))) (EVar X))
    (CSeq 60 (CAssign 70 Y (EInt 1)) (CAssign 80 Zvar (EInt 2))) |}.
  repeat constructor; simpl; intuition discriminate.
Defined.
Definition m0 := mem 1 0 0 0.
Definition m1 := update m0 (addr example_memory Y) 1.
Definition m2 := update m1 (addr example_memory Zvar) 2.

Example nested_lexical_context :
  lookup nested 50 = Some (CGoto 50 (EInt 70), At 20) /\
  lookup nested 70 = Some (CAssign 70 Y (EInt 1), At 80).
Proof. split; reflexivity. Qed.
Example nested_successors :
  next nested 10 = Some (At 30) /\
  nextTrue nested 20 = Some (At 30) /\
  nextFalse nested 20 = Some (At 60) /\
  next nested 40 = Some (At 20) /\
  next nested 70 = Some (At 80).
Proof. repeat split; reflexivity. Qed.
Example goto_has_no_static_successor :
  cont nested 50 = Some (At 20) /\
  next nested 50 = None /\ nextTrue nested 50 = None /\ nextFalse nested 50 = None.
Proof. repeat split; reflexivity. Qed.
Example nested_jump m : @step example_memory nested (At 50, m) (At 70, m).
Proof. eapply StepGoto; [reflexivity|constructor|cbn; auto 20]. Qed.
Example interior_jump_has_no_return :
  @path example_memory nested (At 10, m0) (Halt, m2).
Proof.
  eapply PathCons with (t := (At 30, m0)).
  - eapply StepSeq; reflexivity.
  - eapply PathCons with (t := (At 50, m0)).
    + eapply StepIfFalse with (v := 0); try reflexivity. constructor.
    + eapply PathCons with (t := (At 70, m0)).
      * apply nested_jump.
      * eapply PathCons with (t := (At 80, m1)).
        -- eapply StepAssign; try reflexivity. constructor.
        -- eapply PathCons with (t := (Halt, m2)).
           ++ eapply StepAssign; try reflexivity. constructor.
           ++ constructor.
Qed.
Example nested_final_reachable : @Reach example_memory nested (fun m => m = m0) (Halt, m2).
Proof.
  apply Reach_finite, reachable_path. exists (At 10, m0).
  split; [split; reflexivity|exact interior_jump_has_no_return].
Qed.
Example instantiated_soundness M0 :
  subset (@Reach example_memory nested M0)
    (gamma_state (trivial_domain example_memory)
      (@Reach_sharp example_memory nested (trivial_domain example_memory) tt)).
Proof. apply (reachability_sound (M := example_memory)). intros m H. exact I. Qed.
Example bottom_really_denotes_memory :
  gamma (trivial_domain example_memory) bottom m0.
Proof. exact I. Qed.

Definition body_changes_guard : Program.
Proof.
  refine {| root := CRepeat 1 (CAssign 2 X (EInt 0)) (EVar X) |}.
  repeat constructor; simpl; intuition discriminate.
Defined.
Example repeat_guard_uses_body_memory m :
  @path example_memory body_changes_guard (entry body_changes_guard, m)
    (Halt, update m (addr example_memory X) 0).
Proof.
  eapply PathCons with (t := (At 1, update m (addr example_memory X) 0)).
  - eapply StepAssign; try reflexivity. constructor.
  - econstructor; [|constructor].
    eapply StepRepeatFalse with (v := 0); try reflexivity.
    pose proof (@EvalVar example_memory (update m (addr example_memory X) 0) X) as Heval.
    rewrite update_same in Heval. exact Heval.
Qed.

Definition nested_repeats : Program.
Proof.
  refine {| root := CRepeat 1 (CRepeat 2 (CAssign 3 X (EInt 9)) (EInt 0)) (EInt 0) |}.
  repeat constructor; simpl; intuition discriminate.
Defined.
Example nested_repeat_entry_and_continuations :
  entry nested_repeats = At 3 /\
  next nested_repeats 3 = Some (At 2) /\
  nextTrue nested_repeats 2 = Some (At 3) /\
  nextFalse nested_repeats 2 = Some (At 1) /\
  nextTrue nested_repeats 1 = Some (At 3) /\
  nextFalse nested_repeats 1 = Some Halt.
Proof. repeat split; reflexivity. Qed.

Definition repeat_branch : Program.
Proof.
  refine {| root := CSeq 1 (CAssign 2 X (EInt 0))
    (CIf 3 (EVar X)
      (CRepeat 4 (CAssign 5 X (EInt 9)) (EInt 0))
      (CRepeat 6 (CAssign 7 X (EInt 8)) (EInt 0))) |}.
  repeat constructor; simpl; intuition discriminate.
Defined.
Example branches_enter_repeat_bodies :
  nextTrue repeat_branch 3 = Some (At 5) /\
  nextFalse repeat_branch 3 = Some (At 7).
Proof. split; reflexivity. Qed.
