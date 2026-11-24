From DAnalyzer.Abstract Require Export Domain.
From DAnalyzer.Language Require Export Interpreter.
Set Implicit Arguments.

(** * Definitions *)

Section AbstractInterpreter.
Context {M : AddressMap} (P : Program) (D : AbstractDomain M).
Local Notation L := (memory_cpo D).
Definition interpreter_sharp_cpo := map_cpo cmd (map_cpo (carrier L) L).
Definition AbstractInterpreterEnv := carrier interpreter_sharp_cpo.

Definition resume_sharp (J : AbstractInterpreterEnv) q a : carrier L :=
  match q with
  | Halt => a
  | At l => match lookup P l with Some (c, _) => J c a | None => bottom end
  end.
Definition follow_sharp (J : AbstractInterpreterEnv) q a : carrier L :=
  match q with Some p => resume_sharp J p a | None => bottom end.
Definition interpreter_body_sharp (J : AbstractInterpreterEnv) : AbstractInterpreterEnv :=
  fun c a => match c with
  | CAssign l x e => follow_sharp J (next P l) (assign_sharp D x e a)
  | CStore l x e => follow_sharp J (next P l) (store_sharp D x e a)
  | CSeq l _ _ => follow_sharp J (next P l) a
  | CIf l e _ _ | CRepeat l _ e =>
      union_sharp D (follow_sharp J (nextTrue P l) (assume_sharp D e true a))
                    (follow_sharp J (nextFalse P l) (assume_sharp D e false a))
  | CGoto _ e => unions_sharp D (fun b => exists t, In t (labels (root P)) /\
      b = resume_sharp J (At t) (target_sharp D e t a))
  end.
Definition interpret_sharp : AbstractInterpreterEnv :=
  @iteration_limit interpreter_sharp_cpo interpreter_body_sharp.
Definition outputs_sharp a := interpret_sharp (root P) a.

(** * Lemmas *)

Lemma resume_sharp_mono J K : @le interpreter_sharp_cpo J K ->
  forall q a, le (resume_sharp J q a) (resume_sharp K q a).
Proof.
  intros H [|l] a; simpl; [apply le_refl|].
  destruct (lookup P l) as [[c k]|]; [apply H|apply le_refl].
Qed.
Lemma follow_sharp_mono J K : @le interpreter_sharp_cpo J K ->
  forall q a, le (follow_sharp J q a) (follow_sharp K q a).
Proof. intros H [p|] a; [apply resume_sharp_mono, H|apply le_refl]. Qed.
Lemma interpreter_body_sharp_mono :
  @monotone interpreter_sharp_cpo interpreter_sharp_cpo interpreter_body_sharp.
Proof.
  intros J K H c a. destruct c; cbn [interpreter_body_sharp];
    try (apply follow_sharp_mono, H).
  - apply union_sharp_mono; apply follow_sharp_mono, H.
  - apply union_sharp_mono; apply follow_sharp_mono, H.
  - apply unions_monotone. intros b [t [Ht ->]].
    eexists. split; [exists t; auto|apply resume_sharp_mono, H].
Qed.
Theorem interpret_sharp_fixed :
  @omega_continuous interpreter_sharp_cpo interpreter_body_sharp ->
  @equiv interpreter_sharp_cpo (interpreter_body_sharp interpret_sharp) interpret_sharp.
Proof. intros H. apply lfp_fixed; [apply interpreter_body_sharp_mono|exact H]. Qed.
Theorem interpret_sharp_least J :
  @prefixed interpreter_sharp_cpo interpreter_body_sharp J ->
  @le interpreter_sharp_cpo interpret_sharp J.
Proof. apply lfp_least, interpreter_body_sharp_mono. Qed.
End AbstractInterpreter.

Arguments resume_sharp {M} P D J q a.
Arguments follow_sharp {M} P D J q a.
Arguments interpreter_body_sharp {M} P D J c a.
Arguments interpret_sharp {M} P D c a.
Arguments outputs_sharp {M} P D a.
