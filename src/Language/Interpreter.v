From DAnalyzer.Language Require Export Semantics.
Import ListNotations.
Set Implicit Arguments.

(** * Definitions *)

(* A call runs from a command to the end of the fixed whole program. Its
   lexical continuation is already determined by P, including after goto. *)
Definition interpreter_cpo := map_cpo cmd (map_cpo (set Memory) (set_cpo Memory)).
Definition InterpreterEnv := carrier interpreter_cpo.

Section Interpreter.
Context (M : AddressMap) (P : Program).

Definition resume (J : InterpreterEnv) (q : point) (X : set Memory) : set Memory :=
  match q with
  | Halt => X
  | At l => match lookup P l with Some (c, _) => J c X | None => empty end
  end.
Definition follow (J : InterpreterEnv) (q : option point) X : set Memory :=
  match q with Some p => resume J p X | None => empty end.

(* Recursive calls receive only primitive transfers of X; no command call
   returns to its caller. In particular sequence enters its first child. *)
Definition interpreter_body (J : InterpreterEnv) : InterpreterEnv :=
  fun c X => match c with
  | CAssign l x e => follow J (next P l) (assign M x e X)
  | CStore l x e => follow J (next P l) (store M x e X)
  | CSeq l _ _ => follow J (next P l) X
  | CIf l e _ _ | CRepeat l _ e =>
      union (follow J (nextTrue P l) (assume M e true X))
            (follow J (nextFalse P l) (assume M e false X))
  | CGoto _ e => fun m' => exists t, In t (labels (root P)) /\
      resume J (At t) (target M e t X) m'
  end.

Definition interpret : InterpreterEnv := @lfp interpreter_cpo interpreter_body.
Definition outputs (X : set Memory) := interpret (root P) X.

(* Monotonicity in the input is distinct from monotonicity in the
   recursive environment. *)
Definition input_monotone (J : InterpreterEnv) :=
  forall c X Y, subset X Y -> subset (J c X) (J c Y).

(* The interpreter agrees with finite terminating paths of Exercise 1. *)
Definition returns (q : point) (X : set Memory) : set Memory :=
  fun m' => exists m, X m /\ path M P (q, m) (Halt, m').

(** * Lemmas *)

Lemma resume_mono J K : @le interpreter_cpo J K ->
  forall q X, subset (resume J q X) (resume K q X).
Proof.
  intros H [|l] X; simpl; [apply subset_refl|].
  destruct (lookup P l) as [[c k]|]; [apply H|apply subset_refl].
Qed.
Lemma follow_mono J K : @le interpreter_cpo J K ->
  forall q X, subset (follow J q X) (follow K q X).
Proof. intros H [p|] X; [apply resume_mono, H|apply subset_refl]. Qed.
Lemma interpreter_body_mono : @monotone interpreter_cpo interpreter_cpo interpreter_body.
Proof.
  intros J K H c X. destruct c; cbn [interpreter_body];
    try (apply follow_mono, H).
  - intros m [Hm|Hm]; [left|right]; eapply follow_mono; eauto.
  - intros m [Hm|Hm]; [left|right]; eapply follow_mono; eauto.
  - intros m [t [Ht Hm]]. exists t. split; [exact Ht|]. eapply resume_mono; eauto.
Qed.

Lemma env_sup (Js : nat -> InterpreterEnv) c X m :
  @omega_sup interpreter_cpo Js c X m <-> exists n, Js n c X m.
Proof.
  change ((exists Y, (exists J, (exists K, (exists n, K = Js n) /\ J = K c) /\ Y = J X) /\ Y m)
    <-> exists n, Js n c X m).
  split.
  - intros [Y [ [J [[K [[n ->] ->]] ->]] HY]]. eauto.
  - intros [n H]. exists (Js n c X). split; [|exact H].
    exists (Js n c). split; [|reflexivity]. exists (Js n). split; [exists n; reflexivity|reflexivity].
Qed.
Lemma resume_sup Js q X m :
  resume (@omega_sup interpreter_cpo Js) q X m <->
  exists n, resume (Js n) q X m.
Proof.
  destruct q as [|l]; simpl.
  - split; [intros H; exists O; exact H|intros [n H]; exact H].
  - destruct (lookup P l) as [[c k]|]; [apply env_sup|].
    unfold empty. firstorder.
Qed.
Lemma follow_sup Js q X m :
  follow (@omega_sup interpreter_cpo Js) q X m <->
  exists n, follow (Js n) q X m.
Proof. destruct q; [apply resume_sup|unfold follow, empty; firstorder]. Qed.
Lemma interpreter_body_continuous : @omega_continuous interpreter_cpo interpreter_body.
Proof.
  intros Js Hchain c X m H. apply env_sup. destruct c; cbn [interpreter_body] in *.
  - apply follow_sup in H. exact H.
  - apply follow_sup in H. exact H.
  - apply follow_sup in H. exact H.
  - destruct H as [H|H]; apply follow_sup in H; destruct H as [n H];
      exists n; [left|right]; exact H.
  - destruct H as [H|H]; apply follow_sup in H; destruct H as [n H];
      exists n; [left|right]; exact H.
  - destruct H as [t [Ht H]]. apply resume_sup in H. destruct H as [n H].
    exists n, t. auto.
Qed.
Theorem interpret_fixed :
  @equiv interpreter_cpo (interpreter_body interpret) interpret.
Proof. apply lfp_fixed; [apply interpreter_body_mono|apply interpreter_body_continuous]. Qed.

Lemma resume_input_mono J : input_monotone J ->
  forall q X Y, subset X Y -> subset (resume J q X) (resume J q Y).
Proof.
  intros H [|l] X Y HXY; simpl; [exact HXY|].
  destruct (lookup P l) as [[c k]|]; [apply H, HXY|apply subset_refl].
Qed.
Lemma follow_input_mono J : input_monotone J ->
  forall q X Y, subset X Y -> subset (follow J q X) (follow J q Y).
Proof. intros H [p|] X Y HXY; [apply resume_input_mono; assumption|apply subset_refl]. Qed.
Lemma iterate_input_mono n : input_monotone (@iterate interpreter_cpo interpreter_body n).
Proof.
  induction n as [|n IH].
  - intros c X Y H m Hm. exact Hm.
  - intros c X Y H. simpl. destruct c; cbn [interpreter_body].
    + apply follow_input_mono; [exact IH|apply assign_mono, H].
    + apply follow_input_mono; [exact IH|apply store_mono, H].
    + apply follow_input_mono; assumption.
    + intros m [Hm|Hm]; [left|right];
        eapply follow_input_mono; eauto using assume_mono.
    + intros m [Hm|Hm]; [left|right];
        eapply follow_input_mono; eauto using assume_mono.
    + intros m [t [Ht Hm]]. exists t. split; [exact Ht|].
      eapply resume_input_mono; [exact IH|apply target_mono, H|exact Hm].
Qed.
Lemma interpret_input_mono : input_monotone interpret.
Proof.
  intros c X Y H m Hm. apply env_sup in Hm. apply env_sup.
  destruct Hm as [n Hm]. exists n. eapply iterate_input_mono; eauto.
Qed.

Lemma resume_paths J :
  (forall c, In c (commands (root P)) -> forall X, subset (J c X) (returns (At (label c)) X)) ->
  forall q X, subset (resume J q X) (returns q X).
Proof.
  intros H [|l] X m' Hm; simpl in Hm.
  - exists m'. split; [exact Hm|constructor].
  - destruct (lookup P l) as [[c k]|] eqn:Hl; [|contradiction].
    destruct (@lookup_sound P l c k Hl) as [Hc Heq]. rewrite <- Heq. apply H; assumption.
Qed.
Lemma body_paths J :
  (forall q X, subset (resume J q X) (returns q X)) ->
  forall c, In c (commands (root P)) -> forall X,
    subset (interpreter_body J c X) (returns (At (label c)) X).
Proof.
  intros HJ c Hc X m' H.
  destruct (lookup_complete P c Hc) as [k Hlookup].
  assert (Hcmd : command_at P (label c) = Some c).
  { unfold command_at. rewrite Hlookup. reflexivity. }
  destruct c; cbn [interpreter_body] in H; simpl in Hcmd, Hlookup |- *.
  - assert (Hnext : next P l = Some k) by (unfold next; rewrite Hlookup; reflexivity).
    rewrite Hnext in H. apply HJ in H. destruct H as [n [[m [v [HX [He ->]]]] Hp]].
    exists m. split; [exact HX|]. econstructor; [eapply StepAssign; eauto|exact Hp].
  - assert (Hnext : next P l = Some k) by (unfold next; rewrite Hlookup; reflexivity).
    rewrite Hnext in H. apply HJ in H. destruct H as [n [[m [v [HX [He ->]]]] Hp]].
    exists m. split; [exact HX|]. econstructor; [eapply StepStore; eauto|exact Hp].
  - assert (Hnext : next P l = Some (At (label c1))) by (unfold next; rewrite Hlookup; reflexivity).
    rewrite Hnext in H. apply (HJ (At (label c1)) X) in H. destruct H as [m [HX Hp]].
    exists m. split; [exact HX|]. econstructor; [eapply StepSeq; eauto|exact Hp].
  - assert (Ht : nextTrue P l = Some (At (label c1))) by (unfold nextTrue; rewrite Hlookup; reflexivity).
    assert (Hf : nextFalse P l = Some (At (label c2))) by (unfold nextFalse; rewrite Hlookup; reflexivity).
    destruct H as [H|H].
    + rewrite Ht in H. apply (HJ (At (label c1)) _) in H.
      destruct H as [m [[HX [v [He Hb]]] Hp]]. exists m. split; [exact HX|].
      econstructor; [eapply StepIfTrue; eauto|exact Hp].
    + rewrite Hf in H. apply (HJ (At (label c2)) _) in H.
      destruct H as [m [[HX [v [He Hb]]] Hp]]. exists m. split; [exact HX|].
      econstructor; [eapply StepIfFalse; eauto|exact Hp].
  - assert (Ht : nextTrue P l = Some (At (label c))) by (unfold nextTrue; rewrite Hlookup; reflexivity).
    assert (Hf : nextFalse P l = Some k) by (unfold nextFalse; rewrite Hlookup; reflexivity).
    destruct H as [H|H].
    + rewrite Ht in H. apply (HJ (At (label c)) _) in H.
      destruct H as [m [[HX [v [He Hb]]] Hp]]. exists m. split; [exact HX|].
      econstructor; [eapply StepRepeatTrue; eauto|exact Hp].
    + rewrite Hf in H. apply (HJ k _) in H.
      destruct H as [m [[HX [v [He Hb]]] Hp]]. exists m. split; [exact HX|].
      econstructor; [eapply StepRepeatFalse; eauto|exact Hp].
  - destruct H as [t [Ht H]]. apply (HJ (At t) _) in H. destruct H as [m [[HX He] Hp]].
    exists m. split; [exact HX|]. econstructor; [eapply StepGoto; eauto|exact Hp].
Qed.
Lemma iterate_paths n : forall c, In c (commands (root P)) -> forall X,
  subset (@iterate interpreter_cpo interpreter_body n c X) (returns (At (label c)) X).
Proof.
  induction n as [|n IH]; intros c Hc X.
  - intros m H. exact (False_rect _ H).
  - apply body_paths; [apply resume_paths, IH|exact Hc].
Qed.
Theorem interpret_paths c : In c (commands (root P)) -> forall X,
  subset (interpret c X) (returns (At (label c)) X).
Proof.
  intros Hc X m H. apply env_sup in H. destruct H as [n H].
  eapply iterate_paths; eauto.
Qed.

Lemma resume_body l c X : command_at P l = Some c ->
  subset (interpreter_body interpret c X) (resume interpret (At l) X).
Proof.
  unfold command_at. destruct (lookup P l) as [[d k]|] eqn:Hl; simpl; [|discriminate].
  intros H. inversion H; subst d. rewrite Hl. apply (proj1 interpret_fixed).
Qed.
Lemma step_resume p m q n m' : step M P (p, m) (q, n) ->
  resume interpret q (fun u => u = n) m' ->
  resume interpret p (fun u => u = m) m'.
Proof.
  intros Hstep Hout. inversion Hstep; subst.
  all: eapply resume_body; [eassumption|]; cbn [interpreter_body].
  - rewrite H4. eapply resume_input_mono; [apply interpret_input_mono| |exact Hout].
    intros u ->. exists m, v. repeat split; auto.
  - rewrite H4. eapply resume_input_mono; [apply interpret_input_mono| |exact Hout].
    intros u ->. exists m, v. repeat split; auto.
  - rewrite H4. exact Hout.
  - left. rewrite H4. eapply resume_input_mono; [apply interpret_input_mono| |exact Hout].
    intros u ->. split; [reflexivity|]. exists v. auto.
  - right. rewrite H4. eapply resume_input_mono; [apply interpret_input_mono| |exact Hout].
    intros u ->. split; [reflexivity|]. exists v. auto.
  - left. rewrite H4. eapply resume_input_mono; [apply interpret_input_mono| |exact Hout].
    intros u ->. split; [reflexivity|]. exists v. auto.
  - right. rewrite H4. eapply resume_input_mono; [apply interpret_input_mono| |exact Hout].
    intros u ->. split; [reflexivity|]. exists v. auto.
  - exists t. split; [assumption|].
    eapply resume_input_mono; [apply interpret_input_mono| |exact Hout].
    intros u ->. split; [reflexivity|assumption].
Qed.
Lemma path_resume s t : path M P s t -> forall m',
  resume interpret (fst t) (fun u => u = snd t) m' ->
  resume interpret (fst s) (fun u => u = snd s) m'.
Proof.
  intros H. induction H; intros m' Hout; [exact Hout|].
  destruct s as [p m], t as [q n]. eapply step_resume; [exact H|apply IHpath, Hout].
Qed.
Theorem interpret_returns c : In c (commands (root P)) -> forall X,
  same_set (interpret c X) (returns (At (label c)) X).
Proof.
  intros Hc X. split; [apply interpret_paths, Hc|].
  intros m' [m [HX Hp]].
  assert (Hrun : resume interpret (At (label c)) (fun u => u = m) m').
  { apply (path_resume Hp). reflexivity. }
  destruct (lookup_complete P c Hc) as [k Hl]. cbn [resume] in Hrun. rewrite Hl in Hrun.
  eapply interpret_input_mono; [|exact Hrun]. intros u ->. exact HX.
Qed.
Theorem interpret_natural_extension c X : In c (commands (root P)) ->
  same_set (interpret c X) (fun m' => exists m, X m /\ interpret c (fun u => u = m) m').
Proof.
  intros Hc. split.
  - intros m' H. apply (proj1 (interpret_returns c Hc X)) in H.
    destruct H as [m [HX Hp]]. exists m. split; [exact HX|].
    apply (proj2 (interpret_returns c Hc _)). exists m. split; [reflexivity|exact Hp].
  - intros m' [m [HX H]]. eapply interpret_input_mono; [|exact H]. intros u ->. exact HX.
Qed.
Theorem outputs_reach X m : outputs X m <-> Reach M P X (Halt, m).
Proof.
  unfold outputs. rewrite (Reach_finite M P), (reachable_path M P).
  split.
  - intros H. apply (proj1 (interpret_returns (root P) (command_self _) X)) in H.
    destruct H as [n [HX Hp]]. exists (entry P, n). split; [split; auto|exact Hp].
  - intros [[q n] [[Hq HX] Hp]]. cbn in Hq. subst q.
    apply (proj2 (interpret_returns (root P) (command_self _) X)). exists n. auto.
Qed.

End Interpreter.

