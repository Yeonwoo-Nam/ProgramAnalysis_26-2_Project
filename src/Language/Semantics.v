From DAnalyzer.Language Require Export ControlFlow.
Require Export DAnalyzer.Foundations.Fixpoint.
Import ListNotations.
Set Implicit Arguments.
Open Scope Z_scope.

(** * Definitions *)
Section Definitions.

Section MemoryDefinitions.
Record AddressMap := {
  addr : Var -> Z;
  addr_injective : forall x y, addr x = addr y -> x = y
}.

(* All integer addresses are valid; variable names designate particular cells. *)
Definition Memory := Z -> Z.
Definition update (m : Memory) (a v : Z) : Memory :=
  fun b => if Z.eq_dec b a then v else m b.
End MemoryDefinitions.

Section Evaluation.
Context (M : AddressMap).
Inductive eval (m : Memory) : expr -> Z -> Prop :=
| EvalInt n : eval m (EInt n) n
| EvalAdd a b u v : eval m a u -> eval m b v -> eval m (EAdd a b) (u + v)
| EvalMul a b u v : eval m a u -> eval m b v -> eval m (EMul a b) (u * v)
| EvalNeg a u : eval m a u -> eval m (ENeg a) (-u)
| EvalLt a b u v : eval m a u -> eval m b v ->
    eval m (ELt a b) (if Z.ltb u v then 1 else 0)
| EvalVar x : eval m (EVar x) (m (addr M x))
| EvalDeref x : eval m (EDeref x) (m (m (addr M x)))
| EvalAddr x : eval m (EAddr x) (addr M x)
| EvalRead v : eval m ERead v.

Definition eval_set (e : expr) (X : set Memory) : set Z :=
  fun v => exists m, X m /\ eval m e v.
Definition truth (b : bool) (v : Z) : Prop :=
  if b then v <> 0 else v = 0.
End Evaluation.

Section Transfers.
Context (M : AddressMap).
Definition assign x e (X : set Memory) : set Memory :=
  fun m' => exists m v, X m /\ eval M m e v /\ m' = update m (addr M x) v.
Definition store x e (X : set Memory) : set Memory :=
  fun m' => exists m v,
    X m /\ eval M m e v /\ m' = update m (m (addr M x)) v.
Definition assume e b (X : set Memory) : set Memory :=
  fun m => X m /\ exists v, eval M m e v /\ truth b v.
Definition target e l (X : set Memory) : set Memory :=
  fun m => X m /\ eval M m e (Z.of_nat l).
End Transfers.

Section Transitions.
Context (M : AddressMap) (P : Program).
Definition state := (point * Memory)%type.

(* The node at the source label determines the rule. A repeat node is its
   post-body test; normal entry and true back-edges enter the body. Successors
   come from syntax metadata; goto evaluates its expression directly. *)
Inductive step : state -> state -> Prop :=
| StepAssign l x e q m v :
    command_at P l = Some (CAssign l x e) -> next P l = Some q ->
    eval M m e v -> step (At l, m) (q, update m (addr M x) v)
| StepStore l x e q m v :
    command_at P l = Some (CStore l x e) -> next P l = Some q ->
    eval M m e v -> step (At l, m) (q, update m (m (addr M x)) v)
| StepSeq l a b q m :
    command_at P l = Some (CSeq l a b) -> next P l = Some q ->
    step (At l, m) (q, m)
| StepIfTrue l e a b q m v :
    command_at P l = Some (CIf l e a b) -> nextTrue P l = Some q ->
    eval M m e v -> truth true v -> step (At l, m) (q, m)
| StepIfFalse l e a b q m v :
    command_at P l = Some (CIf l e a b) -> nextFalse P l = Some q ->
    eval M m e v -> truth false v -> step (At l, m) (q, m)
| StepRepeatTrue l b e q m v :
    command_at P l = Some (CRepeat l b e) -> nextTrue P l = Some q ->
    eval M m e v -> truth true v -> step (At l, m) (q, m)
| StepRepeatFalse l b e q m v :
    command_at P l = Some (CRepeat l b e) -> nextFalse P l = Some q ->
    eval M m e v -> truth false v -> step (At l, m) (q, m)
| StepGoto l e m t :
    command_at P l = Some (CGoto l e) ->
    eval M m e (Z.of_nat t) -> In t (labels (root P)) ->
    step (At l, m) (At t, m).

Definition initial (M0 : set Memory) : set state :=
  fun s => fst s = entry P /\ M0 (snd s).
Definition Step (X : set state) : set state := image step X.
Definition F (M0 : set Memory) (X : set state) := union (initial M0) (Step X).

Definition Reach (M0 : set Memory) : set state :=
  @lfp (set_cpo state) (F M0).

Inductive path : state -> state -> Prop :=
| PathRefl s : path s s
| PathCons s t u : step s t -> path t u -> path s u.
Inductive reachable (M0 : set Memory) : state -> Prop :=
| ReachInitial s : initial M0 s -> reachable M0 s
| ReachStep s t : reachable M0 s -> step s t -> reachable M0 t.
End Transitions.

End Definitions.

(** * Lemmas *)
Section Lemmas.

Section MemoryLemmas.
Lemma update_same (m : Memory) a v : update m a v a = v.
Proof. unfold update. destruct (Z.eq_dec a a); congruence. Qed.
Lemma update_other (m : Memory) a b v : b <> a -> update m a v b = m b.
Proof. intros H. unfold update. destruct (Z.eq_dec b a); congruence. Qed.
Lemma update_distinct_variables (A : AddressMap) m x y v :
  x <> y -> update m (addr A x) v (addr A y) = m (addr A y).
Proof.
  intros H. apply update_other. intros Heq. apply H, eq_sym, (addr_injective A), Heq.
Qed.
End MemoryLemmas.

Section EvaluationLemmas.
Context (M : AddressMap).
Lemma eval_deref_iff m x v : eval M m (EDeref x) v <-> v = m (m (addr M x)).
Proof. split; [intros H; inversion H; reflexivity|intros ->; constructor]. Qed.
Lemma eval_int_iff m n v : eval M m (EInt n) v <-> v = n.
Proof. split; [intros H; inversion H; reflexivity| intros ->; constructor]. Qed.
Lemma read_independent m u v :
  eval M m ERead u /\ eval M m ERead v /\ eval M m (EAdd ERead ERead) (u + v).
Proof. repeat split; constructor; constructor. Qed.
End EvaluationLemmas.

Section TransferLemmas.
Context (M : AddressMap).
(* Exact transfers are monotone and preserve arbitrary unions. *)
Lemma assign_mono x e X Y :
  subset X Y -> subset (assign M x e X) (assign M x e Y).
Proof. unfold assign, subset. firstorder. Qed.
Lemma assign_unions {I} x e (X : I -> set Memory) :
  same_set (assign M x e (unions X)) (unions (fun i => assign M x e (X i))).
Proof. unfold assign, unions, same_set, subset. firstorder. Qed.
Lemma assign_empty x e : same_set (assign M x e empty) empty.
Proof. unfold assign, empty, same_set, subset. firstorder. Qed.
Lemma store_mono x e X Y :
  subset X Y -> subset (store M x e X) (store M x e Y).
Proof. unfold store, subset. firstorder. Qed.
Lemma store_unions {I} x e (X : I -> set Memory) :
  same_set (store M x e (unions X)) (unions (fun i => store M x e (X i))).
Proof. unfold store, unions, same_set, subset. firstorder. Qed.
Lemma store_empty x e : same_set (store M x e empty) empty.
Proof. unfold store, empty, same_set, subset. firstorder. Qed.
Lemma assume_mono e b X Y :
  subset X Y -> subset (assume M e b X) (assume M e b Y).
Proof. unfold assume, subset. firstorder. Qed.
Lemma assume_unions {I} e b (X : I -> set Memory) :
  same_set (assume M e b (unions X)) (unions (fun i => assume M e b (X i))).
Proof. unfold assume, unions, same_set, subset. firstorder. Qed.
Lemma assume_empty e b : same_set (assume M e b empty) empty.
Proof. unfold assume, empty, same_set, subset. firstorder. Qed.
Lemma target_mono e l X Y :
  subset X Y -> subset (target M e l X) (target M e l Y).
Proof. unfold target, subset. firstorder. Qed.
Lemma target_unions {I} e l (X : I -> set Memory) :
  same_set (target M e l (unions X)) (unions (fun i => target M e l (X i))).
Proof. unfold target, unions, same_set, subset. firstorder. Qed.
Lemma target_empty e l : same_set (target M e l empty) empty.
Proof. unfold target, empty, same_set, subset. firstorder. Qed.
End TransferLemmas.

Section TransitionLemmas.
Context (M : AddressMap) (P : Program).
Lemma halt_stuck m s : ~ step M P (Halt, m) s.
Proof. intros H. inversion H. Qed.

Theorem step_points p m q m' : step M P (p, m) (q, m') ->
  In p (points P) /\ In q (points P).
Proof.
  intros H. inversion H; subst; split;
    eauto using command_at_valid, next_valid, nextTrue_valid, nextFalse_valid.
  right. apply in_map. assumption.
Qed.

Lemma Step_mono : @monotone (set_cpo state) (set_cpo state) (Step M P).
Proof. intros X Y H. apply image_mono. exact H. Qed.
Lemma F_mono M0 : @monotone (set_cpo state) (set_cpo state) (F M P M0).
Proof. intros X Y H s [Hi|Hs]; [left; exact Hi|right; eapply Step_mono; eauto]. Qed.

Lemma Step_unions {I} (X : I -> set state) :
  same_set (Step M P (unions X)) (unions (fun i => Step M P (X i))).
Proof. apply image_unions. Qed.
Lemma F_continuous M0 : @omega_continuous (set_cpo state) (F M P M0).
Proof.
  intros c Hc s [Hi|[s0 [[X [[n ->] HX]] Hstep]]].
  - exists (F M P M0 (c O)). split; [exists O; reflexivity|]. left; exact Hi.
  - exists (F M P M0 (c n)). split; [exists n; reflexivity|].
    right. exists s0. auto.
Qed.
Theorem Reach_kleene M0 :
  @equiv (set_cpo state) (Reach M P M0)
    (omega_sup (@iterate (set_cpo state) (F M P M0))).
Proof. split; apply le_refl. Qed.

Lemma Reach_closed M0 s t : Reach M P M0 s -> step M P s t -> Reach M P M0 t.
Proof.
  intros Hs Ht. apply (@lfp_prefixed (set_cpo state) (F M P M0)
    (@F_mono M0) (@F_continuous M0)).
  right. exists s. auto.
Qed.
Theorem Reach_finite M0 s : Reach M P M0 s <-> reachable M P M0 s.
Proof.
  split.
  - apply (@lfp_least (set_cpo state) (F M P M0) (reachable M P M0));
      [apply F_mono|].
    intros t [Hi|[u [Hu Hstep]]]; [constructor; exact Hi|econstructor 2; eauto].
  - intros H. induction H.
    + apply (@lfp_prefixed (set_cpo state) (F M P M0)
        (@F_mono M0) (@F_continuous M0)). left; exact H.
    + eapply Reach_closed; eauto.
Qed.
Corollary Reach_points M0 p m : Reach M P M0 (p, m) -> In p (points P).
Proof.
  assert (Hpoints : forall s, reachable M P M0 s -> In (fst s) (points P)).
  { intros s H. induction H.
    - destruct H as [He _]. rewrite He. apply command_entry_valid, command_self.
    - destruct s as [q n], t as [r o]. exact (proj2 (step_points H0)). }
  intros H. apply (Hpoints (p, m)), Reach_finite, H.
Qed.
Lemma path_append s t u : path M P s t -> path M P t u -> path M P s u.
Proof. intros H. induction H; intros Hu; [exact Hu|econstructor; eauto]. Qed.
Theorem reachable_path M0 t : reachable M P M0 t <->
  exists s, initial P M0 s /\ path M P s t.
Proof.
  split.
  - intros H. induction H.
    + exists s. split; [assumption|constructor].
    + destruct IHreachable as [u [Hi Hp]]. exists u. split; [exact Hi|].
      eapply path_append; [exact Hp|]. econstructor; [eassumption|constructor].
  - intros [s [Hi Hp]]. assert (Hs : reachable M P M0 s) by (constructor; exact Hi).
    clear Hi. induction Hp; [exact Hs|]. apply IHHp. econstructor 2; eauto.
Qed.
End TransitionLemmas.

End Lemmas.
