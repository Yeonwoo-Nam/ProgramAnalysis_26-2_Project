From Stdlib Require Export List ZArith String.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope list_scope.

Definition Var := string.

Inductive expr :=
| EInt (n : Z) | EAdd (a b : expr) | EMul (a b : expr)
| ENeg (a : expr) | ELt (a b : expr)
| EVar (x : Var) | EDeref (x : Var) | EAddr (x : Var) | ERead.

Inductive cmd :=
| CAssign (l : nat) (x : Var) (e : expr)
| CStore (l : nat) (x : Var) (e : expr)
| CSeq (l : nat) (a b : cmd)
| CIf (l : nat) (e : expr) (a b : cmd)
| CRepeat (l : nat) (body : cmd) (e : expr)
| CGoto (l : nat) (e : expr).

Definition label (c : cmd) : nat :=
  match c with
  | CAssign l _ _ | CStore l _ _ | CSeq l _ _
  | CIf l _ _ _ | CRepeat l _ _ | CGoto l _ => l
  end.
Fixpoint commands (c : cmd) : list (cmd) :=
  c :: match c with
       | CSeq _ a b | CIf _ _ a b => commands a ++ commands b
       | CRepeat _ b _ => commands b
       | _ => [] end.
Definition labels (c : cmd) := map label (commands c).

(* A program is a syntax tree whose command labels are globally unique. *)
Record Program := {
  root : cmd;
  unique_labels : NoDup (labels root)
}.

Lemma command_self (c : cmd) : In c (commands c).
Proof. destruct c; simpl; auto. Qed.
Lemma commands_trans (small mid whole : cmd) :
  In small (commands mid) -> In mid (commands whole) -> In small (commands whole).
Proof.
  revert small mid. induction whole; intros small mid Ha Hb; simpl in Hb;
    destruct Hb as [<-|Hb]; try exact Ha; try contradiction.
  - simpl. right. apply in_app_iff in Hb. apply in_app_iff.
    destruct Hb; [left; eapply IHwhole1|right; eapply IHwhole2]; eauto.
  - simpl. right. apply in_app_iff in Hb. apply in_app_iff.
    destruct Hb; [left; eapply IHwhole1|right; eapply IHwhole2]; eauto.
  - simpl. right. eapply IHwhole; eauto.
Qed.
Fixpoint expr_vars (e : expr) : list Var :=
  match e with
  | EInt _ | ERead => []
  | EVar x | EDeref x | EAddr x => [x]
  | ENeg a => expr_vars a
  | EAdd a b | EMul a b | ELt a b => expr_vars a ++ expr_vars b
  end.
Fixpoint cmd_vars (c : cmd) : list Var :=
  match c with
  | CAssign _ x e | CStore _ x e => x :: expr_vars e
  | CSeq _ a b => cmd_vars a ++ cmd_vars b
  | CIf _ e a b => expr_vars e ++ cmd_vars a ++ cmd_vars b
  | CRepeat _ b e => cmd_vars b ++ expr_vars e
  | CGoto _ e => expr_vars e
  end.

Inductive point := Halt | At (l : nat).
Definition point_eq_dec : forall p q : point, {p = q} + {p <> q}.
Proof. decide equality; apply Nat.eq_dec. Defined.
