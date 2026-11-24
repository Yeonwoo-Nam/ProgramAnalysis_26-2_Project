(* Predicate sets; all equalities used below are extensional equivalences. *)
Set Implicit Arguments.

Definition set (A : Type) := A -> Prop.
Definition subset {A} (X Y : set A) := forall x, X x -> Y x.
Definition same_set {A} (X Y : set A) := subset X Y /\ subset Y X.
Definition empty {A} : set A := fun _ => False.
Definition union {A} (X Y : set A) : set A := fun x => X x \/ Y x.
Definition unions {I A} (X : I -> set A) : set A :=
  fun x => exists i, X i x.
Definition image {A B} (R : A -> B -> Prop) (X : set A) : set B :=
  fun y => exists x, X x /\ R x y.

Lemma subset_refl {A} (X : set A) : subset X X.
Proof. firstorder. Qed.
Lemma subset_trans {A} (X Y Z : set A) :
  subset X Y -> subset Y Z -> subset X Z.
Proof. firstorder. Qed.
Lemma empty_subset {A} (X : set A) : subset empty X.
Proof. firstorder. Qed.
Lemma image_mono {A B} (R : A -> B -> Prop) X Y :
  subset X Y -> subset (image R X) (image R Y).
Proof. firstorder. Qed.
Lemma image_unions {I A B} (R : A -> B -> Prop) (X : I -> set A) :
  same_set (image R (unions X)) (unions (fun i => image R (X i))).
Proof. firstorder. Qed.
