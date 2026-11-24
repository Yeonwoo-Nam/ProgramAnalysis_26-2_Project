From DAnalyzer.Language Require Export Semantics.
From DAnalyzer.Foundations Require Export Order.
Set Implicit Arguments.

(* CPO structure and abstract union are separate. Union approximates concrete
   union; it need not be a least upper bound in the abstract order. *)
Record AbstractDomain (M : AddressMap) := {
  memory_cpo : CPO;
  alpha : set Memory -> carrier memory_cpo;
  gamma : carrier memory_cpo -> set Memory;
  galois : forall X a, le (alpha X) a <-> subset X (gamma a);
  unions_sharp : set (carrier memory_cpo) -> carrier memory_cpo;
  (* Monotonicity under pointwise improvement of contributions, including
     adding contributions. Inclusion of sets alone would not suffice. *)
  unions_monotone : forall X Y,
    (forall a, X a -> exists b, Y b /\ le a b) ->
    le (unions_sharp X) (unions_sharp Y);
  unions_sound : forall X a, X a -> subset (gamma a) (gamma (unions_sharp X));
  assign_sharp : Var -> expr -> carrier memory_cpo -> carrier memory_cpo;
  store_sharp : Var -> expr -> carrier memory_cpo -> carrier memory_cpo;
  assume_sharp : expr -> bool -> carrier memory_cpo -> carrier memory_cpo;
  target_sharp : expr -> nat -> carrier memory_cpo -> carrier memory_cpo;
  assign_monotone : forall x e, monotone (assign_sharp x e);
  store_monotone : forall x e, monotone (store_sharp x e);
  assume_monotone : forall e b, monotone (assume_sharp e b);
  target_monotone : forall e l, monotone (target_sharp e l);
  assign_sound : forall x e a, subset (assign M x e (gamma a)) (gamma (assign_sharp x e a));
  store_sound : forall x e a, subset (store M x e (gamma a)) (gamma (store_sharp x e a));
  assume_sound : forall e b a, subset (assume M e b (gamma a)) (gamma (assume_sharp e b a));
  target_sound : forall e l a, subset (target M e l (gamma a)) (gamma (target_sharp e l a))
}.
Arguments memory_cpo {M} _.
Arguments alpha {M} _ _.
Arguments gamma {M} _ _ _.
Arguments unions_sharp {M} _ _.

Section DomainLaws.
Context {M : AddressMap} (D : AbstractDomain M).
Local Notation L := (memory_cpo D).

(* Binary abstract union is the two-element case of the bundled operation. *)
Definition union_sharp (a b : carrier L) : carrier L :=
  unions_sharp D (fun c => c = a \/ c = b).

Lemma alpha_covers X : subset X (gamma D (alpha D X)).
Proof. apply (proj1 (galois D X (alpha D X))), le_refl. Qed.
Lemma gamma_mono (a b : carrier L) : le a b -> subset (gamma D a) (gamma D b).
Proof.
  intros H. apply (proj1 (galois D (gamma D a) b)).
  eapply le_trans; [apply (proj2 (galois D (gamma D a) a)), subset_refl|exact H].
Qed.
Lemma union_sharp_mono a b a' b' :
  le a a' -> le b b' -> le (union_sharp a b) (union_sharp a' b').
Proof.
  intros Ha Hb. apply unions_monotone. intros c [-> | ->].
  - exists a'. split; [left; reflexivity|exact Ha].
  - exists b'. split; [right; reflexivity|exact Hb].
Qed.
Lemma gamma_union_left a b : subset (gamma D a) (gamma D (union_sharp a b)).
Proof. apply unions_sound. left; reflexivity. Qed.
Lemma gamma_union_right a b : subset (gamma D b) (gamma D (union_sharp a b)).
Proof. apply unions_sound. right; reflexivity. Qed.

End DomainLaws.
