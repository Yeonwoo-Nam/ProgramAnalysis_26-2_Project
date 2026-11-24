From DAnalyzer.Foundations Require Export Sets.
Set Implicit Arguments.

Definition is_chain {A} (R : A -> A -> Prop) (X : set A) :=
  forall a b, X a -> X b -> R a b \/ R b a.

(* A pointed chain-complete order, up to mutual ordering. [chain_sup] is
   specified only on chains; it is not an arbitrary-union operation. *)
Record CPO := {
  carrier : Type;
  le : carrier -> carrier -> Prop;
  le_refl : forall a, le a a;
  le_trans : forall a b c, le a b -> le b c -> le a c;
  bottom : carrier;
  bottom_le : forall a, le bottom a;
  chain_sup : set carrier -> carrier;
  chain_sup_upper : forall X, is_chain le X -> forall a, X a -> le a (chain_sup X);
  chain_sup_least : forall X, is_chain le X -> forall a,
    (forall b, X b -> le b a) -> le (chain_sup X) a
}.
Arguments le {_} _ _.
Arguments bottom {_}.
Arguments chain_sup {_} _.

Definition equiv {L : CPO} (a b : carrier L) :=
  le a b /\ le b a.
Definition monotone {L K : CPO} (f : carrier L -> carrier K) :=
  forall a b, le a b -> le (f a) (f b).

(* Concrete unions are ordinary set unions, with no additional merge data. *)
Definition set_cpo (A : Type) : CPO.
Proof.
  refine {| carrier := set A; le := subset; bottom := empty;
            chain_sup := fun X a => exists Y, X Y /\ Y a |}; firstorder.
Defined.

Definition map_cpo (I : Type) (L : CPO) : CPO.
Proof.
  refine {| carrier := I -> carrier L;
            le := fun f g => forall i, le (f i) (g i);
            bottom := fun _ => bottom;
            chain_sup := fun X i => chain_sup (fun a => exists f, X f /\ a = f i) |}.
  - intros; apply le_refl.
  - intros a b c H H' i. eapply le_trans; eauto.
  - intros; apply bottom_le.
  - intros X HX f Hf i. apply chain_sup_upper.
    + intros a b [g [Hg ->]] [h [Hh ->]].
      destruct (HX g h Hg Hh) as [H|H]; [left|right]; apply H.
    + exists f; auto.
  - intros X HX f H i. apply chain_sup_least.
    + intros a b [g [Hg ->]] [h [Hh ->]].
      destruct (HX g h Hg Hh) as [Hgh|Hhg]; [left|right]; auto.
    + intros a [g [Hg ->]]. apply H, Hg.
Defined.
