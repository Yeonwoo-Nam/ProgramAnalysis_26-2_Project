From Stdlib Require Import Arith.
From DAnalyzer.Foundations Require Export Order.
Set Implicit Arguments.

Definition prefixed {L : CPO} (f : carrier L -> carrier L) a :=
  le (f a) a.
Fixpoint iterate {L : CPO} (f : carrier L -> carrier L) n :=
  match n with O => bottom | S n => f (iterate f n) end.
Definition omega_sup {L : CPO} (c : nat -> carrier L) :=
  chain_sup (fun a => exists n, a = c n).
Definition chain {L : CPO} (c : nat -> carrier L) :=
  forall n, le (c n) (c (S n)).
Definition omega_continuous {L : CPO} (f : carrier L -> carrier L) :=
  forall c, chain c -> le (f (omega_sup c)) (omega_sup (fun n => f (c n))).

(* Monotonicity makes this an increasing-chain limit. Continuity is needed
   only when identifying it as a fixed point. *)
Definition iteration_limit {L : CPO} (f : carrier L -> carrier L) :=
  omega_sup (iterate f).

(* The lecture's Kleene construction, used as a least fixed point when f is
   monotone and omega-continuous. Abstract semantics uses [iteration_limit]
   directly, since abstract transfers need only be monotone. *)
Definition lfp {L : CPO} (f : carrier L -> carrier L) := iteration_limit f.

Lemma chain_increasing {L : CPO} (c : nat -> carrier L) :
  chain c -> forall n m, n <= m -> le (c n) (c m).
Proof.
  intros Hc n m Hnm. induction Hnm; [apply le_refl|].
  eapply le_trans; [exact IHHnm|apply Hc].
Qed.
Lemma chain_range {L : CPO} (c : nat -> carrier L) :
  chain c -> is_chain le (fun a => exists n, a = c n).
Proof.
  intros Hc a b [n ->] [m ->]. destruct (Nat.le_ge_cases n m);
    [left|right]; eapply chain_increasing; eauto.
Qed.
Lemma chain_map {L K : CPO} (f : carrier L -> carrier K) c :
  monotone f -> chain c -> chain (fun n => f (c n)).
Proof. intros Hf Hc n. apply Hf, Hc. Qed.
Lemma iterate_chain {L} (f : carrier L -> carrier L) :
  monotone f -> chain (iterate f).
Proof.
  intros Hf n. induction n; simpl; [apply bottom_le|apply Hf; assumption].
Qed.
Lemma iterate_below_prefixed {L} (f : carrier L -> carrier L) a :
  monotone f -> prefixed f a -> forall n, le (iterate f n) a.
Proof.
  intros Hf Ha n. induction n; simpl; [apply bottom_le|].
  eapply le_trans; [apply Hf, IHn|exact Ha].
Qed.
Lemma iteration_limit_upper {L} (f : carrier L -> carrier L) :
  monotone f -> forall n, le (iterate f n) (iteration_limit f).
Proof.
  intros Hf n. apply chain_sup_upper; [apply chain_range, iterate_chain, Hf|].
  exists n; reflexivity.
Qed.
Lemma iteration_limit_least {L} (f : carrier L -> carrier L) a :
  monotone f -> (forall n, le (iterate f n) a) -> le (iteration_limit f) a.
Proof.
  intros Hf Ha. apply chain_sup_least; [apply chain_range, iterate_chain, Hf|].
  intros b [n ->]. apply Ha.
Qed.

Lemma lfp_least {L} (f : carrier L -> carrier L) a :
  monotone f -> prefixed f a -> le (lfp f) a.
Proof.
  intros Hf Ha. apply iteration_limit_least; [exact Hf|].
  apply iterate_below_prefixed; assumption.
Qed.
Lemma lfp_prefixed {L} (f : carrier L -> carrier L) :
  monotone f -> omega_continuous f -> prefixed f (lfp f).
Proof.
  intros Hf Hcont. unfold prefixed, lfp, iteration_limit.
  eapply le_trans; [apply Hcont, iterate_chain, Hf|].
  apply chain_sup_least.
  - apply chain_range, chain_map; [exact Hf|apply iterate_chain, Hf].
  - intros a [n ->]. apply chain_sup_upper; [apply chain_range, iterate_chain, Hf|].
    exists (S n); reflexivity.
Qed.
Theorem lfp_fixed {L} (f : carrier L -> carrier L) :
  monotone f -> omega_continuous f -> equiv (f (lfp f)) (lfp f).
Proof.
  intros Hf Hcont. split; [apply lfp_prefixed; assumption|].
  apply lfp_least; [exact Hf|]. apply Hf, lfp_prefixed; assumption.
Qed.
Theorem kleene_lfp {L} (f : carrier L -> carrier L) :
  monotone f -> omega_continuous f ->
  equiv (f (iteration_limit f)) (iteration_limit f) /\
  forall a, prefixed f a -> le (iteration_limit f) a.
Proof.
  intros Hf Hcont. split; [apply lfp_fixed; assumption|].
  intros a Ha. apply lfp_least; assumption.
Qed.

(* Compare finite iterates first; taking their chain limits requires no
   continuity of the abstract functional or of concretization. *)
Lemma iterate_sound {C A : CPO}
    (f : carrier C -> carrier C) (g : carrier A -> carrier A)
    (gamma : carrier A -> carrier C) :
  monotone f -> (forall a, le (f (gamma a)) (gamma (g a))) ->
  forall n, le (iterate f n) (gamma (iterate g n)).
Proof.
  intros Hf Hsound n. induction n; simpl; [apply bottom_le|].
  eapply le_trans; [apply Hf, IHn|apply Hsound].
Qed.
Theorem iteration_limit_sound {C A : CPO}
    (f : carrier C -> carrier C) (g : carrier A -> carrier A)
    (gamma : carrier A -> carrier C) :
  monotone f -> monotone g -> monotone gamma ->
  (forall a, le (f (gamma a)) (gamma (g a))) ->
  le (iteration_limit f) (gamma (iteration_limit g)).
Proof.
  intros Hf Hg Hgamma Hsound. apply iteration_limit_least; [exact Hf|].
  intros n. eapply le_trans; [exact (@iterate_sound C A f g gamma Hf Hsound n)|].
  apply Hgamma, iteration_limit_upper, Hg.
Qed.
