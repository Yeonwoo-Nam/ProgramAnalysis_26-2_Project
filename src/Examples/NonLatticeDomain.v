From DAnalyzer.Abstract Require Import TransitionSound.
Set Implicit Arguments.

(* Three elements up to set equivalence: empty, {true}, and {false}.
   The two nonempty elements have no common upper bound. *)
Definition Fork := {X : set bool | ~ (X true /\ X false)}.
Definition fork_le (a b : Fork) := subset (proj1_sig a) (proj1_sig b).
Definition fork_bottom : Fork.
Proof. exists empty. firstorder. Defined.

(* Outside chains the value is empty; only chain limits are specified. *)
Definition fork_limit (X : set Fork) : Fork.
Proof.
  exists (fun b => is_chain fork_le X /\ exists a, X a /\ proj1_sig a b).
  intros [[HX [a [Ha Hat]]] [_ [b [Hb Hbf]]]].
  destruct (HX a b Ha Hb) as [Hab|Hba].
  - apply (proj2_sig b). split; [apply Hab, Hat|exact Hbf].
  - apply (proj2_sig a). split; [exact Hat|apply Hba, Hbf].
Defined.

Definition fork_cpo : CPO.
Proof.
  refine {| carrier := Fork; le := fork_le; bottom := fork_bottom;
            chain_sup := fork_limit |}.
  - intros a; apply subset_refl.
  - intros a b c; apply subset_trans.
  - intros a b H; contradiction.
  - intros X HX a Ha b Hab. split; [exact HX|]. exists a; auto.
  - intros X HX a H b [_ [c [Hc Hcb]]]. apply (H c Hc), Hcb.
Defined.

Definition fork_true : Fork.
Proof. exists (fun b => b = true). intros [_ H]; discriminate. Defined.
Definition fork_false : Fork.
Proof. exists (fun b => b = false). intros [H _]; discriminate. Defined.

Lemma fork_no_common_upper :
  ~ exists a, @le fork_cpo fork_true a /\ @le fork_cpo fork_false a.
Proof.
  intros [[X HX] [Ht Hf]]. apply HX. split.
  - apply Ht. reflexivity.
  - apply Hf. reflexivity.
Qed.

(* The Galois connection deliberately represents every memory at every
   abstract element. Returning bottom is therefore a sound abstract union,
   although it is not an order upper bound of its contributions. *)
Definition fork_domain (M : AddressMap) : AbstractDomain M.
Proof.
  refine {| memory_cpo := fork_cpo;
            alpha := fun _ => fork_bottom; gamma := fun _ _ => True;
            unions_sharp := fun _ => fork_bottom;
            assign_sharp := fun _ _ _ => fork_bottom;
            store_sharp := fun _ _ _ => fork_bottom;
            assume_sharp := fun _ _ _ => fork_bottom;
            target_sharp := fun _ _ _ => fork_bottom |}; cbn; firstorder.
Defined.

Example fork_union_is_not_an_upper_bound M :
  ~ @le fork_cpo fork_true (union_sharp (fork_domain M) fork_true fork_false).
Proof. intros H. exact (H true eq_refl). Qed.

Example nonlattice_soundness M P M0 :
  subset (Reach M P M0)
    (gamma_state (fork_domain M) (Reach_sharp P (fork_domain M) fork_bottom)).
Proof. apply reachability_sound. intros m Hm. exact I. Qed.
