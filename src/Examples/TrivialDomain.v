From DAnalyzer.Abstract Require Export Domain.
Set Implicit Arguments.

(* A deliberately imprecise domain whose bottom denotes every memory. *)
Definition unit_cpo : CPO.
Proof.
  refine {| carrier := unit; le := fun _ _ => True; bottom := tt;
            chain_sup := fun _ => tt |}; auto.
Defined.

Definition trivial_domain (M : AddressMap) : AbstractDomain M.
Proof.
  refine {| memory_cpo := unit_cpo;
            alpha := fun _ => tt; gamma := fun _ _ => True;
            unions_sharp := fun _ => tt;
            assign_sharp := fun _ _ _ => tt;
            store_sharp := fun _ _ _ => tt;
            assume_sharp := fun _ _ _ => tt;
            target_sharp := fun _ _ _ => tt |}; cbn; firstorder.
Defined.

Lemma trivial_bottom_nonempty M (m : Memory) :
  gamma (trivial_domain M) bottom m.
Proof. exact I. Qed.
