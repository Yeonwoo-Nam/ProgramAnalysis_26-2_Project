From DAnalyzer.Language Require Export Syntax.
Import ListNotations.
Set Implicit Arguments.

(* Numeric points make syntax lookup and successor metadata directly reducible.
   Only labels in [labels (root P)] can be computed-goto destinations. *)
Definition Entry (P : Program) := { l : nat | In l (labels (root P)) }.
Definition entry (P : Program) := At (label (root P)).
Definition points (P : Program) := Halt :: map At (labels (root P)).

(* Search the syntax tree while carrying the normal continuation. *)
Fixpoint lookup_cmd (c : cmd) (k : point) (l : nat) : option (cmd * point) :=
  if Nat.eqb (label c) l then Some (c, k)
  else match c with
  | CSeq _ a b =>
      match lookup_cmd a (At (label b)) l with
      | Some ck => Some ck
      | None => lookup_cmd b k l
      end
  | CIf _ _ a b =>
      match lookup_cmd a k l with
      | Some ck => Some ck
      | None => lookup_cmd b k l
      end
  | CRepeat t b _ => lookup_cmd b (At t) l
  | _ => None
  end.
Definition lookup (P : Program) l := lookup_cmd (root P) Halt l.

Lemma lookup_cmd_sound c k l n q :
  lookup_cmd c k l = Some (n, q) -> In n (commands c) /\ label n = l.
Proof.
  revert k. induction c; intros k H; cbn [lookup_cmd] in H;
    destruct (Nat.eqb (label _) l) eqn:Hl;
    try (inversion H; subst; split; [apply command_self|now apply Nat.eqb_eq in Hl]);
    try discriminate.
  - destruct (lookup_cmd c1 (At (label c2)) l) as [[n' q']|] eqn:Ha.
    + inversion H; subst. apply IHc1 in Ha. destruct Ha as [Hin Heq].
      split; [simpl; right; apply in_or_app; auto|exact Heq].
    + apply IHc2 in H. destruct H as [Hin Heq].
      split; [simpl; right; apply in_or_app; auto|exact Heq].
  - destruct (lookup_cmd c1 k l) as [[n' q']|] eqn:Ha.
    + inversion H; subst. apply IHc1 in Ha. destruct Ha as [Hin Heq].
      split; [simpl; right; apply in_or_app; auto|exact Heq].
    + apply IHc2 in H. destruct H as [Hin Heq].
      split; [simpl; right; apply in_or_app; auto|exact Heq].
  - apply IHc in H. destruct H as [Hin Heq]. split; [simpl; auto|exact Heq].
Qed.
Lemma lookup_sound (P : Program) l c k :
  lookup P l = Some (c, k) -> In c (commands (root P)) /\ label c = l.
Proof. apply lookup_cmd_sound. Qed.

(* Failure means no command in the searched subtree has the requested label. *)
Lemma lookup_cmd_none c k l :
  lookup_cmd c k l = None -> forall n, In n (commands c) -> label n <> l.
Proof.
  revert k. induction c; intros k H n Hin; cbn [lookup_cmd] in H;
    destruct (Nat.eqb (label _) l) eqn:Hl; try discriminate;
    simpl in Hin; destruct Hin as [<-|Hin];
    try (now apply Nat.eqb_neq in Hl); try contradiction.
  - destruct (lookup_cmd c1 (At (label c2)) l) as [ck|] eqn:Ha; [discriminate|].
    apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + eapply IHc1; eauto.
    + eapply IHc2; eauto.
  - destruct (lookup_cmd c1 k l) as [ck|] eqn:Ha; [discriminate|].
    apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + eapply IHc1; eauto.
    + eapply IHc2; eauto.
  - eapply IHc; eauto.
Qed.

Lemma nodup_key_unique {A B} (key : A -> B) xs : NoDup (map key xs) ->
  forall x y, In x xs -> In y xs -> key x = key y -> x = y.
Proof.
  induction xs as [|a xs IH]; simpl; intros Hdup x y Hx Hy Heq; [contradiction|].
  inversion Hdup as [|ka ks Hnot Htail]; subst.
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy]; auto.
  - exfalso. apply Hnot. rewrite Heq. apply in_map, Hy.
  - exfalso. apply Hnot. rewrite <- Heq. apply in_map, Hx.
Qed.

Theorem lookup_complete (P : Program) c :
  In c (commands (root P)) -> exists k, lookup P (label c) = Some (c, k).
Proof.
  intros Hin. destruct (lookup P (label c)) as [[c' k]|] eqn:H.
  - pose proof H as Hsound. apply lookup_sound in Hsound. destruct Hsound as [Hin' Heq].
    assert (c' = c).
    { eapply (nodup_key_unique label); [exact (unique_labels P)|exact Hin'|exact Hin|exact Heq]. }
    subst c'. exists k. reflexivity.
  - exfalso. eapply lookup_cmd_none; [exact H|exact Hin|reflexivity].
Qed.

(* Every inherited continuation stays within the original program scope. *)
Lemma lookup_cmd_scope c k l n q (Good : point -> Prop) :
  (forall d, In d (commands c) -> Good (At (label d))) -> Good k ->
  lookup_cmd c k l = Some (n, q) -> Good q.
Proof.
  revert k. induction c; intros k Hnodes Hk H; cbn [lookup_cmd] in H;
    destruct (Nat.eqb (label _) l) eqn:Hl;
    try (inversion H; subst; exact Hk); try discriminate.
  - destruct (lookup_cmd c1 (At (label c2)) l) as [[n' q']|] eqn:Ha.
    + inversion H; subst. eapply IHc1; [| |exact Ha].
      * intros d Hd. apply Hnodes. simpl. right. apply in_or_app; auto.
      * apply Hnodes. simpl. right. apply in_or_app. right. apply command_self.
    + eapply IHc2; [|exact Hk|exact H].
      intros d Hd. apply Hnodes. simpl. right. apply in_or_app; auto.
  - destruct (lookup_cmd c1 k l) as [[n' q']|] eqn:Ha.
    + inversion H; subst. eapply IHc1; [|exact Hk|exact Ha].
      intros d Hd. apply Hnodes. simpl. right. apply in_or_app; auto.
    + eapply IHc2; [|exact Hk|exact H].
      intros d Hd. apply Hnodes. simpl. right. apply in_or_app; auto.
  - eapply IHc; [| |exact H].
    + intros d Hd. apply Hnodes. simpl; auto.
    + apply (Hnodes (CRepeat l0 c e)). simpl; auto.
Qed.

Lemma command_point_valid (P : Program) c :
  In c (commands (root P)) -> In (At (label c)) (points P).
Proof. intros H. right. apply in_map. unfold labels. apply in_map, H. Qed.
Lemma continuation_valid (P : Program) l c k :
  lookup P l = Some (c, k) -> In k (points P).
Proof.
  intros H. eapply (@lookup_cmd_scope (root P) Halt l c k (fun q => In q (points P)));
    [|simpl; auto|exact H].
  intros n Hn. apply command_point_valid, Hn.
Qed.

(* Partial successor metadata. A goto has no syntax-determined successor. *)
Definition command_at (P : Program) l := option_map fst (lookup P l).
Definition cont (P : Program) l := option_map snd (lookup P l).
Definition next (P : Program) l : option point :=
  match lookup P l with
  | Some (CAssign _ _ _, k) | Some (CStore _ _ _, k) => Some k
  | Some (CSeq _ a _, _) => Some (At (label a))
  | _ => None
  end.
Definition nextTrue (P : Program) l : option point :=
  match lookup P l with
  | Some (CIf _ _ a _, _) | Some (CRepeat _ a _, _) => Some (At (label a))
  | _ => None
  end.
Definition nextFalse (P : Program) l : option point :=
  match lookup P l with
  | Some (CIf _ _ _ b, _) => Some (At (label b))
  | Some (CRepeat _ _ _, k) => Some k
  | _ => None
  end.

Lemma command_at_sound (P : Program) l c :
  command_at P l = Some c ->
  In c (commands (root P)) /\ label c = l.
Proof.
  unfold command_at. destruct (lookup P l) as [[c' k]|] eqn:H; simpl; try discriminate.
  intros Heq. inversion Heq; subst c'. apply lookup_sound in H.
  destruct H as [Hin Hl]. split; assumption.
Qed.
Lemma command_at_valid (P : Program) l c :
  command_at P l = Some c -> In (At l) (points P).
Proof.
  intros H. apply command_at_sound in H. destruct H as [Hin <-].
  apply command_point_valid, Hin.
Qed.

Lemma next_valid (P : Program) l q : next P l = Some q -> In q (points P).
Proof.
  unfold next. destruct (lookup P l) as [[c k]|] eqn:H; [|discriminate].
  pose proof H as Hsound. apply lookup_sound in Hsound. destruct Hsound as [Hin _].
  destruct c; try discriminate; intros Hq; inversion Hq; subst q.
  - eapply continuation_valid; eauto.
  - eapply continuation_valid; eauto.
  - apply command_point_valid. eapply commands_trans; [|exact Hin].
    simpl. right. apply in_or_app. left. apply command_self.
Qed.
Lemma nextTrue_valid (P : Program) l q : nextTrue P l = Some q -> In q (points P).
Proof.
  unfold nextTrue. destruct (lookup P l) as [[c k]|] eqn:H; [|discriminate].
  pose proof H as Hsound. apply lookup_sound in Hsound. destruct Hsound as [Hin _].
  destruct c; try discriminate; intros Hq; inversion Hq; subst q;
    apply command_point_valid.
  - eapply commands_trans; [|exact Hin].
    simpl. right. apply in_or_app. left. apply command_self.
  - eapply commands_trans; [|exact Hin].
    simpl. right. apply command_self.
Qed.
Lemma nextFalse_valid (P : Program) l q : nextFalse P l = Some q -> In q (points P).
Proof.
  unfold nextFalse. destruct (lookup P l) as [[c k]|] eqn:H; [|discriminate].
  pose proof H as Hsound. apply lookup_sound in Hsound. destruct Hsound as [Hin _].
  destruct c; try discriminate; intros Hq; inversion Hq; subst q.
  - apply command_point_valid. eapply commands_trans; [|exact Hin].
    simpl. right. apply in_or_app. right. apply command_self.
  - eapply continuation_valid; eauto.
Qed.
