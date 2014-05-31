Require Import List.
Require Import Bool.
Require Import ZArith.

Local Open Scope list_scope.
Local Open Scope Z_scope.

(*definicija urejenega seznama*)
Fixpoint urejen (l : list Z) :=
  match l with
    | nil => True
    | _ :: nil => True
    | x :: ((y :: _) as l') => x <= y /\ urejen l'
  end.

(*vstavi elt v ze urejen seznam*)
Fixpoint vstavi (x : Z) (l : list Z) : list Z :=
  match l with
    | nil => x :: nil
    | h :: l' => 
      if (x <=? h)
        then x :: l
        else h :: vstavi x l'
    end.

(*urejanje z vstavljanjem*)
Fixpoint insertion (l : list Z) :=
  match l with
    | nil => nil
    | x :: l' => vstavi x (insertion l')
  end.

(*presteje, kolikokrat se elt pojavi v seznamu*)
Fixpoint pojavi (x : Z) (l : list Z) : nat :=
  match l with
    | nil => 0%nat
    | (y :: l') =>
      if x =? y then S (pojavi x l') else pojavi x l'
  end.

(*permutirana (enaka) seznama*)
Definition permutiran (l1 l2 : list Z) :=
  forall x : Z, pojavi x l1 = pojavi x l2.

(*pomozne leme*)
Lemma permutiran_refl (l : list Z): permutiran l l.
Proof.
  intro; reflexivity.
Qed.

Lemma permutiran_sym (l1 l2 : list Z): 
        permutiran l1 l2 -> permutiran l2 l1.
Proof.
  intros E x.
  symmetry.
  apply E.
Qed.

Lemma permutiran_tran (l1 l2 l3 : list Z): 
   permutiran l1 l2 -> permutiran l2 l3 -> permutiran l1 l3.
Proof.
  intros E1 E2 x.
  transitivity (pojavi x l2); auto.
Qed.

Lemma permutiran_glava:
 forall (z : Z) (l l': list Z), permutiran l l' -> 
                             permutiran (z :: l) (z :: l').
Proof.
 intros z l l' H z'.
 simpl. case (z' =? z); auto.  
Qed.

Lemma permutiran_perm: forall (a b:Z) (l l':list Z),
   permutiran l l' -> permutiran (a :: b :: l) (b :: a :: l').
Proof.
 intros a b l l' H x. simpl. 
 case_eq (x =? a); case_eq (x =? b).
 intros. apply Z.eqb_eq in H0. apply Z.eqb_eq in H1.
 case (H x); auto.
 intros. apply Z.eqb_neq in H0. apply Z.eqb_eq in H1.
 case (H x); auto.
 intros. apply Z.eqb_eq in H0. apply Z.eqb_neq in H1.
 case (H x); auto.
 intros. apply Z.eqb_neq in H0. apply Z.eqb_neq in H1.
 case (H x); auto.
Qed.

Lemma vstavi_perm: forall (l : list Z) (x : Z), 
   permutiran (x :: l) ( vstavi x l).
Proof.
 induction l; simpl. intro. apply permutiran_refl.
 intros x; case_eq (x <=? a); simpl. intro. apply  permutiran_refl.
 intro. apply Z.leb_gt in H. apply permutiran_tran with (a :: x :: l). 
 apply permutiran_perm. apply permutiran_refl. 
 apply permutiran_glava; auto.
Qed.

Lemma urejen_tail (x : Z) (l : list Z): urejen (x :: l) -> urejen l.
Proof.
  induction l; firstorder.
Qed.

Lemma urejen_zacetek: forall (z1 z2:Z) (l:list Z),
   z1 <= z2 -> urejen (z2 :: l) -> urejen (z1 :: z2 :: l).
Proof.
 intros. simpl. split; auto.
Qed.

Lemma vstavi_pomozna1: forall (x y:Z) (l:list Z), 
   x <= y -> vstavi x ( y  :: l)= x :: y  :: l. 
Proof.
 intros. simpl. 
 case_eq (x <=? y). intro; auto.
 intro; apply Z.leb_nle in H0.  
 contradiction.
Qed. 

Lemma vstavi_pomozna2: forall (x y:Z) (l:list Z), 
   x > y -> y :: (vstavi  x l) = vstavi x ( y :: l). 
Proof.
 intros. simpl. 
 case_eq (x <=? y).
 intro; apply Zle_bool_imp_le in H0.
 contradiction.
 intro; auto.
Qed. 

Lemma vstavi_urejen: forall (l : list Z) (x : Z), 
   urejen l -> urejen (vstavi x l).
Proof.
 intros.  induction l. simpl; auto.
  case_eq (x <=? a). intro. apply Zle_bool_imp_le in H0. 
  rewrite vstavi_pomozna1. apply urejen_zacetek; auto. assumption.
  intro. apply Z.leb_nle in H0. rewrite <- vstavi_pomozna2.
  destruct l. simpl. split. omega. auto.
  case_eq (x <=? z). intro; apply Zle_bool_imp_le in H1. 
  rewrite vstavi_pomozna1. apply urejen_zacetek; auto; try omega. 
  apply urejen_zacetek; try omega. apply urejen_tail with a.
  assumption. try omega.
  intro. apply Z.leb_nle in H1. rewrite <- vstavi_pomozna2.
  inversion_clear H. apply urejen_zacetek; try omega. 
  rewrite <- vstavi_pomozna2 in IHl; try auto; try omega. omega. omega.
Qed.



(*izreka o pravilnosti delovanja urejanja z vstavljanjem*)

Theorem pravilnost1: forall (l: list Z), permutiran l (insertion l).
Proof.
 induction l; intros. unfold permutiran. intros; simpl; auto.
 apply permutiran_tran with (a :: insertion l). 
 apply permutiran_glava. apply IHl. apply vstavi_perm.
Qed.

Theorem pravilnost2: forall l : list Z, urejen (insertion l).
Proof.
 induction l; simpl; auto.
 apply vstavi_urejen; auto.
Defined.
