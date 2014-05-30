Require Import List.
Require Import Bool.
Require Import ZArith.
Local Open Scope list_scope.


(*vstavi v ze urejen seznam*)
Fixpoint vstavi (x : Z) (l : list Z) : list Z :=
  match l with
    | nil => x :: nil
    | h :: l' => 
      if Z.leb x h
        then x :: l
        else h :: vstavi x l'
    end.

(*insertion sort*)
Fixpoint insertion (l : list Z) :=
  match l with
    | nil => nil
    | x :: l' => vstavi x (insertion l')
  end.

(*pomozna za indukcijo na seznamih*)
Fixpoint list_ind_2
         {A : Set}
         (P : list A -> Prop)
         (p0 : P nil)
         (p1 : forall x, P (x :: nil))
         (p2 : forall x y l, P l -> P (x :: y :: l))
         (l : list A) :=
  match l return P l with
    | nil => p0
    | x :: nil => p1 x
    | x :: y :: l' => p2 x y l' (list_ind_2 P p0 p1 p2 l')
  end.

(*definicija za urejenost*)
Fixpoint urejen (l : list Z) :=
  match l with
    | nil => True
    | _ :: nil => True 
    | x :: ((y :: _) as l') => (x <= y)%Z /\ urejen l' 
  end. 


Lemma insert_urejen: forall (x:Z) (l: list Z), urejen (l) -> urejen( vstavi x l).
Proof.
  intros z lst H.  
  induction lst.
  - simpl. auto.
  - unfold vstavi. 
admit. (*se ni dokocana*)
Qed.

(*1. glavni izrek*)
Theorem insertion_deluje_1' : forall l : list Z, urejen (insertion l).
Proof.
  apply (list_ind_2 (fun l =>  urejen (insertion l))).
  - simpl; auto.
  - simpl; auto.
  - intros. 
    simpl. apply insert_urejen. apply insert_urejen. apply H. 
Qed.



Fixpoint st_pojavitev (x : Z) (l : list Z) : nat :=
  match l with
  | nil => 0
  | (h :: l') =>
      match Z_eq_dec x h with
      | left _ => S (st_pojavitev x l')
      | right _ => st_pojavitev x l'
      end
  end.
 
 (*enakost dveh seznamov*)
Definition enaka (l1 l2 : list Z) : Prop :=
  forall (x:Z), st_pojavitev x l1 = st_pojavitev x l2.

Lemma enaka_refl: forall (l : list Z), enaka l l.
Proof.
 induction l.
 - unfold enaka. auto.
 - unfold enaka. auto.
Qed.

Lemma enaka_simetr: forall (l l' : list Z), enaka l  l' -> enaka l' l.
Proof.
 induction l.
 - unfold enaka. auto.
 -  unfold enaka. auto.
Qed.

Lemma enaka_tr: forall l l' l'':list Z, enaka l l' -> enaka l' l'' -> enaka l l''.
Proof.
 intros. intro x.
 SearchAbout trans_eq.
 eapply trans_eq.
 - auto.
 - auto.
Qed.

Lemma enaka_nov_elt: forall (x : Z) (l l' : list Z), enaka l l' -> enaka (x :: l) (x :: l').
Proof.
 intros. intro x'. simpl. case (Z_eq_dec x' x).
 - auto.
 - auto.
Qed.

Lemma enakost_zamenjan: forall (x y : Z) (l l' : list Z), enaka l l' -> enaka (x :: y :: l) (y :: x :: l').
Proof.
 intros. intro. simpl.
 case (Z_eq_dec x0 y). 
 case (Z_eq_dec x0 x).
 - case (H x0).  auto.
 - auto.
 - case (H x0). auto. 
Qed.

Lemma vstavi_enakost: forall (x : Z) (l : list Z), enaka (x :: l) (vstavi x l).
Proof.
  unfold enaka. intros. simpl. elim (Z.eq_dec x x0).
admit. 
admit. 
Qed.

Theorem deluje2: forall (l l': list Z), l' = insertion l -> enaka l l'.
Proof.
  induction l. intros.
  - unfold enaka. simpl. rewrite H. auto.
  - intros. simpl in H.  rewrite H. intro.
admit.  
Qed.

