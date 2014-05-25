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
