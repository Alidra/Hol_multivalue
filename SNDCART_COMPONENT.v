Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SNDCART_COMPONENT_term_abbrevs.
Require Import LAMBDA_BETA_spec.
Require Import sndcart_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7664620 {A B : Type'} (g : nat -> A) (i : nat) : term0 A B g i.
Proof. exact (@lem7622314 A B g i). Qed.
Lemma lem7664621 {A B : Type'} (g : nat -> A) (i : nat) : (term0 A B g i) = (term1 A B g i).
Proof. exact (eq_refl (term0 A B g i)). Qed.
Lemma lem7664622 {A B : Type'} (g : nat -> A) (i : nat) : term1 A B g i.
Proof. exact (EQ_MP (@lem7664621 A B g i) (@lem7664620 A B g i)). Qed.
Lemma lem7664623 {B : Type'} (i : nat) (h1 : term2 B i) : term2 B i.
Proof. exact (h1). Qed.
Lemma lem7664624 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term2 B i) : (term3 A B g i) = (g i).
Proof. exact (@lem7664622 A B g i (@lem7664623 B i h1)). Qed.
Lemma lem7664630 {A M N : Type'} (f : type2 A M N) : term4 A M N f.
Proof. exact (@lem7635254 A M N f). Qed.
Lemma lem7664631 {A M N : Type'} (f : type2 A M N) : (term4 A M N f) = ((@sndcart A M N f) = (term5 A M N f)).
Proof. exact (eq_refl (term4 A M N f)). Qed.
Lemma lem7664644 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term6 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7664645 (p : Prop) (q : Prop) (p' : Prop) : term7 p q p'.
Proof. exact (fun q' : Prop => @lem7664644 p q p' q'). Qed.
Lemma lem7664646 (p : Prop) (q : Prop) : term8 p q.
Proof. exact (fun p' : Prop => @lem7664645 p q p'). Qed.
Lemma lem7664647 {A M N : Type'} (x : type2 A M N) (i : nat) : term9 A M N x i.
Proof. exact (@lem7664646 (term2 N i) ((term10 A M N x i) = (term11 A M N x i))). Qed.
Lemma lem7664648 {A M N : Type'} (x : type2 A M N) (i : nat) (p' : Prop) : term12 A M N x i p'.
Proof. exact (@lem7664647 A M N x i p'). Qed.
Lemma lem7664649 {A M N : Type'} (x : type2 A M N) (i : nat) (p' : Prop) : (term12 A M N x i p') = (term13 A M N x i p').
Proof. exact (eq_refl (term12 A M N x i p')). Qed.
Lemma lem7664650 {A M N : Type'} (x : type2 A M N) (i : nat) (p' : Prop) : term13 A M N x i p'.
Proof. exact (EQ_MP (@lem7664649 A M N x i p') (@lem7664648 A M N x i p')). Qed.
Lemma lem7664651 {A M N : Type'} (x : type2 A M N) (i : nat) (p' : Prop) (q' : Prop) : term14 A M N x i p' q'.
Proof. exact (@lem7664650 A M N x i p' q'). Qed.
Lemma lem7664652 {A M N : Type'} (x : type2 A M N) (i : nat) (p' : Prop) (q' : Prop) : (term14 A M N x i p' q') = (term15 A M N x i p' q').
Proof. exact (eq_refl (term14 A M N x i p' q')). Qed.
Lemma lem7664653 {A M N : Type'} (x : type2 A M N) (i : nat) (p' : Prop) (q' : Prop) : term15 A M N x i p' q'.
Proof. exact (EQ_MP (@lem7664652 A M N x i p' q') (@lem7664651 A M N x i p' q')). Qed.
Lemma lem7664656 {N : Type'} (i : nat) : (term2 N i) = (term2 N i).
Proof. exact (eq_refl (term2 N i)). Qed.
Lemma lem7664657 {A M N : Type'} (x : type2 A M N) (i : nat) (q' : Prop) : term16 A M N x i q'.
Proof. exact (@lem7664653 A M N x i (term2 N i) q'). Qed.
Lemma lem7664658 {A M N : Type'} (x : type2 A M N) (i : nat) (q' : Prop) : term17 A M N x i q'.
Proof. exact (@lem7664657 A M N x i q' (@lem7664656 N i)). Qed.
Lemma lem7664659 {N : Type'} (i : nat) (h1 : term2 N i) : term2 N i.
Proof. exact (h1). Qed.
Lemma lem7664660 {N : Type'} (i : nat) (h1 : term2 N i) : term18 N i.
Proof. exact (proj2 (@lem7664659 N i h1)). Qed.
Lemma lem7664661 {N : Type'} (i : nat) : (term18 N i) = ((term18 N i) = True).
Proof. exact (@lem7 (term18 N i)). Qed.
Lemma lem7664663 {N : Type'} (i : nat) (h1 : term2 N i) : term19 i.
Proof. exact (proj1 (@lem7664659 N i h1)). Qed.
Lemma lem7664664 (i : nat) : (term19 i) = ((term19 i) = True).
Proof. exact (@lem7 (term19 i)). Qed.
Lemma lem7664669 {A M N : Type'} (f : type2 A M N) : (@sndcart A M N f) = (term5 A M N f).
Proof. exact (EQ_MP (@lem7664631 A M N f) (@lem7664630 A M N f)). Qed.
Lemma lem7664670 {A M N : Type'} (f : type2 A M N) : (@sndcart A M N f) = (term5 A M N f).
Proof. exact (@lem7664669 A M N f). Qed.
Lemma lem7664671 {A M N : Type'} (x : type2 A M N) : (@sndcart A M N x) = (term5 A M N x).
Proof. exact (@lem7664670 A M N x). Qed.
Lemma lem7664672 {A N : Type'} : (@dollar A N) = (@dollar A N).
Proof. exact (eq_refl (@dollar A N)). Qed.
Lemma lem7664673 {A M N : Type'} (x : type2 A M N) : (term20 A M N x) = (term21 A M N x).
Proof. exact (MK_COMB (@lem7664672 A N) (@lem7664671 A M N x)). Qed.
Lemma lem7664674 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7664675 {A M N : Type'} (x : type2 A M N) (i : nat) : (term10 A M N x i) = (term22 A M N x i).
Proof. exact (MK_COMB (@lem7664673 A M N x) (@lem7664674 i)). Qed.
Lemma lem7664677 {A B : Type'} (g : nat -> A) (i : nat) : term1 A B g i.
Proof. exact (fun h0 : term2 B i => @lem7664624 A B g i h0). Qed.
Lemma lem7664678 {A N : Type'} (g : nat -> A) (i : nat) : term1 A N g i.
Proof. exact (@lem7664677 A N g i). Qed.
Lemma lem7664679 {A M N : Type'} (x : type2 A M N) (i : nat) : term23 A M N x i.
Proof. exact (@lem7664678 A N (term24 A M N x) i). Qed.
Lemma lem7664683 {N : Type'} (i : nat) (h1 : term2 N i) : (term19 i) = True.
Proof. exact (EQ_MP (@lem7664664 i) (@lem7664663 N i h1)). Qed.
Lemma lem7664684 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7664685 {N : Type'} (i : nat) (h1 : term2 N i) : (term25 i) = (and True).
Proof. exact (MK_COMB (@lem7664684) (@lem7664683 N i h1)). Qed.
Lemma lem7664687 {N : Type'} (i : nat) (h1 : term2 N i) : (term18 N i) = True.
Proof. exact (EQ_MP (@lem7664661 N i) (@lem7664660 N i h1)). Qed.
Lemma lem7664688 {N : Type'} (i : nat) (h1 : term2 N i) : (term2 N i) = (True /\ True).
Proof. exact (MK_COMB (@lem7664685 N i h1) (@lem7664687 N i h1)). Qed.
Lemma lem7664690 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7664691 : (True /\ True) = True.
Proof. exact (@lem7664690 True). Qed.
Lemma lem7664692 {N : Type'} (i : nat) (h1 : term2 N i) : (term2 N i) = True.
Proof. exact (TRANS (@lem7664688 N i h1) (@lem7664691)). Qed.
Lemma lem7664693 {N : Type'} (i : nat) (h1 : term2 N i) : True = (term2 N i).
Proof. exact (SYM (@lem7664692 N i h1)). Qed.
Lemma lem7664694 {N : Type'} (i : nat) (h1 : term2 N i) : term2 N i.
Proof. exact (EQ_MP (@lem7664693 N i h1) (@lem0)). Qed.
Lemma lem7664695 {A M N : Type'} (x : type2 A M N) (i : nat) (h1 : term2 N i) : (term22 A M N x i) = (term26 A M N x i).
Proof. exact (@lem7664679 A M N x i (@lem7664694 N i h1)). Qed.
Lemma lem7664697 {A B : Type'} (f : A -> B) (y : A) : (term27 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7664698 {A : Type'} (f : nat -> A) (y : nat) : (term28 A f y) = (f y).
Proof. exact (@lem7664697 nat A f y). Qed.
Lemma lem7664699 {A M N : Type'} (x : type2 A M N) (i : nat) : (term29 A M N x i) = (term26 A M N x i).
Proof. exact (@lem7664698 A (term24 A M N x) i). Qed.
Lemma lem7664700 {A M N : Type'} (x : type2 A M N) (i : nat) : (term26 A M N x i) = (term11 A M N x i).
Proof. exact (eq_refl (term26 A M N x i)). Qed.
Lemma lem7664701 {A M N : Type'} (x : type2 A M N) : (term30 A M N x) = (term24 A M N x).
Proof. exact (fun_ext (fun i : nat => @lem7664700 A M N x i)). Qed.
Lemma lem7664702 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7664703 {A M N : Type'} (x : type2 A M N) (i : nat) : (term29 A M N x i) = (term26 A M N x i).
Proof. exact (MK_COMB (@lem7664701 A M N x) (@lem7664702 i)). Qed.
Lemma lem7664704 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7664705 {A M N : Type'} (x : type2 A M N) (i : nat) : (term31 A M N x i) = (term32 A M N x i).
Proof. exact (MK_COMB (@lem7664704 A) (@lem7664703 A M N x i)). Qed.
Lemma lem7664706 {A M N : Type'} (x : type2 A M N) (i : nat) : (term26 A M N x i) = (term11 A M N x i).
Proof. exact (eq_refl (term26 A M N x i)). Qed.
Lemma lem7664707 {A M N : Type'} (x : type2 A M N) (i : nat) : ((term29 A M N x i) = (term26 A M N x i)) = ((term26 A M N x i) = (term11 A M N x i)).
Proof. exact (MK_COMB (@lem7664705 A M N x i) (@lem7664706 A M N x i)). Qed.
Lemma lem7664708 {A M N : Type'} (x : type2 A M N) (i : nat) : (term26 A M N x i) = (term11 A M N x i).
Proof. exact (EQ_MP (@lem7664707 A M N x i) (@lem7664699 A M N x i)). Qed.
Lemma lem7664709 {A M N : Type'} (x : type2 A M N) (i : nat) (h1 : term2 N i) : (term22 A M N x i) = (term11 A M N x i).
Proof. exact (TRANS (@lem7664695 A M N x i h1) (@lem7664708 A M N x i)). Qed.
Lemma lem7664710 {A M N : Type'} (x : type2 A M N) (i : nat) (h1 : term2 N i) : (term10 A M N x i) = (term11 A M N x i).
Proof. exact (TRANS (@lem7664675 A M N x i) (@lem7664709 A M N x i h1)). Qed.
Lemma lem7664711 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7664712 {A M N : Type'} (x : type2 A M N) (i : nat) (h1 : term2 N i) : (term33 A M N x i) = (term34 A M N x i).
Proof. exact (MK_COMB (@lem7664711 A) (@lem7664710 A M N x i h1)). Qed.
Lemma lem7664713 {A M N : Type'} (x : type2 A M N) (i : nat) : (term11 A M N x i) = (term11 A M N x i).
Proof. exact (eq_refl (term11 A M N x i)). Qed.
Lemma lem7664714 {A M N : Type'} (x : type2 A M N) (i : nat) (h1 : term2 N i) : ((term10 A M N x i) = (term11 A M N x i)) = ((term11 A M N x i) = (term11 A M N x i)).
Proof. exact (MK_COMB (@lem7664712 A M N x i h1) (@lem7664713 A M N x i)). Qed.
Lemma lem7664716 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7664717 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem7664716 A x). Qed.
Lemma lem7664718 {A M N : Type'} (x : type2 A M N) (i : nat) : ((term11 A M N x i) = (term11 A M N x i)) = True.
Proof. exact (@lem7664717 A (term11 A M N x i)). Qed.
Lemma lem7664719 {A M N : Type'} (x : type2 A M N) (i : nat) (h1 : term2 N i) : ((term10 A M N x i) = (term11 A M N x i)) = True.
Proof. exact (TRANS (@lem7664714 A M N x i h1) (@lem7664718 A M N x i)). Qed.
Lemma lem7664720 {A M N : Type'} (x : type2 A M N) (i : nat) : term35 A M N x i.
Proof. exact (fun h0 : term2 N i => @lem7664719 A M N x i h0). Qed.
Lemma lem7664721 {A M N : Type'} (x : type2 A M N) (i : nat) : term36 A M N x i.
Proof. exact (@lem7664658 A M N x i True). Qed.
Lemma lem7664722 {A M N : Type'} (x : type2 A M N) (i : nat) : (term37 A M N x i) = (term38 N i).
Proof. exact (@lem7664721 A M N x i (@lem7664720 A M N x i)). Qed.
Lemma lem7664724 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7664725 {N : Type'} (i : nat) : (term38 N i) = True.
Proof. exact (@lem7664724 (term2 N i)). Qed.
Lemma lem7664726 {A M N : Type'} (x : type2 A M N) (i : nat) : (term37 A M N x i) = True.
Proof. exact (TRANS (@lem7664722 A M N x i) (@lem7664725 N i)). Qed.
Lemma lem7664727 {A M N : Type'} (x : type2 A M N) : (term39 A M N x) = term40.
Proof. exact (fun_ext (fun i : nat => @lem7664726 A M N x i)). Qed.
Lemma lem7664728 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7664729 {A M N : Type'} (x : type2 A M N) : (term41 A M N x) = term42.
Proof. exact (MK_COMB (@lem7664728) (@lem7664727 A M N x)). Qed.
Lemma lem7664731 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7664732 (t : Prop) : (term44 t) = t.
Proof. exact (@lem7664731 nat t). Qed.
Lemma lem7664733 : term42 = True.
Proof. exact (@lem7664732 True). Qed.
Lemma lem7664734 {A M N : Type'} (x : type2 A M N) : (term41 A M N x) = True.
Proof. exact (TRANS (@lem7664729 A M N x) (@lem7664733)). Qed.
Lemma lem7664735 {A M N : Type'} : (term45 A M N) = (term46 A M N).
Proof. exact (fun_ext (fun x : type2 A M N => @lem7664734 A M N x)). Qed.
Lemma lem7664736 {A M N : Type'} : (@all (cart A (finite_sum M N))) = (@all (cart A (finite_sum M N))).
Proof. exact (eq_refl (@all (cart A (finite_sum M N)))). Qed.
Lemma lem7664737 {A M N : Type'} : (term47 A M N) = (term48 A M N).
Proof. exact (MK_COMB (@lem7664736 A M N) (@lem7664735 A M N)). Qed.
Lemma lem7664739 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7664740 {A M N : Type'} (t : Prop) : (term49 A M N t) = t.
Proof. exact (@lem7664739 (type2 A M N) t). Qed.
Lemma lem7664741 {A M N : Type'} : (term48 A M N) = True.
Proof. exact (@lem7664740 A M N True). Qed.
Lemma lem7664742 {A M N : Type'} : (term47 A M N) = True.
Proof. exact (TRANS (@lem7664737 A M N) (@lem7664741 A M N)). Qed.
Lemma lem7664743 {A M N : Type'} : True = (term47 A M N).
Proof. exact (SYM (@lem7664742 A M N)). Qed.
Lemma lem7664744 {A M N : Type'} : term47 A M N.
Proof. exact (EQ_MP (@lem7664743 A M N) (@lem0)). Qed.
