Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4333669_term_abbrevs.
Require Import CROSS_UNIV_spec.
Require Import FINITE_CROSS_EQ_spec.
Require Import UNIV_NOT_EMPTY_spec.
Require Import thm1833_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem4333571 {A B : Type'} (h1 : (@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B))) : (@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B)).
Proof. exact (h1). Qed.
Lemma lem4333572 {A B : Type'} (h1 : (@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B))) : (@UNIV (prod A B)) = (@CROSS B A (@UNIV A) (@UNIV B)).
Proof. exact (SYM (@lem4333571 A B h1)). Qed.
Lemma lem4333573 {A B : Type'} (h1 : (@UNIV (prod A B)) = (@CROSS B A (@UNIV A) (@UNIV B))) : (@UNIV (prod A B)) = (@CROSS B A (@UNIV A) (@UNIV B)).
Proof. exact (h1). Qed.
Lemma lem4333574 {A B : Type'} (h1 : (@UNIV (prod A B)) = (@CROSS B A (@UNIV A) (@UNIV B))) : (@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B)).
Proof. exact (SYM (@lem4333573 A B h1)). Qed.
Lemma lem4333575 {A B : Type'} : ((@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B))) = ((@UNIV (prod A B)) = (@CROSS B A (@UNIV A) (@UNIV B))).
Proof. exact (prop_ext (fun h1 : (@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B)) => @lem4333572 A B h1) (fun h1 : (@UNIV (prod A B)) = (@CROSS B A (@UNIV A) (@UNIV B)) => @lem4333574 A B h1)). Qed.
Lemma lem4333577 {A : Type'} : term0 A.
Proof. exact (@lem82 ((@UNIV A) = (@EMPTY A))). Qed.
Lemma lem4333590 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (@lem4330214 A B s). Qed.
Lemma lem4333591 {A B : Type'} (s : A -> Prop) : (term1 A B s) = (term2 A B s).
Proof. exact (eq_refl (term1 A B s)). Qed.
Lemma lem4333592 {A B : Type'} (s : A -> Prop) : term2 A B s.
Proof. exact (EQ_MP (@lem4333591 A B s) (@lem4333590 A B s)). Qed.
Lemma lem4333593 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term3 A B s t.
Proof. exact (@lem4333592 A B s t). Qed.
Lemma lem4333594 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term3 A B s t) = ((term4 A B s t) = (term5 A B s t)).
Proof. exact (eq_refl (term3 A B s t)). Qed.
Lemma lem4333599 {A B : Type'} : (@UNIV (prod A B)) = (@CROSS B A (@UNIV A) (@UNIV B)).
Proof. exact (EQ_MP (@lem4333575 A B) (@lem4327456 A B)). Qed.
Lemma lem4333604 {A B : Type'} : (@FINITE (prod A B)) = (@FINITE (prod A B)).
Proof. exact (eq_refl (@FINITE (prod A B))). Qed.
Lemma lem4333605 {A B : Type'} : (@FINITE (prod A B) (@UNIV (prod A B))) = (term6 A B).
Proof. exact (MK_COMB (@lem4333604 A B) (@lem4333599 A B)). Qed.
Lemma lem4333607 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term4 A B s t) = (term5 A B s t).
Proof. exact (EQ_MP (@lem4333594 A B s t) (@lem4333593 A B s t)). Qed.
Lemma lem4333608 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term4 A B s t) = (term5 A B s t).
Proof. exact (@lem4333607 A B s t). Qed.
Lemma lem4333609 {A B : Type'} : (term6 A B) = (term7 A B).
Proof. exact (@lem4333608 A B (@UNIV A) (@UNIV B)). Qed.
Lemma lem4333613 {A : Type'} : ((@UNIV A) = (@EMPTY A)) = False.
Proof. exact (@lem4333577 A (@lem3216430 A)). Qed.
Lemma lem4333614 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4333615 {A : Type'} : (term8 A) = (or False).
Proof. exact (MK_COMB (@lem4333614) (@lem4333613 A)). Qed.
Lemma lem4333619 {A : Type'} : ((@UNIV A) = (@EMPTY A)) = False.
Proof. exact (@lem4333577 A (@lem3216430 A)). Qed.
Lemma lem4333620 {B : Type'} : ((@UNIV B) = (@EMPTY B)) = False.
Proof. exact (@lem4333619 B). Qed.
Lemma lem4333621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4333622 {B : Type'} : (term8 B) = (or False).
Proof. exact (MK_COMB (@lem4333621) (@lem4333620 B)). Qed.
Lemma lem4333629 {A B : Type'} : (term9 A B) = (term9 A B).
Proof. exact (eq_refl (term9 A B)). Qed.
Lemma lem4333630 {A B : Type'} : (term10 A B) = (term11 A B).
Proof. exact (MK_COMB (@lem4333622 B) (@lem4333629 A B)). Qed.
Lemma lem4333632 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4333633 {A B : Type'} : (term11 A B) = (term9 A B).
Proof. exact (@lem4333632 (term9 A B)). Qed.
Lemma lem4333640 {A B : Type'} : (term10 A B) = (term9 A B).
Proof. exact (TRANS (@lem4333630 A B) (@lem4333633 A B)). Qed.
Lemma lem4333641 {A B : Type'} : (term7 A B) = (term11 A B).
Proof. exact (MK_COMB (@lem4333615 A) (@lem4333640 A B)). Qed.
Lemma lem4333643 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4333644 {A B : Type'} : (term11 A B) = (term9 A B).
Proof. exact (@lem4333643 (term9 A B)). Qed.
Lemma lem4333651 {A B : Type'} : (term7 A B) = (term9 A B).
Proof. exact (TRANS (@lem4333641 A B) (@lem4333644 A B)). Qed.
Lemma lem4333652 {A B : Type'} : (term6 A B) = (term9 A B).
Proof. exact (TRANS (@lem4333609 A B) (@lem4333651 A B)). Qed.
Lemma lem4333653 {A B : Type'} : (@FINITE (prod A B) (@UNIV (prod A B))) = (term9 A B).
Proof. exact (TRANS (@lem4333605 A B) (@lem4333652 A B)). Qed.
Lemma lem4333654 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4333655 {A B : Type'} : (term12 A B) = (term13 A B).
Proof. exact (MK_COMB (@lem4333654) (@lem4333653 A B)). Qed.
Lemma lem4333662 {A B : Type'} : (term9 A B) = (term9 A B).
Proof. exact (eq_refl (term9 A B)). Qed.
Lemma lem4333663 {A B : Type'} : ((@FINITE (prod A B) (@UNIV (prod A B))) = (term9 A B)) = ((term9 A B) = (term9 A B)).
Proof. exact (MK_COMB (@lem4333655 A B) (@lem4333662 A B)). Qed.
Lemma lem4333665 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4333666 (x : Prop) : (x = x) = True.
Proof. exact (@lem4333665 Prop x). Qed.
Lemma lem4333667 {A B : Type'} : ((term9 A B) = (term9 A B)) = True.
Proof. exact (@lem4333666 (term9 A B)). Qed.
Lemma lem4333668 {A B : Type'} : ((@FINITE (prod A B) (@UNIV (prod A B))) = (term9 A B)) = True.
Proof. exact (TRANS (@lem4333663 A B) (@lem4333667 A B)). Qed.
Lemma lem4333669 {A B : Type'} : True = ((@FINITE (prod A B) (@UNIV (prod A B))) = (term9 A B)).
Proof. exact (SYM (@lem4333668 A B)). Qed.
