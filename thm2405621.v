Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2405621_term_abbrevs.
Require Import INT_MUL_LZERO_spec.
Require Import INT_MUL_RZERO_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2405531 (x : int) : term0 x.
Proof. exact (@lem2306290 x). Qed.
Lemma lem2405532 (x : int) : (term0 x) = ((term1 x) = term2).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2405534 (x : int) : term3 x.
Proof. exact (@lem2306041 x). Qed.
Lemma lem2405535 (x : int) : (term3 x) = ((term4 x) = term2).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem2405542 (x : int) : (term4 x) = term2.
Proof. exact (EQ_MP (@lem2405535 x) (@lem2405534 x)). Qed.
Lemma lem2405543 (x : nat) : (term5 x) = term2.
Proof. exact (@lem2405542 (int_of_num x)). Qed.
Lemma lem2405544 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405545 (x : nat) : (term6 x) = term7.
Proof. exact (MK_COMB (@lem2405544) (@lem2405543 x)). Qed.
Lemma lem2405546 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2405547 (x : nat) : ((term5 x) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem2405545 x) (@lem2405546)). Qed.
Lemma lem2405549 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405550 (x : int) : (x = x) = True.
Proof. exact (@lem2405549 int x). Qed.
Lemma lem2405551 : (term2 = term2) = True.
Proof. exact (@lem2405550 term2). Qed.
Lemma lem2405552 (x : nat) : ((term5 x) = term2) = True.
Proof. exact (TRANS (@lem2405547 x) (@lem2405551)). Qed.
Lemma lem2405553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405554 (x : nat) : (term8 x) = (and True).
Proof. exact (MK_COMB (@lem2405553) (@lem2405552 x)). Qed.
Lemma lem2405560 (x : int) : (term4 x) = term2.
Proof. exact (EQ_MP (@lem2405535 x) (@lem2405534 x)). Qed.
Lemma lem2405561 (x : nat) : (term9 x) = term2.
Proof. exact (@lem2405560 (term10 x)). Qed.
Lemma lem2405562 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405563 (x : nat) : (term11 x) = term7.
Proof. exact (MK_COMB (@lem2405562) (@lem2405561 x)). Qed.
Lemma lem2405564 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2405565 (x : nat) : ((term9 x) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem2405563 x) (@lem2405564)). Qed.
Lemma lem2405567 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405568 (x : int) : (x = x) = True.
Proof. exact (@lem2405567 int x). Qed.
Lemma lem2405569 : (term2 = term2) = True.
Proof. exact (@lem2405568 term2). Qed.
Lemma lem2405570 (x : nat) : ((term9 x) = term2) = True.
Proof. exact (TRANS (@lem2405565 x) (@lem2405569)). Qed.
Lemma lem2405571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405572 (x : nat) : (term12 x) = (and True).
Proof. exact (MK_COMB (@lem2405571) (@lem2405570 x)). Qed.
Lemma lem2405578 (x : int) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem2405532 x) (@lem2405531 x)). Qed.
Lemma lem2405579 (x : nat) : (term13 x) = term2.
Proof. exact (@lem2405578 (int_of_num x)). Qed.
Lemma lem2405580 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405581 (x : nat) : (term14 x) = term7.
Proof. exact (MK_COMB (@lem2405580) (@lem2405579 x)). Qed.
Lemma lem2405582 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2405583 (x : nat) : ((term13 x) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem2405581 x) (@lem2405582)). Qed.
Lemma lem2405585 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405586 (x : int) : (x = x) = True.
Proof. exact (@lem2405585 int x). Qed.
Lemma lem2405587 : (term2 = term2) = True.
Proof. exact (@lem2405586 term2). Qed.
Lemma lem2405588 (x : nat) : ((term13 x) = term2) = True.
Proof. exact (TRANS (@lem2405583 x) (@lem2405587)). Qed.
Lemma lem2405589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405590 (x : nat) : (term15 x) = (and True).
Proof. exact (MK_COMB (@lem2405589) (@lem2405588 x)). Qed.
Lemma lem2405594 (x : int) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem2405532 x) (@lem2405531 x)). Qed.
Lemma lem2405595 (x : nat) : (term16 x) = term2.
Proof. exact (@lem2405594 (term10 x)). Qed.
Lemma lem2405596 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405597 (x : nat) : (term17 x) = term7.
Proof. exact (MK_COMB (@lem2405596) (@lem2405595 x)). Qed.
Lemma lem2405598 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2405599 (x : nat) : ((term16 x) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem2405597 x) (@lem2405598)). Qed.
Lemma lem2405601 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405602 (x : int) : (x = x) = True.
Proof. exact (@lem2405601 int x). Qed.
Lemma lem2405603 : (term2 = term2) = True.
Proof. exact (@lem2405602 term2). Qed.
Lemma lem2405604 (x : nat) : ((term16 x) = term2) = True.
Proof. exact (TRANS (@lem2405599 x) (@lem2405603)). Qed.
Lemma lem2405605 (x : nat) : (term18 x) = (True /\ True).
Proof. exact (MK_COMB (@lem2405590 x) (@lem2405604 x)). Qed.
Lemma lem2405607 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2405608 : (True /\ True) = True.
Proof. exact (@lem2405607 True). Qed.
Lemma lem2405609 (x : nat) : (term18 x) = True.
Proof. exact (TRANS (@lem2405605 x) (@lem2405608)). Qed.
Lemma lem2405610 (x : nat) : (term19 x) = (True /\ True).
Proof. exact (MK_COMB (@lem2405572 x) (@lem2405609 x)). Qed.
Lemma lem2405612 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2405613 : (True /\ True) = True.
Proof. exact (@lem2405612 True). Qed.
Lemma lem2405614 (x : nat) : (term19 x) = True.
Proof. exact (TRANS (@lem2405610 x) (@lem2405613)). Qed.
Lemma lem2405615 (x : nat) : (term20 x) = (True /\ True).
Proof. exact (MK_COMB (@lem2405554 x) (@lem2405614 x)). Qed.
Lemma lem2405617 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2405618 : (True /\ True) = True.
Proof. exact (@lem2405617 True). Qed.
Lemma lem2405619 (x : nat) : (term20 x) = True.
Proof. exact (TRANS (@lem2405615 x) (@lem2405618)). Qed.
Lemma lem2405620 (x : nat) : True = (term20 x).
Proof. exact (SYM (@lem2405619 x)). Qed.
Lemma lem2405621 (x : nat) : term20 x.
Proof. exact (EQ_MP (@lem2405620 x) (@lem0)). Qed.
