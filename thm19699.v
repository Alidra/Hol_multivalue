Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm19699_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem19505 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem19506 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem19507 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem19506 a) (@lem19505 a)). Qed.
Lemma lem19508 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem19509 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem19524 (b : Prop) (c : Prop) : (term2 b c) = (term2 b c).
Proof. exact (eq_refl (term2 b c)). Qed.
Lemma lem19525 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term3 b c a) = (term4 b c).
Proof. exact (MK_COMB (@lem19524 b c) (@lem19508 a h1)). Qed.
Lemma lem19526 (b : Prop) (c : Prop) : (term4 b c) = ((term5 b c) = (term6 b c)).
Proof. exact (eq_refl (term4 b c)). Qed.
Lemma lem19527 (b : Prop) (c : Prop) (a : Prop) : (term7 b c a) = (term7 b c a).
Proof. exact (eq_refl (term7 b c a)). Qed.
Lemma lem19528 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term4 b c)) = ((term3 b c a) = ((term5 b c) = (term6 b c))).
Proof. exact (MK_COMB (@lem19527 b c a) (@lem19526 b c)). Qed.
Lemma lem19529 (a : Prop) (b : Prop) (c : Prop) : (term3 b c a) = ((term8 a b c) = (term9 a b c)).
Proof. exact (eq_refl (term3 b c a)). Qed.
Lemma lem19530 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19531 (a : Prop) (b : Prop) (c : Prop) : (term7 b c a) = (term10 a b c).
Proof. exact (MK_COMB (@lem19530) (@lem19529 a b c)). Qed.
Lemma lem19532 (b : Prop) (c : Prop) : ((term5 b c) = (term6 b c)) = ((term5 b c) = (term6 b c)).
Proof. exact (eq_refl ((term5 b c) = (term6 b c))). Qed.
Lemma lem19533 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = ((term5 b c) = (term6 b c))) = (((term8 a b c) = (term9 a b c)) = ((term5 b c) = (term6 b c))).
Proof. exact (MK_COMB (@lem19531 a b c) (@lem19532 b c)). Qed.
Lemma lem19534 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term4 b c)) = (((term8 a b c) = (term9 a b c)) = ((term5 b c) = (term6 b c))).
Proof. exact (TRANS (@lem19528 a b c) (@lem19533 a b c)). Qed.
Lemma lem19535 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term8 a b c) = (term9 a b c)) = ((term5 b c) = (term6 b c)).
Proof. exact (EQ_MP (@lem19534 a b c) (@lem19525 b c a h1)). Qed.
Lemma lem19536 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term5 b c) = (term6 b c)) = ((term8 a b c) = (term9 a b c)).
Proof. exact (SYM (@lem19535 b c a h1)). Qed.
Lemma lem19537 (b : Prop) (c : Prop) : (term2 b c) = (term2 b c).
Proof. exact (eq_refl (term2 b c)). Qed.
Lemma lem19538 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term3 b c a) = (term11 b c).
Proof. exact (MK_COMB (@lem19537 b c) (@lem19509 a h1)). Qed.
Lemma lem19539 (b : Prop) (c : Prop) : (term11 b c) = ((term12 b c) = (term13 b c)).
Proof. exact (eq_refl (term11 b c)). Qed.
Lemma lem19540 (b : Prop) (c : Prop) (a : Prop) : (term7 b c a) = (term7 b c a).
Proof. exact (eq_refl (term7 b c a)). Qed.
Lemma lem19541 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term11 b c)) = ((term3 b c a) = ((term12 b c) = (term13 b c))).
Proof. exact (MK_COMB (@lem19540 b c a) (@lem19539 b c)). Qed.
Lemma lem19542 (a : Prop) (b : Prop) (c : Prop) : (term3 b c a) = ((term8 a b c) = (term9 a b c)).
Proof. exact (eq_refl (term3 b c a)). Qed.
Lemma lem19543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19544 (a : Prop) (b : Prop) (c : Prop) : (term7 b c a) = (term10 a b c).
Proof. exact (MK_COMB (@lem19543) (@lem19542 a b c)). Qed.
Lemma lem19545 (b : Prop) (c : Prop) : ((term12 b c) = (term13 b c)) = ((term12 b c) = (term13 b c)).
Proof. exact (eq_refl ((term12 b c) = (term13 b c))). Qed.
Lemma lem19546 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = ((term12 b c) = (term13 b c))) = (((term8 a b c) = (term9 a b c)) = ((term12 b c) = (term13 b c))).
Proof. exact (MK_COMB (@lem19544 a b c) (@lem19545 b c)). Qed.
Lemma lem19547 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term11 b c)) = (((term8 a b c) = (term9 a b c)) = ((term12 b c) = (term13 b c))).
Proof. exact (TRANS (@lem19541 a b c) (@lem19546 a b c)). Qed.
Lemma lem19548 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term8 a b c) = (term9 a b c)) = ((term12 b c) = (term13 b c)).
Proof. exact (EQ_MP (@lem19547 a b c) (@lem19538 b c a h1)). Qed.
Lemma lem19549 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term12 b c) = (term13 b c)) = ((term8 a b c) = (term9 a b c)).
Proof. exact (SYM (@lem19548 b c a h1)). Qed.
Lemma lem19555 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem19556 (b : Prop) : (True /\ b) = b.
Proof. exact (@lem19555 b). Qed.
Lemma lem19557 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem19558 (b : Prop) : (term14 b) = (or b).
Proof. exact (MK_COMB (@lem19557) (@lem19556 b)). Qed.
Lemma lem19559 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem19560 (b : Prop) (c : Prop) : (term5 b c) = (b \/ c).
Proof. exact (MK_COMB (@lem19558 b) (@lem19559 c)). Qed.
Lemma lem19563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19564 (b : Prop) (c : Prop) : (term15 b c) = (term16 b c).
Proof. exact (MK_COMB (@lem19563) (@lem19560 b c)). Qed.
Lemma lem19568 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem19569 (c : Prop) : (True \/ c) = True.
Proof. exact (@lem19568 c). Qed.
Lemma lem19570 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem19571 (c : Prop) : (term17 c) = (and True).
Proof. exact (MK_COMB (@lem19570) (@lem19569 c)). Qed.
Lemma lem19574 (b : Prop) (c : Prop) : (b \/ c) = (b \/ c).
Proof. exact (eq_refl (b \/ c)). Qed.
Lemma lem19575 (b : Prop) (c : Prop) : (term6 b c) = (term18 b c).
Proof. exact (MK_COMB (@lem19571 c) (@lem19574 b c)). Qed.
Lemma lem19577 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem19578 (b : Prop) (c : Prop) : (term18 b c) = (b \/ c).
Proof. exact (@lem19577 (b \/ c)). Qed.
Lemma lem19581 (b : Prop) (c : Prop) : (term6 b c) = (b \/ c).
Proof. exact (TRANS (@lem19575 b c) (@lem19578 b c)). Qed.
Lemma lem19582 (b : Prop) (c : Prop) : ((term5 b c) = (term6 b c)) = ((b \/ c) = (b \/ c)).
Proof. exact (MK_COMB (@lem19564 b c) (@lem19581 b c)). Qed.
Lemma lem19584 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem19585 (x : Prop) : (x = x) = True.
Proof. exact (@lem19584 Prop x). Qed.
Lemma lem19586 (b : Prop) (c : Prop) : ((b \/ c) = (b \/ c)) = True.
Proof. exact (@lem19585 (b \/ c)). Qed.
Lemma lem19587 (b : Prop) (c : Prop) : ((term5 b c) = (term6 b c)) = True.
Proof. exact (TRANS (@lem19582 b c) (@lem19586 b c)). Qed.
Lemma lem19588 (b : Prop) (c : Prop) : True = ((term5 b c) = (term6 b c)).
Proof. exact (SYM (@lem19587 b c)). Qed.
Lemma lem19589 (b : Prop) (c : Prop) : (term5 b c) = (term6 b c).
Proof. exact (EQ_MP (@lem19588 b c) (@lem0)). Qed.
Lemma lem19595 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem19596 (b : Prop) : (False /\ b) = False.
Proof. exact (@lem19595 b). Qed.
Lemma lem19597 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem19598 (b : Prop) : (term19 b) = (or False).
Proof. exact (MK_COMB (@lem19597) (@lem19596 b)). Qed.
Lemma lem19599 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem19600 (b : Prop) (c : Prop) : (term12 b c) = (False \/ c).
Proof. exact (MK_COMB (@lem19598 b) (@lem19599 c)). Qed.
Lemma lem19602 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem19603 (c : Prop) : (False \/ c) = c.
Proof. exact (@lem19602 c). Qed.
Lemma lem19604 (b : Prop) (c : Prop) : (term12 b c) = c.
Proof. exact (TRANS (@lem19600 b c) (@lem19603 c)). Qed.
Lemma lem19605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19606 (b : Prop) (c : Prop) : (term20 b c) = (@eq Prop c).
Proof. exact (MK_COMB (@lem19605) (@lem19604 b c)). Qed.
Lemma lem19610 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem19611 (c : Prop) : (False \/ c) = c.
Proof. exact (@lem19610 c). Qed.
Lemma lem19612 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem19613 (c : Prop) : (term21 c) = (and c).
Proof. exact (MK_COMB (@lem19612) (@lem19611 c)). Qed.
Lemma lem19616 (b : Prop) (c : Prop) : (b \/ c) = (b \/ c).
Proof. exact (eq_refl (b \/ c)). Qed.
Lemma lem19617 (b : Prop) (c : Prop) : (term13 b c) = (term22 b c).
Proof. exact (MK_COMB (@lem19613 c) (@lem19616 b c)). Qed.
Lemma lem19620 (b : Prop) (c : Prop) : ((term12 b c) = (term13 b c)) = (c = (term22 b c)).
Proof. exact (MK_COMB (@lem19606 b c) (@lem19617 b c)). Qed.
Lemma lem19623 (b : Prop) (c : Prop) : (c = (term22 b c)) = ((term12 b c) = (term13 b c)).
Proof. exact (SYM (@lem19620 b c)). Qed.
Lemma lem19624 (c : Prop) : term0 c.
Proof. exact (@lem9851 c). Qed.
Lemma lem19625 (c : Prop) : (term0 c) = (term1 c).
Proof. exact (eq_refl (term0 c)). Qed.
Lemma lem19626 (c : Prop) : term1 c.
Proof. exact (EQ_MP (@lem19625 c) (@lem19624 c)). Qed.
Lemma lem19627 (c : Prop) (h1 : c = True) : c = True.
Proof. exact (h1). Qed.
Lemma lem19628 (c : Prop) (h1 : c = False) : c = False.
Proof. exact (h1). Qed.
Lemma lem19637 (b : Prop) : (term23 b) = (term23 b).
Proof. exact (eq_refl (term23 b)). Qed.
Lemma lem19638 (b : Prop) (c : Prop) (h1 : c = True) : (term24 b c) = (term25 b).
Proof. exact (MK_COMB (@lem19637 b) (@lem19627 c h1)). Qed.
Lemma lem19639 (b : Prop) : (term25 b) = (True = (term26 b)).
Proof. exact (eq_refl (term25 b)). Qed.
Lemma lem19640 (b : Prop) (c : Prop) : (term27 b c) = (term27 b c).
Proof. exact (eq_refl (term27 b c)). Qed.
Lemma lem19641 (c : Prop) (b : Prop) : ((term24 b c) = (term25 b)) = ((term24 b c) = (True = (term26 b))).
Proof. exact (MK_COMB (@lem19640 b c) (@lem19639 b)). Qed.
Lemma lem19642 (b : Prop) (c : Prop) : (term24 b c) = (c = (term22 b c)).
Proof. exact (eq_refl (term24 b c)). Qed.
Lemma lem19643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19644 (b : Prop) (c : Prop) : (term27 b c) = (term28 b c).
Proof. exact (MK_COMB (@lem19643) (@lem19642 b c)). Qed.
Lemma lem19645 (b : Prop) : (True = (term26 b)) = (True = (term26 b)).
Proof. exact (eq_refl (True = (term26 b))). Qed.
Lemma lem19646 (c : Prop) (b : Prop) : ((term24 b c) = (True = (term26 b))) = ((c = (term22 b c)) = (True = (term26 b))).
Proof. exact (MK_COMB (@lem19644 b c) (@lem19645 b)). Qed.
Lemma lem19647 (c : Prop) (b : Prop) : ((term24 b c) = (term25 b)) = ((c = (term22 b c)) = (True = (term26 b))).
Proof. exact (TRANS (@lem19641 c b) (@lem19646 c b)). Qed.
Lemma lem19648 (b : Prop) (c : Prop) (h1 : c = True) : (c = (term22 b c)) = (True = (term26 b)).
Proof. exact (EQ_MP (@lem19647 c b) (@lem19638 b c h1)). Qed.
Lemma lem19649 (b : Prop) (c : Prop) (h1 : c = True) : (True = (term26 b)) = (c = (term22 b c)).
Proof. exact (SYM (@lem19648 b c h1)). Qed.
Lemma lem19650 (b : Prop) : (term23 b) = (term23 b).
Proof. exact (eq_refl (term23 b)). Qed.
Lemma lem19651 (b : Prop) (c : Prop) (h1 : c = False) : (term24 b c) = (term29 b).
Proof. exact (MK_COMB (@lem19650 b) (@lem19628 c h1)). Qed.
Lemma lem19652 (b : Prop) : (term29 b) = (False = (term30 b)).
Proof. exact (eq_refl (term29 b)). Qed.
Lemma lem19653 (b : Prop) (c : Prop) : (term27 b c) = (term27 b c).
Proof. exact (eq_refl (term27 b c)). Qed.
Lemma lem19654 (c : Prop) (b : Prop) : ((term24 b c) = (term29 b)) = ((term24 b c) = (False = (term30 b))).
Proof. exact (MK_COMB (@lem19653 b c) (@lem19652 b)). Qed.
Lemma lem19655 (b : Prop) (c : Prop) : (term24 b c) = (c = (term22 b c)).
Proof. exact (eq_refl (term24 b c)). Qed.
Lemma lem19656 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19657 (b : Prop) (c : Prop) : (term27 b c) = (term28 b c).
Proof. exact (MK_COMB (@lem19656) (@lem19655 b c)). Qed.
Lemma lem19658 (b : Prop) : (False = (term30 b)) = (False = (term30 b)).
Proof. exact (eq_refl (False = (term30 b))). Qed.
Lemma lem19659 (c : Prop) (b : Prop) : ((term24 b c) = (False = (term30 b))) = ((c = (term22 b c)) = (False = (term30 b))).
Proof. exact (MK_COMB (@lem19657 b c) (@lem19658 b)). Qed.
Lemma lem19660 (c : Prop) (b : Prop) : ((term24 b c) = (term29 b)) = ((c = (term22 b c)) = (False = (term30 b))).
Proof. exact (TRANS (@lem19654 c b) (@lem19659 c b)). Qed.
Lemma lem19661 (b : Prop) (c : Prop) (h1 : c = False) : (c = (term22 b c)) = (False = (term30 b)).
Proof. exact (EQ_MP (@lem19660 c b) (@lem19651 b c h1)). Qed.
Lemma lem19662 (b : Prop) (c : Prop) (h1 : c = False) : (False = (term30 b)) = (c = (term22 b c)).
Proof. exact (SYM (@lem19661 b c h1)). Qed.
Lemma lem19664 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem19665 (b : Prop) : (True = (term26 b)) = (term26 b).
Proof. exact (@lem19664 (term26 b)). Qed.
Lemma lem19667 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem19668 (b : Prop) : (term26 b) = (b \/ True).
Proof. exact (@lem19667 (b \/ True)). Qed.
Lemma lem19670 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem19671 (b : Prop) : (b \/ True) = True.
Proof. exact (@lem19670 b). Qed.
Lemma lem19672 (b : Prop) : (term26 b) = True.
Proof. exact (TRANS (@lem19668 b) (@lem19671 b)). Qed.
Lemma lem19673 (b : Prop) : (True = (term26 b)) = True.
Proof. exact (TRANS (@lem19665 b) (@lem19672 b)). Qed.
Lemma lem19674 (b : Prop) : True = (True = (term26 b)).
Proof. exact (SYM (@lem19673 b)). Qed.
Lemma lem19675 (b : Prop) : True = (term26 b).
Proof. exact (EQ_MP (@lem19674 b) (@lem0)). Qed.
Lemma lem19677 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem19678 (b : Prop) : (False = (term30 b)) = (term31 b).
Proof. exact (@lem19677 (term30 b)). Qed.
Lemma lem19680 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem19681 (b : Prop) : (term30 b) = False.
Proof. exact (@lem19680 (b \/ False)). Qed.
Lemma lem19682 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem19683 (b : Prop) : (term31 b) = (~ False).
Proof. exact (MK_COMB (@lem19682) (@lem19681 b)). Qed.
Lemma lem19685 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem19686 (b : Prop) : (term31 b) = True.
Proof. exact (TRANS (@lem19683 b) (@lem19685)). Qed.
Lemma lem19687 (b : Prop) : (False = (term30 b)) = True.
Proof. exact (TRANS (@lem19678 b) (@lem19686 b)). Qed.
Lemma lem19688 (b : Prop) : True = (False = (term30 b)).
Proof. exact (SYM (@lem19687 b)). Qed.
Lemma lem19689 (b : Prop) : False = (term30 b).
Proof. exact (EQ_MP (@lem19688 b) (@lem0)). Qed.
Lemma lem19690 (b : Prop) (c : Prop) (h1 : c = False) : c = (term22 b c).
Proof. exact (EQ_MP (@lem19662 b c h1) (@lem19689 b)). Qed.
Lemma lem19691 (b : Prop) (c : Prop) (h1 : c = True) : c = (term22 b c).
Proof. exact (EQ_MP (@lem19649 b c h1) (@lem19675 b)). Qed.
Lemma lem19693 (b : Prop) (c : Prop) : c = (term22 b c).
Proof. exact (or_elim (@lem19626 c) (fun h0 : c = True => @lem19691 b c h0) (fun h0 : c = False => @lem19690 b c h0)). Qed.
Lemma lem19694 (b : Prop) (c : Prop) : (term12 b c) = (term13 b c).
Proof. exact (EQ_MP (@lem19623 b c) (@lem19693 b c)). Qed.
Lemma lem19695 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term8 a b c) = (term9 a b c).
Proof. exact (EQ_MP (@lem19549 b c a h1) (@lem19694 b c)). Qed.
Lemma lem19696 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term8 a b c) = (term9 a b c).
Proof. exact (EQ_MP (@lem19536 b c a h1) (@lem19589 b c)). Qed.
Lemma lem19699 (a : Prop) (b : Prop) (c : Prop) : (term8 a b c) = (term9 a b c).
Proof. exact (or_elim (@lem19507 a) (fun h0 : a = True => @lem19696 b c a h0) (fun h0 : a = False => @lem19695 b c a h0)). Qed.
