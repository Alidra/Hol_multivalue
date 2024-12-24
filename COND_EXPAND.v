Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import COND_EXPAND_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem12656 (b : Prop) : term0 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem12657 (b : Prop) : (term0 b) = (term1 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem12658 (b : Prop) : term1 b.
Proof. exact (EQ_MP (@lem12657 b) (@lem12656 b)). Qed.
Lemma lem12659 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem12660 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem12661 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term2 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem12662 (t1 : Prop) (t2 : Prop) (b : Prop) (h1 : b = True) : (term3 t1 t2 b) = (term4 t1 t2).
Proof. exact (MK_COMB (@lem12661 t1 t2) (@lem12659 b h1)). Qed.
Lemma lem12663 (t1 : Prop) (t2 : Prop) : (term4 t1 t2) = ((@COND Prop True t1 t2) = (term5 t1 t2)).
Proof. exact (eq_refl (term4 t1 t2)). Qed.
Lemma lem12664 (t1 : Prop) (t2 : Prop) (b : Prop) : (term6 t1 t2 b) = (term6 t1 t2 b).
Proof. exact (eq_refl (term6 t1 t2 b)). Qed.
Lemma lem12665 (b : Prop) (t1 : Prop) (t2 : Prop) : ((term3 t1 t2 b) = (term4 t1 t2)) = ((term3 t1 t2 b) = ((@COND Prop True t1 t2) = (term5 t1 t2))).
Proof. exact (MK_COMB (@lem12664 t1 t2 b) (@lem12663 t1 t2)). Qed.
Lemma lem12666 (t1 : Prop) (b : Prop) (t2 : Prop) : (term3 t1 t2 b) = ((@COND Prop b t1 t2) = (term7 t1 b t2)).
Proof. exact (eq_refl (term3 t1 t2 b)). Qed.
Lemma lem12667 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12668 (t1 : Prop) (b : Prop) (t2 : Prop) : (term6 t1 t2 b) = (term8 t1 b t2).
Proof. exact (MK_COMB (@lem12667) (@lem12666 t1 b t2)). Qed.
Lemma lem12669 (t1 : Prop) (t2 : Prop) : ((@COND Prop True t1 t2) = (term5 t1 t2)) = ((@COND Prop True t1 t2) = (term5 t1 t2)).
Proof. exact (eq_refl ((@COND Prop True t1 t2) = (term5 t1 t2))). Qed.
Lemma lem12670 (b : Prop) (t1 : Prop) (t2 : Prop) : ((term3 t1 t2 b) = ((@COND Prop True t1 t2) = (term5 t1 t2))) = (((@COND Prop b t1 t2) = (term7 t1 b t2)) = ((@COND Prop True t1 t2) = (term5 t1 t2))).
Proof. exact (MK_COMB (@lem12668 t1 b t2) (@lem12669 t1 t2)). Qed.
Lemma lem12671 (b : Prop) (t1 : Prop) (t2 : Prop) : ((term3 t1 t2 b) = (term4 t1 t2)) = (((@COND Prop b t1 t2) = (term7 t1 b t2)) = ((@COND Prop True t1 t2) = (term5 t1 t2))).
Proof. exact (TRANS (@lem12665 b t1 t2) (@lem12670 b t1 t2)). Qed.
Lemma lem12672 (t1 : Prop) (t2 : Prop) (b : Prop) (h1 : b = True) : ((@COND Prop b t1 t2) = (term7 t1 b t2)) = ((@COND Prop True t1 t2) = (term5 t1 t2)).
Proof. exact (EQ_MP (@lem12671 b t1 t2) (@lem12662 t1 t2 b h1)). Qed.
Lemma lem12673 (t1 : Prop) (t2 : Prop) (b : Prop) (h1 : b = True) : ((@COND Prop True t1 t2) = (term5 t1 t2)) = ((@COND Prop b t1 t2) = (term7 t1 b t2)).
Proof. exact (SYM (@lem12672 t1 t2 b h1)). Qed.
Lemma lem12674 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term2 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem12675 (t1 : Prop) (t2 : Prop) (b : Prop) (h1 : b = False) : (term3 t1 t2 b) = (term9 t1 t2).
Proof. exact (MK_COMB (@lem12674 t1 t2) (@lem12660 b h1)). Qed.
Lemma lem12676 (t1 : Prop) (t2 : Prop) : (term9 t1 t2) = ((@COND Prop False t1 t2) = (term10 t1 t2)).
Proof. exact (eq_refl (term9 t1 t2)). Qed.
Lemma lem12677 (t1 : Prop) (t2 : Prop) (b : Prop) : (term6 t1 t2 b) = (term6 t1 t2 b).
Proof. exact (eq_refl (term6 t1 t2 b)). Qed.
Lemma lem12678 (b : Prop) (t1 : Prop) (t2 : Prop) : ((term3 t1 t2 b) = (term9 t1 t2)) = ((term3 t1 t2 b) = ((@COND Prop False t1 t2) = (term10 t1 t2))).
Proof. exact (MK_COMB (@lem12677 t1 t2 b) (@lem12676 t1 t2)). Qed.
Lemma lem12679 (t1 : Prop) (b : Prop) (t2 : Prop) : (term3 t1 t2 b) = ((@COND Prop b t1 t2) = (term7 t1 b t2)).
Proof. exact (eq_refl (term3 t1 t2 b)). Qed.
Lemma lem12680 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12681 (t1 : Prop) (b : Prop) (t2 : Prop) : (term6 t1 t2 b) = (term8 t1 b t2).
Proof. exact (MK_COMB (@lem12680) (@lem12679 t1 b t2)). Qed.
Lemma lem12682 (t1 : Prop) (t2 : Prop) : ((@COND Prop False t1 t2) = (term10 t1 t2)) = ((@COND Prop False t1 t2) = (term10 t1 t2)).
Proof. exact (eq_refl ((@COND Prop False t1 t2) = (term10 t1 t2))). Qed.
Lemma lem12683 (b : Prop) (t1 : Prop) (t2 : Prop) : ((term3 t1 t2 b) = ((@COND Prop False t1 t2) = (term10 t1 t2))) = (((@COND Prop b t1 t2) = (term7 t1 b t2)) = ((@COND Prop False t1 t2) = (term10 t1 t2))).
Proof. exact (MK_COMB (@lem12681 t1 b t2) (@lem12682 t1 t2)). Qed.
Lemma lem12684 (b : Prop) (t1 : Prop) (t2 : Prop) : ((term3 t1 t2 b) = (term9 t1 t2)) = (((@COND Prop b t1 t2) = (term7 t1 b t2)) = ((@COND Prop False t1 t2) = (term10 t1 t2))).
Proof. exact (TRANS (@lem12678 b t1 t2) (@lem12683 b t1 t2)). Qed.
Lemma lem12685 (t1 : Prop) (t2 : Prop) (b : Prop) (h1 : b = False) : ((@COND Prop b t1 t2) = (term7 t1 b t2)) = ((@COND Prop False t1 t2) = (term10 t1 t2)).
Proof. exact (EQ_MP (@lem12684 b t1 t2) (@lem12675 t1 t2 b h1)). Qed.
Lemma lem12686 (t1 : Prop) (t2 : Prop) (b : Prop) (h1 : b = False) : ((@COND Prop False t1 t2) = (term10 t1 t2)) = ((@COND Prop b t1 t2) = (term7 t1 b t2)).
Proof. exact (SYM (@lem12685 t1 t2 b h1)). Qed.
Lemma lem12690 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem12691 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem12690 Prop t2 t1). Qed.
Lemma lem12692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12693 (t2 : Prop) (t1 : Prop) : (term11 t1 t2) = (@eq Prop t1).
Proof. exact (MK_COMB (@lem12692) (@lem12691 t2 t1)). Qed.
Lemma lem12699 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem12700 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem12701 : term12 = (or False).
Proof. exact (MK_COMB (@lem12700) (@lem12699)). Qed.
Lemma lem12702 (t1 : Prop) : t1 = t1.
Proof. exact (eq_refl t1). Qed.
Lemma lem12703 (t1 : Prop) : (term13 t1) = (False \/ t1).
Proof. exact (MK_COMB (@lem12701) (@lem12702 t1)). Qed.
Lemma lem12705 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem12706 (t1 : Prop) : (False \/ t1) = t1.
Proof. exact (@lem12705 t1). Qed.
Lemma lem12707 (t1 : Prop) : (term13 t1) = t1.
Proof. exact (TRANS (@lem12703 t1) (@lem12706 t1)). Qed.
Lemma lem12708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem12709 (t1 : Prop) : (term14 t1) = (and t1).
Proof. exact (MK_COMB (@lem12708) (@lem12707 t1)). Qed.
Lemma lem12711 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem12712 (t2 : Prop) : (True \/ t2) = True.
Proof. exact (@lem12711 t2). Qed.
Lemma lem12713 (t2 : Prop) (t1 : Prop) : (term5 t1 t2) = (t1 /\ True).
Proof. exact (MK_COMB (@lem12709 t1) (@lem12712 t2)). Qed.
Lemma lem12715 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem12716 (t1 : Prop) : (t1 /\ True) = t1.
Proof. exact (@lem12715 t1). Qed.
Lemma lem12717 (t2 : Prop) (t1 : Prop) : (term5 t1 t2) = t1.
Proof. exact (TRANS (@lem12713 t2 t1) (@lem12716 t1)). Qed.
Lemma lem12718 (t2 : Prop) (t1 : Prop) : ((@COND Prop True t1 t2) = (term5 t1 t2)) = (t1 = t1).
Proof. exact (MK_COMB (@lem12693 t2 t1) (@lem12717 t2 t1)). Qed.
Lemma lem12720 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem12721 (x : Prop) : (x = x) = True.
Proof. exact (@lem12720 Prop x). Qed.
Lemma lem12722 (t1 : Prop) : (t1 = t1) = True.
Proof. exact (@lem12721 t1). Qed.
Lemma lem12723 (t1 : Prop) (t2 : Prop) : ((@COND Prop True t1 t2) = (term5 t1 t2)) = True.
Proof. exact (TRANS (@lem12718 t2 t1) (@lem12722 t1)). Qed.
Lemma lem12724 (t1 : Prop) (t2 : Prop) : True = ((@COND Prop True t1 t2) = (term5 t1 t2)).
Proof. exact (SYM (@lem12723 t1 t2)). Qed.
Lemma lem12725 (t1 : Prop) (t2 : Prop) : (@COND Prop True t1 t2) = (term5 t1 t2).
Proof. exact (EQ_MP (@lem12724 t1 t2) (@lem0)). Qed.
Lemma lem12729 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem12730 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem12729 Prop t1 t2). Qed.
Lemma lem12731 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12732 (t1 : Prop) (t2 : Prop) : (term15 t1 t2) = (@eq Prop t2).
Proof. exact (MK_COMB (@lem12731) (@lem12730 t1 t2)). Qed.
Lemma lem12738 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem12739 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem12740 : term16 = (or True).
Proof. exact (MK_COMB (@lem12739) (@lem12738)). Qed.
Lemma lem12741 (t1 : Prop) : t1 = t1.
Proof. exact (eq_refl t1). Qed.
Lemma lem12742 (t1 : Prop) : (term17 t1) = (True \/ t1).
Proof. exact (MK_COMB (@lem12740) (@lem12741 t1)). Qed.
Lemma lem12744 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem12745 (t1 : Prop) : (True \/ t1) = True.
Proof. exact (@lem12744 t1). Qed.
Lemma lem12746 (t1 : Prop) : (term17 t1) = True.
Proof. exact (TRANS (@lem12742 t1) (@lem12745 t1)). Qed.
Lemma lem12747 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem12748 (t1 : Prop) : (term18 t1) = (and True).
Proof. exact (MK_COMB (@lem12747) (@lem12746 t1)). Qed.
Lemma lem12750 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem12751 (t2 : Prop) : (False \/ t2) = t2.
Proof. exact (@lem12750 t2). Qed.
Lemma lem12752 (t1 : Prop) (t2 : Prop) : (term10 t1 t2) = (True /\ t2).
Proof. exact (MK_COMB (@lem12748 t1) (@lem12751 t2)). Qed.
Lemma lem12754 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem12755 (t2 : Prop) : (True /\ t2) = t2.
Proof. exact (@lem12754 t2). Qed.
Lemma lem12756 (t1 : Prop) (t2 : Prop) : (term10 t1 t2) = t2.
Proof. exact (TRANS (@lem12752 t1 t2) (@lem12755 t2)). Qed.
Lemma lem12757 (t1 : Prop) (t2 : Prop) : ((@COND Prop False t1 t2) = (term10 t1 t2)) = (t2 = t2).
Proof. exact (MK_COMB (@lem12732 t1 t2) (@lem12756 t1 t2)). Qed.
Lemma lem12759 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem12760 (x : Prop) : (x = x) = True.
Proof. exact (@lem12759 Prop x). Qed.
Lemma lem12761 (t2 : Prop) : (t2 = t2) = True.
Proof. exact (@lem12760 t2). Qed.
Lemma lem12762 (t1 : Prop) (t2 : Prop) : ((@COND Prop False t1 t2) = (term10 t1 t2)) = True.
Proof. exact (TRANS (@lem12757 t1 t2) (@lem12761 t2)). Qed.
Lemma lem12763 (t1 : Prop) (t2 : Prop) : True = ((@COND Prop False t1 t2) = (term10 t1 t2)).
Proof. exact (SYM (@lem12762 t1 t2)). Qed.
Lemma lem12764 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = (term10 t1 t2).
Proof. exact (EQ_MP (@lem12763 t1 t2) (@lem0)). Qed.
Lemma lem12765 (t1 : Prop) (t2 : Prop) (b : Prop) (h1 : b = False) : (@COND Prop b t1 t2) = (term7 t1 b t2).
Proof. exact (EQ_MP (@lem12686 t1 t2 b h1) (@lem12764 t1 t2)). Qed.
Lemma lem12766 (t1 : Prop) (t2 : Prop) (b : Prop) (h1 : b = True) : (@COND Prop b t1 t2) = (term7 t1 b t2).
Proof. exact (EQ_MP (@lem12673 t1 t2 b h1) (@lem12725 t1 t2)). Qed.
Lemma lem12767 (t1 : Prop) (b : Prop) (t2 : Prop) : (@COND Prop b t1 t2) = (term7 t1 b t2).
Proof. exact (or_elim (@lem12658 b) (fun h0 : b = True => @lem12766 t1 t2 b h0) (fun h0 : b = False => @lem12765 t1 t2 b h0)). Qed.
Lemma lem12772 (t1 : Prop) (b : Prop) : term19 t1 b.
Proof. exact (fun t2 : Prop => @lem12767 t1 b t2). Qed.
Lemma lem12777 (b : Prop) : term20 b.
Proof. exact (fun t1 : Prop => @lem12772 t1 b). Qed.
Lemma lem12782 : term21.
Proof. exact (fun b : Prop => @lem12777 b). Qed.
