Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16799_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Lemma lem16693 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem16694 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem16695 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem16694 a) (@lem16693 a)). Qed.
Lemma lem16696 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem16697 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem16706 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem16707 (b : Prop) (a : Prop) (h1 : a = True) : (term3 b a) = (term4 b).
Proof. exact (MK_COMB (@lem16706 b) (@lem16696 a h1)). Qed.
Lemma lem16708 (b : Prop) : (term4 b) = (term5 b).
Proof. exact (eq_refl (term4 b)). Qed.
Lemma lem16709 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem16710 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term3 b a) = (term5 b)).
Proof. exact (MK_COMB (@lem16709 b a) (@lem16708 b)). Qed.
Lemma lem16711 (a : Prop) (b : Prop) : (term3 b a) = (term7 a b).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem16712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16713 (a : Prop) (b : Prop) : (term6 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem16712) (@lem16711 a b)). Qed.
Lemma lem16714 (b : Prop) : (term5 b) = (term5 b).
Proof. exact (eq_refl (term5 b)). Qed.
Lemma lem16715 (a : Prop) (b : Prop) : ((term3 b a) = (term5 b)) = ((term7 a b) = (term5 b)).
Proof. exact (MK_COMB (@lem16713 a b) (@lem16714 b)). Qed.
Lemma lem16716 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term7 a b) = (term5 b)).
Proof. exact (TRANS (@lem16710 a b) (@lem16715 a b)). Qed.
Lemma lem16717 (b : Prop) (a : Prop) (h1 : a = True) : (term7 a b) = (term5 b).
Proof. exact (EQ_MP (@lem16716 a b) (@lem16707 b a h1)). Qed.
Lemma lem16718 (b : Prop) (a : Prop) (h1 : a = True) : (term5 b) = (term7 a b).
Proof. exact (SYM (@lem16717 b a h1)). Qed.
Lemma lem16719 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem16720 (b : Prop) (a : Prop) (h1 : a = False) : (term3 b a) = (term9 b).
Proof. exact (MK_COMB (@lem16719 b) (@lem16697 a h1)). Qed.
Lemma lem16721 (b : Prop) : (term9 b) = (term10 b).
Proof. exact (eq_refl (term9 b)). Qed.
Lemma lem16722 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem16723 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = ((term3 b a) = (term10 b)).
Proof. exact (MK_COMB (@lem16722 b a) (@lem16721 b)). Qed.
Lemma lem16724 (a : Prop) (b : Prop) : (term3 b a) = (term7 a b).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem16725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16726 (a : Prop) (b : Prop) : (term6 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem16725) (@lem16724 a b)). Qed.
Lemma lem16727 (b : Prop) : (term10 b) = (term10 b).
Proof. exact (eq_refl (term10 b)). Qed.
Lemma lem16728 (a : Prop) (b : Prop) : ((term3 b a) = (term10 b)) = ((term7 a b) = (term10 b)).
Proof. exact (MK_COMB (@lem16726 a b) (@lem16727 b)). Qed.
Lemma lem16729 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = ((term7 a b) = (term10 b)).
Proof. exact (TRANS (@lem16723 a b) (@lem16728 a b)). Qed.
Lemma lem16730 (b : Prop) (a : Prop) (h1 : a = False) : (term7 a b) = (term10 b).
Proof. exact (EQ_MP (@lem16729 a b) (@lem16720 b a h1)). Qed.
Lemma lem16731 (b : Prop) (a : Prop) (h1 : a = False) : (term10 b) = (term7 a b).
Proof. exact (SYM (@lem16730 b a h1)). Qed.
Lemma lem16735 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem16736 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem16737 : term11 = (imp False).
Proof. exact (MK_COMB (@lem16736) (@lem16735)). Qed.
Lemma lem16741 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem16742 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem16741 b). Qed.
Lemma lem16743 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem16744 (b : Prop) : (term12 b) = (~ True).
Proof. exact (MK_COMB (@lem16743) (@lem16742 b)). Qed.
Lemma lem16746 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem16747 (b : Prop) : (term12 b) = False.
Proof. exact (TRANS (@lem16744 b) (@lem16746)). Qed.
Lemma lem16748 (b : Prop) : (term13 b) = (term13 b).
Proof. exact (eq_refl (term13 b)). Qed.
Lemma lem16749 (b : Prop) : (term14 b) = (term15 b).
Proof. exact (MK_COMB (@lem16748 b) (@lem16747 b)). Qed.
Lemma lem16751 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem16752 (b : Prop) : (term15 b) = (term16 b).
Proof. exact (@lem16751 (~ b)). Qed.
Lemma lem16754 (t : Prop) : (term16 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem16755 (b : Prop) : (term16 b) = b.
Proof. exact (@lem16754 b). Qed.
Lemma lem16756 (b : Prop) : (term15 b) = b.
Proof. exact (TRANS (@lem16752 b) (@lem16755 b)). Qed.
Lemma lem16757 (b : Prop) : (term14 b) = b.
Proof. exact (TRANS (@lem16749 b) (@lem16756 b)). Qed.
Lemma lem16758 (b : Prop) : (term5 b) = (False -> b).
Proof. exact (MK_COMB (@lem16737) (@lem16757 b)). Qed.
Lemma lem16760 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem16761 (b : Prop) : (False -> b) = True.
Proof. exact (@lem16760 b). Qed.
Lemma lem16762 (b : Prop) : (term5 b) = True.
Proof. exact (TRANS (@lem16758 b) (@lem16761 b)). Qed.
Lemma lem16763 (b : Prop) : True = (term5 b).
Proof. exact (SYM (@lem16762 b)). Qed.
Lemma lem16764 (b : Prop) : term5 b.
Proof. exact (EQ_MP (@lem16763 b) (@lem0)). Qed.
Lemma lem16768 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem16769 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem16770 : term17 = (imp True).
Proof. exact (MK_COMB (@lem16769) (@lem16768)). Qed.
Lemma lem16774 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem16775 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem16774 b). Qed.
Lemma lem16776 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem16777 (b : Prop) : (term18 b) = (~ b).
Proof. exact (MK_COMB (@lem16776) (@lem16775 b)). Qed.
Lemma lem16778 (b : Prop) : (term13 b) = (term13 b).
Proof. exact (eq_refl (term13 b)). Qed.
Lemma lem16779 (b : Prop) : (term19 b) = (term20 b).
Proof. exact (MK_COMB (@lem16778 b) (@lem16777 b)). Qed.
Lemma lem16781 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem16782 (b : Prop) : (term20 b) = True.
Proof. exact (@lem16781 (~ b)). Qed.
Lemma lem16783 (b : Prop) : (term19 b) = True.
Proof. exact (TRANS (@lem16779 b) (@lem16782 b)). Qed.
Lemma lem16784 (b : Prop) : (term10 b) = (True -> True).
Proof. exact (MK_COMB (@lem16770) (@lem16783 b)). Qed.
Lemma lem16786 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem16787 : (True -> True) = True.
Proof. exact (@lem16786 True). Qed.
Lemma lem16788 (b : Prop) : (term10 b) = True.
Proof. exact (TRANS (@lem16784 b) (@lem16787)). Qed.
Lemma lem16789 (b : Prop) : True = (term10 b).
Proof. exact (SYM (@lem16788 b)). Qed.
Lemma lem16790 (b : Prop) : term10 b.
Proof. exact (EQ_MP (@lem16789 b) (@lem0)). Qed.
Lemma lem16791 (b : Prop) (a : Prop) (h1 : a = False) : term7 a b.
Proof. exact (EQ_MP (@lem16731 b a h1) (@lem16790 b)). Qed.
Lemma lem16792 (b : Prop) (a : Prop) (h1 : a = True) : term7 a b.
Proof. exact (EQ_MP (@lem16718 b a h1) (@lem16764 b)). Qed.
Lemma lem16795 (a : Prop) (b : Prop) : term7 a b.
Proof. exact (or_elim (@lem16695 a) (fun h0 : a = True => @lem16792 b a h0) (fun h0 : a = False => @lem16791 b a h0)). Qed.
Lemma lem16796 (a : Prop) (h1 : ~ a) : ~ a.
Proof. exact (h1). Qed.
Lemma lem16797 (b : Prop) (a : Prop) (h1 : ~ a) : term21 a b.
Proof. exact (@lem16795 a b (@lem16796 a h1)). Qed.
Lemma lem16798 (b : Prop) (h1 : ~ b) : ~ b.
Proof. exact (h1). Qed.
Lemma lem16799 (a : Prop) (b : Prop) (h1 : ~ a) (h2 : ~ b) : term22 a b.
Proof. exact (@lem16797 b a h1 (@lem16798 b h2)). Qed.
