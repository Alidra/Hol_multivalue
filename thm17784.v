Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17784_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem17659 (p : Prop) : term0 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem17660 (p : Prop) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem17661 (p : Prop) : term1 p.
Proof. exact (EQ_MP (@lem17660 p) (@lem17659 p)). Qed.
Lemma lem17662 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem17663 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem17676 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem17677 (q : Prop) (p : Prop) (h1 : p = True) : (term3 q p) = (term4 q).
Proof. exact (MK_COMB (@lem17676 q) (@lem17662 p h1)). Qed.
Lemma lem17678 (q : Prop) : (term4 q) = ((True = q) = (term5 q)).
Proof. exact (eq_refl (term4 q)). Qed.
Lemma lem17679 (q : Prop) (p : Prop) : (term6 q p) = (term6 q p).
Proof. exact (eq_refl (term6 q p)). Qed.
Lemma lem17680 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = ((term3 q p) = ((True = q) = (term5 q))).
Proof. exact (MK_COMB (@lem17679 q p) (@lem17678 q)). Qed.
Lemma lem17681 (p : Prop) (q : Prop) : (term3 q p) = ((p = q) = (term7 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem17682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17683 (p : Prop) (q : Prop) : (term6 q p) = (term8 p q).
Proof. exact (MK_COMB (@lem17682) (@lem17681 p q)). Qed.
Lemma lem17684 (q : Prop) : ((True = q) = (term5 q)) = ((True = q) = (term5 q)).
Proof. exact (eq_refl ((True = q) = (term5 q))). Qed.
Lemma lem17685 (p : Prop) (q : Prop) : ((term3 q p) = ((True = q) = (term5 q))) = (((p = q) = (term7 p q)) = ((True = q) = (term5 q))).
Proof. exact (MK_COMB (@lem17683 p q) (@lem17684 q)). Qed.
Lemma lem17686 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = (((p = q) = (term7 p q)) = ((True = q) = (term5 q))).
Proof. exact (TRANS (@lem17680 p q) (@lem17685 p q)). Qed.
Lemma lem17687 (q : Prop) (p : Prop) (h1 : p = True) : ((p = q) = (term7 p q)) = ((True = q) = (term5 q)).
Proof. exact (EQ_MP (@lem17686 p q) (@lem17677 q p h1)). Qed.
Lemma lem17688 (q : Prop) (p : Prop) (h1 : p = True) : ((True = q) = (term5 q)) = ((p = q) = (term7 p q)).
Proof. exact (SYM (@lem17687 q p h1)). Qed.
Lemma lem17689 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem17690 (q : Prop) (p : Prop) (h1 : p = False) : (term3 q p) = (term9 q).
Proof. exact (MK_COMB (@lem17689 q) (@lem17663 p h1)). Qed.
Lemma lem17691 (q : Prop) : (term9 q) = ((False = q) = (term10 q)).
Proof. exact (eq_refl (term9 q)). Qed.
Lemma lem17692 (q : Prop) (p : Prop) : (term6 q p) = (term6 q p).
Proof. exact (eq_refl (term6 q p)). Qed.
Lemma lem17693 (p : Prop) (q : Prop) : ((term3 q p) = (term9 q)) = ((term3 q p) = ((False = q) = (term10 q))).
Proof. exact (MK_COMB (@lem17692 q p) (@lem17691 q)). Qed.
Lemma lem17694 (p : Prop) (q : Prop) : (term3 q p) = ((p = q) = (term7 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem17695 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17696 (p : Prop) (q : Prop) : (term6 q p) = (term8 p q).
Proof. exact (MK_COMB (@lem17695) (@lem17694 p q)). Qed.
Lemma lem17697 (q : Prop) : ((False = q) = (term10 q)) = ((False = q) = (term10 q)).
Proof. exact (eq_refl ((False = q) = (term10 q))). Qed.
Lemma lem17698 (p : Prop) (q : Prop) : ((term3 q p) = ((False = q) = (term10 q))) = (((p = q) = (term7 p q)) = ((False = q) = (term10 q))).
Proof. exact (MK_COMB (@lem17696 p q) (@lem17697 q)). Qed.
Lemma lem17699 (p : Prop) (q : Prop) : ((term3 q p) = (term9 q)) = (((p = q) = (term7 p q)) = ((False = q) = (term10 q))).
Proof. exact (TRANS (@lem17693 p q) (@lem17698 p q)). Qed.
Lemma lem17700 (q : Prop) (p : Prop) (h1 : p = False) : ((p = q) = (term7 p q)) = ((False = q) = (term10 q)).
Proof. exact (EQ_MP (@lem17699 p q) (@lem17690 q p h1)). Qed.
Lemma lem17701 (q : Prop) (p : Prop) (h1 : p = False) : ((False = q) = (term10 q)) = ((p = q) = (term7 p q)).
Proof. exact (SYM (@lem17700 q p h1)). Qed.
Lemma lem17705 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem17706 (q : Prop) : (True = q) = q.
Proof. exact (@lem17705 q). Qed.
Lemma lem17707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17708 (q : Prop) : (term11 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem17707) (@lem17706 q)). Qed.
Lemma lem17712 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem17713 (q : Prop) : (term12 q) = True.
Proof. exact (@lem17712 (~ q)). Qed.
Lemma lem17714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem17715 (q : Prop) : (term13 q) = (and True).
Proof. exact (MK_COMB (@lem17714) (@lem17713 q)). Qed.
Lemma lem17719 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem17720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem17721 : term14 = (or False).
Proof. exact (MK_COMB (@lem17720) (@lem17719)). Qed.
Lemma lem17722 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem17723 (q : Prop) : (term15 q) = (False \/ q).
Proof. exact (MK_COMB (@lem17721) (@lem17722 q)). Qed.
Lemma lem17725 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem17726 (q : Prop) : (False \/ q) = q.
Proof. exact (@lem17725 q). Qed.
Lemma lem17727 (q : Prop) : (term15 q) = q.
Proof. exact (TRANS (@lem17723 q) (@lem17726 q)). Qed.
Lemma lem17728 (q : Prop) : (term5 q) = (True /\ q).
Proof. exact (MK_COMB (@lem17715 q) (@lem17727 q)). Qed.
Lemma lem17730 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem17731 (q : Prop) : (True /\ q) = q.
Proof. exact (@lem17730 q). Qed.
Lemma lem17732 (q : Prop) : (term5 q) = q.
Proof. exact (TRANS (@lem17728 q) (@lem17731 q)). Qed.
Lemma lem17733 (q : Prop) : ((True = q) = (term5 q)) = (q = q).
Proof. exact (MK_COMB (@lem17708 q) (@lem17732 q)). Qed.
Lemma lem17735 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem17736 (x : Prop) : (x = x) = True.
Proof. exact (@lem17735 Prop x). Qed.
Lemma lem17737 (q : Prop) : (q = q) = True.
Proof. exact (@lem17736 q). Qed.
Lemma lem17738 (q : Prop) : ((True = q) = (term5 q)) = True.
Proof. exact (TRANS (@lem17733 q) (@lem17737 q)). Qed.
Lemma lem17739 (q : Prop) : True = ((True = q) = (term5 q)).
Proof. exact (SYM (@lem17738 q)). Qed.
Lemma lem17740 (q : Prop) : (True = q) = (term5 q).
Proof. exact (EQ_MP (@lem17739 q) (@lem0)). Qed.
Lemma lem17744 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem17745 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem17744 q). Qed.
Lemma lem17746 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17747 (q : Prop) : (term16 q) = (term17 q).
Proof. exact (MK_COMB (@lem17746) (@lem17745 q)). Qed.
Lemma lem17751 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem17752 (q : Prop) : (term18 q) = (~ q).
Proof. exact (@lem17751 (~ q)). Qed.
Lemma lem17753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem17754 (q : Prop) : (term19 q) = (term20 q).
Proof. exact (MK_COMB (@lem17753) (@lem17752 q)). Qed.
Lemma lem17758 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem17759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem17760 : term21 = (or True).
Proof. exact (MK_COMB (@lem17759) (@lem17758)). Qed.
Lemma lem17761 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem17762 (q : Prop) : (term22 q) = (True \/ q).
Proof. exact (MK_COMB (@lem17760) (@lem17761 q)). Qed.
Lemma lem17764 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem17765 (q : Prop) : (True \/ q) = True.
Proof. exact (@lem17764 q). Qed.
Lemma lem17766 (q : Prop) : (term22 q) = True.
Proof. exact (TRANS (@lem17762 q) (@lem17765 q)). Qed.
Lemma lem17767 (q : Prop) : (term10 q) = (term23 q).
Proof. exact (MK_COMB (@lem17754 q) (@lem17766 q)). Qed.
Lemma lem17769 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem17770 (q : Prop) : (term23 q) = (~ q).
Proof. exact (@lem17769 (~ q)). Qed.
Lemma lem17771 (q : Prop) : (term10 q) = (~ q).
Proof. exact (TRANS (@lem17767 q) (@lem17770 q)). Qed.
Lemma lem17772 (q : Prop) : ((False = q) = (term10 q)) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem17747 q) (@lem17771 q)). Qed.
Lemma lem17774 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem17775 (x : Prop) : (x = x) = True.
Proof. exact (@lem17774 Prop x). Qed.
Lemma lem17776 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem17775 (~ q)). Qed.
Lemma lem17777 (q : Prop) : ((False = q) = (term10 q)) = True.
Proof. exact (TRANS (@lem17772 q) (@lem17776 q)). Qed.
Lemma lem17778 (q : Prop) : True = ((False = q) = (term10 q)).
Proof. exact (SYM (@lem17777 q)). Qed.
Lemma lem17779 (q : Prop) : (False = q) = (term10 q).
Proof. exact (EQ_MP (@lem17778 q) (@lem0)). Qed.
Lemma lem17780 (q : Prop) (p : Prop) (h1 : p = False) : (p = q) = (term7 p q).
Proof. exact (EQ_MP (@lem17701 q p h1) (@lem17779 q)). Qed.
Lemma lem17781 (q : Prop) (p : Prop) (h1 : p = True) : (p = q) = (term7 p q).
Proof. exact (EQ_MP (@lem17688 q p h1) (@lem17740 q)). Qed.
Lemma lem17784 (p : Prop) (q : Prop) : (p = q) = (term7 p q).
Proof. exact (or_elim (@lem17661 p) (fun h0 : p = True => @lem17781 q p h0) (fun h0 : p = False => @lem17780 q p h0)). Qed.
