Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_NOT_THM_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem10661 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem10662 {A : Type'} (P : A -> Prop) : (term0 A P) = ((term1 A P) = (term2 A P)).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem10672 (a : Prop) : term3 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem10673 (a : Prop) : (term3 a) = (term4 a).
Proof. exact (eq_refl (term3 a)). Qed.
Lemma lem10674 (a : Prop) : term4 a.
Proof. exact (EQ_MP (@lem10673 a) (@lem10672 a)). Qed.
Lemma lem10675 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem10676 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem10685 (b : Prop) : (term5 b) = (term5 b).
Proof. exact (eq_refl (term5 b)). Qed.
Lemma lem10686 (b : Prop) (a : Prop) (h1 : a = True) : (term6 b a) = (term7 b).
Proof. exact (MK_COMB (@lem10685 b) (@lem10675 a h1)). Qed.
Lemma lem10687 (b : Prop) : (term7 b) = ((True = (~ b)) = ((~ True) = b)).
Proof. exact (eq_refl (term7 b)). Qed.
Lemma lem10688 (b : Prop) (a : Prop) : (term8 b a) = (term8 b a).
Proof. exact (eq_refl (term8 b a)). Qed.
Lemma lem10689 (a : Prop) (b : Prop) : ((term6 b a) = (term7 b)) = ((term6 b a) = ((True = (~ b)) = ((~ True) = b))).
Proof. exact (MK_COMB (@lem10688 b a) (@lem10687 b)). Qed.
Lemma lem10690 (a : Prop) (b : Prop) : (term6 b a) = ((a = (~ b)) = ((~ a) = b)).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem10691 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10692 (a : Prop) (b : Prop) : (term8 b a) = (term9 a b).
Proof. exact (MK_COMB (@lem10691) (@lem10690 a b)). Qed.
Lemma lem10693 (b : Prop) : ((True = (~ b)) = ((~ True) = b)) = ((True = (~ b)) = ((~ True) = b)).
Proof. exact (eq_refl ((True = (~ b)) = ((~ True) = b))). Qed.
Lemma lem10694 (a : Prop) (b : Prop) : ((term6 b a) = ((True = (~ b)) = ((~ True) = b))) = (((a = (~ b)) = ((~ a) = b)) = ((True = (~ b)) = ((~ True) = b))).
Proof. exact (MK_COMB (@lem10692 a b) (@lem10693 b)). Qed.
Lemma lem10695 (a : Prop) (b : Prop) : ((term6 b a) = (term7 b)) = (((a = (~ b)) = ((~ a) = b)) = ((True = (~ b)) = ((~ True) = b))).
Proof. exact (TRANS (@lem10689 a b) (@lem10694 a b)). Qed.
Lemma lem10696 (b : Prop) (a : Prop) (h1 : a = True) : ((a = (~ b)) = ((~ a) = b)) = ((True = (~ b)) = ((~ True) = b)).
Proof. exact (EQ_MP (@lem10695 a b) (@lem10686 b a h1)). Qed.
Lemma lem10697 (b : Prop) (a : Prop) (h1 : a = True) : ((True = (~ b)) = ((~ True) = b)) = ((a = (~ b)) = ((~ a) = b)).
Proof. exact (SYM (@lem10696 b a h1)). Qed.
Lemma lem10698 (b : Prop) : (term5 b) = (term5 b).
Proof. exact (eq_refl (term5 b)). Qed.
Lemma lem10699 (b : Prop) (a : Prop) (h1 : a = False) : (term6 b a) = (term10 b).
Proof. exact (MK_COMB (@lem10698 b) (@lem10676 a h1)). Qed.
Lemma lem10700 (b : Prop) : (term10 b) = ((False = (~ b)) = ((~ False) = b)).
Proof. exact (eq_refl (term10 b)). Qed.
Lemma lem10701 (b : Prop) (a : Prop) : (term8 b a) = (term8 b a).
Proof. exact (eq_refl (term8 b a)). Qed.
Lemma lem10702 (a : Prop) (b : Prop) : ((term6 b a) = (term10 b)) = ((term6 b a) = ((False = (~ b)) = ((~ False) = b))).
Proof. exact (MK_COMB (@lem10701 b a) (@lem10700 b)). Qed.
Lemma lem10703 (a : Prop) (b : Prop) : (term6 b a) = ((a = (~ b)) = ((~ a) = b)).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem10704 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10705 (a : Prop) (b : Prop) : (term8 b a) = (term9 a b).
Proof. exact (MK_COMB (@lem10704) (@lem10703 a b)). Qed.
Lemma lem10706 (b : Prop) : ((False = (~ b)) = ((~ False) = b)) = ((False = (~ b)) = ((~ False) = b)).
Proof. exact (eq_refl ((False = (~ b)) = ((~ False) = b))). Qed.
Lemma lem10707 (a : Prop) (b : Prop) : ((term6 b a) = ((False = (~ b)) = ((~ False) = b))) = (((a = (~ b)) = ((~ a) = b)) = ((False = (~ b)) = ((~ False) = b))).
Proof. exact (MK_COMB (@lem10705 a b) (@lem10706 b)). Qed.
Lemma lem10708 (a : Prop) (b : Prop) : ((term6 b a) = (term10 b)) = (((a = (~ b)) = ((~ a) = b)) = ((False = (~ b)) = ((~ False) = b))).
Proof. exact (TRANS (@lem10702 a b) (@lem10707 a b)). Qed.
Lemma lem10709 (b : Prop) (a : Prop) (h1 : a = False) : ((a = (~ b)) = ((~ a) = b)) = ((False = (~ b)) = ((~ False) = b)).
Proof. exact (EQ_MP (@lem10708 a b) (@lem10699 b a h1)). Qed.
Lemma lem10710 (b : Prop) (a : Prop) (h1 : a = False) : ((False = (~ b)) = ((~ False) = b)) = ((a = (~ b)) = ((~ a) = b)).
Proof. exact (SYM (@lem10709 b a h1)). Qed.
Lemma lem10714 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem10715 (b : Prop) : (True = (~ b)) = (~ b).
Proof. exact (@lem10714 (~ b)). Qed.
Lemma lem10716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10717 (b : Prop) : (term11 b) = (term12 b).
Proof. exact (MK_COMB (@lem10716) (@lem10715 b)). Qed.
Lemma lem10721 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem10722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10723 : term13 = (@eq Prop False).
Proof. exact (MK_COMB (@lem10722) (@lem10721)). Qed.
Lemma lem10724 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem10725 (b : Prop) : ((~ True) = b) = (False = b).
Proof. exact (MK_COMB (@lem10723) (@lem10724 b)). Qed.
Lemma lem10727 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem10728 (b : Prop) : (False = b) = (~ b).
Proof. exact (@lem10727 b). Qed.
Lemma lem10729 (b : Prop) : ((~ True) = b) = (~ b).
Proof. exact (TRANS (@lem10725 b) (@lem10728 b)). Qed.
Lemma lem10730 (b : Prop) : ((True = (~ b)) = ((~ True) = b)) = ((~ b) = (~ b)).
Proof. exact (MK_COMB (@lem10717 b) (@lem10729 b)). Qed.
Lemma lem10732 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem10733 (x : Prop) : (x = x) = True.
Proof. exact (@lem10732 Prop x). Qed.
Lemma lem10734 (b : Prop) : ((~ b) = (~ b)) = True.
Proof. exact (@lem10733 (~ b)). Qed.
Lemma lem10735 (b : Prop) : ((True = (~ b)) = ((~ True) = b)) = True.
Proof. exact (TRANS (@lem10730 b) (@lem10734 b)). Qed.
Lemma lem10736 (b : Prop) : True = ((True = (~ b)) = ((~ True) = b)).
Proof. exact (SYM (@lem10735 b)). Qed.
Lemma lem10737 (b : Prop) : (True = (~ b)) = ((~ True) = b).
Proof. exact (EQ_MP (@lem10736 b) (@lem0)). Qed.
Lemma lem10741 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem10742 (b : Prop) : (False = (~ b)) = (term14 b).
Proof. exact (@lem10741 (~ b)). Qed.
Lemma lem10743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10744 (b : Prop) : (term15 b) = (term16 b).
Proof. exact (MK_COMB (@lem10743) (@lem10742 b)). Qed.
Lemma lem10748 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem10749 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10750 : term17 = (@eq Prop True).
Proof. exact (MK_COMB (@lem10749) (@lem10748)). Qed.
Lemma lem10751 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem10752 (b : Prop) : ((~ False) = b) = (True = b).
Proof. exact (MK_COMB (@lem10750) (@lem10751 b)). Qed.
Lemma lem10754 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem10755 (b : Prop) : (True = b) = b.
Proof. exact (@lem10754 b). Qed.
Lemma lem10756 (b : Prop) : ((~ False) = b) = b.
Proof. exact (TRANS (@lem10752 b) (@lem10755 b)). Qed.
Lemma lem10757 (b : Prop) : ((False = (~ b)) = ((~ False) = b)) = ((term14 b) = b).
Proof. exact (MK_COMB (@lem10744 b) (@lem10756 b)). Qed.
Lemma lem10760 (b : Prop) : ((term14 b) = b) = ((False = (~ b)) = ((~ False) = b)).
Proof. exact (SYM (@lem10757 b)). Qed.
Lemma lem10769 (t : Prop) : (term14 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem10770 (b : Prop) : (term14 b) = b.
Proof. exact (@lem10769 b). Qed.
Lemma lem10771 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10772 (b : Prop) : (term16 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem10771) (@lem10770 b)). Qed.
Lemma lem10773 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem10774 (b : Prop) : ((term14 b) = b) = (b = b).
Proof. exact (MK_COMB (@lem10772 b) (@lem10773 b)). Qed.
Lemma lem10776 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem10777 (x : Prop) : (x = x) = True.
Proof. exact (@lem10776 Prop x). Qed.
Lemma lem10778 (b : Prop) : (b = b) = True.
Proof. exact (@lem10777 b). Qed.
Lemma lem10779 (b : Prop) : ((term14 b) = b) = True.
Proof. exact (TRANS (@lem10774 b) (@lem10778 b)). Qed.
Lemma lem10780 (b : Prop) : True = ((term14 b) = b).
Proof. exact (SYM (@lem10779 b)). Qed.
Lemma lem10781 (b : Prop) : (term14 b) = b.
Proof. exact (EQ_MP (@lem10780 b) (@lem0)). Qed.
Lemma lem10782 (b : Prop) : (False = (~ b)) = ((~ False) = b).
Proof. exact (EQ_MP (@lem10760 b) (@lem10781 b)). Qed.
Lemma lem10783 (b : Prop) (a : Prop) (h1 : a = False) : (a = (~ b)) = ((~ a) = b).
Proof. exact (EQ_MP (@lem10710 b a h1) (@lem10782 b)). Qed.
Lemma lem10784 (b : Prop) (a : Prop) (h1 : a = True) : (a = (~ b)) = ((~ a) = b).
Proof. exact (EQ_MP (@lem10697 b a h1) (@lem10737 b)). Qed.
Lemma lem10793 (a : Prop) (b : Prop) : (a = (~ b)) = ((~ a) = b).
Proof. exact (or_elim (@lem10674 a) (fun h0 : a = True => @lem10784 b a h0) (fun h0 : a = False => @lem10783 b a h0)). Qed.
Lemma lem10794 {A : Type'} (P : A -> Prop) : ((term18 A P) = (term19 A P)) = ((term20 A P) = (term21 A P)).
Proof. exact (@lem10793 (term18 A P) (term21 A P)). Qed.
Lemma lem10795 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem10794 A P)). Qed.
Lemma lem10796 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem10797 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (MK_COMB (@lem10796 A) (@lem10795 A)). Qed.
Lemma lem10798 {A : Type'} : (term25 A) = (term24 A).
Proof. exact (SYM (@lem10797 A)). Qed.
Lemma lem10806 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (EQ_MP (@lem10662 A P) (@lem10661 A P)). Qed.
Lemma lem10807 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (@lem10806 A P). Qed.
Lemma lem10808 {A : Type'} (P : A -> Prop) : (term26 A P) = (term27 A P).
Proof. exact (@lem10807 A (term28 A P)). Qed.
Lemma lem10809 {A : Type'} (P : A -> Prop) (x : A) : (term29 A P x) = (term30 A P x).
Proof. exact (eq_refl (term29 A P x)). Qed.
Lemma lem10810 {A : Type'} (P : A -> Prop) : (term31 A P) = (term28 A P).
Proof. exact (fun_ext (fun x : A => @lem10809 A P x)). Qed.
Lemma lem10811 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem10812 {A : Type'} (P : A -> Prop) : (term32 A P) = (term18 A P).
Proof. exact (MK_COMB (@lem10811 A) (@lem10810 A P)). Qed.
Lemma lem10813 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem10814 {A : Type'} (P : A -> Prop) : (term26 A P) = (term20 A P).
Proof. exact (MK_COMB (@lem10813) (@lem10812 A P)). Qed.
Lemma lem10815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10816 {A : Type'} (P : A -> Prop) : (term33 A P) = (term34 A P).
Proof. exact (MK_COMB (@lem10815) (@lem10814 A P)). Qed.
Lemma lem10817 {A : Type'} (P : A -> Prop) (x : A) : (term29 A P x) = (term30 A P x).
Proof. exact (eq_refl (term29 A P x)). Qed.
Lemma lem10818 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem10819 {A : Type'} (P : A -> Prop) (x : A) : (term35 A P x) = (term36 A P x).
Proof. exact (MK_COMB (@lem10818) (@lem10817 A P x)). Qed.
Lemma lem10820 {A : Type'} (P : A -> Prop) : (term37 A P) = (term38 A P).
Proof. exact (fun_ext (fun x : A => @lem10819 A P x)). Qed.
Lemma lem10821 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem10822 {A : Type'} (P : A -> Prop) : (term27 A P) = (term39 A P).
Proof. exact (MK_COMB (@lem10821 A) (@lem10820 A P)). Qed.
Lemma lem10823 {A : Type'} (P : A -> Prop) : ((term26 A P) = (term27 A P)) = ((term20 A P) = (term39 A P)).
Proof. exact (MK_COMB (@lem10816 A P) (@lem10822 A P)). Qed.
Lemma lem10824 {A : Type'} (P : A -> Prop) : (term20 A P) = (term39 A P).
Proof. exact (EQ_MP (@lem10823 A P) (@lem10808 A P)). Qed.
Lemma lem10830 (t : Prop) : (term14 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem10831 {A : Type'} (P : A -> Prop) (x : A) : (term36 A P x) = (P x).
Proof. exact (@lem10830 (P x)). Qed.
Lemma lem10832 {A : Type'} (P : A -> Prop) : (term38 A P) = (term40 A P).
Proof. exact (fun_ext (fun x : A => @lem10831 A P x)). Qed.
Lemma lem10833 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem10834 {A : Type'} (P : A -> Prop) : (term39 A P) = (term21 A P).
Proof. exact (MK_COMB (@lem10833 A) (@lem10832 A P)). Qed.
Lemma lem10839 {A : Type'} (P : A -> Prop) : (term20 A P) = (term21 A P).
Proof. exact (TRANS (@lem10824 A P) (@lem10834 A P)). Qed.
Lemma lem10840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10841 {A : Type'} (P : A -> Prop) : (term34 A P) = (term41 A P).
Proof. exact (MK_COMB (@lem10840) (@lem10839 A P)). Qed.
Lemma lem10846 {A : Type'} (P : A -> Prop) : (term21 A P) = (term21 A P).
Proof. exact (eq_refl (term21 A P)). Qed.
Lemma lem10847 {A : Type'} (P : A -> Prop) : ((term20 A P) = (term21 A P)) = ((term21 A P) = (term21 A P)).
Proof. exact (MK_COMB (@lem10841 A P) (@lem10846 A P)). Qed.
Lemma lem10849 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem10850 (x : Prop) : (x = x) = True.
Proof. exact (@lem10849 Prop x). Qed.
Lemma lem10851 {A : Type'} (P : A -> Prop) : ((term21 A P) = (term21 A P)) = True.
Proof. exact (@lem10850 (term21 A P)). Qed.
Lemma lem10852 {A : Type'} (P : A -> Prop) : ((term20 A P) = (term21 A P)) = True.
Proof. exact (TRANS (@lem10847 A P) (@lem10851 A P)). Qed.
Lemma lem10853 {A : Type'} : (term23 A) = (term42 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem10852 A P)). Qed.
Lemma lem10854 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem10855 {A : Type'} : (term25 A) = (term43 A).
Proof. exact (MK_COMB (@lem10854 A) (@lem10853 A)). Qed.
Lemma lem10857 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem10858 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (@lem10857 (A -> Prop) t). Qed.
Lemma lem10859 {A : Type'} : (term43 A) = True.
Proof. exact (@lem10858 A True). Qed.
Lemma lem10860 {A : Type'} : (term25 A) = True.
Proof. exact (TRANS (@lem10855 A) (@lem10859 A)). Qed.
Lemma lem10861 {A : Type'} : True = (term25 A).
Proof. exact (SYM (@lem10860 A)). Qed.
Lemma lem10862 {A : Type'} : term25 A.
Proof. exact (EQ_MP (@lem10861 A) (@lem0)). Qed.
Lemma lem10863 {A : Type'} : term24 A.
Proof. exact (EQ_MP (@lem10798 A) (@lem10862 A)). Qed.
