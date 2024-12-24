Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_EMPTY_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3235675 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3235676 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3235675 A s t). Qed.
Lemma lem3235677 {A : Type'} (s : A -> Prop) : ((@UNION A (@EMPTY A) s) = s) = (term1 A s).
Proof. exact (@lem3235676 A (@UNION A (@EMPTY A) s) s). Qed.
Lemma lem3235686 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3235677 A s)). Qed.
Lemma lem3235687 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3235688 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem3235687 A) (@lem3235686 A)). Qed.
Lemma lem3235693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3235694 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem3235693) (@lem3235688 A)). Qed.
Lemma lem3235702 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3235703 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3235702 A s t). Qed.
Lemma lem3235704 {A : Type'} (s : A -> Prop) : ((@UNION A s (@EMPTY A)) = s) = (term8 A s).
Proof. exact (@lem3235703 A (@UNION A s (@EMPTY A)) s). Qed.
Lemma lem3235713 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3235704 A s)). Qed.
Lemma lem3235714 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3235715 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem3235714 A) (@lem3235713 A)). Qed.
Lemma lem3235720 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (MK_COMB (@lem3235694 A) (@lem3235715 A)). Qed.
Lemma lem3235723 {A : Type'} : (term14 A) = (term13 A).
Proof. exact (SYM (@lem3235720 A)). Qed.
Lemma lem3235737 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3235738 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (@lem3235737 A s x t). Qed.
Lemma lem3235739 {A : Type'} (x : A) (s : A -> Prop) : (term17 A x s) = (term18 A x s).
Proof. exact (@lem3235738 A (@EMPTY A) x s). Qed.
Lemma lem3235743 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3235744 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3235743 A x). Qed.
Lemma lem3235745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3235746 {A : Type'} (x : A) : (term19 A x) = (or False).
Proof. exact (MK_COMB (@lem3235745) (@lem3235744 A x)). Qed.
Lemma lem3235748 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3235749 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3235748 A P x). Qed.
Lemma lem3235750 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3235749 A s x). Qed.
Lemma lem3235751 {A : Type'} (s : A -> Prop) (x : A) : (term18 A x s) = (term20 A s x).
Proof. exact (MK_COMB (@lem3235746 A x) (@lem3235750 A s x)). Qed.
Lemma lem3235753 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem3235754 {A : Type'} (s : A -> Prop) (x : A) : (term20 A s x) = (s x).
Proof. exact (@lem3235753 (s x)). Qed.
Lemma lem3235755 {A : Type'} (s : A -> Prop) (x : A) : (term18 A x s) = (s x).
Proof. exact (TRANS (@lem3235751 A s x) (@lem3235754 A s x)). Qed.
Lemma lem3235756 {A : Type'} (s : A -> Prop) (x : A) : (term17 A x s) = (s x).
Proof. exact (TRANS (@lem3235739 A x s) (@lem3235755 A s x)). Qed.
Lemma lem3235757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3235758 {A : Type'} (s : A -> Prop) (x : A) : (term21 A x s) = (term22 A s x).
Proof. exact (MK_COMB (@lem3235757) (@lem3235756 A s x)). Qed.
Lemma lem3235760 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3235761 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3235760 A P x). Qed.
Lemma lem3235762 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3235761 A s x). Qed.
Lemma lem3235763 {A : Type'} (s : A -> Prop) (x : A) : ((term17 A x s) = (@IN A x s)) = ((s x) = (s x)).
Proof. exact (MK_COMB (@lem3235758 A s x) (@lem3235762 A s x)). Qed.
Lemma lem3235765 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3235766 (x : Prop) : (x = x) = True.
Proof. exact (@lem3235765 Prop x). Qed.
Lemma lem3235767 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = (s x)) = True.
Proof. exact (@lem3235766 (s x)). Qed.
Lemma lem3235768 {A : Type'} (x : A) (s : A -> Prop) : ((term17 A x s) = (@IN A x s)) = True.
Proof. exact (TRANS (@lem3235763 A s x) (@lem3235767 A s x)). Qed.
Lemma lem3235769 {A : Type'} (s : A -> Prop) : (term23 A s) = (term24 A).
Proof. exact (fun_ext (fun x : A => @lem3235768 A x s)). Qed.
Lemma lem3235770 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3235771 {A : Type'} (s : A -> Prop) : (term1 A s) = (term25 A).
Proof. exact (MK_COMB (@lem3235770 A) (@lem3235769 A s)). Qed.
Lemma lem3235773 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3235774 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (@lem3235773 A t). Qed.
Lemma lem3235775 {A : Type'} : (term25 A) = True.
Proof. exact (@lem3235774 A True). Qed.
Lemma lem3235776 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (TRANS (@lem3235771 A s) (@lem3235775 A)). Qed.
Lemma lem3235777 {A : Type'} : (term3 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3235776 A s)). Qed.
Lemma lem3235778 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3235779 {A : Type'} : (term5 A) = (term28 A).
Proof. exact (MK_COMB (@lem3235778 A) (@lem3235777 A)). Qed.
Lemma lem3235781 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3235782 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (@lem3235781 (A -> Prop) t). Qed.
Lemma lem3235783 {A : Type'} : (term28 A) = True.
Proof. exact (@lem3235782 A True). Qed.
Lemma lem3235784 {A : Type'} : (term5 A) = True.
Proof. exact (TRANS (@lem3235779 A) (@lem3235783 A)). Qed.
Lemma lem3235785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3235786 {A : Type'} : (term7 A) = (and True).
Proof. exact (MK_COMB (@lem3235785) (@lem3235784 A)). Qed.
Lemma lem3235798 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3235799 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (@lem3235798 A s x t). Qed.
Lemma lem3235800 {A : Type'} (s : A -> Prop) (x : A) : (term30 A x s) = (term31 A s x).
Proof. exact (@lem3235799 A s x (@EMPTY A)). Qed.
Lemma lem3235804 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3235805 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3235804 A P x). Qed.
Lemma lem3235806 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3235805 A s x). Qed.
Lemma lem3235807 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3235808 {A : Type'} (s : A -> Prop) (x : A) : (term32 A x s) = (term33 A s x).
Proof. exact (MK_COMB (@lem3235807) (@lem3235806 A s x)). Qed.
Lemma lem3235810 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3235811 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3235810 A x). Qed.
Lemma lem3235812 {A : Type'} (s : A -> Prop) (x : A) : (term31 A s x) = (term34 A s x).
Proof. exact (MK_COMB (@lem3235808 A s x) (@lem3235811 A x)). Qed.
Lemma lem3235814 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3235815 {A : Type'} (s : A -> Prop) (x : A) : (term34 A s x) = (s x).
Proof. exact (@lem3235814 (s x)). Qed.
Lemma lem3235816 {A : Type'} (s : A -> Prop) (x : A) : (term31 A s x) = (s x).
Proof. exact (TRANS (@lem3235812 A s x) (@lem3235815 A s x)). Qed.
Lemma lem3235817 {A : Type'} (s : A -> Prop) (x : A) : (term30 A x s) = (s x).
Proof. exact (TRANS (@lem3235800 A s x) (@lem3235816 A s x)). Qed.
Lemma lem3235818 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3235819 {A : Type'} (s : A -> Prop) (x : A) : (term35 A x s) = (term22 A s x).
Proof. exact (MK_COMB (@lem3235818) (@lem3235817 A s x)). Qed.
Lemma lem3235821 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3235822 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3235821 A P x). Qed.
Lemma lem3235823 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3235822 A s x). Qed.
Lemma lem3235824 {A : Type'} (s : A -> Prop) (x : A) : ((term30 A x s) = (@IN A x s)) = ((s x) = (s x)).
Proof. exact (MK_COMB (@lem3235819 A s x) (@lem3235823 A s x)). Qed.
Lemma lem3235826 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3235827 (x : Prop) : (x = x) = True.
Proof. exact (@lem3235826 Prop x). Qed.
Lemma lem3235828 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = (s x)) = True.
Proof. exact (@lem3235827 (s x)). Qed.
Lemma lem3235829 {A : Type'} (x : A) (s : A -> Prop) : ((term30 A x s) = (@IN A x s)) = True.
Proof. exact (TRANS (@lem3235824 A s x) (@lem3235828 A s x)). Qed.
Lemma lem3235830 {A : Type'} (s : A -> Prop) : (term36 A s) = (term24 A).
Proof. exact (fun_ext (fun x : A => @lem3235829 A x s)). Qed.
Lemma lem3235831 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3235832 {A : Type'} (s : A -> Prop) : (term8 A s) = (term25 A).
Proof. exact (MK_COMB (@lem3235831 A) (@lem3235830 A s)). Qed.
Lemma lem3235834 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3235835 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (@lem3235834 A t). Qed.
Lemma lem3235836 {A : Type'} : (term25 A) = True.
Proof. exact (@lem3235835 A True). Qed.
Lemma lem3235837 {A : Type'} (s : A -> Prop) : (term8 A s) = True.
Proof. exact (TRANS (@lem3235832 A s) (@lem3235836 A)). Qed.
Lemma lem3235838 {A : Type'} : (term10 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3235837 A s)). Qed.
Lemma lem3235839 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3235840 {A : Type'} : (term12 A) = (term28 A).
Proof. exact (MK_COMB (@lem3235839 A) (@lem3235838 A)). Qed.
Lemma lem3235842 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3235843 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (@lem3235842 (A -> Prop) t). Qed.
Lemma lem3235844 {A : Type'} : (term28 A) = True.
Proof. exact (@lem3235843 A True). Qed.
Lemma lem3235845 {A : Type'} : (term12 A) = True.
Proof. exact (TRANS (@lem3235840 A) (@lem3235844 A)). Qed.
Lemma lem3235846 {A : Type'} : (term14 A) = (True /\ True).
Proof. exact (MK_COMB (@lem3235786 A) (@lem3235845 A)). Qed.
Lemma lem3235848 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3235849 : (True /\ True) = True.
Proof. exact (@lem3235848 True). Qed.
Lemma lem3235850 {A : Type'} : (term14 A) = True.
Proof. exact (TRANS (@lem3235846 A) (@lem3235849)). Qed.
Lemma lem3235851 {A : Type'} : True = (term14 A).
Proof. exact (SYM (@lem3235850 A)). Qed.
Lemma lem3235852 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3235851 A) (@lem0)). Qed.
Lemma lem3235853 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem3235723 A) (@lem3235852 A)). Qed.
