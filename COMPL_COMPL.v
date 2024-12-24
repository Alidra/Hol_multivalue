Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import COMPL_COMPL_term_abbrevs.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3270720 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3270721 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3270720 A s t). Qed.
Lemma lem3270722 {A : Type'} (s : A -> Prop) : ((term1 A s) = s) = (term2 A s).
Proof. exact (@lem3270721 A (term1 A s) s). Qed.
Lemma lem3270731 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3270722 A s)). Qed.
Lemma lem3270732 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3270733 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (MK_COMB (@lem3270732 A) (@lem3270731 A)). Qed.
Lemma lem3270738 {A : Type'} : (term6 A) = (term5 A).
Proof. exact (SYM (@lem3270733 A)). Qed.
Lemma lem3270750 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3270751 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (@lem3270750 A s x t). Qed.
Lemma lem3270752 {A : Type'} (x : A) (s : A -> Prop) : (term9 A x s) = (term10 A x s).
Proof. exact (@lem3270751 A (@UNIV A) x (@DIFF A (@UNIV A) s)). Qed.
Lemma lem3270756 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3270757 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3270756 A x). Qed.
Lemma lem3270758 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3270759 {A : Type'} (x : A) : (term11 A x) = (and True).
Proof. exact (MK_COMB (@lem3270758) (@lem3270757 A x)). Qed.
Lemma lem3270761 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3270762 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (@lem3270761 A s x t). Qed.
Lemma lem3270763 {A : Type'} (x : A) (s : A -> Prop) : (term12 A x s) = (term13 A x s).
Proof. exact (@lem3270762 A (@UNIV A) x s). Qed.
Lemma lem3270767 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3270768 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3270767 A x). Qed.
Lemma lem3270769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3270770 {A : Type'} (x : A) : (term11 A x) = (and True).
Proof. exact (MK_COMB (@lem3270769) (@lem3270768 A x)). Qed.
Lemma lem3270772 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3270773 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3270772 A P x). Qed.
Lemma lem3270774 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3270773 A s x). Qed.
Lemma lem3270775 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3270776 {A : Type'} (s : A -> Prop) (x : A) : (term14 A x s) = (term15 A s x).
Proof. exact (MK_COMB (@lem3270775) (@lem3270774 A s x)). Qed.
Lemma lem3270777 {A : Type'} (s : A -> Prop) (x : A) : (term13 A x s) = (term16 A s x).
Proof. exact (MK_COMB (@lem3270770 A x) (@lem3270776 A s x)). Qed.
Lemma lem3270779 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3270780 {A : Type'} (s : A -> Prop) (x : A) : (term16 A s x) = (term15 A s x).
Proof. exact (@lem3270779 (term15 A s x)). Qed.
Lemma lem3270781 {A : Type'} (s : A -> Prop) (x : A) : (term13 A x s) = (term15 A s x).
Proof. exact (TRANS (@lem3270777 A s x) (@lem3270780 A s x)). Qed.
Lemma lem3270782 {A : Type'} (s : A -> Prop) (x : A) : (term12 A x s) = (term15 A s x).
Proof. exact (TRANS (@lem3270763 A x s) (@lem3270781 A s x)). Qed.
Lemma lem3270783 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3270784 {A : Type'} (s : A -> Prop) (x : A) : (term17 A x s) = (term18 A s x).
Proof. exact (MK_COMB (@lem3270783) (@lem3270782 A s x)). Qed.
Lemma lem3270786 (t : Prop) : (term19 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem3270787 {A : Type'} (s : A -> Prop) (x : A) : (term18 A s x) = (s x).
Proof. exact (@lem3270786 (s x)). Qed.
Lemma lem3270788 {A : Type'} (s : A -> Prop) (x : A) : (term17 A x s) = (s x).
Proof. exact (TRANS (@lem3270784 A s x) (@lem3270787 A s x)). Qed.
Lemma lem3270789 {A : Type'} (s : A -> Prop) (x : A) : (term10 A x s) = (term20 A s x).
Proof. exact (MK_COMB (@lem3270759 A x) (@lem3270788 A s x)). Qed.
Lemma lem3270791 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3270792 {A : Type'} (s : A -> Prop) (x : A) : (term20 A s x) = (s x).
Proof. exact (@lem3270791 (s x)). Qed.
Lemma lem3270793 {A : Type'} (s : A -> Prop) (x : A) : (term10 A x s) = (s x).
Proof. exact (TRANS (@lem3270789 A s x) (@lem3270792 A s x)). Qed.
Lemma lem3270794 {A : Type'} (s : A -> Prop) (x : A) : (term9 A x s) = (s x).
Proof. exact (TRANS (@lem3270752 A x s) (@lem3270793 A s x)). Qed.
Lemma lem3270795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3270796 {A : Type'} (s : A -> Prop) (x : A) : (term21 A x s) = (term22 A s x).
Proof. exact (MK_COMB (@lem3270795) (@lem3270794 A s x)). Qed.
Lemma lem3270798 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3270799 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3270798 A P x). Qed.
Lemma lem3270800 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3270799 A s x). Qed.
Lemma lem3270801 {A : Type'} (s : A -> Prop) (x : A) : ((term9 A x s) = (@IN A x s)) = ((s x) = (s x)).
Proof. exact (MK_COMB (@lem3270796 A s x) (@lem3270800 A s x)). Qed.
Lemma lem3270803 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3270804 (x : Prop) : (x = x) = True.
Proof. exact (@lem3270803 Prop x). Qed.
Lemma lem3270805 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = (s x)) = True.
Proof. exact (@lem3270804 (s x)). Qed.
Lemma lem3270806 {A : Type'} (x : A) (s : A -> Prop) : ((term9 A x s) = (@IN A x s)) = True.
Proof. exact (TRANS (@lem3270801 A s x) (@lem3270805 A s x)). Qed.
Lemma lem3270807 {A : Type'} (s : A -> Prop) : (term23 A s) = (term24 A).
Proof. exact (fun_ext (fun x : A => @lem3270806 A x s)). Qed.
Lemma lem3270808 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3270809 {A : Type'} (s : A -> Prop) : (term2 A s) = (term25 A).
Proof. exact (MK_COMB (@lem3270808 A) (@lem3270807 A s)). Qed.
Lemma lem3270811 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3270812 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (@lem3270811 A t). Qed.
Lemma lem3270813 {A : Type'} : (term25 A) = True.
Proof. exact (@lem3270812 A True). Qed.
Lemma lem3270814 {A : Type'} (s : A -> Prop) : (term2 A s) = True.
Proof. exact (TRANS (@lem3270809 A s) (@lem3270813 A)). Qed.
Lemma lem3270815 {A : Type'} : (term4 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3270814 A s)). Qed.
Lemma lem3270816 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3270817 {A : Type'} : (term6 A) = (term28 A).
Proof. exact (MK_COMB (@lem3270816 A) (@lem3270815 A)). Qed.
Lemma lem3270819 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3270820 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (@lem3270819 (A -> Prop) t). Qed.
Lemma lem3270821 {A : Type'} : (term28 A) = True.
Proof. exact (@lem3270820 A True). Qed.
Lemma lem3270822 {A : Type'} : (term6 A) = True.
Proof. exact (TRANS (@lem3270817 A) (@lem3270821 A)). Qed.
Lemma lem3270823 {A : Type'} : True = (term6 A).
Proof. exact (SYM (@lem3270822 A)). Qed.
Lemma lem3270824 {A : Type'} : term6 A.
Proof. exact (EQ_MP (@lem3270823 A) (@lem0)). Qed.
Lemma lem3270825 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem3270738 A) (@lem3270824 A)). Qed.
