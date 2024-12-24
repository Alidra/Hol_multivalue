Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import COND_ID_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem12783 (b : Prop) : term0 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem12784 (b : Prop) : (term0 b) = (term1 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem12785 (b : Prop) : term1 b.
Proof. exact (EQ_MP (@lem12784 b) (@lem12783 b)). Qed.
Lemma lem12786 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem12787 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem12788 {A : Type'} (t : A) : (term2 A t) = (term2 A t).
Proof. exact (eq_refl (term2 A t)). Qed.
Lemma lem12789 {A : Type'} (t : A) (b : Prop) (h1 : b = True) : (term3 A t b) = (term4 A t).
Proof. exact (MK_COMB (@lem12788 A t) (@lem12786 b h1)). Qed.
Lemma lem12790 {A : Type'} (t : A) : (term4 A t) = ((@COND A True t t) = t).
Proof. exact (eq_refl (term4 A t)). Qed.
Lemma lem12791 {A : Type'} (t : A) (b : Prop) : (term5 A t b) = (term5 A t b).
Proof. exact (eq_refl (term5 A t b)). Qed.
Lemma lem12792 {A : Type'} (b : Prop) (t : A) : ((term3 A t b) = (term4 A t)) = ((term3 A t b) = ((@COND A True t t) = t)).
Proof. exact (MK_COMB (@lem12791 A t b) (@lem12790 A t)). Qed.
Lemma lem12793 {A : Type'} (b : Prop) (t : A) : (term3 A t b) = ((@COND A b t t) = t).
Proof. exact (eq_refl (term3 A t b)). Qed.
Lemma lem12794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12795 {A : Type'} (b : Prop) (t : A) : (term5 A t b) = (term6 A b t).
Proof. exact (MK_COMB (@lem12794) (@lem12793 A b t)). Qed.
Lemma lem12796 {A : Type'} (t : A) : ((@COND A True t t) = t) = ((@COND A True t t) = t).
Proof. exact (eq_refl ((@COND A True t t) = t)). Qed.
Lemma lem12797 {A : Type'} (b : Prop) (t : A) : ((term3 A t b) = ((@COND A True t t) = t)) = (((@COND A b t t) = t) = ((@COND A True t t) = t)).
Proof. exact (MK_COMB (@lem12795 A b t) (@lem12796 A t)). Qed.
Lemma lem12798 {A : Type'} (b : Prop) (t : A) : ((term3 A t b) = (term4 A t)) = (((@COND A b t t) = t) = ((@COND A True t t) = t)).
Proof. exact (TRANS (@lem12792 A b t) (@lem12797 A b t)). Qed.
Lemma lem12799 {A : Type'} (t : A) (b : Prop) (h1 : b = True) : ((@COND A b t t) = t) = ((@COND A True t t) = t).
Proof. exact (EQ_MP (@lem12798 A b t) (@lem12789 A t b h1)). Qed.
Lemma lem12800 {A : Type'} (t : A) (b : Prop) (h1 : b = True) : ((@COND A True t t) = t) = ((@COND A b t t) = t).
Proof. exact (SYM (@lem12799 A t b h1)). Qed.
Lemma lem12801 {A : Type'} (t : A) : (term2 A t) = (term2 A t).
Proof. exact (eq_refl (term2 A t)). Qed.
Lemma lem12802 {A : Type'} (t : A) (b : Prop) (h1 : b = False) : (term3 A t b) = (term7 A t).
Proof. exact (MK_COMB (@lem12801 A t) (@lem12787 b h1)). Qed.
Lemma lem12803 {A : Type'} (t : A) : (term7 A t) = ((@COND A False t t) = t).
Proof. exact (eq_refl (term7 A t)). Qed.
Lemma lem12804 {A : Type'} (t : A) (b : Prop) : (term5 A t b) = (term5 A t b).
Proof. exact (eq_refl (term5 A t b)). Qed.
Lemma lem12805 {A : Type'} (b : Prop) (t : A) : ((term3 A t b) = (term7 A t)) = ((term3 A t b) = ((@COND A False t t) = t)).
Proof. exact (MK_COMB (@lem12804 A t b) (@lem12803 A t)). Qed.
Lemma lem12806 {A : Type'} (b : Prop) (t : A) : (term3 A t b) = ((@COND A b t t) = t).
Proof. exact (eq_refl (term3 A t b)). Qed.
Lemma lem12807 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12808 {A : Type'} (b : Prop) (t : A) : (term5 A t b) = (term6 A b t).
Proof. exact (MK_COMB (@lem12807) (@lem12806 A b t)). Qed.
Lemma lem12809 {A : Type'} (t : A) : ((@COND A False t t) = t) = ((@COND A False t t) = t).
Proof. exact (eq_refl ((@COND A False t t) = t)). Qed.
Lemma lem12810 {A : Type'} (b : Prop) (t : A) : ((term3 A t b) = ((@COND A False t t) = t)) = (((@COND A b t t) = t) = ((@COND A False t t) = t)).
Proof. exact (MK_COMB (@lem12808 A b t) (@lem12809 A t)). Qed.
Lemma lem12811 {A : Type'} (b : Prop) (t : A) : ((term3 A t b) = (term7 A t)) = (((@COND A b t t) = t) = ((@COND A False t t) = t)).
Proof. exact (TRANS (@lem12805 A b t) (@lem12810 A b t)). Qed.
Lemma lem12812 {A : Type'} (t : A) (b : Prop) (h1 : b = False) : ((@COND A b t t) = t) = ((@COND A False t t) = t).
Proof. exact (EQ_MP (@lem12811 A b t) (@lem12802 A t b h1)). Qed.
Lemma lem12813 {A : Type'} (t : A) (b : Prop) (h1 : b = False) : ((@COND A False t t) = t) = ((@COND A b t t) = t).
Proof. exact (SYM (@lem12812 A t b h1)). Qed.
Lemma lem12817 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem12818 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem12817 A t2 t1). Qed.
Lemma lem12819 {A : Type'} (t : A) : (@COND A True t t) = t.
Proof. exact (@lem12818 A t t). Qed.
Lemma lem12820 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem12821 {A : Type'} (t : A) : (term8 A t) = (@eq A t).
Proof. exact (MK_COMB (@lem12820 A) (@lem12819 A t)). Qed.
Lemma lem12822 {A : Type'} (t : A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem12823 {A : Type'} (t : A) : ((@COND A True t t) = t) = (t = t).
Proof. exact (MK_COMB (@lem12821 A t) (@lem12822 A t)). Qed.
Lemma lem12825 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem12826 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem12825 A x). Qed.
Lemma lem12827 {A : Type'} (t : A) : (t = t) = True.
Proof. exact (@lem12826 A t). Qed.
Lemma lem12828 {A : Type'} (t : A) : ((@COND A True t t) = t) = True.
Proof. exact (TRANS (@lem12823 A t) (@lem12827 A t)). Qed.
Lemma lem12829 {A : Type'} (t : A) : True = ((@COND A True t t) = t).
Proof. exact (SYM (@lem12828 A t)). Qed.
Lemma lem12830 {A : Type'} (t : A) : (@COND A True t t) = t.
Proof. exact (EQ_MP (@lem12829 A t) (@lem0)). Qed.
Lemma lem12834 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem12835 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem12834 A t1 t2). Qed.
Lemma lem12836 {A : Type'} (t : A) : (@COND A False t t) = t.
Proof. exact (@lem12835 A t t). Qed.
Lemma lem12837 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem12838 {A : Type'} (t : A) : (term9 A t) = (@eq A t).
Proof. exact (MK_COMB (@lem12837 A) (@lem12836 A t)). Qed.
Lemma lem12839 {A : Type'} (t : A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem12840 {A : Type'} (t : A) : ((@COND A False t t) = t) = (t = t).
Proof. exact (MK_COMB (@lem12838 A t) (@lem12839 A t)). Qed.
Lemma lem12842 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem12843 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem12842 A x). Qed.
Lemma lem12844 {A : Type'} (t : A) : (t = t) = True.
Proof. exact (@lem12843 A t). Qed.
Lemma lem12845 {A : Type'} (t : A) : ((@COND A False t t) = t) = True.
Proof. exact (TRANS (@lem12840 A t) (@lem12844 A t)). Qed.
Lemma lem12846 {A : Type'} (t : A) : True = ((@COND A False t t) = t).
Proof. exact (SYM (@lem12845 A t)). Qed.
Lemma lem12847 {A : Type'} (t : A) : (@COND A False t t) = t.
Proof. exact (EQ_MP (@lem12846 A t) (@lem0)). Qed.
Lemma lem12848 {A : Type'} (t : A) (b : Prop) (h1 : b = False) : (@COND A b t t) = t.
Proof. exact (EQ_MP (@lem12813 A t b h1) (@lem12847 A t)). Qed.
Lemma lem12849 {A : Type'} (t : A) (b : Prop) (h1 : b = True) : (@COND A b t t) = t.
Proof. exact (EQ_MP (@lem12800 A t b h1) (@lem12830 A t)). Qed.
Lemma lem12850 {A : Type'} (b : Prop) (t : A) : (@COND A b t t) = t.
Proof. exact (or_elim (@lem12785 b) (fun h0 : b = True => @lem12849 A t b h0) (fun h0 : b = False => @lem12848 A t b h0)). Qed.
Lemma lem12855 {A : Type'} (b : Prop) : term10 A b.
Proof. exact (fun t : A => @lem12850 A b t). Qed.
Lemma lem12860 {A : Type'} : term11 A.
Proof. exact (fun b : Prop => @lem12855 A b). Qed.
