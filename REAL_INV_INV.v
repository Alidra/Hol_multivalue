Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INV_INV_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_MUL_RINV_UNIQ_spec.
Require Import TREAL_INV_0_spec.
Require Import thm0_spec.
Require Import thm1340072_spec.
Require Import thm1340174_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem1587798 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1587799 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1587798 h1 x). Qed.
Lemma lem1587800 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1587801 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1587800 x) (@lem1587799 x h1)). Qed.
Lemma lem1587802 (x : real) (h1 : term3 x) : term3 x.
Proof. exact (h1). Qed.
Lemma lem1587803 (x : real) (h1 : term0) (h2 : term3 x) : (term4 x) = term5.
Proof. exact (@lem1587801 x h1 (@lem1587802 x h2)). Qed.
Lemma lem1587804 (x : real) (h1 : term3 x) : term6 x.
Proof. exact (fun h0 : term0 => @lem1587803 x h0 h1). Qed.
Lemma lem1587805 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1587806 (x : real) (h1 : term0) (h2 : term3 x) : (term4 x) = term5.
Proof. exact (@lem1587804 x h2 (@lem1587805 h1)). Qed.
Lemma lem1587807 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun h0 : term3 x => @lem1587806 x h1 h0). Qed.
Lemma lem1587808 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1587807 x h1). Qed.
Lemma lem1587809 : term7.
Proof. exact (fun h0 : term0 => @lem1587808 h0). Qed.
Lemma lem1587810 : term0.
Proof. exact (@lem1587809 (@lem1340174)). Qed.
Lemma lem1587811 (x : real) : term1 x.
Proof. exact (@lem1587810 x). Qed.
Lemma lem1587812 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1587814 (h1 : term8) : term8.
Proof. exact (h1). Qed.
Lemma lem1587815 (x : real) (h1 : term8) : term9 x.
Proof. exact (@lem1587814 h1 x). Qed.
Lemma lem1587816 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1587817 (x : real) (h1 : term8) : term10 x.
Proof. exact (EQ_MP (@lem1587816 x) (@lem1587815 x h1)). Qed.
Lemma lem1587818 (x : real) (y : real) (h1 : term8) : term11 x y.
Proof. exact (@lem1587817 x h1 y). Qed.
Lemma lem1587819 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1587820 (x : real) (y : real) (h1 : term8) : term12 x y.
Proof. exact (EQ_MP (@lem1587819 x y) (@lem1587818 x y h1)). Qed.
Lemma lem1587821 (x : real) (y : real) (h1 : (real_mul x y) = term5) : (real_mul x y) = term5.
Proof. exact (h1). Qed.
Lemma lem1587822 (x : real) (y : real) (h1 : term8) (h2 : (real_mul x y) = term5) : (real_inv x) = y.
Proof. exact (@lem1587820 x y h1 (@lem1587821 x y h2)). Qed.
Lemma lem1587823 (x : real) (y : real) (h1 : (real_mul x y) = term5) : term13 x y.
Proof. exact (fun h0 : term8 => @lem1587822 x y h0 h1). Qed.
Lemma lem1587824 (h1 : term8) : term8.
Proof. exact (h1). Qed.
Lemma lem1587825 (x : real) (y : real) (h1 : term8) (h2 : (real_mul x y) = term5) : (real_inv x) = y.
Proof. exact (@lem1587823 x y h2 (@lem1587824 h1)). Qed.
Lemma lem1587826 (x : real) (y : real) (h1 : term8) : term12 x y.
Proof. exact (fun h0 : (real_mul x y) = term5 => @lem1587825 x y h1 h0). Qed.
Lemma lem1587827 (x : real) (h1 : term8) : term10 x.
Proof. exact (fun y : real => @lem1587826 x y h1). Qed.
Lemma lem1587828 (h1 : term8) : term8.
Proof. exact (fun x : real => @lem1587827 x h1). Qed.
Lemma lem1587829 : term14.
Proof. exact (fun h0 : term8 => @lem1587828 h0). Qed.
Lemma lem1587830 : term8.
Proof. exact (@lem1587829 (@lem1587797)). Qed.
Lemma lem1587831 (x : real) : term9 x.
Proof. exact (@lem1587830 x). Qed.
Lemma lem1587832 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1587833 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem1587832 x) (@lem1587831 x)). Qed.
Lemma lem1587834 (x : real) (y : real) : term11 x y.
Proof. exact (@lem1587833 x y). Qed.
Lemma lem1587835 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1587837 (x : real) : term15 x.
Proof. exact (@lem9784 (x = term16)). Qed.
Lemma lem1587838 (x : real) : (term15 x) = (term17 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1587839 (x : real) : term17 x.
Proof. exact (EQ_MP (@lem1587838 x) (@lem1587837 x)). Qed.
Lemma lem1587841 (x : real) (h1 : term3 x) : term3 x.
Proof. exact (h1). Qed.
Lemma lem1587845 (x : real) (h1 : x = term16) : x = term16.
Proof. exact (h1). Qed.
Lemma lem1587846 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1587847 (x : real) (h1 : x = term16) : (real_inv x) = term18.
Proof. exact (MK_COMB (@lem1587846) (@lem1587845 x h1)). Qed.
Lemma lem1587849 : term18 = term16.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1587850 (x : real) (h1 : x = term16) : (real_inv x) = term16.
Proof. exact (TRANS (@lem1587847 x h1) (@lem1587849)). Qed.
Lemma lem1587851 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1587852 (x : real) (h1 : x = term16) : (term19 x) = term18.
Proof. exact (MK_COMB (@lem1587851) (@lem1587850 x h1)). Qed.
Lemma lem1587854 : term18 = term16.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1587855 (x : real) (h1 : x = term16) : (term19 x) = term16.
Proof. exact (TRANS (@lem1587852 x h1) (@lem1587854)). Qed.
Lemma lem1587856 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1587857 (x : real) (h1 : x = term16) : (term20 x) = term21.
Proof. exact (MK_COMB (@lem1587856) (@lem1587855 x h1)). Qed.
Lemma lem1587859 (x : real) (h1 : x = term16) : x = term16.
Proof. exact (h1). Qed.
Lemma lem1587860 (x : real) (h1 : x = term16) : ((term19 x) = x) = (term16 = term16).
Proof. exact (MK_COMB (@lem1587857 x h1) (@lem1587859 x h1)). Qed.
Lemma lem1587862 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1587863 (x : real) : (x = x) = True.
Proof. exact (@lem1587862 real x). Qed.
Lemma lem1587864 : (term16 = term16) = True.
Proof. exact (@lem1587863 term16). Qed.
Lemma lem1587865 (x : real) (h1 : x = term16) : ((term19 x) = x) = True.
Proof. exact (TRANS (@lem1587860 x h1) (@lem1587864)). Qed.
Lemma lem1587866 (x : real) (h1 : x = term16) : True = ((term19 x) = x).
Proof. exact (SYM (@lem1587865 x h1)). Qed.
Lemma lem1587867 (x : real) (h1 : x = term16) : (term19 x) = x.
Proof. exact (EQ_MP (@lem1587866 x h1) (@lem0)). Qed.
Lemma lem1587886 (x : real) (y : real) : term12 x y.
Proof. exact (EQ_MP (@lem1587835 x y) (@lem1587834 x y)). Qed.
Lemma lem1587887 (x : real) : term22 x.
Proof. exact (@lem1587886 (real_inv x) x). Qed.
Lemma lem1587889 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1587812 x) (@lem1587811 x)). Qed.
Lemma lem1587890 (x : real) : term23 x.
Proof. exact (@lem82 (x = term16)). Qed.
Lemma lem1587904 (x : real) (h1 : term3 x) : (x = term16) = False.
Proof. exact (@lem1587890 x (@lem1587841 x h1)). Qed.
Lemma lem1587905 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1587906 (x : real) (h1 : term3 x) : (term3 x) = (~ False).
Proof. exact (MK_COMB (@lem1587905) (@lem1587904 x h1)). Qed.
Lemma lem1587908 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1587909 (x : real) (h1 : term3 x) : (term3 x) = True.
Proof. exact (TRANS (@lem1587906 x h1) (@lem1587908)). Qed.
Lemma lem1587910 (x : real) (h1 : term3 x) : True = (term3 x).
Proof. exact (SYM (@lem1587909 x h1)). Qed.
Lemma lem1587911 (x : real) (h1 : term3 x) : term3 x.
Proof. exact (EQ_MP (@lem1587910 x h1) (@lem0)). Qed.
Lemma lem1587912 (x : real) (h1 : term3 x) : (term4 x) = term5.
Proof. exact (@lem1587889 x (@lem1587911 x h1)). Qed.
Lemma lem1587914 (x : real) (h1 : term3 x) : (term19 x) = x.
Proof. exact (@lem1587887 x (@lem1587912 x h1)). Qed.
Lemma lem1587915 (x : real) : (term19 x) = x.
Proof. exact (or_elim (@lem1587839 x) (fun h0 : x = term16 => @lem1587867 x h0) (fun h0 : term3 x => @lem1587914 x h0)). Qed.
Lemma lem1587920 : term24.
Proof. exact (fun x : real => @lem1587915 x). Qed.
