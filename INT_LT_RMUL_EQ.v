Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_RMUL_EQ_term_abbrevs.
Require Import REAL_LT_RMUL_EQ_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304824 (x : int) : term0 x.
Proof. exact (@lem1602515 (real_of_int x)). Qed.
Lemma lem2304825 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304826 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304825 x) (@lem2304824 x)). Qed.
Lemma lem2304827 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304826 x (real_of_int y)). Qed.
Lemma lem2304828 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304829 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2304828 x y) (@lem2304827 x y)). Qed.
Lemma lem2304830 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2304829 x y (real_of_int z)). Qed.
Lemma lem2304831 (z : int) (x : int) (y : int) : (term4 x y z) = (term5 z x y).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2304832 (z : int) (x : int) (y : int) : term5 z x y.
Proof. exact (EQ_MP (@lem2304831 z x y) (@lem2304830 x y z)). Qed.
Lemma lem2304834 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304835 : term7 = term8.
Proof. exact (@lem2304834 (NUMERAL 0)). Qed.
Lemma lem2304836 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304837 : term9 = term10.
Proof. exact (MK_COMB (@lem2304836) (@lem2304835)). Qed.
Lemma lem2304838 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2304839 (z : int) : (term11 z) = (term12 z).
Proof. exact (MK_COMB (@lem2304837) (@lem2304838 z)). Qed.
Lemma lem2304841 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304842 (z : int) : (term12 z) = (term14 z).
Proof. exact (@lem2304841 term15 z). Qed.
Lemma lem2304843 (z : int) : (term11 z) = (term14 z).
Proof. exact (TRANS (@lem2304839 z) (@lem2304842 z)). Qed.
Lemma lem2304844 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2304845 (z : int) : (term16 z) = (term17 z).
Proof. exact (MK_COMB (@lem2304844) (@lem2304843 z)). Qed.
Lemma lem2304847 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304848 (x : int) (z : int) : (term18 x z) = (term19 x z).
Proof. exact (@lem2304847 x z). Qed.
Lemma lem2304849 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304850 (x : int) (z : int) : (term20 x z) = (term21 x z).
Proof. exact (MK_COMB (@lem2304849) (@lem2304848 x z)). Qed.
Lemma lem2304852 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304853 (y : int) (z : int) : (term18 y z) = (term19 y z).
Proof. exact (@lem2304852 y z). Qed.
Lemma lem2304854 (x : int) (y : int) (z : int) : (term22 x y z) = (term23 x y z).
Proof. exact (MK_COMB (@lem2304850 x z) (@lem2304853 y z)). Qed.
Lemma lem2304856 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304857 (x : int) (y : int) (z : int) : (term23 x y z) = (term24 x y z).
Proof. exact (@lem2304856 (int_mul x z) (int_mul y z)). Qed.
Lemma lem2304858 (x : int) (y : int) (z : int) : (term22 x y z) = (term24 x y z).
Proof. exact (TRANS (@lem2304854 x y z) (@lem2304857 x y z)). Qed.
Lemma lem2304859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304860 (x : int) (y : int) (z : int) : (term25 x y z) = (term26 x y z).
Proof. exact (MK_COMB (@lem2304859) (@lem2304858 x y z)). Qed.
Lemma lem2304862 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304863 (z : int) (x : int) (y : int) : ((term22 x y z) = (term13 x y)) = ((term24 x y z) = (int_lt x y)).
Proof. exact (MK_COMB (@lem2304860 x y z) (@lem2304862 x y)). Qed.
Lemma lem2304864 (z : int) (x : int) (y : int) : (term5 z x y) = (term27 z x y).
Proof. exact (MK_COMB (@lem2304845 z) (@lem2304863 z x y)). Qed.
Lemma lem2304865 (z : int) (x : int) (y : int) : term27 z x y.
Proof. exact (EQ_MP (@lem2304864 z x y) (@lem2304832 z x y)). Qed.
Lemma lem2304866 (x : int) (y : int) : term28 x y.
Proof. exact (fun z : int => @lem2304865 z x y). Qed.
Lemma lem2304867 (x : int) : term29 x.
Proof. exact (fun y : int => @lem2304866 x y). Qed.
Lemma lem2304868 : term30.
Proof. exact (fun x : int => @lem2304867 x). Qed.
