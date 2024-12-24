Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_RNEG_term_abbrevs.
Require Import REAL_LT_RNEG_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304869 (x : int) : term0 x.
Proof. exact (@lem1502267 (real_of_int x)). Qed.
Lemma lem2304870 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304871 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304870 x) (@lem2304869 x)). Qed.
Lemma lem2304872 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304871 x (real_of_int y)). Qed.
Lemma lem2304873 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304874 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2304873 x y) (@lem2304872 x y)). Qed.
Lemma lem2304876 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2304877 (y : int) : (term5 y) = (term6 y).
Proof. exact (@lem2304876 y). Qed.
Lemma lem2304878 (x : int) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2304879 (x : int) (y : int) : (term3 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2304878 x) (@lem2304877 y)). Qed.
Lemma lem2304881 (x : int) (y : int) : (term9 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304882 (x : int) (y : int) : (term8 x y) = (term10 x y).
Proof. exact (@lem2304881 x (int_neg y)). Qed.
Lemma lem2304883 (x : int) (y : int) : (term3 x y) = (term10 x y).
Proof. exact (TRANS (@lem2304879 x y) (@lem2304882 x y)). Qed.
Lemma lem2304884 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304885 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2304884) (@lem2304883 x y)). Qed.
Lemma lem2304887 (x : int) (y : int) : (term13 x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2304888 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304889 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem2304888) (@lem2304887 x y)). Qed.
Lemma lem2304891 (n : nat) : (real_of_num n) = (term17 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304892 : term18 = term19.
Proof. exact (@lem2304891 (NUMERAL 0)). Qed.
Lemma lem2304893 (x : int) (y : int) : (term4 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem2304889 x y) (@lem2304892)). Qed.
Lemma lem2304895 (x : int) (y : int) : (term9 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304896 (x : int) (y : int) : (term20 x y) = (term21 x y).
Proof. exact (@lem2304895 (int_add x y) term22). Qed.
Lemma lem2304897 (x : int) (y : int) : (term4 x y) = (term21 x y).
Proof. exact (TRANS (@lem2304893 x y) (@lem2304896 x y)). Qed.
Lemma lem2304898 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term10 x y) = (term21 x y)).
Proof. exact (MK_COMB (@lem2304885 x y) (@lem2304897 x y)). Qed.
Lemma lem2304899 (x : int) (y : int) : (term10 x y) = (term21 x y).
Proof. exact (EQ_MP (@lem2304898 x y) (@lem2304874 x y)). Qed.
Lemma lem2304900 (x : int) : term23 x.
Proof. exact (fun y : int => @lem2304899 x y). Qed.
Lemma lem2304901 : term24.
Proof. exact (fun x : int => @lem2304900 x). Qed.
