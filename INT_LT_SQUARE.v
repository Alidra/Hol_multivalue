Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_SQUARE_term_abbrevs.
Require Import REAL_LT_SQUARE_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2304902 (x : int) : term0 x.
Proof. exact (@lem1630933 (real_of_int x)). Qed.
Lemma lem2304903 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304904 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2304903 x) (@lem2304902 x)). Qed.
Lemma lem2304906 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304907 : term4 = term5.
Proof. exact (@lem2304906 (NUMERAL 0)). Qed.
Lemma lem2304908 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304909 : term6 = term7.
Proof. exact (MK_COMB (@lem2304908) (@lem2304907)). Qed.
Lemma lem2304911 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304912 (x : int) : (term10 x) = (term11 x).
Proof. exact (@lem2304911 x x). Qed.
Lemma lem2304913 (x : int) : (term1 x) = (term12 x).
Proof. exact (MK_COMB (@lem2304909) (@lem2304912 x)). Qed.
Lemma lem2304915 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304916 (x : int) : (term12 x) = (term14 x).
Proof. exact (@lem2304915 term15 (int_mul x x)). Qed.
Lemma lem2304917 (x : int) : (term1 x) = (term14 x).
Proof. exact (TRANS (@lem2304913 x) (@lem2304916 x)). Qed.
Lemma lem2304918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304919 (x : int) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem2304918) (@lem2304917 x)). Qed.
Lemma lem2304921 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304922 : term4 = term5.
Proof. exact (@lem2304921 (NUMERAL 0)). Qed.
Lemma lem2304923 (x : int) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem2304924 (x : int) : ((real_of_int x) = term4) = ((real_of_int x) = term5).
Proof. exact (MK_COMB (@lem2304923 x) (@lem2304922)). Qed.
Lemma lem2304926 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2304927 (x : int) : ((real_of_int x) = term5) = (x = term15).
Proof. exact (@lem2304926 x term15). Qed.
Lemma lem2304928 (x : int) : ((real_of_int x) = term4) = (x = term15).
Proof. exact (TRANS (@lem2304924 x) (@lem2304927 x)). Qed.
Lemma lem2304929 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2304930 (x : int) : (term2 x) = (term19 x).
Proof. exact (MK_COMB (@lem2304929) (@lem2304928 x)). Qed.
Lemma lem2304931 (x : int) : ((term1 x) = (term2 x)) = ((term14 x) = (term19 x)).
Proof. exact (MK_COMB (@lem2304919 x) (@lem2304930 x)). Qed.
Lemma lem2304932 (x : int) : (term14 x) = (term19 x).
Proof. exact (EQ_MP (@lem2304931 x) (@lem2304904 x)). Qed.
Lemma lem2304933 : term20.
Proof. exact (fun x : int => @lem2304932 x). Qed.
