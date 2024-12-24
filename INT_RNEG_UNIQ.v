Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_RNEG_UNIQ_term_abbrevs.
Require Import REAL_RNEG_UNIQ_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2308947 (x : int) : term0 x.
Proof. exact (@lem1491188 (real_of_int x)). Qed.
Lemma lem2308948 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2308949 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2308948 x) (@lem2308947 x)). Qed.
Lemma lem2308950 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2308949 x (real_of_int y)). Qed.
Lemma lem2308951 (y : int) (x : int) : (term2 x y) = (((term3 x y) = term4) = ((real_of_int y) = (term5 x))).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2308952 (y : int) (x : int) : ((term3 x y) = term4) = ((real_of_int y) = (term5 x)).
Proof. exact (EQ_MP (@lem2308951 y x) (@lem2308950 x y)). Qed.
Lemma lem2308954 (x : int) (y : int) : (term3 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2308955 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2308956 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2308955) (@lem2308954 x y)). Qed.
Lemma lem2308958 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308959 : term4 = term10.
Proof. exact (@lem2308958 (NUMERAL 0)). Qed.
Lemma lem2308960 (x : int) (y : int) : ((term3 x y) = term4) = ((term6 x y) = term10).
Proof. exact (MK_COMB (@lem2308956 x y) (@lem2308959)). Qed.
Lemma lem2308962 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308963 (x : int) (y : int) : ((term6 x y) = term10) = ((int_add x y) = term11).
Proof. exact (@lem2308962 (int_add x y) term11). Qed.
Lemma lem2308964 (x : int) (y : int) : ((term3 x y) = term4) = ((int_add x y) = term11).
Proof. exact (TRANS (@lem2308960 x y) (@lem2308963 x y)). Qed.
Lemma lem2308965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2308966 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2308965) (@lem2308964 x y)). Qed.
Lemma lem2308968 (x : int) : (term5 x) = (term14 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2308969 (y : int) : (term15 y) = (term15 y).
Proof. exact (eq_refl (term15 y)). Qed.
Lemma lem2308970 (y : int) (x : int) : ((real_of_int y) = (term5 x)) = ((real_of_int y) = (term14 x)).
Proof. exact (MK_COMB (@lem2308969 y) (@lem2308968 x)). Qed.
Lemma lem2308972 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308973 (y : int) (x : int) : ((real_of_int y) = (term14 x)) = (y = (int_neg x)).
Proof. exact (@lem2308972 y (int_neg x)). Qed.
Lemma lem2308974 (y : int) (x : int) : ((real_of_int y) = (term5 x)) = (y = (int_neg x)).
Proof. exact (TRANS (@lem2308970 y x) (@lem2308973 y x)). Qed.
Lemma lem2308975 (y : int) (x : int) : (((term3 x y) = term4) = ((real_of_int y) = (term5 x))) = (((int_add x y) = term11) = (y = (int_neg x))).
Proof. exact (MK_COMB (@lem2308966 x y) (@lem2308974 y x)). Qed.
Lemma lem2308976 (y : int) (x : int) : ((int_add x y) = term11) = (y = (int_neg x)).
Proof. exact (EQ_MP (@lem2308975 y x) (@lem2308952 y x)). Qed.
Lemma lem2308977 (x : int) : term16 x.
Proof. exact (fun y : int => @lem2308976 y x). Qed.
Lemma lem2308978 : term17.
Proof. exact (fun x : int => @lem2308977 x). Qed.
