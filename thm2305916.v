Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2305916_term_abbrevs.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2305905 (x : int) (y : int) : (term0 x y) = (term1 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305906 (m : int) (n : int) : (term0 m n) = (term1 m n).
Proof. exact (@lem2305905 m n). Qed.
Lemma lem2305907 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305908 (m : int) (n : int) : (term2 m n) = (term3 m n).
Proof. exact (MK_COMB (@lem2305907) (@lem2305906 m n)). Qed.
Lemma lem2305910 (x : int) (y : int) : (term0 x y) = (term1 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305911 (n : int) (m : int) : (term0 n m) = (term1 n m).
Proof. exact (@lem2305910 n m). Qed.
Lemma lem2305912 (n : int) (m : int) : ((term0 m n) = (term0 n m)) = ((term1 m n) = (term1 n m)).
Proof. exact (MK_COMB (@lem2305908 m n) (@lem2305911 n m)). Qed.
Lemma lem2305914 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305915 (n : int) (m : int) : ((term1 m n) = (term1 n m)) = ((int_mul m n) = (int_mul n m)).
Proof. exact (@lem2305914 (int_mul m n) (int_mul n m)). Qed.
Lemma lem2305916 (n : int) (m : int) : ((term0 m n) = (term0 n m)) = ((int_mul m n) = (int_mul n m)).
Proof. exact (TRANS (@lem2305912 n m) (@lem2305915 n m)). Qed.
