Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2301026_term_abbrevs.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301015 (x : int) (y : int) : (term0 x y) = (term1 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301016 (m : int) (n : int) : (term0 m n) = (term1 m n).
Proof. exact (@lem2301015 m n). Qed.
Lemma lem2301017 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301018 (m : int) (n : int) : (term2 m n) = (term3 m n).
Proof. exact (MK_COMB (@lem2301017) (@lem2301016 m n)). Qed.
Lemma lem2301020 (x : int) (y : int) : (term0 x y) = (term1 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301021 (n : int) (m : int) : (term0 n m) = (term1 n m).
Proof. exact (@lem2301020 n m). Qed.
Lemma lem2301022 (n : int) (m : int) : ((term0 m n) = (term0 n m)) = ((term1 m n) = (term1 n m)).
Proof. exact (MK_COMB (@lem2301018 m n) (@lem2301021 n m)). Qed.
Lemma lem2301024 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301025 (n : int) (m : int) : ((term1 m n) = (term1 n m)) = ((int_add m n) = (int_add n m)).
Proof. exact (@lem2301024 (int_add m n) (int_add n m)). Qed.
Lemma lem2301026 (n : int) (m : int) : ((term0 m n) = (term0 n m)) = ((int_add m n) = (int_add n m)).
Proof. exact (TRANS (@lem2301022 n m) (@lem2301025 n m)). Qed.
