Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MUL_LZERO_term_abbrevs.
Require Import REAL_MUL_LZERO_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306016 (x : int) : term0 x.
Proof. exact (@lem1357243 (real_of_int x)). Qed.
Lemma lem2306017 (x : int) : (term0 x) = ((term1 x) = term2).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306018 (x : int) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem2306017 x) (@lem2306016 x)). Qed.
Lemma lem2306020 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306021 : term2 = term4.
Proof. exact (@lem2306020 (NUMERAL 0)). Qed.
Lemma lem2306022 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2306023 : term5 = term6.
Proof. exact (MK_COMB (@lem2306022) (@lem2306021)). Qed.
Lemma lem2306024 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2306025 (x : int) : (term1 x) = (term7 x).
Proof. exact (MK_COMB (@lem2306023) (@lem2306024 x)). Qed.
Lemma lem2306027 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306028 (x : int) : (term7 x) = (term10 x).
Proof. exact (@lem2306027 term11 x). Qed.
Lemma lem2306029 (x : int) : (term1 x) = (term10 x).
Proof. exact (TRANS (@lem2306025 x) (@lem2306028 x)). Qed.
Lemma lem2306030 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306031 (x : int) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem2306030) (@lem2306029 x)). Qed.
Lemma lem2306033 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306034 : term2 = term4.
Proof. exact (@lem2306033 (NUMERAL 0)). Qed.
Lemma lem2306035 (x : int) : ((term1 x) = term2) = ((term10 x) = term4).
Proof. exact (MK_COMB (@lem2306031 x) (@lem2306034)). Qed.
Lemma lem2306037 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306038 (x : int) : ((term10 x) = term4) = ((term14 x) = term11).
Proof. exact (@lem2306037 (term14 x) term11). Qed.
Lemma lem2306039 (x : int) : ((term1 x) = term2) = ((term14 x) = term11).
Proof. exact (TRANS (@lem2306035 x) (@lem2306038 x)). Qed.
Lemma lem2306040 (x : int) : (term14 x) = term11.
Proof. exact (EQ_MP (@lem2306039 x) (@lem2306018 x)). Qed.
Lemma lem2306041 : term15.
Proof. exact (fun x : int => @lem2306040 x). Qed.
