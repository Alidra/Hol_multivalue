Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NEG_EQ_0_term_abbrevs.
Require Import REAL_NEG_EQ_0_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306399 (x : int) : term0 x.
Proof. exact (@lem1507647 (real_of_int x)). Qed.
Lemma lem2306400 (x : int) : (term0 x) = (((term1 x) = term2) = ((real_of_int x) = term2)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306401 (x : int) : ((term1 x) = term2) = ((real_of_int x) = term2).
Proof. exact (EQ_MP (@lem2306400 x) (@lem2306399 x)). Qed.
Lemma lem2306403 (x : int) : (term1 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306404 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306405 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2306404) (@lem2306403 x)). Qed.
Lemma lem2306407 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306408 : term2 = term7.
Proof. exact (@lem2306407 (NUMERAL 0)). Qed.
Lemma lem2306409 (x : int) : ((term1 x) = term2) = ((term3 x) = term7).
Proof. exact (MK_COMB (@lem2306405 x) (@lem2306408)). Qed.
Lemma lem2306411 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306412 (x : int) : ((term3 x) = term7) = ((int_neg x) = term8).
Proof. exact (@lem2306411 (int_neg x) term8). Qed.
Lemma lem2306413 (x : int) : ((term1 x) = term2) = ((int_neg x) = term8).
Proof. exact (TRANS (@lem2306409 x) (@lem2306412 x)). Qed.
Lemma lem2306414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2306415 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2306414) (@lem2306413 x)). Qed.
Lemma lem2306417 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306418 : term2 = term7.
Proof. exact (@lem2306417 (NUMERAL 0)). Qed.
Lemma lem2306419 (x : int) : (term11 x) = (term11 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem2306420 (x : int) : ((real_of_int x) = term2) = ((real_of_int x) = term7).
Proof. exact (MK_COMB (@lem2306419 x) (@lem2306418)). Qed.
Lemma lem2306422 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306423 (x : int) : ((real_of_int x) = term7) = (x = term8).
Proof. exact (@lem2306422 x term8). Qed.
Lemma lem2306424 (x : int) : ((real_of_int x) = term2) = (x = term8).
Proof. exact (TRANS (@lem2306420 x) (@lem2306423 x)). Qed.
Lemma lem2306425 (x : int) : (((term1 x) = term2) = ((real_of_int x) = term2)) = (((int_neg x) = term8) = (x = term8)).
Proof. exact (MK_COMB (@lem2306415 x) (@lem2306424 x)). Qed.
Lemma lem2306426 (x : int) : ((int_neg x) = term8) = (x = term8).
Proof. exact (EQ_MP (@lem2306425 x) (@lem2306401 x)). Qed.
Lemma lem2306427 : term12.
Proof. exact (fun x : int => @lem2306426 x). Qed.
