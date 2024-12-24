Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NEG_GE0_term_abbrevs.
Require Import REAL_NEG_GE0_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2306428 (x : int) : term0 x.
Proof. exact (@lem1498282 (real_of_int x)). Qed.
Lemma lem2306429 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306430 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2306429 x) (@lem2306428 x)). Qed.
Lemma lem2306432 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306433 : term4 = term5.
Proof. exact (@lem2306432 (NUMERAL 0)). Qed.
Lemma lem2306434 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2306435 : term6 = term7.
Proof. exact (MK_COMB (@lem2306434) (@lem2306433)). Qed.
Lemma lem2306437 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306438 (x : int) : (term1 x) = (term10 x).
Proof. exact (MK_COMB (@lem2306435) (@lem2306437 x)). Qed.
Lemma lem2306440 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2306441 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2306440 term13 (int_neg x)). Qed.
Lemma lem2306442 (x : int) : (term1 x) = (term12 x).
Proof. exact (TRANS (@lem2306438 x) (@lem2306441 x)). Qed.
Lemma lem2306443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2306444 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2306443) (@lem2306442 x)). Qed.
Lemma lem2306446 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306447 : term4 = term5.
Proof. exact (@lem2306446 (NUMERAL 0)). Qed.
Lemma lem2306448 (x : int) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem2306449 (x : int) : (term2 x) = (term17 x).
Proof. exact (MK_COMB (@lem2306448 x) (@lem2306447)). Qed.
Lemma lem2306451 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2306452 (x : int) : (term17 x) = (term18 x).
Proof. exact (@lem2306451 x term13). Qed.
Lemma lem2306453 (x : int) : (term2 x) = (term18 x).
Proof. exact (TRANS (@lem2306449 x) (@lem2306452 x)). Qed.
Lemma lem2306454 (x : int) : ((term1 x) = (term2 x)) = ((term12 x) = (term18 x)).
Proof. exact (MK_COMB (@lem2306444 x) (@lem2306453 x)). Qed.
Lemma lem2306455 (x : int) : (term12 x) = (term18 x).
Proof. exact (EQ_MP (@lem2306454 x) (@lem2306430 x)). Qed.
Lemma lem2306456 : term19.
Proof. exact (fun x : int => @lem2306455 x). Qed.
