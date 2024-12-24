Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_LT2_ODD_term_abbrevs.
Require Import REAL_POW_LT2_ODD_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2308496 (n : nat) : term0 n.
Proof. exact (@lem1660753 n). Qed.
Lemma lem2308497 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308498 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2308497 n) (@lem2308496 n)). Qed.
Lemma lem2308499 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2308498 n (real_of_int x)). Qed.
Lemma lem2308500 (x : int) (n : nat) : (term2 n x) = (term3 x n).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2308501 (x : int) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem2308500 x n) (@lem2308499 n x)). Qed.
Lemma lem2308502 (x : int) (n : nat) (y : int) : term4 x n y.
Proof. exact (@lem2308501 x n (real_of_int y)). Qed.
Lemma lem2308503 (x : int) (y : int) (n : nat) : (term4 x n y) = (term5 x y n).
Proof. exact (eq_refl (term4 x n y)). Qed.
Lemma lem2308504 (x : int) (y : int) (n : nat) : term5 x y n.
Proof. exact (EQ_MP (@lem2308503 x y n) (@lem2308502 x n y)). Qed.
Lemma lem2308506 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2308508 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2308507) (@lem2308506 x y)). Qed.
Lemma lem2308509 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem2308510 (x : int) (y : int) (n : nat) : (term9 x y n) = (term10 x y n).
Proof. exact (MK_COMB (@lem2308508 x y) (@lem2308509 n)). Qed.
Lemma lem2308511 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308512 (x : int) (y : int) (n : nat) : (term11 x y n) = (term12 x y n).
Proof. exact (MK_COMB (@lem2308511) (@lem2308510 x y n)). Qed.
Lemma lem2308514 (x : int) (n : nat) : (term13 x n) = (term14 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308515 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2308516 (x : int) (n : nat) : (term15 x n) = (term16 x n).
Proof. exact (MK_COMB (@lem2308515) (@lem2308514 x n)). Qed.
Lemma lem2308518 (x : int) (n : nat) : (term13 x n) = (term14 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308519 (y : int) (n : nat) : (term13 y n) = (term14 y n).
Proof. exact (@lem2308518 y n). Qed.
Lemma lem2308520 (x : int) (y : int) (n : nat) : (term17 x y n) = (term18 x y n).
Proof. exact (MK_COMB (@lem2308516 x n) (@lem2308519 y n)). Qed.
Lemma lem2308522 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308523 (x : int) (y : int) (n : nat) : (term18 x y n) = (term19 x y n).
Proof. exact (@lem2308522 (int_pow x n) (int_pow y n)). Qed.
Lemma lem2308524 (x : int) (y : int) (n : nat) : (term17 x y n) = (term19 x y n).
Proof. exact (TRANS (@lem2308520 x y n) (@lem2308523 x y n)). Qed.
Lemma lem2308525 (x : int) (y : int) (n : nat) : (term5 x y n) = (term20 x y n).
Proof. exact (MK_COMB (@lem2308512 x y n) (@lem2308524 x y n)). Qed.
Lemma lem2308526 (x : int) (y : int) (n : nat) : term20 x y n.
Proof. exact (EQ_MP (@lem2308525 x y n) (@lem2308504 x y n)). Qed.
Lemma lem2308527 (x : int) (n : nat) : term21 x n.
Proof. exact (fun y : int => @lem2308526 x y n). Qed.
Lemma lem2308528 (n : nat) : term22 n.
Proof. exact (fun x : int => @lem2308527 x n). Qed.
Lemma lem2308529 : term23.
Proof. exact (fun n : nat => @lem2308528 n). Qed.
