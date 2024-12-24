Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_LE2_ODD_term_abbrevs.
Require Import REAL_POW_LE2_ODD_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2308268 (n : nat) : term0 n.
Proof. exact (@lem1661016 n). Qed.
Lemma lem2308269 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308270 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2308269 n) (@lem2308268 n)). Qed.
Lemma lem2308271 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2308270 n (real_of_int x)). Qed.
Lemma lem2308272 (x : int) (n : nat) : (term2 n x) = (term3 x n).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2308273 (x : int) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem2308272 x n) (@lem2308271 n x)). Qed.
Lemma lem2308274 (x : int) (n : nat) (y : int) : term4 x n y.
Proof. exact (@lem2308273 x n (real_of_int y)). Qed.
Lemma lem2308275 (x : int) (y : int) (n : nat) : (term4 x n y) = (term5 x y n).
Proof. exact (eq_refl (term4 x n y)). Qed.
Lemma lem2308276 (x : int) (y : int) (n : nat) : term5 x y n.
Proof. exact (EQ_MP (@lem2308275 x y n) (@lem2308274 x n y)). Qed.
Lemma lem2308278 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2308280 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2308279) (@lem2308278 x y)). Qed.
Lemma lem2308281 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem2308282 (x : int) (y : int) (n : nat) : (term9 x y n) = (term10 x y n).
Proof. exact (MK_COMB (@lem2308280 x y) (@lem2308281 n)). Qed.
Lemma lem2308283 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308284 (x : int) (y : int) (n : nat) : (term11 x y n) = (term12 x y n).
Proof. exact (MK_COMB (@lem2308283) (@lem2308282 x y n)). Qed.
Lemma lem2308286 (x : int) (n : nat) : (term13 x n) = (term14 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308287 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308288 (x : int) (n : nat) : (term15 x n) = (term16 x n).
Proof. exact (MK_COMB (@lem2308287) (@lem2308286 x n)). Qed.
Lemma lem2308290 (x : int) (n : nat) : (term13 x n) = (term14 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308291 (y : int) (n : nat) : (term13 y n) = (term14 y n).
Proof. exact (@lem2308290 y n). Qed.
Lemma lem2308292 (x : int) (y : int) (n : nat) : (term17 x y n) = (term18 x y n).
Proof. exact (MK_COMB (@lem2308288 x n) (@lem2308291 y n)). Qed.
Lemma lem2308294 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308295 (x : int) (y : int) (n : nat) : (term18 x y n) = (term19 x y n).
Proof. exact (@lem2308294 (int_pow x n) (int_pow y n)). Qed.
Lemma lem2308296 (x : int) (y : int) (n : nat) : (term17 x y n) = (term19 x y n).
Proof. exact (TRANS (@lem2308292 x y n) (@lem2308295 x y n)). Qed.
Lemma lem2308297 (x : int) (y : int) (n : nat) : (term5 x y n) = (term20 x y n).
Proof. exact (MK_COMB (@lem2308284 x y n) (@lem2308296 x y n)). Qed.
Lemma lem2308298 (x : int) (y : int) (n : nat) : term20 x y n.
Proof. exact (EQ_MP (@lem2308297 x y n) (@lem2308276 x y n)). Qed.
Lemma lem2308299 (x : int) (n : nat) : term21 x n.
Proof. exact (fun y : int => @lem2308298 x y n). Qed.
Lemma lem2308300 (n : nat) : term22 n.
Proof. exact (fun x : int => @lem2308299 x n). Qed.
Lemma lem2308301 : term23.
Proof. exact (fun n : nat => @lem2308300 n). Qed.
