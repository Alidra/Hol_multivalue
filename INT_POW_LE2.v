Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_LE2_term_abbrevs.
Require Import REAL_POW_LE2_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2308224 (n : nat) : term0 n.
Proof. exact (@lem1636714 n). Qed.
Lemma lem2308225 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308226 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2308225 n) (@lem2308224 n)). Qed.
Lemma lem2308227 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2308226 n (real_of_int x)). Qed.
Lemma lem2308228 (x : int) (n : nat) : (term2 n x) = (term3 x n).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2308229 (x : int) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem2308228 x n) (@lem2308227 n x)). Qed.
Lemma lem2308230 (x : int) (n : nat) (y : int) : term4 x n y.
Proof. exact (@lem2308229 x n (real_of_int y)). Qed.
Lemma lem2308231 (x : int) (y : int) (n : nat) : (term4 x n y) = (term5 x y n).
Proof. exact (eq_refl (term4 x n y)). Qed.
Lemma lem2308232 (x : int) (y : int) (n : nat) : term5 x y n.
Proof. exact (EQ_MP (@lem2308231 x y n) (@lem2308230 x n y)). Qed.
Lemma lem2308234 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308235 : term7 = term8.
Proof. exact (@lem2308234 (NUMERAL 0)). Qed.
Lemma lem2308236 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308237 : term9 = term10.
Proof. exact (MK_COMB (@lem2308236) (@lem2308235)). Qed.
Lemma lem2308238 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2308239 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2308237) (@lem2308238 x)). Qed.
Lemma lem2308241 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308242 (x : int) : (term12 x) = (term14 x).
Proof. exact (@lem2308241 term15 x). Qed.
Lemma lem2308243 (x : int) : (term11 x) = (term14 x).
Proof. exact (TRANS (@lem2308239 x) (@lem2308242 x)). Qed.
Lemma lem2308244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2308245 (x : int) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem2308244) (@lem2308243 x)). Qed.
Lemma lem2308247 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308248 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem2308245 x) (@lem2308247 x y)). Qed.
Lemma lem2308249 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308250 (x : int) (y : int) : (term20 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem2308249) (@lem2308248 x y)). Qed.
Lemma lem2308252 (x : int) (n : nat) : (term22 x n) = (term23 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308253 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308254 (x : int) (n : nat) : (term24 x n) = (term25 x n).
Proof. exact (MK_COMB (@lem2308253) (@lem2308252 x n)). Qed.
Lemma lem2308256 (x : int) (n : nat) : (term22 x n) = (term23 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308257 (y : int) (n : nat) : (term22 y n) = (term23 y n).
Proof. exact (@lem2308256 y n). Qed.
Lemma lem2308258 (x : int) (y : int) (n : nat) : (term26 x y n) = (term27 x y n).
Proof. exact (MK_COMB (@lem2308254 x n) (@lem2308257 y n)). Qed.
Lemma lem2308260 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308261 (x : int) (y : int) (n : nat) : (term27 x y n) = (term28 x y n).
Proof. exact (@lem2308260 (int_pow x n) (int_pow y n)). Qed.
Lemma lem2308262 (x : int) (y : int) (n : nat) : (term26 x y n) = (term28 x y n).
Proof. exact (TRANS (@lem2308258 x y n) (@lem2308261 x y n)). Qed.
Lemma lem2308263 (x : int) (y : int) (n : nat) : (term5 x y n) = (term29 x y n).
Proof. exact (MK_COMB (@lem2308250 x y) (@lem2308262 x y n)). Qed.
Lemma lem2308264 (x : int) (y : int) (n : nat) : term29 x y n.
Proof. exact (EQ_MP (@lem2308263 x y n) (@lem2308232 x y n)). Qed.
Lemma lem2308265 (x : int) (n : nat) : term30 x n.
Proof. exact (fun y : int => @lem2308264 x y n). Qed.
Lemma lem2308266 (n : nat) : term31 n.
Proof. exact (fun x : int => @lem2308265 x n). Qed.
Lemma lem2308267 : term32.
Proof. exact (fun n : nat => @lem2308266 n). Qed.
