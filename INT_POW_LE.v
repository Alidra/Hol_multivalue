Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_LE_term_abbrevs.
Require Import REAL_POW_LE_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2308189 (x : int) : term0 x.
Proof. exact (@lem1582434 (real_of_int x)). Qed.
Lemma lem2308190 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2308191 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2308190 x) (@lem2308189 x)). Qed.
Lemma lem2308192 (x : int) (n : nat) : term2 x n.
Proof. exact (@lem2308191 x n). Qed.
Lemma lem2308193 (x : int) (n : nat) : (term2 x n) = (term3 x n).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem2308194 (x : int) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem2308193 x n) (@lem2308192 x n)). Qed.
Lemma lem2308196 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308197 : term5 = term6.
Proof. exact (@lem2308196 (NUMERAL 0)). Qed.
Lemma lem2308198 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308199 : term7 = term8.
Proof. exact (MK_COMB (@lem2308198) (@lem2308197)). Qed.
Lemma lem2308200 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2308201 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2308199) (@lem2308200 x)). Qed.
Lemma lem2308203 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308204 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2308203 term13 x). Qed.
Lemma lem2308205 (x : int) : (term9 x) = (term12 x).
Proof. exact (TRANS (@lem2308201 x) (@lem2308204 x)). Qed.
Lemma lem2308206 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308207 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2308206) (@lem2308205 x)). Qed.
Lemma lem2308209 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308210 : term5 = term6.
Proof. exact (@lem2308209 (NUMERAL 0)). Qed.
Lemma lem2308211 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308212 : term7 = term8.
Proof. exact (MK_COMB (@lem2308211) (@lem2308210)). Qed.
Lemma lem2308214 (x : int) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308215 (x : int) (n : nat) : (term18 x n) = (term19 x n).
Proof. exact (MK_COMB (@lem2308212) (@lem2308214 x n)). Qed.
Lemma lem2308217 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308218 (x : int) (n : nat) : (term19 x n) = (term20 x n).
Proof. exact (@lem2308217 term13 (int_pow x n)). Qed.
Lemma lem2308219 (x : int) (n : nat) : (term18 x n) = (term20 x n).
Proof. exact (TRANS (@lem2308215 x n) (@lem2308218 x n)). Qed.
Lemma lem2308220 (x : int) (n : nat) : (term3 x n) = (term21 x n).
Proof. exact (MK_COMB (@lem2308207 x) (@lem2308219 x n)). Qed.
Lemma lem2308221 (x : int) (n : nat) : term21 x n.
Proof. exact (EQ_MP (@lem2308220 x n) (@lem2308194 x n)). Qed.
Lemma lem2308222 (x : int) : term22 x.
Proof. exact (fun n : nat => @lem2308221 x n). Qed.
Lemma lem2308223 : term23.
Proof. exact (fun x : int => @lem2308222 x). Qed.
