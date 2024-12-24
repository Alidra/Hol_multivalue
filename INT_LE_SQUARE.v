Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_SQUARE_term_abbrevs.
Require Import REAL_LE_SQUARE_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303281 (x : int) : term0 x.
Proof. exact (@lem1382902 (real_of_int x)). Qed.
Lemma lem2303282 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303283 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303282 x) (@lem2303281 x)). Qed.
Lemma lem2303285 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303286 : term3 = term4.
Proof. exact (@lem2303285 (NUMERAL 0)). Qed.
Lemma lem2303287 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303288 : term5 = term6.
Proof. exact (MK_COMB (@lem2303287) (@lem2303286)). Qed.
Lemma lem2303290 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2303291 (x : int) : (term9 x) = (term10 x).
Proof. exact (@lem2303290 x x). Qed.
Lemma lem2303292 (x : int) : (term1 x) = (term11 x).
Proof. exact (MK_COMB (@lem2303288) (@lem2303291 x)). Qed.
Lemma lem2303294 (x : int) (y : int) : (term12 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303295 (x : int) : (term11 x) = (term13 x).
Proof. exact (@lem2303294 term14 (int_mul x x)). Qed.
Lemma lem2303296 (x : int) : (term1 x) = (term13 x).
Proof. exact (TRANS (@lem2303292 x) (@lem2303295 x)). Qed.
Lemma lem2303297 (x : int) : term13 x.
Proof. exact (EQ_MP (@lem2303296 x) (@lem2303283 x)). Qed.
Lemma lem2303298 : term15.
Proof. exact (fun x : int => @lem2303297 x). Qed.
