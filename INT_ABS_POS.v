Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_POS_term_abbrevs.
Require Import REAL_ABS_POS_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2300506 (x : int) : term0 x.
Proof. exact (@lem1532076 (real_of_int x)). Qed.
Lemma lem2300507 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300508 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300507 x) (@lem2300506 x)). Qed.
Lemma lem2300510 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300511 : term3 = term4.
Proof. exact (@lem2300510 (NUMERAL 0)). Qed.
Lemma lem2300512 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2300513 : term5 = term6.
Proof. exact (MK_COMB (@lem2300512) (@lem2300511)). Qed.
Lemma lem2300515 (x : int) : (term7 x) = (term8 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300516 (x : int) : (term1 x) = (term9 x).
Proof. exact (MK_COMB (@lem2300513) (@lem2300515 x)). Qed.
Lemma lem2300518 (x : int) (y : int) : (term10 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2300519 (x : int) : (term9 x) = (term11 x).
Proof. exact (@lem2300518 term12 (int_abs x)). Qed.
Lemma lem2300520 (x : int) : (term1 x) = (term11 x).
Proof. exact (TRANS (@lem2300516 x) (@lem2300519 x)). Qed.
Lemma lem2300521 (x : int) : term11 x.
Proof. exact (EQ_MP (@lem2300520 x) (@lem2300508 x)). Qed.
Lemma lem2300522 : term13.
Proof. exact (fun x : int => @lem2300521 x). Qed.
