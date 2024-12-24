Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NEG_LT0_term_abbrevs.
Require Import REAL_NEG_LT0_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2306551 (x : int) : term0 x.
Proof. exact (@lem1496731 (real_of_int x)). Qed.
Lemma lem2306552 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306553 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2306552 x) (@lem2306551 x)). Qed.
Lemma lem2306555 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306556 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2306557 (x : int) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem2306556) (@lem2306555 x)). Qed.
Lemma lem2306559 (n : nat) : (real_of_num n) = (term7 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306560 : term8 = term9.
Proof. exact (@lem2306559 (NUMERAL 0)). Qed.
Lemma lem2306561 (x : int) : (term1 x) = (term10 x).
Proof. exact (MK_COMB (@lem2306557 x) (@lem2306560)). Qed.
Lemma lem2306563 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306564 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2306563 (int_neg x) term13). Qed.
Lemma lem2306565 (x : int) : (term1 x) = (term12 x).
Proof. exact (TRANS (@lem2306561 x) (@lem2306564 x)). Qed.
Lemma lem2306566 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2306567 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2306566) (@lem2306565 x)). Qed.
Lemma lem2306569 (n : nat) : (real_of_num n) = (term7 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306570 : term8 = term9.
Proof. exact (@lem2306569 (NUMERAL 0)). Qed.
Lemma lem2306571 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2306572 : term16 = term17.
Proof. exact (MK_COMB (@lem2306571) (@lem2306570)). Qed.
Lemma lem2306573 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2306574 (x : int) : (term2 x) = (term18 x).
Proof. exact (MK_COMB (@lem2306572) (@lem2306573 x)). Qed.
Lemma lem2306576 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306577 (x : int) : (term18 x) = (term19 x).
Proof. exact (@lem2306576 term13 x). Qed.
Lemma lem2306578 (x : int) : (term2 x) = (term19 x).
Proof. exact (TRANS (@lem2306574 x) (@lem2306577 x)). Qed.
Lemma lem2306579 (x : int) : ((term1 x) = (term2 x)) = ((term12 x) = (term19 x)).
Proof. exact (MK_COMB (@lem2306567 x) (@lem2306578 x)). Qed.
Lemma lem2306580 (x : int) : (term12 x) = (term19 x).
Proof. exact (EQ_MP (@lem2306579 x) (@lem2306553 x)). Qed.
Lemma lem2306581 : term20.
Proof. exact (fun x : int => @lem2306580 x). Qed.
