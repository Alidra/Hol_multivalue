Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POS_EQ_SQUARE_term_abbrevs.
Require Import REAL_POS_EQ_SQUARE_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2307536 (x : int) : term0 x.
Proof. exact (@lem1944746 (real_of_int x)). Qed.
Lemma lem2307537 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2307538 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2307537 x) (@lem2307536 x)). Qed.
Lemma lem2307540 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307541 : term4 = term5.
Proof. exact (@lem2307540 (NUMERAL 0)). Qed.
Lemma lem2307542 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2307543 : term6 = term7.
Proof. exact (MK_COMB (@lem2307542) (@lem2307541)). Qed.
Lemma lem2307544 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2307545 (x : int) : (term1 x) = (term8 x).
Proof. exact (MK_COMB (@lem2307543) (@lem2307544 x)). Qed.
Lemma lem2307547 (x : int) (y : int) : (term9 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2307548 (x : int) : (term8 x) = (term10 x).
Proof. exact (@lem2307547 term11 x). Qed.
Lemma lem2307549 (x : int) : (term1 x) = (term10 x).
Proof. exact (TRANS (@lem2307545 x) (@lem2307548 x)). Qed.
Lemma lem2307550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2307551 (x : int) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem2307550) (@lem2307549 x)). Qed.
Lemma lem2307552 (x : int) : (term2 x) = (term2 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem2307553 (x : int) : ((term1 x) = (term2 x)) = ((term10 x) = (term2 x)).
Proof. exact (MK_COMB (@lem2307551 x) (@lem2307552 x)). Qed.
Lemma lem2307554 (x : int) : (term10 x) = (term2 x).
Proof. exact (EQ_MP (@lem2307553 x) (@lem2307538 x)). Qed.
Lemma lem2307555 : term14.
Proof. exact (fun x : int => @lem2307554 x). Qed.
