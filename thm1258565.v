Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258565_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246874_spec.
Require Import thm1246875_spec.
Require Import thm1823_spec.
Lemma lem1258543 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1258544 (d''' : nat) (d' : nat) : (term0 d''' d') = (term1 d''' d').
Proof. exact (@lem1258543 ((term2 d''' d') = (NUMERAL 0))). Qed.
Lemma lem1258548 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246875 m n) (@lem1246874 m n)). Qed.
Lemma lem1258549 (d''' : nat) (d' : nat) : (term2 d''' d') = (term5 d''' d').
Proof. exact (@lem1258548 d''' (Nat.add d' d')). Qed.
Lemma lem1258550 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258551 (d''' : nat) (d' : nat) : (term6 d''' d') = (term7 d''' d').
Proof. exact (MK_COMB (@lem1258550) (@lem1258549 d''' d')). Qed.
Lemma lem1258552 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1258553 (d''' : nat) (d' : nat) : ((term2 d''' d') = (NUMERAL 0)) = ((term5 d''' d') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1258551 d''' d') (@lem1258552)). Qed.
Lemma lem1258555 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1258556 (d''' : nat) (d' : nat) : ((term5 d''' d') = (NUMERAL 0)) = False.
Proof. exact (@lem1258555 (term8 d''' d')). Qed.
Lemma lem1258557 (d''' : nat) (d' : nat) : ((term2 d''' d') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1258553 d''' d') (@lem1258556 d''' d')). Qed.
Lemma lem1258558 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1258559 (d''' : nat) (d' : nat) : (term1 d''' d') = (~ False).
Proof. exact (MK_COMB (@lem1258558) (@lem1258557 d''' d')). Qed.
Lemma lem1258561 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1258562 (d''' : nat) (d' : nat) : (term1 d''' d') = True.
Proof. exact (TRANS (@lem1258559 d''' d') (@lem1258561)). Qed.
Lemma lem1258563 (d''' : nat) (d' : nat) : (term0 d''' d') = True.
Proof. exact (TRANS (@lem1258544 d''' d') (@lem1258562 d''' d')). Qed.
Lemma lem1258564 (d''' : nat) (d' : nat) : True = (term0 d''' d').
Proof. exact (SYM (@lem1258563 d''' d')). Qed.
Lemma lem1258565 (d''' : nat) (d' : nat) : term0 d''' d'.
Proof. exact (EQ_MP (@lem1258564 d''' d') (@lem0)). Qed.
