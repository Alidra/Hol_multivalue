Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258679_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246874_spec.
Require Import thm1246875_spec.
Require Import thm1823_spec.
Lemma lem1258657 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1258658 (d''' : nat) (d' : nat) : (term0 d''' d') = (term1 d''' d').
Proof. exact (@lem1258657 ((term2 d''' d') = (NUMERAL 0))). Qed.
Lemma lem1258662 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246875 m n) (@lem1246874 m n)). Qed.
Lemma lem1258663 (d''' : nat) (d' : nat) : (term2 d''' d') = (term5 d''' d').
Proof. exact (@lem1258662 d''' (Nat.add d' d')). Qed.
Lemma lem1258664 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258665 (d''' : nat) (d' : nat) : (term6 d''' d') = (term7 d''' d').
Proof. exact (MK_COMB (@lem1258664) (@lem1258663 d''' d')). Qed.
Lemma lem1258666 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1258667 (d''' : nat) (d' : nat) : ((term2 d''' d') = (NUMERAL 0)) = ((term5 d''' d') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1258665 d''' d') (@lem1258666)). Qed.
Lemma lem1258669 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1258670 (d''' : nat) (d' : nat) : ((term5 d''' d') = (NUMERAL 0)) = False.
Proof. exact (@lem1258669 (term8 d''' d')). Qed.
Lemma lem1258671 (d''' : nat) (d' : nat) : ((term2 d''' d') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1258667 d''' d') (@lem1258670 d''' d')). Qed.
Lemma lem1258672 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1258673 (d''' : nat) (d' : nat) : (term1 d''' d') = (~ False).
Proof. exact (MK_COMB (@lem1258672) (@lem1258671 d''' d')). Qed.
Lemma lem1258675 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1258676 (d''' : nat) (d' : nat) : (term1 d''' d') = True.
Proof. exact (TRANS (@lem1258673 d''' d') (@lem1258675)). Qed.
Lemma lem1258677 (d''' : nat) (d' : nat) : (term0 d''' d') = True.
Proof. exact (TRANS (@lem1258658 d''' d') (@lem1258676 d''' d')). Qed.
Lemma lem1258678 (d''' : nat) (d' : nat) : True = (term0 d''' d').
Proof. exact (SYM (@lem1258677 d''' d')). Qed.
Lemma lem1258679 (d''' : nat) (d' : nat) : term0 d''' d'.
Proof. exact (EQ_MP (@lem1258678 d''' d') (@lem0)). Qed.
