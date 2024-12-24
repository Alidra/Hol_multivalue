Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1011992_term_abbrevs.
Require Import LE_REFL_spec.
Require Import thm0_spec.
Require Import thm1856_spec.
Require Import thm7_spec.
Lemma lem1011977 (n : nat) : term0 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem1011978 (n : nat) : (term0 n) = (Peano.le n n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1011979 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem1011978 n) (@lem1011977 n)). Qed.
Lemma lem1011980 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem1011983 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1011984 (n : nat) : ((term1 n) = True) = (term1 n).
Proof. exact (@lem1011983 (term1 n)). Qed.
Lemma lem1011986 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem1011980 n) (@lem1011979 n)). Qed.
Lemma lem1011987 (n : nat) : (term1 n) = True.
Proof. exact (@lem1011986 (NUMERAL n)). Qed.
Lemma lem1011988 (n : nat) : ((term1 n) = True) = True.
Proof. exact (TRANS (@lem1011984 n) (@lem1011987 n)). Qed.
Lemma lem1011989 (n : nat) : True = ((term1 n) = True).
Proof. exact (SYM (@lem1011988 n)). Qed.
Lemma lem1011992 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem1011989 n) (@lem0)). Qed.
