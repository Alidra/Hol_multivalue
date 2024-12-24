Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm513146_term_abbrevs.
Require Import thm513091_spec.
Lemma lem513144 (n : nat) : term0 n.
Proof. exact (@lem513091 n). Qed.
Lemma lem513145 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem513146 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem513145 n) (@lem513144 n)). Qed.
