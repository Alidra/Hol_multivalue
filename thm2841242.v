Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841242_term_abbrevs.
Require Import INT_OF_NUM_MUL_spec.
Lemma lem2841240 (k : nat) : term0 k.
Proof. exact (@lem2307381 (NUMERAL k)). Qed.
Lemma lem2841241 (k : nat) : (term0 k) = (term1 k).
Proof. exact (eq_refl (term0 k)). Qed.
Lemma lem2841242 (k : nat) : term1 k.
Proof. exact (EQ_MP (@lem2841241 k) (@lem2841240 k)). Qed.
