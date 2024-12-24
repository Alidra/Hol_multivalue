Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5418284_term_abbrevs.
Require Import thm5400860_spec.
Require Import thm5413112_spec.
Lemma lem5418284 (m : nat) (n : nat) (h1 : term0 m n) : term1 m n.
Proof. exact (@lem5413112 m n (@lem5400860 m n h1)). Qed.
