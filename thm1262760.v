Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1262760_term_abbrevs.
Lemma lem1262760 (r : nat -> nat) : (is_nadd r) = ((term0 r) = r).
Proof. exact (@axiom_20 r). Qed.
