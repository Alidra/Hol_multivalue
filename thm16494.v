Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16494_term_abbrevs.
Require Import thm16493_spec.
Lemma lem16494 (t : Prop) : term0 t.
Proof. exact (proj2 (@lem16493 t)). Qed.
