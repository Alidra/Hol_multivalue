Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16463_term_abbrevs.
Require Import thm16462_spec.
Lemma lem16463 (t : Prop) : term0 t.
Proof. exact (proj2 (@lem16462 t)). Qed.
