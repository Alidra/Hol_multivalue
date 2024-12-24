Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16464_term_abbrevs.
Require Import thm16463_spec.
Lemma lem16464 (t : Prop) : term0 t.
Proof. exact (proj2 (@lem16463 t)). Qed.
