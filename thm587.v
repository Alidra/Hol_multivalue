Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm587_term_abbrevs.
Require Import thm585_spec.
Require Import thm586_spec.
Lemma lem587 (p : Prop) (q : Prop) (r : Prop) : (term0 p q r) = (term1 p q r).
Proof. exact (EQ_MP (@lem586 p q r) (@lem585 p q r)). Qed.
