Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm795_term_abbrevs.
Require Import thm793_spec.
Require Import thm794_spec.
Lemma lem795 (q : Prop) (p : Prop) (r : Prop) : (term0 p q r) = (term0 q p r).
Proof. exact (EQ_MP (@lem794 q p r) (@lem793 p q r)). Qed.
