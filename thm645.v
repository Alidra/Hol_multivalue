Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm645_term_abbrevs.
Require Import thm643_spec.
Require Import thm644_spec.
Lemma lem645 (p : Prop) (q : Prop) : (term0 p q) = (p /\ q).
Proof. exact (EQ_MP (@lem644 p q) (@lem643 p q)). Qed.
