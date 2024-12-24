Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm627_term_abbrevs.
Require Import thm32_spec.
Lemma lem627 (p : Prop) : (term0 p) = ((p /\ p) = p).
Proof. exact (@lem32 (p /\ p) p). Qed.
