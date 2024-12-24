Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm822_term_abbrevs.
Require Import thm32_spec.
Lemma lem822 (p : Prop) (q : Prop) : (term0 p q) = ((term1 p q) = (p \/ q)).
Proof. exact (@lem32 (term1 p q) (p \/ q)). Qed.
