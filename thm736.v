Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm736_term_abbrevs.
Require Import thm32_spec.
Lemma lem736 (q : Prop) (p : Prop) : (term0 p q) = ((p \/ q) = (q \/ p)).
Proof. exact (@lem32 (p \/ q) (q \/ p)). Qed.
