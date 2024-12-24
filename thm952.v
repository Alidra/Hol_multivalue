Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm952_term_abbrevs.
Require Import thm32_spec.
Lemma lem952 (q : Prop) (p : Prop) (r : Prop) : (term0 p q r) = ((term1 p q r) = (term2 q p r)).
Proof. exact (@lem32 (term1 p q r) (term2 q p r)). Qed.
