Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm823_term_abbrevs.
Require Import thm821_spec.
Require Import thm822_spec.
Lemma lem823 (p : Prop) (q : Prop) : (term0 p q) = (p \/ q).
Proof. exact (EQ_MP (@lem822 p q) (@lem821 p q)). Qed.
