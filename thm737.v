Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm735_spec.
Require Import thm736_spec.
Lemma lem737 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
