Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm618_term_abbrevs.
Require Import thm616_spec.
Require Import thm617_spec.
Lemma lem618 (q : Prop) (p : Prop) (r : Prop) : (term0 p q r) = (term0 q p r).
Proof. exact (EQ_MP (@lem617 q p r) (@lem616 p q r)). Qed.
