Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21180_term_abbrevs.
Require Import thm21138_spec.
Require Import thm21160_spec.
Lemma lem21180 (p : Prop) (h1 : p = True) : (term0 p) = p.
Proof. exact (EQ_MP (@lem21138 p h1) (@lem21160)). Qed.
