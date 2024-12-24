Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21105_term_abbrevs.
Require Import thm21052_spec.
Require Import thm21087_spec.
Lemma lem21105 (p : Prop) (h1 : p = True) : (term0 p) = (~ p).
Proof. exact (EQ_MP (@lem21052 p h1) (@lem21087)). Qed.
