Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21596_term_abbrevs.
Require Import thm21529_spec.
Require Import thm21568_spec.
Lemma lem21596 (b : Prop) (a : Prop) (h1 : a = True) : term0 b a.
Proof. exact (EQ_MP (@lem21529 b a h1) (@lem21568 b)). Qed.
