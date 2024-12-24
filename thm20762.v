Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20762_term_abbrevs.
Require Import thm20708_spec.
Require Import thm20738_spec.
Lemma lem20762 (b : Prop) (a : Prop) (h1 : a = True) : (a \/ b) = (term0 b a).
Proof. exact (EQ_MP (@lem20708 b a h1) (@lem20738 b)). Qed.
