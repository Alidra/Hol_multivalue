Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6920431_spec.
Require Import thm6921992_spec.
Lemma lem6921993 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
