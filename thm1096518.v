Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1096518_term_abbrevs.
Require Import thm1096517_spec.
Lemma lem1096518 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem1096517 A)). Qed.
