Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1490_spec.
Require Import thm1491_spec.
Lemma lem1492 : (~ True) = False.
Proof. exact (EQ_MP (@lem1491) (@lem1490)). Qed.
