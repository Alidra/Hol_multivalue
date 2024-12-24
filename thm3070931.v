Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3070931_term_abbrevs.
Require Import thm7_spec.
Lemma lem3070931 (x : int) : (term0 x) = ((term0 x) = True).
Proof. exact (@lem7 (term0 x)). Qed.
