Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3070925_term_abbrevs.
Require Import INT_ABS_ABS_spec.
Lemma lem3070925 (x : int) : term0 x.
Proof. exact (@lem2300012 x). Qed.
