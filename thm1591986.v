Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1591986_term_abbrevs.
Require Import thm1338986_spec.
Lemma lem1591986 (x : real) : term0 x.
Proof. exact (@lem1338986 x). Qed.
