Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1344313_term_abbrevs.
Require Import thm1344308_spec.
Lemma lem1344313 (x : real) : term0 x.
Proof. exact (@lem1344308 x). Qed.
