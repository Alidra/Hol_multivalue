Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm912741_term_abbrevs.
Require Import thm709031_spec.
Require Import thm709039_spec.
Lemma lem912741 : term0 = term1.
Proof. exact (TRANS (@lem709031) (@lem709039)). Qed.
