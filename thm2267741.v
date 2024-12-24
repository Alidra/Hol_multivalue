Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2267741_term_abbrevs.
Lemma lem2267741 (r : real) : (term0 r) = ((integer r) = ((term1 r) = r)).
Proof. exact (eq_refl (term0 r)). Qed.
