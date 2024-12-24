Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1980266_term_abbrevs.
Lemma lem1980266 (y : real) (x : real) : (term0 y x) = ((real_gt x y) = (real_lt y x)).
Proof. exact (eq_refl (term0 y x)). Qed.
