Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm161362_term_abbrevs.
Lemma lem161362 : term0 = term0.
Proof. exact (eq_refl term0). Qed.