Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211610_term_abbrevs.
Lemma lem3211610 {A : Type'} (P : A -> Prop) (x : A) : (term0 A P x) = ((@IN A x P) = (P x)).
Proof. exact (eq_refl (term0 A P x)). Qed.
