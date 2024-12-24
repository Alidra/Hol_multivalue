Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3459023_term_abbrevs.
Lemma lem3459023 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term0 _83064 P x) = ((term1 _83064 x P) = (term2 _83064 P x)).
Proof. exact (eq_refl (term0 _83064 P x)). Qed.
