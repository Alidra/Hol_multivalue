Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211641_term_abbrevs.
Lemma lem3211641 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term0 _83095 p x) = ((term1 _83095 x p) = (p x)).
Proof. exact (eq_refl (term0 _83095 p x)). Qed.
