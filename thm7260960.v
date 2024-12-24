Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7260960_term_abbrevs.
Lemma lem7260960 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term0 _132349 f s g) = (term1 _132349 f s g).
Proof. exact (eq_refl (term0 _132349 f s g)). Qed.
