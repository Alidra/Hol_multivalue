Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7261450_term_abbrevs.
Lemma lem7261450 {_137613 : Type'} (f : _137613 -> real) (s : _137613 -> Prop) (g : _137613 -> real) : (term0 _137613 f g s) = (term1 _137613 f s g).
Proof. exact (eq_refl (term0 _137613 f g s)). Qed.
