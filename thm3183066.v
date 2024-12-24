Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183066_term_abbrevs.
Lemma lem3183066 {_83031 : Type'} (P : Prop) (v : _83031) (t : _83031) : (term0 _83031 P v t) = ((@SETSPEC _83031 v P t) = (term1 _83031 P v t)).
Proof. exact (eq_refl (term0 _83031 P v t)). Qed.
