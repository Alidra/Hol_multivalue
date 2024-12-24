Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7260962_term_abbrevs.
Lemma lem7260962 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : term0 _137613 s f g.
Proof. exact (h1). Qed.
