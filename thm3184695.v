Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184695_term_abbrevs.
Require Import thm3183232_spec.
Require Import thm3184689_spec.
Lemma lem3184695 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term0 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem3183232 _83152 p x) (@lem3184689 _83152 p x)). Qed.
