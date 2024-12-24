Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184713_term_abbrevs.
Require Import thm3184695_spec.
Lemma lem3184713 {_83152 : Type'} (p : _83152 -> Prop) : term0 _83152 p.
Proof. exact (fun x : _83152 => @lem3184695 _83152 p x). Qed.
