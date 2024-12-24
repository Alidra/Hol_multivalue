Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184718_term_abbrevs.
Require Import thm3184713_spec.
Lemma lem3184718 {_83152 : Type'} : term0 _83152.
Proof. exact (fun p : _83152 -> Prop => @lem3184713 _83152 p). Qed.
