Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184708_term_abbrevs.
Require Import thm3184703_spec.
Lemma lem3184708 {_83169 : Type'} : term0 _83169.
Proof. exact (fun p : _83169 -> Prop => @lem3184703 _83169 p). Qed.
