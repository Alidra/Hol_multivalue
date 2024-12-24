Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184736_term_abbrevs.
Require Import thm3184735_spec.
Lemma lem3184736 {_83095 : Type'} : term0 _83095.
Proof. exact (fun p : _83095 -> Prop => @lem3184735 _83095 p). Qed.
