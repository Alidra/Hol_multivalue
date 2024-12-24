Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184735_term_abbrevs.
Require Import thm3184697_spec.
Lemma lem3184735 {_83095 : Type'} (p : _83095 -> Prop) : term0 _83095 p.
Proof. exact (fun x : _83095 => @lem3184697 _83095 p x). Qed.
