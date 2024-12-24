Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184703_term_abbrevs.
Require Import thm3183254_spec.
Lemma lem3184703 {_83169 : Type'} (p : _83169 -> Prop) : term0 _83169 p.
Proof. exact (fun x : _83169 => @lem3183254 _83169 p x). Qed.
