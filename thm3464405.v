Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3464405_term_abbrevs.
Require Import thm3464404_spec.
Lemma lem3464405 {_89711 _89725 : Type'} : term0 _89711 _89725.
Proof. exact (fun P : _89725 -> Prop => @lem3464404 _89711 _89725 P). Qed.
