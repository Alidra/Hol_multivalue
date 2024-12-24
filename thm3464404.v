Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3464404_term_abbrevs.
Require Import thm3464378_spec.
Lemma lem3464404 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term0 _89711 _89725 P.
Proof. exact (fun f : type1470 _89711 _89725 => @lem3464378 _89711 _89725 P f). Qed.
