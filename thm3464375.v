Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3464375_term_abbrevs.
Require Import thm3459188_spec.
Require Import thm3460802_spec.
Lemma lem3464375 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term0 _89711 _89725 P f.
Proof. exact (EQ_MP (@lem3459188 _89711 _89725 P f) (@lem3460802 _89711 _89725 P f)). Qed.
