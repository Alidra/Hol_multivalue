Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_GSPEC_term_abbrevs.
Require Import thm3464399_spec.
Require Import thm3464404_spec.
Lemma lem3464409 {_89711 _89725 : Type'} : term0 _89711 _89725.
Proof. exact (fun P : _89725 -> Prop => @lem3464404 _89711 _89725 P). Qed.
Lemma lem3464410 {_89711 _89725 _89769 _89788 _89789 _89837 _89861 _89862 _89863 : Type'} : term1 _89711 _89725 _89769 _89788 _89789 _89837 _89861 _89862 _89863.
Proof. exact (conj (@lem3464409 _89711 _89725) (@lem3464399 _89769 _89788 _89789 _89837 _89861 _89862 _89863)). Qed.
