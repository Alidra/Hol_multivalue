Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3459041_term_abbrevs.
Require Import thm3459034_spec.
Require Import thm3459035_spec.
Lemma lem3459038 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3459035 A s t) (@lem3459034 A s t)). Qed.
Lemma lem3459039 {_89711 : Type'} (s : _89711 -> Prop) (t : _89711 -> Prop) : (s = t) = (term0 _89711 s t).
Proof. exact (@lem3459038 _89711 s t). Qed.
Lemma lem3459040 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : ((term1 _89711 _89725 P f) = (term2 _89711 _89725 P f)) = (term3 _89711 _89725 P f).
Proof. exact (@lem3459039 _89711 (term1 _89711 _89725 P f) (term2 _89711 _89725 P f)). Qed.
Lemma lem3459041 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term3 _89711 _89725 P f) = ((term1 _89711 _89725 P f) = (term2 _89711 _89725 P f)).
Proof. exact (SYM (@lem3459040 _89711 _89725 P f)). Qed.
