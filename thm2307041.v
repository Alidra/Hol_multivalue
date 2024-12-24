Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2307041_term_abbrevs.
Require Import thm2307014_spec.
Require Import thm2307040_spec.
Lemma lem2307041 : term0.
Proof. exact (conj (@lem2307040) (@lem2307014)). Qed.
