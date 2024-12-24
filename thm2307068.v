Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2307068_term_abbrevs.
Require Import thm2307041_spec.
Require Import thm2307067_spec.
Lemma lem2307068 : term0.
Proof. exact (conj (@lem2307067) (@lem2307041)). Qed.
