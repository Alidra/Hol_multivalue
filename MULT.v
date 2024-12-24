Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MULT_term_abbrevs.
Require Import thm80977_spec.
Lemma lem80978 : term0.
Proof. exact (proj2 (@lem80977)). Qed.
Lemma lem80979 : term1.
Proof. exact (proj1 (@lem80977)). Qed.
Lemma lem80980 : term2.
Proof. exact (conj (@lem80979) (@lem80978)). Qed.
