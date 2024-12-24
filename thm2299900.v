Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299900_term_abbrevs.
Require Import thm2299800_spec.
Lemma lem2299900 (x : int) : term0 x.
Proof. exact (@lem2299800 x). Qed.
