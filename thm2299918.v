Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299918_term_abbrevs.
Require Import thm2299752_spec.
Lemma lem2299918 (n : nat) : term0 n.
Proof. exact (@lem2299752 n). Qed.
