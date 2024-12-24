Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2405763_term_abbrevs.
Require Import thm2405621_spec.
Lemma lem2405763 (x : nat) : term0 x.
Proof. exact (proj2 (@lem2405621 x)). Qed.
