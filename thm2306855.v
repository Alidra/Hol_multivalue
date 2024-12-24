Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2306855_term_abbrevs.
Require Import thm2306854_spec.
Lemma lem2306855 : term0.
Proof. exact (fun x : nat => @lem2306854 x). Qed.
