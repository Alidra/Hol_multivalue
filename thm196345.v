Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm196345_term_abbrevs.
Require Import thm196344_spec.
Lemma lem196345 : term0.
Proof. exact (fun m : nat => @lem196344 m). Qed.
