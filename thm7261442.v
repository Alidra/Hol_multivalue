Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7261442_term_abbrevs.
Require Import thm7261413_spec.
Lemma lem7261442 : term0.
Proof. exact (fun f : nat -> real => @lem7261413 f). Qed.
