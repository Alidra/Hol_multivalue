Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm161359_term_abbrevs.
Require Import thm161358_spec.
Lemma lem161359 : term0.
Proof. exact (fun m : nat => @lem161358 m). Qed.
