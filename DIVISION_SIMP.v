Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVISION_SIMP_term_abbrevs.
Require Import thm161363_spec.
Require Import thm161368_spec.
Lemma lem161373 : term0.
Proof. exact (fun m : nat => @lem161368 m). Qed.
Lemma lem161374 : term1.
Proof. exact (conj (@lem161373) (@lem161363)). Qed.
