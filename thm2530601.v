Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2530601_term_abbrevs.
Require Import thm2530600_spec.
Lemma lem2530601 : term0.
Proof. exact (fun m : int => @lem2530600 m). Qed.
