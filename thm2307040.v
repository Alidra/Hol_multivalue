Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2307040_term_abbrevs.
Require Import thm2307039_spec.
Lemma lem2307040 : term0.
Proof. exact (fun m : nat => @lem2307039 m). Qed.
