Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1502_term_abbrevs.
Require Import thm32_spec.
Lemma lem1502 : term0 = ((~ False) = True).
Proof. exact (@lem32 (~ False) True). Qed.
