Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1491_term_abbrevs.
Require Import thm32_spec.
Lemma lem1491 : term0 = ((~ True) = False).
Proof. exact (@lem32 (~ True) False). Qed.
