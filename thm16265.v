Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16265_term_abbrevs.
Require Import thm32_spec.
Lemma lem16265 (P : unit -> Prop) : (term0 P) = ((term1 P) = (P tt)).
Proof. exact (@lem32 (term1 P) (P tt)). Qed.
