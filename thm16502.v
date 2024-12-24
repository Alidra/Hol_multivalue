Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16502_term_abbrevs.
Require Import thm10177_spec.
Require Import thm10185_spec.
Lemma lem16502 : term0.
Proof. exact (conj (@lem10177) (@lem10185)). Qed.
