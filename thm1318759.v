Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318759_term_abbrevs.
Require Import thm1318748_spec.
Lemma lem1318758 : term0.
Proof. exact (proj1 (@lem1318748)). Qed.
Lemma lem1318759 (P : hreal -> Prop) : term1 P.
Proof. exact (@lem1318758 P). Qed.
