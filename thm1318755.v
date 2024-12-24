Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318755_term_abbrevs.
Require Import thm1318748_spec.
Lemma lem1318749 : term0.
Proof. exact (proj2 (@lem1318748)). Qed.
Lemma lem1318754 : term1.
Proof. exact (proj1 (@lem1318749)). Qed.
Lemma lem1318755 (P : hreal -> Prop) : term2 P.
Proof. exact (@lem1318754 P). Qed.
