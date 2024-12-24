Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1101587_term_abbrevs.
Require Import thm1101584_spec.
Lemma lem1101586 {_25328 : Type'} : term0 _25328.
Proof. exact (proj1 (@lem1101584 _25328)). Qed.
Lemma lem1101587 {_25328 : Type'} (P : _25328 -> Prop) : term1 _25328 P.
Proof. exact (@lem1101586 _25328 P). Qed.
