Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_ONE_REP_term_abbrevs.
Lemma lem15711 : True.
Proof. exact (Logic.I). Qed.
Lemma lem15712 : term0.
Proof. exact (ex_intro term1 True (@lem15711)). Qed.
