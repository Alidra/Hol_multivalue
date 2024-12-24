Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import T_DEF_term_abbrevs.
Lemma lem1 : True = (term0 = term0).
Proof. exact (@T_def). Qed.
