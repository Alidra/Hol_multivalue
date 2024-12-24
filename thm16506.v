Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16506_term_abbrevs.
Require Import thm10187_spec.
Require Import thm10190_spec.
Lemma lem16505 : term0.
Proof. exact (EQ_MP (@lem10190) (@lem10187)). Qed.
Lemma lem16506 (t : Prop) : term1 t.
Proof. exact (@lem16505 t). Qed.
