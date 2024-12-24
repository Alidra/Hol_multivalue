Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm0_spec.
Require Import thm10176_spec.
Lemma lem10177 : (~ True) = False.
Proof. exact (EQ_MP (@lem10176) (@lem0)). Qed.
