Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_BOOL_THM_term_abbrevs.
Require Import thm11004_spec.
Require Import thm11005_spec.
Lemma lem11006 (P : Prop -> Prop) : (term0 P) = (term1 P).
Proof. exact (EQ_MP (@lem11005 P) (@lem11004 P)). Qed.
