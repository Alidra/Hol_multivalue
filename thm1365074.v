Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm0_spec.
Require Import thm1365073_spec.
Lemma lem1365074 : (True /\ False) = False.
Proof. exact (EQ_MP (@lem1365073) (@lem0)). Qed.
