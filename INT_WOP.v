Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_WOP_term_abbrevs.
Require Import thm2338993_spec.
Require Import thm2339318_spec.
Lemma lem2339319 (P : int -> Prop) : (term0 P) = (term1 P).
Proof. exact (EQ_MP (@lem2338993 P) (@lem2339318 P)). Qed.
