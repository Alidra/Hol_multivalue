Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259233_term_abbrevs.
Require Import thm1250376_spec.
Require Import thm1258565_spec.
Lemma lem1259233 (d''' : nat) (d' : nat) (p : nat) (d'' : nat) : term0 d''' d' p d''.
Proof. exact (EQ_MP (@lem1250376 d''' d' p d'') (@lem1258565 d''' d')). Qed.
