Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259230_term_abbrevs.
Require Import thm1251285_spec.
Require Import thm1258679_spec.
Lemma lem1259230 (d' : nat) (d''' : nat) (n : nat) (d'' : nat) : term0 d' d''' n d''.
Proof. exact (EQ_MP (@lem1251285 d' d''' n d'') (@lem1258679 d''' d')). Qed.
