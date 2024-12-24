Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259234_term_abbrevs.
Require Import thm1250093_spec.
Require Import thm1258539_spec.
Lemma lem1259234 (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : term0 d'' d''' n d'.
Proof. exact (EQ_MP (@lem1250093 d'' d''' n d') (@lem1258539 d''' d'')). Qed.
