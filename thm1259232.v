Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259232_term_abbrevs.
Require Import thm1250723_spec.
Require Import thm1258609_spec.
Lemma lem1259232 (p : nat) (d''' : nat) (d' : nat) (d'' : nat) : term0 p d''' d' d''.
Proof. exact (EQ_MP (@lem1250723 p d''' d' d'') (@lem1258609 d'' d' d''')). Qed.
