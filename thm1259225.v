Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259225_term_abbrevs.
Require Import thm1252920_spec.
Require Import thm1258807_spec.
Lemma lem1259225 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : term0 m q d' d'' d'''.
Proof. exact (EQ_MP (@lem1252920 m q d' d'' d''') (@lem1258807 d' d''')). Qed.
