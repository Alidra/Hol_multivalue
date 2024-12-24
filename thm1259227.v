Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259227_term_abbrevs.
Require Import thm1252107_spec.
Require Import thm1258743_spec.
Lemma lem1259227 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : term0 p q d' d'' d'''.
Proof. exact (EQ_MP (@lem1252107 p q d' d'' d''') (@lem1258743 d''')). Qed.
