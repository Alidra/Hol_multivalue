Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259221_term_abbrevs.
Require Import thm1254597_spec.
Require Import thm1258959_spec.
Lemma lem1259221 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : term0 m q d' d'' d'''.
Proof. exact (EQ_MP (@lem1254597 m q d' d'' d''') (@lem1258959 d'' d''')). Qed.
