Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259226_term_abbrevs.
Require Import thm1252523_spec.
Require Import thm1258775_spec.
Lemma lem1259226 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : term0 p n d' d'' d'''.
Proof. exact (EQ_MP (@lem1252523 p n d' d'' d''') (@lem1258775 d'' d''')). Qed.
