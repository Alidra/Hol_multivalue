Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259224_term_abbrevs.
Require Import thm1253393_spec.
Require Import thm1258851_spec.
Lemma lem1259224 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : term0 m n d' d'' d'''.
Proof. exact (EQ_MP (@lem1253393 m n d' d'' d''') (@lem1258851 d'' d' d''')). Qed.
