Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259223_term_abbrevs.
Require Import thm1253868_spec.
Require Import thm1258895_spec.
Lemma lem1259223 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : term0 p q d' d'' d'''.
Proof. exact (EQ_MP (@lem1253868 p q d' d'' d''') (@lem1258895 d'' d' d''')). Qed.
