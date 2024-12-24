Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259215_term_abbrevs.
Require Import thm1257154_spec.
Require Import thm1259125_spec.
Lemma lem1259215 (m : nat) (d'' : nat) (d''' : nat) (q : nat) (d' : nat) : term0 m d'' d''' q d'.
Proof. exact (EQ_MP (@lem1257154 m d'' d''' q d') (@lem1259125 d' d''')). Qed.
