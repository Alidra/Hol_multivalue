Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259217_term_abbrevs.
Require Import thm1256354_spec.
Require Import thm1259061_spec.
Lemma lem1259217 (p : nat) (d''' : nat) (q : nat) (d'' : nat) (d' : nat) : term0 p d''' q d'' d'.
Proof. exact (EQ_MP (@lem1256354 p d''' q d'' d') (@lem1259061 d'' d' d''')). Qed.
