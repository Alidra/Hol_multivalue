Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259213_term_abbrevs.
Require Import thm1258084_spec.
Require Import thm1259185_spec.
Lemma lem1259213 (d''' : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : term0 d''' m q d'' d'.
Proof. exact (EQ_MP (@lem1258084 d''' m q d'' d') (@lem1259185 d''')). Qed.
