Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259231_term_abbrevs.
Require Import thm1251039_spec.
Require Import thm1258653_spec.
Lemma lem1259231 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : term0 n d' d''' d''.
Proof. exact (EQ_MP (@lem1251039 n d' d''' d'') (@lem1258653 d'' d' d''')). Qed.
