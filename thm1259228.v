Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259228_term_abbrevs.
Require Import thm1251719_spec.
Require Import thm1258727_spec.
Lemma lem1259228 (d''' : nat) (m : nat) (d' : nat) (d'' : nat) : term0 d''' m d' d''.
Proof. exact (EQ_MP (@lem1251719 d''' m d' d'') (@lem1258727 d''')). Qed.
