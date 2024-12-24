Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259218_term_abbrevs.
Require Import thm1255830_spec.
Require Import thm1259017_spec.
Lemma lem1259218 (d''' : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : term0 d''' p n d'' d'.
Proof. exact (EQ_MP (@lem1255830 d''' p n d'' d') (@lem1259017 d''')). Qed.
