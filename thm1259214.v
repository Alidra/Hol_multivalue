Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259214_term_abbrevs.
Require Import thm1257676_spec.
Require Import thm1259169_spec.
Lemma lem1259214 (m : nat) (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : term0 m d''' n d'' d'.
Proof. exact (EQ_MP (@lem1257676 m d''' n d'' d') (@lem1259169 d'' d' d''')). Qed.
