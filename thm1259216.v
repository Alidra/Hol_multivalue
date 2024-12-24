Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259216_term_abbrevs.
Require Import thm1256728_spec.
Require Import thm1259093_spec.
Lemma lem1259216 (p : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : term0 p d'' d''' n d'.
Proof. exact (EQ_MP (@lem1256728 p d'' d''' n d') (@lem1259093 d' d''')). Qed.
