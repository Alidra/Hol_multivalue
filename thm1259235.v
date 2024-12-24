Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259235_term_abbrevs.
Require Import thm1249859_spec.
Require Import thm1258513_spec.
Lemma lem1259235 (d''' : nat) (p : nat) (d'' : nat) (d' : nat) : term0 d''' p d'' d'.
Proof. exact (EQ_MP (@lem1249859 d''' p d'' d') (@lem1258513 d''')). Qed.
