Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259222_term_abbrevs.
Require Import thm1254205_spec.
Require Import thm1258927_spec.
Lemma lem1259222 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : term0 p n d' d'' d'''.
Proof. exact (EQ_MP (@lem1254205 p n d' d'' d''') (@lem1258927 d' d''')). Qed.
