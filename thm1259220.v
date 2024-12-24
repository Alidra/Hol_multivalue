Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259220_term_abbrevs.
Require Import thm1254983_spec.
Require Import thm1258975_spec.
Lemma lem1259220 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : term0 m n d' d'' d'''.
Proof. exact (EQ_MP (@lem1254983 m n d' d'' d''') (@lem1258975 d''')). Qed.
