Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259229_term_abbrevs.
Require Import thm1251497_spec.
Require Import thm1258711_spec.
Lemma lem1259229 (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : term0 m d' d''' d''.
Proof. exact (EQ_MP (@lem1251497 m d' d''' d'') (@lem1258711 d'' d''')). Qed.
