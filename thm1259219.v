Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259219_term_abbrevs.
Require Import thm1255398_spec.
Require Import thm1259001_spec.
Lemma lem1259219 (d''' : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : term0 d''' d'' p q d'.
Proof. exact (EQ_MP (@lem1255398 d''' d'' p q d') (@lem1259001 d''' d'')). Qed.
