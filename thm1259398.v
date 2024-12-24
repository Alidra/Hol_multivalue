Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259398_term_abbrevs.
Require Import thm1248646_spec.
Require Import thm1259354_spec.
Lemma lem1259398 (d' : nat) (d : nat) (n : nat) (d'' : nat) (h1 : (term0 n d' d) = (Nat.add n d'')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248646 d d' d'') (@lem1259354 d' d n d'' h1)). Qed.
