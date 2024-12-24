Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259401_term_abbrevs.
Require Import thm1248598_spec.
Require Import thm1259369_spec.
Lemma lem1259401 (d : nat) (d' : nat) (p : nat) (d'' : nat) (h1 : (term0 p d d') = (Nat.add p d'')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248598 d d' d'') (@lem1259369 d d' p d'' h1)). Qed.
