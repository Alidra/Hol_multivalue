Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259397_term_abbrevs.
Require Import thm1248662_spec.
Require Import thm1259349_spec.
Lemma lem1259397 (d' : nat) (m : nat) (d : nat) (d'' : nat) (h1 : (Nat.add m d') = (term0 m d d'')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248662 d d' d'') (@lem1259349 d' m d d'' h1)). Qed.