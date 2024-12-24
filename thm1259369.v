Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259369_term_abbrevs.
Require Import thm1248993_spec.
Require Import thm1249021_spec.
Require Import thm1259233_spec.
Require Import thm69_spec.
Lemma lem1259365 (d''' : nat) (d : nat) (d' : nat) (p : nat) (d'' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : (term1 p d d') = (Nat.add p d'')) : False.
Proof. exact (@lem1259233 d''' d' p d'' (@lem1249021 d''' d d' p d'' h1 h2)). Qed.
Lemma lem1259366 (d : nat) (d' : nat) (p : nat) (d'' : nat) (h1 : term2 d d' d'') (h2 : (term1 p d d') = (Nat.add p d'')) : False.
Proof. exact (ex_elim (@lem1248993 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259365 d''' d d' p d'' h0 h2)). Qed.
Lemma lem1259367 (d : nat) (d' : nat) (p : nat) (d'' : nat) (h1 : (term1 p d d') = (Nat.add p d'')) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259366 d d' p d'' h0 h1). Qed.
Lemma lem1259368 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259369 (d : nat) (d' : nat) (p : nat) (d'' : nat) (h1 : (term1 p d d') = (Nat.add p d'')) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259368 d d' d'') (@lem1259367 d d' p d'' h1)). Qed.
