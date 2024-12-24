Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259364_term_abbrevs.
Require Import thm1249022_spec.
Require Import thm1249050_spec.
Require Import thm1259232_spec.
Require Import thm69_spec.
Lemma lem1259360 (d''' : nat) (p : nat) (d : nat) (d' : nat) (d'' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : p = (term1 p d d' d'')) : False.
Proof. exact (@lem1259232 p d''' d' d'' (@lem1249050 d''' p d d' d'' h1 h2)). Qed.
Lemma lem1259361 (p : nat) (d : nat) (d' : nat) (d'' : nat) (h1 : term2 d d' d'') (h2 : p = (term1 p d d' d'')) : False.
Proof. exact (ex_elim (@lem1249022 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259360 d''' p d d' d'' h0 h2)). Qed.
Lemma lem1259362 (p : nat) (d : nat) (d' : nat) (d'' : nat) (h1 : p = (term1 p d d' d'')) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259361 p d d' d'' h0 h1). Qed.
Lemma lem1259363 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259364 (p : nat) (d : nat) (d' : nat) (d'' : nat) (h1 : p = (term1 p d d' d'')) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259363 d d' d'') (@lem1259362 p d d' d'' h1)). Qed.
