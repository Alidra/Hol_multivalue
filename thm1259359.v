Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259359_term_abbrevs.
Require Import thm1249051_spec.
Require Import thm1249079_spec.
Require Import thm1259231_spec.
Require Import thm69_spec.
Lemma lem1259355 (d''' : nat) (n : nat) (d' : nat) (d : nat) (d'' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : n = (term1 n d' d d'')) : False.
Proof. exact (@lem1259231 n d' d''' d'' (@lem1249079 d''' n d' d d'' h1 h2)). Qed.
Lemma lem1259356 (n : nat) (d' : nat) (d : nat) (d'' : nat) (h1 : term2 d d' d'') (h2 : n = (term1 n d' d d'')) : False.
Proof. exact (ex_elim (@lem1249051 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259355 d''' n d' d d'' h0 h2)). Qed.
Lemma lem1259357 (n : nat) (d' : nat) (d : nat) (d'' : nat) (h1 : n = (term1 n d' d d'')) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259356 n d' d d'' h0 h1). Qed.
Lemma lem1259358 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259359 (n : nat) (d' : nat) (d : nat) (d'' : nat) (h1 : n = (term1 n d' d d'')) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259358 d d' d'') (@lem1259357 n d' d d'' h1)). Qed.
