Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259354_term_abbrevs.
Require Import thm1249080_spec.
Require Import thm1249108_spec.
Require Import thm1259230_spec.
Require Import thm69_spec.
Lemma lem1259350 (d''' : nat) (d' : nat) (d : nat) (n : nat) (d'' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : (term1 n d' d) = (Nat.add n d'')) : False.
Proof. exact (@lem1259230 d' d''' n d'' (@lem1249108 d''' d' d n d'' h1 h2)). Qed.
Lemma lem1259351 (d' : nat) (d : nat) (n : nat) (d'' : nat) (h1 : term2 d d' d'') (h2 : (term1 n d' d) = (Nat.add n d'')) : False.
Proof. exact (ex_elim (@lem1249080 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259350 d''' d' d n d'' h0 h2)). Qed.
Lemma lem1259352 (d' : nat) (d : nat) (n : nat) (d'' : nat) (h1 : (term1 n d' d) = (Nat.add n d'')) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259351 d' d n d'' h0 h1). Qed.
Lemma lem1259353 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259354 (d' : nat) (d : nat) (n : nat) (d'' : nat) (h1 : (term1 n d' d) = (Nat.add n d'')) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259353 d d' d'') (@lem1259352 d' d n d'' h1)). Qed.
