Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259294_term_abbrevs.
Require Import thm1249428_spec.
Require Import thm1249456_spec.
Require Import thm1259218_spec.
Require Import thm69_spec.
Lemma lem1259290 (d''' : nat) (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : q = (Nat.add n d'')) (h3 : (term1 p d n) = (term1 p q d')) : False.
Proof. exact (@lem1259218 d''' p n d'' d' (@lem1249456 d''' d'' d n p q d' h1 h2 h3)). Qed.
Lemma lem1259291 (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : term2 d d' d'') (h2 : q = (Nat.add n d'')) (h3 : (term1 p d n) = (term1 p q d')) : False.
Proof. exact (ex_elim (@lem1249428 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259290 d''' d'' d n p q d' h0 h2 h3)). Qed.
Lemma lem1259292 (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (term1 p d n) = (term1 p q d')) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259291 d'' d n p q d' h0 h1 h2). Qed.
Lemma lem1259293 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259294 (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (term1 p d n) = (term1 p q d')) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259293 d d' d'') (@lem1259292 d'' d n p q d' h1 h2)). Qed.
