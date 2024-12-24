Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259379_term_abbrevs.
Require Import thm1248935_spec.
Require Import thm1248963_spec.
Require Import thm1259235_spec.
Require Import thm69_spec.
Lemma lem1259375 (d''' : nat) (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : n = (Nat.add p d'')) (h3 : (Nat.add p d) = (Nat.add n d')) : False.
Proof. exact (@lem1259235 d''' p d'' d' (@lem1248963 d''' d'' p d n d' h1 h2 h3)). Qed.
Lemma lem1259376 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : term1 d d' d'') (h2 : n = (Nat.add p d'')) (h3 : (Nat.add p d) = (Nat.add n d')) : False.
Proof. exact (ex_elim (@lem1248935 d d' d'' h1) (fun d''' : nat => fun h0 : term2 d d' d'' d''' => @lem1259375 d''' d'' p d n d' h0 h2 h3)). Qed.
Lemma lem1259377 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : n = (Nat.add p d'')) (h2 : (Nat.add p d) = (Nat.add n d')) : term3 d d' d''.
Proof. exact (fun h0 : term1 d d' d'' => @lem1259376 d'' p d n d' h0 h1 h2). Qed.
Lemma lem1259378 (d : nat) (d' : nat) (d'' : nat) : (term3 d d' d'') = (term4 d d' d'').
Proof. exact (@lem69 (term1 d d' d'')). Qed.
Lemma lem1259379 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : n = (Nat.add p d'')) (h2 : (Nat.add p d) = (Nat.add n d')) : term4 d d' d''.
Proof. exact (EQ_MP (@lem1259378 d d' d'') (@lem1259377 d'' p d n d' h1 h2)). Qed.
