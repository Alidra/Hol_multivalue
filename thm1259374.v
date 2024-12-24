Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259374_term_abbrevs.
Require Import thm1248964_spec.
Require Import thm1248992_spec.
Require Import thm1259234_spec.
Require Import thm69_spec.
Lemma lem1259370 (d''' : nat) (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : p = (Nat.add n d'')) (h3 : (Nat.add p d) = (Nat.add n d')) : False.
Proof. exact (@lem1259234 d'' d''' n d' (@lem1248992 d''' d'' p d n d' h1 h2 h3)). Qed.
Lemma lem1259371 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : term1 d d' d'') (h2 : p = (Nat.add n d'')) (h3 : (Nat.add p d) = (Nat.add n d')) : False.
Proof. exact (ex_elim (@lem1248964 d d' d'' h1) (fun d''' : nat => fun h0 : term2 d d' d'' d''' => @lem1259370 d''' d'' p d n d' h0 h2 h3)). Qed.
Lemma lem1259372 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : p = (Nat.add n d'')) (h2 : (Nat.add p d) = (Nat.add n d')) : term3 d d' d''.
Proof. exact (fun h0 : term1 d d' d'' => @lem1259371 d'' p d n d' h0 h1 h2). Qed.
Lemma lem1259373 (d : nat) (d' : nat) (d'' : nat) : (term3 d d' d'') = (term4 d d' d'').
Proof. exact (@lem69 (term1 d d' d'')). Qed.
Lemma lem1259374 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : p = (Nat.add n d'')) (h2 : (Nat.add p d) = (Nat.add n d')) : term4 d d' d''.
Proof. exact (EQ_MP (@lem1259373 d d' d'') (@lem1259372 d'' p d n d' h1 h2)). Qed.
