Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259274_term_abbrevs.
Require Import thm1249544_spec.
Require Import thm1249572_spec.
Require Import thm1259214_spec.
Require Import thm69_spec.
Lemma lem1259270 (d''' : nat) (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add m n) = (term1 m d q d')) : False.
Proof. exact (@lem1259214 m d''' n d'' d' (@lem1249572 d''' d'' n m d q d' h1 h2 h3)). Qed.
Lemma lem1259271 (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : term2 d d' d'') (h2 : q = (Nat.add n d'')) (h3 : (Nat.add m n) = (term1 m d q d')) : False.
Proof. exact (ex_elim (@lem1249544 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259270 d''' d'' n m d q d' h0 h2 h3)). Qed.
Lemma lem1259272 (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (Nat.add m n) = (term1 m d q d')) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259271 d'' n m d q d' h0 h1 h2). Qed.
Lemma lem1259273 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259274 (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (Nat.add m n) = (term1 m d q d')) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259273 d d' d'') (@lem1259272 d'' n m d q d' h1 h2)). Qed.
