Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259279_term_abbrevs.
Require Import thm1249515_spec.
Require Import thm1249543_spec.
Require Import thm1259215_spec.
Require Import thm69_spec.
Lemma lem1259275 (d''' : nat) (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add m n) = (term1 m d q d')) : False.
Proof. exact (@lem1259215 m d'' d''' q d' (@lem1249543 d''' d'' n m d q d' h1 h2 h3)). Qed.
Lemma lem1259276 (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : term2 d d' d'') (h2 : n = (Nat.add q d'')) (h3 : (Nat.add m n) = (term1 m d q d')) : False.
Proof. exact (ex_elim (@lem1249515 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259275 d''' d'' n m d q d' h0 h2 h3)). Qed.
Lemma lem1259277 (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (Nat.add m n) = (term1 m d q d')) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259276 d'' n m d q d' h0 h1 h2). Qed.
Lemma lem1259278 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259279 (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (Nat.add m n) = (term1 m d q d')) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259278 d d' d'') (@lem1259277 d'' n m d q d' h1 h2)). Qed.
