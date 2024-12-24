Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259264_term_abbrevs.
Require Import thm1249602_spec.
Require Import thm1249630_spec.
Require Import thm1259212_spec.
Require Import thm69_spec.
Lemma lem1259260 (d''' : nat) (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : q = (Nat.add n d'')) (h3 : (term1 m d q) = (term1 m n d')) : False.
Proof. exact (@lem1259212 d''' d'' m n d' (@lem1249630 d''' d'' d q m n d' h1 h2 h3)). Qed.
Lemma lem1259261 (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : term2 d d' d'') (h2 : q = (Nat.add n d'')) (h3 : (term1 m d q) = (term1 m n d')) : False.
Proof. exact (ex_elim (@lem1249602 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259260 d''' d'' d q m n d' h0 h2 h3)). Qed.
Lemma lem1259262 (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (term1 m d q) = (term1 m n d')) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259261 d'' d q m n d' h0 h1 h2). Qed.
Lemma lem1259263 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259264 (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (term1 m d q) = (term1 m n d')) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259263 d d' d'') (@lem1259262 d'' d q m n d' h1 h2)). Qed.
