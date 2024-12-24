Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259349_term_abbrevs.
Require Import thm1249109_spec.
Require Import thm1249137_spec.
Require Import thm1259229_spec.
Require Import thm69_spec.
Lemma lem1259345 (d''' : nat) (d' : nat) (m : nat) (d : nat) (d'' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : (Nat.add m d') = (term1 m d d'')) : False.
Proof. exact (@lem1259229 m d' d''' d'' (@lem1249137 d''' d' m d d'' h1 h2)). Qed.
Lemma lem1259346 (d' : nat) (m : nat) (d : nat) (d'' : nat) (h1 : term2 d d' d'') (h2 : (Nat.add m d') = (term1 m d d'')) : False.
Proof. exact (ex_elim (@lem1249109 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259345 d''' d' m d d'' h0 h2)). Qed.
Lemma lem1259347 (d' : nat) (m : nat) (d : nat) (d'' : nat) (h1 : (Nat.add m d') = (term1 m d d'')) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259346 d' m d d'' h0 h1). Qed.
Lemma lem1259348 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259349 (d' : nat) (m : nat) (d : nat) (d'' : nat) (h1 : (Nat.add m d') = (term1 m d d'')) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259348 d d' d'') (@lem1259347 d' m d d'' h1)). Qed.
