Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248742_term_abbrevs.
Require Import thm1246902_spec.
Require Import thm1246903_spec.
Require Import thm1246908_spec.
Require Import thm1246909_spec.
Lemma lem1248728 (m : nat) (n : nat) : (Peano.le n m) = (term0 m n).
Proof. exact (EQ_MP (@lem1246909 m n) (@lem1246908 m n)). Qed.
Lemma lem1248729 (d' : nat) (d'' : nat) (d : nat) : (term1 d d' d'') = (term2 d' d'' d).
Proof. exact (@lem1248728 (Nat.add d' d'') d). Qed.
Lemma lem1248731 (n : nat) (m : nat) : (Peano.lt m n) = (term3 n m).
Proof. exact (EQ_MP (@lem1246903 n m) (@lem1246902 m n)). Qed.
Lemma lem1248732 (d : nat) (d' : nat) (d'' : nat) : (term4 d' d'' d) = (term5 d d' d'').
Proof. exact (@lem1248731 d (Nat.add d' d'')). Qed.
Lemma lem1248739 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1248740 (d : nat) (d' : nat) (d'' : nat) : (term2 d' d'' d) = (term6 d d' d'').
Proof. exact (MK_COMB (@lem1248739) (@lem1248732 d d' d'')). Qed.
Lemma lem1248741 (d : nat) (d' : nat) (d'' : nat) : (term1 d d' d'') = (term6 d d' d'').
Proof. exact (TRANS (@lem1248729 d' d'' d) (@lem1248740 d d' d'')). Qed.
Lemma lem1248742 (d : nat) (d' : nat) (d'' : nat) : (term6 d d' d'') = (term1 d d' d'').
Proof. exact (SYM (@lem1248741 d d' d'')). Qed.
