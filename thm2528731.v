Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2528731_term_abbrevs.
Require Import thm2528721_spec.
Require Import thm2528722_spec.
Lemma lem2528729 (m : int) (n : int) (p : int) : ((rem m p) = (rem n p)) = (term0 m n p).
Proof. exact (EQ_MP (@lem2528722 m n p) (@lem2528721 m n p)). Qed.
Lemma lem2528730 (n : int) (m : int) (p : int) : ((term1 m n p) = (rem m p)) = (term2 n m p).
Proof. exact (@lem2528729 (term3 m n p) m p). Qed.
Lemma lem2528731 (n : int) (m : int) (p : int) : (term2 n m p) = ((term1 m n p) = (rem m p)).
Proof. exact (SYM (@lem2528730 n m p)). Qed.
