Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2528727_term_abbrevs.
Require Import thm2528721_spec.
Require Import thm2528722_spec.
Lemma lem2528725 (m : int) (n : int) (p : int) : ((rem m p) = (rem n p)) = (term0 m n p).
Proof. exact (EQ_MP (@lem2528722 m n p) (@lem2528721 m n p)). Qed.
Lemma lem2528726 (p : int) (m : int) (n : int) : ((term1 m p n) = (rem m n)) = (term2 p m n).
Proof. exact (@lem2528725 (term3 m n p) m n). Qed.
Lemma lem2528727 (p : int) (m : int) (n : int) : (term2 p m n) = ((term1 m p n) = (rem m n)).
Proof. exact (SYM (@lem2528726 p m n)). Qed.
