Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2530575_term_abbrevs.
Require Import thm2528727_spec.
Require Import thm2530573_spec.
Lemma lem2530575 (p : int) (m : int) (n : int) : (term0 m p n) = (rem m n).
Proof. exact (EQ_MP (@lem2528727 p m n) (@lem2530573 p m n)). Qed.
