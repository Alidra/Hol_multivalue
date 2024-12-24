Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7637206_term_abbrevs.
Require Import thm7635341_spec.
Require Import thm7637129_spec.
Lemma lem7637180 {A B : Type'} : (@UNIV (finite_sum A B)) = (term0 A B).
Proof. exact (EQ_MP (@lem7635341 A B) (@lem7637129 A B)). Qed.
Lemma lem7637181 {M N : Type'} : (@UNIV (finite_sum M N)) = (term0 M N).
Proof. exact (@lem7637180 M N). Qed.
Lemma lem7637186 {M N : Type'} : (@HAS_SIZE (finite_sum M N)) = (@HAS_SIZE (finite_sum M N)).
Proof. exact (eq_refl (@HAS_SIZE (finite_sum M N))). Qed.
Lemma lem7637187 {M N : Type'} : (@HAS_SIZE (finite_sum M N) (@UNIV (finite_sum M N))) = (term1 M N).
Proof. exact (MK_COMB (@lem7637186 M N) (@lem7637181 M N)). Qed.
Lemma lem7637196 {M N : Type'} : (term2 M N) = (term2 M N).
Proof. exact (eq_refl (term2 M N)). Qed.
Lemma lem7637197 {M N : Type'} : (term3 M N) = (term4 M N).
Proof. exact (MK_COMB (@lem7637187 M N) (@lem7637196 M N)). Qed.
Lemma lem7637206 {M N : Type'} : (term4 M N) = (term3 M N).
Proof. exact (SYM (@lem7637197 M N)). Qed.
