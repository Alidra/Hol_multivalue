Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7640394_term_abbrevs.
Require Import DIMINDEX_HAS_SIZE_FINITE_SUM_spec.
Require Import HAS_SIZE_spec.
Lemma lem7640380 {_100044 : Type'} (s : _100044 -> Prop) : term0 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem7640381 {_100044 : Type'} (s : _100044 -> Prop) : (term0 _100044 s) = (term1 _100044 s).
Proof. exact (eq_refl (term0 _100044 s)). Qed.
Lemma lem7640382 {_100044 : Type'} (s : _100044 -> Prop) : term1 _100044 s.
Proof. exact (EQ_MP (@lem7640381 _100044 s) (@lem7640380 _100044 s)). Qed.
Lemma lem7640383 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term2 _100044 s n.
Proof. exact (@lem7640382 _100044 s n). Qed.
Lemma lem7640384 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term2 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term3 _100044 s n)).
Proof. exact (eq_refl (term2 _100044 s n)). Qed.
Lemma lem7640387 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term3 _100044 s n).
Proof. exact (EQ_MP (@lem7640384 _100044 s n) (@lem7640383 _100044 s n)). Qed.
Lemma lem7640388 {M N : Type'} (s : type49 M N) (n : nat) : (@HAS_SIZE (finite_sum M N) s n) = (term4 M N s n).
Proof. exact (@lem7640387 (finite_sum M N) s n). Qed.
Lemma lem7640389 {M N : Type'} : (term5 M N) = (term6 M N).
Proof. exact (@lem7640388 M N (@UNIV (finite_sum M N)) (term7 M N)). Qed.
Lemma lem7640394 {M N : Type'} : term6 M N.
Proof. exact (EQ_MP (@lem7640389 M N) (@lem7640379 M N)). Qed.
