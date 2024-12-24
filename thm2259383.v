Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2259383_term_abbrevs.
Require Import integer_spec.
Lemma lem2259354 (x : real) : term0 x.
Proof. exact (@lem2259353 x). Qed.
Lemma lem2259355 (x : real) : (term0 x) = ((integer x) = (term1 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2259360 (x : real) : (integer x) = (term1 x).
Proof. exact (EQ_MP (@lem2259355 x) (@lem2259354 x)). Qed.
Lemma lem2259367 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2259368 (x : real) : (term2 x) = (term3 x).
Proof. exact (MK_COMB (@lem2259367) (@lem2259360 x)). Qed.
Lemma lem2259379 (x : real) : (term4 x) = (term4 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem2259380 (x : real) : ((integer x) = (term4 x)) = ((term1 x) = (term4 x)).
Proof. exact (MK_COMB (@lem2259368 x) (@lem2259379 x)). Qed.
Lemma lem2259383 (x : real) : ((term1 x) = (term4 x)) = ((integer x) = (term4 x)).
Proof. exact (SYM (@lem2259380 x)). Qed.
