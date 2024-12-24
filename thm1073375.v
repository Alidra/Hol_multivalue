Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1073375_term_abbrevs.
Require Import PAIR_EQ_spec.
Lemma lem1073366 {A B : Type'} (x : A) : term0 A B x.
Proof. exact (@lem47438 A B x). Qed.
Lemma lem1073367 {A B : Type'} (x : A) : (term0 A B x) = (term1 A B x).
Proof. exact (eq_refl (term0 A B x)). Qed.
Lemma lem1073368 {A B : Type'} (x : A) : term1 A B x.
Proof. exact (EQ_MP (@lem1073367 A B x) (@lem1073366 A B x)). Qed.
Lemma lem1073369 {A B : Type'} (x : A) (y : B) : term2 A B x y.
Proof. exact (@lem1073368 A B x y). Qed.
Lemma lem1073370 {A B : Type'} (x : A) (y : B) : (term2 A B x y) = (term3 A B x y).
Proof. exact (eq_refl (term2 A B x y)). Qed.
Lemma lem1073371 {A B : Type'} (x : A) (y : B) : term3 A B x y.
Proof. exact (EQ_MP (@lem1073370 A B x y) (@lem1073369 A B x y)). Qed.
Lemma lem1073372 {A B : Type'} (x : A) (y : B) (a : A) : term4 A B x y a.
Proof. exact (@lem1073371 A B x y a). Qed.
Lemma lem1073373 {A B : Type'} (x : A) (a : A) (y : B) : (term4 A B x y a) = (term5 A B x a y).
Proof. exact (eq_refl (term4 A B x y a)). Qed.
Lemma lem1073374 {A B : Type'} (x : A) (a : A) (y : B) : term5 A B x a y.
Proof. exact (EQ_MP (@lem1073373 A B x a y) (@lem1073372 A B x y a)). Qed.
Lemma lem1073375 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term6 A B x a y b.
Proof. exact (@lem1073374 A B x a y b). Qed.
