Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm48213_term_abbrevs.
Require Import SND_spec.
Lemma lem48210 {A B : Type'} (x : A) : term0 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem48211 {A B : Type'} (x : A) : (term0 A B x) = (term1 A B x).
Proof. exact (eq_refl (term0 A B x)). Qed.
Lemma lem48212 {A B : Type'} (x : A) : term1 A B x.
Proof. exact (EQ_MP (@lem48211 A B x) (@lem48210 A B x)). Qed.
Lemma lem48213 {A B : Type'} (x : A) (y : B) : term2 A B x y.
Proof. exact (@lem48212 A B x y). Qed.
