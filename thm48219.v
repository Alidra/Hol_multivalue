Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm48219_term_abbrevs.
Require Import FST_spec.
Lemma lem48216 {A B : Type'} (x : A) : term0 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem48217 {A B : Type'} (x : A) : (term0 A B x) = (term1 A B x).
Proof. exact (eq_refl (term0 A B x)). Qed.
Lemma lem48218 {A B : Type'} (x : A) : term1 A B x.
Proof. exact (EQ_MP (@lem48217 A B x) (@lem48216 A B x)). Qed.
Lemma lem48219 {A B : Type'} (x : A) (y : B) : term2 A B x y.
Proof. exact (@lem48218 A B x y). Qed.
