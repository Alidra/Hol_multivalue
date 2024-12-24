Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINREC_term_abbrevs.
Require Import thm3791011_spec.
Require Import thm3791024_spec.
Require Import thm3791025_spec.
Lemma lem3791026 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term0 A B f b s a n) = (term1 A B b s n a f).
Proof. exact (EQ_MP (@lem3791025 A B b s n a f) (@lem3791024 A B b s n a f)). Qed.
Lemma lem3791027 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : term2 A B b s n a f.
Proof. exact (conj (@lem3791011 A B f s a b) (@lem3791026 A B b s n a f)). Qed.
