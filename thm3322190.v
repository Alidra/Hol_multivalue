Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3322190_term_abbrevs.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3322179 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3322180 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) : (s = t) = (term0 _86807 s t).
Proof. exact (@lem3322179 _86807 s t). Qed.
Lemma lem3322181 {_86807 : Type'} (s : _86807 -> Prop) : ((term1 _86807 s) = s) = (term2 _86807 s).
Proof. exact (@lem3322180 _86807 (term1 _86807 s) s). Qed.
Lemma lem3322190 {_86807 : Type'} (s : _86807 -> Prop) : (term2 _86807 s) = ((term1 _86807 s) = s).
Proof. exact (SYM (@lem3322181 _86807 s)). Qed.
