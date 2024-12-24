Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184697_term_abbrevs.
Require Import thm3183162_spec.
Require Import thm3184690_spec.
Lemma lem3184697 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term0 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3183162 _83095 p x) (@lem3184690 _83095 p x)). Qed.
