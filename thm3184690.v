Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184690_term_abbrevs.
Require Import thm3183509_spec.
Require Import thm3184137_spec.
Lemma lem3184690 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term0 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3183509 _83095 p x) (@lem3184137 _83095 p x)). Qed.
