Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_INSERT_term_abbrevs.
Require Import thm3324017_spec.
Require Import thm3325374_spec.
Lemma lem3325375 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term0 _86841 s u) = (term1 _86841 s u).
Proof. exact (EQ_MP (@lem3324017 _86841 s u) (@lem3325374 _86841 s u)). Qed.
