Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_1_term_abbrevs.
Require Import thm3354723_spec.
Require Import thm3355403_spec.
Lemma lem3355404 {_87240 : Type'} (s : _87240 -> Prop) : (term0 _87240 s) = s.
Proof. exact (EQ_MP (@lem3354723 _87240 s) (@lem3355403 _87240 s)). Qed.
