Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3354723_term_abbrevs.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3354712 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3354713 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) : (s = t) = (term0 _87240 s t).
Proof. exact (@lem3354712 _87240 s t). Qed.
Lemma lem3354714 {_87240 : Type'} (s : _87240 -> Prop) : ((term1 _87240 s) = s) = (term2 _87240 s).
Proof. exact (@lem3354713 _87240 (term1 _87240 s) s). Qed.
Lemma lem3354723 {_87240 : Type'} (s : _87240 -> Prop) : (term2 _87240 s) = ((term1 _87240 s) = s).
Proof. exact (SYM (@lem3354714 _87240 s)). Qed.
