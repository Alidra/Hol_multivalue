Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3322101_term_abbrevs.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3322090 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3322091 {_86801 : Type'} (s : _86801 -> Prop) (t : _86801 -> Prop) : (s = t) = (term0 _86801 s t).
Proof. exact (@lem3322090 _86801 s t). Qed.
Lemma lem3322092 {_86801 : Type'} : ((@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801)) = (term1 _86801).
Proof. exact (@lem3322091 _86801 (@UNIONS _86801 (@EMPTY (_86801 -> Prop))) (@EMPTY _86801)). Qed.
Lemma lem3322101 {_86801 : Type'} : (term1 _86801) = ((@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801)).
Proof. exact (SYM (@lem3322092 _86801)). Qed.
