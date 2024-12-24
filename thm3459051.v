Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3459051_term_abbrevs.
Require Import thm3459034_spec.
Require Import thm3459035_spec.
Lemma lem3459048 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3459035 A s t) (@lem3459034 A s t)). Qed.
Lemma lem3459049 {_89837 : Type'} (s : _89837 -> Prop) (t : _89837 -> Prop) : (s = t) = (term0 _89837 s t).
Proof. exact (@lem3459048 _89837 s t). Qed.
Lemma lem3459050 {_89837 _89861 _89862 _89863 : Type'} (P : type1517 _89861 _89862 _89863) (f : type1524 _89837 _89861 _89862 _89863) : ((term1 _89837 _89861 _89862 _89863 P f) = (term2 _89837 _89861 _89862 _89863 P f)) = (term3 _89837 _89861 _89862 _89863 P f).
Proof. exact (@lem3459049 _89837 (term1 _89837 _89861 _89862 _89863 P f) (term2 _89837 _89861 _89862 _89863 P f)). Qed.
Lemma lem3459051 {_89837 _89861 _89862 _89863 : Type'} (P : type1517 _89861 _89862 _89863) (f : type1524 _89837 _89861 _89862 _89863) : (term3 _89837 _89861 _89862 _89863 P f) = ((term1 _89837 _89861 _89862 _89863 P f) = (term2 _89837 _89861 _89862 _89863 P f)).
Proof. exact (SYM (@lem3459050 _89837 _89861 _89862 _89863 P f)). Qed.
