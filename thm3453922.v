Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3453922_term_abbrevs.
Require Import thm3453905_spec.
Require Import thm3453906_spec.
Lemma lem3453919 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3453906 A s t) (@lem3453905 A s t)). Qed.
Lemma lem3453920 {_89646 : Type'} (s : _89646 -> Prop) (t : _89646 -> Prop) : (s = t) = (term0 _89646 s t).
Proof. exact (@lem3453919 _89646 s t). Qed.
Lemma lem3453921 {_89646 _89670 _89671 _89672 : Type'} (P : type1517 _89670 _89671 _89672) (f : type1524 _89646 _89670 _89671 _89672) : ((term1 _89646 _89670 _89671 _89672 P f) = (term2 _89646 _89670 _89671 _89672 P f)) = (term3 _89646 _89670 _89671 _89672 P f).
Proof. exact (@lem3453920 _89646 (term1 _89646 _89670 _89671 _89672 P f) (term2 _89646 _89670 _89671 _89672 P f)). Qed.
Lemma lem3453922 {_89646 _89670 _89671 _89672 : Type'} (P : type1517 _89670 _89671 _89672) (f : type1524 _89646 _89670 _89671 _89672) : (term3 _89646 _89670 _89671 _89672 P f) = ((term1 _89646 _89670 _89671 _89672 P f) = (term2 _89646 _89670 _89671 _89672 P f)).
Proof. exact (SYM (@lem3453921 _89646 _89670 _89671 _89672 P f)). Qed.
