Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3453912_term_abbrevs.
Require Import thm3453905_spec.
Require Import thm3453906_spec.
Lemma lem3453909 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3453906 A s t) (@lem3453905 A s t)). Qed.
Lemma lem3453910 {_89520 : Type'} (s : _89520 -> Prop) (t : _89520 -> Prop) : (s = t) = (term0 _89520 s t).
Proof. exact (@lem3453909 _89520 s t). Qed.
Lemma lem3453911 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : ((term1 _89520 _89534 P f) = (term2 _89520 _89534 P f)) = (term3 _89520 _89534 P f).
Proof. exact (@lem3453910 _89520 (term1 _89520 _89534 P f) (term2 _89520 _89534 P f)). Qed.
Lemma lem3453912 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term3 _89520 _89534 P f) = ((term1 _89520 _89534 P f) = (term2 _89520 _89534 P f)).
Proof. exact (SYM (@lem3453911 _89520 _89534 P f)). Qed.
