Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3453917_term_abbrevs.
Require Import thm3453905_spec.
Require Import thm3453906_spec.
Lemma lem3453914 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3453906 A s t) (@lem3453905 A s t)). Qed.
Lemma lem3453915 {_89578 : Type'} (s : _89578 -> Prop) (t : _89578 -> Prop) : (s = t) = (term0 _89578 s t).
Proof. exact (@lem3453914 _89578 s t). Qed.
Lemma lem3453916 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : ((term1 _89578 _89597 _89598 P f) = (term2 _89578 _89597 _89598 P f)) = (term3 _89578 _89597 _89598 P f).
Proof. exact (@lem3453915 _89578 (term1 _89578 _89597 _89598 P f) (term2 _89578 _89597 _89598 P f)). Qed.
Lemma lem3453917 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term3 _89578 _89597 _89598 P f) = ((term1 _89578 _89597 _89598 P f) = (term2 _89578 _89597 _89598 P f)).
Proof. exact (SYM (@lem3453916 _89578 _89597 _89598 P f)). Qed.
