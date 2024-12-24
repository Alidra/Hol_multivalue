Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3399787_term_abbrevs.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3399772 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3399773 {_88312 : Type'} (s : _88312 -> Prop) (t : _88312 -> Prop) : (s = t) = (term0 _88312 s t).
Proof. exact (@lem3399772 _88312 s t). Qed.
Lemma lem3399774 {_88312 : Type'} : ((term1 _88312) = (@UNIV _88312)) = (term2 _88312).
Proof. exact (@lem3399773 _88312 (term1 _88312) (@UNIV _88312)). Qed.
Lemma lem3399787 {_88312 : Type'} : (term2 _88312) = ((term1 _88312) = (@UNIV _88312)).
Proof. exact (SYM (@lem3399774 _88312)). Qed.
