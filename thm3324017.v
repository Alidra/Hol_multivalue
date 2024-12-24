Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3324017_term_abbrevs.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3324006 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3324007 {_86841 : Type'} (s : _86841 -> Prop) (t : _86841 -> Prop) : (s = t) = (term0 _86841 s t).
Proof. exact (@lem3324006 _86841 s t). Qed.
Lemma lem3324008 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : ((term1 _86841 s u) = (term2 _86841 s u)) = (term3 _86841 s u).
Proof. exact (@lem3324007 _86841 (term1 _86841 s u) (term2 _86841 s u)). Qed.
Lemma lem3324017 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term3 _86841 s u) = ((term1 _86841 s u) = (term2 _86841 s u)).
Proof. exact (SYM (@lem3324008 _86841 s u)). Qed.
