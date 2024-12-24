Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3399706_term_abbrevs.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3399691 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3399692 {_88295 : Type'} (s : _88295 -> Prop) (t : _88295 -> Prop) : (s = t) = (term0 _88295 s t).
Proof. exact (@lem3399691 _88295 s t). Qed.
Lemma lem3399693 {_88295 : Type'} : ((term1 _88295) = (@EMPTY _88295)) = (term2 _88295).
Proof. exact (@lem3399692 _88295 (term1 _88295) (@EMPTY _88295)). Qed.
Lemma lem3399706 {_88295 : Type'} : (term2 _88295) = ((term1 _88295) = (@EMPTY _88295)).
Proof. exact (SYM (@lem3399693 _88295)). Qed.
