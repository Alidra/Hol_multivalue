Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3356591_term_abbrevs.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3356580 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3356581 {_87274 : Type'} (s : _87274 -> Prop) (t : _87274 -> Prop) : (s = t) = (term0 _87274 s t).
Proof. exact (@lem3356580 _87274 s t). Qed.
Lemma lem3356582 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : ((term1 _87274 s u) = (term2 _87274 s u)) = (term3 _87274 s u).
Proof. exact (@lem3356581 _87274 (term1 _87274 s u) (term2 _87274 s u)). Qed.
Lemma lem3356591 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : (term3 _87274 s u) = ((term1 _87274 s u) = (term2 _87274 s u)).
Proof. exact (SYM (@lem3356582 _87274 s u)). Qed.
