Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_INSERT_term_abbrevs.
Require Import thm3356591_spec.
Require Import thm3358011_spec.
Lemma lem3358012 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : (term0 _87274 s u) = (term1 _87274 s u).
Proof. exact (EQ_MP (@lem3356591 _87274 s u) (@lem3358011 _87274 s u)). Qed.
