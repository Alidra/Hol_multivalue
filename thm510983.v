Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm510983_term_abbrevs.
Require Import thm10578_spec.
Require Import thm10597_spec.
Lemma lem510981 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem510982 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : ((term1 _17370 _17371 P Q) = (term2 _17370 _17371 P Q)) = (term3 _17370 _17371 P Q).
Proof. exact (@lem510981 ((term1 _17370 _17371 P Q) = (term2 _17370 _17371 P Q))). Qed.
Lemma lem510983 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term3 _17370 _17371 P Q) = ((term1 _17370 _17371 P Q) = (term2 _17370 _17371 P Q)).
Proof. exact (SYM (@lem510982 _17370 _17371 P Q)). Qed.
