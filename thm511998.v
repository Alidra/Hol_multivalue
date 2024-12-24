Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm511998_term_abbrevs.
Require Import thm10578_spec.
Require Import thm10597_spec.
Lemma lem511996 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem511997 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : ((term1 _17389 P e Q) = (term2 _17389 P e Q)) = (term3 _17389 P e Q).
Proof. exact (@lem511996 ((term1 _17389 P e Q) = (term2 _17389 P e Q))). Qed.
Lemma lem511998 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : (term3 _17389 P e Q) = ((term1 _17389 P e Q) = (term2 _17389 P e Q)).
Proof. exact (SYM (@lem511997 _17389 P e Q)). Qed.
