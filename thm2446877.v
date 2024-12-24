Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2446877_term_abbrevs.
Require Import thm10578_spec.
Require Import thm10597_spec.
Lemma lem2446875 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2446876 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) : (term1 _60393 x y p) = (term2 _60393 x y p).
Proof. exact (@lem2446875 (term1 _60393 x y p)). Qed.
Lemma lem2446877 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) : (term2 _60393 x y p) = (term1 _60393 x y p).
Proof. exact (SYM (@lem2446876 _60393 x y p)). Qed.
