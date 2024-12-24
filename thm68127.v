Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1856_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem68121 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem68122 {_5989 : Type'} (x : _5989) : ((x = x) = True) = (x = x).
Proof. exact (@lem68121 (x = x)). Qed.
Lemma lem68124 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem68125 {_5989 : Type'} (x : _5989) : (x = x) = True.
Proof. exact (@lem68124 _5989 x). Qed.
Lemma lem68126 {_5989 : Type'} (x : _5989) : ((x = x) = True) = True.
Proof. exact (TRANS (@lem68122 _5989 x) (@lem68125 _5989 x)). Qed.
Lemma lem68127 {_5989 : Type'} (x : _5989) : True = ((x = x) = True).
Proof. exact (SYM (@lem68126 _5989 x)). Qed.
