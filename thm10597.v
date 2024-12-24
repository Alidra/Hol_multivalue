Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm10597_term_abbrevs.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem10587 (t : Prop) : (term0 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem10588 (p : Prop) : (term0 p) = p.
Proof. exact (@lem10587 p). Qed.
Lemma lem10589 (p : Prop) : (@eq Prop p) = (@eq Prop p).
Proof. exact (eq_refl (@eq Prop p)). Qed.
Lemma lem10590 (p : Prop) : (p = (term0 p)) = (p = p).
Proof. exact (MK_COMB (@lem10589 p) (@lem10588 p)). Qed.
Lemma lem10592 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem10593 (x : Prop) : (x = x) = True.
Proof. exact (@lem10592 Prop x). Qed.
Lemma lem10594 (p : Prop) : (p = p) = True.
Proof. exact (@lem10593 p). Qed.
Lemma lem10595 (p : Prop) : (p = (term0 p)) = True.
Proof. exact (TRANS (@lem10590 p) (@lem10594 p)). Qed.
Lemma lem10596 (p : Prop) : True = (p = (term0 p)).
Proof. exact (SYM (@lem10595 p)). Qed.
Lemma lem10597 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10596 p) (@lem0)). Qed.
