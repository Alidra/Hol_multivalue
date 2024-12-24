Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16933_term_abbrevs.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem16921 (t : Prop) : (term0 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem16922 (p : Prop) : (term0 p) = p.
Proof. exact (@lem16921 p). Qed.
Lemma lem16923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16924 (p : Prop) : (term1 p) = (@eq Prop p).
Proof. exact (MK_COMB (@lem16923) (@lem16922 p)). Qed.
Lemma lem16925 (p : Prop) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem16926 (p : Prop) : ((term0 p) = p) = (p = p).
Proof. exact (MK_COMB (@lem16924 p) (@lem16925 p)). Qed.
Lemma lem16928 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem16929 (x : Prop) : (x = x) = True.
Proof. exact (@lem16928 Prop x). Qed.
Lemma lem16930 (p : Prop) : (p = p) = True.
Proof. exact (@lem16929 p). Qed.
Lemma lem16931 (p : Prop) : ((term0 p) = p) = True.
Proof. exact (TRANS (@lem16926 p) (@lem16930 p)). Qed.
Lemma lem16932 (p : Prop) : True = ((term0 p) = p).
Proof. exact (SYM (@lem16931 p)). Qed.
Lemma lem16933 (p : Prop) : (term0 p) = p.
Proof. exact (EQ_MP (@lem16932 p) (@lem0)). Qed.
