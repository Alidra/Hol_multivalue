Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2318604_term_abbrevs.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2318592 (t : Prop) : (term0 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem2318593 (p : Prop) : (term0 p) = p.
Proof. exact (@lem2318592 p). Qed.
Lemma lem2318594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2318595 (p : Prop) : (term1 p) = (@eq Prop p).
Proof. exact (MK_COMB (@lem2318594) (@lem2318593 p)). Qed.
Lemma lem2318596 (p : Prop) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem2318597 (p : Prop) : ((term0 p) = p) = (p = p).
Proof. exact (MK_COMB (@lem2318595 p) (@lem2318596 p)). Qed.
Lemma lem2318599 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2318600 (x : Prop) : (x = x) = True.
Proof. exact (@lem2318599 Prop x). Qed.
Lemma lem2318601 (p : Prop) : (p = p) = True.
Proof. exact (@lem2318600 p). Qed.
Lemma lem2318602 (p : Prop) : ((term0 p) = p) = True.
Proof. exact (TRANS (@lem2318597 p) (@lem2318601 p)). Qed.
Lemma lem2318603 (p : Prop) : True = ((term0 p) = p).
Proof. exact (SYM (@lem2318602 p)). Qed.
Lemma lem2318604 (p : Prop) : (term0 p) = p.
Proof. exact (EQ_MP (@lem2318603 p) (@lem0)). Qed.
