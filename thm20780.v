Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20780_term_abbrevs.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem20769 (t : Prop) : (term0 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem20770 (a : Prop) : (term0 a) = a.
Proof. exact (@lem20769 a). Qed.
Lemma lem20771 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20772 (a : Prop) : (term1 a) = (@eq Prop a).
Proof. exact (MK_COMB (@lem20771) (@lem20770 a)). Qed.
Lemma lem20773 (a : Prop) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem20774 (a : Prop) : ((term0 a) = a) = (a = a).
Proof. exact (MK_COMB (@lem20772 a) (@lem20773 a)). Qed.
Lemma lem20776 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem20777 (x : Prop) : (x = x) = True.
Proof. exact (@lem20776 Prop x). Qed.
Lemma lem20778 (a : Prop) : (a = a) = True.
Proof. exact (@lem20777 a). Qed.
Lemma lem20779 (a : Prop) : ((term0 a) = a) = True.
Proof. exact (TRANS (@lem20774 a) (@lem20778 a)). Qed.
Lemma lem20780 (a : Prop) : True = ((term0 a) = a).
Proof. exact (SYM (@lem20779 a)). Qed.
