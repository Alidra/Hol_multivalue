Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21021_term_abbrevs.
Require Import thm1823_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem21012 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem21013 (p : Prop) : (p -> False) = (~ p).
Proof. exact (@lem21012 p). Qed.
Lemma lem21014 (p : Prop) : (term0 p) = (term0 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem21015 (p : Prop) : ((~ p) = (p -> False)) = ((~ p) = (~ p)).
Proof. exact (MK_COMB (@lem21014 p) (@lem21013 p)). Qed.
Lemma lem21017 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem21018 (x : Prop) : (x = x) = True.
Proof. exact (@lem21017 Prop x). Qed.
Lemma lem21019 (p : Prop) : ((~ p) = (~ p)) = True.
Proof. exact (@lem21018 (~ p)). Qed.
Lemma lem21020 (p : Prop) : ((~ p) = (p -> False)) = True.
Proof. exact (TRANS (@lem21015 p) (@lem21019 p)). Qed.
Lemma lem21021 (p : Prop) : True = ((~ p) = (p -> False)).
Proof. exact (SYM (@lem21020 p)). Qed.
