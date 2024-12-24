Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import dimindex_term_abbrevs.
Lemma lem7590192 {A : Type'} : (@dimindex A) = (term0 A).
Proof. exact (@dimindex_def A). Qed.
Lemma lem7590193 {A : Type'} (_97595 : A -> Prop) : _97595 = _97595.
Proof. exact (eq_refl _97595). Qed.
Lemma lem7590194 {A : Type'} (_97595 : A -> Prop) : (@dimindex A _97595) = (term1 A _97595).
Proof. exact (MK_COMB (@lem7590192 A) (@lem7590193 A _97595)). Qed.
Lemma lem7590195 {A : Type'} (_97595 : A -> Prop) : (term1 A _97595) = (term2 A).
Proof. exact (eq_refl (term1 A _97595)). Qed.
Lemma lem7590196 {A : Type'} (_97595 : A -> Prop) : (@dimindex A _97595) = (term2 A).
Proof. exact (TRANS (@lem7590194 A _97595) (@lem7590195 A _97595)). Qed.
Lemma lem7590197 {A : Type'} : term3 A.
Proof. exact (fun _97595 : A -> Prop => @lem7590196 A _97595). Qed.
Lemma lem7590198 {A : Type'} (_97595 : A -> Prop) : term4 A _97595.
Proof. exact (@lem7590197 A _97595). Qed.
Lemma lem7590199 {A : Type'} (_97595 : A -> Prop) : (term4 A _97595) = ((@dimindex A _97595) = (term2 A)).
Proof. exact (eq_refl (term4 A _97595)). Qed.
Lemma lem7590200 {A : Type'} (_97595 : A -> Prop) : (@dimindex A _97595) = (term2 A).
Proof. exact (EQ_MP (@lem7590199 A _97595) (@lem7590198 A _97595)). Qed.
Lemma lem7590230 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term2 A).
Proof. exact (@lem7590200 A s). Qed.
Lemma lem7590231 {A : Type'} : term3 A.
Proof. exact (fun s : A -> Prop => @lem7590230 A s). Qed.
