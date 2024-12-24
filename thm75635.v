Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm75635_term_abbrevs.
Require Import num_Axiom_spec.
Require Import thm113_spec.
Lemma lem75625 {A : Type'} (e : A) : term0 A e.
Proof. exact (@lem75608 A e). Qed.
Lemma lem75626 {A : Type'} (e : A) : (term0 A e) = (term1 A e).
Proof. exact (eq_refl (term0 A e)). Qed.
Lemma lem75627 {A : Type'} (e : A) : term1 A e.
Proof. exact (EQ_MP (@lem75626 A e) (@lem75625 A e)). Qed.
Lemma lem75628 {A : Type'} (e : A) (f : type1423 A) : term2 A e f.
Proof. exact (@lem75627 A e f). Qed.
Lemma lem75629 {A : Type'} (e : A) (f : type1423 A) : (term2 A e f) = (term3 A e f).
Proof. exact (eq_refl (term2 A e f)). Qed.
Lemma lem75630 {A : Type'} (e : A) (f : type1423 A) : term3 A e f.
Proof. exact (EQ_MP (@lem75629 A e f) (@lem75628 A e f)). Qed.
Lemma lem75631 {A : Type'} (P : type976 A) : term4 A P.
Proof. exact (@lem113 (nat -> A) P). Qed.
Lemma lem75632 {A : Type'} (e : A) (f : type1423 A) : term5 A e f.
Proof. exact (@lem75631 A (term6 A e f)). Qed.
Lemma lem75633 {A : Type'} (e : A) (f : type1423 A) : term7 A e f.
Proof. exact (@lem75632 A e f (@lem75630 A e f)). Qed.
Lemma lem75634 {A : Type'} (e : A) : term8 A e.
Proof. exact (fun f : type1423 A => @lem75633 A e f). Qed.
Lemma lem75635 {A : Type'} : term9 A.
Proof. exact (fun e : A => @lem75634 A e). Qed.
