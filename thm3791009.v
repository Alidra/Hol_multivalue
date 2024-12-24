Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3791009_term_abbrevs.
Require Import thm3790997_spec.
Lemma lem3790999 {A B : Type'} : term0 A B.
Proof. exact (proj1 (@lem3790997 A B)). Qed.
Lemma lem3791000 {A B : Type'} (f : type1411 A B) : term1 A B f.
Proof. exact (@lem3790999 A B f). Qed.
Lemma lem3791001 {A B : Type'} (f : type1411 A B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem3791002 {A B : Type'} (f : type1411 A B) : term2 A B f.
Proof. exact (EQ_MP (@lem3791001 A B f) (@lem3791000 A B f)). Qed.
Lemma lem3791003 {A B : Type'} (f : type1411 A B) (s : A -> Prop) : term3 A B f s.
Proof. exact (@lem3791002 A B f s). Qed.
Lemma lem3791004 {A B : Type'} (f : type1411 A B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem3791005 {A B : Type'} (f : type1411 A B) (s : A -> Prop) : term4 A B f s.
Proof. exact (EQ_MP (@lem3791004 A B f s) (@lem3791003 A B f s)). Qed.
Lemma lem3791006 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) : term5 A B f s a.
Proof. exact (@lem3791005 A B f s a). Qed.
Lemma lem3791007 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) : (term5 A B f s a) = (term6 A B f s a).
Proof. exact (eq_refl (term5 A B f s a)). Qed.
Lemma lem3791008 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) : term6 A B f s a.
Proof. exact (EQ_MP (@lem3791007 A B f s a) (@lem3791006 A B f s a)). Qed.
Lemma lem3791009 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : term7 A B f s a b.
Proof. exact (@lem3791008 A B f s a b). Qed.
