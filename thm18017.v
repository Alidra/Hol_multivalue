Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18017_term_abbrevs.
Require Import thm17976_spec.
Require Import thm17977_spec.
Lemma lem18006 {A B : Type'} (t : A -> B) : t = (term0 A B t).
Proof. exact (EQ_MP (@lem17977 A B t) (@lem17976 A B t)). Qed.
Lemma lem18007 {A : Type'} (t : A -> Prop) : t = (term1 A t).
Proof. exact (@lem18006 A Prop t). Qed.
Lemma lem18008 {A : Type'} (P : A -> Prop) : P = (term1 A P).
Proof. exact (@lem18007 A P). Qed.
Lemma lem18009 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem18010 {A : Type'} (P : A -> Prop) : (@ex1 A P) = (term2 A P).
Proof. exact (MK_COMB (@lem18009 A) (@lem18008 A P)). Qed.
Lemma lem18011 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem18012 {A : Type'} (P : A -> Prop) : (term3 A P) = (term4 A P).
Proof. exact (MK_COMB (@lem18011) (@lem18010 A P)). Qed.
Lemma lem18013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18014 {A : Type'} (P : A -> Prop) : (term5 A P) = (term6 A P).
Proof. exact (MK_COMB (@lem18013) (@lem18012 A P)). Qed.
Lemma lem18015 {A : Type'} (P : A -> Prop) : (term7 A P) = (term7 A P).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem18016 {A : Type'} (P : A -> Prop) : ((term3 A P) = (term7 A P)) = ((term4 A P) = (term7 A P)).
Proof. exact (MK_COMB (@lem18014 A P) (@lem18015 A P)). Qed.
Lemma lem18017 {A : Type'} (P : A -> Prop) : ((term4 A P) = (term7 A P)) = ((term3 A P) = (term7 A P)).
Proof. exact (SYM (@lem18016 A P)). Qed.
