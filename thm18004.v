Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18004_term_abbrevs.
Require Import thm17976_spec.
Require Import thm17977_spec.
Lemma lem17993 {A B : Type'} (t : A -> B) : t = (term0 A B t).
Proof. exact (EQ_MP (@lem17977 A B t) (@lem17976 A B t)). Qed.
Lemma lem17994 {A : Type'} (t : A -> Prop) : t = (term1 A t).
Proof. exact (@lem17993 A Prop t). Qed.
Lemma lem17995 {A : Type'} (P : A -> Prop) : P = (term1 A P).
Proof. exact (@lem17994 A P). Qed.
Lemma lem17996 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem17997 {A : Type'} (P : A -> Prop) : (ex P) = (term2 A P).
Proof. exact (MK_COMB (@lem17996 A) (@lem17995 A P)). Qed.
Lemma lem17998 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem17999 {A : Type'} (P : A -> Prop) : (term3 A P) = (term4 A P).
Proof. exact (MK_COMB (@lem17998) (@lem17997 A P)). Qed.
Lemma lem18000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18001 {A : Type'} (P : A -> Prop) : (term5 A P) = (term6 A P).
Proof. exact (MK_COMB (@lem18000) (@lem17999 A P)). Qed.
Lemma lem18002 {A : Type'} (P : A -> Prop) : (term7 A P) = (term7 A P).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem18003 {A : Type'} (P : A -> Prop) : ((term3 A P) = (term7 A P)) = ((term4 A P) = (term7 A P)).
Proof. exact (MK_COMB (@lem18001 A P) (@lem18002 A P)). Qed.
Lemma lem18004 {A : Type'} (P : A -> Prop) : ((term4 A P) = (term7 A P)) = ((term3 A P) = (term7 A P)).
Proof. exact (SYM (@lem18003 A P)). Qed.
