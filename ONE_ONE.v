Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ONE_ONE_term_abbrevs.
Lemma lem68546 {A B : Type'} : (@ONE_ONE A B) = (term0 A B).
Proof. exact (@ONE_ONE_def A B). Qed.
Lemma lem68547 {A B : Type'} (_2064 : A -> B) : _2064 = _2064.
Proof. exact (eq_refl _2064). Qed.
Lemma lem68548 {A B : Type'} (_2064 : A -> B) : (@ONE_ONE A B _2064) = (term1 A B _2064).
Proof. exact (MK_COMB (@lem68546 A B) (@lem68547 A B _2064)). Qed.
Lemma lem68549 {A B : Type'} (_2064 : A -> B) : (term1 A B _2064) = (term2 A B _2064).
Proof. exact (eq_refl (term1 A B _2064)). Qed.
Lemma lem68550 {A B : Type'} (_2064 : A -> B) : (@ONE_ONE A B _2064) = (term2 A B _2064).
Proof. exact (TRANS (@lem68548 A B _2064) (@lem68549 A B _2064)). Qed.
Lemma lem68551 {A B : Type'} : term3 A B.
Proof. exact (fun _2064 : A -> B => @lem68550 A B _2064). Qed.
Lemma lem68552 {A B : Type'} (_2064 : A -> B) : term4 A B _2064.
Proof. exact (@lem68551 A B _2064). Qed.
Lemma lem68553 {A B : Type'} (_2064 : A -> B) : (term4 A B _2064) = ((@ONE_ONE A B _2064) = (term2 A B _2064)).
Proof. exact (eq_refl (term4 A B _2064)). Qed.
Lemma lem68554 {A B : Type'} (_2064 : A -> B) : (@ONE_ONE A B _2064) = (term2 A B _2064).
Proof. exact (EQ_MP (@lem68553 A B _2064) (@lem68552 A B _2064)). Qed.
Lemma lem68584 {A B : Type'} (f : A -> B) : (@ONE_ONE A B f) = (term2 A B f).
Proof. exact (@lem68554 A B f). Qed.
Lemma lem68585 {A B : Type'} : term3 A B.
Proof. exact (fun f : A -> B => @lem68584 A B f). Qed.
