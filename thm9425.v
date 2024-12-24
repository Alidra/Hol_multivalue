Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm9425_term_abbrevs.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem9400 {A : Type'} : (@ex A) = (term0 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem9401 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem9402 {A : Type'} (P : A -> Prop) : (ex P) = (term1 A P).
Proof. exact (MK_COMB (@lem9400 A) (@lem9401 A P)). Qed.
Lemma lem9404 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem9405 {A : Type'} (f : type686 A) (y : A -> Prop) : (term3 A f y) = (f y).
Proof. exact (@lem9404 (A -> Prop) Prop f y). Qed.
Lemma lem9406 {A : Type'} (P : A -> Prop) : (term4 A P) = (term1 A P).
Proof. exact (@lem9405 A (term0 A) P). Qed.
Lemma lem9407 {A : Type'} (P : A -> Prop) : (term1 A P) = (term5 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem9408 {A : Type'} : (term6 A) = (term0 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem9407 A P)). Qed.
Lemma lem9409 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem9410 {A : Type'} (P : A -> Prop) : (term4 A P) = (term1 A P).
Proof. exact (MK_COMB (@lem9408 A) (@lem9409 A P)). Qed.
Lemma lem9411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem9412 {A : Type'} (P : A -> Prop) : (term7 A P) = (term8 A P).
Proof. exact (MK_COMB (@lem9411) (@lem9410 A P)). Qed.
Lemma lem9413 {A : Type'} (P : A -> Prop) : (term1 A P) = (term5 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem9414 {A : Type'} (P : A -> Prop) : ((term4 A P) = (term1 A P)) = ((term1 A P) = (term5 A P)).
Proof. exact (MK_COMB (@lem9412 A P) (@lem9413 A P)). Qed.
Lemma lem9415 {A : Type'} (P : A -> Prop) : (term1 A P) = (term5 A P).
Proof. exact (EQ_MP (@lem9414 A P) (@lem9406 A P)). Qed.
Lemma lem9416 {A : Type'} (P : A -> Prop) : (ex P) = (term5 A P).
Proof. exact (TRANS (@lem9402 A P) (@lem9415 A P)). Qed.
Lemma lem9417 {A : Type'} (P : A -> Prop) : (term9 A P) = (term9 A P).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem9418 {A : Type'} (P : A -> Prop) : ((term5 A P) = (ex P)) = ((term5 A P) = (term5 A P)).
Proof. exact (MK_COMB (@lem9417 A P) (@lem9416 A P)). Qed.
Lemma lem9420 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem9421 (x : Prop) : (x = x) = True.
Proof. exact (@lem9420 Prop x). Qed.
Lemma lem9422 {A : Type'} (P : A -> Prop) : ((term5 A P) = (term5 A P)) = True.
Proof. exact (@lem9421 (term5 A P)). Qed.
Lemma lem9423 {A : Type'} (P : A -> Prop) : ((term5 A P) = (ex P)) = True.
Proof. exact (TRANS (@lem9418 A P) (@lem9422 A P)). Qed.
Lemma lem9424 {A : Type'} (P : A -> Prop) : True = ((term5 A P) = (ex P)).
Proof. exact (SYM (@lem9423 A P)). Qed.
Lemma lem9425 {A : Type'} (P : A -> Prop) : (term5 A P) = (ex P).
Proof. exact (EQ_MP (@lem9424 A P) (@lem0)). Qed.
