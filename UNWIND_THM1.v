Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNWIND_THM1_term_abbrevs.
Require Import thm32_spec.
Lemma lem4477 {A : Type'} (a : A) (P : A -> Prop) (h1 : term0 A a P) : term0 A a P.
Proof. exact (h1). Qed.
Lemma lem4478 {A : Type'} (a : A) (P : A -> Prop) (x : A) (h1 : term1 A a P x) : term1 A a P x.
Proof. exact (h1). Qed.
Lemma lem4479 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem4480 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4481 {A : Type'} (P : A -> Prop) : (term2 A P) = (term2 A P).
Proof. exact (eq_refl (term2 A P)). Qed.
Lemma lem4482 {A : Type'} (P : A -> Prop) (a : A) (x : A) (h1 : a = x) : (term3 A P a) = (term3 A P x).
Proof. exact (MK_COMB (@lem4481 A P) (@lem4480 A a x h1)). Qed.
Lemma lem4483 {A : Type'} (P : A -> Prop) (x : A) : (term3 A P x) = (P x).
Proof. exact (eq_refl (term3 A P x)). Qed.
Lemma lem4484 {A : Type'} (P : A -> Prop) (a : A) : (term4 A P a) = (term4 A P a).
Proof. exact (eq_refl (term4 A P a)). Qed.
Lemma lem4485 {A : Type'} (a : A) (P : A -> Prop) (x : A) : ((term3 A P a) = (term3 A P x)) = ((term3 A P a) = (P x)).
Proof. exact (MK_COMB (@lem4484 A P a) (@lem4483 A P x)). Qed.
Lemma lem4486 {A : Type'} (P : A -> Prop) (a : A) : (term3 A P a) = (P a).
Proof. exact (eq_refl (term3 A P a)). Qed.
Lemma lem4487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4488 {A : Type'} (P : A -> Prop) (a : A) : (term4 A P a) = (term5 A P a).
Proof. exact (MK_COMB (@lem4487) (@lem4486 A P a)). Qed.
Lemma lem4489 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem4490 {A : Type'} (a : A) (P : A -> Prop) (x : A) : ((term3 A P a) = (P x)) = ((P a) = (P x)).
Proof. exact (MK_COMB (@lem4488 A P a) (@lem4489 A P x)). Qed.
Lemma lem4491 {A : Type'} (a : A) (P : A -> Prop) (x : A) : ((term3 A P a) = (term3 A P x)) = ((P a) = (P x)).
Proof. exact (TRANS (@lem4485 A a P x) (@lem4490 A a P x)). Qed.
Lemma lem4492 {A : Type'} (P : A -> Prop) (a : A) (x : A) (h1 : a = x) : (P a) = (P x).
Proof. exact (EQ_MP (@lem4491 A a P x) (@lem4482 A P a x h1)). Qed.
Lemma lem4493 {A : Type'} (P : A -> Prop) (a : A) (x : A) (h1 : a = x) : (P x) = (P a).
Proof. exact (SYM (@lem4492 A P a x h1)). Qed.
Lemma lem4494 {A : Type'} (P : A -> Prop) (a : A) (x : A) (h1 : P x) (h2 : a = x) : P a.
Proof. exact (EQ_MP (@lem4493 A P a x h2) (@lem4479 A P x h1)). Qed.
Lemma lem4495 {A : Type'} (a : A) (P : A -> Prop) (x : A) (h1 : term1 A a P x) : P x.
Proof. exact (proj2 (@lem4478 A a P x h1)). Qed.
Lemma lem4496 {A : Type'} (a : A) (P : A -> Prop) (x : A) (h1 : term1 A a P x) : a = x.
Proof. exact (proj1 (@lem4478 A a P x h1)). Qed.
Lemma lem4497 {A : Type'} (P : A -> Prop) (a : A) (x : A) (h1 : term1 A a P x) (h2 : a = x) : (P x) = (P a).
Proof. exact (prop_ext (fun h3 : P x => @lem4494 A P a x h3 h2) (fun h3 : P a => @lem4495 A a P x h1)). Qed.
Lemma lem4498 {A : Type'} (P : A -> Prop) (a : A) (x : A) (h1 : term1 A a P x) (h2 : a = x) : P a.
Proof. exact (EQ_MP (@lem4497 A P a x h1 h2) (@lem4495 A a P x h1)). Qed.
Lemma lem4499 {A : Type'} (a : A) (P : A -> Prop) (x : A) (h1 : term1 A a P x) : (a = x) = (P a).
Proof. exact (prop_ext (fun h2 : a = x => @lem4498 A P a x h1 h2) (fun h2 : P a => @lem4496 A a P x h1)). Qed.
Lemma lem4500 {A : Type'} (a : A) (P : A -> Prop) (x : A) (h1 : term1 A a P x) : P a.
Proof. exact (EQ_MP (@lem4499 A a P x h1) (@lem4496 A a P x h1)). Qed.
Lemma lem4501 {A : Type'} (a : A) (P : A -> Prop) (h1 : term0 A a P) : P a.
Proof. exact (ex_elim (@lem4477 A a P h1) (fun x : A => fun h0 : term6 A a P x => @lem4500 A a P x h0)). Qed.
Lemma lem4502 {A : Type'} (P : A -> Prop) (a : A) : term7 A P a.
Proof. exact (fun h0 : term0 A a P => @lem4501 A a P h0). Qed.
Lemma lem4507 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem4508 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4509 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : term8 A P a.
Proof. exact (conj (@lem4508 A a) (@lem4507 A P a h1)). Qed.
Lemma lem4510 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : term0 A a P.
Proof. exact (ex_intro (term6 A a P) a (@lem4509 A P a h1)). Qed.
Lemma lem4511 {A : Type'} (a : A) (P : A -> Prop) : term9 A a P.
Proof. exact (fun h0 : P a => @lem4510 A P a h0). Qed.
Lemma lem4512 {A : Type'} (a : A) (P : A -> Prop) : term10 A a P.
Proof. exact (conj (@lem4502 A P a) (@lem4511 A a P)). Qed.
Lemma lem4513 {A : Type'} (P : A -> Prop) (a : A) : (term10 A a P) = ((term0 A a P) = (P a)).
Proof. exact (@lem32 (term0 A a P) (P a)). Qed.
Lemma lem4514 {A : Type'} (P : A -> Prop) (a : A) : (term0 A a P) = (P a).
Proof. exact (EQ_MP (@lem4513 A P a) (@lem4512 A a P)). Qed.
Lemma lem4519 {A : Type'} (P : A -> Prop) : term11 A P.
Proof. exact (fun a : A => @lem4514 A P a). Qed.
Lemma lem4524 {A : Type'} : term12 A.
Proof. exact (fun P : A -> Prop => @lem4519 A P). Qed.
