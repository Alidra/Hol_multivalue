Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNWIND_THM2_term_abbrevs.
Require Import UNWIND_THM1_spec.
Lemma lem4527 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4528 {A : Type'} (x : A) (a : A) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem4527 A x a h1)). Qed.
Lemma lem4529 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4530 {A : Type'} (a : A) (x : A) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem4529 A a x h1)). Qed.
Lemma lem4531 {A : Type'} (a : A) (x : A) : (x = a) = (a = x).
Proof. exact (prop_ext (fun h1 : x = a => @lem4528 A x a h1) (fun h1 : a = x => @lem4530 A a x h1)). Qed.
Lemma lem4532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4533 {A : Type'} (a : A) (x : A) : (term0 A x a) = (term0 A a x).
Proof. exact (MK_COMB (@lem4532) (@lem4531 A a x)). Qed.
Lemma lem4535 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem4536 {A : Type'} (a : A) (P : A -> Prop) (x : A) : (term1 A a P x) = (term2 A a P x).
Proof. exact (MK_COMB (@lem4533 A a x) (@lem4535 A P x)). Qed.
Lemma lem4537 {A : Type'} (a : A) (P : A -> Prop) : (term3 A a P) = (term4 A a P).
Proof. exact (fun_ext (fun x : A => @lem4536 A a P x)). Qed.
Lemma lem4538 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4539 {A : Type'} (a : A) (P : A -> Prop) : (term5 A a P) = (term6 A a P).
Proof. exact (MK_COMB (@lem4538 A) (@lem4537 A a P)). Qed.
Lemma lem4540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4541 {A : Type'} (a : A) (P : A -> Prop) : (term7 A a P) = (term8 A a P).
Proof. exact (MK_COMB (@lem4540) (@lem4539 A a P)). Qed.
Lemma lem4542 {A : Type'} (P : A -> Prop) (a : A) : (P a) = (P a).
Proof. exact (eq_refl (P a)). Qed.
Lemma lem4543 {A : Type'} (P : A -> Prop) (a : A) : ((term5 A a P) = (P a)) = ((term6 A a P) = (P a)).
Proof. exact (MK_COMB (@lem4541 A a P) (@lem4542 A P a)). Qed.
Lemma lem4544 {A : Type'} (P : A -> Prop) (a : A) : ((term6 A a P) = (P a)) = ((term5 A a P) = (P a)).
Proof. exact (SYM (@lem4543 A P a)). Qed.
Lemma lem4545 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (@lem4524 A P). Qed.
Lemma lem4546 {A : Type'} (P : A -> Prop) : (term9 A P) = (term10 A P).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem4547 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (EQ_MP (@lem4546 A P) (@lem4545 A P)). Qed.
Lemma lem4548 {A : Type'} (P : A -> Prop) (a : A) : term11 A P a.
Proof. exact (@lem4547 A P a). Qed.
Lemma lem4549 {A : Type'} (P : A -> Prop) (a : A) : (term11 A P a) = ((term6 A a P) = (P a)).
Proof. exact (eq_refl (term11 A P a)). Qed.
Lemma lem4552 {A : Type'} (P : A -> Prop) (a : A) : (term6 A a P) = (P a).
Proof. exact (EQ_MP (@lem4549 A P a) (@lem4548 A P a)). Qed.
Lemma lem4553 {A : Type'} (P : A -> Prop) (a : A) : (term6 A a P) = (P a).
Proof. exact (@lem4552 A P a). Qed.
Lemma lem4554 {A : Type'} (P : A -> Prop) (a : A) : (term5 A a P) = (P a).
Proof. exact (EQ_MP (@lem4544 A P a) (@lem4553 A P a)). Qed.
Lemma lem4559 {A : Type'} (P : A -> Prop) : term12 A P.
Proof. exact (fun a : A => @lem4554 A P a). Qed.
Lemma lem4564 {A : Type'} : term13 A.
Proof. exact (fun P : A -> Prop => @lem4559 A P). Qed.
