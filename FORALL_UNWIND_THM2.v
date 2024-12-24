Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_UNWIND_THM2_term_abbrevs.
Require Import thm0_spec.
Require Import thm1804_spec.
Require Import thm1823_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem4565 {A : Type'} (a : A) (P : A -> Prop) (h1 : term0 A a P) : term0 A a P.
Proof. exact (h1). Qed.
Lemma lem4566 {A : Type'} (a : A) (P : A -> Prop) (h1 : term0 A a P) : term1 A P a.
Proof. exact (@lem4565 A a P h1 a). Qed.
Lemma lem4567 {A : Type'} (P : A -> Prop) (a : A) : (term1 A P a) = (term2 A P a).
Proof. exact (eq_refl (term1 A P a)). Qed.
Lemma lem4568 {A : Type'} (a : A) (P : A -> Prop) (h1 : term0 A a P) : term2 A P a.
Proof. exact (EQ_MP (@lem4567 A P a) (@lem4566 A a P h1)). Qed.
Lemma lem4572 {_739 : Type'} (x : _739) (p : Prop) : (term3 _739 x p) = p.
Proof. exact (EQ_MP (@lem1804 _739 x p) (@lem0)). Qed.
Lemma lem4573 {A : Type'} (x : A) (p : Prop) : (term3 A x p) = p.
Proof. exact (@lem4572 A x p). Qed.
Lemma lem4574 {A : Type'} (P : A -> Prop) (a : A) : (term2 A P a) = (P a).
Proof. exact (@lem4573 A a (P a)). Qed.
Lemma lem4575 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4576 {A : Type'} (P : A -> Prop) (a : A) : (term4 A P a) = (term5 A P a).
Proof. exact (MK_COMB (@lem4575) (@lem4574 A P a)). Qed.
Lemma lem4577 {A : Type'} (P : A -> Prop) (a : A) : (P a) = (P a).
Proof. exact (eq_refl (P a)). Qed.
Lemma lem4578 {A : Type'} (P : A -> Prop) (a : A) : (term6 A P a) = (term7 A P a).
Proof. exact (MK_COMB (@lem4576 A P a) (@lem4577 A P a)). Qed.
Lemma lem4580 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem4581 {A : Type'} (P : A -> Prop) (a : A) : (term7 A P a) = True.
Proof. exact (@lem4580 (P a)). Qed.
Lemma lem4582 {A : Type'} (P : A -> Prop) (a : A) : (term6 A P a) = True.
Proof. exact (TRANS (@lem4578 A P a) (@lem4581 A P a)). Qed.
Lemma lem4583 {A : Type'} (P : A -> Prop) (a : A) : True = (term6 A P a).
Proof. exact (SYM (@lem4582 A P a)). Qed.
Lemma lem4584 {A : Type'} (P : A -> Prop) (a : A) : term6 A P a.
Proof. exact (EQ_MP (@lem4583 A P a) (@lem0)). Qed.
Lemma lem4585 {A : Type'} (a : A) (P : A -> Prop) (h1 : term0 A a P) : P a.
Proof. exact (@lem4584 A P a (@lem4568 A a P h1)). Qed.
Lemma lem4586 {A : Type'} (P : A -> Prop) (a : A) : term8 A P a.
Proof. exact (fun h0 : term0 A a P => @lem4585 A a P h0). Qed.
Lemma lem4587 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem4588 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4589 {A : Type'} (P : A -> Prop) : (term9 A P) = (term9 A P).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem4590 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term10 A P x) = (term10 A P a).
Proof. exact (MK_COMB (@lem4589 A P) (@lem4588 A x a h1)). Qed.
Lemma lem4591 {A : Type'} (P : A -> Prop) (a : A) : (term10 A P a) = (P a).
Proof. exact (eq_refl (term10 A P a)). Qed.
Lemma lem4592 {A : Type'} (P : A -> Prop) (x : A) : (term11 A P x) = (term11 A P x).
Proof. exact (eq_refl (term11 A P x)). Qed.
Lemma lem4593 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term10 A P x) = (term10 A P a)) = ((term10 A P x) = (P a)).
Proof. exact (MK_COMB (@lem4592 A P x) (@lem4591 A P a)). Qed.
Lemma lem4594 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem4595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4596 {A : Type'} (P : A -> Prop) (x : A) : (term11 A P x) = (term12 A P x).
Proof. exact (MK_COMB (@lem4595) (@lem4594 A P x)). Qed.
Lemma lem4597 {A : Type'} (P : A -> Prop) (a : A) : (P a) = (P a).
Proof. exact (eq_refl (P a)). Qed.
Lemma lem4598 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term10 A P x) = (P a)) = ((P x) = (P a)).
Proof. exact (MK_COMB (@lem4596 A P x) (@lem4597 A P a)). Qed.
Lemma lem4599 {A : Type'} (x : A) (P : A -> Prop) (a : A) : ((term10 A P x) = (term10 A P a)) = ((P x) = (P a)).
Proof. exact (TRANS (@lem4593 A x P a) (@lem4598 A x P a)). Qed.
Lemma lem4600 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (P x) = (P a).
Proof. exact (EQ_MP (@lem4599 A x P a) (@lem4590 A P x a h1)). Qed.
Lemma lem4601 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : x = a) : (P a) = (P x).
Proof. exact (SYM (@lem4600 A P x a h1)). Qed.
Lemma lem4602 {A : Type'} (P : A -> Prop) (a : A) : (P a) = ((P a) = True).
Proof. exact (@lem7 (P a)). Qed.
Lemma lem4605 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : (P a) = True.
Proof. exact (EQ_MP (@lem4602 A P a) (@lem4587 A P a h1)). Qed.
Lemma lem4606 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : True = (P a).
Proof. exact (SYM (@lem4605 A P a h1)). Qed.
Lemma lem4607 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (EQ_MP (@lem4606 A P a h1) (@lem0)). Qed.
Lemma lem4608 {A : Type'} (P : A -> Prop) (x : A) (a : A) (h1 : P a) (h2 : x = a) : P x.
Proof. exact (EQ_MP (@lem4601 A P x a h2) (@lem4607 A P a h1)). Qed.
Lemma lem4609 {A : Type'} (x : A) (P : A -> Prop) (a : A) (h1 : P a) : term13 A a P x.
Proof. exact (fun h0 : x = a => @lem4608 A P x a h1 h0). Qed.
Lemma lem4614 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : term0 A a P.
Proof. exact (fun x : A => @lem4609 A x P a h1). Qed.
Lemma lem4615 {A : Type'} (a : A) (P : A -> Prop) : term14 A a P.
Proof. exact (fun h0 : P a => @lem4614 A P a h0). Qed.
Lemma lem4616 {A : Type'} (a : A) (P : A -> Prop) : term15 A a P.
Proof. exact (conj (@lem4586 A P a) (@lem4615 A a P)). Qed.
Lemma lem4617 {A : Type'} (P : A -> Prop) (a : A) : (term15 A a P) = ((term0 A a P) = (P a)).
Proof. exact (@lem32 (term0 A a P) (P a)). Qed.
Lemma lem4618 {A : Type'} (P : A -> Prop) (a : A) : (term0 A a P) = (P a).
Proof. exact (EQ_MP (@lem4617 A P a) (@lem4616 A a P)). Qed.
Lemma lem4623 {A : Type'} (P : A -> Prop) : term16 A P.
Proof. exact (fun a : A => @lem4618 A P a). Qed.
Lemma lem4628 {A : Type'} : term17 A.
Proof. exact (fun P : A -> Prop => @lem4623 A P). Qed.
