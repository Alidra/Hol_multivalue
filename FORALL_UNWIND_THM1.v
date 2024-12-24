Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_UNWIND_THM1_term_abbrevs.
Require Import FORALL_UNWIND_THM2_spec.
Lemma lem4631 {_910 : Type'} (a : _910) (x : _910) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem4632 {_910 : Type'} (a : _910) (x : _910) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem4631 _910 a x h1)). Qed.
Lemma lem4633 {_910 : Type'} (x : _910) (a : _910) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4634 {_910 : Type'} (x : _910) (a : _910) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem4633 _910 x a h1)). Qed.
Lemma lem4635 {_910 : Type'} (x : _910) (a : _910) : (a = x) = (x = a).
Proof. exact (prop_ext (fun h1 : a = x => @lem4632 _910 a x h1) (fun h1 : x = a => @lem4634 _910 x a h1)). Qed.
Lemma lem4636 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4637 {_910 : Type'} (x : _910) (a : _910) : (term0 _910 a x) = (term0 _910 x a).
Proof. exact (MK_COMB (@lem4636) (@lem4635 _910 x a)). Qed.
Lemma lem4639 {_910 : Type'} (P : _910 -> Prop) (x : _910) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem4640 {_910 : Type'} (a : _910) (P : _910 -> Prop) (x : _910) : (term1 _910 a P x) = (term2 _910 a P x).
Proof. exact (MK_COMB (@lem4637 _910 x a) (@lem4639 _910 P x)). Qed.
Lemma lem4641 {_910 : Type'} (a : _910) (P : _910 -> Prop) : (term3 _910 a P) = (term4 _910 a P).
Proof. exact (fun_ext (fun x : _910 => @lem4640 _910 a P x)). Qed.
Lemma lem4642 {_910 : Type'} : (@all _910) = (@all _910).
Proof. exact (eq_refl (@all _910)). Qed.
Lemma lem4643 {_910 : Type'} (a : _910) (P : _910 -> Prop) : (term5 _910 a P) = (term6 _910 a P).
Proof. exact (MK_COMB (@lem4642 _910) (@lem4641 _910 a P)). Qed.
Lemma lem4644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4645 {_910 : Type'} (a : _910) (P : _910 -> Prop) : (term7 _910 a P) = (term8 _910 a P).
Proof. exact (MK_COMB (@lem4644) (@lem4643 _910 a P)). Qed.
Lemma lem4646 {_910 : Type'} (P : _910 -> Prop) (a : _910) : (P a) = (P a).
Proof. exact (eq_refl (P a)). Qed.
Lemma lem4647 {_910 : Type'} (P : _910 -> Prop) (a : _910) : ((term5 _910 a P) = (P a)) = ((term6 _910 a P) = (P a)).
Proof. exact (MK_COMB (@lem4645 _910 a P) (@lem4646 _910 P a)). Qed.
Lemma lem4648 {_910 : Type'} (P : _910 -> Prop) (a : _910) : ((term6 _910 a P) = (P a)) = ((term5 _910 a P) = (P a)).
Proof. exact (SYM (@lem4647 _910 P a)). Qed.
Lemma lem4649 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (@lem4628 A P). Qed.
Lemma lem4650 {A : Type'} (P : A -> Prop) : (term9 A P) = (term10 A P).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem4651 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (EQ_MP (@lem4650 A P) (@lem4649 A P)). Qed.
Lemma lem4652 {A : Type'} (P : A -> Prop) (a : A) : term11 A P a.
Proof. exact (@lem4651 A P a). Qed.
Lemma lem4653 {A : Type'} (P : A -> Prop) (a : A) : (term11 A P a) = ((term6 A a P) = (P a)).
Proof. exact (eq_refl (term11 A P a)). Qed.
Lemma lem4656 {A : Type'} (P : A -> Prop) (a : A) : (term6 A a P) = (P a).
Proof. exact (EQ_MP (@lem4653 A P a) (@lem4652 A P a)). Qed.
Lemma lem4657 {_910 : Type'} (P : _910 -> Prop) (a : _910) : (term6 _910 a P) = (P a).
Proof. exact (@lem4656 _910 P a). Qed.
Lemma lem4658 {_910 : Type'} (P : _910 -> Prop) (a : _910) : (term5 _910 a P) = (P a).
Proof. exact (EQ_MP (@lem4648 _910 P a) (@lem4657 _910 P a)). Qed.
Lemma lem4663 {_910 : Type'} (P : _910 -> Prop) : term12 _910 P.
Proof. exact (fun a : _910 => @lem4658 _910 P a). Qed.
Lemma lem4668 {_910 : Type'} : term13 _910.
Proof. exact (fun P : _910 -> Prop => @lem4663 _910 P). Qed.
