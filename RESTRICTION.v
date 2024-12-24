Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_term_abbrevs.
Lemma lem4386543 {A B : Type'} : (@RESTRICTION A B) = (term0 A B).
Proof. exact (@RESTRICTION_def A B). Qed.
Lemma lem4386544 {A : Type'} (_50098 : A -> Prop) : _50098 = _50098.
Proof. exact (eq_refl _50098). Qed.
Lemma lem4386545 {A B : Type'} (_50098 : A -> Prop) : (@RESTRICTION A B _50098) = (term1 A B _50098).
Proof. exact (MK_COMB (@lem4386543 A B) (@lem4386544 A _50098)). Qed.
Lemma lem4386546 {A B : Type'} (_50098 : A -> Prop) : (term1 A B _50098) = (term2 A B _50098).
Proof. exact (eq_refl (term1 A B _50098)). Qed.
Lemma lem4386547 {A B : Type'} (_50098 : A -> Prop) : (@RESTRICTION A B _50098) = (term2 A B _50098).
Proof. exact (TRANS (@lem4386545 A B _50098) (@lem4386546 A B _50098)). Qed.
Lemma lem4386548 {A B : Type'} (_50099 : A -> B) : _50099 = _50099.
Proof. exact (eq_refl _50099). Qed.
Lemma lem4386549 {A B : Type'} (_50098 : A -> Prop) (_50099 : A -> B) : (@RESTRICTION A B _50098 _50099) = (term3 A B _50098 _50099).
Proof. exact (MK_COMB (@lem4386547 A B _50098) (@lem4386548 A B _50099)). Qed.
Lemma lem4386550 {A B : Type'} (_50098 : A -> Prop) (_50099 : A -> B) : (term3 A B _50098 _50099) = (term4 A B _50098 _50099).
Proof. exact (eq_refl (term3 A B _50098 _50099)). Qed.
Lemma lem4386551 {A B : Type'} (_50098 : A -> Prop) (_50099 : A -> B) : (@RESTRICTION A B _50098 _50099) = (term4 A B _50098 _50099).
Proof. exact (TRANS (@lem4386549 A B _50098 _50099) (@lem4386550 A B _50098 _50099)). Qed.
Lemma lem4386552 {A : Type'} (_50100 : A) : _50100 = _50100.
Proof. exact (eq_refl _50100). Qed.
Lemma lem4386553 {A B : Type'} (_50098 : A -> Prop) (_50099 : A -> B) (_50100 : A) : (@RESTRICTION A B _50098 _50099 _50100) = (term5 A B _50098 _50099 _50100).
Proof. exact (MK_COMB (@lem4386551 A B _50098 _50099) (@lem4386552 A _50100)). Qed.
Lemma lem4386554 {A B : Type'} (_50098 : A -> Prop) (_50099 : A -> B) (_50100 : A) : (term5 A B _50098 _50099 _50100) = (term6 A B _50098 _50099 _50100).
Proof. exact (eq_refl (term5 A B _50098 _50099 _50100)). Qed.
Lemma lem4386555 {A B : Type'} (_50098 : A -> Prop) (_50099 : A -> B) (_50100 : A) : (@RESTRICTION A B _50098 _50099 _50100) = (term6 A B _50098 _50099 _50100).
Proof. exact (TRANS (@lem4386553 A B _50098 _50099 _50100) (@lem4386554 A B _50098 _50099 _50100)). Qed.
Lemma lem4386556 {A B : Type'} (_50098 : A -> Prop) (_50099 : A -> B) : term7 A B _50098 _50099.
Proof. exact (fun _50100 : A => @lem4386555 A B _50098 _50099 _50100). Qed.
Lemma lem4386557 {A B : Type'} (_50098 : A -> Prop) : term8 A B _50098.
Proof. exact (fun _50099 : A -> B => @lem4386556 A B _50098 _50099). Qed.
Lemma lem4386558 {A B : Type'} : term9 A B.
Proof. exact (fun _50098 : A -> Prop => @lem4386557 A B _50098). Qed.
Lemma lem4386559 {A B : Type'} (_50098 : A -> Prop) : term10 A B _50098.
Proof. exact (@lem4386558 A B _50098). Qed.
Lemma lem4386560 {A B : Type'} (_50098 : A -> Prop) : (term10 A B _50098) = (term8 A B _50098).
Proof. exact (eq_refl (term10 A B _50098)). Qed.
Lemma lem4386561 {A B : Type'} (_50098 : A -> Prop) : term8 A B _50098.
Proof. exact (EQ_MP (@lem4386560 A B _50098) (@lem4386559 A B _50098)). Qed.
Lemma lem4386562 {A B : Type'} (_50098 : A -> Prop) (_50099 : A -> B) : term11 A B _50098 _50099.
Proof. exact (@lem4386561 A B _50098 _50099). Qed.
Lemma lem4386563 {A B : Type'} (_50098 : A -> Prop) (_50099 : A -> B) : (term11 A B _50098 _50099) = (term7 A B _50098 _50099).
Proof. exact (eq_refl (term11 A B _50098 _50099)). Qed.
Lemma lem4386564 {A B : Type'} (_50098 : A -> Prop) (_50099 : A -> B) : term7 A B _50098 _50099.
Proof. exact (EQ_MP (@lem4386563 A B _50098 _50099) (@lem4386562 A B _50098 _50099)). Qed.
Lemma lem4386565 {A B : Type'} (_50098 : A -> Prop) (_50099 : A -> B) (_50100 : A) : term12 A B _50098 _50099 _50100.
Proof. exact (@lem4386564 A B _50098 _50099 _50100). Qed.
Lemma lem4386566 {A B : Type'} (_50098 : A -> Prop) (_50099 : A -> B) (_50100 : A) : (term12 A B _50098 _50099 _50100) = ((@RESTRICTION A B _50098 _50099 _50100) = (term6 A B _50098 _50099 _50100)).
Proof. exact (eq_refl (term12 A B _50098 _50099 _50100)). Qed.
Lemma lem4386567 {A B : Type'} (_50098 : A -> Prop) (_50099 : A -> B) (_50100 : A) : (@RESTRICTION A B _50098 _50099 _50100) = (term6 A B _50098 _50099 _50100).
Proof. exact (EQ_MP (@lem4386566 A B _50098 _50099 _50100) (@lem4386565 A B _50098 _50099 _50100)). Qed.
Lemma lem4386623 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term6 A B s f x).
Proof. exact (@lem4386567 A B s f x). Qed.
Lemma lem4386624 {A B : Type'} (s : A -> Prop) (f : A -> B) : term7 A B s f.
Proof. exact (fun x : A => @lem4386623 A B s f x). Qed.
Lemma lem4386625 {A B : Type'} (s : A -> Prop) : term8 A B s.
Proof. exact (fun f : A -> B => @lem4386624 A B s f). Qed.
Lemma lem4386626 {A B : Type'} : term9 A B.
Proof. exact (fun s : A -> Prop => @lem4386625 A B s). Qed.
