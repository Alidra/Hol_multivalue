Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7931551_term_abbrevs.
Require Import thm9102_spec.
Require Import tybit0_INDUCT_spec.
Lemma lem7931517 {A : Type'} (P : type1345 A) : term0 A P.
Proof. exact (@lem7927982 A P). Qed.
Lemma lem7931518 {A : Type'} (P : type1345 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem7931519 {A : Type'} (P : type1345 A) : term1 A P.
Proof. exact (EQ_MP (@lem7931518 A P) (@lem7931517 A P)). Qed.
Lemma lem7931520 {A : Type'} : term2 A.
Proof. exact (@lem7931519 A (term3 A)). Qed.
Lemma lem7931521 {A : Type'} (a : finite_sum A A) : (term4 A a) = (term5 A a).
Proof. exact (eq_refl (term4 A a)). Qed.
Lemma lem7931522 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (fun_ext (fun a : finite_sum A A => @lem7931521 A a)). Qed.
Lemma lem7931523 {A : Type'} : (@all (finite_sum A A)) = (@all (finite_sum A A)).
Proof. exact (eq_refl (@all (finite_sum A A))). Qed.
Lemma lem7931524 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (MK_COMB (@lem7931523 A) (@lem7931522 A)). Qed.
Lemma lem7931525 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7931526 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (MK_COMB (@lem7931525) (@lem7931524 A)). Qed.
Lemma lem7931527 {A : Type'} (x : tybit0 A) : (term12 A x) = (term13 A x).
Proof. exact (eq_refl (term12 A x)). Qed.
Lemma lem7931528 {A : Type'} : (term14 A) = (term3 A).
Proof. exact (fun_ext (fun x : tybit0 A => @lem7931527 A x)). Qed.
Lemma lem7931529 {A : Type'} : (@all (tybit0 A)) = (@all (tybit0 A)).
Proof. exact (eq_refl (@all (tybit0 A))). Qed.
Lemma lem7931530 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem7931529 A) (@lem7931528 A)). Qed.
Lemma lem7931531 {A : Type'} : (term2 A) = (term17 A).
Proof. exact (MK_COMB (@lem7931526 A) (@lem7931530 A)). Qed.
Lemma lem7931532 {A : Type'} : term17 A.
Proof. exact (EQ_MP (@lem7931531 A) (@lem7931520 A)). Qed.
Lemma lem7931533 {A : Type'} (a' : finite_sum A A) (a : finite_sum A A) (h1 : a' = a) : a' = a.
Proof. exact (h1). Qed.
Lemma lem7931534 {A : Type'} : (@mktybit0 A) = (@mktybit0 A).
Proof. exact (eq_refl (@mktybit0 A)). Qed.
Lemma lem7931535 {A : Type'} (a' : finite_sum A A) (a : finite_sum A A) (h1 : a' = a) : (@mktybit0 A a') = (@mktybit0 A a).
Proof. exact (MK_COMB (@lem7931534 A) (@lem7931533 A a' a h1)). Qed.
Lemma lem7931536 {A : Type'} (a' : finite_sum A A) (a : finite_sum A A) (h1 : a' = a) : (@mktybit0 A a) = (@mktybit0 A a').
Proof. exact (SYM (@lem7931535 A a' a h1)). Qed.
Lemma lem7931537 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) : (term18 A a a') = ((@mktybit0 A a) = (@mktybit0 A a')).
Proof. exact (eq_refl (term18 A a a')). Qed.
Lemma lem7931538 {A : Type'} : term19 A.
Proof. exact (@lem9102 (finite_sum A A)). Qed.
Lemma lem7931539 {A : Type'} (a : finite_sum A A) : term20 A a.
Proof. exact (@lem7931538 A (term21 A a)). Qed.
Lemma lem7931540 {A : Type'} (a : finite_sum A A) : (term20 A a) = (term22 A a).
Proof. exact (eq_refl (term20 A a)). Qed.
Lemma lem7931541 {A : Type'} (a : finite_sum A A) : term22 A a.
Proof. exact (EQ_MP (@lem7931540 A a) (@lem7931539 A a)). Qed.
Lemma lem7931542 {A : Type'} (a : finite_sum A A) : term23 A a.
Proof. exact (@lem7931541 A a a). Qed.
Lemma lem7931543 {A : Type'} (a : finite_sum A A) : (term23 A a) = (term24 A a).
Proof. exact (eq_refl (term23 A a)). Qed.
Lemma lem7931544 {A : Type'} (a : finite_sum A A) : term24 A a.
Proof. exact (EQ_MP (@lem7931543 A a) (@lem7931542 A a)). Qed.
Lemma lem7931545 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) : ((@mktybit0 A a) = (@mktybit0 A a')) = (term18 A a a').
Proof. exact (SYM (@lem7931537 A a a')). Qed.
Lemma lem7931546 {A : Type'} (a' : finite_sum A A) (a : finite_sum A A) (h1 : a' = a) : term18 A a a'.
Proof. exact (EQ_MP (@lem7931545 A a a') (@lem7931536 A a' a h1)). Qed.
Lemma lem7931547 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) : term25 A a a'.
Proof. exact (fun h0 : a' = a => @lem7931546 A a' a h0). Qed.
Lemma lem7931548 {A : Type'} (a : finite_sum A A) : term26 A a.
Proof. exact (fun a' : finite_sum A A => @lem7931547 A a a'). Qed.
Lemma lem7931549 {A : Type'} (a : finite_sum A A) : term5 A a.
Proof. exact (@lem7931544 A a (@lem7931548 A a)). Qed.
Lemma lem7931550 {A : Type'} : term9 A.
Proof. exact (fun a : finite_sum A A => @lem7931549 A a). Qed.
Lemma lem7931551 {A : Type'} : term16 A.
Proof. exact (@lem7931532 A (@lem7931550 A)). Qed.
