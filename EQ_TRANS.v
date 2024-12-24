Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_TRANS_term_abbrevs.
Lemma lem363 {A : Type'} (x : A) (y : A) (z : A) (h1 : term0 A x y z) : term0 A x y z.
Proof. exact (h1). Qed.
Lemma lem364 {A : Type'} (y : A) (z : A) (h1 : y = z) : y = z.
Proof. exact (h1). Qed.
Lemma lem365 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem367 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem369 {A : Type'} (y : A) (z : A) (h1 : y = z) : y = z.
Proof. exact (h1). Qed.
Lemma lem370 {A : Type'} (x : A) (y : A) (z : A) (h1 : x = y) (h2 : y = z) : x = z.
Proof. exact (TRANS (@lem367 A x y h1) (@lem369 A y z h2)). Qed.
Lemma lem371 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem372 {A : Type'} (x : A) (y : A) (z : A) (h1 : x = y) (h2 : y = z) : (@eq A x) = (@eq A z).
Proof. exact (MK_COMB (@lem371 A) (@lem370 A x y z h1 h2)). Qed.
Lemma lem373 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem374 {A : Type'} (x : A) (y : A) (z : A) (h1 : x = y) (h2 : y = z) : (x = z) = (z = z).
Proof. exact (MK_COMB (@lem372 A x y z h1 h2) (@lem373 A z)). Qed.
Lemma lem375 {A : Type'} (x : A) (y : A) (z : A) (h1 : x = y) (h2 : y = z) : (z = z) = (x = z).
Proof. exact (SYM (@lem374 A x y z h1 h2)). Qed.
Lemma lem376 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem377 {A : Type'} (x : A) (y : A) (z : A) (h1 : x = y) (h2 : y = z) : x = z.
Proof. exact (EQ_MP (@lem375 A x y z h1 h2) (@lem376 A z)). Qed.
Lemma lem378 {A : Type'} (x : A) (y : A) (z : A) (h1 : term0 A x y z) : y = z.
Proof. exact (proj2 (@lem363 A x y z h1)). Qed.
Lemma lem379 {A : Type'} (x : A) (y : A) (z : A) (h1 : term0 A x y z) : x = y.
Proof. exact (proj1 (@lem363 A x y z h1)). Qed.
Lemma lem380 {A : Type'} (x : A) (y : A) (z : A) (h1 : x = y) (h2 : y = z) : (y = z) = (x = z).
Proof. exact (prop_ext (fun h3 : y = z => @lem377 A x y z h1 h2) (fun h3 : x = z => @lem364 A y z h2)). Qed.
Lemma lem381 {A : Type'} (x : A) (y : A) (z : A) (h1 : x = y) (h2 : y = z) : x = z.
Proof. exact (EQ_MP (@lem380 A x y z h1 h2) (@lem364 A y z h2)). Qed.
Lemma lem382 {A : Type'} (x : A) (y : A) (z : A) (h1 : x = y) (h2 : y = z) : (x = y) = (x = z).
Proof. exact (prop_ext (fun h3 : x = y => @lem381 A x y z h1 h2) (fun h3 : x = z => @lem365 A x y h1)). Qed.
Lemma lem383 {A : Type'} (x : A) (y : A) (z : A) (h1 : x = y) (h2 : y = z) : x = z.
Proof. exact (EQ_MP (@lem382 A x y z h1 h2) (@lem365 A x y h1)). Qed.
Lemma lem384 {A : Type'} (z : A) (x : A) (y : A) (h1 : term0 A x y z) (h2 : x = y) : (y = z) = (x = z).
Proof. exact (prop_ext (fun h3 : y = z => @lem383 A x y z h2 h3) (fun h3 : x = z => @lem378 A x y z h1)). Qed.
Lemma lem385 {A : Type'} (z : A) (x : A) (y : A) (h1 : term0 A x y z) (h2 : x = y) : x = z.
Proof. exact (EQ_MP (@lem384 A z x y h1 h2) (@lem378 A x y z h1)). Qed.
Lemma lem386 {A : Type'} (x : A) (y : A) (z : A) (h1 : term0 A x y z) : (x = y) = (x = z).
Proof. exact (prop_ext (fun h2 : x = y => @lem385 A z x y h1 h2) (fun h2 : x = z => @lem379 A x y z h1)). Qed.
Lemma lem387 {A : Type'} (x : A) (y : A) (z : A) (h1 : term0 A x y z) : x = z.
Proof. exact (EQ_MP (@lem386 A x y z h1) (@lem379 A x y z h1)). Qed.
Lemma lem388 {A : Type'} (y : A) (x : A) (z : A) : term1 A y x z.
Proof. exact (fun h0 : term0 A x y z => @lem387 A x y z h0). Qed.
Lemma lem393 {A : Type'} (y : A) (x : A) : term2 A y x.
Proof. exact (fun z : A => @lem388 A y x z). Qed.
Lemma lem398 {A : Type'} (x : A) : term3 A x.
Proof. exact (fun y : A => @lem393 A y x). Qed.
Lemma lem403 {A : Type'} : term4 A.
Proof. exact (fun x : A => @lem398 A x). Qed.
