Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_SYM_EQ_term_abbrevs.
Require Import EQ_SYM_spec.
Require Import thm32_spec.
Lemma lem331 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem330 A x). Qed.
Lemma lem332 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem333 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem332 A x) (@lem331 A x)). Qed.
Lemma lem334 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem333 A x y). Qed.
Lemma lem335 {A : Type'} (y : A) (x : A) : (term2 A x y) = (term3 A y x).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem338 {A : Type'} (y : A) (x : A) : term3 A y x.
Proof. exact (EQ_MP (@lem335 A y x) (@lem334 A x y)). Qed.
Lemma lem339 {A : Type'} (y : A) (x : A) : term3 A y x.
Proof. exact (@lem338 A y x). Qed.
Lemma lem340 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem330 A x). Qed.
Lemma lem341 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem342 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem341 A x) (@lem340 A x)). Qed.
Lemma lem343 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem342 A x y). Qed.
Lemma lem344 {A : Type'} (y : A) (x : A) : (term2 A x y) = (term3 A y x).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem347 {A : Type'} (y : A) (x : A) : term3 A y x.
Proof. exact (EQ_MP (@lem344 A y x) (@lem343 A x y)). Qed.
Lemma lem348 {A : Type'} (y : A) (x : A) : term3 A y x.
Proof. exact (@lem347 A y x). Qed.
Lemma lem349 {A : Type'} (x : A) (y : A) : term3 A x y.
Proof. exact (@lem348 A x y). Qed.
Lemma lem350 {A : Type'} (x : A) (y : A) : term4 A x y.
Proof. exact (conj (@lem339 A y x) (@lem349 A x y)). Qed.
Lemma lem351 {A : Type'} (y : A) (x : A) : (term4 A x y) = ((x = y) = (y = x)).
Proof. exact (@lem32 (x = y) (y = x)). Qed.
Lemma lem352 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem351 A y x) (@lem350 A x y)). Qed.
Lemma lem357 {A : Type'} (x : A) : term5 A x.
Proof. exact (fun y : A => @lem352 A y x). Qed.
Lemma lem362 {A : Type'} : term6 A.
Proof. exact (fun x : A => @lem357 A x). Qed.
