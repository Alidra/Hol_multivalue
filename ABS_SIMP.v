Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ABS_SIMP_term_abbrevs.
Require Import BETA_THM_spec.
Require Import REFL_CLAUSE_spec.
Require Import thm0_spec.
Lemma lem422 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem423 {A : Type'} (x : A) : (term0 A x) = ((x = x) = True).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem425 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem426 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem427 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem426 A B f) (@lem425 A B f)). Qed.
Lemma lem428 {A B : Type'} (f : A -> B) (y : A) : term3 A B f y.
Proof. exact (@lem427 A B f y). Qed.
Lemma lem429 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = ((term4 A B f y) = (f y)).
Proof. exact (eq_refl (term3 A B f y)). Qed.
Lemma lem434 {A B : Type'} (f : A -> B) (y : A) : (term4 A B f y) = (f y).
Proof. exact (EQ_MP (@lem429 A B f y) (@lem428 A B f y)). Qed.
Lemma lem435 {A B : Type'} (f : B -> A) (y : B) : (term5 A B f y) = (f y).
Proof. exact (@lem434 B A f y). Qed.
Lemma lem436 {A B : Type'} (t1 : A) (t2 : B) : (term6 A B t1 t2) = (term7 A B t1 t2).
Proof. exact (@lem435 A B (term8 A B t1) t2). Qed.
Lemma lem437 {A B : Type'} (x : B) (t1 : A) : (term7 A B t1 x) = t1.
Proof. exact (eq_refl (term7 A B t1 x)). Qed.
Lemma lem438 {A B : Type'} (t1 : A) : (term9 A B t1) = (term8 A B t1).
Proof. exact (fun_ext (fun x : B => @lem437 A B x t1)). Qed.
Lemma lem439 {B : Type'} (t2 : B) : t2 = t2.
Proof. exact (eq_refl t2). Qed.
Lemma lem440 {A B : Type'} (t1 : A) (t2 : B) : (term6 A B t1 t2) = (term7 A B t1 t2).
Proof. exact (MK_COMB (@lem438 A B t1) (@lem439 B t2)). Qed.
Lemma lem441 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem442 {A B : Type'} (t1 : A) (t2 : B) : (term10 A B t1 t2) = (term11 A B t1 t2).
Proof. exact (MK_COMB (@lem441 A) (@lem440 A B t1 t2)). Qed.
Lemma lem443 {A B : Type'} (t2 : B) (t1 : A) : (term7 A B t1 t2) = t1.
Proof. exact (eq_refl (term7 A B t1 t2)). Qed.
Lemma lem444 {A B : Type'} (t2 : B) (t1 : A) : ((term6 A B t1 t2) = (term7 A B t1 t2)) = ((term7 A B t1 t2) = t1).
Proof. exact (MK_COMB (@lem442 A B t1 t2) (@lem443 A B t2 t1)). Qed.
Lemma lem445 {A B : Type'} (t2 : B) (t1 : A) : (term7 A B t1 t2) = t1.
Proof. exact (EQ_MP (@lem444 A B t2 t1) (@lem436 A B t1 t2)). Qed.
Lemma lem446 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem447 {A B : Type'} (t2 : B) (t1 : A) : (term11 A B t1 t2) = (@eq A t1).
Proof. exact (MK_COMB (@lem446 A) (@lem445 A B t2 t1)). Qed.
Lemma lem448 {A : Type'} (t1 : A) : t1 = t1.
Proof. exact (eq_refl t1). Qed.
Lemma lem449 {A B : Type'} (t2 : B) (t1 : A) : ((term7 A B t1 t2) = t1) = (t1 = t1).
Proof. exact (MK_COMB (@lem447 A B t2 t1) (@lem448 A t1)). Qed.
Lemma lem451 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem423 A x) (@lem422 A x)). Qed.
Lemma lem452 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem451 A x). Qed.
Lemma lem453 {A : Type'} (t1 : A) : (t1 = t1) = True.
Proof. exact (@lem452 A t1). Qed.
Lemma lem454 {A B : Type'} (t2 : B) (t1 : A) : ((term7 A B t1 t2) = t1) = True.
Proof. exact (TRANS (@lem449 A B t2 t1) (@lem453 A t1)). Qed.
Lemma lem455 {A B : Type'} (t2 : B) (t1 : A) : True = ((term7 A B t1 t2) = t1).
Proof. exact (SYM (@lem454 A B t2 t1)). Qed.
Lemma lem456 {A B : Type'} (t2 : B) (t1 : A) : (term7 A B t1 t2) = t1.
Proof. exact (EQ_MP (@lem455 A B t2 t1) (@lem0)). Qed.
Lemma lem461 {A B : Type'} (t1 : A) : term12 A B t1.
Proof. exact (fun t2 : B => @lem456 A B t2 t1). Qed.
Lemma lem466 {A B : Type'} : term13 A B.
Proof. exact (fun t1 : A => @lem461 A B t1). Qed.
