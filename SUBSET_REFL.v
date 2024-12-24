Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_REFL_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3217369 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3217370 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3217369 A s t). Qed.
Lemma lem3217371 {A : Type'} (s : A -> Prop) : (@SUBSET A s s) = (term1 A s).
Proof. exact (@lem3217370 A s s). Qed.
Lemma lem3217377 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3217378 {A : Type'} (x : A) (s : A -> Prop) : (term2 A x s) = True.
Proof. exact (@lem3217377 (@IN A x s)). Qed.
Lemma lem3217379 {A : Type'} (s : A -> Prop) : (term3 A s) = (term4 A).
Proof. exact (fun_ext (fun x : A => @lem3217378 A x s)). Qed.
Lemma lem3217380 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217381 {A : Type'} (s : A -> Prop) : (term1 A s) = (term5 A).
Proof. exact (MK_COMB (@lem3217380 A) (@lem3217379 A s)). Qed.
Lemma lem3217383 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3217384 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (@lem3217383 A t). Qed.
Lemma lem3217385 {A : Type'} : (term5 A) = True.
Proof. exact (@lem3217384 A True). Qed.
Lemma lem3217386 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (TRANS (@lem3217381 A s) (@lem3217385 A)). Qed.
Lemma lem3217387 {A : Type'} (s : A -> Prop) : (@SUBSET A s s) = True.
Proof. exact (TRANS (@lem3217371 A s) (@lem3217386 A s)). Qed.
Lemma lem3217388 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3217387 A s)). Qed.
Lemma lem3217389 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3217390 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem3217389 A) (@lem3217388 A)). Qed.
Lemma lem3217392 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3217393 {A : Type'} (t : Prop) : (term11 A t) = t.
Proof. exact (@lem3217392 (A -> Prop) t). Qed.
Lemma lem3217394 {A : Type'} : (term10 A) = True.
Proof. exact (@lem3217393 A True). Qed.
Lemma lem3217395 {A : Type'} : (term9 A) = True.
Proof. exact (TRANS (@lem3217390 A) (@lem3217394 A)). Qed.
Lemma lem3217396 {A : Type'} : True = (term9 A).
Proof. exact (SYM (@lem3217395 A)). Qed.
Lemma lem3217397 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem3217396 A) (@lem0)). Qed.
