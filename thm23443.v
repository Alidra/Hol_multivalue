Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm23443_term_abbrevs.
Require Import EQ_SYM_EQ_spec.
Require Import SELECT_REFL_spec.
Lemma lem23415 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem362 A x). Qed.
Lemma lem23416 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem23417 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem23416 A x) (@lem23415 A x)). Qed.
Lemma lem23418 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem23417 A x y). Qed.
Lemma lem23419 {A : Type'} (y : A) (x : A) : (term2 A x y) = ((x = y) = (y = x)).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem23422 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem23419 A y x) (@lem23418 A x y)). Qed.
Lemma lem23423 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (@lem23422 A y x). Qed.
Lemma lem23424 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (fun_ext (fun y : A => @lem23423 A y x)). Qed.
Lemma lem23425 {A : Type'} : (@ε A) = (@ε A).
Proof. exact (eq_refl (@ε A)). Qed.
Lemma lem23426 {A : Type'} (x : A) : (term5 A x) = (term6 A x).
Proof. exact (MK_COMB (@lem23425 A) (@lem23424 A x)). Qed.
Lemma lem23427 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem23428 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (MK_COMB (@lem23427 A) (@lem23426 A x)). Qed.
Lemma lem23429 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem23430 {A : Type'} (x : A) : ((term5 A x) = x) = ((term6 A x) = x).
Proof. exact (MK_COMB (@lem23428 A x) (@lem23429 A x)). Qed.
Lemma lem23431 {A : Type'} (x : A) : ((term6 A x) = x) = ((term5 A x) = x).
Proof. exact (SYM (@lem23430 A x)). Qed.
Lemma lem23432 {A : Type'} (x : A) : term9 A x.
Proof. exact (@lem9442 A x). Qed.
Lemma lem23433 {A : Type'} (x : A) : (term9 A x) = ((term6 A x) = x).
Proof. exact (eq_refl (term9 A x)). Qed.
Lemma lem23436 {A : Type'} (x : A) : (term6 A x) = x.
Proof. exact (EQ_MP (@lem23433 A x) (@lem23432 A x)). Qed.
Lemma lem23437 {A : Type'} (x : A) : (term6 A x) = x.
Proof. exact (@lem23436 A x). Qed.
Lemma lem23438 {A : Type'} (x : A) : (term5 A x) = x.
Proof. exact (EQ_MP (@lem23431 A x) (@lem23437 A x)). Qed.
Lemma lem23443 {A : Type'} : term10 A.
Proof. exact (fun x : A => @lem23438 A x). Qed.
