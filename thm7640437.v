Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7640437_term_abbrevs.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7640394_spec.
Require Import thm7640396_spec.
Require Import thm7640397_spec.
Lemma lem7640414 {M N : Type'} : (@FINITE (finite_sum M N) (@UNIV (finite_sum M N))) = True.
Proof. exact (EQ_MP (@lem7640397 M N) (@lem7640396 M N)). Qed.
Lemma lem7640415 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7640416 {M N : Type'} : (term0 M N) = (@COND nat True).
Proof. exact (MK_COMB (@lem7640415) (@lem7640414 M N)). Qed.
Lemma lem7640418 {M N : Type'} : (@CARD (finite_sum M N) (@UNIV (finite_sum M N))) = (term1 M N).
Proof. exact (proj2 (@lem7640394 M N)). Qed.
Lemma lem7640419 {M N : Type'} : (term2 M N) = (term3 M N).
Proof. exact (MK_COMB (@lem7640416 M N) (@lem7640418 M N)). Qed.
Lemma lem7640420 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem7640421 {M N : Type'} : (term5 M N) = (term6 M N).
Proof. exact (MK_COMB (@lem7640419 M N) (@lem7640420)). Qed.
Lemma lem7640423 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7640424 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7640423 nat t2 t1). Qed.
Lemma lem7640425 {M N : Type'} : (term6 M N) = (term1 M N).
Proof. exact (@lem7640424 term4 (term1 M N)). Qed.
Lemma lem7640426 {M N : Type'} : (term5 M N) = (term1 M N).
Proof. exact (TRANS (@lem7640421 M N) (@lem7640425 M N)). Qed.
Lemma lem7640427 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7640428 {M N : Type'} : (term7 M N) = (term8 M N).
Proof. exact (MK_COMB (@lem7640427) (@lem7640426 M N)). Qed.
Lemma lem7640429 {M N : Type'} : (term1 M N) = (term1 M N).
Proof. exact (eq_refl (term1 M N)). Qed.
Lemma lem7640430 {M N : Type'} : ((term5 M N) = (term1 M N)) = ((term1 M N) = (term1 M N)).
Proof. exact (MK_COMB (@lem7640428 M N) (@lem7640429 M N)). Qed.
Lemma lem7640432 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7640433 (x : nat) : (x = x) = True.
Proof. exact (@lem7640432 nat x). Qed.
Lemma lem7640434 {M N : Type'} : ((term1 M N) = (term1 M N)) = True.
Proof. exact (@lem7640433 (term1 M N)). Qed.
Lemma lem7640435 {M N : Type'} : ((term5 M N) = (term1 M N)) = True.
Proof. exact (TRANS (@lem7640430 M N) (@lem7640434 M N)). Qed.
Lemma lem7640436 {M N : Type'} : True = ((term5 M N) = (term1 M N)).
Proof. exact (SYM (@lem7640435 M N)). Qed.
Lemma lem7640437 {M N : Type'} : (term5 M N) = (term1 M N).
Proof. exact (EQ_MP (@lem7640436 M N) (@lem0)). Qed.
