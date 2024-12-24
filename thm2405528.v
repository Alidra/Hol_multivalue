Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2405528_term_abbrevs.
Require Import INT_NEG_NEG_spec.
Require Import REAL_NEG_0_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2306330_spec.
Lemma lem2405488 (x : int) : term0 x.
Proof. exact (@lem2306663 x). Qed.
Lemma lem2405489 (x : int) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2405496 : term2 = term3.
Proof. exact (EQ_MP (@lem2306330) (@lem1362041)). Qed.
Lemma lem2405497 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405498 : term4 = term5.
Proof. exact (MK_COMB (@lem2405497) (@lem2405496)). Qed.
Lemma lem2405499 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem2405500 : (term2 = term3) = (term3 = term3).
Proof. exact (MK_COMB (@lem2405498) (@lem2405499)). Qed.
Lemma lem2405502 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405503 (x : int) : (x = x) = True.
Proof. exact (@lem2405502 int x). Qed.
Lemma lem2405504 : (term3 = term3) = True.
Proof. exact (@lem2405503 term3). Qed.
Lemma lem2405505 : (term2 = term3) = True.
Proof. exact (TRANS (@lem2405500) (@lem2405504)). Qed.
Lemma lem2405506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405507 : term6 = (and True).
Proof. exact (MK_COMB (@lem2405506) (@lem2405505)). Qed.
Lemma lem2405511 (x : int) : (term1 x) = x.
Proof. exact (EQ_MP (@lem2405489 x) (@lem2405488 x)). Qed.
Lemma lem2405512 (x : nat) : (term7 x) = (int_of_num x).
Proof. exact (@lem2405511 (int_of_num x)). Qed.
Lemma lem2405513 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405514 (x : nat) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem2405513) (@lem2405512 x)). Qed.
Lemma lem2405515 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem2405516 (x : nat) : ((term7 x) = (int_of_num x)) = ((int_of_num x) = (int_of_num x)).
Proof. exact (MK_COMB (@lem2405514 x) (@lem2405515 x)). Qed.
Lemma lem2405518 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405519 (x : int) : (x = x) = True.
Proof. exact (@lem2405518 int x). Qed.
Lemma lem2405520 (x : nat) : ((int_of_num x) = (int_of_num x)) = True.
Proof. exact (@lem2405519 (int_of_num x)). Qed.
Lemma lem2405521 (x : nat) : ((term7 x) = (int_of_num x)) = True.
Proof. exact (TRANS (@lem2405516 x) (@lem2405520 x)). Qed.
Lemma lem2405522 (x : nat) : (term10 x) = (True /\ True).
Proof. exact (MK_COMB (@lem2405507) (@lem2405521 x)). Qed.
Lemma lem2405524 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2405525 : (True /\ True) = True.
Proof. exact (@lem2405524 True). Qed.
Lemma lem2405526 (x : nat) : (term10 x) = True.
Proof. exact (TRANS (@lem2405522 x) (@lem2405525)). Qed.
Lemma lem2405527 (x : nat) : True = (term10 x).
Proof. exact (SYM (@lem2405526 x)). Qed.
Lemma lem2405528 (x : nat) : term10 x.
Proof. exact (EQ_MP (@lem2405527 x) (@lem0)). Qed.
