Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_ONE_term_abbrevs.
Require Import COND_ID_spec.
Require Import REAL_POW_ONE_spec.
Require Import real_zpow_spec.
Require Import thm0_spec.
Require Import thm1592014_spec.
Require Import thm1592030_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3169426 {A : Type'} (b : Prop) : term0 A b.
Proof. exact (@lem12860 A b). Qed.
Lemma lem3169427 {A : Type'} (b : Prop) : (term0 A b) = (term1 A b).
Proof. exact (eq_refl (term0 A b)). Qed.
Lemma lem3169428 {A : Type'} (b : Prop) : term1 A b.
Proof. exact (EQ_MP (@lem3169427 A b) (@lem3169426 A b)). Qed.
Lemma lem3169429 {A : Type'} (b : Prop) (t : A) : term2 A b t.
Proof. exact (@lem3169428 A b t). Qed.
Lemma lem3169430 {A : Type'} (b : Prop) (t : A) : (term2 A b t) = ((@COND A b t t) = t).
Proof. exact (eq_refl (term2 A b t)). Qed.
Lemma lem3169432 (n : nat) : term3 n.
Proof. exact (@lem1631092 n). Qed.
Lemma lem3169433 (n : nat) : (term3 n) = ((term4 n) = term5).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem3169435 (z : real) : term6 z.
Proof. exact (@lem3169164 z). Qed.
Lemma lem3169436 (z : real) : (term6 z) = (term7 z).
Proof. exact (eq_refl (term6 z)). Qed.
Lemma lem3169437 (z : real) : term7 z.
Proof. exact (EQ_MP (@lem3169436 z) (@lem3169435 z)). Qed.
Lemma lem3169438 (z : real) (i : int) : term8 z i.
Proof. exact (@lem3169437 z i). Qed.
Lemma lem3169439 (z : real) (i : int) : (term8 z i) = ((real_zpow z i) = (term9 z i)).
Proof. exact (eq_refl (term8 z i)). Qed.
Lemma lem3169448 (z : real) (i : int) : (real_zpow z i) = (term9 z i).
Proof. exact (EQ_MP (@lem3169439 z i) (@lem3169438 z i)). Qed.
Lemma lem3169449 (n : int) : (term10 n) = (term11 n).
Proof. exact (@lem3169448 term5 n). Qed.
Lemma lem3169453 (n : nat) : (term4 n) = term5.
Proof. exact (EQ_MP (@lem3169433 n) (@lem3169432 n)). Qed.
Lemma lem3169454 (n : int) : (term12 n) = term5.
Proof. exact (@lem3169453 (num_of_int n)). Qed.
Lemma lem3169455 (n : int) : (term13 n) = (term13 n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem3169456 (n : int) : (term14 n) = (term15 n).
Proof. exact (MK_COMB (@lem3169455 n) (@lem3169454 n)). Qed.
Lemma lem3169458 (n : nat) : (term4 n) = term5.
Proof. exact (EQ_MP (@lem3169433 n) (@lem3169432 n)). Qed.
Lemma lem3169459 (n : int) : (term16 n) = term5.
Proof. exact (@lem3169458 (term17 n)). Qed.
Lemma lem3169460 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3169461 (n : int) : (term18 n) = term19.
Proof. exact (MK_COMB (@lem3169460) (@lem3169459 n)). Qed.
Lemma lem3169463 : term19 = term5.
Proof. exact (@lem1592014 (@lem1592030)). Qed.
Lemma lem3169464 (n : int) : (term18 n) = term5.
Proof. exact (TRANS (@lem3169461 n) (@lem3169463)). Qed.
Lemma lem3169465 (n : int) : (term11 n) = (term20 n).
Proof. exact (MK_COMB (@lem3169456 n) (@lem3169464 n)). Qed.
Lemma lem3169467 {A : Type'} (b : Prop) (t : A) : (@COND A b t t) = t.
Proof. exact (EQ_MP (@lem3169430 A b t) (@lem3169429 A b t)). Qed.
Lemma lem3169468 (b : Prop) (t : real) : (@COND real b t t) = t.
Proof. exact (@lem3169467 real b t). Qed.
Lemma lem3169469 (n : int) : (term20 n) = term5.
Proof. exact (@lem3169468 (term21 n) term5). Qed.
Lemma lem3169470 (n : int) : (term11 n) = term5.
Proof. exact (TRANS (@lem3169465 n) (@lem3169469 n)). Qed.
Lemma lem3169471 (n : int) : (term10 n) = term5.
Proof. exact (TRANS (@lem3169449 n) (@lem3169470 n)). Qed.
Lemma lem3169472 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3169473 (n : int) : (term22 n) = term23.
Proof. exact (MK_COMB (@lem3169472) (@lem3169471 n)). Qed.
Lemma lem3169474 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem3169475 (n : int) : ((term10 n) = term5) = (term5 = term5).
Proof. exact (MK_COMB (@lem3169473 n) (@lem3169474)). Qed.
Lemma lem3169477 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3169478 (x : real) : (x = x) = True.
Proof. exact (@lem3169477 real x). Qed.
Lemma lem3169479 : (term5 = term5) = True.
Proof. exact (@lem3169478 term5). Qed.
Lemma lem3169480 (n : int) : ((term10 n) = term5) = True.
Proof. exact (TRANS (@lem3169475 n) (@lem3169479)). Qed.
Lemma lem3169481 : term24 = term25.
Proof. exact (fun_ext (fun n : int => @lem3169480 n)). Qed.
Lemma lem3169482 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3169483 : term26 = term27.
Proof. exact (MK_COMB (@lem3169482) (@lem3169481)). Qed.
Lemma lem3169485 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3169486 (t : Prop) : (term29 t) = t.
Proof. exact (@lem3169485 int t). Qed.
Lemma lem3169487 : term27 = True.
Proof. exact (@lem3169486 True). Qed.
Lemma lem3169488 : term26 = True.
Proof. exact (TRANS (@lem3169483) (@lem3169487)). Qed.
Lemma lem3169489 : True = term26.
Proof. exact (SYM (@lem3169488)). Qed.
Lemma lem3169490 : term26.
Proof. exact (EQ_MP (@lem3169489) (@lem0)). Qed.
