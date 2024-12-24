Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_DIV_term_abbrevs.
Require Import REAL_INV_ZPOW_spec.
Require Import REAL_ZPOW_MUL_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3175419 (x : real) : term0 x.
Proof. exact (@lem3175418 x). Qed.
Lemma lem3175420 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3175421 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem3175420 x) (@lem3175419 x)). Qed.
Lemma lem3175422 (x : real) (y : real) : term2 x y.
Proof. exact (@lem3175421 x y). Qed.
Lemma lem3175423 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem3175424 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem3175423 x y) (@lem3175422 x y)). Qed.
Lemma lem3175425 (x : real) (y : real) (n : int) : term4 x y n.
Proof. exact (@lem3175424 x y n). Qed.
Lemma lem3175426 (x : real) (y : real) (n : int) : (term4 x y n) = ((term5 x y n) = (term6 x y n)).
Proof. exact (eq_refl (term4 x y n)). Qed.
Lemma lem3175428 (x : real) : term7 x.
Proof. exact (@lem3174478 x). Qed.
Lemma lem3175429 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem3175430 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem3175429 x) (@lem3175428 x)). Qed.
Lemma lem3175431 (x : real) (n : int) : term9 x n.
Proof. exact (@lem3175430 x n). Qed.
Lemma lem3175432 (x : real) (n : int) : (term9 x n) = ((term10 x n) = (term11 x n)).
Proof. exact (eq_refl (term9 x n)). Qed.
Lemma lem3175434 (x : real) : term12 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem3175435 (x : real) : (term12 x) = (term13 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem3175436 (x : real) : term13 x.
Proof. exact (EQ_MP (@lem3175435 x) (@lem3175434 x)). Qed.
Lemma lem3175437 (x : real) (y : real) : term14 x y.
Proof. exact (@lem3175436 x y). Qed.
Lemma lem3175438 (x : real) (y : real) : (term14 x y) = ((real_div x y) = (term15 x y)).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem3175455 (x : real) (y : real) : (real_div x y) = (term15 x y).
Proof. exact (EQ_MP (@lem3175438 x y) (@lem3175437 x y)). Qed.
Lemma lem3175456 : real_zpow = real_zpow.
Proof. exact (eq_refl real_zpow). Qed.
Lemma lem3175457 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem3175456) (@lem3175455 x y)). Qed.
Lemma lem3175458 (n : int) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3175459 (x : real) (y : real) (n : int) : (term18 x y n) = (term19 x y n).
Proof. exact (MK_COMB (@lem3175457 x y) (@lem3175458 n)). Qed.
Lemma lem3175461 (x : real) (y : real) (n : int) : (term5 x y n) = (term6 x y n).
Proof. exact (EQ_MP (@lem3175426 x y n) (@lem3175425 x y n)). Qed.
Lemma lem3175462 (x : real) (y : real) (n : int) : (term19 x y n) = (term20 x y n).
Proof. exact (@lem3175461 x (real_inv y) n). Qed.
Lemma lem3175463 (x : real) (y : real) (n : int) : (term18 x y n) = (term20 x y n).
Proof. exact (TRANS (@lem3175459 x y n) (@lem3175462 x y n)). Qed.
Lemma lem3175464 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3175465 (x : real) (y : real) (n : int) : (term21 x y n) = (term22 x y n).
Proof. exact (MK_COMB (@lem3175464) (@lem3175463 x y n)). Qed.
Lemma lem3175467 (x : real) (y : real) : (real_div x y) = (term15 x y).
Proof. exact (EQ_MP (@lem3175438 x y) (@lem3175437 x y)). Qed.
Lemma lem3175468 (x : real) (y : real) (n : int) : (term23 x y n) = (term24 x y n).
Proof. exact (@lem3175467 (real_zpow x n) (real_zpow y n)). Qed.
Lemma lem3175470 (x : real) (n : int) : (term10 x n) = (term11 x n).
Proof. exact (EQ_MP (@lem3175432 x n) (@lem3175431 x n)). Qed.
Lemma lem3175471 (y : real) (n : int) : (term10 y n) = (term11 y n).
Proof. exact (@lem3175470 y n). Qed.
Lemma lem3175472 (x : real) (n : int) : (term25 x n) = (term25 x n).
Proof. exact (eq_refl (term25 x n)). Qed.
Lemma lem3175473 (x : real) (y : real) (n : int) : (term24 x y n) = (term20 x y n).
Proof. exact (MK_COMB (@lem3175472 x n) (@lem3175471 y n)). Qed.
Lemma lem3175474 (x : real) (y : real) (n : int) : (term23 x y n) = (term20 x y n).
Proof. exact (TRANS (@lem3175468 x y n) (@lem3175473 x y n)). Qed.
Lemma lem3175475 (x : real) (y : real) (n : int) : ((term18 x y n) = (term23 x y n)) = ((term20 x y n) = (term20 x y n)).
Proof. exact (MK_COMB (@lem3175465 x y n) (@lem3175474 x y n)). Qed.
Lemma lem3175477 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3175478 (x : real) : (x = x) = True.
Proof. exact (@lem3175477 real x). Qed.
Lemma lem3175479 (x : real) (y : real) (n : int) : ((term20 x y n) = (term20 x y n)) = True.
Proof. exact (@lem3175478 (term20 x y n)). Qed.
Lemma lem3175480 (x : real) (y : real) (n : int) : ((term18 x y n) = (term23 x y n)) = True.
Proof. exact (TRANS (@lem3175475 x y n) (@lem3175479 x y n)). Qed.
Lemma lem3175481 (x : real) (y : real) : (term26 x y) = term27.
Proof. exact (fun_ext (fun n : int => @lem3175480 x y n)). Qed.
Lemma lem3175482 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3175483 (x : real) (y : real) : (term28 x y) = term29.
Proof. exact (MK_COMB (@lem3175482) (@lem3175481 x y)). Qed.
Lemma lem3175485 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3175486 (t : Prop) : (term31 t) = t.
Proof. exact (@lem3175485 int t). Qed.
Lemma lem3175487 : term29 = True.
Proof. exact (@lem3175486 True). Qed.
Lemma lem3175488 (x : real) (y : real) : (term28 x y) = True.
Proof. exact (TRANS (@lem3175483 x y) (@lem3175487)). Qed.
Lemma lem3175489 (x : real) : (term32 x) = term33.
Proof. exact (fun_ext (fun y : real => @lem3175488 x y)). Qed.
Lemma lem3175490 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3175491 (x : real) : (term34 x) = term35.
Proof. exact (MK_COMB (@lem3175490) (@lem3175489 x)). Qed.
Lemma lem3175493 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3175494 (t : Prop) : (term36 t) = t.
Proof. exact (@lem3175493 real t). Qed.
Lemma lem3175495 : term35 = True.
Proof. exact (@lem3175494 True). Qed.
Lemma lem3175496 (x : real) : (term34 x) = True.
Proof. exact (TRANS (@lem3175491 x) (@lem3175495)). Qed.
Lemma lem3175497 : term37 = term33.
Proof. exact (fun_ext (fun x : real => @lem3175496 x)). Qed.
Lemma lem3175498 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3175499 : term38 = term35.
Proof. exact (MK_COMB (@lem3175498) (@lem3175497)). Qed.
Lemma lem3175501 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3175502 (t : Prop) : (term36 t) = t.
Proof. exact (@lem3175501 real t). Qed.
Lemma lem3175503 : term35 = True.
Proof. exact (@lem3175502 True). Qed.
Lemma lem3175504 : term38 = True.
Proof. exact (TRANS (@lem3175499) (@lem3175503)). Qed.
Lemma lem3175505 : True = term38.
Proof. exact (SYM (@lem3175504)). Qed.
Lemma lem3175506 : term38.
Proof. exact (EQ_MP (@lem3175505) (@lem0)). Qed.
