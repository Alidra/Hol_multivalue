Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_MUL_term_abbrevs.
Require Import REAL_MUL_AC_spec.
Require Import thm0_spec.
Require Import thm1338986_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1595378 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1595379 (x : real) (y : real) : term1 x y.
Proof. exact (@lem1595378 (term2 x y)). Qed.
Lemma lem1595380 (x : real) (y : real) : (term3 x y) = ((term4 x y) = (term5 x y)).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1595381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1595382 (x : real) (y : real) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem1595381) (@lem1595380 x y)). Qed.
Lemma lem1595383 (x : real) (y : real) (n : nat) : (term8 x y n) = ((term9 x y n) = (term10 x y n)).
Proof. exact (eq_refl (term8 x y n)). Qed.
Lemma lem1595384 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1595385 (x : real) (y : real) (n : nat) : (term11 x y n) = (term12 x y n).
Proof. exact (MK_COMB (@lem1595384) (@lem1595383 x y n)). Qed.
Lemma lem1595386 (x : real) (y : real) (n : nat) : (term13 x y n) = ((term14 x y n) = (term15 x y n)).
Proof. exact (eq_refl (term13 x y n)). Qed.
Lemma lem1595387 (x : real) (y : real) (n : nat) : (term16 x y n) = (term17 x y n).
Proof. exact (MK_COMB (@lem1595385 x y n) (@lem1595386 x y n)). Qed.
Lemma lem1595388 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (fun_ext (fun n : nat => @lem1595387 x y n)). Qed.
Lemma lem1595389 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1595390 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem1595389) (@lem1595388 x y)). Qed.
Lemma lem1595391 (x : real) (y : real) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1595382 x y) (@lem1595390 x y)). Qed.
Lemma lem1595392 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1595393 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1595392) (@lem1595391 x y)). Qed.
Lemma lem1595394 (x : real) (y : real) (n : nat) : (term8 x y n) = ((term9 x y n) = (term10 x y n)).
Proof. exact (eq_refl (term8 x y n)). Qed.
Lemma lem1595395 (x : real) (y : real) : (term26 x y) = (term2 x y).
Proof. exact (fun_ext (fun n : nat => @lem1595394 x y n)). Qed.
Lemma lem1595396 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1595397 (x : real) (y : real) : (term27 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1595396) (@lem1595395 x y)). Qed.
Lemma lem1595398 (x : real) (y : real) : (term1 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1595393 x y) (@lem1595397 x y)). Qed.
Lemma lem1595399 (x : real) (y : real) : term29 x y.
Proof. exact (EQ_MP (@lem1595398 x y) (@lem1595379 x y)). Qed.
Lemma lem1595405 (x : real) : term30 x.
Proof. exact (@lem1338986 x). Qed.
Lemma lem1595406 (x : real) : (term30 x) = ((term31 x) = x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1595416 (x : real) : (term32 x) = term33.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1595417 (x : real) (y : real) : (term4 x y) = term33.
Proof. exact (@lem1595416 (real_mul x y)). Qed.
Lemma lem1595418 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1595419 (x : real) (y : real) : (term34 x y) = term35.
Proof. exact (MK_COMB (@lem1595418) (@lem1595417 x y)). Qed.
Lemma lem1595424 (x : real) : (term32 x) = term33.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1595425 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1595426 (x : real) : (term36 x) = term37.
Proof. exact (MK_COMB (@lem1595425) (@lem1595424 x)). Qed.
Lemma lem1595428 (x : real) : (term32 x) = term33.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1595429 (y : real) : (term32 y) = term33.
Proof. exact (@lem1595428 y). Qed.
Lemma lem1595430 (x : real) (y : real) : (term5 x y) = term38.
Proof. exact (MK_COMB (@lem1595426 x) (@lem1595429 y)). Qed.
Lemma lem1595432 (x : real) : (term31 x) = x.
Proof. exact (EQ_MP (@lem1595406 x) (@lem1595405 x)). Qed.
Lemma lem1595433 : term38 = term33.
Proof. exact (@lem1595432 term33). Qed.
Lemma lem1595434 (x : real) (y : real) : (term5 x y) = term33.
Proof. exact (TRANS (@lem1595430 x y) (@lem1595433)). Qed.
Lemma lem1595435 (x : real) (y : real) : ((term4 x y) = (term5 x y)) = (term33 = term33).
Proof. exact (MK_COMB (@lem1595419 x y) (@lem1595434 x y)). Qed.
Lemma lem1595437 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1595438 (x : real) : (x = x) = True.
Proof. exact (@lem1595437 real x). Qed.
Lemma lem1595439 : (term33 = term33) = True.
Proof. exact (@lem1595438 term33). Qed.
Lemma lem1595440 (x : real) (y : real) : ((term4 x y) = (term5 x y)) = True.
Proof. exact (TRANS (@lem1595435 x y) (@lem1595439)). Qed.
Lemma lem1595441 (x : real) (y : real) : True = ((term4 x y) = (term5 x y)).
Proof. exact (SYM (@lem1595440 x y)). Qed.
Lemma lem1595442 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem1595441 x y) (@lem0)). Qed.
Lemma lem1595443 (n : real) (m : real) (p : real) : term39 n m p.
Proof. exact (proj2 (@lem1486340 n m p)). Qed.
Lemma lem1595450 (x : real) : term40 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1595451 (x : real) (n : nat) : term41 x n.
Proof. exact (@lem1595450 x n). Qed.
Lemma lem1595452 (x : real) (n : nat) : (term41 x n) = ((term42 x n) = (term43 x n)).
Proof. exact (eq_refl (term41 x n)). Qed.
Lemma lem1595458 (x : real) (n : nat) : (term42 x n) = (term43 x n).
Proof. exact (EQ_MP (@lem1595452 x n) (@lem1595451 x n)). Qed.
Lemma lem1595459 (x : real) (y : real) (n : nat) : (term14 x y n) = (term44 x y n).
Proof. exact (@lem1595458 (real_mul x y) n). Qed.
Lemma lem1595461 (m : real) (n : real) (p : real) : (term45 m n p) = (term46 m n p).
Proof. exact (proj1 (@lem1595443 n m p)). Qed.
Lemma lem1595462 (x : real) (y : real) (n : nat) : (term44 x y n) = (term47 x y n).
Proof. exact (@lem1595461 x y (term9 x y n)). Qed.
Lemma lem1595469 (x : real) (y : real) (n : nat) : (term14 x y n) = (term47 x y n).
Proof. exact (TRANS (@lem1595459 x y n) (@lem1595462 x y n)). Qed.
Lemma lem1595474 (x : real) (y : real) (n : nat) (h1 : (term9 x y n) = (term10 x y n)) : (term9 x y n) = (term10 x y n).
Proof. exact (h1). Qed.
Lemma lem1595478 (y : real) : (real_mul y) = (real_mul y).
Proof. exact (eq_refl (real_mul y)). Qed.
Lemma lem1595479 (x : real) (y : real) (n : nat) (h1 : (term9 x y n) = (term10 x y n)) : (term48 x y n) = (term49 x y n).
Proof. exact (MK_COMB (@lem1595478 y) (@lem1595474 x y n h1)). Qed.
Lemma lem1595486 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1595487 (x : real) (y : real) (n : nat) (h1 : (term9 x y n) = (term10 x y n)) : (term47 x y n) = (term50 x y n).
Proof. exact (MK_COMB (@lem1595486 x) (@lem1595479 x y n h1)). Qed.
Lemma lem1595494 (x : real) (y : real) (n : nat) (h1 : (term9 x y n) = (term10 x y n)) : (term14 x y n) = (term50 x y n).
Proof. exact (TRANS (@lem1595469 x y n) (@lem1595487 x y n h1)). Qed.
Lemma lem1595495 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1595496 (x : real) (y : real) (n : nat) (h1 : (term9 x y n) = (term10 x y n)) : (term51 x y n) = (term52 x y n).
Proof. exact (MK_COMB (@lem1595495) (@lem1595494 x y n h1)). Qed.
Lemma lem1595501 (x : real) (n : nat) : (term42 x n) = (term43 x n).
Proof. exact (EQ_MP (@lem1595452 x n) (@lem1595451 x n)). Qed.
Lemma lem1595505 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1595506 (x : real) (n : nat) : (term53 x n) = (term54 x n).
Proof. exact (MK_COMB (@lem1595505) (@lem1595501 x n)). Qed.
Lemma lem1595508 (x : real) (n : nat) : (term42 x n) = (term43 x n).
Proof. exact (EQ_MP (@lem1595452 x n) (@lem1595451 x n)). Qed.
Lemma lem1595509 (y : real) (n : nat) : (term42 y n) = (term43 y n).
Proof. exact (@lem1595508 y n). Qed.
Lemma lem1595513 (x : real) (y : real) (n : nat) : (term15 x y n) = (term55 x y n).
Proof. exact (MK_COMB (@lem1595506 x n) (@lem1595509 y n)). Qed.
Lemma lem1595515 (m : real) (n : real) (p : real) : (term45 m n p) = (term46 m n p).
Proof. exact (proj1 (@lem1595443 n m p)). Qed.
Lemma lem1595516 (x : real) (y : real) (n : nat) : (term55 x y n) = (term56 x y n).
Proof. exact (@lem1595515 x (real_pow x n) (term43 y n)). Qed.
Lemma lem1595524 (n : real) (m : real) (p : real) : (term46 m n p) = (term46 n m p).
Proof. exact (proj2 (@lem1595443 n m p)). Qed.
Lemma lem1595525 (x : real) (y : real) (n : nat) : (term57 x y n) = (term49 x y n).
Proof. exact (@lem1595524 y (real_pow x n) (real_pow y n)). Qed.
Lemma lem1595535 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1595536 (x : real) (y : real) (n : nat) : (term56 x y n) = (term50 x y n).
Proof. exact (MK_COMB (@lem1595535 x) (@lem1595525 x y n)). Qed.
Lemma lem1595543 (x : real) (y : real) (n : nat) : (term55 x y n) = (term50 x y n).
Proof. exact (TRANS (@lem1595516 x y n) (@lem1595536 x y n)). Qed.
Lemma lem1595544 (x : real) (y : real) (n : nat) : (term15 x y n) = (term50 x y n).
Proof. exact (TRANS (@lem1595513 x y n) (@lem1595543 x y n)). Qed.
Lemma lem1595545 (x : real) (y : real) (n : nat) (h1 : (term9 x y n) = (term10 x y n)) : ((term14 x y n) = (term15 x y n)) = ((term50 x y n) = (term50 x y n)).
Proof. exact (MK_COMB (@lem1595496 x y n h1) (@lem1595544 x y n)). Qed.
Lemma lem1595547 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1595548 (x : real) : (x = x) = True.
Proof. exact (@lem1595547 real x). Qed.
Lemma lem1595549 (x : real) (y : real) (n : nat) : ((term50 x y n) = (term50 x y n)) = True.
Proof. exact (@lem1595548 (term50 x y n)). Qed.
Lemma lem1595550 (x : real) (y : real) (n : nat) (h1 : (term9 x y n) = (term10 x y n)) : ((term14 x y n) = (term15 x y n)) = True.
Proof. exact (TRANS (@lem1595545 x y n h1) (@lem1595549 x y n)). Qed.
Lemma lem1595551 (x : real) (y : real) (n : nat) (h1 : (term9 x y n) = (term10 x y n)) : True = ((term14 x y n) = (term15 x y n)).
Proof. exact (SYM (@lem1595550 x y n h1)). Qed.
Lemma lem1595552 (x : real) (y : real) (n : nat) (h1 : (term9 x y n) = (term10 x y n)) : (term14 x y n) = (term15 x y n).
Proof. exact (EQ_MP (@lem1595551 x y n h1) (@lem0)). Qed.
Lemma lem1595553 (x : real) (y : real) (n : nat) : term17 x y n.
Proof. exact (fun h0 : (term9 x y n) = (term10 x y n) => @lem1595552 x y n h0). Qed.
Lemma lem1595558 (x : real) (y : real) : term21 x y.
Proof. exact (fun n : nat => @lem1595553 x y n). Qed.
Lemma lem1595559 (x : real) (y : real) : term23 x y.
Proof. exact (conj (@lem1595442 x y) (@lem1595558 x y)). Qed.
Lemma lem1595560 (x : real) (y : real) : term28 x y.
Proof. exact (@lem1595399 x y (@lem1595559 x y)). Qed.
Lemma lem1595565 (x : real) : term58 x.
Proof. exact (fun y : real => @lem1595560 x y). Qed.
Lemma lem1595570 : term59.
Proof. exact (fun x : real => @lem1595565 x). Qed.
