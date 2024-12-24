Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_NUM_POW_term_abbrevs.
Require Import thm0_spec.
Require Import thm1340396_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm86199_spec.
Lemma lem1362467 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1362468 (x : nat) : term1 x.
Proof. exact (@lem1362467 (term2 x)). Qed.
Lemma lem1362469 (x : nat) : (term3 x) = ((term4 x) = (term5 x)).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1362470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1362471 (x : nat) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem1362470) (@lem1362469 x)). Qed.
Lemma lem1362472 (x : nat) (n : nat) : (term8 x n) = ((term9 x n) = (term10 x n)).
Proof. exact (eq_refl (term8 x n)). Qed.
Lemma lem1362473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1362474 (x : nat) (n : nat) : (term11 x n) = (term12 x n).
Proof. exact (MK_COMB (@lem1362473) (@lem1362472 x n)). Qed.
Lemma lem1362475 (x : nat) (n : nat) : (term13 x n) = ((term14 x n) = (term15 x n)).
Proof. exact (eq_refl (term13 x n)). Qed.
Lemma lem1362476 (x : nat) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (MK_COMB (@lem1362474 x n) (@lem1362475 x n)). Qed.
Lemma lem1362477 (x : nat) : (term18 x) = (term19 x).
Proof. exact (fun_ext (fun n : nat => @lem1362476 x n)). Qed.
Lemma lem1362478 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1362479 (x : nat) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem1362478) (@lem1362477 x)). Qed.
Lemma lem1362480 (x : nat) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem1362471 x) (@lem1362479 x)). Qed.
Lemma lem1362481 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1362482 (x : nat) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1362481) (@lem1362480 x)). Qed.
Lemma lem1362483 (x : nat) (n : nat) : (term8 x n) = ((term9 x n) = (term10 x n)).
Proof. exact (eq_refl (term8 x n)). Qed.
Lemma lem1362484 (x : nat) : (term26 x) = (term2 x).
Proof. exact (fun_ext (fun n : nat => @lem1362483 x n)). Qed.
Lemma lem1362485 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1362486 (x : nat) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1362485) (@lem1362484 x)). Qed.
Lemma lem1362487 (x : nat) : (term1 x) = (term29 x).
Proof. exact (MK_COMB (@lem1362482 x) (@lem1362486 x)). Qed.
Lemma lem1362488 (x : nat) : term29 x.
Proof. exact (EQ_MP (@lem1362487 x) (@lem1362468 x)). Qed.
Lemma lem1362503 : term30.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem1362504 (m : nat) : term31 m.
Proof. exact (@lem1362503 m). Qed.
Lemma lem1362505 (m : nat) : (term31 m) = ((term32 m) = term33).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem1362515 (x : real) : (term34 x) = term35.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1362516 (x : nat) : (term4 x) = term35.
Proof. exact (@lem1362515 (real_of_num x)). Qed.
Lemma lem1362517 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1362518 (x : nat) : (term36 x) = term37.
Proof. exact (MK_COMB (@lem1362517) (@lem1362516 x)). Qed.
Lemma lem1362520 (m : nat) : (term32 m) = term33.
Proof. exact (EQ_MP (@lem1362505 m) (@lem1362504 m)). Qed.
Lemma lem1362521 (x : nat) : (term32 x) = term33.
Proof. exact (@lem1362520 x). Qed.
Lemma lem1362522 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1362523 (x : nat) : (term5 x) = term35.
Proof. exact (MK_COMB (@lem1362522) (@lem1362521 x)). Qed.
Lemma lem1362524 (x : nat) : ((term4 x) = (term5 x)) = (term35 = term35).
Proof. exact (MK_COMB (@lem1362518 x) (@lem1362523 x)). Qed.
Lemma lem1362526 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1362527 (x : real) : (x = x) = True.
Proof. exact (@lem1362526 real x). Qed.
Lemma lem1362528 : (term35 = term35) = True.
Proof. exact (@lem1362527 term35). Qed.
Lemma lem1362529 (x : nat) : ((term4 x) = (term5 x)) = True.
Proof. exact (TRANS (@lem1362524 x) (@lem1362528)). Qed.
Lemma lem1362530 (x : nat) : True = ((term4 x) = (term5 x)).
Proof. exact (SYM (@lem1362529 x)). Qed.
Lemma lem1362531 (x : nat) : (term4 x) = (term5 x).
Proof. exact (EQ_MP (@lem1362530 x) (@lem0)). Qed.
Lemma lem1362532 (m : nat) : term38 m.
Proof. exact (@lem1340396 m). Qed.
Lemma lem1362533 (m : nat) : (term38 m) = (term39 m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem1362534 (m : nat) : term39 m.
Proof. exact (EQ_MP (@lem1362533 m) (@lem1362532 m)). Qed.
Lemma lem1362535 (m : nat) (n : nat) : term40 m n.
Proof. exact (@lem1362534 m n). Qed.
Lemma lem1362536 (m : nat) (n : nat) : (term40 m n) = ((term41 m n) = (term42 m n)).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem1362538 : term43.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem1362539 (m : nat) : term44 m.
Proof. exact (@lem1362538 m). Qed.
Lemma lem1362540 (m : nat) : (term44 m) = (term45 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem1362541 (m : nat) : term45 m.
Proof. exact (EQ_MP (@lem1362540 m) (@lem1362539 m)). Qed.
Lemma lem1362542 (m : nat) (n : nat) : term46 m n.
Proof. exact (@lem1362541 m n). Qed.
Lemma lem1362543 (m : nat) (n : nat) : (term46 m n) = ((term47 m n) = (term48 m n)).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem1362549 (x : real) : term49 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1362550 (x : real) (n : nat) : term50 x n.
Proof. exact (@lem1362549 x n). Qed.
Lemma lem1362551 (x : real) (n : nat) : (term50 x n) = ((term51 x n) = (term52 x n)).
Proof. exact (eq_refl (term50 x n)). Qed.
Lemma lem1362557 (x : real) (n : nat) : (term51 x n) = (term52 x n).
Proof. exact (EQ_MP (@lem1362551 x n) (@lem1362550 x n)). Qed.
Lemma lem1362558 (x : nat) (n : nat) : (term14 x n) = (term53 x n).
Proof. exact (@lem1362557 (real_of_num x) n). Qed.
Lemma lem1362560 (x : nat) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term9 x n) = (term10 x n).
Proof. exact (h1). Qed.
Lemma lem1362561 (x : nat) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1362562 (x : nat) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term53 x n) = (term55 x n).
Proof. exact (MK_COMB (@lem1362561 x) (@lem1362560 x n h1)). Qed.
Lemma lem1362564 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (EQ_MP (@lem1362536 m n) (@lem1362535 m n)). Qed.
Lemma lem1362565 (x : nat) (n : nat) : (term55 x n) = (term56 x n).
Proof. exact (@lem1362564 x (Nat.pow x n)). Qed.
Lemma lem1362566 (x : nat) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term53 x n) = (term56 x n).
Proof. exact (TRANS (@lem1362562 x n h1) (@lem1362565 x n)). Qed.
Lemma lem1362567 (x : nat) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term14 x n) = (term56 x n).
Proof. exact (TRANS (@lem1362558 x n) (@lem1362566 x n h1)). Qed.
Lemma lem1362568 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1362569 (x : nat) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term57 x n) = (term58 x n).
Proof. exact (MK_COMB (@lem1362568) (@lem1362567 x n h1)). Qed.
Lemma lem1362571 (m : nat) (n : nat) : (term47 m n) = (term48 m n).
Proof. exact (EQ_MP (@lem1362543 m n) (@lem1362542 m n)). Qed.
Lemma lem1362572 (x : nat) (n : nat) : (term47 x n) = (term48 x n).
Proof. exact (@lem1362571 x n). Qed.
Lemma lem1362573 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1362574 (x : nat) (n : nat) : (term15 x n) = (term56 x n).
Proof. exact (MK_COMB (@lem1362573) (@lem1362572 x n)). Qed.
Lemma lem1362575 (x : nat) (n : nat) (h1 : (term9 x n) = (term10 x n)) : ((term14 x n) = (term15 x n)) = ((term56 x n) = (term56 x n)).
Proof. exact (MK_COMB (@lem1362569 x n h1) (@lem1362574 x n)). Qed.
Lemma lem1362577 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1362578 (x : real) : (x = x) = True.
Proof. exact (@lem1362577 real x). Qed.
Lemma lem1362579 (x : nat) (n : nat) : ((term56 x n) = (term56 x n)) = True.
Proof. exact (@lem1362578 (term56 x n)). Qed.
Lemma lem1362580 (x : nat) (n : nat) (h1 : (term9 x n) = (term10 x n)) : ((term14 x n) = (term15 x n)) = True.
Proof. exact (TRANS (@lem1362575 x n h1) (@lem1362579 x n)). Qed.
Lemma lem1362581 (x : nat) (n : nat) (h1 : (term9 x n) = (term10 x n)) : True = ((term14 x n) = (term15 x n)).
Proof. exact (SYM (@lem1362580 x n h1)). Qed.
Lemma lem1362582 (x : nat) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term14 x n) = (term15 x n).
Proof. exact (EQ_MP (@lem1362581 x n h1) (@lem0)). Qed.
Lemma lem1362583 (x : nat) (n : nat) : term17 x n.
Proof. exact (fun h0 : (term9 x n) = (term10 x n) => @lem1362582 x n h0). Qed.
Lemma lem1362588 (x : nat) : term21 x.
Proof. exact (fun n : nat => @lem1362583 x n). Qed.
Lemma lem1362589 (x : nat) : term23 x.
Proof. exact (conj (@lem1362531 x) (@lem1362588 x)). Qed.
Lemma lem1362590 (x : nat) : term28 x.
Proof. exact (@lem1362488 x (@lem1362589 x)). Qed.
Lemma lem1362595 : term59.
Proof. exact (fun x : nat => @lem1362590 x). Qed.
