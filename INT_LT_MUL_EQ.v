Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_MUL_EQ_term_abbrevs.
Require Import REAL_LT_MUL_EQ_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304464 : term0.
Proof. exact (proj2 (@lem1610545)). Qed.
Lemma lem2304465 (x : int) : term1 x.
Proof. exact (@lem2304464 (real_of_int x)). Qed.
Lemma lem2304466 (x : int) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem2304467 (x : int) : term2 x.
Proof. exact (EQ_MP (@lem2304466 x) (@lem2304465 x)). Qed.
Lemma lem2304468 (x : int) (y : int) : term3 x y.
Proof. exact (@lem2304467 x (real_of_int y)). Qed.
Lemma lem2304469 (y : int) (x : int) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem2304470 (y : int) (x : int) : term4 y x.
Proof. exact (EQ_MP (@lem2304469 y x) (@lem2304468 x y)). Qed.
Lemma lem2304472 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304473 : term6 = term7.
Proof. exact (@lem2304472 (NUMERAL 0)). Qed.
Lemma lem2304474 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304475 : term8 = term9.
Proof. exact (MK_COMB (@lem2304474) (@lem2304473)). Qed.
Lemma lem2304476 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2304477 (y : int) : (term10 y) = (term11 y).
Proof. exact (MK_COMB (@lem2304475) (@lem2304476 y)). Qed.
Lemma lem2304479 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304480 (y : int) : (term11 y) = (term13 y).
Proof. exact (@lem2304479 term14 y). Qed.
Lemma lem2304481 (y : int) : (term10 y) = (term13 y).
Proof. exact (TRANS (@lem2304477 y) (@lem2304480 y)). Qed.
Lemma lem2304482 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2304483 (y : int) : (term15 y) = (term16 y).
Proof. exact (MK_COMB (@lem2304482) (@lem2304481 y)). Qed.
Lemma lem2304485 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304486 : term6 = term7.
Proof. exact (@lem2304485 (NUMERAL 0)). Qed.
Lemma lem2304487 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304488 : term8 = term9.
Proof. exact (MK_COMB (@lem2304487) (@lem2304486)). Qed.
Lemma lem2304490 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304491 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem2304488) (@lem2304490 x y)). Qed.
Lemma lem2304493 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304494 (x : int) (y : int) : (term20 x y) = (term21 x y).
Proof. exact (@lem2304493 term14 (int_mul x y)). Qed.
Lemma lem2304495 (x : int) (y : int) : (term19 x y) = (term21 x y).
Proof. exact (TRANS (@lem2304491 x y) (@lem2304494 x y)). Qed.
Lemma lem2304496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304497 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem2304496) (@lem2304495 x y)). Qed.
Lemma lem2304499 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304500 : term6 = term7.
Proof. exact (@lem2304499 (NUMERAL 0)). Qed.
Lemma lem2304501 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304502 : term8 = term9.
Proof. exact (MK_COMB (@lem2304501) (@lem2304500)). Qed.
Lemma lem2304503 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2304504 (x : int) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem2304502) (@lem2304503 x)). Qed.
Lemma lem2304506 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304507 (x : int) : (term11 x) = (term13 x).
Proof. exact (@lem2304506 term14 x). Qed.
Lemma lem2304508 (x : int) : (term10 x) = (term13 x).
Proof. exact (TRANS (@lem2304504 x) (@lem2304507 x)). Qed.
Lemma lem2304509 (y : int) (x : int) : ((term19 x y) = (term10 x)) = ((term21 x y) = (term13 x)).
Proof. exact (MK_COMB (@lem2304497 x y) (@lem2304508 x)). Qed.
Lemma lem2304510 (y : int) (x : int) : (term4 y x) = (term24 y x).
Proof. exact (MK_COMB (@lem2304483 y) (@lem2304509 y x)). Qed.
Lemma lem2304511 (y : int) (x : int) : term24 y x.
Proof. exact (EQ_MP (@lem2304510 y x) (@lem2304470 y x)). Qed.
Lemma lem2304512 (x : int) : term25 x.
Proof. exact (fun y : int => @lem2304511 y x). Qed.
Lemma lem2304513 : term26.
Proof. exact (fun x : int => @lem2304512 x). Qed.
Lemma lem2304514 : term27.
Proof. exact (proj1 (@lem1610545)). Qed.
Lemma lem2304515 (x : int) : term28 x.
Proof. exact (@lem2304514 (real_of_int x)). Qed.
Lemma lem2304516 (x : int) : (term28 x) = (term29 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem2304517 (x : int) : term29 x.
Proof. exact (EQ_MP (@lem2304516 x) (@lem2304515 x)). Qed.
Lemma lem2304518 (x : int) (y : int) : term30 x y.
Proof. exact (@lem2304517 x (real_of_int y)). Qed.
Lemma lem2304519 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem2304520 (x : int) (y : int) : term31 x y.
Proof. exact (EQ_MP (@lem2304519 x y) (@lem2304518 x y)). Qed.
Lemma lem2304522 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304523 : term6 = term7.
Proof. exact (@lem2304522 (NUMERAL 0)). Qed.
Lemma lem2304524 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304525 : term8 = term9.
Proof. exact (MK_COMB (@lem2304524) (@lem2304523)). Qed.
Lemma lem2304526 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2304527 (x : int) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem2304525) (@lem2304526 x)). Qed.
Lemma lem2304529 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304530 (x : int) : (term11 x) = (term13 x).
Proof. exact (@lem2304529 term14 x). Qed.
Lemma lem2304531 (x : int) : (term10 x) = (term13 x).
Proof. exact (TRANS (@lem2304527 x) (@lem2304530 x)). Qed.
Lemma lem2304532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2304533 (x : int) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem2304532) (@lem2304531 x)). Qed.
Lemma lem2304535 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304536 : term6 = term7.
Proof. exact (@lem2304535 (NUMERAL 0)). Qed.
Lemma lem2304537 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304538 : term8 = term9.
Proof. exact (MK_COMB (@lem2304537) (@lem2304536)). Qed.
Lemma lem2304540 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304541 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem2304538) (@lem2304540 x y)). Qed.
Lemma lem2304543 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304544 (x : int) (y : int) : (term20 x y) = (term21 x y).
Proof. exact (@lem2304543 term14 (int_mul x y)). Qed.
Lemma lem2304545 (x : int) (y : int) : (term19 x y) = (term21 x y).
Proof. exact (TRANS (@lem2304541 x y) (@lem2304544 x y)). Qed.
Lemma lem2304546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304547 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem2304546) (@lem2304545 x y)). Qed.
Lemma lem2304549 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304550 : term6 = term7.
Proof. exact (@lem2304549 (NUMERAL 0)). Qed.
Lemma lem2304551 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304552 : term8 = term9.
Proof. exact (MK_COMB (@lem2304551) (@lem2304550)). Qed.
Lemma lem2304553 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2304554 (y : int) : (term10 y) = (term11 y).
Proof. exact (MK_COMB (@lem2304552) (@lem2304553 y)). Qed.
Lemma lem2304556 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304557 (y : int) : (term11 y) = (term13 y).
Proof. exact (@lem2304556 term14 y). Qed.
Lemma lem2304558 (y : int) : (term10 y) = (term13 y).
Proof. exact (TRANS (@lem2304554 y) (@lem2304557 y)). Qed.
Lemma lem2304559 (x : int) (y : int) : ((term19 x y) = (term10 y)) = ((term21 x y) = (term13 y)).
Proof. exact (MK_COMB (@lem2304547 x y) (@lem2304558 y)). Qed.
Lemma lem2304560 (x : int) (y : int) : (term31 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem2304533 x) (@lem2304559 x y)). Qed.
Lemma lem2304561 (x : int) (y : int) : term32 x y.
Proof. exact (EQ_MP (@lem2304560 x y) (@lem2304520 x y)). Qed.
Lemma lem2304562 (x : int) : term33 x.
Proof. exact (fun y : int => @lem2304561 x y). Qed.
Lemma lem2304563 : term34.
Proof. exact (fun x : int => @lem2304562 x). Qed.
Lemma lem2304564 : term35.
Proof. exact (conj (@lem2304563) (@lem2304513)). Qed.
