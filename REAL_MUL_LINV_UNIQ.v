Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MUL_LINV_UNIQ_term_abbrevs.
Require Import ARITH_EQ_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import REAL_EQ_MUL_RCANCEL_spec.
Require Import REAL_MUL_RZERO_spec.
Require Import thm0_spec.
Require Import thm1340174_spec.
Require Import thm1340231_spec.
Require Import thm1822_spec.
Require Import thm1834_spec.
Require Import thm82_spec.
Lemma lem1587430 (x : real) : term0 x.
Proof. exact (@lem1340174 x). Qed.
Lemma lem1587431 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1587433 (y : real) : term2 y.
Proof. exact (@lem9784 (y = term3)). Qed.
Lemma lem1587434 (y : real) : (term2 y) = (term4 y).
Proof. exact (eq_refl (term2 y)). Qed.
Lemma lem1587435 (y : real) : term4 y.
Proof. exact (EQ_MP (@lem1587434 y) (@lem1587433 y)). Qed.
Lemma lem1587437 (y : real) (h1 : term5 y) : term5 y.
Proof. exact (h1). Qed.
Lemma lem1587438 : term6.
Proof. exact (proj2 (@lem522076)). Qed.
Lemma lem1587439 : term7.
Proof. exact (proj2 (@lem1587438)). Qed.
Lemma lem1587440 : term8.
Proof. exact (proj2 (@lem1587439)). Qed.
Lemma lem1587441 : term9.
Proof. exact (proj2 (@lem1587440)). Qed.
Lemma lem1587442 : term10.
Proof. exact (proj2 (@lem1587441)). Qed.
Lemma lem1587474 : term11.
Proof. exact (proj1 (@lem1587442)). Qed.
Lemma lem1587475 (n : nat) : term12 n.
Proof. exact (@lem1587474 n). Qed.
Lemma lem1587476 (n : nat) : (term12 n) = ((0 = (BIT1 n)) = False).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem1587491 : term13.
Proof. exact (proj1 (@lem522076)). Qed.
Lemma lem1587492 (m : nat) : term14 m.
Proof. exact (@lem1587491 m). Qed.
Lemma lem1587493 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1587494 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem1587493 m) (@lem1587492 m)). Qed.
Lemma lem1587495 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem1587494 m n). Qed.
Lemma lem1587496 (m : nat) (n : nat) : (term16 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1587498 (m : nat) : term17 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem1587499 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem1587500 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem1587499 m) (@lem1587498 m)). Qed.
Lemma lem1587501 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1587500 m n). Qed.
Lemma lem1587502 (m : nat) (n : nat) : (term19 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1587504 (x : real) : term20 x.
Proof. exact (@lem1356740 x). Qed.
Lemma lem1587505 (x : real) : (term20 x) = ((term21 x) = term3).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1587514 (y : real) (h1 : y = term3) : y = term3.
Proof. exact (h1). Qed.
Lemma lem1587515 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1587516 (x : real) (y : real) (h1 : y = term3) : (real_mul x y) = (term21 x).
Proof. exact (MK_COMB (@lem1587515 x) (@lem1587514 y h1)). Qed.
Lemma lem1587518 (x : real) : (term21 x) = term3.
Proof. exact (EQ_MP (@lem1587505 x) (@lem1587504 x)). Qed.
Lemma lem1587519 (x : real) (y : real) (h1 : y = term3) : (real_mul x y) = term3.
Proof. exact (TRANS (@lem1587516 x y h1) (@lem1587518 x)). Qed.
Lemma lem1587520 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1587521 (x : real) (y : real) (h1 : y = term3) : (term22 x y) = term23.
Proof. exact (MK_COMB (@lem1587520) (@lem1587519 x y h1)). Qed.
Lemma lem1587522 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1587523 (x : real) (y : real) (h1 : y = term3) : ((real_mul x y) = term24) = (term3 = term24).
Proof. exact (MK_COMB (@lem1587521 x y h1) (@lem1587522)). Qed.
Lemma lem1587525 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1587502 m n) (@lem1587501 m n)). Qed.
Lemma lem1587526 : (term3 = term24) = ((NUMERAL 0) = term25).
Proof. exact (@lem1587525 (NUMERAL 0) term25). Qed.
Lemma lem1587528 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1587496 m n) (@lem1587495 m n)). Qed.
Lemma lem1587529 : ((NUMERAL 0) = term25) = (0 = (BIT1 0)).
Proof. exact (@lem1587528 0 (BIT1 0)). Qed.
Lemma lem1587531 (n : nat) : (0 = (BIT1 n)) = False.
Proof. exact (EQ_MP (@lem1587476 n) (@lem1587475 n)). Qed.
Lemma lem1587532 : (0 = (BIT1 0)) = False.
Proof. exact (@lem1587531 0). Qed.
Lemma lem1587533 : ((NUMERAL 0) = term25) = False.
Proof. exact (TRANS (@lem1587529) (@lem1587532)). Qed.
Lemma lem1587534 : (term3 = term24) = False.
Proof. exact (TRANS (@lem1587526) (@lem1587533)). Qed.
Lemma lem1587535 (x : real) (y : real) (h1 : y = term3) : ((real_mul x y) = term24) = False.
Proof. exact (TRANS (@lem1587523 x y h1) (@lem1587534)). Qed.
Lemma lem1587536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1587537 (x : real) (y : real) (h1 : y = term3) : (term26 x y) = (imp False).
Proof. exact (MK_COMB (@lem1587536) (@lem1587535 x y h1)). Qed.
Lemma lem1587541 (y : real) (h1 : y = term3) : y = term3.
Proof. exact (h1). Qed.
Lemma lem1587542 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1587543 (y : real) (h1 : y = term3) : (real_inv y) = term27.
Proof. exact (MK_COMB (@lem1587542) (@lem1587541 y h1)). Qed.
Lemma lem1587544 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1587545 (y : real) (h1 : y = term3) : (term28 y) = term29.
Proof. exact (MK_COMB (@lem1587544) (@lem1587543 y h1)). Qed.
Lemma lem1587546 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1587547 (x : real) (y : real) (h1 : y = term3) : ((real_inv y) = x) = (term27 = x).
Proof. exact (MK_COMB (@lem1587545 y h1) (@lem1587546 x)). Qed.
Lemma lem1587550 (x : real) (y : real) (h1 : y = term3) : (term30 y x) = (term31 x).
Proof. exact (MK_COMB (@lem1587537 x y h1) (@lem1587547 x y h1)). Qed.
Lemma lem1587552 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1587553 (x : real) : (term31 x) = True.
Proof. exact (@lem1587552 (term27 = x)). Qed.
Lemma lem1587554 (x : real) (y : real) (h1 : y = term3) : (term30 y x) = True.
Proof. exact (TRANS (@lem1587550 x y h1) (@lem1587553 x)). Qed.
Lemma lem1587555 (x : real) (y : real) (h1 : y = term3) : True = (term30 y x).
Proof. exact (SYM (@lem1587554 x y h1)). Qed.
Lemma lem1587556 (x : real) (y : real) (h1 : y = term3) : term30 y x.
Proof. exact (EQ_MP (@lem1587555 x y h1) (@lem0)). Qed.
Lemma lem1587650 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1587431 x) (@lem1587430 x)). Qed.
Lemma lem1587651 (y : real) : term1 y.
Proof. exact (@lem1587650 y). Qed.
Lemma lem1587652 (y : real) (h1 : term5 y) : (term32 y) = term24.
Proof. exact (@lem1587651 y (@lem1587437 y h1)). Qed.
Lemma lem1587653 (y : real) (h1 : term5 y) : term24 = (term32 y).
Proof. exact (SYM (@lem1587652 y h1)). Qed.
Lemma lem1587654 (y : real) (x : real) : (term33 y x) = (term33 y x).
Proof. exact (eq_refl (term33 y x)). Qed.
Lemma lem1587655 (x : real) (y : real) (h1 : term5 y) : (term34 y x) = (term35 x y).
Proof. exact (MK_COMB (@lem1587654 y x) (@lem1587653 y h1)). Qed.
Lemma lem1587656 (y : real) (x : real) : (term35 x y) = (term36 y x).
Proof. exact (eq_refl (term35 x y)). Qed.
Lemma lem1587657 (y : real) (x : real) : (term37 y x) = (term37 y x).
Proof. exact (eq_refl (term37 y x)). Qed.
Lemma lem1587658 (y : real) (x : real) : ((term34 y x) = (term35 x y)) = ((term34 y x) = (term36 y x)).
Proof. exact (MK_COMB (@lem1587657 y x) (@lem1587656 y x)). Qed.
Lemma lem1587659 (y : real) (x : real) : (term34 y x) = (term30 y x).
Proof. exact (eq_refl (term34 y x)). Qed.
Lemma lem1587660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1587661 (y : real) (x : real) : (term37 y x) = (term38 y x).
Proof. exact (MK_COMB (@lem1587660) (@lem1587659 y x)). Qed.
Lemma lem1587662 (y : real) (x : real) : (term36 y x) = (term36 y x).
Proof. exact (eq_refl (term36 y x)). Qed.
Lemma lem1587663 (y : real) (x : real) : ((term34 y x) = (term36 y x)) = ((term30 y x) = (term36 y x)).
Proof. exact (MK_COMB (@lem1587661 y x) (@lem1587662 y x)). Qed.
Lemma lem1587664 (y : real) (x : real) : ((term34 y x) = (term35 x y)) = ((term30 y x) = (term36 y x)).
Proof. exact (TRANS (@lem1587658 y x) (@lem1587663 y x)). Qed.
Lemma lem1587665 (x : real) (y : real) (h1 : term5 y) : (term30 y x) = (term36 y x).
Proof. exact (EQ_MP (@lem1587664 y x) (@lem1587655 x y h1)). Qed.
Lemma lem1587666 (x : real) (y : real) (h1 : term5 y) : (term36 y x) = (term30 y x).
Proof. exact (SYM (@lem1587665 x y h1)). Qed.
Lemma lem1587667 (x : real) : term39 x.
Proof. exact (@lem1587429 x). Qed.
Lemma lem1587668 (x : real) : (term39 x) = (term40 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1587669 (x : real) : term40 x.
Proof. exact (EQ_MP (@lem1587668 x) (@lem1587667 x)). Qed.
Lemma lem1587670 (x : real) (y : real) : term41 x y.
Proof. exact (@lem1587669 x y). Qed.
Lemma lem1587671 (x : real) (y : real) : (term41 x y) = (term42 x y).
Proof. exact (eq_refl (term41 x y)). Qed.
Lemma lem1587672 (x : real) (y : real) : term42 x y.
Proof. exact (EQ_MP (@lem1587671 x y) (@lem1587670 x y)). Qed.
Lemma lem1587673 (x : real) (y : real) (z : real) : term43 x y z.
Proof. exact (@lem1587672 x y z). Qed.
Lemma lem1587674 (x : real) (y : real) (z : real) : (term43 x y z) = (((real_mul x z) = (real_mul y z)) = (term44 x y z)).
Proof. exact (eq_refl (term43 x y z)). Qed.
Lemma lem1587676 (y : real) : term45 y.
Proof. exact (@lem82 (y = term3)). Qed.
Lemma lem1587694 (x : real) (y : real) (z : real) : ((real_mul x z) = (real_mul y z)) = (term44 x y z).
Proof. exact (EQ_MP (@lem1587674 x y z) (@lem1587673 x y z)). Qed.
Lemma lem1587695 (x : real) (y : real) : ((real_mul x y) = (term32 y)) = (term46 x y).
Proof. exact (@lem1587694 x (real_inv y) y). Qed.
Lemma lem1587701 (y : real) (h1 : term5 y) : (y = term3) = False.
Proof. exact (@lem1587676 y (@lem1587437 y h1)). Qed.
Lemma lem1587702 (x : real) (y : real) : (term47 x y) = (term47 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1587703 (x : real) (y : real) (h1 : term5 y) : (term46 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1587702 x y) (@lem1587701 y h1)). Qed.
Lemma lem1587705 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1587706 (x : real) (y : real) : (term48 x y) = (x = (real_inv y)).
Proof. exact (@lem1587705 (x = (real_inv y))). Qed.
Lemma lem1587709 (x : real) (y : real) (h1 : term5 y) : (term46 x y) = (x = (real_inv y)).
Proof. exact (TRANS (@lem1587703 x y h1) (@lem1587706 x y)). Qed.
Lemma lem1587710 (x : real) (y : real) (h1 : term5 y) : ((real_mul x y) = (term32 y)) = (x = (real_inv y)).
Proof. exact (TRANS (@lem1587695 x y) (@lem1587709 x y h1)). Qed.
Lemma lem1587711 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1587712 (x : real) (y : real) (h1 : term5 y) : (term49 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem1587711) (@lem1587710 x y h1)). Qed.
Lemma lem1587715 (y : real) (x : real) : ((real_inv y) = x) = ((real_inv y) = x).
Proof. exact (eq_refl ((real_inv y) = x)). Qed.
Lemma lem1587716 (x : real) (y : real) (h1 : term5 y) : (term36 y x) = (term51 y x).
Proof. exact (MK_COMB (@lem1587712 x y h1) (@lem1587715 y x)). Qed.
Lemma lem1587721 (x : real) (y : real) (h1 : term5 y) : (term51 y x) = (term36 y x).
Proof. exact (SYM (@lem1587716 x y h1)). Qed.
Lemma lem1587722 (x : real) (y : real) (h1 : x = (real_inv y)) : x = (real_inv y).
Proof. exact (h1). Qed.
Lemma lem1587723 (x : real) (y : real) (h1 : x = (real_inv y)) : (real_inv y) = x.
Proof. exact (SYM (@lem1587722 x y h1)). Qed.
Lemma lem1587724 (y : real) (x : real) : term51 y x.
Proof. exact (fun h0 : x = (real_inv y) => @lem1587723 x y h0). Qed.
Lemma lem1587725 (x : real) (y : real) (h1 : term5 y) : term36 y x.
Proof. exact (EQ_MP (@lem1587721 x y h1) (@lem1587724 y x)). Qed.
Lemma lem1587727 (x : real) (y : real) (h1 : term5 y) : term30 y x.
Proof. exact (EQ_MP (@lem1587666 x y h1) (@lem1587725 x y h1)). Qed.
Lemma lem1587728 (y : real) (x : real) : term30 y x.
Proof. exact (or_elim (@lem1587435 y) (fun h0 : y = term3 => @lem1587556 x y h0) (fun h0 : term5 y => @lem1587727 x y h0)). Qed.
Lemma lem1587733 (x : real) : term52 x.
Proof. exact (fun y : real => @lem1587728 y x). Qed.
Lemma lem1587738 : term53.
Proof. exact (fun x : real => @lem1587733 x). Qed.
