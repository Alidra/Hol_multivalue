Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MUL_POS_LT_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_LT_MUL_spec.
Require Import REAL_LT_NEGTOTAL_spec.
Require Import REAL_LT_REFL_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_MUL_RZERO_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483464_spec.
Require Import thm1483472_spec.
Require Import thm1483474_spec.
Require Import thm1483478_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1610546 (x : real) : term0 x.
Proof. exact (@lem1487565 x). Qed.
Lemma lem1610547 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1610548 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1610547 x) (@lem1610546 x)). Qed.
Lemma lem1610549 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1610548 x y). Qed.
Lemma lem1610550 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1610552 (y : real) : term4 y.
Proof. exact (@lem1499257 y). Qed.
Lemma lem1610553 (y : real) : (term4 y) = (term5 y).
Proof. exact (eq_refl (term4 y)). Qed.
Lemma lem1610554 (y : real) : term5 y.
Proof. exact (EQ_MP (@lem1610553 y) (@lem1610552 y)). Qed.
Lemma lem1610555 (y : real) (h1 : y = term6) : y = term6.
Proof. exact (h1). Qed.
Lemma lem1610556 (y : real) (h1 : term7 y) : term7 y.
Proof. exact (h1). Qed.
Lemma lem1610557 (x : real) : term4 x.
Proof. exact (@lem1499257 x). Qed.
Lemma lem1610558 (x : real) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1610559 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem1610558 x) (@lem1610557 x)). Qed.
Lemma lem1610560 (x : real) (h1 : x = term6) : x = term6.
Proof. exact (h1). Qed.
Lemma lem1610561 (x : real) (h1 : term7 x) : term7 x.
Proof. exact (h1). Qed.
Lemma lem1610562 (x : real) (h1 : term8 x) : term8 x.
Proof. exact (h1). Qed.
Lemma lem1610563 (x : real) (h1 : term9 x) : term9 x.
Proof. exact (h1). Qed.
Lemma lem1610564 (y : real) (h1 : term8 y) : term8 y.
Proof. exact (h1). Qed.
Lemma lem1610566 (y : real) (h1 : term8 y) : term8 y.
Proof. exact (h1). Qed.
Lemma lem1610567 (y : real) (h1 : term9 y) : term9 y.
Proof. exact (h1). Qed.
Lemma lem1610568 (y : real) (h1 : term8 y) : term8 y.
Proof. exact (h1). Qed.
Lemma lem1610569 (y : real) (h1 : term9 y) : term9 y.
Proof. exact (h1). Qed.
Lemma lem1610570 (x : real) : term10 x.
Proof. exact (@lem1379422 x). Qed.
Lemma lem1610571 (x : real) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1610572 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1610571 x) (@lem1610570 x)). Qed.
Lemma lem1610573 (x : real) : term12 x.
Proof. exact (@lem82 (real_lt x x)). Qed.
Lemma lem1610578 (x : real) : term13 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1610579 (x : real) : (term13 x) = ((term14 x) = term6).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1610586 (x : real) (h1 : x = term6) : x = term6.
Proof. exact (h1). Qed.
Lemma lem1610587 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1610588 (x : real) (h1 : x = term6) : (real_mul x) = term15.
Proof. exact (MK_COMB (@lem1610587) (@lem1610586 x h1)). Qed.
Lemma lem1610590 (y : real) (h1 : y = term6) : y = term6.
Proof. exact (h1). Qed.
Lemma lem1610591 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (real_mul x y) = term16.
Proof. exact (MK_COMB (@lem1610588 x h1) (@lem1610590 y h2)). Qed.
Lemma lem1610593 (x : real) : (term14 x) = term6.
Proof. exact (EQ_MP (@lem1610579 x) (@lem1610578 x)). Qed.
Lemma lem1610594 : term16 = term6.
Proof. exact (@lem1610593 term6). Qed.
Lemma lem1610595 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (real_mul x y) = term6.
Proof. exact (TRANS (@lem1610591 x y h1 h2) (@lem1610594)). Qed.
Lemma lem1610596 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1610597 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (term18 x y) = term19.
Proof. exact (MK_COMB (@lem1610596) (@lem1610595 x y h1 h2)). Qed.
Lemma lem1610599 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1610573 x (@lem1610572 x)). Qed.
Lemma lem1610600 : term19 = False.
Proof. exact (@lem1610599 term6). Qed.
Lemma lem1610601 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (term18 x y) = False.
Proof. exact (TRANS (@lem1610597 x y h1 h2) (@lem1610600)). Qed.
Lemma lem1610602 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1610603 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (term20 x y) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1610602) (@lem1610601 x y h1 h2)). Qed.
Lemma lem1610611 (x : real) (h1 : x = term6) : x = term6.
Proof. exact (h1). Qed.
Lemma lem1610612 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1610613 (x : real) (h1 : x = term6) : (term8 x) = term19.
Proof. exact (MK_COMB (@lem1610612) (@lem1610611 x h1)). Qed.
Lemma lem1610615 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1610573 x (@lem1610572 x)). Qed.
Lemma lem1610616 : term19 = False.
Proof. exact (@lem1610615 term6). Qed.
Lemma lem1610617 (x : real) (h1 : x = term6) : (term8 x) = False.
Proof. exact (TRANS (@lem1610613 x h1) (@lem1610616)). Qed.
Lemma lem1610618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1610619 (x : real) (h1 : x = term6) : (term21 x) = (and False).
Proof. exact (MK_COMB (@lem1610618) (@lem1610617 x h1)). Qed.
Lemma lem1610623 (y : real) (h1 : y = term6) : y = term6.
Proof. exact (h1). Qed.
Lemma lem1610624 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1610625 (y : real) (h1 : y = term6) : (term8 y) = term19.
Proof. exact (MK_COMB (@lem1610624) (@lem1610623 y h1)). Qed.
Lemma lem1610627 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1610573 x (@lem1610572 x)). Qed.
Lemma lem1610628 : term19 = False.
Proof. exact (@lem1610627 term6). Qed.
Lemma lem1610629 (y : real) (h1 : y = term6) : (term8 y) = False.
Proof. exact (TRANS (@lem1610625 y h1) (@lem1610628)). Qed.
Lemma lem1610630 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (term22 x y) = (False /\ False).
Proof. exact (MK_COMB (@lem1610619 x h1) (@lem1610629 y h2)). Qed.
Lemma lem1610632 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1610633 : (False /\ False) = False.
Proof. exact (@lem1610632 False). Qed.
Lemma lem1610634 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (term22 x y) = False.
Proof. exact (TRANS (@lem1610630 x y h1 h2) (@lem1610633)). Qed.
Lemma lem1610635 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1610636 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (term23 x y) = (or False).
Proof. exact (MK_COMB (@lem1610635) (@lem1610634 x y h1 h2)). Qed.
Lemma lem1610642 (x : real) (h1 : x = term6) : x = term6.
Proof. exact (h1). Qed.
Lemma lem1610643 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1610644 (x : real) (h1 : x = term6) : (real_lt x) = term17.
Proof. exact (MK_COMB (@lem1610643) (@lem1610642 x h1)). Qed.
Lemma lem1610645 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1610646 (x : real) (h1 : x = term6) : (term24 x) = term19.
Proof. exact (MK_COMB (@lem1610644 x h1) (@lem1610645)). Qed.
Lemma lem1610648 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1610573 x (@lem1610572 x)). Qed.
Lemma lem1610649 : term19 = False.
Proof. exact (@lem1610648 term6). Qed.
Lemma lem1610650 (x : real) (h1 : x = term6) : (term24 x) = False.
Proof. exact (TRANS (@lem1610646 x h1) (@lem1610649)). Qed.
Lemma lem1610651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1610652 (x : real) (h1 : x = term6) : (term25 x) = (and False).
Proof. exact (MK_COMB (@lem1610651) (@lem1610650 x h1)). Qed.
Lemma lem1610656 (y : real) (h1 : y = term6) : y = term6.
Proof. exact (h1). Qed.
Lemma lem1610657 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1610658 (y : real) (h1 : y = term6) : (real_lt y) = term17.
Proof. exact (MK_COMB (@lem1610657) (@lem1610656 y h1)). Qed.
Lemma lem1610659 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1610660 (y : real) (h1 : y = term6) : (term24 y) = term19.
Proof. exact (MK_COMB (@lem1610658 y h1) (@lem1610659)). Qed.
Lemma lem1610662 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1610573 x (@lem1610572 x)). Qed.
Lemma lem1610663 : term19 = False.
Proof. exact (@lem1610662 term6). Qed.
Lemma lem1610664 (y : real) (h1 : y = term6) : (term24 y) = False.
Proof. exact (TRANS (@lem1610660 y h1) (@lem1610663)). Qed.
Lemma lem1610665 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (term26 x y) = (False /\ False).
Proof. exact (MK_COMB (@lem1610652 x h1) (@lem1610664 y h2)). Qed.
Lemma lem1610667 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1610668 : (False /\ False) = False.
Proof. exact (@lem1610667 False). Qed.
Lemma lem1610669 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (term26 x y) = False.
Proof. exact (TRANS (@lem1610665 x y h1 h2) (@lem1610668)). Qed.
Lemma lem1610670 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (term27 x y) = (False \/ False).
Proof. exact (MK_COMB (@lem1610636 x y h1 h2) (@lem1610669 x y h1 h2)). Qed.
Lemma lem1610672 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1610673 : (False \/ False) = False.
Proof. exact (@lem1610672 False). Qed.
Lemma lem1610674 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (term27 x y) = False.
Proof. exact (TRANS (@lem1610670 x y h1 h2) (@lem1610673)). Qed.
Lemma lem1610675 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : ((term18 x y) = (term27 x y)) = (False = False).
Proof. exact (MK_COMB (@lem1610603 x y h1 h2) (@lem1610674 x y h1 h2)). Qed.
Lemma lem1610677 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1610678 : (False = False) = (~ False).
Proof. exact (@lem1610677 False). Qed.
Lemma lem1610680 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1610681 : (False = False) = True.
Proof. exact (TRANS (@lem1610678) (@lem1610680)). Qed.
Lemma lem1610682 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : ((term18 x y) = (term27 x y)) = True.
Proof. exact (TRANS (@lem1610675 x y h1 h2) (@lem1610681)). Qed.
Lemma lem1610683 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : True = ((term18 x y) = (term27 x y)).
Proof. exact (SYM (@lem1610682 x y h1 h2)). Qed.
Lemma lem1610684 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1610683 x y h1 h2) (@lem0)). Qed.
Lemma lem1610685 (x : real) : term10 x.
Proof. exact (@lem1379422 x). Qed.
Lemma lem1610686 (x : real) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1610687 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1610686 x) (@lem1610685 x)). Qed.
Lemma lem1610688 (x : real) : term12 x.
Proof. exact (@lem82 (real_lt x x)). Qed.
Lemma lem1610693 (x : real) : term13 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1610694 (x : real) : (term13 x) = ((term14 x) = term6).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1610696 (y : real) : (term8 y) = ((term8 y) = True).
Proof. exact (@lem7 (term8 y)). Qed.
Lemma lem1610703 (x : real) (h1 : x = term6) : x = term6.
Proof. exact (h1). Qed.
Lemma lem1610704 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1610705 (x : real) (h1 : x = term6) : (real_mul x) = term15.
Proof. exact (MK_COMB (@lem1610704) (@lem1610703 x h1)). Qed.
Lemma lem1610706 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1610707 (y : real) (x : real) (h1 : x = term6) : (real_mul x y) = (term14 y).
Proof. exact (MK_COMB (@lem1610705 x h1) (@lem1610706 y)). Qed.
Lemma lem1610709 (x : real) : (term14 x) = term6.
Proof. exact (EQ_MP (@lem1610694 x) (@lem1610693 x)). Qed.
Lemma lem1610710 (y : real) : (term14 y) = term6.
Proof. exact (@lem1610709 y). Qed.
Lemma lem1610711 (y : real) (x : real) (h1 : x = term6) : (real_mul x y) = term6.
Proof. exact (TRANS (@lem1610707 y x h1) (@lem1610710 y)). Qed.
Lemma lem1610712 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1610713 (y : real) (x : real) (h1 : x = term6) : (term18 x y) = term19.
Proof. exact (MK_COMB (@lem1610712) (@lem1610711 y x h1)). Qed.
Lemma lem1610715 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1610688 x (@lem1610687 x)). Qed.
Lemma lem1610716 : term19 = False.
Proof. exact (@lem1610715 term6). Qed.
Lemma lem1610717 (y : real) (x : real) (h1 : x = term6) : (term18 x y) = False.
Proof. exact (TRANS (@lem1610713 y x h1) (@lem1610716)). Qed.
Lemma lem1610718 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1610719 (y : real) (x : real) (h1 : x = term6) : (term20 x y) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1610718) (@lem1610717 y x h1)). Qed.
Lemma lem1610727 (x : real) (h1 : x = term6) : x = term6.
Proof. exact (h1). Qed.
Lemma lem1610728 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1610729 (x : real) (h1 : x = term6) : (term8 x) = term19.
Proof. exact (MK_COMB (@lem1610728) (@lem1610727 x h1)). Qed.
Lemma lem1610731 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1610688 x (@lem1610687 x)). Qed.
Lemma lem1610732 : term19 = False.
Proof. exact (@lem1610731 term6). Qed.
Lemma lem1610733 (x : real) (h1 : x = term6) : (term8 x) = False.
Proof. exact (TRANS (@lem1610729 x h1) (@lem1610732)). Qed.
Lemma lem1610734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1610735 (x : real) (h1 : x = term6) : (term21 x) = (and False).
Proof. exact (MK_COMB (@lem1610734) (@lem1610733 x h1)). Qed.
Lemma lem1610737 (y : real) (h1 : term8 y) : (term8 y) = True.
Proof. exact (EQ_MP (@lem1610696 y) (@lem1610564 y h1)). Qed.
Lemma lem1610738 (x : real) (y : real) (h1 : x = term6) (h2 : term8 y) : (term22 x y) = (False /\ True).
Proof. exact (MK_COMB (@lem1610735 x h1) (@lem1610737 y h2)). Qed.
Lemma lem1610740 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1610741 : (False /\ True) = False.
Proof. exact (@lem1610740 True). Qed.
Lemma lem1610742 (x : real) (y : real) (h1 : x = term6) (h2 : term8 y) : (term22 x y) = False.
Proof. exact (TRANS (@lem1610738 x y h1 h2) (@lem1610741)). Qed.
Lemma lem1610743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1610744 (x : real) (y : real) (h1 : x = term6) (h2 : term8 y) : (term23 x y) = (or False).
Proof. exact (MK_COMB (@lem1610743) (@lem1610742 x y h1 h2)). Qed.
Lemma lem1610750 (x : real) (h1 : x = term6) : x = term6.
Proof. exact (h1). Qed.
Lemma lem1610751 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1610752 (x : real) (h1 : x = term6) : (real_lt x) = term17.
Proof. exact (MK_COMB (@lem1610751) (@lem1610750 x h1)). Qed.
Lemma lem1610753 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1610754 (x : real) (h1 : x = term6) : (term24 x) = term19.
Proof. exact (MK_COMB (@lem1610752 x h1) (@lem1610753)). Qed.
Lemma lem1610756 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1610688 x (@lem1610687 x)). Qed.
Lemma lem1610757 : term19 = False.
Proof. exact (@lem1610756 term6). Qed.
Lemma lem1610758 (x : real) (h1 : x = term6) : (term24 x) = False.
Proof. exact (TRANS (@lem1610754 x h1) (@lem1610757)). Qed.
Lemma lem1610759 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1610760 (x : real) (h1 : x = term6) : (term25 x) = (and False).
Proof. exact (MK_COMB (@lem1610759) (@lem1610758 x h1)). Qed.
Lemma lem1610763 (y : real) : (term24 y) = (term24 y).
Proof. exact (eq_refl (term24 y)). Qed.
Lemma lem1610764 (y : real) (x : real) (h1 : x = term6) : (term26 x y) = (term28 y).
Proof. exact (MK_COMB (@lem1610760 x h1) (@lem1610763 y)). Qed.
Lemma lem1610766 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1610767 (y : real) : (term28 y) = False.
Proof. exact (@lem1610766 (term24 y)). Qed.
Lemma lem1610768 (y : real) (x : real) (h1 : x = term6) : (term26 x y) = False.
Proof. exact (TRANS (@lem1610764 y x h1) (@lem1610767 y)). Qed.
Lemma lem1610769 (x : real) (y : real) (h1 : x = term6) (h2 : term8 y) : (term27 x y) = (False \/ False).
Proof. exact (MK_COMB (@lem1610744 x y h1 h2) (@lem1610768 y x h1)). Qed.
Lemma lem1610771 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1610772 : (False \/ False) = False.
Proof. exact (@lem1610771 False). Qed.
Lemma lem1610773 (x : real) (y : real) (h1 : x = term6) (h2 : term8 y) : (term27 x y) = False.
Proof. exact (TRANS (@lem1610769 x y h1 h2) (@lem1610772)). Qed.
Lemma lem1610774 (x : real) (y : real) (h1 : x = term6) (h2 : term8 y) : ((term18 x y) = (term27 x y)) = (False = False).
Proof. exact (MK_COMB (@lem1610719 y x h1) (@lem1610773 x y h1 h2)). Qed.
Lemma lem1610776 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1610777 : (False = False) = (~ False).
Proof. exact (@lem1610776 False). Qed.
Lemma lem1610779 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1610780 : (False = False) = True.
Proof. exact (TRANS (@lem1610777) (@lem1610779)). Qed.
Lemma lem1610781 (x : real) (y : real) (h1 : x = term6) (h2 : term8 y) : ((term18 x y) = (term27 x y)) = True.
Proof. exact (TRANS (@lem1610774 x y h1 h2) (@lem1610780)). Qed.
Lemma lem1610782 (x : real) (y : real) (h1 : x = term6) (h2 : term8 y) : True = ((term18 x y) = (term27 x y)).
Proof. exact (SYM (@lem1610781 x y h1 h2)). Qed.
Lemma lem1610783 (x : real) (y : real) (h1 : x = term6) (h2 : term8 y) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1610782 x y h1 h2) (@lem0)). Qed.
Lemma lem1610784 (x : real) : term10 x.
Proof. exact (@lem1379422 x). Qed.
Lemma lem1610785 (x : real) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1610786 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1610785 x) (@lem1610784 x)). Qed.
Lemma lem1610787 (x : real) : term12 x.
Proof. exact (@lem82 (real_lt x x)). Qed.
Lemma lem1610792 (x : real) : term13 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1610793 (x : real) : (term13 x) = ((term14 x) = term6).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1610802 (x : real) (h1 : x = term6) : x = term6.
Proof. exact (h1). Qed.
Lemma lem1610803 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1610804 (x : real) (h1 : x = term6) : (real_mul x) = term15.
Proof. exact (MK_COMB (@lem1610803) (@lem1610802 x h1)). Qed.
Lemma lem1610805 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1610806 (y : real) (x : real) (h1 : x = term6) : (real_mul x y) = (term14 y).
Proof. exact (MK_COMB (@lem1610804 x h1) (@lem1610805 y)). Qed.
Lemma lem1610808 (x : real) : (term14 x) = term6.
Proof. exact (EQ_MP (@lem1610793 x) (@lem1610792 x)). Qed.
Lemma lem1610809 (y : real) : (term14 y) = term6.
Proof. exact (@lem1610808 y). Qed.
Lemma lem1610810 (y : real) (x : real) (h1 : x = term6) : (real_mul x y) = term6.
Proof. exact (TRANS (@lem1610806 y x h1) (@lem1610809 y)). Qed.
Lemma lem1610811 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1610812 (y : real) (x : real) (h1 : x = term6) : (term18 x y) = term19.
Proof. exact (MK_COMB (@lem1610811) (@lem1610810 y x h1)). Qed.
Lemma lem1610814 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1610787 x (@lem1610786 x)). Qed.
Lemma lem1610815 : term19 = False.
Proof. exact (@lem1610814 term6). Qed.
Lemma lem1610816 (y : real) (x : real) (h1 : x = term6) : (term18 x y) = False.
Proof. exact (TRANS (@lem1610812 y x h1) (@lem1610815)). Qed.
Lemma lem1610817 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1610818 (y : real) (x : real) (h1 : x = term6) : (term20 x y) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1610817) (@lem1610816 y x h1)). Qed.
Lemma lem1610826 (x : real) (h1 : x = term6) : x = term6.
Proof. exact (h1). Qed.
Lemma lem1610827 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1610828 (x : real) (h1 : x = term6) : (term8 x) = term19.
Proof. exact (MK_COMB (@lem1610827) (@lem1610826 x h1)). Qed.
Lemma lem1610830 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1610787 x (@lem1610786 x)). Qed.
Lemma lem1610831 : term19 = False.
Proof. exact (@lem1610830 term6). Qed.
Lemma lem1610832 (x : real) (h1 : x = term6) : (term8 x) = False.
Proof. exact (TRANS (@lem1610828 x h1) (@lem1610831)). Qed.
Lemma lem1610833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1610834 (x : real) (h1 : x = term6) : (term21 x) = (and False).
Proof. exact (MK_COMB (@lem1610833) (@lem1610832 x h1)). Qed.
Lemma lem1610837 (y : real) : (term8 y) = (term8 y).
Proof. exact (eq_refl (term8 y)). Qed.
Lemma lem1610838 (y : real) (x : real) (h1 : x = term6) : (term22 x y) = (term29 y).
Proof. exact (MK_COMB (@lem1610834 x h1) (@lem1610837 y)). Qed.
Lemma lem1610840 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1610841 (y : real) : (term29 y) = False.
Proof. exact (@lem1610840 (term8 y)). Qed.
Lemma lem1610842 (y : real) (x : real) (h1 : x = term6) : (term22 x y) = False.
Proof. exact (TRANS (@lem1610838 y x h1) (@lem1610841 y)). Qed.
Lemma lem1610843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1610844 (y : real) (x : real) (h1 : x = term6) : (term23 x y) = (or False).
Proof. exact (MK_COMB (@lem1610843) (@lem1610842 y x h1)). Qed.
Lemma lem1610850 (x : real) (h1 : x = term6) : x = term6.
Proof. exact (h1). Qed.
Lemma lem1610851 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1610852 (x : real) (h1 : x = term6) : (real_lt x) = term17.
Proof. exact (MK_COMB (@lem1610851) (@lem1610850 x h1)). Qed.
Lemma lem1610853 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1610854 (x : real) (h1 : x = term6) : (term24 x) = term19.
Proof. exact (MK_COMB (@lem1610852 x h1) (@lem1610853)). Qed.
Lemma lem1610856 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1610787 x (@lem1610786 x)). Qed.
Lemma lem1610857 : term19 = False.
Proof. exact (@lem1610856 term6). Qed.
Lemma lem1610858 (x : real) (h1 : x = term6) : (term24 x) = False.
Proof. exact (TRANS (@lem1610854 x h1) (@lem1610857)). Qed.
Lemma lem1610859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1610860 (x : real) (h1 : x = term6) : (term25 x) = (and False).
Proof. exact (MK_COMB (@lem1610859) (@lem1610858 x h1)). Qed.
Lemma lem1610863 (y : real) : (term24 y) = (term24 y).
Proof. exact (eq_refl (term24 y)). Qed.
Lemma lem1610864 (y : real) (x : real) (h1 : x = term6) : (term26 x y) = (term28 y).
Proof. exact (MK_COMB (@lem1610860 x h1) (@lem1610863 y)). Qed.
Lemma lem1610866 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1610867 (y : real) : (term28 y) = False.
Proof. exact (@lem1610866 (term24 y)). Qed.
Lemma lem1610868 (y : real) (x : real) (h1 : x = term6) : (term26 x y) = False.
Proof. exact (TRANS (@lem1610864 y x h1) (@lem1610867 y)). Qed.
Lemma lem1610869 (y : real) (x : real) (h1 : x = term6) : (term27 x y) = (False \/ False).
Proof. exact (MK_COMB (@lem1610844 y x h1) (@lem1610868 y x h1)). Qed.
Lemma lem1610871 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1610872 : (False \/ False) = False.
Proof. exact (@lem1610871 False). Qed.
Lemma lem1610873 (y : real) (x : real) (h1 : x = term6) : (term27 x y) = False.
Proof. exact (TRANS (@lem1610869 y x h1) (@lem1610872)). Qed.
Lemma lem1610874 (y : real) (x : real) (h1 : x = term6) : ((term18 x y) = (term27 x y)) = (False = False).
Proof. exact (MK_COMB (@lem1610818 y x h1) (@lem1610873 y x h1)). Qed.
Lemma lem1610876 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1610877 : (False = False) = (~ False).
Proof. exact (@lem1610876 False). Qed.
Lemma lem1610879 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1610880 : (False = False) = True.
Proof. exact (TRANS (@lem1610877) (@lem1610879)). Qed.
Lemma lem1610881 (y : real) (x : real) (h1 : x = term6) : ((term18 x y) = (term27 x y)) = True.
Proof. exact (TRANS (@lem1610874 y x h1) (@lem1610880)). Qed.
Lemma lem1610882 (y : real) (x : real) (h1 : x = term6) : True = ((term18 x y) = (term27 x y)).
Proof. exact (SYM (@lem1610881 y x h1)). Qed.
Lemma lem1610883 (y : real) (x : real) (h1 : x = term6) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1610882 y x h1) (@lem0)). Qed.
Lemma lem1610884 (x : real) : term10 x.
Proof. exact (@lem1379422 x). Qed.
Lemma lem1610885 (x : real) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1610886 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1610885 x) (@lem1610884 x)). Qed.
Lemma lem1610887 (x : real) : term12 x.
Proof. exact (@lem82 (real_lt x x)). Qed.
Lemma lem1610889 (x : real) : term30 x.
Proof. exact (@lem1356740 x). Qed.
Lemma lem1610890 (x : real) : (term30 x) = ((term31 x) = term6).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1610895 (x : real) : (term8 x) = ((term8 x) = True).
Proof. exact (@lem7 (term8 x)). Qed.
Lemma lem1610902 (y : real) (h1 : y = term6) : y = term6.
Proof. exact (h1). Qed.
Lemma lem1610903 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1610904 (x : real) (y : real) (h1 : y = term6) : (real_mul x y) = (term31 x).
Proof. exact (MK_COMB (@lem1610903 x) (@lem1610902 y h1)). Qed.
Lemma lem1610906 (x : real) : (term31 x) = term6.
Proof. exact (EQ_MP (@lem1610890 x) (@lem1610889 x)). Qed.
Lemma lem1610907 (x : real) (y : real) (h1 : y = term6) : (real_mul x y) = term6.
Proof. exact (TRANS (@lem1610904 x y h1) (@lem1610906 x)). Qed.
Lemma lem1610908 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1610909 (x : real) (y : real) (h1 : y = term6) : (term18 x y) = term19.
Proof. exact (MK_COMB (@lem1610908) (@lem1610907 x y h1)). Qed.
Lemma lem1610911 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1610887 x (@lem1610886 x)). Qed.
Lemma lem1610912 : term19 = False.
Proof. exact (@lem1610911 term6). Qed.
Lemma lem1610913 (x : real) (y : real) (h1 : y = term6) : (term18 x y) = False.
Proof. exact (TRANS (@lem1610909 x y h1) (@lem1610912)). Qed.
Lemma lem1610914 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1610915 (x : real) (y : real) (h1 : y = term6) : (term20 x y) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1610914) (@lem1610913 x y h1)). Qed.
Lemma lem1610921 (x : real) (h1 : term8 x) : (term8 x) = True.
Proof. exact (EQ_MP (@lem1610895 x) (@lem1610562 x h1)). Qed.
Lemma lem1610922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1610923 (x : real) (h1 : term8 x) : (term21 x) = (and True).
Proof. exact (MK_COMB (@lem1610922) (@lem1610921 x h1)). Qed.
Lemma lem1610927 (y : real) (h1 : y = term6) : y = term6.
Proof. exact (h1). Qed.
Lemma lem1610928 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1610929 (y : real) (h1 : y = term6) : (term8 y) = term19.
Proof. exact (MK_COMB (@lem1610928) (@lem1610927 y h1)). Qed.
Lemma lem1610931 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1610887 x (@lem1610886 x)). Qed.
Lemma lem1610932 : term19 = False.
Proof. exact (@lem1610931 term6). Qed.
Lemma lem1610933 (y : real) (h1 : y = term6) : (term8 y) = False.
Proof. exact (TRANS (@lem1610929 y h1) (@lem1610932)). Qed.
Lemma lem1610934 (y : real) (x : real) (h1 : y = term6) (h2 : term8 x) : (term22 x y) = (True /\ False).
Proof. exact (MK_COMB (@lem1610923 x h2) (@lem1610933 y h1)). Qed.
Lemma lem1610936 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1610937 : (True /\ False) = False.
Proof. exact (@lem1610936 False). Qed.
Lemma lem1610938 (y : real) (x : real) (h1 : y = term6) (h2 : term8 x) : (term22 x y) = False.
Proof. exact (TRANS (@lem1610934 y x h1 h2) (@lem1610937)). Qed.
Lemma lem1610939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1610940 (y : real) (x : real) (h1 : y = term6) (h2 : term8 x) : (term23 x y) = (or False).
Proof. exact (MK_COMB (@lem1610939) (@lem1610938 y x h1 h2)). Qed.
Lemma lem1610948 (y : real) (h1 : y = term6) : y = term6.
Proof. exact (h1). Qed.
Lemma lem1610949 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1610950 (y : real) (h1 : y = term6) : (real_lt y) = term17.
Proof. exact (MK_COMB (@lem1610949) (@lem1610948 y h1)). Qed.
Lemma lem1610951 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1610952 (y : real) (h1 : y = term6) : (term24 y) = term19.
Proof. exact (MK_COMB (@lem1610950 y h1) (@lem1610951)). Qed.
Lemma lem1610954 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1610887 x (@lem1610886 x)). Qed.
Lemma lem1610955 : term19 = False.
Proof. exact (@lem1610954 term6). Qed.
Lemma lem1610956 (y : real) (h1 : y = term6) : (term24 y) = False.
Proof. exact (TRANS (@lem1610952 y h1) (@lem1610955)). Qed.
Lemma lem1610957 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1610958 (x : real) (y : real) (h1 : y = term6) : (term26 x y) = (term32 x).
Proof. exact (MK_COMB (@lem1610957 x) (@lem1610956 y h1)). Qed.
Lemma lem1610960 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1610961 (x : real) : (term32 x) = False.
Proof. exact (@lem1610960 (term24 x)). Qed.
Lemma lem1610962 (x : real) (y : real) (h1 : y = term6) : (term26 x y) = False.
Proof. exact (TRANS (@lem1610958 x y h1) (@lem1610961 x)). Qed.
Lemma lem1610963 (y : real) (x : real) (h1 : y = term6) (h2 : term8 x) : (term27 x y) = (False \/ False).
Proof. exact (MK_COMB (@lem1610940 y x h1 h2) (@lem1610962 x y h1)). Qed.
Lemma lem1610965 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1610966 : (False \/ False) = False.
Proof. exact (@lem1610965 False). Qed.
Lemma lem1610967 (y : real) (x : real) (h1 : y = term6) (h2 : term8 x) : (term27 x y) = False.
Proof. exact (TRANS (@lem1610963 y x h1 h2) (@lem1610966)). Qed.
Lemma lem1610968 (y : real) (x : real) (h1 : y = term6) (h2 : term8 x) : ((term18 x y) = (term27 x y)) = (False = False).
Proof. exact (MK_COMB (@lem1610915 x y h1) (@lem1610967 y x h1 h2)). Qed.
Lemma lem1610970 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1610971 : (False = False) = (~ False).
Proof. exact (@lem1610970 False). Qed.
Lemma lem1610973 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1610974 : (False = False) = True.
Proof. exact (TRANS (@lem1610971) (@lem1610973)). Qed.
Lemma lem1610975 (y : real) (x : real) (h1 : y = term6) (h2 : term8 x) : ((term18 x y) = (term27 x y)) = True.
Proof. exact (TRANS (@lem1610968 y x h1 h2) (@lem1610974)). Qed.
Lemma lem1610976 (y : real) (x : real) (h1 : y = term6) (h2 : term8 x) : True = ((term18 x y) = (term27 x y)).
Proof. exact (SYM (@lem1610975 y x h1 h2)). Qed.
Lemma lem1610977 (y : real) (x : real) (h1 : y = term6) (h2 : term8 x) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1610976 y x h1 h2) (@lem0)). Qed.
Lemma lem1610989 (x : real) : (term8 x) = ((term8 x) = True).
Proof. exact (@lem7 (term8 x)). Qed.
Lemma lem1610991 (y : real) : (term8 y) = ((term8 y) = True).
Proof. exact (@lem7 (term8 y)). Qed.
Lemma lem1611002 (x : real) (h1 : term8 x) : (term8 x) = True.
Proof. exact (EQ_MP (@lem1610989 x) (@lem1610562 x h1)). Qed.
Lemma lem1611003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1611004 (x : real) (h1 : term8 x) : (term21 x) = (and True).
Proof. exact (MK_COMB (@lem1611003) (@lem1611002 x h1)). Qed.
Lemma lem1611006 (y : real) (h1 : term8 y) : (term8 y) = True.
Proof. exact (EQ_MP (@lem1610991 y) (@lem1610566 y h1)). Qed.
Lemma lem1611007 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : (term22 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1611004 x h1) (@lem1611006 y h2)). Qed.
Lemma lem1611009 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1611010 : (True /\ True) = True.
Proof. exact (@lem1611009 True). Qed.
Lemma lem1611011 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : (term22 x y) = True.
Proof. exact (TRANS (@lem1611007 x y h1 h2) (@lem1611010)). Qed.
Lemma lem1611012 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1611013 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : (term23 x y) = (or True).
Proof. exact (MK_COMB (@lem1611012) (@lem1611011 x y h1 h2)). Qed.
Lemma lem1611020 (x : real) (y : real) : (term26 x y) = (term26 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1611021 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : (term27 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1611013 x y h1 h2) (@lem1611020 x y)). Qed.
Lemma lem1611023 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1611024 (x : real) (y : real) : (term33 x y) = True.
Proof. exact (@lem1611023 (term26 x y)). Qed.
Lemma lem1611025 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : (term27 x y) = True.
Proof. exact (TRANS (@lem1611021 x y h1 h2) (@lem1611024 x y)). Qed.
Lemma lem1611026 (x : real) (y : real) : (term20 x y) = (term20 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1611027 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : ((term18 x y) = (term27 x y)) = ((term18 x y) = True).
Proof. exact (MK_COMB (@lem1611026 x y) (@lem1611025 x y h1 h2)). Qed.
Lemma lem1611029 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1611030 (x : real) (y : real) : ((term18 x y) = True) = (term18 x y).
Proof. exact (@lem1611029 (term18 x y)). Qed.
Lemma lem1611033 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : ((term18 x y) = (term27 x y)) = (term18 x y).
Proof. exact (TRANS (@lem1611027 x y h1 h2) (@lem1611030 x y)). Qed.
Lemma lem1611034 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : (term18 x y) = ((term18 x y) = (term27 x y)).
Proof. exact (SYM (@lem1611033 x y h1 h2)). Qed.
Lemma lem1611046 (x : real) : (term8 x) = ((term8 x) = True).
Proof. exact (@lem7 (term8 x)). Qed.
Lemma lem1611059 (x : real) (h1 : term8 x) : (term8 x) = True.
Proof. exact (EQ_MP (@lem1611046 x) (@lem1610562 x h1)). Qed.
Lemma lem1611060 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1611061 (x : real) (h1 : term8 x) : (term21 x) = (and True).
Proof. exact (MK_COMB (@lem1611060) (@lem1611059 x h1)). Qed.
Lemma lem1611064 (y : real) : (term8 y) = (term8 y).
Proof. exact (eq_refl (term8 y)). Qed.
Lemma lem1611065 (y : real) (x : real) (h1 : term8 x) : (term22 x y) = (term34 y).
Proof. exact (MK_COMB (@lem1611061 x h1) (@lem1611064 y)). Qed.
Lemma lem1611067 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1611068 (y : real) : (term34 y) = (term8 y).
Proof. exact (@lem1611067 (term8 y)). Qed.
Lemma lem1611071 (y : real) (x : real) (h1 : term8 x) : (term22 x y) = (term8 y).
Proof. exact (TRANS (@lem1611065 y x h1) (@lem1611068 y)). Qed.
Lemma lem1611072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1611073 (y : real) (x : real) (h1 : term8 x) : (term23 x y) = (term35 y).
Proof. exact (MK_COMB (@lem1611072) (@lem1611071 y x h1)). Qed.
Lemma lem1611080 (x : real) (y : real) : (term26 x y) = (term26 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1611081 (y : real) (x : real) (h1 : term8 x) : (term27 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem1611073 y x h1) (@lem1611080 x y)). Qed.
Lemma lem1611084 (x : real) (y : real) : (term20 x y) = (term20 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1611085 (y : real) (x : real) (h1 : term8 x) : ((term18 x y) = (term27 x y)) = ((term18 x y) = (term36 x y)).
Proof. exact (MK_COMB (@lem1611084 x y) (@lem1611081 y x h1)). Qed.
Lemma lem1611088 (y : real) (x : real) (h1 : term8 x) : ((term18 x y) = (term36 x y)) = ((term18 x y) = (term27 x y)).
Proof. exact (SYM (@lem1611085 y x h1)). Qed.
Lemma lem1611089 (x : real) : term10 x.
Proof. exact (@lem1379422 x). Qed.
Lemma lem1611090 (x : real) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1611091 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1611090 x) (@lem1611089 x)). Qed.
Lemma lem1611092 (x : real) : term12 x.
Proof. exact (@lem82 (real_lt x x)). Qed.
Lemma lem1611094 (x : real) : term30 x.
Proof. exact (@lem1356740 x). Qed.
Lemma lem1611095 (x : real) : (term30 x) = ((term31 x) = term6).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1611107 (y : real) (h1 : y = term6) : y = term6.
Proof. exact (h1). Qed.
Lemma lem1611108 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1611109 (x : real) (y : real) (h1 : y = term6) : (real_mul x y) = (term31 x).
Proof. exact (MK_COMB (@lem1611108 x) (@lem1611107 y h1)). Qed.
Lemma lem1611111 (x : real) : (term31 x) = term6.
Proof. exact (EQ_MP (@lem1611095 x) (@lem1611094 x)). Qed.
Lemma lem1611112 (x : real) (y : real) (h1 : y = term6) : (real_mul x y) = term6.
Proof. exact (TRANS (@lem1611109 x y h1) (@lem1611111 x)). Qed.
Lemma lem1611113 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1611114 (x : real) (y : real) (h1 : y = term6) : (term18 x y) = term19.
Proof. exact (MK_COMB (@lem1611113) (@lem1611112 x y h1)). Qed.
Lemma lem1611116 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1611092 x (@lem1611091 x)). Qed.
Lemma lem1611117 : term19 = False.
Proof. exact (@lem1611116 term6). Qed.
Lemma lem1611118 (x : real) (y : real) (h1 : y = term6) : (term18 x y) = False.
Proof. exact (TRANS (@lem1611114 x y h1) (@lem1611117)). Qed.
Lemma lem1611119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1611120 (x : real) (y : real) (h1 : y = term6) : (term20 x y) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1611119) (@lem1611118 x y h1)). Qed.
Lemma lem1611130 (y : real) (h1 : y = term6) : y = term6.
Proof. exact (h1). Qed.
Lemma lem1611131 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1611132 (y : real) (h1 : y = term6) : (term8 y) = term19.
Proof. exact (MK_COMB (@lem1611131) (@lem1611130 y h1)). Qed.
Lemma lem1611134 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1611092 x (@lem1611091 x)). Qed.
Lemma lem1611135 : term19 = False.
Proof. exact (@lem1611134 term6). Qed.
Lemma lem1611136 (y : real) (h1 : y = term6) : (term8 y) = False.
Proof. exact (TRANS (@lem1611132 y h1) (@lem1611135)). Qed.
Lemma lem1611137 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1611138 (x : real) (y : real) (h1 : y = term6) : (term22 x y) = (term37 x).
Proof. exact (MK_COMB (@lem1611137 x) (@lem1611136 y h1)). Qed.
Lemma lem1611140 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1611141 (x : real) : (term37 x) = False.
Proof. exact (@lem1611140 (term8 x)). Qed.
Lemma lem1611142 (x : real) (y : real) (h1 : y = term6) : (term22 x y) = False.
Proof. exact (TRANS (@lem1611138 x y h1) (@lem1611141 x)). Qed.
Lemma lem1611143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1611144 (x : real) (y : real) (h1 : y = term6) : (term23 x y) = (or False).
Proof. exact (MK_COMB (@lem1611143) (@lem1611142 x y h1)). Qed.
Lemma lem1611152 (y : real) (h1 : y = term6) : y = term6.
Proof. exact (h1). Qed.
Lemma lem1611153 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1611154 (y : real) (h1 : y = term6) : (real_lt y) = term17.
Proof. exact (MK_COMB (@lem1611153) (@lem1611152 y h1)). Qed.
Lemma lem1611155 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611156 (y : real) (h1 : y = term6) : (term24 y) = term19.
Proof. exact (MK_COMB (@lem1611154 y h1) (@lem1611155)). Qed.
Lemma lem1611158 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1611092 x (@lem1611091 x)). Qed.
Lemma lem1611159 : term19 = False.
Proof. exact (@lem1611158 term6). Qed.
Lemma lem1611160 (y : real) (h1 : y = term6) : (term24 y) = False.
Proof. exact (TRANS (@lem1611156 y h1) (@lem1611159)). Qed.
Lemma lem1611161 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1611162 (x : real) (y : real) (h1 : y = term6) : (term26 x y) = (term32 x).
Proof. exact (MK_COMB (@lem1611161 x) (@lem1611160 y h1)). Qed.
Lemma lem1611164 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1611165 (x : real) : (term32 x) = False.
Proof. exact (@lem1611164 (term24 x)). Qed.
Lemma lem1611166 (x : real) (y : real) (h1 : y = term6) : (term26 x y) = False.
Proof. exact (TRANS (@lem1611162 x y h1) (@lem1611165 x)). Qed.
Lemma lem1611167 (x : real) (y : real) (h1 : y = term6) : (term27 x y) = (False \/ False).
Proof. exact (MK_COMB (@lem1611144 x y h1) (@lem1611166 x y h1)). Qed.
Lemma lem1611169 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1611170 : (False \/ False) = False.
Proof. exact (@lem1611169 False). Qed.
Lemma lem1611171 (x : real) (y : real) (h1 : y = term6) : (term27 x y) = False.
Proof. exact (TRANS (@lem1611167 x y h1) (@lem1611170)). Qed.
Lemma lem1611172 (x : real) (y : real) (h1 : y = term6) : ((term18 x y) = (term27 x y)) = (False = False).
Proof. exact (MK_COMB (@lem1611120 x y h1) (@lem1611171 x y h1)). Qed.
Lemma lem1611174 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1611175 : (False = False) = (~ False).
Proof. exact (@lem1611174 False). Qed.
Lemma lem1611177 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1611178 : (False = False) = True.
Proof. exact (TRANS (@lem1611175) (@lem1611177)). Qed.
Lemma lem1611179 (x : real) (y : real) (h1 : y = term6) : ((term18 x y) = (term27 x y)) = True.
Proof. exact (TRANS (@lem1611172 x y h1) (@lem1611178)). Qed.
Lemma lem1611180 (x : real) (y : real) (h1 : y = term6) : True = ((term18 x y) = (term27 x y)).
Proof. exact (SYM (@lem1611179 x y h1)). Qed.
Lemma lem1611181 (x : real) (y : real) (h1 : y = term6) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1611180 x y h1) (@lem0)). Qed.
Lemma lem1611195 (y : real) : (term8 y) = ((term8 y) = True).
Proof. exact (@lem7 (term8 y)). Qed.
Lemma lem1611208 (y : real) (h1 : term8 y) : (term8 y) = True.
Proof. exact (EQ_MP (@lem1611195 y) (@lem1610568 y h1)). Qed.
Lemma lem1611209 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1611210 (x : real) (y : real) (h1 : term8 y) : (term22 x y) = (term38 x).
Proof. exact (MK_COMB (@lem1611209 x) (@lem1611208 y h1)). Qed.
Lemma lem1611212 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1611213 (x : real) : (term38 x) = (term8 x).
Proof. exact (@lem1611212 (term8 x)). Qed.
Lemma lem1611216 (x : real) (y : real) (h1 : term8 y) : (term22 x y) = (term8 x).
Proof. exact (TRANS (@lem1611210 x y h1) (@lem1611213 x)). Qed.
Lemma lem1611217 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1611218 (x : real) (y : real) (h1 : term8 y) : (term23 x y) = (term35 x).
Proof. exact (MK_COMB (@lem1611217) (@lem1611216 x y h1)). Qed.
Lemma lem1611225 (x : real) (y : real) : (term26 x y) = (term26 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1611226 (x : real) (y : real) (h1 : term8 y) : (term27 x y) = (term39 x y).
Proof. exact (MK_COMB (@lem1611218 x y h1) (@lem1611225 x y)). Qed.
Lemma lem1611229 (x : real) (y : real) : (term20 x y) = (term20 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1611230 (x : real) (y : real) (h1 : term8 y) : ((term18 x y) = (term27 x y)) = ((term18 x y) = (term39 x y)).
Proof. exact (MK_COMB (@lem1611229 x y) (@lem1611226 x y h1)). Qed.
Lemma lem1611233 (x : real) (y : real) (h1 : term8 y) : ((term18 x y) = (term39 x y)) = ((term18 x y) = (term27 x y)).
Proof. exact (SYM (@lem1611230 x y h1)). Qed.
Lemma lem1611269 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : term22 y x.
Proof. exact (conj (@lem1610566 y h2) (@lem1610562 x h1)). Qed.
Lemma lem1611271 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem1610550 x y) (@lem1610549 x y)). Qed.
Lemma lem1611272 (y : real) (x : real) : term3 y x.
Proof. exact (@lem1611271 y x). Qed.
Lemma lem1611273 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : term18 y x.
Proof. exact (@lem1611272 y x (@lem1611269 x y h1 h2)). Qed.
Lemma lem1611274 (x : real) (y : real) (h1 : term8 x) (h2 : term9 y) : term40 y x.
Proof. exact (conj (@lem1610567 y h2) (@lem1610562 x h1)). Qed.
Lemma lem1611276 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem1610550 x y) (@lem1610549 x y)). Qed.
Lemma lem1611277 (y : real) (x : real) : term41 y x.
Proof. exact (@lem1611276 (real_neg y) x). Qed.
Lemma lem1611278 (x : real) (y : real) (h1 : term8 x) (h2 : term9 y) : term42 y x.
Proof. exact (@lem1611277 y x (@lem1611274 x y h1 h2)). Qed.
Lemma lem1611279 (y : real) (x : real) (h1 : term8 y) (h2 : term9 x) : term43 y x.
Proof. exact (conj (@lem1610568 y h1) (@lem1610563 x h2)). Qed.
Lemma lem1611281 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem1610550 x y) (@lem1610549 x y)). Qed.
Lemma lem1611282 (y : real) (x : real) : term44 y x.
Proof. exact (@lem1611281 y (real_neg x)). Qed.
Lemma lem1611283 (y : real) (x : real) (h1 : term8 y) (h2 : term9 x) : term45 y x.
Proof. exact (@lem1611282 y x (@lem1611279 y x h1 h2)). Qed.
Lemma lem1611284 (x : real) (y : real) (h1 : term9 x) (h2 : term9 y) : term46 y x.
Proof. exact (conj (@lem1610569 y h2) (@lem1610563 x h1)). Qed.
Lemma lem1611286 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem1610550 x y) (@lem1610549 x y)). Qed.
Lemma lem1611287 (y : real) (x : real) : term47 y x.
Proof. exact (@lem1611286 (real_neg y) (real_neg x)). Qed.
Lemma lem1611288 (x : real) (y : real) (h1 : term9 x) (h2 : term9 y) : term48 y x.
Proof. exact (@lem1611287 y x (@lem1611284 x y h1 h2)). Qed.
Lemma lem1611306 (x : real) (y : real) : (term49 x y) = (term50 x y).
Proof. exact (@lem17362 (term18 y x) (term18 x y)). Qed.
Lemma lem1611308 (y : real) : (term21 y) = (term21 y).
Proof. exact (eq_refl (term21 y)). Qed.
Lemma lem1611309 (x : real) (y : real) : (term51 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem1611308 y) (@lem1611306 x y)). Qed.
Lemma lem1611310 (x : real) (y : real) : (term53 x y) = (term51 x y).
Proof. exact (@lem17362 (term8 y) (term54 x y)). Qed.
Lemma lem1611311 (x : real) (y : real) : (term53 x y) = (term52 x y).
Proof. exact (TRANS (@lem1611310 x y) (@lem1611309 x y)). Qed.
Lemma lem1611313 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1611314 (x : real) (y : real) : (term55 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1611313 x) (@lem1611311 x y)). Qed.
Lemma lem1611315 (x : real) (y : real) : (term57 x y) = (term55 x y).
Proof. exact (@lem17362 (term8 x) (term58 x y)). Qed.
Lemma lem1611333 (x : real) (y : real) : (term57 x y) = (term56 x y).
Proof. exact (TRANS (@lem1611315 x y) (@lem1611314 x y)). Qed.
Lemma lem1611334 (x : real) : (term8 x) = (term59 x).
Proof. exact (@lem1483521 x term6). Qed.
Lemma lem1611340 (x : real) : (term60 x) = (term61 x).
Proof. exact (@lem1483519 x term6). Qed.
Lemma lem1611342 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1611343 : term63 = term6.
Proof. exact (@lem1611342 term64). Qed.
Lemma lem1611344 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1611345 (x : real) : (term61 x) = (term65 x).
Proof. exact (MK_COMB (@lem1611344 x) (@lem1611343)). Qed.
Lemma lem1611346 (x : real) : (term65 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1611347 (x : real) : (term61 x) = x.
Proof. exact (TRANS (@lem1611345 x) (@lem1611346 x)). Qed.
Lemma lem1611349 (x : real) : (term60 x) = x.
Proof. exact (TRANS (@lem1611340 x) (@lem1611347 x)). Qed.
Lemma lem1611350 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1611351 (x : real) : (term66 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1611350) (@lem1611349 x)). Qed.
Lemma lem1611352 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611353 (x : real) : (term59 x) = (term67 x).
Proof. exact (MK_COMB (@lem1611351 x) (@lem1611352)). Qed.
Lemma lem1611354 (x : real) : (term8 x) = (term67 x).
Proof. exact (TRANS (@lem1611334 x) (@lem1611353 x)). Qed.
Lemma lem1611355 (y : real) : (term8 y) = (term59 y).
Proof. exact (@lem1483521 y term6). Qed.
Lemma lem1611361 (y : real) : (term60 y) = (term61 y).
Proof. exact (@lem1483519 y term6). Qed.
Lemma lem1611363 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1611364 : term63 = term6.
Proof. exact (@lem1611363 term64). Qed.
Lemma lem1611365 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1611366 (y : real) : (term61 y) = (term65 y).
Proof. exact (MK_COMB (@lem1611365 y) (@lem1611364)). Qed.
Lemma lem1611367 (y : real) : (term65 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1611368 (y : real) : (term61 y) = y.
Proof. exact (TRANS (@lem1611366 y) (@lem1611367 y)). Qed.
Lemma lem1611370 (y : real) : (term60 y) = y.
Proof. exact (TRANS (@lem1611361 y) (@lem1611368 y)). Qed.
Lemma lem1611371 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1611372 (y : real) : (term66 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1611371) (@lem1611370 y)). Qed.
Lemma lem1611373 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611374 (y : real) : (term59 y) = (term67 y).
Proof. exact (MK_COMB (@lem1611372 y) (@lem1611373)). Qed.
Lemma lem1611375 (y : real) : (term8 y) = (term67 y).
Proof. exact (TRANS (@lem1611355 y) (@lem1611374 y)). Qed.
Lemma lem1611376 (y : real) (x : real) : (term18 y x) = (term68 y x).
Proof. exact (@lem1483521 (real_mul y x) term6). Qed.
Lemma lem1611377 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611384 (x : real) (y : real) : (real_mul y x) = (real_mul x y).
Proof. exact (@lem1483474 x y). Qed.
Lemma lem1611385 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1611386 (x : real) (y : real) : (term69 y x) = (term69 x y).
Proof. exact (MK_COMB (@lem1611385) (@lem1611384 x y)). Qed.
Lemma lem1611387 (x : real) (y : real) : (term70 y x) = (term70 x y).
Proof. exact (MK_COMB (@lem1611386 x y) (@lem1611377)). Qed.
Lemma lem1611388 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (@lem1483519 (real_mul x y) term6). Qed.
Lemma lem1611390 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1611391 : term63 = term6.
Proof. exact (@lem1611390 term64). Qed.
Lemma lem1611392 (x : real) (y : real) : (term72 x y) = (term72 x y).
Proof. exact (eq_refl (term72 x y)). Qed.
Lemma lem1611393 (x : real) (y : real) : (term71 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem1611392 x y) (@lem1611391)). Qed.
Lemma lem1611394 (x : real) (y : real) : (term73 x y) = (real_mul x y).
Proof. exact (@lem1483450 (real_mul x y)). Qed.
Lemma lem1611395 (x : real) (y : real) : (term71 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1611393 x y) (@lem1611394 x y)). Qed.
Lemma lem1611396 (x : real) (y : real) : (term70 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1611388 x y) (@lem1611395 x y)). Qed.
Lemma lem1611397 (x : real) (y : real) : (term70 y x) = (real_mul x y).
Proof. exact (TRANS (@lem1611387 x y) (@lem1611396 x y)). Qed.
Lemma lem1611398 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1611399 (x : real) (y : real) : (term74 y x) = (term75 x y).
Proof. exact (MK_COMB (@lem1611398) (@lem1611397 x y)). Qed.
Lemma lem1611400 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611401 (x : real) (y : real) : (term68 y x) = (term76 x y).
Proof. exact (MK_COMB (@lem1611399 x y) (@lem1611400)). Qed.
Lemma lem1611402 (x : real) (y : real) : (term18 y x) = (term76 x y).
Proof. exact (TRANS (@lem1611376 y x) (@lem1611401 x y)). Qed.
Lemma lem1611403 (x : real) (y : real) : (term77 x y) = (term78 x y).
Proof. exact (@lem1483531 term6 (real_mul x y)). Qed.
Lemma lem1611415 (x : real) (y : real) : (term79 x y) = (term80 x y).
Proof. exact (@lem1483519 term6 (real_mul x y)). Qed.
Lemma lem1611420 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (@lem1483448 (term81 x y)). Qed.
Lemma lem1611422 (x : real) (y : real) : (term79 x y) = (term81 x y).
Proof. exact (TRANS (@lem1611415 x y) (@lem1611420 x y)). Qed.
Lemma lem1611423 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1611424 (x : real) (y : real) : (term82 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1611423) (@lem1611422 x y)). Qed.
Lemma lem1611425 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611426 (x : real) (y : real) : (term78 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1611424 x y) (@lem1611425)). Qed.
Lemma lem1611427 (x : real) (y : real) : (term77 x y) = (term84 x y).
Proof. exact (TRANS (@lem1611403 x y) (@lem1611426 x y)). Qed.
Lemma lem1611428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1611429 (x : real) (y : real) : (term85 y x) = (term86 x y).
Proof. exact (MK_COMB (@lem1611428) (@lem1611402 x y)). Qed.
Lemma lem1611430 (x : real) (y : real) : (term50 x y) = (term87 x y).
Proof. exact (MK_COMB (@lem1611429 x y) (@lem1611427 x y)). Qed.
Lemma lem1611431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1611432 (y : real) : (term21 y) = (term88 y).
Proof. exact (MK_COMB (@lem1611431) (@lem1611375 y)). Qed.
Lemma lem1611433 (x : real) (y : real) : (term52 x y) = (term89 x y).
Proof. exact (MK_COMB (@lem1611432 y) (@lem1611430 x y)). Qed.
Lemma lem1611434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1611435 (x : real) : (term21 x) = (term88 x).
Proof. exact (MK_COMB (@lem1611434) (@lem1611354 x)). Qed.
Lemma lem1611436 (x : real) (y : real) : (term56 x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1611435 x) (@lem1611433 x y)). Qed.
Lemma lem1611463 (x : real) (y : real) : (term57 x y) = (term90 x y).
Proof. exact (TRANS (@lem1611333 x y) (@lem1611436 x y)). Qed.
Lemma lem1611467 (x : real) (y : real) (h1 : term90 x y) : term90 x y.
Proof. exact (h1). Qed.
Lemma lem1611468 (x : real) (y : real) (h1 : term90 x y) : term89 x y.
Proof. exact (proj2 (@lem1611467 x y h1)). Qed.
Lemma lem1611470 (x : real) (y : real) (h1 : term90 x y) : term87 x y.
Proof. exact (proj2 (@lem1611468 x y h1)). Qed.
Lemma lem1611472 (x : real) (y : real) (h1 : term90 x y) : term84 x y.
Proof. exact (proj2 (@lem1611470 x y h1)). Qed.
Lemma lem1611473 (x : real) (y : real) (h1 : term90 x y) : term76 x y.
Proof. exact (proj1 (@lem1611470 x y h1)). Qed.
Lemma lem1611475 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1611476 : term92 = term93.
Proof. exact (@lem1611475 (NUMERAL 0) term64). Qed.
Lemma lem1611477 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1611478 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1611479 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1611478 h1) (fun h1 : term93 = True => @lem1611477)). Qed.
Lemma lem1611480 : term93 = True.
Proof. exact (EQ_MP (@lem1611479) (@lem1611477)). Qed.
Lemma lem1611481 : term92 = True.
Proof. exact (TRANS (@lem1611476) (@lem1611480)). Qed.
Lemma lem1611482 : True = term92.
Proof. exact (SYM (@lem1611481)). Qed.
Lemma lem1611483 : term92.
Proof. exact (EQ_MP (@lem1611482) (@lem0)). Qed.
Lemma lem1611484 (x : real) (y : real) (h1 : term90 x y) : term95 x y.
Proof. exact (conj (@lem1611483) (@lem1611472 x y h1)). Qed.
Lemma lem1611486 (x : real) (y : real) : term96 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1611487 (x : real) (y : real) : term97 x y.
Proof. exact (@lem1611486 term98 (term81 x y)). Qed.
Lemma lem1611488 (x : real) (y : real) (h1 : term90 x y) : term99 x y.
Proof. exact (@lem1611487 x y (@lem1611484 x y h1)). Qed.
Lemma lem1611489 (x : real) (y : real) : (term100 x y) = (term81 x y).
Proof. exact (@lem1483460 (term81 x y)). Qed.
Lemma lem1611490 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1611491 (x : real) (y : real) : (term101 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1611490) (@lem1611489 x y)). Qed.
Lemma lem1611492 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611493 (x : real) (y : real) : (term99 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1611491 x y) (@lem1611492)). Qed.
Lemma lem1611494 (x : real) (y : real) (h1 : term90 x y) : term84 x y.
Proof. exact (EQ_MP (@lem1611493 x y) (@lem1611488 x y h1)). Qed.
Lemma lem1611496 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1611497 : term92 = term93.
Proof. exact (@lem1611496 (NUMERAL 0) term64). Qed.
Lemma lem1611498 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1611499 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1611500 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1611499 h1) (fun h1 : term93 = True => @lem1611498)). Qed.
Lemma lem1611501 : term93 = True.
Proof. exact (EQ_MP (@lem1611500) (@lem1611498)). Qed.
Lemma lem1611502 : term92 = True.
Proof. exact (TRANS (@lem1611497) (@lem1611501)). Qed.
Lemma lem1611503 : True = term92.
Proof. exact (SYM (@lem1611502)). Qed.
Lemma lem1611504 : term92.
Proof. exact (EQ_MP (@lem1611503) (@lem0)). Qed.
Lemma lem1611505 (x : real) (y : real) (h1 : term90 x y) : term102 x y.
Proof. exact (conj (@lem1611504) (@lem1611473 x y h1)). Qed.
Lemma lem1611507 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1611508 (x : real) (y : real) : term104 x y.
Proof. exact (@lem1611507 term98 (real_mul x y)). Qed.
Lemma lem1611509 (x : real) (y : real) (h1 : term90 x y) : term105 x y.
Proof. exact (@lem1611508 x y (@lem1611505 x y h1)). Qed.
Lemma lem1611510 (x : real) (y : real) : (term106 x y) = (real_mul x y).
Proof. exact (@lem1483460 (real_mul x y)). Qed.
Lemma lem1611511 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1611512 (x : real) (y : real) : (term107 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1611511) (@lem1611510 x y)). Qed.
Lemma lem1611513 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611514 (x : real) (y : real) : (term105 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1611512 x y) (@lem1611513)). Qed.
Lemma lem1611515 (x : real) (y : real) (h1 : term90 x y) : term76 x y.
Proof. exact (EQ_MP (@lem1611514 x y) (@lem1611509 x y h1)). Qed.
Lemma lem1611516 (x : real) (y : real) (h1 : term90 x y) : term87 x y.
Proof. exact (conj (@lem1611515 x y h1) (@lem1611494 x y h1)). Qed.
Lemma lem1611518 (x : real) (y : real) : term108 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1611519 (x : real) (y : real) : term109 x y.
Proof. exact (@lem1611518 (real_mul x y) (term81 x y)). Qed.
Lemma lem1611520 (x : real) (y : real) (h1 : term90 x y) : term110 x y.
Proof. exact (@lem1611519 x y (@lem1611516 x y h1)). Qed.
Lemma lem1611521 (x : real) (y : real) : (term111 x y) = (term112 x y).
Proof. exact (@lem1483442 term113 (real_mul x y)). Qed.
Lemma lem1611523 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1611524 : term115 = term6.
Proof. exact (@lem1611523 term64). Qed.
Lemma lem1611525 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1611526 : term116 = term15.
Proof. exact (MK_COMB (@lem1611525) (@lem1611524)). Qed.
Lemma lem1611527 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1611528 (x : real) (y : real) : (term112 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem1611526) (@lem1611527 x y)). Qed.
Lemma lem1611529 (x : real) (y : real) : (term111 x y) = (term117 x y).
Proof. exact (TRANS (@lem1611521 x y) (@lem1611528 x y)). Qed.
Lemma lem1611530 (x : real) (y : real) : (term117 x y) = term6.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1611531 (x : real) (y : real) : (term111 x y) = term6.
Proof. exact (TRANS (@lem1611529 x y) (@lem1611530 x y)). Qed.
Lemma lem1611532 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1611533 (x : real) (y : real) : (term118 x y) = term119.
Proof. exact (MK_COMB (@lem1611532) (@lem1611531 x y)). Qed.
Lemma lem1611534 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611535 (x : real) (y : real) : (term110 x y) = term120.
Proof. exact (MK_COMB (@lem1611533 x y) (@lem1611534)). Qed.
Lemma lem1611536 (x : real) (y : real) (h1 : term90 x y) : term120.
Proof. exact (EQ_MP (@lem1611535 x y) (@lem1611520 x y h1)). Qed.
Lemma lem1611538 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1611539 : term120 = term121.
Proof. exact (@lem1611538 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1611540 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1611541 : term120 = False.
Proof. exact (TRANS (@lem1611539) (@lem1611540)). Qed.
Lemma lem1611542 (x : real) (y : real) (h1 : term90 x y) : False.
Proof. exact (EQ_MP (@lem1611541) (@lem1611536 x y h1)). Qed.
Lemma lem1611544 (x : real) (y : real) (h1 : term90 x y) : term90 x y.
Proof. exact (h1). Qed.
Lemma lem1611545 (x : real) (y : real) (h1 : term90 x y) : (term90 x y) = False.
Proof. exact (prop_ext (fun h2 : term90 x y => @lem1611542 x y h1) (fun h2 : False => @lem1611544 x y h1)). Qed.
Lemma lem1611546 (x : real) (y : real) (h1 : term90 x y) : False.
Proof. exact (EQ_MP (@lem1611545 x y h1) (@lem1611544 x y h1)). Qed.
Lemma lem1611547 (x : real) (y : real) (h1 : term57 x y) : term57 x y.
Proof. exact (h1). Qed.
Lemma lem1611548 (x : real) (y : real) (h1 : term57 x y) : term90 x y.
Proof. exact (EQ_MP (@lem1611463 x y) (@lem1611547 x y h1)). Qed.
Lemma lem1611549 (x : real) (y : real) (h1 : term57 x y) : (term90 x y) = False.
Proof. exact (prop_ext (fun h2 : term90 x y => @lem1611546 x y h2) (fun h2 : False => @lem1611548 x y h1)). Qed.
Lemma lem1611550 (x : real) (y : real) (h1 : term57 x y) : False.
Proof. exact (EQ_MP (@lem1611549 x y h1) (@lem1611548 x y h1)). Qed.
Lemma lem1611551 (x : real) (y : real) : term122 x y.
Proof. exact (fun h0 : term57 x y => @lem1611550 x y h0). Qed.
Lemma lem1611552 (x : real) (y : real) : term123 x y.
Proof. exact (@lem1386578 (term124 x y)). Qed.
Lemma lem1611553 (x : real) (y : real) : term124 x y.
Proof. exact (@lem1611552 x y (@lem1611551 x y)). Qed.
Lemma lem1611582 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (@lem17045 (term24 x) (term24 y)). Qed.
Lemma lem1611587 (y : real) : (term127 y) = (term127 y).
Proof. exact (eq_refl (term127 y)). Qed.
Lemma lem1611588 (x : real) (y : real) : (term128 x y) = (term129 x y).
Proof. exact (MK_COMB (@lem1611587 y) (@lem1611582 x y)). Qed.
Lemma lem1611589 (x : real) (y : real) : (term130 x y) = (term128 x y).
Proof. exact (@lem17160 (term8 y) (term26 x y)). Qed.
Lemma lem1611590 (x : real) (y : real) : (term130 x y) = (term129 x y).
Proof. exact (TRANS (@lem1611589 x y) (@lem1611588 x y)). Qed.
Lemma lem1611596 (x : real) (y : real) : (term131 x y) = (term131 x y).
Proof. exact (eq_refl (term131 x y)). Qed.
Lemma lem1611598 (x : real) (y : real) : (term85 x y) = (term85 x y).
Proof. exact (eq_refl (term85 x y)). Qed.
Lemma lem1611599 (x : real) (y : real) : (term132 x y) = (term133 x y).
Proof. exact (MK_COMB (@lem1611598 x y) (@lem1611590 x y)). Qed.
Lemma lem1611600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1611601 (x : real) (y : real) : (term134 x y) = (term135 x y).
Proof. exact (MK_COMB (@lem1611600) (@lem1611599 x y)). Qed.
Lemma lem1611602 (x : real) (y : real) : (term136 x y) = (term137 x y).
Proof. exact (MK_COMB (@lem1611601 x y) (@lem1611596 x y)). Qed.
Lemma lem1611603 (x : real) (y : real) : (term138 x y) = (term136 x y).
Proof. exact (@lem17646 (term18 x y) (term36 x y)). Qed.
Lemma lem1611604 (x : real) (y : real) : (term138 x y) = (term137 x y).
Proof. exact (TRANS (@lem1611603 x y) (@lem1611602 x y)). Qed.
Lemma lem1611606 (y : real) (x : real) : (term139 y x) = (term139 y x).
Proof. exact (eq_refl (term139 y x)). Qed.
Lemma lem1611607 (x : real) (y : real) : (term140 x y) = (term141 x y).
Proof. exact (MK_COMB (@lem1611606 y x) (@lem1611604 x y)). Qed.
Lemma lem1611608 (x : real) (y : real) : (term142 x y) = (term140 x y).
Proof. exact (@lem17362 (term42 y x) ((term18 x y) = (term36 x y))). Qed.
Lemma lem1611609 (x : real) (y : real) : (term142 x y) = (term141 x y).
Proof. exact (TRANS (@lem1611608 x y) (@lem1611607 x y)). Qed.
Lemma lem1611611 (y : real) : (term143 y) = (term143 y).
Proof. exact (eq_refl (term143 y)). Qed.
Lemma lem1611612 (x : real) (y : real) : (term144 x y) = (term145 x y).
Proof. exact (MK_COMB (@lem1611611 y) (@lem1611609 x y)). Qed.
Lemma lem1611613 (x : real) (y : real) : (term146 x y) = (term144 x y).
Proof. exact (@lem17362 (term9 y) (term147 x y)). Qed.
Lemma lem1611614 (x : real) (y : real) : (term146 x y) = (term145 x y).
Proof. exact (TRANS (@lem1611613 x y) (@lem1611612 x y)). Qed.
Lemma lem1611616 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1611617 (x : real) (y : real) : (term148 x y) = (term149 x y).
Proof. exact (MK_COMB (@lem1611616 x) (@lem1611614 x y)). Qed.
Lemma lem1611618 (x : real) (y : real) : (term150 x y) = (term148 x y).
Proof. exact (@lem17362 (term8 x) (term151 x y)). Qed.
Lemma lem1611670 (x : real) (y : real) : (term150 x y) = (term149 x y).
Proof. exact (TRANS (@lem1611618 x y) (@lem1611617 x y)). Qed.
Lemma lem1611671 (x : real) : (term8 x) = (term59 x).
Proof. exact (@lem1483521 x term6). Qed.
Lemma lem1611677 (x : real) : (term60 x) = (term61 x).
Proof. exact (@lem1483519 x term6). Qed.
Lemma lem1611679 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1611680 : term63 = term6.
Proof. exact (@lem1611679 term64). Qed.
Lemma lem1611681 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1611682 (x : real) : (term61 x) = (term65 x).
Proof. exact (MK_COMB (@lem1611681 x) (@lem1611680)). Qed.
Lemma lem1611683 (x : real) : (term65 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1611684 (x : real) : (term61 x) = x.
Proof. exact (TRANS (@lem1611682 x) (@lem1611683 x)). Qed.
Lemma lem1611686 (x : real) : (term60 x) = x.
Proof. exact (TRANS (@lem1611677 x) (@lem1611684 x)). Qed.
Lemma lem1611687 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1611688 (x : real) : (term66 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1611687) (@lem1611686 x)). Qed.
Lemma lem1611689 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611690 (x : real) : (term59 x) = (term67 x).
Proof. exact (MK_COMB (@lem1611688 x) (@lem1611689)). Qed.
Lemma lem1611691 (x : real) : (term8 x) = (term67 x).
Proof. exact (TRANS (@lem1611671 x) (@lem1611690 x)). Qed.
Lemma lem1611692 (y : real) : (term9 y) = (term152 y).
Proof. exact (@lem1483521 (real_neg y) term6). Qed.
Lemma lem1611693 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611700 (y : real) : (real_neg y) = (term153 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1611701 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1611702 (y : real) : (term154 y) = (term155 y).
Proof. exact (MK_COMB (@lem1611701) (@lem1611700 y)). Qed.
Lemma lem1611703 (y : real) : (term156 y) = (term157 y).
Proof. exact (MK_COMB (@lem1611702 y) (@lem1611693)). Qed.
Lemma lem1611704 (y : real) : (term157 y) = (term158 y).
Proof. exact (@lem1483519 (term153 y) term6). Qed.
Lemma lem1611706 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1611707 : term63 = term6.
Proof. exact (@lem1611706 term64). Qed.
Lemma lem1611708 (y : real) : (term159 y) = (term159 y).
Proof. exact (eq_refl (term159 y)). Qed.
Lemma lem1611709 (y : real) : (term158 y) = (term160 y).
Proof. exact (MK_COMB (@lem1611708 y) (@lem1611707)). Qed.
Lemma lem1611710 (y : real) : (term160 y) = (term153 y).
Proof. exact (@lem1483450 (term153 y)). Qed.
Lemma lem1611711 (y : real) : (term158 y) = (term153 y).
Proof. exact (TRANS (@lem1611709 y) (@lem1611710 y)). Qed.
Lemma lem1611712 (y : real) : (term157 y) = (term153 y).
Proof. exact (TRANS (@lem1611704 y) (@lem1611711 y)). Qed.
Lemma lem1611713 (y : real) : (term156 y) = (term153 y).
Proof. exact (TRANS (@lem1611703 y) (@lem1611712 y)). Qed.
Lemma lem1611714 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1611715 (y : real) : (term161 y) = (term162 y).
Proof. exact (MK_COMB (@lem1611714) (@lem1611713 y)). Qed.
Lemma lem1611716 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611717 (y : real) : (term152 y) = (term163 y).
Proof. exact (MK_COMB (@lem1611715 y) (@lem1611716)). Qed.
Lemma lem1611718 (y : real) : (term9 y) = (term163 y).
Proof. exact (TRANS (@lem1611692 y) (@lem1611717 y)). Qed.
Lemma lem1611719 (y : real) (x : real) : (term42 y x) = (term164 y x).
Proof. exact (@lem1483521 (term165 y x) term6). Qed.
Lemma lem1611720 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611721 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1611728 (y : real) : (real_neg y) = (term153 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1611729 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1611730 (y : real) : (term166 y) = (term167 y).
Proof. exact (MK_COMB (@lem1611729) (@lem1611728 y)). Qed.
Lemma lem1611731 (y : real) (x : real) : (term165 y x) = (term168 y x).
Proof. exact (MK_COMB (@lem1611730 y) (@lem1611721 x)). Qed.
Lemma lem1611732 (y : real) (x : real) : (term168 y x) = (term81 y x).
Proof. exact (@lem1483472 term113 y x). Qed.
Lemma lem1611733 (x : real) (y : real) : (real_mul y x) = (real_mul x y).
Proof. exact (@lem1483474 x y). Qed.
Lemma lem1611734 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem1611735 (x : real) (y : real) : (term81 y x) = (term81 x y).
Proof. exact (MK_COMB (@lem1611734) (@lem1611733 x y)). Qed.
Lemma lem1611736 (x : real) (y : real) : (term168 y x) = (term81 x y).
Proof. exact (TRANS (@lem1611732 y x) (@lem1611735 x y)). Qed.
Lemma lem1611737 (x : real) (y : real) : (term165 y x) = (term81 x y).
Proof. exact (TRANS (@lem1611731 y x) (@lem1611736 x y)). Qed.
Lemma lem1611738 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1611739 (x : real) (y : real) : (term170 y x) = (term171 x y).
Proof. exact (MK_COMB (@lem1611738) (@lem1611737 x y)). Qed.
Lemma lem1611740 (x : real) (y : real) : (term172 y x) = (term173 x y).
Proof. exact (MK_COMB (@lem1611739 x y) (@lem1611720)). Qed.
Lemma lem1611741 (x : real) (y : real) : (term173 x y) = (term174 x y).
Proof. exact (@lem1483519 (term81 x y) term6). Qed.
Lemma lem1611743 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1611744 : term63 = term6.
Proof. exact (@lem1611743 term64). Qed.
Lemma lem1611745 (x : real) (y : real) : (term175 x y) = (term175 x y).
Proof. exact (eq_refl (term175 x y)). Qed.
Lemma lem1611746 (x : real) (y : real) : (term174 x y) = (term176 x y).
Proof. exact (MK_COMB (@lem1611745 x y) (@lem1611744)). Qed.
Lemma lem1611747 (x : real) (y : real) : (term176 x y) = (term81 x y).
Proof. exact (@lem1483450 (term81 x y)). Qed.
Lemma lem1611748 (x : real) (y : real) : (term174 x y) = (term81 x y).
Proof. exact (TRANS (@lem1611746 x y) (@lem1611747 x y)). Qed.
Lemma lem1611749 (x : real) (y : real) : (term173 x y) = (term81 x y).
Proof. exact (TRANS (@lem1611741 x y) (@lem1611748 x y)). Qed.
Lemma lem1611750 (x : real) (y : real) : (term172 y x) = (term81 x y).
Proof. exact (TRANS (@lem1611740 x y) (@lem1611749 x y)). Qed.
Lemma lem1611751 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1611752 (x : real) (y : real) : (term177 y x) = (term178 x y).
Proof. exact (MK_COMB (@lem1611751) (@lem1611750 x y)). Qed.
Lemma lem1611753 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611754 (x : real) (y : real) : (term164 y x) = (term179 x y).
Proof. exact (MK_COMB (@lem1611752 x y) (@lem1611753)). Qed.
Lemma lem1611755 (x : real) (y : real) : (term42 y x) = (term179 x y).
Proof. exact (TRANS (@lem1611719 y x) (@lem1611754 x y)). Qed.
Lemma lem1611756 (x : real) (y : real) : (term18 x y) = (term68 x y).
Proof. exact (@lem1483521 (real_mul x y) term6). Qed.
Lemma lem1611768 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (@lem1483519 (real_mul x y) term6). Qed.
Lemma lem1611770 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1611771 : term63 = term6.
Proof. exact (@lem1611770 term64). Qed.
Lemma lem1611772 (x : real) (y : real) : (term72 x y) = (term72 x y).
Proof. exact (eq_refl (term72 x y)). Qed.
Lemma lem1611773 (x : real) (y : real) : (term71 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem1611772 x y) (@lem1611771)). Qed.
Lemma lem1611774 (x : real) (y : real) : (term73 x y) = (real_mul x y).
Proof. exact (@lem1483450 (real_mul x y)). Qed.
Lemma lem1611775 (x : real) (y : real) : (term71 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1611773 x y) (@lem1611774 x y)). Qed.
Lemma lem1611777 (x : real) (y : real) : (term70 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1611768 x y) (@lem1611775 x y)). Qed.
Lemma lem1611778 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1611779 (x : real) (y : real) : (term74 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1611778) (@lem1611777 x y)). Qed.
Lemma lem1611780 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611781 (x : real) (y : real) : (term68 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1611779 x y) (@lem1611780)). Qed.
Lemma lem1611782 (x : real) (y : real) : (term18 x y) = (term76 x y).
Proof. exact (TRANS (@lem1611756 x y) (@lem1611781 x y)). Qed.
Lemma lem1611783 (y : real) : (term180 y) = (term181 y).
Proof. exact (@lem1483531 term6 y). Qed.
Lemma lem1611789 (y : real) : (term182 y) = (term183 y).
Proof. exact (@lem1483519 term6 y). Qed.
Lemma lem1611794 (y : real) : (term183 y) = (term153 y).
Proof. exact (@lem1483448 (term153 y)). Qed.
Lemma lem1611796 (y : real) : (term182 y) = (term153 y).
Proof. exact (TRANS (@lem1611789 y) (@lem1611794 y)). Qed.
Lemma lem1611797 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1611798 (y : real) : (term184 y) = (term185 y).
Proof. exact (MK_COMB (@lem1611797) (@lem1611796 y)). Qed.
Lemma lem1611799 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611800 (y : real) : (term181 y) = (term186 y).
Proof. exact (MK_COMB (@lem1611798 y) (@lem1611799)). Qed.
Lemma lem1611801 (y : real) : (term180 y) = (term186 y).
Proof. exact (TRANS (@lem1611783 y) (@lem1611800 y)). Qed.
Lemma lem1611802 (x : real) : (term187 x) = (term188 x).
Proof. exact (@lem1483531 x term6). Qed.
Lemma lem1611808 (x : real) : (term60 x) = (term61 x).
Proof. exact (@lem1483519 x term6). Qed.
Lemma lem1611810 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1611811 : term63 = term6.
Proof. exact (@lem1611810 term64). Qed.
Lemma lem1611812 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1611813 (x : real) : (term61 x) = (term65 x).
Proof. exact (MK_COMB (@lem1611812 x) (@lem1611811)). Qed.
Lemma lem1611814 (x : real) : (term65 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1611815 (x : real) : (term61 x) = x.
Proof. exact (TRANS (@lem1611813 x) (@lem1611814 x)). Qed.
Lemma lem1611817 (x : real) : (term60 x) = x.
Proof. exact (TRANS (@lem1611808 x) (@lem1611815 x)). Qed.
Lemma lem1611818 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1611819 (x : real) : (term189 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1611818) (@lem1611817 x)). Qed.
Lemma lem1611820 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611821 (x : real) : (term188 x) = (term190 x).
Proof. exact (MK_COMB (@lem1611819 x) (@lem1611820)). Qed.
Lemma lem1611822 (x : real) : (term187 x) = (term190 x).
Proof. exact (TRANS (@lem1611802 x) (@lem1611821 x)). Qed.
Lemma lem1611823 (y : real) : (term187 y) = (term188 y).
Proof. exact (@lem1483531 y term6). Qed.
Lemma lem1611829 (y : real) : (term60 y) = (term61 y).
Proof. exact (@lem1483519 y term6). Qed.
Lemma lem1611831 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1611832 : term63 = term6.
Proof. exact (@lem1611831 term64). Qed.
Lemma lem1611833 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1611834 (y : real) : (term61 y) = (term65 y).
Proof. exact (MK_COMB (@lem1611833 y) (@lem1611832)). Qed.
Lemma lem1611835 (y : real) : (term65 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1611836 (y : real) : (term61 y) = y.
Proof. exact (TRANS (@lem1611834 y) (@lem1611835 y)). Qed.
Lemma lem1611838 (y : real) : (term60 y) = y.
Proof. exact (TRANS (@lem1611829 y) (@lem1611836 y)). Qed.
Lemma lem1611839 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1611840 (y : real) : (term189 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1611839) (@lem1611838 y)). Qed.
Lemma lem1611841 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611842 (y : real) : (term188 y) = (term190 y).
Proof. exact (MK_COMB (@lem1611840 y) (@lem1611841)). Qed.
Lemma lem1611843 (y : real) : (term187 y) = (term190 y).
Proof. exact (TRANS (@lem1611823 y) (@lem1611842 y)). Qed.
Lemma lem1611844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1611845 (x : real) : (term191 x) = (term192 x).
Proof. exact (MK_COMB (@lem1611844) (@lem1611822 x)). Qed.
Lemma lem1611846 (x : real) (y : real) : (term126 x y) = (term193 x y).
Proof. exact (MK_COMB (@lem1611845 x) (@lem1611843 y)). Qed.
Lemma lem1611847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1611848 (y : real) : (term127 y) = (term194 y).
Proof. exact (MK_COMB (@lem1611847) (@lem1611801 y)). Qed.
Lemma lem1611849 (x : real) (y : real) : (term129 x y) = (term195 x y).
Proof. exact (MK_COMB (@lem1611848 y) (@lem1611846 x y)). Qed.
Lemma lem1611850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1611851 (x : real) (y : real) : (term85 x y) = (term86 x y).
Proof. exact (MK_COMB (@lem1611850) (@lem1611782 x y)). Qed.
Lemma lem1611852 (x : real) (y : real) : (term133 x y) = (term196 x y).
Proof. exact (MK_COMB (@lem1611851 x y) (@lem1611849 x y)). Qed.
Lemma lem1611853 (x : real) (y : real) : (term77 x y) = (term78 x y).
Proof. exact (@lem1483531 term6 (real_mul x y)). Qed.
Lemma lem1611865 (x : real) (y : real) : (term79 x y) = (term80 x y).
Proof. exact (@lem1483519 term6 (real_mul x y)). Qed.
Lemma lem1611870 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (@lem1483448 (term81 x y)). Qed.
Lemma lem1611872 (x : real) (y : real) : (term79 x y) = (term81 x y).
Proof. exact (TRANS (@lem1611865 x y) (@lem1611870 x y)). Qed.
Lemma lem1611873 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1611874 (x : real) (y : real) : (term82 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1611873) (@lem1611872 x y)). Qed.
Lemma lem1611875 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611876 (x : real) (y : real) : (term78 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1611874 x y) (@lem1611875)). Qed.
Lemma lem1611877 (x : real) (y : real) : (term77 x y) = (term84 x y).
Proof. exact (TRANS (@lem1611853 x y) (@lem1611876 x y)). Qed.
Lemma lem1611878 (y : real) : (term8 y) = (term59 y).
Proof. exact (@lem1483521 y term6). Qed.
Lemma lem1611884 (y : real) : (term60 y) = (term61 y).
Proof. exact (@lem1483519 y term6). Qed.
Lemma lem1611886 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1611887 : term63 = term6.
Proof. exact (@lem1611886 term64). Qed.
Lemma lem1611888 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1611889 (y : real) : (term61 y) = (term65 y).
Proof. exact (MK_COMB (@lem1611888 y) (@lem1611887)). Qed.
Lemma lem1611890 (y : real) : (term65 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1611891 (y : real) : (term61 y) = y.
Proof. exact (TRANS (@lem1611889 y) (@lem1611890 y)). Qed.
Lemma lem1611893 (y : real) : (term60 y) = y.
Proof. exact (TRANS (@lem1611884 y) (@lem1611891 y)). Qed.
Lemma lem1611894 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1611895 (y : real) : (term66 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1611894) (@lem1611893 y)). Qed.
Lemma lem1611896 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611897 (y : real) : (term59 y) = (term67 y).
Proof. exact (MK_COMB (@lem1611895 y) (@lem1611896)). Qed.
Lemma lem1611898 (y : real) : (term8 y) = (term67 y).
Proof. exact (TRANS (@lem1611878 y) (@lem1611897 y)). Qed.
Lemma lem1611899 (x : real) : (term24 x) = (term197 x).
Proof. exact (@lem1483521 term6 x). Qed.
Lemma lem1611905 (x : real) : (term182 x) = (term183 x).
Proof. exact (@lem1483519 term6 x). Qed.
Lemma lem1611910 (x : real) : (term183 x) = (term153 x).
Proof. exact (@lem1483448 (term153 x)). Qed.
Lemma lem1611912 (x : real) : (term182 x) = (term153 x).
Proof. exact (TRANS (@lem1611905 x) (@lem1611910 x)). Qed.
Lemma lem1611913 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1611914 (x : real) : (term198 x) = (term162 x).
Proof. exact (MK_COMB (@lem1611913) (@lem1611912 x)). Qed.
Lemma lem1611915 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611916 (x : real) : (term197 x) = (term163 x).
Proof. exact (MK_COMB (@lem1611914 x) (@lem1611915)). Qed.
Lemma lem1611917 (x : real) : (term24 x) = (term163 x).
Proof. exact (TRANS (@lem1611899 x) (@lem1611916 x)). Qed.
Lemma lem1611918 (y : real) : (term24 y) = (term197 y).
Proof. exact (@lem1483521 term6 y). Qed.
Lemma lem1611924 (y : real) : (term182 y) = (term183 y).
Proof. exact (@lem1483519 term6 y). Qed.
Lemma lem1611929 (y : real) : (term183 y) = (term153 y).
Proof. exact (@lem1483448 (term153 y)). Qed.
Lemma lem1611931 (y : real) : (term182 y) = (term153 y).
Proof. exact (TRANS (@lem1611924 y) (@lem1611929 y)). Qed.
Lemma lem1611932 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1611933 (y : real) : (term198 y) = (term162 y).
Proof. exact (MK_COMB (@lem1611932) (@lem1611931 y)). Qed.
Lemma lem1611934 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1611935 (y : real) : (term197 y) = (term163 y).
Proof. exact (MK_COMB (@lem1611933 y) (@lem1611934)). Qed.
Lemma lem1611936 (y : real) : (term24 y) = (term163 y).
Proof. exact (TRANS (@lem1611918 y) (@lem1611935 y)). Qed.
Lemma lem1611937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1611938 (x : real) : (term25 x) = (term199 x).
Proof. exact (MK_COMB (@lem1611937) (@lem1611917 x)). Qed.
Lemma lem1611939 (x : real) (y : real) : (term26 x y) = (term200 x y).
Proof. exact (MK_COMB (@lem1611938 x) (@lem1611936 y)). Qed.
Lemma lem1611940 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1611941 (y : real) : (term35 y) = (term201 y).
Proof. exact (MK_COMB (@lem1611940) (@lem1611898 y)). Qed.
Lemma lem1611942 (x : real) (y : real) : (term36 x y) = (term202 x y).
Proof. exact (MK_COMB (@lem1611941 y) (@lem1611939 x y)). Qed.
Lemma lem1611943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1611944 (x : real) (y : real) : (term203 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem1611943) (@lem1611877 x y)). Qed.
Lemma lem1611945 (x : real) (y : real) : (term131 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem1611944 x y) (@lem1611942 x y)). Qed.
Lemma lem1611946 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1611947 (x : real) (y : real) : (term135 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem1611946) (@lem1611852 x y)). Qed.
Lemma lem1611948 (x : real) (y : real) : (term137 x y) = (term207 x y).
Proof. exact (MK_COMB (@lem1611947 x y) (@lem1611945 x y)). Qed.
Lemma lem1611949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1611950 (x : real) (y : real) : (term139 y x) = (term208 x y).
Proof. exact (MK_COMB (@lem1611949) (@lem1611755 x y)). Qed.
Lemma lem1611951 (x : real) (y : real) : (term141 x y) = (term209 x y).
Proof. exact (MK_COMB (@lem1611950 x y) (@lem1611948 x y)). Qed.
Lemma lem1611952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1611953 (y : real) : (term143 y) = (term199 y).
Proof. exact (MK_COMB (@lem1611952) (@lem1611718 y)). Qed.
Lemma lem1611954 (x : real) (y : real) : (term145 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem1611953 y) (@lem1611951 x y)). Qed.
Lemma lem1611955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1611956 (x : real) : (term21 x) = (term88 x).
Proof. exact (MK_COMB (@lem1611955) (@lem1611691 x)). Qed.
Lemma lem1611957 (x : real) (y : real) : (term149 x y) = (term211 x y).
Proof. exact (MK_COMB (@lem1611956 x) (@lem1611954 x y)). Qed.
Lemma lem1611964 (x : real) (y : real) : (term150 x y) = (term211 x y).
Proof. exact (TRANS (@lem1611670 x y) (@lem1611957 x y)). Qed.
Lemma lem1611987 (x : real) (y : real) : (term205 x y) = (term212 x y).
Proof. exact (@lem19158 (term67 y) (term84 x y) (term200 x y)). Qed.
Lemma lem1612004 (x : real) (y : real) : (term195 x y) = (term213 x y).
Proof. exact (@lem19158 (term190 x) (term186 y) (term190 y)). Qed.
Lemma lem1612007 (x : real) (y : real) : (term86 x y) = (term86 x y).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1612008 (x : real) (y : real) : (term196 x y) = (term214 x y).
Proof. exact (MK_COMB (@lem1612007 x y) (@lem1612004 x y)). Qed.
Lemma lem1612015 (x : real) (y : real) : (term214 x y) = (term215 x y).
Proof. exact (@lem19158 (term216 y x) (term76 x y) (term217 y)). Qed.
Lemma lem1612016 (x : real) (y : real) : (term196 x y) = (term215 x y).
Proof. exact (TRANS (@lem1612008 x y) (@lem1612015 x y)). Qed.
Lemma lem1612017 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1612018 (x : real) (y : real) : (term206 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem1612017) (@lem1612016 x y)). Qed.
Lemma lem1612019 (x : real) (y : real) : (term207 x y) = (term219 x y).
Proof. exact (MK_COMB (@lem1612018 x y) (@lem1611987 x y)). Qed.
Lemma lem1612022 (x : real) (y : real) : (term208 x y) = (term208 x y).
Proof. exact (eq_refl (term208 x y)). Qed.
Lemma lem1612023 (x : real) (y : real) : (term209 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem1612022 x y) (@lem1612019 x y)). Qed.
Lemma lem1612024 (x : real) (y : real) : (term220 x y) = (term221 x y).
Proof. exact (@lem19158 (term215 x y) (term179 x y) (term212 x y)). Qed.
Lemma lem1612031 (x : real) (y : real) : (term222 x y) = (term223 x y).
Proof. exact (@lem19158 (term224 x y) (term179 x y) (term225 x y)). Qed.
Lemma lem1612038 (x : real) (y : real) : (term226 x y) = (term227 x y).
Proof. exact (@lem19158 (term228 y x) (term179 x y) (term229 x y)). Qed.
Lemma lem1612039 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1612040 (x : real) (y : real) : (term230 x y) = (term231 x y).
Proof. exact (MK_COMB (@lem1612039) (@lem1612038 x y)). Qed.
Lemma lem1612041 (x : real) (y : real) : (term221 x y) = (term232 x y).
Proof. exact (MK_COMB (@lem1612040 x y) (@lem1612031 x y)). Qed.
Lemma lem1612042 (x : real) (y : real) : (term220 x y) = (term232 x y).
Proof. exact (TRANS (@lem1612024 x y) (@lem1612041 x y)). Qed.
Lemma lem1612043 (x : real) (y : real) : (term209 x y) = (term232 x y).
Proof. exact (TRANS (@lem1612023 x y) (@lem1612042 x y)). Qed.
Lemma lem1612046 (y : real) : (term199 y) = (term199 y).
Proof. exact (eq_refl (term199 y)). Qed.
Lemma lem1612047 (x : real) (y : real) : (term210 x y) = (term233 x y).
Proof. exact (MK_COMB (@lem1612046 y) (@lem1612043 x y)). Qed.
Lemma lem1612048 (x : real) (y : real) : (term233 x y) = (term234 x y).
Proof. exact (@lem19158 (term227 x y) (term163 y) (term223 x y)). Qed.
Lemma lem1612055 (x : real) (y : real) : (term235 x y) = (term236 x y).
Proof. exact (@lem19158 (term237 x y) (term163 y) (term238 x y)). Qed.
Lemma lem1612062 (x : real) (y : real) : (term239 x y) = (term240 x y).
Proof. exact (@lem19158 (term241 y x) (term163 y) (term242 x y)). Qed.
Lemma lem1612063 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1612064 (x : real) (y : real) : (term243 x y) = (term244 x y).
Proof. exact (MK_COMB (@lem1612063) (@lem1612062 x y)). Qed.
Lemma lem1612065 (x : real) (y : real) : (term234 x y) = (term245 x y).
Proof. exact (MK_COMB (@lem1612064 x y) (@lem1612055 x y)). Qed.
Lemma lem1612066 (x : real) (y : real) : (term233 x y) = (term245 x y).
Proof. exact (TRANS (@lem1612048 x y) (@lem1612065 x y)). Qed.
Lemma lem1612067 (x : real) (y : real) : (term210 x y) = (term245 x y).
Proof. exact (TRANS (@lem1612047 x y) (@lem1612066 x y)). Qed.
Lemma lem1612070 (x : real) : (term88 x) = (term88 x).
Proof. exact (eq_refl (term88 x)). Qed.
Lemma lem1612071 (x : real) (y : real) : (term211 x y) = (term246 x y).
Proof. exact (MK_COMB (@lem1612070 x) (@lem1612067 x y)). Qed.
Lemma lem1612072 (x : real) (y : real) : (term246 x y) = (term247 x y).
Proof. exact (@lem19158 (term240 x y) (term67 x) (term236 x y)). Qed.
Lemma lem1612079 (x : real) (y : real) : (term248 x y) = (term249 x y).
Proof. exact (@lem19158 (term250 x y) (term67 x) (term251 x y)). Qed.
Lemma lem1612086 (x : real) (y : real) : (term252 x y) = (term253 x y).
Proof. exact (@lem19158 (term254 y x) (term67 x) (term255 x y)). Qed.
Lemma lem1612087 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1612088 (x : real) (y : real) : (term256 x y) = (term257 x y).
Proof. exact (MK_COMB (@lem1612087) (@lem1612086 x y)). Qed.
Lemma lem1612089 (x : real) (y : real) : (term247 x y) = (term258 x y).
Proof. exact (MK_COMB (@lem1612088 x y) (@lem1612079 x y)). Qed.
Lemma lem1612090 (x : real) (y : real) : (term246 x y) = (term258 x y).
Proof. exact (TRANS (@lem1612072 x y) (@lem1612089 x y)). Qed.
Lemma lem1612091 (x : real) (y : real) : (term211 x y) = (term258 x y).
Proof. exact (TRANS (@lem1612071 x y) (@lem1612090 x y)). Qed.
Lemma lem1612092 (x : real) (y : real) : (term150 x y) = (term258 x y).
Proof. exact (TRANS (@lem1611964 x y) (@lem1612091 x y)). Qed.
Lemma lem1612114 (x : real) (y : real) (h1 : term258 x y) : term258 x y.
Proof. exact (h1). Qed.
Lemma lem1612115 (x : real) (y : real) (h1 : term253 x y) : term253 x y.
Proof. exact (h1). Qed.
Lemma lem1612116 (y : real) (x : real) (h1 : term259 y x) : term259 y x.
Proof. exact (h1). Qed.
Lemma lem1612117 (y : real) (x : real) (h1 : term259 y x) : term254 y x.
Proof. exact (proj2 (@lem1612116 y x h1)). Qed.
Lemma lem1612119 (y : real) (x : real) (h1 : term259 y x) : term241 y x.
Proof. exact (proj2 (@lem1612117 y x h1)). Qed.
Lemma lem1612121 (y : real) (x : real) (h1 : term259 y x) : term228 y x.
Proof. exact (proj2 (@lem1612119 y x h1)). Qed.
Lemma lem1612122 (y : real) (x : real) (h1 : term259 y x) : term179 x y.
Proof. exact (proj1 (@lem1612119 y x h1)). Qed.
Lemma lem1612124 (y : real) (x : real) (h1 : term259 y x) : term76 x y.
Proof. exact (proj1 (@lem1612121 y x h1)). Qed.
Lemma lem1612128 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1612129 : term92 = term93.
Proof. exact (@lem1612128 (NUMERAL 0) term64). Qed.
Lemma lem1612130 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1612131 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1612132 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1612131 h1) (fun h1 : term93 = True => @lem1612130)). Qed.
Lemma lem1612133 : term93 = True.
Proof. exact (EQ_MP (@lem1612132) (@lem1612130)). Qed.
Lemma lem1612134 : term92 = True.
Proof. exact (TRANS (@lem1612129) (@lem1612133)). Qed.
Lemma lem1612135 : True = term92.
Proof. exact (SYM (@lem1612134)). Qed.
Lemma lem1612136 : term92.
Proof. exact (EQ_MP (@lem1612135) (@lem0)). Qed.
Lemma lem1612137 (y : real) (x : real) (h1 : term259 y x) : term102 x y.
Proof. exact (conj (@lem1612136) (@lem1612124 y x h1)). Qed.
Lemma lem1612139 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1612140 (x : real) (y : real) : term104 x y.
Proof. exact (@lem1612139 term98 (real_mul x y)). Qed.
Lemma lem1612141 (y : real) (x : real) (h1 : term259 y x) : term105 x y.
Proof. exact (@lem1612140 x y (@lem1612137 y x h1)). Qed.
Lemma lem1612142 (x : real) (y : real) : (term106 x y) = (real_mul x y).
Proof. exact (@lem1483460 (real_mul x y)). Qed.
Lemma lem1612143 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612144 (x : real) (y : real) : (term107 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1612143) (@lem1612142 x y)). Qed.
Lemma lem1612145 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612146 (x : real) (y : real) : (term105 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1612144 x y) (@lem1612145)). Qed.
Lemma lem1612147 (y : real) (x : real) (h1 : term259 y x) : term76 x y.
Proof. exact (EQ_MP (@lem1612146 x y) (@lem1612141 y x h1)). Qed.
Lemma lem1612149 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1612150 : term92 = term93.
Proof. exact (@lem1612149 (NUMERAL 0) term64). Qed.
Lemma lem1612151 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1612152 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1612153 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1612152 h1) (fun h1 : term93 = True => @lem1612151)). Qed.
Lemma lem1612154 : term93 = True.
Proof. exact (EQ_MP (@lem1612153) (@lem1612151)). Qed.
Lemma lem1612155 : term92 = True.
Proof. exact (TRANS (@lem1612150) (@lem1612154)). Qed.
Lemma lem1612156 : True = term92.
Proof. exact (SYM (@lem1612155)). Qed.
Lemma lem1612157 : term92.
Proof. exact (EQ_MP (@lem1612156) (@lem0)). Qed.
Lemma lem1612158 (y : real) (x : real) (h1 : term259 y x) : term260 x y.
Proof. exact (conj (@lem1612157) (@lem1612122 y x h1)). Qed.
Lemma lem1612160 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1612161 (x : real) (y : real) : term261 x y.
Proof. exact (@lem1612160 term98 (term81 x y)). Qed.
Lemma lem1612162 (y : real) (x : real) (h1 : term259 y x) : term262 x y.
Proof. exact (@lem1612161 x y (@lem1612158 y x h1)). Qed.
Lemma lem1612163 (x : real) (y : real) : (term100 x y) = (term81 x y).
Proof. exact (@lem1483460 (term81 x y)). Qed.
Lemma lem1612164 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612165 (x : real) (y : real) : (term263 x y) = (term178 x y).
Proof. exact (MK_COMB (@lem1612164) (@lem1612163 x y)). Qed.
Lemma lem1612166 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612167 (x : real) (y : real) : (term262 x y) = (term179 x y).
Proof. exact (MK_COMB (@lem1612165 x y) (@lem1612166)). Qed.
Lemma lem1612168 (y : real) (x : real) (h1 : term259 y x) : term179 x y.
Proof. exact (EQ_MP (@lem1612167 x y) (@lem1612162 y x h1)). Qed.
Lemma lem1612169 (y : real) (x : real) (h1 : term259 y x) : term264 x y.
Proof. exact (conj (@lem1612168 y x h1) (@lem1612147 y x h1)). Qed.
Lemma lem1612171 (x : real) (y : real) : term265 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1612172 (x : real) (y : real) : term266 x y.
Proof. exact (@lem1612171 (term81 x y) (real_mul x y)). Qed.
Lemma lem1612173 (y : real) (x : real) (h1 : term259 y x) : term267 x y.
Proof. exact (@lem1612172 x y (@lem1612169 y x h1)). Qed.
Lemma lem1612174 (x : real) (y : real) : (term268 x y) = (term112 x y).
Proof. exact (@lem1483440 term113 (real_mul x y)). Qed.
Lemma lem1612176 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1612177 : term115 = term6.
Proof. exact (@lem1612176 term64). Qed.
Lemma lem1612178 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1612179 : term116 = term15.
Proof. exact (MK_COMB (@lem1612178) (@lem1612177)). Qed.
Lemma lem1612180 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1612181 (x : real) (y : real) : (term112 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem1612179) (@lem1612180 x y)). Qed.
Lemma lem1612182 (x : real) (y : real) : (term268 x y) = (term117 x y).
Proof. exact (TRANS (@lem1612174 x y) (@lem1612181 x y)). Qed.
Lemma lem1612183 (x : real) (y : real) : (term117 x y) = term6.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1612184 (x : real) (y : real) : (term268 x y) = term6.
Proof. exact (TRANS (@lem1612182 x y) (@lem1612183 x y)). Qed.
Lemma lem1612185 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612186 (x : real) (y : real) : (term269 x y) = term119.
Proof. exact (MK_COMB (@lem1612185) (@lem1612184 x y)). Qed.
Lemma lem1612187 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612188 (x : real) (y : real) : (term267 x y) = term120.
Proof. exact (MK_COMB (@lem1612186 x y) (@lem1612187)). Qed.
Lemma lem1612189 (y : real) (x : real) (h1 : term259 y x) : term120.
Proof. exact (EQ_MP (@lem1612188 x y) (@lem1612173 y x h1)). Qed.
Lemma lem1612191 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1612192 : term120 = term121.
Proof. exact (@lem1612191 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1612193 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1612194 : term120 = False.
Proof. exact (TRANS (@lem1612192) (@lem1612193)). Qed.
Lemma lem1612195 (y : real) (x : real) (h1 : term259 y x) : False.
Proof. exact (EQ_MP (@lem1612194) (@lem1612189 y x h1)). Qed.
Lemma lem1612196 (x : real) (y : real) (h1 : term270 x y) : term270 x y.
Proof. exact (h1). Qed.
Lemma lem1612197 (x : real) (y : real) (h1 : term270 x y) : term255 x y.
Proof. exact (proj2 (@lem1612196 x y h1)). Qed.
Lemma lem1612199 (x : real) (y : real) (h1 : term270 x y) : term242 x y.
Proof. exact (proj2 (@lem1612197 x y h1)). Qed.
Lemma lem1612201 (x : real) (y : real) (h1 : term270 x y) : term229 x y.
Proof. exact (proj2 (@lem1612199 x y h1)). Qed.
Lemma lem1612202 (x : real) (y : real) (h1 : term270 x y) : term179 x y.
Proof. exact (proj1 (@lem1612199 x y h1)). Qed.
Lemma lem1612204 (x : real) (y : real) (h1 : term270 x y) : term76 x y.
Proof. exact (proj1 (@lem1612201 x y h1)). Qed.
Lemma lem1612208 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1612209 : term92 = term93.
Proof. exact (@lem1612208 (NUMERAL 0) term64). Qed.
Lemma lem1612210 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1612211 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1612212 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1612211 h1) (fun h1 : term93 = True => @lem1612210)). Qed.
Lemma lem1612213 : term93 = True.
Proof. exact (EQ_MP (@lem1612212) (@lem1612210)). Qed.
Lemma lem1612214 : term92 = True.
Proof. exact (TRANS (@lem1612209) (@lem1612213)). Qed.
Lemma lem1612215 : True = term92.
Proof. exact (SYM (@lem1612214)). Qed.
Lemma lem1612216 : term92.
Proof. exact (EQ_MP (@lem1612215) (@lem0)). Qed.
Lemma lem1612217 (x : real) (y : real) (h1 : term270 x y) : term102 x y.
Proof. exact (conj (@lem1612216) (@lem1612204 x y h1)). Qed.
Lemma lem1612219 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1612220 (x : real) (y : real) : term104 x y.
Proof. exact (@lem1612219 term98 (real_mul x y)). Qed.
Lemma lem1612221 (x : real) (y : real) (h1 : term270 x y) : term105 x y.
Proof. exact (@lem1612220 x y (@lem1612217 x y h1)). Qed.
Lemma lem1612222 (x : real) (y : real) : (term106 x y) = (real_mul x y).
Proof. exact (@lem1483460 (real_mul x y)). Qed.
Lemma lem1612223 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612224 (x : real) (y : real) : (term107 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1612223) (@lem1612222 x y)). Qed.
Lemma lem1612225 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612226 (x : real) (y : real) : (term105 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1612224 x y) (@lem1612225)). Qed.
Lemma lem1612227 (x : real) (y : real) (h1 : term270 x y) : term76 x y.
Proof. exact (EQ_MP (@lem1612226 x y) (@lem1612221 x y h1)). Qed.
Lemma lem1612229 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1612230 : term92 = term93.
Proof. exact (@lem1612229 (NUMERAL 0) term64). Qed.
Lemma lem1612231 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1612232 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1612233 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1612232 h1) (fun h1 : term93 = True => @lem1612231)). Qed.
Lemma lem1612234 : term93 = True.
Proof. exact (EQ_MP (@lem1612233) (@lem1612231)). Qed.
Lemma lem1612235 : term92 = True.
Proof. exact (TRANS (@lem1612230) (@lem1612234)). Qed.
Lemma lem1612236 : True = term92.
Proof. exact (SYM (@lem1612235)). Qed.
Lemma lem1612237 : term92.
Proof. exact (EQ_MP (@lem1612236) (@lem0)). Qed.
Lemma lem1612238 (x : real) (y : real) (h1 : term270 x y) : term260 x y.
Proof. exact (conj (@lem1612237) (@lem1612202 x y h1)). Qed.
Lemma lem1612240 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1612241 (x : real) (y : real) : term261 x y.
Proof. exact (@lem1612240 term98 (term81 x y)). Qed.
Lemma lem1612242 (x : real) (y : real) (h1 : term270 x y) : term262 x y.
Proof. exact (@lem1612241 x y (@lem1612238 x y h1)). Qed.
Lemma lem1612243 (x : real) (y : real) : (term100 x y) = (term81 x y).
Proof. exact (@lem1483460 (term81 x y)). Qed.
Lemma lem1612244 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612245 (x : real) (y : real) : (term263 x y) = (term178 x y).
Proof. exact (MK_COMB (@lem1612244) (@lem1612243 x y)). Qed.
Lemma lem1612246 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612247 (x : real) (y : real) : (term262 x y) = (term179 x y).
Proof. exact (MK_COMB (@lem1612245 x y) (@lem1612246)). Qed.
Lemma lem1612248 (x : real) (y : real) (h1 : term270 x y) : term179 x y.
Proof. exact (EQ_MP (@lem1612247 x y) (@lem1612242 x y h1)). Qed.
Lemma lem1612249 (x : real) (y : real) (h1 : term270 x y) : term264 x y.
Proof. exact (conj (@lem1612248 x y h1) (@lem1612227 x y h1)). Qed.
Lemma lem1612251 (x : real) (y : real) : term265 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1612252 (x : real) (y : real) : term266 x y.
Proof. exact (@lem1612251 (term81 x y) (real_mul x y)). Qed.
Lemma lem1612253 (x : real) (y : real) (h1 : term270 x y) : term267 x y.
Proof. exact (@lem1612252 x y (@lem1612249 x y h1)). Qed.
Lemma lem1612254 (x : real) (y : real) : (term268 x y) = (term112 x y).
Proof. exact (@lem1483440 term113 (real_mul x y)). Qed.
Lemma lem1612256 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1612257 : term115 = term6.
Proof. exact (@lem1612256 term64). Qed.
Lemma lem1612258 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1612259 : term116 = term15.
Proof. exact (MK_COMB (@lem1612258) (@lem1612257)). Qed.
Lemma lem1612260 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1612261 (x : real) (y : real) : (term112 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem1612259) (@lem1612260 x y)). Qed.
Lemma lem1612262 (x : real) (y : real) : (term268 x y) = (term117 x y).
Proof. exact (TRANS (@lem1612254 x y) (@lem1612261 x y)). Qed.
Lemma lem1612263 (x : real) (y : real) : (term117 x y) = term6.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1612264 (x : real) (y : real) : (term268 x y) = term6.
Proof. exact (TRANS (@lem1612262 x y) (@lem1612263 x y)). Qed.
Lemma lem1612265 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612266 (x : real) (y : real) : (term269 x y) = term119.
Proof. exact (MK_COMB (@lem1612265) (@lem1612264 x y)). Qed.
Lemma lem1612267 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612268 (x : real) (y : real) : (term267 x y) = term120.
Proof. exact (MK_COMB (@lem1612266 x y) (@lem1612267)). Qed.
Lemma lem1612269 (x : real) (y : real) (h1 : term270 x y) : term120.
Proof. exact (EQ_MP (@lem1612268 x y) (@lem1612253 x y h1)). Qed.
Lemma lem1612271 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1612272 : term120 = term121.
Proof. exact (@lem1612271 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1612273 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1612274 : term120 = False.
Proof. exact (TRANS (@lem1612272) (@lem1612273)). Qed.
Lemma lem1612275 (x : real) (y : real) (h1 : term270 x y) : False.
Proof. exact (EQ_MP (@lem1612274) (@lem1612269 x y h1)). Qed.
Lemma lem1612276 (x : real) (y : real) (h1 : term253 x y) : False.
Proof. exact (or_elim (@lem1612115 x y h1) (fun h0 : term259 y x => @lem1612195 y x h0) (fun h0 : term270 x y => @lem1612275 x y h0)). Qed.
Lemma lem1612277 (x : real) (y : real) (h1 : term249 x y) : term249 x y.
Proof. exact (h1). Qed.
Lemma lem1612278 (x : real) (y : real) (h1 : term271 x y) : term271 x y.
Proof. exact (h1). Qed.
Lemma lem1612279 (x : real) (y : real) (h1 : term271 x y) : term250 x y.
Proof. exact (proj2 (@lem1612278 x y h1)). Qed.
Lemma lem1612281 (x : real) (y : real) (h1 : term271 x y) : term237 x y.
Proof. exact (proj2 (@lem1612279 x y h1)). Qed.
Lemma lem1612282 (x : real) (y : real) (h1 : term271 x y) : term163 y.
Proof. exact (proj1 (@lem1612279 x y h1)). Qed.
Lemma lem1612283 (x : real) (y : real) (h1 : term271 x y) : term224 x y.
Proof. exact (proj2 (@lem1612281 x y h1)). Qed.
Lemma lem1612285 (x : real) (y : real) (h1 : term271 x y) : term67 y.
Proof. exact (proj2 (@lem1612283 x y h1)). Qed.
Lemma lem1612288 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1612289 : term92 = term93.
Proof. exact (@lem1612288 (NUMERAL 0) term64). Qed.
Lemma lem1612290 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1612291 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1612292 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1612291 h1) (fun h1 : term93 = True => @lem1612290)). Qed.
Lemma lem1612293 : term93 = True.
Proof. exact (EQ_MP (@lem1612292) (@lem1612290)). Qed.
Lemma lem1612294 : term92 = True.
Proof. exact (TRANS (@lem1612289) (@lem1612293)). Qed.
Lemma lem1612295 : True = term92.
Proof. exact (SYM (@lem1612294)). Qed.
Lemma lem1612296 : term92.
Proof. exact (EQ_MP (@lem1612295) (@lem0)). Qed.
Lemma lem1612297 (x : real) (y : real) (h1 : term271 x y) : term272 y.
Proof. exact (conj (@lem1612296) (@lem1612285 x y h1)). Qed.
Lemma lem1612299 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1612300 (y : real) : term273 y.
Proof. exact (@lem1612299 term98 y). Qed.
Lemma lem1612301 (x : real) (y : real) (h1 : term271 x y) : term274 y.
Proof. exact (@lem1612300 y (@lem1612297 x y h1)). Qed.
Lemma lem1612302 (y : real) : (term275 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1612303 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612304 (y : real) : (term276 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1612303) (@lem1612302 y)). Qed.
Lemma lem1612305 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612306 (y : real) : (term274 y) = (term67 y).
Proof. exact (MK_COMB (@lem1612304 y) (@lem1612305)). Qed.
Lemma lem1612307 (x : real) (y : real) (h1 : term271 x y) : term67 y.
Proof. exact (EQ_MP (@lem1612306 y) (@lem1612301 x y h1)). Qed.
Lemma lem1612309 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1612310 : term92 = term93.
Proof. exact (@lem1612309 (NUMERAL 0) term64). Qed.
Lemma lem1612311 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1612312 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1612313 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1612312 h1) (fun h1 : term93 = True => @lem1612311)). Qed.
Lemma lem1612314 : term93 = True.
Proof. exact (EQ_MP (@lem1612313) (@lem1612311)). Qed.
Lemma lem1612315 : term92 = True.
Proof. exact (TRANS (@lem1612310) (@lem1612314)). Qed.
Lemma lem1612316 : True = term92.
Proof. exact (SYM (@lem1612315)). Qed.
Lemma lem1612317 : term92.
Proof. exact (EQ_MP (@lem1612316) (@lem0)). Qed.
Lemma lem1612318 (x : real) (y : real) (h1 : term271 x y) : term277 y.
Proof. exact (conj (@lem1612317) (@lem1612282 x y h1)). Qed.
Lemma lem1612320 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1612321 (y : real) : term278 y.
Proof. exact (@lem1612320 term98 (term153 y)). Qed.
Lemma lem1612322 (x : real) (y : real) (h1 : term271 x y) : term279 y.
Proof. exact (@lem1612321 y (@lem1612318 x y h1)). Qed.
Lemma lem1612323 (y : real) : (term280 y) = (term153 y).
Proof. exact (@lem1483460 (term153 y)). Qed.
Lemma lem1612324 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612325 (y : real) : (term281 y) = (term162 y).
Proof. exact (MK_COMB (@lem1612324) (@lem1612323 y)). Qed.
Lemma lem1612326 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612327 (y : real) : (term279 y) = (term163 y).
Proof. exact (MK_COMB (@lem1612325 y) (@lem1612326)). Qed.
Lemma lem1612328 (x : real) (y : real) (h1 : term271 x y) : term163 y.
Proof. exact (EQ_MP (@lem1612327 y) (@lem1612322 x y h1)). Qed.
Lemma lem1612329 (x : real) (y : real) (h1 : term271 x y) : term282 y.
Proof. exact (conj (@lem1612328 x y h1) (@lem1612307 x y h1)). Qed.
Lemma lem1612331 (x : real) (y : real) : term265 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1612332 (y : real) : term283 y.
Proof. exact (@lem1612331 (term153 y) y). Qed.
Lemma lem1612333 (x : real) (y : real) (h1 : term271 x y) : term284 y.
Proof. exact (@lem1612332 y (@lem1612329 x y h1)). Qed.
Lemma lem1612334 (y : real) : (term285 y) = (term286 y).
Proof. exact (@lem1483440 term113 y). Qed.
Lemma lem1612336 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1612337 : term115 = term6.
Proof. exact (@lem1612336 term64). Qed.
Lemma lem1612338 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1612339 : term116 = term15.
Proof. exact (MK_COMB (@lem1612338) (@lem1612337)). Qed.
Lemma lem1612340 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1612341 (y : real) : (term286 y) = (term14 y).
Proof. exact (MK_COMB (@lem1612339) (@lem1612340 y)). Qed.
Lemma lem1612342 (y : real) : (term285 y) = (term14 y).
Proof. exact (TRANS (@lem1612334 y) (@lem1612341 y)). Qed.
Lemma lem1612343 (y : real) : (term14 y) = term6.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1612344 (y : real) : (term285 y) = term6.
Proof. exact (TRANS (@lem1612342 y) (@lem1612343 y)). Qed.
Lemma lem1612345 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612346 (y : real) : (term287 y) = term119.
Proof. exact (MK_COMB (@lem1612345) (@lem1612344 y)). Qed.
Lemma lem1612347 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612348 (y : real) : (term284 y) = term120.
Proof. exact (MK_COMB (@lem1612346 y) (@lem1612347)). Qed.
Lemma lem1612349 (x : real) (y : real) (h1 : term271 x y) : term120.
Proof. exact (EQ_MP (@lem1612348 y) (@lem1612333 x y h1)). Qed.
Lemma lem1612351 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1612352 : term120 = term121.
Proof. exact (@lem1612351 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1612353 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1612354 : term120 = False.
Proof. exact (TRANS (@lem1612352) (@lem1612353)). Qed.
Lemma lem1612355 (x : real) (y : real) (h1 : term271 x y) : False.
Proof. exact (EQ_MP (@lem1612354) (@lem1612349 x y h1)). Qed.
Lemma lem1612356 (x : real) (y : real) (h1 : term288 x y) : term288 x y.
Proof. exact (h1). Qed.
Lemma lem1612357 (x : real) (y : real) (h1 : term288 x y) : term251 x y.
Proof. exact (proj2 (@lem1612356 x y h1)). Qed.
Lemma lem1612358 (x : real) (y : real) (h1 : term288 x y) : term67 x.
Proof. exact (proj1 (@lem1612356 x y h1)). Qed.
Lemma lem1612359 (x : real) (y : real) (h1 : term288 x y) : term238 x y.
Proof. exact (proj2 (@lem1612357 x y h1)). Qed.
Lemma lem1612361 (x : real) (y : real) (h1 : term288 x y) : term225 x y.
Proof. exact (proj2 (@lem1612359 x y h1)). Qed.
Lemma lem1612363 (x : real) (y : real) (h1 : term288 x y) : term200 x y.
Proof. exact (proj2 (@lem1612361 x y h1)). Qed.
Lemma lem1612366 (x : real) (y : real) (h1 : term288 x y) : term163 x.
Proof. exact (proj1 (@lem1612363 x y h1)). Qed.
Lemma lem1612368 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1612369 : term92 = term93.
Proof. exact (@lem1612368 (NUMERAL 0) term64). Qed.
Lemma lem1612370 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1612371 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1612372 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1612371 h1) (fun h1 : term93 = True => @lem1612370)). Qed.
Lemma lem1612373 : term93 = True.
Proof. exact (EQ_MP (@lem1612372) (@lem1612370)). Qed.
Lemma lem1612374 : term92 = True.
Proof. exact (TRANS (@lem1612369) (@lem1612373)). Qed.
Lemma lem1612375 : True = term92.
Proof. exact (SYM (@lem1612374)). Qed.
Lemma lem1612376 : term92.
Proof. exact (EQ_MP (@lem1612375) (@lem0)). Qed.
Lemma lem1612377 (x : real) (y : real) (h1 : term288 x y) : term272 x.
Proof. exact (conj (@lem1612376) (@lem1612358 x y h1)). Qed.
Lemma lem1612379 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1612380 (x : real) : term273 x.
Proof. exact (@lem1612379 term98 x). Qed.
Lemma lem1612381 (x : real) (y : real) (h1 : term288 x y) : term274 x.
Proof. exact (@lem1612380 x (@lem1612377 x y h1)). Qed.
Lemma lem1612382 (x : real) : (term275 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1612383 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612384 (x : real) : (term276 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1612383) (@lem1612382 x)). Qed.
Lemma lem1612385 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612386 (x : real) : (term274 x) = (term67 x).
Proof. exact (MK_COMB (@lem1612384 x) (@lem1612385)). Qed.
Lemma lem1612387 (x : real) (y : real) (h1 : term288 x y) : term67 x.
Proof. exact (EQ_MP (@lem1612386 x) (@lem1612381 x y h1)). Qed.
Lemma lem1612389 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1612390 : term92 = term93.
Proof. exact (@lem1612389 (NUMERAL 0) term64). Qed.
Lemma lem1612391 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1612392 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1612393 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1612392 h1) (fun h1 : term93 = True => @lem1612391)). Qed.
Lemma lem1612394 : term93 = True.
Proof. exact (EQ_MP (@lem1612393) (@lem1612391)). Qed.
Lemma lem1612395 : term92 = True.
Proof. exact (TRANS (@lem1612390) (@lem1612394)). Qed.
Lemma lem1612396 : True = term92.
Proof. exact (SYM (@lem1612395)). Qed.
Lemma lem1612397 : term92.
Proof. exact (EQ_MP (@lem1612396) (@lem0)). Qed.
Lemma lem1612398 (x : real) (y : real) (h1 : term288 x y) : term277 x.
Proof. exact (conj (@lem1612397) (@lem1612366 x y h1)). Qed.
Lemma lem1612400 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1612401 (x : real) : term278 x.
Proof. exact (@lem1612400 term98 (term153 x)). Qed.
Lemma lem1612402 (x : real) (y : real) (h1 : term288 x y) : term279 x.
Proof. exact (@lem1612401 x (@lem1612398 x y h1)). Qed.
Lemma lem1612403 (x : real) : (term280 x) = (term153 x).
Proof. exact (@lem1483460 (term153 x)). Qed.
Lemma lem1612404 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612405 (x : real) : (term281 x) = (term162 x).
Proof. exact (MK_COMB (@lem1612404) (@lem1612403 x)). Qed.
Lemma lem1612406 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612407 (x : real) : (term279 x) = (term163 x).
Proof. exact (MK_COMB (@lem1612405 x) (@lem1612406)). Qed.
Lemma lem1612408 (x : real) (y : real) (h1 : term288 x y) : term163 x.
Proof. exact (EQ_MP (@lem1612407 x) (@lem1612402 x y h1)). Qed.
Lemma lem1612409 (x : real) (y : real) (h1 : term288 x y) : term282 x.
Proof. exact (conj (@lem1612408 x y h1) (@lem1612387 x y h1)). Qed.
Lemma lem1612411 (x : real) (y : real) : term265 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1612412 (x : real) : term283 x.
Proof. exact (@lem1612411 (term153 x) x). Qed.
Lemma lem1612413 (x : real) (y : real) (h1 : term288 x y) : term284 x.
Proof. exact (@lem1612412 x (@lem1612409 x y h1)). Qed.
Lemma lem1612414 (x : real) : (term285 x) = (term286 x).
Proof. exact (@lem1483440 term113 x). Qed.
Lemma lem1612416 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1612417 : term115 = term6.
Proof. exact (@lem1612416 term64). Qed.
Lemma lem1612418 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1612419 : term116 = term15.
Proof. exact (MK_COMB (@lem1612418) (@lem1612417)). Qed.
Lemma lem1612420 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1612421 (x : real) : (term286 x) = (term14 x).
Proof. exact (MK_COMB (@lem1612419) (@lem1612420 x)). Qed.
Lemma lem1612422 (x : real) : (term285 x) = (term14 x).
Proof. exact (TRANS (@lem1612414 x) (@lem1612421 x)). Qed.
Lemma lem1612423 (x : real) : (term14 x) = term6.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1612424 (x : real) : (term285 x) = term6.
Proof. exact (TRANS (@lem1612422 x) (@lem1612423 x)). Qed.
Lemma lem1612425 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612426 (x : real) : (term287 x) = term119.
Proof. exact (MK_COMB (@lem1612425) (@lem1612424 x)). Qed.
Lemma lem1612427 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612428 (x : real) : (term284 x) = term120.
Proof. exact (MK_COMB (@lem1612426 x) (@lem1612427)). Qed.
Lemma lem1612429 (x : real) (y : real) (h1 : term288 x y) : term120.
Proof. exact (EQ_MP (@lem1612428 x) (@lem1612413 x y h1)). Qed.
Lemma lem1612431 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1612432 : term120 = term121.
Proof. exact (@lem1612431 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1612433 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1612434 : term120 = False.
Proof. exact (TRANS (@lem1612432) (@lem1612433)). Qed.
Lemma lem1612435 (x : real) (y : real) (h1 : term288 x y) : False.
Proof. exact (EQ_MP (@lem1612434) (@lem1612429 x y h1)). Qed.
Lemma lem1612436 (x : real) (y : real) (h1 : term249 x y) : False.
Proof. exact (or_elim (@lem1612277 x y h1) (fun h0 : term271 x y => @lem1612355 x y h0) (fun h0 : term288 x y => @lem1612435 x y h0)). Qed.
Lemma lem1612437 (x : real) (y : real) (h1 : term258 x y) : False.
Proof. exact (or_elim (@lem1612114 x y h1) (fun h0 : term253 x y => @lem1612276 x y h0) (fun h0 : term249 x y => @lem1612436 x y h0)). Qed.
Lemma lem1612439 (x : real) (y : real) (h1 : term258 x y) : term258 x y.
Proof. exact (h1). Qed.
Lemma lem1612440 (x : real) (y : real) (h1 : term258 x y) : (term258 x y) = False.
Proof. exact (prop_ext (fun h2 : term258 x y => @lem1612437 x y h1) (fun h2 : False => @lem1612439 x y h1)). Qed.
Lemma lem1612441 (x : real) (y : real) (h1 : term258 x y) : False.
Proof. exact (EQ_MP (@lem1612440 x y h1) (@lem1612439 x y h1)). Qed.
Lemma lem1612442 (x : real) (y : real) (h1 : term150 x y) : term150 x y.
Proof. exact (h1). Qed.
Lemma lem1612443 (x : real) (y : real) (h1 : term150 x y) : term258 x y.
Proof. exact (EQ_MP (@lem1612092 x y) (@lem1612442 x y h1)). Qed.
Lemma lem1612444 (x : real) (y : real) (h1 : term150 x y) : (term258 x y) = False.
Proof. exact (prop_ext (fun h2 : term258 x y => @lem1612441 x y h2) (fun h2 : False => @lem1612443 x y h1)). Qed.
Lemma lem1612445 (x : real) (y : real) (h1 : term150 x y) : False.
Proof. exact (EQ_MP (@lem1612444 x y h1) (@lem1612443 x y h1)). Qed.
Lemma lem1612446 (x : real) (y : real) : term289 x y.
Proof. exact (fun h0 : term150 x y => @lem1612445 x y h0). Qed.
Lemma lem1612447 (x : real) (y : real) : term290 x y.
Proof. exact (@lem1386578 (term291 x y)). Qed.
Lemma lem1612448 (x : real) (y : real) : term291 x y.
Proof. exact (@lem1612447 x y (@lem1612446 x y)). Qed.
Lemma lem1612477 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (@lem17045 (term24 x) (term24 y)). Qed.
Lemma lem1612482 (x : real) : (term127 x) = (term127 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem1612483 (x : real) (y : real) : (term292 x y) = (term293 x y).
Proof. exact (MK_COMB (@lem1612482 x) (@lem1612477 x y)). Qed.
Lemma lem1612484 (x : real) (y : real) : (term294 x y) = (term292 x y).
Proof. exact (@lem17160 (term8 x) (term26 x y)). Qed.
Lemma lem1612485 (x : real) (y : real) : (term294 x y) = (term293 x y).
Proof. exact (TRANS (@lem1612484 x y) (@lem1612483 x y)). Qed.
Lemma lem1612491 (x : real) (y : real) : (term295 x y) = (term295 x y).
Proof. exact (eq_refl (term295 x y)). Qed.
Lemma lem1612493 (x : real) (y : real) : (term85 x y) = (term85 x y).
Proof. exact (eq_refl (term85 x y)). Qed.
Lemma lem1612494 (x : real) (y : real) : (term296 x y) = (term297 x y).
Proof. exact (MK_COMB (@lem1612493 x y) (@lem1612485 x y)). Qed.
Lemma lem1612495 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1612496 (x : real) (y : real) : (term298 x y) = (term299 x y).
Proof. exact (MK_COMB (@lem1612495) (@lem1612494 x y)). Qed.
Lemma lem1612497 (x : real) (y : real) : (term300 x y) = (term301 x y).
Proof. exact (MK_COMB (@lem1612496 x y) (@lem1612491 x y)). Qed.
Lemma lem1612498 (x : real) (y : real) : (term302 x y) = (term300 x y).
Proof. exact (@lem17646 (term18 x y) (term39 x y)). Qed.
Lemma lem1612499 (x : real) (y : real) : (term302 x y) = (term301 x y).
Proof. exact (TRANS (@lem1612498 x y) (@lem1612497 x y)). Qed.
Lemma lem1612501 (y : real) (x : real) : (term303 y x) = (term303 y x).
Proof. exact (eq_refl (term303 y x)). Qed.
Lemma lem1612502 (x : real) (y : real) : (term304 x y) = (term305 x y).
Proof. exact (MK_COMB (@lem1612501 y x) (@lem1612499 x y)). Qed.
Lemma lem1612503 (x : real) (y : real) : (term306 x y) = (term304 x y).
Proof. exact (@lem17362 (term45 y x) ((term18 x y) = (term39 x y))). Qed.
Lemma lem1612504 (x : real) (y : real) : (term306 x y) = (term305 x y).
Proof. exact (TRANS (@lem1612503 x y) (@lem1612502 x y)). Qed.
Lemma lem1612506 (y : real) : (term21 y) = (term21 y).
Proof. exact (eq_refl (term21 y)). Qed.
Lemma lem1612507 (x : real) (y : real) : (term307 x y) = (term308 x y).
Proof. exact (MK_COMB (@lem1612506 y) (@lem1612504 x y)). Qed.
Lemma lem1612508 (x : real) (y : real) : (term309 x y) = (term307 x y).
Proof. exact (@lem17362 (term8 y) (term310 x y)). Qed.
Lemma lem1612509 (x : real) (y : real) : (term309 x y) = (term308 x y).
Proof. exact (TRANS (@lem1612508 x y) (@lem1612507 x y)). Qed.
Lemma lem1612511 (x : real) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem1612512 (x : real) (y : real) : (term311 x y) = (term312 x y).
Proof. exact (MK_COMB (@lem1612511 x) (@lem1612509 x y)). Qed.
Lemma lem1612513 (x : real) (y : real) : (term313 x y) = (term311 x y).
Proof. exact (@lem17362 (term9 x) (term314 x y)). Qed.
Lemma lem1612565 (x : real) (y : real) : (term313 x y) = (term312 x y).
Proof. exact (TRANS (@lem1612513 x y) (@lem1612512 x y)). Qed.
Lemma lem1612566 (x : real) : (term9 x) = (term152 x).
Proof. exact (@lem1483521 (real_neg x) term6). Qed.
Lemma lem1612567 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612574 (x : real) : (real_neg x) = (term153 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1612575 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1612576 (x : real) : (term154 x) = (term155 x).
Proof. exact (MK_COMB (@lem1612575) (@lem1612574 x)). Qed.
Lemma lem1612577 (x : real) : (term156 x) = (term157 x).
Proof. exact (MK_COMB (@lem1612576 x) (@lem1612567)). Qed.
Lemma lem1612578 (x : real) : (term157 x) = (term158 x).
Proof. exact (@lem1483519 (term153 x) term6). Qed.
Lemma lem1612580 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1612581 : term63 = term6.
Proof. exact (@lem1612580 term64). Qed.
Lemma lem1612582 (x : real) : (term159 x) = (term159 x).
Proof. exact (eq_refl (term159 x)). Qed.
Lemma lem1612583 (x : real) : (term158 x) = (term160 x).
Proof. exact (MK_COMB (@lem1612582 x) (@lem1612581)). Qed.
Lemma lem1612584 (x : real) : (term160 x) = (term153 x).
Proof. exact (@lem1483450 (term153 x)). Qed.
Lemma lem1612585 (x : real) : (term158 x) = (term153 x).
Proof. exact (TRANS (@lem1612583 x) (@lem1612584 x)). Qed.
Lemma lem1612586 (x : real) : (term157 x) = (term153 x).
Proof. exact (TRANS (@lem1612578 x) (@lem1612585 x)). Qed.
Lemma lem1612587 (x : real) : (term156 x) = (term153 x).
Proof. exact (TRANS (@lem1612577 x) (@lem1612586 x)). Qed.
Lemma lem1612588 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612589 (x : real) : (term161 x) = (term162 x).
Proof. exact (MK_COMB (@lem1612588) (@lem1612587 x)). Qed.
Lemma lem1612590 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612591 (x : real) : (term152 x) = (term163 x).
Proof. exact (MK_COMB (@lem1612589 x) (@lem1612590)). Qed.
Lemma lem1612592 (x : real) : (term9 x) = (term163 x).
Proof. exact (TRANS (@lem1612566 x) (@lem1612591 x)). Qed.
Lemma lem1612593 (y : real) : (term8 y) = (term59 y).
Proof. exact (@lem1483521 y term6). Qed.
Lemma lem1612599 (y : real) : (term60 y) = (term61 y).
Proof. exact (@lem1483519 y term6). Qed.
Lemma lem1612601 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1612602 : term63 = term6.
Proof. exact (@lem1612601 term64). Qed.
Lemma lem1612603 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1612604 (y : real) : (term61 y) = (term65 y).
Proof. exact (MK_COMB (@lem1612603 y) (@lem1612602)). Qed.
Lemma lem1612605 (y : real) : (term65 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1612606 (y : real) : (term61 y) = y.
Proof. exact (TRANS (@lem1612604 y) (@lem1612605 y)). Qed.
Lemma lem1612608 (y : real) : (term60 y) = y.
Proof. exact (TRANS (@lem1612599 y) (@lem1612606 y)). Qed.
Lemma lem1612609 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612610 (y : real) : (term66 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1612609) (@lem1612608 y)). Qed.
Lemma lem1612611 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612612 (y : real) : (term59 y) = (term67 y).
Proof. exact (MK_COMB (@lem1612610 y) (@lem1612611)). Qed.
Lemma lem1612613 (y : real) : (term8 y) = (term67 y).
Proof. exact (TRANS (@lem1612593 y) (@lem1612612 y)). Qed.
Lemma lem1612614 (y : real) (x : real) : (term45 y x) = (term315 y x).
Proof. exact (@lem1483521 (term316 y x) term6). Qed.
Lemma lem1612615 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612622 (x : real) : (real_neg x) = (term153 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1612625 (y : real) : (real_mul y) = (real_mul y).
Proof. exact (eq_refl (real_mul y)). Qed.
Lemma lem1612626 (y : real) (x : real) : (term316 y x) = (term317 y x).
Proof. exact (MK_COMB (@lem1612625 y) (@lem1612622 x)). Qed.
Lemma lem1612627 (y : real) (x : real) : (term317 y x) = (term81 y x).
Proof. exact (@lem1483478 term113 y x). Qed.
Lemma lem1612628 (x : real) (y : real) : (real_mul y x) = (real_mul x y).
Proof. exact (@lem1483474 x y). Qed.
Lemma lem1612629 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem1612630 (x : real) (y : real) : (term81 y x) = (term81 x y).
Proof. exact (MK_COMB (@lem1612629) (@lem1612628 x y)). Qed.
Lemma lem1612631 (x : real) (y : real) : (term317 y x) = (term81 x y).
Proof. exact (TRANS (@lem1612627 y x) (@lem1612630 x y)). Qed.
Lemma lem1612632 (x : real) (y : real) : (term316 y x) = (term81 x y).
Proof. exact (TRANS (@lem1612626 y x) (@lem1612631 x y)). Qed.
Lemma lem1612633 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1612634 (x : real) (y : real) : (term318 y x) = (term171 x y).
Proof. exact (MK_COMB (@lem1612633) (@lem1612632 x y)). Qed.
Lemma lem1612635 (x : real) (y : real) : (term319 y x) = (term173 x y).
Proof. exact (MK_COMB (@lem1612634 x y) (@lem1612615)). Qed.
Lemma lem1612636 (x : real) (y : real) : (term173 x y) = (term174 x y).
Proof. exact (@lem1483519 (term81 x y) term6). Qed.
Lemma lem1612638 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1612639 : term63 = term6.
Proof. exact (@lem1612638 term64). Qed.
Lemma lem1612640 (x : real) (y : real) : (term175 x y) = (term175 x y).
Proof. exact (eq_refl (term175 x y)). Qed.
Lemma lem1612641 (x : real) (y : real) : (term174 x y) = (term176 x y).
Proof. exact (MK_COMB (@lem1612640 x y) (@lem1612639)). Qed.
Lemma lem1612642 (x : real) (y : real) : (term176 x y) = (term81 x y).
Proof. exact (@lem1483450 (term81 x y)). Qed.
Lemma lem1612643 (x : real) (y : real) : (term174 x y) = (term81 x y).
Proof. exact (TRANS (@lem1612641 x y) (@lem1612642 x y)). Qed.
Lemma lem1612644 (x : real) (y : real) : (term173 x y) = (term81 x y).
Proof. exact (TRANS (@lem1612636 x y) (@lem1612643 x y)). Qed.
Lemma lem1612645 (x : real) (y : real) : (term319 y x) = (term81 x y).
Proof. exact (TRANS (@lem1612635 x y) (@lem1612644 x y)). Qed.
Lemma lem1612646 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612647 (x : real) (y : real) : (term320 y x) = (term178 x y).
Proof. exact (MK_COMB (@lem1612646) (@lem1612645 x y)). Qed.
Lemma lem1612648 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612649 (x : real) (y : real) : (term315 y x) = (term179 x y).
Proof. exact (MK_COMB (@lem1612647 x y) (@lem1612648)). Qed.
Lemma lem1612650 (x : real) (y : real) : (term45 y x) = (term179 x y).
Proof. exact (TRANS (@lem1612614 y x) (@lem1612649 x y)). Qed.
Lemma lem1612651 (x : real) (y : real) : (term18 x y) = (term68 x y).
Proof. exact (@lem1483521 (real_mul x y) term6). Qed.
Lemma lem1612663 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (@lem1483519 (real_mul x y) term6). Qed.
Lemma lem1612665 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1612666 : term63 = term6.
Proof. exact (@lem1612665 term64). Qed.
Lemma lem1612667 (x : real) (y : real) : (term72 x y) = (term72 x y).
Proof. exact (eq_refl (term72 x y)). Qed.
Lemma lem1612668 (x : real) (y : real) : (term71 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem1612667 x y) (@lem1612666)). Qed.
Lemma lem1612669 (x : real) (y : real) : (term73 x y) = (real_mul x y).
Proof. exact (@lem1483450 (real_mul x y)). Qed.
Lemma lem1612670 (x : real) (y : real) : (term71 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1612668 x y) (@lem1612669 x y)). Qed.
Lemma lem1612672 (x : real) (y : real) : (term70 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1612663 x y) (@lem1612670 x y)). Qed.
Lemma lem1612673 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612674 (x : real) (y : real) : (term74 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1612673) (@lem1612672 x y)). Qed.
Lemma lem1612675 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612676 (x : real) (y : real) : (term68 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1612674 x y) (@lem1612675)). Qed.
Lemma lem1612677 (x : real) (y : real) : (term18 x y) = (term76 x y).
Proof. exact (TRANS (@lem1612651 x y) (@lem1612676 x y)). Qed.
Lemma lem1612678 (x : real) : (term180 x) = (term181 x).
Proof. exact (@lem1483531 term6 x). Qed.
Lemma lem1612684 (x : real) : (term182 x) = (term183 x).
Proof. exact (@lem1483519 term6 x). Qed.
Lemma lem1612689 (x : real) : (term183 x) = (term153 x).
Proof. exact (@lem1483448 (term153 x)). Qed.
Lemma lem1612691 (x : real) : (term182 x) = (term153 x).
Proof. exact (TRANS (@lem1612684 x) (@lem1612689 x)). Qed.
Lemma lem1612692 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1612693 (x : real) : (term184 x) = (term185 x).
Proof. exact (MK_COMB (@lem1612692) (@lem1612691 x)). Qed.
Lemma lem1612694 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612695 (x : real) : (term181 x) = (term186 x).
Proof. exact (MK_COMB (@lem1612693 x) (@lem1612694)). Qed.
Lemma lem1612696 (x : real) : (term180 x) = (term186 x).
Proof. exact (TRANS (@lem1612678 x) (@lem1612695 x)). Qed.
Lemma lem1612697 (x : real) : (term187 x) = (term188 x).
Proof. exact (@lem1483531 x term6). Qed.
Lemma lem1612703 (x : real) : (term60 x) = (term61 x).
Proof. exact (@lem1483519 x term6). Qed.
Lemma lem1612705 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1612706 : term63 = term6.
Proof. exact (@lem1612705 term64). Qed.
Lemma lem1612707 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1612708 (x : real) : (term61 x) = (term65 x).
Proof. exact (MK_COMB (@lem1612707 x) (@lem1612706)). Qed.
Lemma lem1612709 (x : real) : (term65 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1612710 (x : real) : (term61 x) = x.
Proof. exact (TRANS (@lem1612708 x) (@lem1612709 x)). Qed.
Lemma lem1612712 (x : real) : (term60 x) = x.
Proof. exact (TRANS (@lem1612703 x) (@lem1612710 x)). Qed.
Lemma lem1612713 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1612714 (x : real) : (term189 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1612713) (@lem1612712 x)). Qed.
Lemma lem1612715 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612716 (x : real) : (term188 x) = (term190 x).
Proof. exact (MK_COMB (@lem1612714 x) (@lem1612715)). Qed.
Lemma lem1612717 (x : real) : (term187 x) = (term190 x).
Proof. exact (TRANS (@lem1612697 x) (@lem1612716 x)). Qed.
Lemma lem1612718 (y : real) : (term187 y) = (term188 y).
Proof. exact (@lem1483531 y term6). Qed.
Lemma lem1612724 (y : real) : (term60 y) = (term61 y).
Proof. exact (@lem1483519 y term6). Qed.
Lemma lem1612726 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1612727 : term63 = term6.
Proof. exact (@lem1612726 term64). Qed.
Lemma lem1612728 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1612729 (y : real) : (term61 y) = (term65 y).
Proof. exact (MK_COMB (@lem1612728 y) (@lem1612727)). Qed.
Lemma lem1612730 (y : real) : (term65 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1612731 (y : real) : (term61 y) = y.
Proof. exact (TRANS (@lem1612729 y) (@lem1612730 y)). Qed.
Lemma lem1612733 (y : real) : (term60 y) = y.
Proof. exact (TRANS (@lem1612724 y) (@lem1612731 y)). Qed.
Lemma lem1612734 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1612735 (y : real) : (term189 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1612734) (@lem1612733 y)). Qed.
Lemma lem1612736 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612737 (y : real) : (term188 y) = (term190 y).
Proof. exact (MK_COMB (@lem1612735 y) (@lem1612736)). Qed.
Lemma lem1612738 (y : real) : (term187 y) = (term190 y).
Proof. exact (TRANS (@lem1612718 y) (@lem1612737 y)). Qed.
Lemma lem1612739 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1612740 (x : real) : (term191 x) = (term192 x).
Proof. exact (MK_COMB (@lem1612739) (@lem1612717 x)). Qed.
Lemma lem1612741 (x : real) (y : real) : (term126 x y) = (term193 x y).
Proof. exact (MK_COMB (@lem1612740 x) (@lem1612738 y)). Qed.
Lemma lem1612742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1612743 (x : real) : (term127 x) = (term194 x).
Proof. exact (MK_COMB (@lem1612742) (@lem1612696 x)). Qed.
Lemma lem1612744 (x : real) (y : real) : (term293 x y) = (term321 x y).
Proof. exact (MK_COMB (@lem1612743 x) (@lem1612741 x y)). Qed.
Lemma lem1612745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1612746 (x : real) (y : real) : (term85 x y) = (term86 x y).
Proof. exact (MK_COMB (@lem1612745) (@lem1612677 x y)). Qed.
Lemma lem1612747 (x : real) (y : real) : (term297 x y) = (term322 x y).
Proof. exact (MK_COMB (@lem1612746 x y) (@lem1612744 x y)). Qed.
Lemma lem1612748 (x : real) (y : real) : (term77 x y) = (term78 x y).
Proof. exact (@lem1483531 term6 (real_mul x y)). Qed.
Lemma lem1612760 (x : real) (y : real) : (term79 x y) = (term80 x y).
Proof. exact (@lem1483519 term6 (real_mul x y)). Qed.
Lemma lem1612765 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (@lem1483448 (term81 x y)). Qed.
Lemma lem1612767 (x : real) (y : real) : (term79 x y) = (term81 x y).
Proof. exact (TRANS (@lem1612760 x y) (@lem1612765 x y)). Qed.
Lemma lem1612768 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1612769 (x : real) (y : real) : (term82 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1612768) (@lem1612767 x y)). Qed.
Lemma lem1612770 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612771 (x : real) (y : real) : (term78 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1612769 x y) (@lem1612770)). Qed.
Lemma lem1612772 (x : real) (y : real) : (term77 x y) = (term84 x y).
Proof. exact (TRANS (@lem1612748 x y) (@lem1612771 x y)). Qed.
Lemma lem1612773 (x : real) : (term8 x) = (term59 x).
Proof. exact (@lem1483521 x term6). Qed.
Lemma lem1612779 (x : real) : (term60 x) = (term61 x).
Proof. exact (@lem1483519 x term6). Qed.
Lemma lem1612781 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1612782 : term63 = term6.
Proof. exact (@lem1612781 term64). Qed.
Lemma lem1612783 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1612784 (x : real) : (term61 x) = (term65 x).
Proof. exact (MK_COMB (@lem1612783 x) (@lem1612782)). Qed.
Lemma lem1612785 (x : real) : (term65 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1612786 (x : real) : (term61 x) = x.
Proof. exact (TRANS (@lem1612784 x) (@lem1612785 x)). Qed.
Lemma lem1612788 (x : real) : (term60 x) = x.
Proof. exact (TRANS (@lem1612779 x) (@lem1612786 x)). Qed.
Lemma lem1612789 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612790 (x : real) : (term66 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1612789) (@lem1612788 x)). Qed.
Lemma lem1612791 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612792 (x : real) : (term59 x) = (term67 x).
Proof. exact (MK_COMB (@lem1612790 x) (@lem1612791)). Qed.
Lemma lem1612793 (x : real) : (term8 x) = (term67 x).
Proof. exact (TRANS (@lem1612773 x) (@lem1612792 x)). Qed.
Lemma lem1612794 (x : real) : (term24 x) = (term197 x).
Proof. exact (@lem1483521 term6 x). Qed.
Lemma lem1612800 (x : real) : (term182 x) = (term183 x).
Proof. exact (@lem1483519 term6 x). Qed.
Lemma lem1612805 (x : real) : (term183 x) = (term153 x).
Proof. exact (@lem1483448 (term153 x)). Qed.
Lemma lem1612807 (x : real) : (term182 x) = (term153 x).
Proof. exact (TRANS (@lem1612800 x) (@lem1612805 x)). Qed.
Lemma lem1612808 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612809 (x : real) : (term198 x) = (term162 x).
Proof. exact (MK_COMB (@lem1612808) (@lem1612807 x)). Qed.
Lemma lem1612810 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612811 (x : real) : (term197 x) = (term163 x).
Proof. exact (MK_COMB (@lem1612809 x) (@lem1612810)). Qed.
Lemma lem1612812 (x : real) : (term24 x) = (term163 x).
Proof. exact (TRANS (@lem1612794 x) (@lem1612811 x)). Qed.
Lemma lem1612813 (y : real) : (term24 y) = (term197 y).
Proof. exact (@lem1483521 term6 y). Qed.
Lemma lem1612819 (y : real) : (term182 y) = (term183 y).
Proof. exact (@lem1483519 term6 y). Qed.
Lemma lem1612824 (y : real) : (term183 y) = (term153 y).
Proof. exact (@lem1483448 (term153 y)). Qed.
Lemma lem1612826 (y : real) : (term182 y) = (term153 y).
Proof. exact (TRANS (@lem1612819 y) (@lem1612824 y)). Qed.
Lemma lem1612827 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1612828 (y : real) : (term198 y) = (term162 y).
Proof. exact (MK_COMB (@lem1612827) (@lem1612826 y)). Qed.
Lemma lem1612829 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1612830 (y : real) : (term197 y) = (term163 y).
Proof. exact (MK_COMB (@lem1612828 y) (@lem1612829)). Qed.
Lemma lem1612831 (y : real) : (term24 y) = (term163 y).
Proof. exact (TRANS (@lem1612813 y) (@lem1612830 y)). Qed.
Lemma lem1612832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1612833 (x : real) : (term25 x) = (term199 x).
Proof. exact (MK_COMB (@lem1612832) (@lem1612812 x)). Qed.
Lemma lem1612834 (x : real) (y : real) : (term26 x y) = (term200 x y).
Proof. exact (MK_COMB (@lem1612833 x) (@lem1612831 y)). Qed.
Lemma lem1612835 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1612836 (x : real) : (term35 x) = (term201 x).
Proof. exact (MK_COMB (@lem1612835) (@lem1612793 x)). Qed.
Lemma lem1612837 (x : real) (y : real) : (term39 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem1612836 x) (@lem1612834 x y)). Qed.
Lemma lem1612838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1612839 (x : real) (y : real) : (term203 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem1612838) (@lem1612772 x y)). Qed.
Lemma lem1612840 (x : real) (y : real) : (term295 x y) = (term324 x y).
Proof. exact (MK_COMB (@lem1612839 x y) (@lem1612837 x y)). Qed.
Lemma lem1612841 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1612842 (x : real) (y : real) : (term299 x y) = (term325 x y).
Proof. exact (MK_COMB (@lem1612841) (@lem1612747 x y)). Qed.
Lemma lem1612843 (x : real) (y : real) : (term301 x y) = (term326 x y).
Proof. exact (MK_COMB (@lem1612842 x y) (@lem1612840 x y)). Qed.
Lemma lem1612844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1612845 (x : real) (y : real) : (term303 y x) = (term208 x y).
Proof. exact (MK_COMB (@lem1612844) (@lem1612650 x y)). Qed.
Lemma lem1612846 (x : real) (y : real) : (term305 x y) = (term327 x y).
Proof. exact (MK_COMB (@lem1612845 x y) (@lem1612843 x y)). Qed.
Lemma lem1612847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1612848 (y : real) : (term21 y) = (term88 y).
Proof. exact (MK_COMB (@lem1612847) (@lem1612613 y)). Qed.
Lemma lem1612849 (x : real) (y : real) : (term308 x y) = (term328 x y).
Proof. exact (MK_COMB (@lem1612848 y) (@lem1612846 x y)). Qed.
Lemma lem1612850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1612851 (x : real) : (term143 x) = (term199 x).
Proof. exact (MK_COMB (@lem1612850) (@lem1612592 x)). Qed.
Lemma lem1612852 (x : real) (y : real) : (term312 x y) = (term329 x y).
Proof. exact (MK_COMB (@lem1612851 x) (@lem1612849 x y)). Qed.
Lemma lem1612859 (x : real) (y : real) : (term313 x y) = (term329 x y).
Proof. exact (TRANS (@lem1612565 x y) (@lem1612852 x y)). Qed.
Lemma lem1612882 (x : real) (y : real) : (term324 x y) = (term330 x y).
Proof. exact (@lem19158 (term67 x) (term84 x y) (term200 x y)). Qed.
Lemma lem1612899 (x : real) (y : real) : (term321 x y) = (term331 x y).
Proof. exact (@lem19158 (term190 x) (term186 x) (term190 y)). Qed.
Lemma lem1612902 (x : real) (y : real) : (term86 x y) = (term86 x y).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1612903 (x : real) (y : real) : (term322 x y) = (term332 x y).
Proof. exact (MK_COMB (@lem1612902 x y) (@lem1612899 x y)). Qed.
Lemma lem1612910 (x : real) (y : real) : (term332 x y) = (term333 x y).
Proof. exact (@lem19158 (term217 x) (term76 x y) (term216 x y)). Qed.
Lemma lem1612911 (x : real) (y : real) : (term322 x y) = (term333 x y).
Proof. exact (TRANS (@lem1612903 x y) (@lem1612910 x y)). Qed.
Lemma lem1612912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1612913 (x : real) (y : real) : (term325 x y) = (term334 x y).
Proof. exact (MK_COMB (@lem1612912) (@lem1612911 x y)). Qed.
Lemma lem1612914 (x : real) (y : real) : (term326 x y) = (term335 x y).
Proof. exact (MK_COMB (@lem1612913 x y) (@lem1612882 x y)). Qed.
Lemma lem1612917 (x : real) (y : real) : (term208 x y) = (term208 x y).
Proof. exact (eq_refl (term208 x y)). Qed.
Lemma lem1612918 (x : real) (y : real) : (term327 x y) = (term336 x y).
Proof. exact (MK_COMB (@lem1612917 x y) (@lem1612914 x y)). Qed.
Lemma lem1612919 (x : real) (y : real) : (term336 x y) = (term337 x y).
Proof. exact (@lem19158 (term333 x y) (term179 x y) (term330 x y)). Qed.
Lemma lem1612926 (x : real) (y : real) : (term338 x y) = (term339 x y).
Proof. exact (@lem19158 (term340 y x) (term179 x y) (term225 x y)). Qed.
Lemma lem1612933 (x : real) (y : real) : (term341 x y) = (term342 x y).
Proof. exact (@lem19158 (term343 y x) (term179 x y) (term344 x y)). Qed.
Lemma lem1612934 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1612935 (x : real) (y : real) : (term345 x y) = (term346 x y).
Proof. exact (MK_COMB (@lem1612934) (@lem1612933 x y)). Qed.
Lemma lem1612936 (x : real) (y : real) : (term337 x y) = (term347 x y).
Proof. exact (MK_COMB (@lem1612935 x y) (@lem1612926 x y)). Qed.
Lemma lem1612937 (x : real) (y : real) : (term336 x y) = (term347 x y).
Proof. exact (TRANS (@lem1612919 x y) (@lem1612936 x y)). Qed.
Lemma lem1612938 (x : real) (y : real) : (term327 x y) = (term347 x y).
Proof. exact (TRANS (@lem1612918 x y) (@lem1612937 x y)). Qed.
Lemma lem1612941 (y : real) : (term88 y) = (term88 y).
Proof. exact (eq_refl (term88 y)). Qed.
Lemma lem1612942 (x : real) (y : real) : (term328 x y) = (term348 x y).
Proof. exact (MK_COMB (@lem1612941 y) (@lem1612938 x y)). Qed.
Lemma lem1612943 (x : real) (y : real) : (term348 x y) = (term349 x y).
Proof. exact (@lem19158 (term342 x y) (term67 y) (term339 x y)). Qed.
Lemma lem1612950 (x : real) (y : real) : (term350 x y) = (term351 x y).
Proof. exact (@lem19158 (term352 y x) (term67 y) (term238 x y)). Qed.
Lemma lem1612957 (x : real) (y : real) : (term353 x y) = (term354 x y).
Proof. exact (@lem19158 (term355 y x) (term67 y) (term356 x y)). Qed.
Lemma lem1612958 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1612959 (x : real) (y : real) : (term357 x y) = (term358 x y).
Proof. exact (MK_COMB (@lem1612958) (@lem1612957 x y)). Qed.
Lemma lem1612960 (x : real) (y : real) : (term349 x y) = (term359 x y).
Proof. exact (MK_COMB (@lem1612959 x y) (@lem1612950 x y)). Qed.
Lemma lem1612961 (x : real) (y : real) : (term348 x y) = (term359 x y).
Proof. exact (TRANS (@lem1612943 x y) (@lem1612960 x y)). Qed.
Lemma lem1612962 (x : real) (y : real) : (term328 x y) = (term359 x y).
Proof. exact (TRANS (@lem1612942 x y) (@lem1612961 x y)). Qed.
Lemma lem1612965 (x : real) : (term199 x) = (term199 x).
Proof. exact (eq_refl (term199 x)). Qed.
Lemma lem1612966 (x : real) (y : real) : (term329 x y) = (term360 x y).
Proof. exact (MK_COMB (@lem1612965 x) (@lem1612962 x y)). Qed.
Lemma lem1612967 (x : real) (y : real) : (term360 x y) = (term361 x y).
Proof. exact (@lem19158 (term354 x y) (term163 x) (term351 x y)). Qed.
Lemma lem1612974 (x : real) (y : real) : (term362 x y) = (term363 x y).
Proof. exact (@lem19158 (term364 y x) (term163 x) (term365 x y)). Qed.
Lemma lem1612981 (x : real) (y : real) : (term366 x y) = (term367 x y).
Proof. exact (@lem19158 (term368 y x) (term163 x) (term369 x y)). Qed.
Lemma lem1612982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1612983 (x : real) (y : real) : (term370 x y) = (term371 x y).
Proof. exact (MK_COMB (@lem1612982) (@lem1612981 x y)). Qed.
Lemma lem1612984 (x : real) (y : real) : (term361 x y) = (term372 x y).
Proof. exact (MK_COMB (@lem1612983 x y) (@lem1612974 x y)). Qed.
Lemma lem1612985 (x : real) (y : real) : (term360 x y) = (term372 x y).
Proof. exact (TRANS (@lem1612967 x y) (@lem1612984 x y)). Qed.
Lemma lem1612986 (x : real) (y : real) : (term329 x y) = (term372 x y).
Proof. exact (TRANS (@lem1612966 x y) (@lem1612985 x y)). Qed.
Lemma lem1612987 (x : real) (y : real) : (term313 x y) = (term372 x y).
Proof. exact (TRANS (@lem1612859 x y) (@lem1612986 x y)). Qed.
Lemma lem1613009 (x : real) (y : real) (h1 : term372 x y) : term372 x y.
Proof. exact (h1). Qed.
Lemma lem1613010 (x : real) (y : real) (h1 : term367 x y) : term367 x y.
Proof. exact (h1). Qed.
Lemma lem1613011 (y : real) (x : real) (h1 : term373 y x) : term373 y x.
Proof. exact (h1). Qed.
Lemma lem1613012 (y : real) (x : real) (h1 : term373 y x) : term368 y x.
Proof. exact (proj2 (@lem1613011 y x h1)). Qed.
Lemma lem1613014 (y : real) (x : real) (h1 : term373 y x) : term355 y x.
Proof. exact (proj2 (@lem1613012 y x h1)). Qed.
Lemma lem1613016 (y : real) (x : real) (h1 : term373 y x) : term343 y x.
Proof. exact (proj2 (@lem1613014 y x h1)). Qed.
Lemma lem1613017 (y : real) (x : real) (h1 : term373 y x) : term179 x y.
Proof. exact (proj1 (@lem1613014 y x h1)). Qed.
Lemma lem1613019 (y : real) (x : real) (h1 : term373 y x) : term76 x y.
Proof. exact (proj1 (@lem1613016 y x h1)). Qed.
Lemma lem1613023 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1613024 : term92 = term93.
Proof. exact (@lem1613023 (NUMERAL 0) term64). Qed.
Lemma lem1613025 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1613026 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1613027 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1613026 h1) (fun h1 : term93 = True => @lem1613025)). Qed.
Lemma lem1613028 : term93 = True.
Proof. exact (EQ_MP (@lem1613027) (@lem1613025)). Qed.
Lemma lem1613029 : term92 = True.
Proof. exact (TRANS (@lem1613024) (@lem1613028)). Qed.
Lemma lem1613030 : True = term92.
Proof. exact (SYM (@lem1613029)). Qed.
Lemma lem1613031 : term92.
Proof. exact (EQ_MP (@lem1613030) (@lem0)). Qed.
Lemma lem1613032 (y : real) (x : real) (h1 : term373 y x) : term102 x y.
Proof. exact (conj (@lem1613031) (@lem1613019 y x h1)). Qed.
Lemma lem1613034 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1613035 (x : real) (y : real) : term104 x y.
Proof. exact (@lem1613034 term98 (real_mul x y)). Qed.
Lemma lem1613036 (y : real) (x : real) (h1 : term373 y x) : term105 x y.
Proof. exact (@lem1613035 x y (@lem1613032 y x h1)). Qed.
Lemma lem1613037 (x : real) (y : real) : (term106 x y) = (real_mul x y).
Proof. exact (@lem1483460 (real_mul x y)). Qed.
Lemma lem1613038 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613039 (x : real) (y : real) : (term107 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1613038) (@lem1613037 x y)). Qed.
Lemma lem1613040 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613041 (x : real) (y : real) : (term105 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1613039 x y) (@lem1613040)). Qed.
Lemma lem1613042 (y : real) (x : real) (h1 : term373 y x) : term76 x y.
Proof. exact (EQ_MP (@lem1613041 x y) (@lem1613036 y x h1)). Qed.
Lemma lem1613044 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1613045 : term92 = term93.
Proof. exact (@lem1613044 (NUMERAL 0) term64). Qed.
Lemma lem1613046 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1613047 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1613048 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1613047 h1) (fun h1 : term93 = True => @lem1613046)). Qed.
Lemma lem1613049 : term93 = True.
Proof. exact (EQ_MP (@lem1613048) (@lem1613046)). Qed.
Lemma lem1613050 : term92 = True.
Proof. exact (TRANS (@lem1613045) (@lem1613049)). Qed.
Lemma lem1613051 : True = term92.
Proof. exact (SYM (@lem1613050)). Qed.
Lemma lem1613052 : term92.
Proof. exact (EQ_MP (@lem1613051) (@lem0)). Qed.
Lemma lem1613053 (y : real) (x : real) (h1 : term373 y x) : term260 x y.
Proof. exact (conj (@lem1613052) (@lem1613017 y x h1)). Qed.
Lemma lem1613055 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1613056 (x : real) (y : real) : term261 x y.
Proof. exact (@lem1613055 term98 (term81 x y)). Qed.
Lemma lem1613057 (y : real) (x : real) (h1 : term373 y x) : term262 x y.
Proof. exact (@lem1613056 x y (@lem1613053 y x h1)). Qed.
Lemma lem1613058 (x : real) (y : real) : (term100 x y) = (term81 x y).
Proof. exact (@lem1483460 (term81 x y)). Qed.
Lemma lem1613059 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613060 (x : real) (y : real) : (term263 x y) = (term178 x y).
Proof. exact (MK_COMB (@lem1613059) (@lem1613058 x y)). Qed.
Lemma lem1613061 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613062 (x : real) (y : real) : (term262 x y) = (term179 x y).
Proof. exact (MK_COMB (@lem1613060 x y) (@lem1613061)). Qed.
Lemma lem1613063 (y : real) (x : real) (h1 : term373 y x) : term179 x y.
Proof. exact (EQ_MP (@lem1613062 x y) (@lem1613057 y x h1)). Qed.
Lemma lem1613064 (y : real) (x : real) (h1 : term373 y x) : term264 x y.
Proof. exact (conj (@lem1613063 y x h1) (@lem1613042 y x h1)). Qed.
Lemma lem1613066 (x : real) (y : real) : term265 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1613067 (x : real) (y : real) : term266 x y.
Proof. exact (@lem1613066 (term81 x y) (real_mul x y)). Qed.
Lemma lem1613068 (y : real) (x : real) (h1 : term373 y x) : term267 x y.
Proof. exact (@lem1613067 x y (@lem1613064 y x h1)). Qed.
Lemma lem1613069 (x : real) (y : real) : (term268 x y) = (term112 x y).
Proof. exact (@lem1483440 term113 (real_mul x y)). Qed.
Lemma lem1613071 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1613072 : term115 = term6.
Proof. exact (@lem1613071 term64). Qed.
Lemma lem1613073 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1613074 : term116 = term15.
Proof. exact (MK_COMB (@lem1613073) (@lem1613072)). Qed.
Lemma lem1613075 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1613076 (x : real) (y : real) : (term112 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem1613074) (@lem1613075 x y)). Qed.
Lemma lem1613077 (x : real) (y : real) : (term268 x y) = (term117 x y).
Proof. exact (TRANS (@lem1613069 x y) (@lem1613076 x y)). Qed.
Lemma lem1613078 (x : real) (y : real) : (term117 x y) = term6.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1613079 (x : real) (y : real) : (term268 x y) = term6.
Proof. exact (TRANS (@lem1613077 x y) (@lem1613078 x y)). Qed.
Lemma lem1613080 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613081 (x : real) (y : real) : (term269 x y) = term119.
Proof. exact (MK_COMB (@lem1613080) (@lem1613079 x y)). Qed.
Lemma lem1613082 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613083 (x : real) (y : real) : (term267 x y) = term120.
Proof. exact (MK_COMB (@lem1613081 x y) (@lem1613082)). Qed.
Lemma lem1613084 (y : real) (x : real) (h1 : term373 y x) : term120.
Proof. exact (EQ_MP (@lem1613083 x y) (@lem1613068 y x h1)). Qed.
Lemma lem1613086 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1613087 : term120 = term121.
Proof. exact (@lem1613086 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1613088 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1613089 : term120 = False.
Proof. exact (TRANS (@lem1613087) (@lem1613088)). Qed.
Lemma lem1613090 (y : real) (x : real) (h1 : term373 y x) : False.
Proof. exact (EQ_MP (@lem1613089) (@lem1613084 y x h1)). Qed.
Lemma lem1613091 (x : real) (y : real) (h1 : term374 x y) : term374 x y.
Proof. exact (h1). Qed.
Lemma lem1613092 (x : real) (y : real) (h1 : term374 x y) : term369 x y.
Proof. exact (proj2 (@lem1613091 x y h1)). Qed.
Lemma lem1613094 (x : real) (y : real) (h1 : term374 x y) : term356 x y.
Proof. exact (proj2 (@lem1613092 x y h1)). Qed.
Lemma lem1613096 (x : real) (y : real) (h1 : term374 x y) : term344 x y.
Proof. exact (proj2 (@lem1613094 x y h1)). Qed.
Lemma lem1613097 (x : real) (y : real) (h1 : term374 x y) : term179 x y.
Proof. exact (proj1 (@lem1613094 x y h1)). Qed.
Lemma lem1613099 (x : real) (y : real) (h1 : term374 x y) : term76 x y.
Proof. exact (proj1 (@lem1613096 x y h1)). Qed.
Lemma lem1613103 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1613104 : term92 = term93.
Proof. exact (@lem1613103 (NUMERAL 0) term64). Qed.
Lemma lem1613105 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1613106 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1613107 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1613106 h1) (fun h1 : term93 = True => @lem1613105)). Qed.
Lemma lem1613108 : term93 = True.
Proof. exact (EQ_MP (@lem1613107) (@lem1613105)). Qed.
Lemma lem1613109 : term92 = True.
Proof. exact (TRANS (@lem1613104) (@lem1613108)). Qed.
Lemma lem1613110 : True = term92.
Proof. exact (SYM (@lem1613109)). Qed.
Lemma lem1613111 : term92.
Proof. exact (EQ_MP (@lem1613110) (@lem0)). Qed.
Lemma lem1613112 (x : real) (y : real) (h1 : term374 x y) : term102 x y.
Proof. exact (conj (@lem1613111) (@lem1613099 x y h1)). Qed.
Lemma lem1613114 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1613115 (x : real) (y : real) : term104 x y.
Proof. exact (@lem1613114 term98 (real_mul x y)). Qed.
Lemma lem1613116 (x : real) (y : real) (h1 : term374 x y) : term105 x y.
Proof. exact (@lem1613115 x y (@lem1613112 x y h1)). Qed.
Lemma lem1613117 (x : real) (y : real) : (term106 x y) = (real_mul x y).
Proof. exact (@lem1483460 (real_mul x y)). Qed.
Lemma lem1613118 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613119 (x : real) (y : real) : (term107 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1613118) (@lem1613117 x y)). Qed.
Lemma lem1613120 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613121 (x : real) (y : real) : (term105 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1613119 x y) (@lem1613120)). Qed.
Lemma lem1613122 (x : real) (y : real) (h1 : term374 x y) : term76 x y.
Proof. exact (EQ_MP (@lem1613121 x y) (@lem1613116 x y h1)). Qed.
Lemma lem1613124 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1613125 : term92 = term93.
Proof. exact (@lem1613124 (NUMERAL 0) term64). Qed.
Lemma lem1613126 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1613127 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1613128 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1613127 h1) (fun h1 : term93 = True => @lem1613126)). Qed.
Lemma lem1613129 : term93 = True.
Proof. exact (EQ_MP (@lem1613128) (@lem1613126)). Qed.
Lemma lem1613130 : term92 = True.
Proof. exact (TRANS (@lem1613125) (@lem1613129)). Qed.
Lemma lem1613131 : True = term92.
Proof. exact (SYM (@lem1613130)). Qed.
Lemma lem1613132 : term92.
Proof. exact (EQ_MP (@lem1613131) (@lem0)). Qed.
Lemma lem1613133 (x : real) (y : real) (h1 : term374 x y) : term260 x y.
Proof. exact (conj (@lem1613132) (@lem1613097 x y h1)). Qed.
Lemma lem1613135 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1613136 (x : real) (y : real) : term261 x y.
Proof. exact (@lem1613135 term98 (term81 x y)). Qed.
Lemma lem1613137 (x : real) (y : real) (h1 : term374 x y) : term262 x y.
Proof. exact (@lem1613136 x y (@lem1613133 x y h1)). Qed.
Lemma lem1613138 (x : real) (y : real) : (term100 x y) = (term81 x y).
Proof. exact (@lem1483460 (term81 x y)). Qed.
Lemma lem1613139 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613140 (x : real) (y : real) : (term263 x y) = (term178 x y).
Proof. exact (MK_COMB (@lem1613139) (@lem1613138 x y)). Qed.
Lemma lem1613141 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613142 (x : real) (y : real) : (term262 x y) = (term179 x y).
Proof. exact (MK_COMB (@lem1613140 x y) (@lem1613141)). Qed.
Lemma lem1613143 (x : real) (y : real) (h1 : term374 x y) : term179 x y.
Proof. exact (EQ_MP (@lem1613142 x y) (@lem1613137 x y h1)). Qed.
Lemma lem1613144 (x : real) (y : real) (h1 : term374 x y) : term264 x y.
Proof. exact (conj (@lem1613143 x y h1) (@lem1613122 x y h1)). Qed.
Lemma lem1613146 (x : real) (y : real) : term265 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1613147 (x : real) (y : real) : term266 x y.
Proof. exact (@lem1613146 (term81 x y) (real_mul x y)). Qed.
Lemma lem1613148 (x : real) (y : real) (h1 : term374 x y) : term267 x y.
Proof. exact (@lem1613147 x y (@lem1613144 x y h1)). Qed.
Lemma lem1613149 (x : real) (y : real) : (term268 x y) = (term112 x y).
Proof. exact (@lem1483440 term113 (real_mul x y)). Qed.
Lemma lem1613151 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1613152 : term115 = term6.
Proof. exact (@lem1613151 term64). Qed.
Lemma lem1613153 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1613154 : term116 = term15.
Proof. exact (MK_COMB (@lem1613153) (@lem1613152)). Qed.
Lemma lem1613155 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1613156 (x : real) (y : real) : (term112 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem1613154) (@lem1613155 x y)). Qed.
Lemma lem1613157 (x : real) (y : real) : (term268 x y) = (term117 x y).
Proof. exact (TRANS (@lem1613149 x y) (@lem1613156 x y)). Qed.
Lemma lem1613158 (x : real) (y : real) : (term117 x y) = term6.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1613159 (x : real) (y : real) : (term268 x y) = term6.
Proof. exact (TRANS (@lem1613157 x y) (@lem1613158 x y)). Qed.
Lemma lem1613160 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613161 (x : real) (y : real) : (term269 x y) = term119.
Proof. exact (MK_COMB (@lem1613160) (@lem1613159 x y)). Qed.
Lemma lem1613162 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613163 (x : real) (y : real) : (term267 x y) = term120.
Proof. exact (MK_COMB (@lem1613161 x y) (@lem1613162)). Qed.
Lemma lem1613164 (x : real) (y : real) (h1 : term374 x y) : term120.
Proof. exact (EQ_MP (@lem1613163 x y) (@lem1613148 x y h1)). Qed.
Lemma lem1613166 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1613167 : term120 = term121.
Proof. exact (@lem1613166 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1613168 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1613169 : term120 = False.
Proof. exact (TRANS (@lem1613167) (@lem1613168)). Qed.
Lemma lem1613170 (x : real) (y : real) (h1 : term374 x y) : False.
Proof. exact (EQ_MP (@lem1613169) (@lem1613164 x y h1)). Qed.
Lemma lem1613171 (x : real) (y : real) (h1 : term367 x y) : False.
Proof. exact (or_elim (@lem1613010 x y h1) (fun h0 : term373 y x => @lem1613090 y x h0) (fun h0 : term374 x y => @lem1613170 x y h0)). Qed.
Lemma lem1613172 (x : real) (y : real) (h1 : term363 x y) : term363 x y.
Proof. exact (h1). Qed.
Lemma lem1613173 (y : real) (x : real) (h1 : term375 y x) : term375 y x.
Proof. exact (h1). Qed.
Lemma lem1613174 (y : real) (x : real) (h1 : term375 y x) : term364 y x.
Proof. exact (proj2 (@lem1613173 y x h1)). Qed.
Lemma lem1613175 (y : real) (x : real) (h1 : term375 y x) : term163 x.
Proof. exact (proj1 (@lem1613173 y x h1)). Qed.
Lemma lem1613176 (y : real) (x : real) (h1 : term375 y x) : term352 y x.
Proof. exact (proj2 (@lem1613174 y x h1)). Qed.
Lemma lem1613178 (y : real) (x : real) (h1 : term375 y x) : term340 y x.
Proof. exact (proj2 (@lem1613176 y x h1)). Qed.
Lemma lem1613180 (y : real) (x : real) (h1 : term375 y x) : term67 x.
Proof. exact (proj2 (@lem1613178 y x h1)). Qed.
Lemma lem1613183 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1613184 : term92 = term93.
Proof. exact (@lem1613183 (NUMERAL 0) term64). Qed.
Lemma lem1613185 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1613186 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1613187 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1613186 h1) (fun h1 : term93 = True => @lem1613185)). Qed.
Lemma lem1613188 : term93 = True.
Proof. exact (EQ_MP (@lem1613187) (@lem1613185)). Qed.
Lemma lem1613189 : term92 = True.
Proof. exact (TRANS (@lem1613184) (@lem1613188)). Qed.
Lemma lem1613190 : True = term92.
Proof. exact (SYM (@lem1613189)). Qed.
Lemma lem1613191 : term92.
Proof. exact (EQ_MP (@lem1613190) (@lem0)). Qed.
Lemma lem1613192 (y : real) (x : real) (h1 : term375 y x) : term272 x.
Proof. exact (conj (@lem1613191) (@lem1613180 y x h1)). Qed.
Lemma lem1613194 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1613195 (x : real) : term273 x.
Proof. exact (@lem1613194 term98 x). Qed.
Lemma lem1613196 (y : real) (x : real) (h1 : term375 y x) : term274 x.
Proof. exact (@lem1613195 x (@lem1613192 y x h1)). Qed.
Lemma lem1613197 (x : real) : (term275 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1613198 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613199 (x : real) : (term276 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1613198) (@lem1613197 x)). Qed.
Lemma lem1613200 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613201 (x : real) : (term274 x) = (term67 x).
Proof. exact (MK_COMB (@lem1613199 x) (@lem1613200)). Qed.
Lemma lem1613202 (y : real) (x : real) (h1 : term375 y x) : term67 x.
Proof. exact (EQ_MP (@lem1613201 x) (@lem1613196 y x h1)). Qed.
Lemma lem1613204 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1613205 : term92 = term93.
Proof. exact (@lem1613204 (NUMERAL 0) term64). Qed.
Lemma lem1613206 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1613207 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1613208 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1613207 h1) (fun h1 : term93 = True => @lem1613206)). Qed.
Lemma lem1613209 : term93 = True.
Proof. exact (EQ_MP (@lem1613208) (@lem1613206)). Qed.
Lemma lem1613210 : term92 = True.
Proof. exact (TRANS (@lem1613205) (@lem1613209)). Qed.
Lemma lem1613211 : True = term92.
Proof. exact (SYM (@lem1613210)). Qed.
Lemma lem1613212 : term92.
Proof. exact (EQ_MP (@lem1613211) (@lem0)). Qed.
Lemma lem1613213 (y : real) (x : real) (h1 : term375 y x) : term277 x.
Proof. exact (conj (@lem1613212) (@lem1613175 y x h1)). Qed.
Lemma lem1613215 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1613216 (x : real) : term278 x.
Proof. exact (@lem1613215 term98 (term153 x)). Qed.
Lemma lem1613217 (y : real) (x : real) (h1 : term375 y x) : term279 x.
Proof. exact (@lem1613216 x (@lem1613213 y x h1)). Qed.
Lemma lem1613218 (x : real) : (term280 x) = (term153 x).
Proof. exact (@lem1483460 (term153 x)). Qed.
Lemma lem1613219 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613220 (x : real) : (term281 x) = (term162 x).
Proof. exact (MK_COMB (@lem1613219) (@lem1613218 x)). Qed.
Lemma lem1613221 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613222 (x : real) : (term279 x) = (term163 x).
Proof. exact (MK_COMB (@lem1613220 x) (@lem1613221)). Qed.
Lemma lem1613223 (y : real) (x : real) (h1 : term375 y x) : term163 x.
Proof. exact (EQ_MP (@lem1613222 x) (@lem1613217 y x h1)). Qed.
Lemma lem1613224 (y : real) (x : real) (h1 : term375 y x) : term282 x.
Proof. exact (conj (@lem1613223 y x h1) (@lem1613202 y x h1)). Qed.
Lemma lem1613226 (x : real) (y : real) : term265 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1613227 (x : real) : term283 x.
Proof. exact (@lem1613226 (term153 x) x). Qed.
Lemma lem1613228 (y : real) (x : real) (h1 : term375 y x) : term284 x.
Proof. exact (@lem1613227 x (@lem1613224 y x h1)). Qed.
Lemma lem1613229 (x : real) : (term285 x) = (term286 x).
Proof. exact (@lem1483440 term113 x). Qed.
Lemma lem1613231 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1613232 : term115 = term6.
Proof. exact (@lem1613231 term64). Qed.
Lemma lem1613233 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1613234 : term116 = term15.
Proof. exact (MK_COMB (@lem1613233) (@lem1613232)). Qed.
Lemma lem1613235 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1613236 (x : real) : (term286 x) = (term14 x).
Proof. exact (MK_COMB (@lem1613234) (@lem1613235 x)). Qed.
Lemma lem1613237 (x : real) : (term285 x) = (term14 x).
Proof. exact (TRANS (@lem1613229 x) (@lem1613236 x)). Qed.
Lemma lem1613238 (x : real) : (term14 x) = term6.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1613239 (x : real) : (term285 x) = term6.
Proof. exact (TRANS (@lem1613237 x) (@lem1613238 x)). Qed.
Lemma lem1613240 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613241 (x : real) : (term287 x) = term119.
Proof. exact (MK_COMB (@lem1613240) (@lem1613239 x)). Qed.
Lemma lem1613242 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613243 (x : real) : (term284 x) = term120.
Proof. exact (MK_COMB (@lem1613241 x) (@lem1613242)). Qed.
Lemma lem1613244 (y : real) (x : real) (h1 : term375 y x) : term120.
Proof. exact (EQ_MP (@lem1613243 x) (@lem1613228 y x h1)). Qed.
Lemma lem1613246 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1613247 : term120 = term121.
Proof. exact (@lem1613246 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1613248 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1613249 : term120 = False.
Proof. exact (TRANS (@lem1613247) (@lem1613248)). Qed.
Lemma lem1613250 (y : real) (x : real) (h1 : term375 y x) : False.
Proof. exact (EQ_MP (@lem1613249) (@lem1613244 y x h1)). Qed.
Lemma lem1613251 (x : real) (y : real) (h1 : term376 x y) : term376 x y.
Proof. exact (h1). Qed.
Lemma lem1613252 (x : real) (y : real) (h1 : term376 x y) : term365 x y.
Proof. exact (proj2 (@lem1613251 x y h1)). Qed.
Lemma lem1613254 (x : real) (y : real) (h1 : term376 x y) : term238 x y.
Proof. exact (proj2 (@lem1613252 x y h1)). Qed.
Lemma lem1613255 (x : real) (y : real) (h1 : term376 x y) : term67 y.
Proof. exact (proj1 (@lem1613252 x y h1)). Qed.
Lemma lem1613256 (x : real) (y : real) (h1 : term376 x y) : term225 x y.
Proof. exact (proj2 (@lem1613254 x y h1)). Qed.
Lemma lem1613258 (x : real) (y : real) (h1 : term376 x y) : term200 x y.
Proof. exact (proj2 (@lem1613256 x y h1)). Qed.
Lemma lem1613260 (x : real) (y : real) (h1 : term376 x y) : term163 y.
Proof. exact (proj2 (@lem1613258 x y h1)). Qed.
Lemma lem1613263 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1613264 : term92 = term93.
Proof. exact (@lem1613263 (NUMERAL 0) term64). Qed.
Lemma lem1613265 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1613266 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1613267 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1613266 h1) (fun h1 : term93 = True => @lem1613265)). Qed.
Lemma lem1613268 : term93 = True.
Proof. exact (EQ_MP (@lem1613267) (@lem1613265)). Qed.
Lemma lem1613269 : term92 = True.
Proof. exact (TRANS (@lem1613264) (@lem1613268)). Qed.
Lemma lem1613270 : True = term92.
Proof. exact (SYM (@lem1613269)). Qed.
Lemma lem1613271 : term92.
Proof. exact (EQ_MP (@lem1613270) (@lem0)). Qed.
Lemma lem1613272 (x : real) (y : real) (h1 : term376 x y) : term272 y.
Proof. exact (conj (@lem1613271) (@lem1613255 x y h1)). Qed.
Lemma lem1613274 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1613275 (y : real) : term273 y.
Proof. exact (@lem1613274 term98 y). Qed.
Lemma lem1613276 (x : real) (y : real) (h1 : term376 x y) : term274 y.
Proof. exact (@lem1613275 y (@lem1613272 x y h1)). Qed.
Lemma lem1613277 (y : real) : (term275 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1613278 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613279 (y : real) : (term276 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1613278) (@lem1613277 y)). Qed.
Lemma lem1613280 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613281 (y : real) : (term274 y) = (term67 y).
Proof. exact (MK_COMB (@lem1613279 y) (@lem1613280)). Qed.
Lemma lem1613282 (x : real) (y : real) (h1 : term376 x y) : term67 y.
Proof. exact (EQ_MP (@lem1613281 y) (@lem1613276 x y h1)). Qed.
Lemma lem1613284 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1613285 : term92 = term93.
Proof. exact (@lem1613284 (NUMERAL 0) term64). Qed.
Lemma lem1613286 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1613287 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1613288 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1613287 h1) (fun h1 : term93 = True => @lem1613286)). Qed.
Lemma lem1613289 : term93 = True.
Proof. exact (EQ_MP (@lem1613288) (@lem1613286)). Qed.
Lemma lem1613290 : term92 = True.
Proof. exact (TRANS (@lem1613285) (@lem1613289)). Qed.
Lemma lem1613291 : True = term92.
Proof. exact (SYM (@lem1613290)). Qed.
Lemma lem1613292 : term92.
Proof. exact (EQ_MP (@lem1613291) (@lem0)). Qed.
Lemma lem1613293 (x : real) (y : real) (h1 : term376 x y) : term277 y.
Proof. exact (conj (@lem1613292) (@lem1613260 x y h1)). Qed.
Lemma lem1613295 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1613296 (y : real) : term278 y.
Proof. exact (@lem1613295 term98 (term153 y)). Qed.
Lemma lem1613297 (x : real) (y : real) (h1 : term376 x y) : term279 y.
Proof. exact (@lem1613296 y (@lem1613293 x y h1)). Qed.
Lemma lem1613298 (y : real) : (term280 y) = (term153 y).
Proof. exact (@lem1483460 (term153 y)). Qed.
Lemma lem1613299 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613300 (y : real) : (term281 y) = (term162 y).
Proof. exact (MK_COMB (@lem1613299) (@lem1613298 y)). Qed.
Lemma lem1613301 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613302 (y : real) : (term279 y) = (term163 y).
Proof. exact (MK_COMB (@lem1613300 y) (@lem1613301)). Qed.
Lemma lem1613303 (x : real) (y : real) (h1 : term376 x y) : term163 y.
Proof. exact (EQ_MP (@lem1613302 y) (@lem1613297 x y h1)). Qed.
Lemma lem1613304 (x : real) (y : real) (h1 : term376 x y) : term282 y.
Proof. exact (conj (@lem1613303 x y h1) (@lem1613282 x y h1)). Qed.
Lemma lem1613306 (x : real) (y : real) : term265 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1613307 (y : real) : term283 y.
Proof. exact (@lem1613306 (term153 y) y). Qed.
Lemma lem1613308 (x : real) (y : real) (h1 : term376 x y) : term284 y.
Proof. exact (@lem1613307 y (@lem1613304 x y h1)). Qed.
Lemma lem1613309 (y : real) : (term285 y) = (term286 y).
Proof. exact (@lem1483440 term113 y). Qed.
Lemma lem1613311 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1613312 : term115 = term6.
Proof. exact (@lem1613311 term64). Qed.
Lemma lem1613313 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1613314 : term116 = term15.
Proof. exact (MK_COMB (@lem1613313) (@lem1613312)). Qed.
Lemma lem1613315 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1613316 (y : real) : (term286 y) = (term14 y).
Proof. exact (MK_COMB (@lem1613314) (@lem1613315 y)). Qed.
Lemma lem1613317 (y : real) : (term285 y) = (term14 y).
Proof. exact (TRANS (@lem1613309 y) (@lem1613316 y)). Qed.
Lemma lem1613318 (y : real) : (term14 y) = term6.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1613319 (y : real) : (term285 y) = term6.
Proof. exact (TRANS (@lem1613317 y) (@lem1613318 y)). Qed.
Lemma lem1613320 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613321 (y : real) : (term287 y) = term119.
Proof. exact (MK_COMB (@lem1613320) (@lem1613319 y)). Qed.
Lemma lem1613322 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613323 (y : real) : (term284 y) = term120.
Proof. exact (MK_COMB (@lem1613321 y) (@lem1613322)). Qed.
Lemma lem1613324 (x : real) (y : real) (h1 : term376 x y) : term120.
Proof. exact (EQ_MP (@lem1613323 y) (@lem1613308 x y h1)). Qed.
Lemma lem1613326 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1613327 : term120 = term121.
Proof. exact (@lem1613326 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1613328 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1613329 : term120 = False.
Proof. exact (TRANS (@lem1613327) (@lem1613328)). Qed.
Lemma lem1613330 (x : real) (y : real) (h1 : term376 x y) : False.
Proof. exact (EQ_MP (@lem1613329) (@lem1613324 x y h1)). Qed.
Lemma lem1613331 (x : real) (y : real) (h1 : term363 x y) : False.
Proof. exact (or_elim (@lem1613172 x y h1) (fun h0 : term375 y x => @lem1613250 y x h0) (fun h0 : term376 x y => @lem1613330 x y h0)). Qed.
Lemma lem1613332 (x : real) (y : real) (h1 : term372 x y) : False.
Proof. exact (or_elim (@lem1613009 x y h1) (fun h0 : term367 x y => @lem1613171 x y h0) (fun h0 : term363 x y => @lem1613331 x y h0)). Qed.
Lemma lem1613334 (x : real) (y : real) (h1 : term372 x y) : term372 x y.
Proof. exact (h1). Qed.
Lemma lem1613335 (x : real) (y : real) (h1 : term372 x y) : (term372 x y) = False.
Proof. exact (prop_ext (fun h2 : term372 x y => @lem1613332 x y h1) (fun h2 : False => @lem1613334 x y h1)). Qed.
Lemma lem1613336 (x : real) (y : real) (h1 : term372 x y) : False.
Proof. exact (EQ_MP (@lem1613335 x y h1) (@lem1613334 x y h1)). Qed.
Lemma lem1613337 (x : real) (y : real) (h1 : term313 x y) : term313 x y.
Proof. exact (h1). Qed.
Lemma lem1613338 (x : real) (y : real) (h1 : term313 x y) : term372 x y.
Proof. exact (EQ_MP (@lem1612987 x y) (@lem1613337 x y h1)). Qed.
Lemma lem1613339 (x : real) (y : real) (h1 : term313 x y) : (term372 x y) = False.
Proof. exact (prop_ext (fun h2 : term372 x y => @lem1613336 x y h2) (fun h2 : False => @lem1613338 x y h1)). Qed.
Lemma lem1613340 (x : real) (y : real) (h1 : term313 x y) : False.
Proof. exact (EQ_MP (@lem1613339 x y h1) (@lem1613338 x y h1)). Qed.
Lemma lem1613341 (x : real) (y : real) : term377 x y.
Proof. exact (fun h0 : term313 x y => @lem1613340 x y h0). Qed.
Lemma lem1613342 (x : real) (y : real) : term378 x y.
Proof. exact (@lem1386578 (term379 x y)). Qed.
Lemma lem1613343 (x : real) (y : real) : term379 x y.
Proof. exact (@lem1613342 x y (@lem1613341 x y)). Qed.
Lemma lem1613372 (x : real) (y : real) : (term380 x y) = (term381 x y).
Proof. exact (@lem17045 (term8 x) (term8 y)). Qed.
Lemma lem1613384 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (@lem17045 (term24 x) (term24 y)). Qed.
Lemma lem1613388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1613389 (x : real) (y : real) : (term382 x y) = (term383 x y).
Proof. exact (MK_COMB (@lem1613388) (@lem1613372 x y)). Qed.
Lemma lem1613390 (x : real) (y : real) : (term384 x y) = (term385 x y).
Proof. exact (MK_COMB (@lem1613389 x y) (@lem1613384 x y)). Qed.
Lemma lem1613391 (x : real) (y : real) : (term386 x y) = (term384 x y).
Proof. exact (@lem17160 (term22 x y) (term26 x y)). Qed.
Lemma lem1613392 (x : real) (y : real) : (term386 x y) = (term385 x y).
Proof. exact (TRANS (@lem1613391 x y) (@lem1613390 x y)). Qed.
Lemma lem1613398 (x : real) (y : real) : (term387 x y) = (term387 x y).
Proof. exact (eq_refl (term387 x y)). Qed.
Lemma lem1613400 (x : real) (y : real) : (term85 x y) = (term85 x y).
Proof. exact (eq_refl (term85 x y)). Qed.
Lemma lem1613401 (x : real) (y : real) : (term388 x y) = (term389 x y).
Proof. exact (MK_COMB (@lem1613400 x y) (@lem1613392 x y)). Qed.
Lemma lem1613402 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1613403 (x : real) (y : real) : (term390 x y) = (term391 x y).
Proof. exact (MK_COMB (@lem1613402) (@lem1613401 x y)). Qed.
Lemma lem1613404 (x : real) (y : real) : (term392 x y) = (term393 x y).
Proof. exact (MK_COMB (@lem1613403 x y) (@lem1613398 x y)). Qed.
Lemma lem1613405 (x : real) (y : real) : (term394 x y) = (term392 x y).
Proof. exact (@lem17646 (term18 x y) (term27 x y)). Qed.
Lemma lem1613406 (x : real) (y : real) : (term394 x y) = (term393 x y).
Proof. exact (TRANS (@lem1613405 x y) (@lem1613404 x y)). Qed.
Lemma lem1613408 (y : real) (x : real) : (term395 y x) = (term395 y x).
Proof. exact (eq_refl (term395 y x)). Qed.
Lemma lem1613409 (x : real) (y : real) : (term396 x y) = (term397 x y).
Proof. exact (MK_COMB (@lem1613408 y x) (@lem1613406 x y)). Qed.
Lemma lem1613410 (x : real) (y : real) : (term398 x y) = (term396 x y).
Proof. exact (@lem17362 (term48 y x) ((term18 x y) = (term27 x y))). Qed.
Lemma lem1613411 (x : real) (y : real) : (term398 x y) = (term397 x y).
Proof. exact (TRANS (@lem1613410 x y) (@lem1613409 x y)). Qed.
Lemma lem1613413 (y : real) : (term143 y) = (term143 y).
Proof. exact (eq_refl (term143 y)). Qed.
Lemma lem1613414 (x : real) (y : real) : (term399 x y) = (term400 x y).
Proof. exact (MK_COMB (@lem1613413 y) (@lem1613411 x y)). Qed.
Lemma lem1613415 (x : real) (y : real) : (term401 x y) = (term399 x y).
Proof. exact (@lem17362 (term9 y) (term402 x y)). Qed.
Lemma lem1613416 (x : real) (y : real) : (term401 x y) = (term400 x y).
Proof. exact (TRANS (@lem1613415 x y) (@lem1613414 x y)). Qed.
Lemma lem1613418 (x : real) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem1613419 (x : real) (y : real) : (term403 x y) = (term404 x y).
Proof. exact (MK_COMB (@lem1613418 x) (@lem1613416 x y)). Qed.
Lemma lem1613420 (x : real) (y : real) : (term405 x y) = (term403 x y).
Proof. exact (@lem17362 (term9 x) (term406 x y)). Qed.
Lemma lem1613482 (x : real) (y : real) : (term405 x y) = (term404 x y).
Proof. exact (TRANS (@lem1613420 x y) (@lem1613419 x y)). Qed.
Lemma lem1613483 (x : real) : (term9 x) = (term152 x).
Proof. exact (@lem1483521 (real_neg x) term6). Qed.
Lemma lem1613484 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613491 (x : real) : (real_neg x) = (term153 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1613492 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1613493 (x : real) : (term154 x) = (term155 x).
Proof. exact (MK_COMB (@lem1613492) (@lem1613491 x)). Qed.
Lemma lem1613494 (x : real) : (term156 x) = (term157 x).
Proof. exact (MK_COMB (@lem1613493 x) (@lem1613484)). Qed.
Lemma lem1613495 (x : real) : (term157 x) = (term158 x).
Proof. exact (@lem1483519 (term153 x) term6). Qed.
Lemma lem1613497 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1613498 : term63 = term6.
Proof. exact (@lem1613497 term64). Qed.
Lemma lem1613499 (x : real) : (term159 x) = (term159 x).
Proof. exact (eq_refl (term159 x)). Qed.
Lemma lem1613500 (x : real) : (term158 x) = (term160 x).
Proof. exact (MK_COMB (@lem1613499 x) (@lem1613498)). Qed.
Lemma lem1613501 (x : real) : (term160 x) = (term153 x).
Proof. exact (@lem1483450 (term153 x)). Qed.
Lemma lem1613502 (x : real) : (term158 x) = (term153 x).
Proof. exact (TRANS (@lem1613500 x) (@lem1613501 x)). Qed.
Lemma lem1613503 (x : real) : (term157 x) = (term153 x).
Proof. exact (TRANS (@lem1613495 x) (@lem1613502 x)). Qed.
Lemma lem1613504 (x : real) : (term156 x) = (term153 x).
Proof. exact (TRANS (@lem1613494 x) (@lem1613503 x)). Qed.
Lemma lem1613505 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613506 (x : real) : (term161 x) = (term162 x).
Proof. exact (MK_COMB (@lem1613505) (@lem1613504 x)). Qed.
Lemma lem1613507 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613508 (x : real) : (term152 x) = (term163 x).
Proof. exact (MK_COMB (@lem1613506 x) (@lem1613507)). Qed.
Lemma lem1613509 (x : real) : (term9 x) = (term163 x).
Proof. exact (TRANS (@lem1613483 x) (@lem1613508 x)). Qed.
Lemma lem1613510 (y : real) : (term9 y) = (term152 y).
Proof. exact (@lem1483521 (real_neg y) term6). Qed.
Lemma lem1613511 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613518 (y : real) : (real_neg y) = (term153 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1613519 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1613520 (y : real) : (term154 y) = (term155 y).
Proof. exact (MK_COMB (@lem1613519) (@lem1613518 y)). Qed.
Lemma lem1613521 (y : real) : (term156 y) = (term157 y).
Proof. exact (MK_COMB (@lem1613520 y) (@lem1613511)). Qed.
Lemma lem1613522 (y : real) : (term157 y) = (term158 y).
Proof. exact (@lem1483519 (term153 y) term6). Qed.
Lemma lem1613524 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1613525 : term63 = term6.
Proof. exact (@lem1613524 term64). Qed.
Lemma lem1613526 (y : real) : (term159 y) = (term159 y).
Proof. exact (eq_refl (term159 y)). Qed.
Lemma lem1613527 (y : real) : (term158 y) = (term160 y).
Proof. exact (MK_COMB (@lem1613526 y) (@lem1613525)). Qed.
Lemma lem1613528 (y : real) : (term160 y) = (term153 y).
Proof. exact (@lem1483450 (term153 y)). Qed.
Lemma lem1613529 (y : real) : (term158 y) = (term153 y).
Proof. exact (TRANS (@lem1613527 y) (@lem1613528 y)). Qed.
Lemma lem1613530 (y : real) : (term157 y) = (term153 y).
Proof. exact (TRANS (@lem1613522 y) (@lem1613529 y)). Qed.
Lemma lem1613531 (y : real) : (term156 y) = (term153 y).
Proof. exact (TRANS (@lem1613521 y) (@lem1613530 y)). Qed.
Lemma lem1613532 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613533 (y : real) : (term161 y) = (term162 y).
Proof. exact (MK_COMB (@lem1613532) (@lem1613531 y)). Qed.
Lemma lem1613534 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613535 (y : real) : (term152 y) = (term163 y).
Proof. exact (MK_COMB (@lem1613533 y) (@lem1613534)). Qed.
Lemma lem1613536 (y : real) : (term9 y) = (term163 y).
Proof. exact (TRANS (@lem1613510 y) (@lem1613535 y)). Qed.
Lemma lem1613537 (y : real) (x : real) : (term48 y x) = (term407 y x).
Proof. exact (@lem1483521 (term408 y x) term6). Qed.
Lemma lem1613538 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613545 (x : real) : (real_neg x) = (term153 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1613552 (y : real) : (real_neg y) = (term153 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1613553 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1613554 (y : real) : (term166 y) = (term167 y).
Proof. exact (MK_COMB (@lem1613553) (@lem1613552 y)). Qed.
Lemma lem1613555 (y : real) (x : real) : (term408 y x) = (term409 y x).
Proof. exact (MK_COMB (@lem1613554 y) (@lem1613545 x)). Qed.
Lemma lem1613556 (y : real) (x : real) : (term409 y x) = (term410 y x).
Proof. exact (@lem1483464 term113 term113 y x). Qed.
Lemma lem1613558 (m : nat) (n : nat) : (term411 m n) = (term412 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1613559 : term413 = term414.
Proof. exact (@lem1613558 term64 term64). Qed.
Lemma lem1613560 : (term415 = (BIT1 0)) = (term416 = term64).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1613561 : term416 = term64.
Proof. exact (EQ_MP (@lem1613560) (@lem940073)). Qed.
Lemma lem1613562 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1613563 : term414 = term98.
Proof. exact (MK_COMB (@lem1613562) (@lem1613561)). Qed.
Lemma lem1613564 : term413 = term98.
Proof. exact (TRANS (@lem1613559) (@lem1613563)). Qed.
Lemma lem1613565 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1613566 : term417 = term418.
Proof. exact (MK_COMB (@lem1613565) (@lem1613564)). Qed.
Lemma lem1613567 (y : real) (x : real) : (real_mul y x) = (real_mul y x).
Proof. exact (eq_refl (real_mul y x)). Qed.
Lemma lem1613568 (y : real) (x : real) : (term410 y x) = (term106 y x).
Proof. exact (MK_COMB (@lem1613566) (@lem1613567 y x)). Qed.
Lemma lem1613569 (y : real) (x : real) : (term409 y x) = (term106 y x).
Proof. exact (TRANS (@lem1613556 y x) (@lem1613568 y x)). Qed.
Lemma lem1613570 (x : real) (y : real) : (real_mul y x) = (real_mul x y).
Proof. exact (@lem1483474 x y). Qed.
Lemma lem1613571 : term418 = term418.
Proof. exact (eq_refl term418). Qed.
Lemma lem1613572 (x : real) (y : real) : (term106 y x) = (term106 x y).
Proof. exact (MK_COMB (@lem1613571) (@lem1613570 x y)). Qed.
Lemma lem1613573 (x : real) (y : real) : (term409 y x) = (term106 x y).
Proof. exact (TRANS (@lem1613569 y x) (@lem1613572 x y)). Qed.
Lemma lem1613574 (x : real) (y : real) : (term106 x y) = (real_mul x y).
Proof. exact (@lem1483436 (real_mul x y)). Qed.
Lemma lem1613575 (x : real) (y : real) : (term409 y x) = (real_mul x y).
Proof. exact (TRANS (@lem1613573 x y) (@lem1613574 x y)). Qed.
Lemma lem1613576 (x : real) (y : real) : (term408 y x) = (real_mul x y).
Proof. exact (TRANS (@lem1613555 y x) (@lem1613575 x y)). Qed.
Lemma lem1613577 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1613578 (x : real) (y : real) : (term419 y x) = (term69 x y).
Proof. exact (MK_COMB (@lem1613577) (@lem1613576 x y)). Qed.
Lemma lem1613579 (x : real) (y : real) : (term420 y x) = (term70 x y).
Proof. exact (MK_COMB (@lem1613578 x y) (@lem1613538)). Qed.
Lemma lem1613580 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (@lem1483519 (real_mul x y) term6). Qed.
Lemma lem1613582 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1613583 : term63 = term6.
Proof. exact (@lem1613582 term64). Qed.
Lemma lem1613584 (x : real) (y : real) : (term72 x y) = (term72 x y).
Proof. exact (eq_refl (term72 x y)). Qed.
Lemma lem1613585 (x : real) (y : real) : (term71 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem1613584 x y) (@lem1613583)). Qed.
Lemma lem1613586 (x : real) (y : real) : (term73 x y) = (real_mul x y).
Proof. exact (@lem1483450 (real_mul x y)). Qed.
Lemma lem1613587 (x : real) (y : real) : (term71 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1613585 x y) (@lem1613586 x y)). Qed.
Lemma lem1613588 (x : real) (y : real) : (term70 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1613580 x y) (@lem1613587 x y)). Qed.
Lemma lem1613589 (x : real) (y : real) : (term420 y x) = (real_mul x y).
Proof. exact (TRANS (@lem1613579 x y) (@lem1613588 x y)). Qed.
Lemma lem1613590 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613591 (x : real) (y : real) : (term421 y x) = (term75 x y).
Proof. exact (MK_COMB (@lem1613590) (@lem1613589 x y)). Qed.
Lemma lem1613592 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613593 (x : real) (y : real) : (term407 y x) = (term76 x y).
Proof. exact (MK_COMB (@lem1613591 x y) (@lem1613592)). Qed.
Lemma lem1613594 (x : real) (y : real) : (term48 y x) = (term76 x y).
Proof. exact (TRANS (@lem1613537 y x) (@lem1613593 x y)). Qed.
Lemma lem1613595 (x : real) (y : real) : (term18 x y) = (term68 x y).
Proof. exact (@lem1483521 (real_mul x y) term6). Qed.
Lemma lem1613607 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (@lem1483519 (real_mul x y) term6). Qed.
Lemma lem1613609 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1613610 : term63 = term6.
Proof. exact (@lem1613609 term64). Qed.
Lemma lem1613611 (x : real) (y : real) : (term72 x y) = (term72 x y).
Proof. exact (eq_refl (term72 x y)). Qed.
Lemma lem1613612 (x : real) (y : real) : (term71 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem1613611 x y) (@lem1613610)). Qed.
Lemma lem1613613 (x : real) (y : real) : (term73 x y) = (real_mul x y).
Proof. exact (@lem1483450 (real_mul x y)). Qed.
Lemma lem1613614 (x : real) (y : real) : (term71 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1613612 x y) (@lem1613613 x y)). Qed.
Lemma lem1613616 (x : real) (y : real) : (term70 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1613607 x y) (@lem1613614 x y)). Qed.
Lemma lem1613617 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613618 (x : real) (y : real) : (term74 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1613617) (@lem1613616 x y)). Qed.
Lemma lem1613619 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613620 (x : real) (y : real) : (term68 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1613618 x y) (@lem1613619)). Qed.
Lemma lem1613621 (x : real) (y : real) : (term18 x y) = (term76 x y).
Proof. exact (TRANS (@lem1613595 x y) (@lem1613620 x y)). Qed.
Lemma lem1613622 (x : real) : (term180 x) = (term181 x).
Proof. exact (@lem1483531 term6 x). Qed.
Lemma lem1613628 (x : real) : (term182 x) = (term183 x).
Proof. exact (@lem1483519 term6 x). Qed.
Lemma lem1613633 (x : real) : (term183 x) = (term153 x).
Proof. exact (@lem1483448 (term153 x)). Qed.
Lemma lem1613635 (x : real) : (term182 x) = (term153 x).
Proof. exact (TRANS (@lem1613628 x) (@lem1613633 x)). Qed.
Lemma lem1613636 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1613637 (x : real) : (term184 x) = (term185 x).
Proof. exact (MK_COMB (@lem1613636) (@lem1613635 x)). Qed.
Lemma lem1613638 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613639 (x : real) : (term181 x) = (term186 x).
Proof. exact (MK_COMB (@lem1613637 x) (@lem1613638)). Qed.
Lemma lem1613640 (x : real) : (term180 x) = (term186 x).
Proof. exact (TRANS (@lem1613622 x) (@lem1613639 x)). Qed.
Lemma lem1613641 (y : real) : (term180 y) = (term181 y).
Proof. exact (@lem1483531 term6 y). Qed.
Lemma lem1613647 (y : real) : (term182 y) = (term183 y).
Proof. exact (@lem1483519 term6 y). Qed.
Lemma lem1613652 (y : real) : (term183 y) = (term153 y).
Proof. exact (@lem1483448 (term153 y)). Qed.
Lemma lem1613654 (y : real) : (term182 y) = (term153 y).
Proof. exact (TRANS (@lem1613647 y) (@lem1613652 y)). Qed.
Lemma lem1613655 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1613656 (y : real) : (term184 y) = (term185 y).
Proof. exact (MK_COMB (@lem1613655) (@lem1613654 y)). Qed.
Lemma lem1613657 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613658 (y : real) : (term181 y) = (term186 y).
Proof. exact (MK_COMB (@lem1613656 y) (@lem1613657)). Qed.
Lemma lem1613659 (y : real) : (term180 y) = (term186 y).
Proof. exact (TRANS (@lem1613641 y) (@lem1613658 y)). Qed.
Lemma lem1613660 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1613661 (x : real) : (term422 x) = (term423 x).
Proof. exact (MK_COMB (@lem1613660) (@lem1613640 x)). Qed.
Lemma lem1613662 (x : real) (y : real) : (term381 x y) = (term424 x y).
Proof. exact (MK_COMB (@lem1613661 x) (@lem1613659 y)). Qed.
Lemma lem1613663 (x : real) : (term187 x) = (term188 x).
Proof. exact (@lem1483531 x term6). Qed.
Lemma lem1613669 (x : real) : (term60 x) = (term61 x).
Proof. exact (@lem1483519 x term6). Qed.
Lemma lem1613671 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1613672 : term63 = term6.
Proof. exact (@lem1613671 term64). Qed.
Lemma lem1613673 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1613674 (x : real) : (term61 x) = (term65 x).
Proof. exact (MK_COMB (@lem1613673 x) (@lem1613672)). Qed.
Lemma lem1613675 (x : real) : (term65 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1613676 (x : real) : (term61 x) = x.
Proof. exact (TRANS (@lem1613674 x) (@lem1613675 x)). Qed.
Lemma lem1613678 (x : real) : (term60 x) = x.
Proof. exact (TRANS (@lem1613669 x) (@lem1613676 x)). Qed.
Lemma lem1613679 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1613680 (x : real) : (term189 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1613679) (@lem1613678 x)). Qed.
Lemma lem1613681 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613682 (x : real) : (term188 x) = (term190 x).
Proof. exact (MK_COMB (@lem1613680 x) (@lem1613681)). Qed.
Lemma lem1613683 (x : real) : (term187 x) = (term190 x).
Proof. exact (TRANS (@lem1613663 x) (@lem1613682 x)). Qed.
Lemma lem1613684 (y : real) : (term187 y) = (term188 y).
Proof. exact (@lem1483531 y term6). Qed.
Lemma lem1613690 (y : real) : (term60 y) = (term61 y).
Proof. exact (@lem1483519 y term6). Qed.
Lemma lem1613692 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1613693 : term63 = term6.
Proof. exact (@lem1613692 term64). Qed.
Lemma lem1613694 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1613695 (y : real) : (term61 y) = (term65 y).
Proof. exact (MK_COMB (@lem1613694 y) (@lem1613693)). Qed.
Lemma lem1613696 (y : real) : (term65 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1613697 (y : real) : (term61 y) = y.
Proof. exact (TRANS (@lem1613695 y) (@lem1613696 y)). Qed.
Lemma lem1613699 (y : real) : (term60 y) = y.
Proof. exact (TRANS (@lem1613690 y) (@lem1613697 y)). Qed.
Lemma lem1613700 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1613701 (y : real) : (term189 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1613700) (@lem1613699 y)). Qed.
Lemma lem1613702 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613703 (y : real) : (term188 y) = (term190 y).
Proof. exact (MK_COMB (@lem1613701 y) (@lem1613702)). Qed.
Lemma lem1613704 (y : real) : (term187 y) = (term190 y).
Proof. exact (TRANS (@lem1613684 y) (@lem1613703 y)). Qed.
Lemma lem1613705 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1613706 (x : real) : (term191 x) = (term192 x).
Proof. exact (MK_COMB (@lem1613705) (@lem1613683 x)). Qed.
Lemma lem1613707 (x : real) (y : real) : (term126 x y) = (term193 x y).
Proof. exact (MK_COMB (@lem1613706 x) (@lem1613704 y)). Qed.
Lemma lem1613708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1613709 (x : real) (y : real) : (term383 x y) = (term425 x y).
Proof. exact (MK_COMB (@lem1613708) (@lem1613662 x y)). Qed.
Lemma lem1613710 (x : real) (y : real) : (term385 x y) = (term426 x y).
Proof. exact (MK_COMB (@lem1613709 x y) (@lem1613707 x y)). Qed.
Lemma lem1613711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1613712 (x : real) (y : real) : (term85 x y) = (term86 x y).
Proof. exact (MK_COMB (@lem1613711) (@lem1613621 x y)). Qed.
Lemma lem1613713 (x : real) (y : real) : (term389 x y) = (term427 x y).
Proof. exact (MK_COMB (@lem1613712 x y) (@lem1613710 x y)). Qed.
Lemma lem1613714 (x : real) (y : real) : (term77 x y) = (term78 x y).
Proof. exact (@lem1483531 term6 (real_mul x y)). Qed.
Lemma lem1613726 (x : real) (y : real) : (term79 x y) = (term80 x y).
Proof. exact (@lem1483519 term6 (real_mul x y)). Qed.
Lemma lem1613731 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (@lem1483448 (term81 x y)). Qed.
Lemma lem1613733 (x : real) (y : real) : (term79 x y) = (term81 x y).
Proof. exact (TRANS (@lem1613726 x y) (@lem1613731 x y)). Qed.
Lemma lem1613734 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1613735 (x : real) (y : real) : (term82 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1613734) (@lem1613733 x y)). Qed.
Lemma lem1613736 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613737 (x : real) (y : real) : (term78 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1613735 x y) (@lem1613736)). Qed.
Lemma lem1613738 (x : real) (y : real) : (term77 x y) = (term84 x y).
Proof. exact (TRANS (@lem1613714 x y) (@lem1613737 x y)). Qed.
Lemma lem1613739 (x : real) : (term8 x) = (term59 x).
Proof. exact (@lem1483521 x term6). Qed.
Lemma lem1613745 (x : real) : (term60 x) = (term61 x).
Proof. exact (@lem1483519 x term6). Qed.
Lemma lem1613747 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1613748 : term63 = term6.
Proof. exact (@lem1613747 term64). Qed.
Lemma lem1613749 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1613750 (x : real) : (term61 x) = (term65 x).
Proof. exact (MK_COMB (@lem1613749 x) (@lem1613748)). Qed.
Lemma lem1613751 (x : real) : (term65 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1613752 (x : real) : (term61 x) = x.
Proof. exact (TRANS (@lem1613750 x) (@lem1613751 x)). Qed.
Lemma lem1613754 (x : real) : (term60 x) = x.
Proof. exact (TRANS (@lem1613745 x) (@lem1613752 x)). Qed.
Lemma lem1613755 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613756 (x : real) : (term66 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1613755) (@lem1613754 x)). Qed.
Lemma lem1613757 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613758 (x : real) : (term59 x) = (term67 x).
Proof. exact (MK_COMB (@lem1613756 x) (@lem1613757)). Qed.
Lemma lem1613759 (x : real) : (term8 x) = (term67 x).
Proof. exact (TRANS (@lem1613739 x) (@lem1613758 x)). Qed.
Lemma lem1613760 (y : real) : (term8 y) = (term59 y).
Proof. exact (@lem1483521 y term6). Qed.
Lemma lem1613766 (y : real) : (term60 y) = (term61 y).
Proof. exact (@lem1483519 y term6). Qed.
Lemma lem1613768 (x : nat) : (term62 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1613769 : term63 = term6.
Proof. exact (@lem1613768 term64). Qed.
Lemma lem1613770 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1613771 (y : real) : (term61 y) = (term65 y).
Proof. exact (MK_COMB (@lem1613770 y) (@lem1613769)). Qed.
Lemma lem1613772 (y : real) : (term65 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1613773 (y : real) : (term61 y) = y.
Proof. exact (TRANS (@lem1613771 y) (@lem1613772 y)). Qed.
Lemma lem1613775 (y : real) : (term60 y) = y.
Proof. exact (TRANS (@lem1613766 y) (@lem1613773 y)). Qed.
Lemma lem1613776 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613777 (y : real) : (term66 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1613776) (@lem1613775 y)). Qed.
Lemma lem1613778 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613779 (y : real) : (term59 y) = (term67 y).
Proof. exact (MK_COMB (@lem1613777 y) (@lem1613778)). Qed.
Lemma lem1613780 (y : real) : (term8 y) = (term67 y).
Proof. exact (TRANS (@lem1613760 y) (@lem1613779 y)). Qed.
Lemma lem1613781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1613782 (x : real) : (term21 x) = (term88 x).
Proof. exact (MK_COMB (@lem1613781) (@lem1613759 x)). Qed.
Lemma lem1613783 (x : real) (y : real) : (term22 x y) = (term428 x y).
Proof. exact (MK_COMB (@lem1613782 x) (@lem1613780 y)). Qed.
Lemma lem1613784 (x : real) : (term24 x) = (term197 x).
Proof. exact (@lem1483521 term6 x). Qed.
Lemma lem1613790 (x : real) : (term182 x) = (term183 x).
Proof. exact (@lem1483519 term6 x). Qed.
Lemma lem1613795 (x : real) : (term183 x) = (term153 x).
Proof. exact (@lem1483448 (term153 x)). Qed.
Lemma lem1613797 (x : real) : (term182 x) = (term153 x).
Proof. exact (TRANS (@lem1613790 x) (@lem1613795 x)). Qed.
Lemma lem1613798 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613799 (x : real) : (term198 x) = (term162 x).
Proof. exact (MK_COMB (@lem1613798) (@lem1613797 x)). Qed.
Lemma lem1613800 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613801 (x : real) : (term197 x) = (term163 x).
Proof. exact (MK_COMB (@lem1613799 x) (@lem1613800)). Qed.
Lemma lem1613802 (x : real) : (term24 x) = (term163 x).
Proof. exact (TRANS (@lem1613784 x) (@lem1613801 x)). Qed.
Lemma lem1613803 (y : real) : (term24 y) = (term197 y).
Proof. exact (@lem1483521 term6 y). Qed.
Lemma lem1613809 (y : real) : (term182 y) = (term183 y).
Proof. exact (@lem1483519 term6 y). Qed.
Lemma lem1613814 (y : real) : (term183 y) = (term153 y).
Proof. exact (@lem1483448 (term153 y)). Qed.
Lemma lem1613816 (y : real) : (term182 y) = (term153 y).
Proof. exact (TRANS (@lem1613809 y) (@lem1613814 y)). Qed.
Lemma lem1613817 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1613818 (y : real) : (term198 y) = (term162 y).
Proof. exact (MK_COMB (@lem1613817) (@lem1613816 y)). Qed.
Lemma lem1613819 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1613820 (y : real) : (term197 y) = (term163 y).
Proof. exact (MK_COMB (@lem1613818 y) (@lem1613819)). Qed.
Lemma lem1613821 (y : real) : (term24 y) = (term163 y).
Proof. exact (TRANS (@lem1613803 y) (@lem1613820 y)). Qed.
Lemma lem1613822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1613823 (x : real) : (term25 x) = (term199 x).
Proof. exact (MK_COMB (@lem1613822) (@lem1613802 x)). Qed.
Lemma lem1613824 (x : real) (y : real) : (term26 x y) = (term200 x y).
Proof. exact (MK_COMB (@lem1613823 x) (@lem1613821 y)). Qed.
Lemma lem1613825 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1613826 (x : real) (y : real) : (term23 x y) = (term429 x y).
Proof. exact (MK_COMB (@lem1613825) (@lem1613783 x y)). Qed.
Lemma lem1613827 (x : real) (y : real) : (term27 x y) = (term430 x y).
Proof. exact (MK_COMB (@lem1613826 x y) (@lem1613824 x y)). Qed.
Lemma lem1613828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1613829 (x : real) (y : real) : (term203 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem1613828) (@lem1613738 x y)). Qed.
Lemma lem1613830 (x : real) (y : real) : (term387 x y) = (term431 x y).
Proof. exact (MK_COMB (@lem1613829 x y) (@lem1613827 x y)). Qed.
Lemma lem1613831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1613832 (x : real) (y : real) : (term391 x y) = (term432 x y).
Proof. exact (MK_COMB (@lem1613831) (@lem1613713 x y)). Qed.
Lemma lem1613833 (x : real) (y : real) : (term393 x y) = (term433 x y).
Proof. exact (MK_COMB (@lem1613832 x y) (@lem1613830 x y)). Qed.
Lemma lem1613834 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1613835 (x : real) (y : real) : (term395 y x) = (term86 x y).
Proof. exact (MK_COMB (@lem1613834) (@lem1613594 x y)). Qed.
Lemma lem1613836 (x : real) (y : real) : (term397 x y) = (term434 x y).
Proof. exact (MK_COMB (@lem1613835 x y) (@lem1613833 x y)). Qed.
Lemma lem1613837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1613838 (y : real) : (term143 y) = (term199 y).
Proof. exact (MK_COMB (@lem1613837) (@lem1613536 y)). Qed.
Lemma lem1613839 (x : real) (y : real) : (term400 x y) = (term435 x y).
Proof. exact (MK_COMB (@lem1613838 y) (@lem1613836 x y)). Qed.
Lemma lem1613840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1613841 (x : real) : (term143 x) = (term199 x).
Proof. exact (MK_COMB (@lem1613840) (@lem1613509 x)). Qed.
Lemma lem1613842 (x : real) (y : real) : (term404 x y) = (term436 x y).
Proof. exact (MK_COMB (@lem1613841 x) (@lem1613839 x y)). Qed.
Lemma lem1613849 (x : real) (y : real) : (term405 x y) = (term436 x y).
Proof. exact (TRANS (@lem1613482 x y) (@lem1613842 x y)). Qed.
Lemma lem1613878 (x : real) (y : real) : (term431 x y) = (term437 x y).
Proof. exact (@lem19158 (term428 x y) (term84 x y) (term200 x y)). Qed.
Lemma lem1613892 (x : real) (y : real) : (term426 x y) = (term438 x y).
Proof. exact (@lem19158 (term190 x) (term424 x y) (term190 y)). Qed.
Lemma lem1613899 (x : real) (y : real) : (term439 x y) = (term440 x y).
Proof. exact (@lem19367 (term186 x) (term186 y) (term190 y)). Qed.
Lemma lem1613906 (y : real) (x : real) : (term441 y x) = (term442 y x).
Proof. exact (@lem19367 (term186 x) (term186 y) (term190 x)). Qed.
Lemma lem1613907 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1613908 (y : real) (x : real) : (term443 y x) = (term444 y x).
Proof. exact (MK_COMB (@lem1613907) (@lem1613906 y x)). Qed.
Lemma lem1613909 (x : real) (y : real) : (term438 x y) = (term445 x y).
Proof. exact (MK_COMB (@lem1613908 y x) (@lem1613899 x y)). Qed.
Lemma lem1613911 (x : real) (y : real) : (term426 x y) = (term445 x y).
Proof. exact (TRANS (@lem1613892 x y) (@lem1613909 x y)). Qed.
Lemma lem1613914 (x : real) (y : real) : (term86 x y) = (term86 x y).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1613915 (x : real) (y : real) : (term427 x y) = (term446 x y).
Proof. exact (MK_COMB (@lem1613914 x y) (@lem1613911 x y)). Qed.
Lemma lem1613916 (x : real) (y : real) : (term446 x y) = (term447 x y).
Proof. exact (@lem19158 (term442 y x) (term76 x y) (term440 x y)). Qed.
Lemma lem1613923 (x : real) (y : real) : (term448 x y) = (term449 x y).
Proof. exact (@lem19158 (term216 x y) (term76 x y) (term217 y)). Qed.
Lemma lem1613930 (y : real) (x : real) : (term450 y x) = (term451 y x).
Proof. exact (@lem19158 (term217 x) (term76 x y) (term216 y x)). Qed.
Lemma lem1613931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1613932 (y : real) (x : real) : (term452 y x) = (term453 y x).
Proof. exact (MK_COMB (@lem1613931) (@lem1613930 y x)). Qed.
Lemma lem1613933 (x : real) (y : real) : (term447 x y) = (term454 x y).
Proof. exact (MK_COMB (@lem1613932 y x) (@lem1613923 x y)). Qed.
Lemma lem1613934 (x : real) (y : real) : (term446 x y) = (term454 x y).
Proof. exact (TRANS (@lem1613916 x y) (@lem1613933 x y)). Qed.
Lemma lem1613935 (x : real) (y : real) : (term427 x y) = (term454 x y).
Proof. exact (TRANS (@lem1613915 x y) (@lem1613934 x y)). Qed.
Lemma lem1613936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1613937 (x : real) (y : real) : (term432 x y) = (term455 x y).
Proof. exact (MK_COMB (@lem1613936) (@lem1613935 x y)). Qed.
Lemma lem1613938 (x : real) (y : real) : (term433 x y) = (term456 x y).
Proof. exact (MK_COMB (@lem1613937 x y) (@lem1613878 x y)). Qed.
Lemma lem1613941 (x : real) (y : real) : (term86 x y) = (term86 x y).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1613942 (x : real) (y : real) : (term434 x y) = (term457 x y).
Proof. exact (MK_COMB (@lem1613941 x y) (@lem1613938 x y)). Qed.
Lemma lem1613943 (x : real) (y : real) : (term457 x y) = (term458 x y).
Proof. exact (@lem19158 (term454 x y) (term76 x y) (term437 x y)). Qed.
Lemma lem1613950 (x : real) (y : real) : (term459 x y) = (term460 x y).
Proof. exact (@lem19158 (term461 x y) (term76 x y) (term225 x y)). Qed.
Lemma lem1613951 (x : real) (y : real) : (term462 x y) = (term463 x y).
Proof. exact (@lem19158 (term451 y x) (term76 x y) (term449 x y)). Qed.
Lemma lem1613958 (x : real) (y : real) : (term464 x y) = (term465 x y).
Proof. exact (@lem19158 (term344 x y) (term76 x y) (term229 x y)). Qed.
Lemma lem1613965 (y : real) (x : real) : (term466 y x) = (term467 y x).
Proof. exact (@lem19158 (term343 y x) (term76 x y) (term228 y x)). Qed.
Lemma lem1613966 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1613967 (y : real) (x : real) : (term468 y x) = (term469 y x).
Proof. exact (MK_COMB (@lem1613966) (@lem1613965 y x)). Qed.
Lemma lem1613968 (x : real) (y : real) : (term463 x y) = (term470 x y).
Proof. exact (MK_COMB (@lem1613967 y x) (@lem1613958 x y)). Qed.
Lemma lem1613969 (x : real) (y : real) : (term462 x y) = (term470 x y).
Proof. exact (TRANS (@lem1613951 x y) (@lem1613968 x y)). Qed.
Lemma lem1613970 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1613971 (x : real) (y : real) : (term471 x y) = (term472 x y).
Proof. exact (MK_COMB (@lem1613970) (@lem1613969 x y)). Qed.
Lemma lem1613972 (x : real) (y : real) : (term458 x y) = (term473 x y).
Proof. exact (MK_COMB (@lem1613971 x y) (@lem1613950 x y)). Qed.
Lemma lem1613973 (x : real) (y : real) : (term457 x y) = (term473 x y).
Proof. exact (TRANS (@lem1613943 x y) (@lem1613972 x y)). Qed.
Lemma lem1613974 (x : real) (y : real) : (term434 x y) = (term473 x y).
Proof. exact (TRANS (@lem1613942 x y) (@lem1613973 x y)). Qed.
Lemma lem1613977 (y : real) : (term199 y) = (term199 y).
Proof. exact (eq_refl (term199 y)). Qed.
Lemma lem1613978 (x : real) (y : real) : (term435 x y) = (term474 x y).
Proof. exact (MK_COMB (@lem1613977 y) (@lem1613974 x y)). Qed.
Lemma lem1613979 (x : real) (y : real) : (term474 x y) = (term475 x y).
Proof. exact (@lem19158 (term470 x y) (term163 y) (term460 x y)). Qed.
Lemma lem1613986 (x : real) (y : real) : (term476 x y) = (term477 x y).
Proof. exact (@lem19158 (term478 x y) (term163 y) (term479 x y)). Qed.
Lemma lem1613987 (x : real) (y : real) : (term480 x y) = (term481 x y).
Proof. exact (@lem19158 (term467 y x) (term163 y) (term465 x y)). Qed.
Lemma lem1613994 (x : real) (y : real) : (term482 x y) = (term483 x y).
Proof. exact (@lem19158 (term484 x y) (term163 y) (term485 x y)). Qed.
Lemma lem1614001 (y : real) (x : real) : (term486 y x) = (term487 y x).
Proof. exact (@lem19158 (term488 y x) (term163 y) (term489 y x)). Qed.
Lemma lem1614002 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1614003 (y : real) (x : real) : (term490 y x) = (term491 y x).
Proof. exact (MK_COMB (@lem1614002) (@lem1614001 y x)). Qed.
Lemma lem1614004 (x : real) (y : real) : (term481 x y) = (term492 x y).
Proof. exact (MK_COMB (@lem1614003 y x) (@lem1613994 x y)). Qed.
Lemma lem1614005 (x : real) (y : real) : (term480 x y) = (term492 x y).
Proof. exact (TRANS (@lem1613987 x y) (@lem1614004 x y)). Qed.
Lemma lem1614006 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1614007 (x : real) (y : real) : (term493 x y) = (term494 x y).
Proof. exact (MK_COMB (@lem1614006) (@lem1614005 x y)). Qed.
Lemma lem1614008 (x : real) (y : real) : (term475 x y) = (term495 x y).
Proof. exact (MK_COMB (@lem1614007 x y) (@lem1613986 x y)). Qed.
Lemma lem1614009 (x : real) (y : real) : (term474 x y) = (term495 x y).
Proof. exact (TRANS (@lem1613979 x y) (@lem1614008 x y)). Qed.
Lemma lem1614010 (x : real) (y : real) : (term435 x y) = (term495 x y).
Proof. exact (TRANS (@lem1613978 x y) (@lem1614009 x y)). Qed.
Lemma lem1614013 (x : real) : (term199 x) = (term199 x).
Proof. exact (eq_refl (term199 x)). Qed.
Lemma lem1614014 (x : real) (y : real) : (term436 x y) = (term496 x y).
Proof. exact (MK_COMB (@lem1614013 x) (@lem1614010 x y)). Qed.
Lemma lem1614015 (x : real) (y : real) : (term496 x y) = (term497 x y).
Proof. exact (@lem19158 (term492 x y) (term163 x) (term477 x y)). Qed.
Lemma lem1614022 (x : real) (y : real) : (term498 x y) = (term499 x y).
Proof. exact (@lem19158 (term500 x y) (term163 x) (term501 x y)). Qed.
Lemma lem1614023 (x : real) (y : real) : (term502 x y) = (term503 x y).
Proof. exact (@lem19158 (term487 y x) (term163 x) (term483 x y)). Qed.
Lemma lem1614030 (x : real) (y : real) : (term504 x y) = (term505 x y).
Proof. exact (@lem19158 (term506 x y) (term163 x) (term507 x y)). Qed.
Lemma lem1614037 (y : real) (x : real) : (term508 y x) = (term509 y x).
Proof. exact (@lem19158 (term510 y x) (term163 x) (term511 y x)). Qed.
Lemma lem1614038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1614039 (y : real) (x : real) : (term512 y x) = (term513 y x).
Proof. exact (MK_COMB (@lem1614038) (@lem1614037 y x)). Qed.
Lemma lem1614040 (x : real) (y : real) : (term503 x y) = (term514 x y).
Proof. exact (MK_COMB (@lem1614039 y x) (@lem1614030 x y)). Qed.
Lemma lem1614041 (x : real) (y : real) : (term502 x y) = (term514 x y).
Proof. exact (TRANS (@lem1614023 x y) (@lem1614040 x y)). Qed.
Lemma lem1614042 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1614043 (x : real) (y : real) : (term515 x y) = (term516 x y).
Proof. exact (MK_COMB (@lem1614042) (@lem1614041 x y)). Qed.
Lemma lem1614044 (x : real) (y : real) : (term497 x y) = (term517 x y).
Proof. exact (MK_COMB (@lem1614043 x y) (@lem1614022 x y)). Qed.
Lemma lem1614045 (x : real) (y : real) : (term496 x y) = (term517 x y).
Proof. exact (TRANS (@lem1614015 x y) (@lem1614044 x y)). Qed.
Lemma lem1614046 (x : real) (y : real) : (term436 x y) = (term517 x y).
Proof. exact (TRANS (@lem1614014 x y) (@lem1614045 x y)). Qed.
Lemma lem1614047 (x : real) (y : real) : (term405 x y) = (term517 x y).
Proof. exact (TRANS (@lem1613849 x y) (@lem1614046 x y)). Qed.
Lemma lem1614081 (x : real) (y : real) (h1 : term517 x y) : term517 x y.
Proof. exact (h1). Qed.
Lemma lem1614082 (x : real) (y : real) (h1 : term514 x y) : term514 x y.
Proof. exact (h1). Qed.
Lemma lem1614083 (y : real) (x : real) (h1 : term509 y x) : term509 y x.
Proof. exact (h1). Qed.
Lemma lem1614084 (y : real) (x : real) (h1 : term518 y x) : term518 y x.
Proof. exact (h1). Qed.
Lemma lem1614085 (y : real) (x : real) (h1 : term518 y x) : term510 y x.
Proof. exact (proj2 (@lem1614084 y x h1)). Qed.
Lemma lem1614086 (y : real) (x : real) (h1 : term518 y x) : term163 x.
Proof. exact (proj1 (@lem1614084 y x h1)). Qed.
Lemma lem1614087 (y : real) (x : real) (h1 : term518 y x) : term488 y x.
Proof. exact (proj2 (@lem1614085 y x h1)). Qed.
Lemma lem1614089 (y : real) (x : real) (h1 : term518 y x) : term343 y x.
Proof. exact (proj2 (@lem1614087 y x h1)). Qed.
Lemma lem1614091 (y : real) (x : real) (h1 : term518 y x) : term217 x.
Proof. exact (proj2 (@lem1614089 y x h1)). Qed.
Lemma lem1614093 (y : real) (x : real) (h1 : term518 y x) : term190 x.
Proof. exact (proj2 (@lem1614091 y x h1)). Qed.
Lemma lem1614096 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614097 : term92 = term93.
Proof. exact (@lem1614096 (NUMERAL 0) term64). Qed.
Lemma lem1614098 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1614099 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1614100 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1614099 h1) (fun h1 : term93 = True => @lem1614098)). Qed.
Lemma lem1614101 : term93 = True.
Proof. exact (EQ_MP (@lem1614100) (@lem1614098)). Qed.
Lemma lem1614102 : term92 = True.
Proof. exact (TRANS (@lem1614097) (@lem1614101)). Qed.
Lemma lem1614103 : True = term92.
Proof. exact (SYM (@lem1614102)). Qed.
Lemma lem1614104 : term92.
Proof. exact (EQ_MP (@lem1614103) (@lem0)). Qed.
Lemma lem1614105 (y : real) (x : real) (h1 : term518 y x) : term519 x.
Proof. exact (conj (@lem1614104) (@lem1614093 y x h1)). Qed.
Lemma lem1614107 (x : real) (y : real) : term96 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1614108 (x : real) : term520 x.
Proof. exact (@lem1614107 term98 x). Qed.
Lemma lem1614109 (y : real) (x : real) (h1 : term518 y x) : term521 x.
Proof. exact (@lem1614108 x (@lem1614105 y x h1)). Qed.
Lemma lem1614110 (x : real) : (term275 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1614111 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1614112 (x : real) : (term522 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1614111) (@lem1614110 x)). Qed.
Lemma lem1614113 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614114 (x : real) : (term521 x) = (term190 x).
Proof. exact (MK_COMB (@lem1614112 x) (@lem1614113)). Qed.
Lemma lem1614115 (y : real) (x : real) (h1 : term518 y x) : term190 x.
Proof. exact (EQ_MP (@lem1614114 x) (@lem1614109 y x h1)). Qed.
Lemma lem1614117 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614118 : term92 = term93.
Proof. exact (@lem1614117 (NUMERAL 0) term64). Qed.
Lemma lem1614119 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1614120 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1614121 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1614120 h1) (fun h1 : term93 = True => @lem1614119)). Qed.
Lemma lem1614122 : term93 = True.
Proof. exact (EQ_MP (@lem1614121) (@lem1614119)). Qed.
Lemma lem1614123 : term92 = True.
Proof. exact (TRANS (@lem1614118) (@lem1614122)). Qed.
Lemma lem1614124 : True = term92.
Proof. exact (SYM (@lem1614123)). Qed.
Lemma lem1614125 : term92.
Proof. exact (EQ_MP (@lem1614124) (@lem0)). Qed.
Lemma lem1614126 (y : real) (x : real) (h1 : term518 y x) : term277 x.
Proof. exact (conj (@lem1614125) (@lem1614086 y x h1)). Qed.
Lemma lem1614128 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1614129 (x : real) : term278 x.
Proof. exact (@lem1614128 term98 (term153 x)). Qed.
Lemma lem1614130 (y : real) (x : real) (h1 : term518 y x) : term279 x.
Proof. exact (@lem1614129 x (@lem1614126 y x h1)). Qed.
Lemma lem1614131 (x : real) : (term280 x) = (term153 x).
Proof. exact (@lem1483460 (term153 x)). Qed.
Lemma lem1614132 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1614133 (x : real) : (term281 x) = (term162 x).
Proof. exact (MK_COMB (@lem1614132) (@lem1614131 x)). Qed.
Lemma lem1614134 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614135 (x : real) : (term279 x) = (term163 x).
Proof. exact (MK_COMB (@lem1614133 x) (@lem1614134)). Qed.
Lemma lem1614136 (y : real) (x : real) (h1 : term518 y x) : term163 x.
Proof. exact (EQ_MP (@lem1614135 x) (@lem1614130 y x h1)). Qed.
Lemma lem1614137 (y : real) (x : real) (h1 : term518 y x) : term523 x.
Proof. exact (conj (@lem1614136 y x h1) (@lem1614115 y x h1)). Qed.
Lemma lem1614139 (x : real) (y : real) : term108 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1614140 (x : real) : term524 x.
Proof. exact (@lem1614139 (term153 x) x). Qed.
Lemma lem1614141 (y : real) (x : real) (h1 : term518 y x) : term284 x.
Proof. exact (@lem1614140 x (@lem1614137 y x h1)). Qed.
Lemma lem1614142 (x : real) : (term285 x) = (term286 x).
Proof. exact (@lem1483440 term113 x). Qed.
Lemma lem1614144 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1614145 : term115 = term6.
Proof. exact (@lem1614144 term64). Qed.
Lemma lem1614146 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1614147 : term116 = term15.
Proof. exact (MK_COMB (@lem1614146) (@lem1614145)). Qed.
Lemma lem1614148 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1614149 (x : real) : (term286 x) = (term14 x).
Proof. exact (MK_COMB (@lem1614147) (@lem1614148 x)). Qed.
Lemma lem1614150 (x : real) : (term285 x) = (term14 x).
Proof. exact (TRANS (@lem1614142 x) (@lem1614149 x)). Qed.
Lemma lem1614151 (x : real) : (term14 x) = term6.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1614152 (x : real) : (term285 x) = term6.
Proof. exact (TRANS (@lem1614150 x) (@lem1614151 x)). Qed.
Lemma lem1614153 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1614154 (x : real) : (term287 x) = term119.
Proof. exact (MK_COMB (@lem1614153) (@lem1614152 x)). Qed.
Lemma lem1614155 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614156 (x : real) : (term284 x) = term120.
Proof. exact (MK_COMB (@lem1614154 x) (@lem1614155)). Qed.
Lemma lem1614157 (y : real) (x : real) (h1 : term518 y x) : term120.
Proof. exact (EQ_MP (@lem1614156 x) (@lem1614141 y x h1)). Qed.
Lemma lem1614159 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614160 : term120 = term121.
Proof. exact (@lem1614159 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1614161 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1614162 : term120 = False.
Proof. exact (TRANS (@lem1614160) (@lem1614161)). Qed.
Lemma lem1614163 (y : real) (x : real) (h1 : term518 y x) : False.
Proof. exact (EQ_MP (@lem1614162) (@lem1614157 y x h1)). Qed.
Lemma lem1614164 (y : real) (x : real) (h1 : term525 y x) : term525 y x.
Proof. exact (h1). Qed.
Lemma lem1614165 (y : real) (x : real) (h1 : term525 y x) : term511 y x.
Proof. exact (proj2 (@lem1614164 y x h1)). Qed.
Lemma lem1614166 (y : real) (x : real) (h1 : term525 y x) : term163 x.
Proof. exact (proj1 (@lem1614164 y x h1)). Qed.
Lemma lem1614167 (y : real) (x : real) (h1 : term525 y x) : term489 y x.
Proof. exact (proj2 (@lem1614165 y x h1)). Qed.
Lemma lem1614169 (y : real) (x : real) (h1 : term525 y x) : term228 y x.
Proof. exact (proj2 (@lem1614167 y x h1)). Qed.
Lemma lem1614171 (y : real) (x : real) (h1 : term525 y x) : term216 y x.
Proof. exact (proj2 (@lem1614169 y x h1)). Qed.
Lemma lem1614173 (y : real) (x : real) (h1 : term525 y x) : term190 x.
Proof. exact (proj2 (@lem1614171 y x h1)). Qed.
Lemma lem1614176 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614177 : term92 = term93.
Proof. exact (@lem1614176 (NUMERAL 0) term64). Qed.
Lemma lem1614178 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1614179 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1614180 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1614179 h1) (fun h1 : term93 = True => @lem1614178)). Qed.
Lemma lem1614181 : term93 = True.
Proof. exact (EQ_MP (@lem1614180) (@lem1614178)). Qed.
Lemma lem1614182 : term92 = True.
Proof. exact (TRANS (@lem1614177) (@lem1614181)). Qed.
Lemma lem1614183 : True = term92.
Proof. exact (SYM (@lem1614182)). Qed.
Lemma lem1614184 : term92.
Proof. exact (EQ_MP (@lem1614183) (@lem0)). Qed.
Lemma lem1614185 (y : real) (x : real) (h1 : term525 y x) : term519 x.
Proof. exact (conj (@lem1614184) (@lem1614173 y x h1)). Qed.
Lemma lem1614187 (x : real) (y : real) : term96 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1614188 (x : real) : term520 x.
Proof. exact (@lem1614187 term98 x). Qed.
Lemma lem1614189 (y : real) (x : real) (h1 : term525 y x) : term521 x.
Proof. exact (@lem1614188 x (@lem1614185 y x h1)). Qed.
Lemma lem1614190 (x : real) : (term275 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1614191 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1614192 (x : real) : (term522 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1614191) (@lem1614190 x)). Qed.
Lemma lem1614193 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614194 (x : real) : (term521 x) = (term190 x).
Proof. exact (MK_COMB (@lem1614192 x) (@lem1614193)). Qed.
Lemma lem1614195 (y : real) (x : real) (h1 : term525 y x) : term190 x.
Proof. exact (EQ_MP (@lem1614194 x) (@lem1614189 y x h1)). Qed.
Lemma lem1614197 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614198 : term92 = term93.
Proof. exact (@lem1614197 (NUMERAL 0) term64). Qed.
Lemma lem1614199 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1614200 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1614201 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1614200 h1) (fun h1 : term93 = True => @lem1614199)). Qed.
Lemma lem1614202 : term93 = True.
Proof. exact (EQ_MP (@lem1614201) (@lem1614199)). Qed.
Lemma lem1614203 : term92 = True.
Proof. exact (TRANS (@lem1614198) (@lem1614202)). Qed.
Lemma lem1614204 : True = term92.
Proof. exact (SYM (@lem1614203)). Qed.
Lemma lem1614205 : term92.
Proof. exact (EQ_MP (@lem1614204) (@lem0)). Qed.
Lemma lem1614206 (y : real) (x : real) (h1 : term525 y x) : term277 x.
Proof. exact (conj (@lem1614205) (@lem1614166 y x h1)). Qed.
Lemma lem1614208 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1614209 (x : real) : term278 x.
Proof. exact (@lem1614208 term98 (term153 x)). Qed.
Lemma lem1614210 (y : real) (x : real) (h1 : term525 y x) : term279 x.
Proof. exact (@lem1614209 x (@lem1614206 y x h1)). Qed.
Lemma lem1614211 (x : real) : (term280 x) = (term153 x).
Proof. exact (@lem1483460 (term153 x)). Qed.
Lemma lem1614212 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1614213 (x : real) : (term281 x) = (term162 x).
Proof. exact (MK_COMB (@lem1614212) (@lem1614211 x)). Qed.
Lemma lem1614214 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614215 (x : real) : (term279 x) = (term163 x).
Proof. exact (MK_COMB (@lem1614213 x) (@lem1614214)). Qed.
Lemma lem1614216 (y : real) (x : real) (h1 : term525 y x) : term163 x.
Proof. exact (EQ_MP (@lem1614215 x) (@lem1614210 y x h1)). Qed.
Lemma lem1614217 (y : real) (x : real) (h1 : term525 y x) : term523 x.
Proof. exact (conj (@lem1614216 y x h1) (@lem1614195 y x h1)). Qed.
Lemma lem1614219 (x : real) (y : real) : term108 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1614220 (x : real) : term524 x.
Proof. exact (@lem1614219 (term153 x) x). Qed.
Lemma lem1614221 (y : real) (x : real) (h1 : term525 y x) : term284 x.
Proof. exact (@lem1614220 x (@lem1614217 y x h1)). Qed.
Lemma lem1614222 (x : real) : (term285 x) = (term286 x).
Proof. exact (@lem1483440 term113 x). Qed.
Lemma lem1614224 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1614225 : term115 = term6.
Proof. exact (@lem1614224 term64). Qed.
Lemma lem1614226 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1614227 : term116 = term15.
Proof. exact (MK_COMB (@lem1614226) (@lem1614225)). Qed.
Lemma lem1614228 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1614229 (x : real) : (term286 x) = (term14 x).
Proof. exact (MK_COMB (@lem1614227) (@lem1614228 x)). Qed.
Lemma lem1614230 (x : real) : (term285 x) = (term14 x).
Proof. exact (TRANS (@lem1614222 x) (@lem1614229 x)). Qed.
Lemma lem1614231 (x : real) : (term14 x) = term6.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1614232 (x : real) : (term285 x) = term6.
Proof. exact (TRANS (@lem1614230 x) (@lem1614231 x)). Qed.
Lemma lem1614233 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1614234 (x : real) : (term287 x) = term119.
Proof. exact (MK_COMB (@lem1614233) (@lem1614232 x)). Qed.
Lemma lem1614235 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614236 (x : real) : (term284 x) = term120.
Proof. exact (MK_COMB (@lem1614234 x) (@lem1614235)). Qed.
Lemma lem1614237 (y : real) (x : real) (h1 : term525 y x) : term120.
Proof. exact (EQ_MP (@lem1614236 x) (@lem1614221 y x h1)). Qed.
Lemma lem1614239 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614240 : term120 = term121.
Proof. exact (@lem1614239 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1614241 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1614242 : term120 = False.
Proof. exact (TRANS (@lem1614240) (@lem1614241)). Qed.
Lemma lem1614243 (y : real) (x : real) (h1 : term525 y x) : False.
Proof. exact (EQ_MP (@lem1614242) (@lem1614237 y x h1)). Qed.
Lemma lem1614244 (y : real) (x : real) (h1 : term509 y x) : False.
Proof. exact (or_elim (@lem1614083 y x h1) (fun h0 : term518 y x => @lem1614163 y x h0) (fun h0 : term525 y x => @lem1614243 y x h0)). Qed.
Lemma lem1614245 (x : real) (y : real) (h1 : term505 x y) : term505 x y.
Proof. exact (h1). Qed.
Lemma lem1614246 (x : real) (y : real) (h1 : term526 x y) : term526 x y.
Proof. exact (h1). Qed.
Lemma lem1614247 (x : real) (y : real) (h1 : term526 x y) : term506 x y.
Proof. exact (proj2 (@lem1614246 x y h1)). Qed.
Lemma lem1614249 (x : real) (y : real) (h1 : term526 x y) : term484 x y.
Proof. exact (proj2 (@lem1614247 x y h1)). Qed.
Lemma lem1614250 (x : real) (y : real) (h1 : term526 x y) : term163 y.
Proof. exact (proj1 (@lem1614247 x y h1)). Qed.
Lemma lem1614251 (x : real) (y : real) (h1 : term526 x y) : term344 x y.
Proof. exact (proj2 (@lem1614249 x y h1)). Qed.
Lemma lem1614253 (x : real) (y : real) (h1 : term526 x y) : term216 x y.
Proof. exact (proj2 (@lem1614251 x y h1)). Qed.
Lemma lem1614255 (x : real) (y : real) (h1 : term526 x y) : term190 y.
Proof. exact (proj2 (@lem1614253 x y h1)). Qed.
Lemma lem1614258 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614259 : term92 = term93.
Proof. exact (@lem1614258 (NUMERAL 0) term64). Qed.
Lemma lem1614260 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1614261 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1614262 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1614261 h1) (fun h1 : term93 = True => @lem1614260)). Qed.
Lemma lem1614263 : term93 = True.
Proof. exact (EQ_MP (@lem1614262) (@lem1614260)). Qed.
Lemma lem1614264 : term92 = True.
Proof. exact (TRANS (@lem1614259) (@lem1614263)). Qed.
Lemma lem1614265 : True = term92.
Proof. exact (SYM (@lem1614264)). Qed.
Lemma lem1614266 : term92.
Proof. exact (EQ_MP (@lem1614265) (@lem0)). Qed.
Lemma lem1614267 (x : real) (y : real) (h1 : term526 x y) : term519 y.
Proof. exact (conj (@lem1614266) (@lem1614255 x y h1)). Qed.
Lemma lem1614269 (x : real) (y : real) : term96 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1614270 (y : real) : term520 y.
Proof. exact (@lem1614269 term98 y). Qed.
Lemma lem1614271 (x : real) (y : real) (h1 : term526 x y) : term521 y.
Proof. exact (@lem1614270 y (@lem1614267 x y h1)). Qed.
Lemma lem1614272 (y : real) : (term275 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1614273 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1614274 (y : real) : (term522 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1614273) (@lem1614272 y)). Qed.
Lemma lem1614275 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614276 (y : real) : (term521 y) = (term190 y).
Proof. exact (MK_COMB (@lem1614274 y) (@lem1614275)). Qed.
Lemma lem1614277 (x : real) (y : real) (h1 : term526 x y) : term190 y.
Proof. exact (EQ_MP (@lem1614276 y) (@lem1614271 x y h1)). Qed.
Lemma lem1614279 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614280 : term92 = term93.
Proof. exact (@lem1614279 (NUMERAL 0) term64). Qed.
Lemma lem1614281 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1614282 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1614283 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1614282 h1) (fun h1 : term93 = True => @lem1614281)). Qed.
Lemma lem1614284 : term93 = True.
Proof. exact (EQ_MP (@lem1614283) (@lem1614281)). Qed.
Lemma lem1614285 : term92 = True.
Proof. exact (TRANS (@lem1614280) (@lem1614284)). Qed.
Lemma lem1614286 : True = term92.
Proof. exact (SYM (@lem1614285)). Qed.
Lemma lem1614287 : term92.
Proof. exact (EQ_MP (@lem1614286) (@lem0)). Qed.
Lemma lem1614288 (x : real) (y : real) (h1 : term526 x y) : term277 y.
Proof. exact (conj (@lem1614287) (@lem1614250 x y h1)). Qed.
Lemma lem1614290 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1614291 (y : real) : term278 y.
Proof. exact (@lem1614290 term98 (term153 y)). Qed.
Lemma lem1614292 (x : real) (y : real) (h1 : term526 x y) : term279 y.
Proof. exact (@lem1614291 y (@lem1614288 x y h1)). Qed.
Lemma lem1614293 (y : real) : (term280 y) = (term153 y).
Proof. exact (@lem1483460 (term153 y)). Qed.
Lemma lem1614294 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1614295 (y : real) : (term281 y) = (term162 y).
Proof. exact (MK_COMB (@lem1614294) (@lem1614293 y)). Qed.
Lemma lem1614296 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614297 (y : real) : (term279 y) = (term163 y).
Proof. exact (MK_COMB (@lem1614295 y) (@lem1614296)). Qed.
Lemma lem1614298 (x : real) (y : real) (h1 : term526 x y) : term163 y.
Proof. exact (EQ_MP (@lem1614297 y) (@lem1614292 x y h1)). Qed.
Lemma lem1614299 (x : real) (y : real) (h1 : term526 x y) : term523 y.
Proof. exact (conj (@lem1614298 x y h1) (@lem1614277 x y h1)). Qed.
Lemma lem1614301 (x : real) (y : real) : term108 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1614302 (y : real) : term524 y.
Proof. exact (@lem1614301 (term153 y) y). Qed.
Lemma lem1614303 (x : real) (y : real) (h1 : term526 x y) : term284 y.
Proof. exact (@lem1614302 y (@lem1614299 x y h1)). Qed.
Lemma lem1614304 (y : real) : (term285 y) = (term286 y).
Proof. exact (@lem1483440 term113 y). Qed.
Lemma lem1614306 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1614307 : term115 = term6.
Proof. exact (@lem1614306 term64). Qed.
Lemma lem1614308 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1614309 : term116 = term15.
Proof. exact (MK_COMB (@lem1614308) (@lem1614307)). Qed.
Lemma lem1614310 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1614311 (y : real) : (term286 y) = (term14 y).
Proof. exact (MK_COMB (@lem1614309) (@lem1614310 y)). Qed.
Lemma lem1614312 (y : real) : (term285 y) = (term14 y).
Proof. exact (TRANS (@lem1614304 y) (@lem1614311 y)). Qed.
Lemma lem1614313 (y : real) : (term14 y) = term6.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1614314 (y : real) : (term285 y) = term6.
Proof. exact (TRANS (@lem1614312 y) (@lem1614313 y)). Qed.
Lemma lem1614315 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1614316 (y : real) : (term287 y) = term119.
Proof. exact (MK_COMB (@lem1614315) (@lem1614314 y)). Qed.
Lemma lem1614317 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614318 (y : real) : (term284 y) = term120.
Proof. exact (MK_COMB (@lem1614316 y) (@lem1614317)). Qed.
Lemma lem1614319 (x : real) (y : real) (h1 : term526 x y) : term120.
Proof. exact (EQ_MP (@lem1614318 y) (@lem1614303 x y h1)). Qed.
Lemma lem1614321 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614322 : term120 = term121.
Proof. exact (@lem1614321 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1614323 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1614324 : term120 = False.
Proof. exact (TRANS (@lem1614322) (@lem1614323)). Qed.
Lemma lem1614325 (x : real) (y : real) (h1 : term526 x y) : False.
Proof. exact (EQ_MP (@lem1614324) (@lem1614319 x y h1)). Qed.
Lemma lem1614326 (x : real) (y : real) (h1 : term527 x y) : term527 x y.
Proof. exact (h1). Qed.
Lemma lem1614327 (x : real) (y : real) (h1 : term527 x y) : term507 x y.
Proof. exact (proj2 (@lem1614326 x y h1)). Qed.
Lemma lem1614329 (x : real) (y : real) (h1 : term527 x y) : term485 x y.
Proof. exact (proj2 (@lem1614327 x y h1)). Qed.
Lemma lem1614330 (x : real) (y : real) (h1 : term527 x y) : term163 y.
Proof. exact (proj1 (@lem1614327 x y h1)). Qed.
Lemma lem1614331 (x : real) (y : real) (h1 : term527 x y) : term229 x y.
Proof. exact (proj2 (@lem1614329 x y h1)). Qed.
Lemma lem1614333 (x : real) (y : real) (h1 : term527 x y) : term217 y.
Proof. exact (proj2 (@lem1614331 x y h1)). Qed.
Lemma lem1614335 (x : real) (y : real) (h1 : term527 x y) : term190 y.
Proof. exact (proj2 (@lem1614333 x y h1)). Qed.
Lemma lem1614338 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614339 : term92 = term93.
Proof. exact (@lem1614338 (NUMERAL 0) term64). Qed.
Lemma lem1614340 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1614341 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1614342 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1614341 h1) (fun h1 : term93 = True => @lem1614340)). Qed.
Lemma lem1614343 : term93 = True.
Proof. exact (EQ_MP (@lem1614342) (@lem1614340)). Qed.
Lemma lem1614344 : term92 = True.
Proof. exact (TRANS (@lem1614339) (@lem1614343)). Qed.
Lemma lem1614345 : True = term92.
Proof. exact (SYM (@lem1614344)). Qed.
Lemma lem1614346 : term92.
Proof. exact (EQ_MP (@lem1614345) (@lem0)). Qed.
Lemma lem1614347 (x : real) (y : real) (h1 : term527 x y) : term519 y.
Proof. exact (conj (@lem1614346) (@lem1614335 x y h1)). Qed.
Lemma lem1614349 (x : real) (y : real) : term96 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1614350 (y : real) : term520 y.
Proof. exact (@lem1614349 term98 y). Qed.
Lemma lem1614351 (x : real) (y : real) (h1 : term527 x y) : term521 y.
Proof. exact (@lem1614350 y (@lem1614347 x y h1)). Qed.
Lemma lem1614352 (y : real) : (term275 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1614353 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1614354 (y : real) : (term522 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1614353) (@lem1614352 y)). Qed.
Lemma lem1614355 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614356 (y : real) : (term521 y) = (term190 y).
Proof. exact (MK_COMB (@lem1614354 y) (@lem1614355)). Qed.
Lemma lem1614357 (x : real) (y : real) (h1 : term527 x y) : term190 y.
Proof. exact (EQ_MP (@lem1614356 y) (@lem1614351 x y h1)). Qed.
Lemma lem1614359 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614360 : term92 = term93.
Proof. exact (@lem1614359 (NUMERAL 0) term64). Qed.
Lemma lem1614361 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1614362 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1614363 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1614362 h1) (fun h1 : term93 = True => @lem1614361)). Qed.
Lemma lem1614364 : term93 = True.
Proof. exact (EQ_MP (@lem1614363) (@lem1614361)). Qed.
Lemma lem1614365 : term92 = True.
Proof. exact (TRANS (@lem1614360) (@lem1614364)). Qed.
Lemma lem1614366 : True = term92.
Proof. exact (SYM (@lem1614365)). Qed.
Lemma lem1614367 : term92.
Proof. exact (EQ_MP (@lem1614366) (@lem0)). Qed.
Lemma lem1614368 (x : real) (y : real) (h1 : term527 x y) : term277 y.
Proof. exact (conj (@lem1614367) (@lem1614330 x y h1)). Qed.
Lemma lem1614370 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1614371 (y : real) : term278 y.
Proof. exact (@lem1614370 term98 (term153 y)). Qed.
Lemma lem1614372 (x : real) (y : real) (h1 : term527 x y) : term279 y.
Proof. exact (@lem1614371 y (@lem1614368 x y h1)). Qed.
Lemma lem1614373 (y : real) : (term280 y) = (term153 y).
Proof. exact (@lem1483460 (term153 y)). Qed.
Lemma lem1614374 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1614375 (y : real) : (term281 y) = (term162 y).
Proof. exact (MK_COMB (@lem1614374) (@lem1614373 y)). Qed.
Lemma lem1614376 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614377 (y : real) : (term279 y) = (term163 y).
Proof. exact (MK_COMB (@lem1614375 y) (@lem1614376)). Qed.
Lemma lem1614378 (x : real) (y : real) (h1 : term527 x y) : term163 y.
Proof. exact (EQ_MP (@lem1614377 y) (@lem1614372 x y h1)). Qed.
Lemma lem1614379 (x : real) (y : real) (h1 : term527 x y) : term523 y.
Proof. exact (conj (@lem1614378 x y h1) (@lem1614357 x y h1)). Qed.
Lemma lem1614381 (x : real) (y : real) : term108 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1614382 (y : real) : term524 y.
Proof. exact (@lem1614381 (term153 y) y). Qed.
Lemma lem1614383 (x : real) (y : real) (h1 : term527 x y) : term284 y.
Proof. exact (@lem1614382 y (@lem1614379 x y h1)). Qed.
Lemma lem1614384 (y : real) : (term285 y) = (term286 y).
Proof. exact (@lem1483440 term113 y). Qed.
Lemma lem1614386 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1614387 : term115 = term6.
Proof. exact (@lem1614386 term64). Qed.
Lemma lem1614388 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1614389 : term116 = term15.
Proof. exact (MK_COMB (@lem1614388) (@lem1614387)). Qed.
Lemma lem1614390 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1614391 (y : real) : (term286 y) = (term14 y).
Proof. exact (MK_COMB (@lem1614389) (@lem1614390 y)). Qed.
Lemma lem1614392 (y : real) : (term285 y) = (term14 y).
Proof. exact (TRANS (@lem1614384 y) (@lem1614391 y)). Qed.
Lemma lem1614393 (y : real) : (term14 y) = term6.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1614394 (y : real) : (term285 y) = term6.
Proof. exact (TRANS (@lem1614392 y) (@lem1614393 y)). Qed.
Lemma lem1614395 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1614396 (y : real) : (term287 y) = term119.
Proof. exact (MK_COMB (@lem1614395) (@lem1614394 y)). Qed.
Lemma lem1614397 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614398 (y : real) : (term284 y) = term120.
Proof. exact (MK_COMB (@lem1614396 y) (@lem1614397)). Qed.
Lemma lem1614399 (x : real) (y : real) (h1 : term527 x y) : term120.
Proof. exact (EQ_MP (@lem1614398 y) (@lem1614383 x y h1)). Qed.
Lemma lem1614401 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614402 : term120 = term121.
Proof. exact (@lem1614401 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1614403 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1614404 : term120 = False.
Proof. exact (TRANS (@lem1614402) (@lem1614403)). Qed.
Lemma lem1614405 (x : real) (y : real) (h1 : term527 x y) : False.
Proof. exact (EQ_MP (@lem1614404) (@lem1614399 x y h1)). Qed.
Lemma lem1614406 (x : real) (y : real) (h1 : term505 x y) : False.
Proof. exact (or_elim (@lem1614245 x y h1) (fun h0 : term526 x y => @lem1614325 x y h0) (fun h0 : term527 x y => @lem1614405 x y h0)). Qed.
Lemma lem1614407 (x : real) (y : real) (h1 : term514 x y) : False.
Proof. exact (or_elim (@lem1614082 x y h1) (fun h0 : term509 y x => @lem1614244 y x h0) (fun h0 : term505 x y => @lem1614406 x y h0)). Qed.
Lemma lem1614408 (x : real) (y : real) (h1 : term499 x y) : term499 x y.
Proof. exact (h1). Qed.
Lemma lem1614409 (x : real) (y : real) (h1 : term528 x y) : term528 x y.
Proof. exact (h1). Qed.
Lemma lem1614410 (x : real) (y : real) (h1 : term528 x y) : term500 x y.
Proof. exact (proj2 (@lem1614409 x y h1)). Qed.
Lemma lem1614411 (x : real) (y : real) (h1 : term528 x y) : term163 x.
Proof. exact (proj1 (@lem1614409 x y h1)). Qed.
Lemma lem1614412 (x : real) (y : real) (h1 : term528 x y) : term478 x y.
Proof. exact (proj2 (@lem1614410 x y h1)). Qed.
Lemma lem1614414 (x : real) (y : real) (h1 : term528 x y) : term461 x y.
Proof. exact (proj2 (@lem1614412 x y h1)). Qed.
Lemma lem1614416 (x : real) (y : real) (h1 : term528 x y) : term428 x y.
Proof. exact (proj2 (@lem1614414 x y h1)). Qed.
Lemma lem1614419 (x : real) (y : real) (h1 : term528 x y) : term67 x.
Proof. exact (proj1 (@lem1614416 x y h1)). Qed.
Lemma lem1614421 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614422 : term92 = term93.
Proof. exact (@lem1614421 (NUMERAL 0) term64). Qed.
Lemma lem1614423 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1614424 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1614425 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1614424 h1) (fun h1 : term93 = True => @lem1614423)). Qed.
Lemma lem1614426 : term93 = True.
Proof. exact (EQ_MP (@lem1614425) (@lem1614423)). Qed.
Lemma lem1614427 : term92 = True.
Proof. exact (TRANS (@lem1614422) (@lem1614426)). Qed.
Lemma lem1614428 : True = term92.
Proof. exact (SYM (@lem1614427)). Qed.
Lemma lem1614429 : term92.
Proof. exact (EQ_MP (@lem1614428) (@lem0)). Qed.
Lemma lem1614430 (x : real) (y : real) (h1 : term528 x y) : term272 x.
Proof. exact (conj (@lem1614429) (@lem1614419 x y h1)). Qed.
Lemma lem1614432 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1614433 (x : real) : term273 x.
Proof. exact (@lem1614432 term98 x). Qed.
Lemma lem1614434 (x : real) (y : real) (h1 : term528 x y) : term274 x.
Proof. exact (@lem1614433 x (@lem1614430 x y h1)). Qed.
Lemma lem1614435 (x : real) : (term275 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1614436 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1614437 (x : real) : (term276 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1614436) (@lem1614435 x)). Qed.
Lemma lem1614438 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614439 (x : real) : (term274 x) = (term67 x).
Proof. exact (MK_COMB (@lem1614437 x) (@lem1614438)). Qed.
Lemma lem1614440 (x : real) (y : real) (h1 : term528 x y) : term67 x.
Proof. exact (EQ_MP (@lem1614439 x) (@lem1614434 x y h1)). Qed.
Lemma lem1614442 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614443 : term92 = term93.
Proof. exact (@lem1614442 (NUMERAL 0) term64). Qed.
Lemma lem1614444 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1614445 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1614446 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1614445 h1) (fun h1 : term93 = True => @lem1614444)). Qed.
Lemma lem1614447 : term93 = True.
Proof. exact (EQ_MP (@lem1614446) (@lem1614444)). Qed.
Lemma lem1614448 : term92 = True.
Proof. exact (TRANS (@lem1614443) (@lem1614447)). Qed.
Lemma lem1614449 : True = term92.
Proof. exact (SYM (@lem1614448)). Qed.
Lemma lem1614450 : term92.
Proof. exact (EQ_MP (@lem1614449) (@lem0)). Qed.
Lemma lem1614451 (x : real) (y : real) (h1 : term528 x y) : term277 x.
Proof. exact (conj (@lem1614450) (@lem1614411 x y h1)). Qed.
Lemma lem1614453 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1614454 (x : real) : term278 x.
Proof. exact (@lem1614453 term98 (term153 x)). Qed.
Lemma lem1614455 (x : real) (y : real) (h1 : term528 x y) : term279 x.
Proof. exact (@lem1614454 x (@lem1614451 x y h1)). Qed.
Lemma lem1614456 (x : real) : (term280 x) = (term153 x).
Proof. exact (@lem1483460 (term153 x)). Qed.
Lemma lem1614457 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1614458 (x : real) : (term281 x) = (term162 x).
Proof. exact (MK_COMB (@lem1614457) (@lem1614456 x)). Qed.
Lemma lem1614459 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614460 (x : real) : (term279 x) = (term163 x).
Proof. exact (MK_COMB (@lem1614458 x) (@lem1614459)). Qed.
Lemma lem1614461 (x : real) (y : real) (h1 : term528 x y) : term163 x.
Proof. exact (EQ_MP (@lem1614460 x) (@lem1614455 x y h1)). Qed.
Lemma lem1614462 (x : real) (y : real) (h1 : term528 x y) : term282 x.
Proof. exact (conj (@lem1614461 x y h1) (@lem1614440 x y h1)). Qed.
Lemma lem1614464 (x : real) (y : real) : term265 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1614465 (x : real) : term283 x.
Proof. exact (@lem1614464 (term153 x) x). Qed.
Lemma lem1614466 (x : real) (y : real) (h1 : term528 x y) : term284 x.
Proof. exact (@lem1614465 x (@lem1614462 x y h1)). Qed.
Lemma lem1614467 (x : real) : (term285 x) = (term286 x).
Proof. exact (@lem1483440 term113 x). Qed.
Lemma lem1614469 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1614470 : term115 = term6.
Proof. exact (@lem1614469 term64). Qed.
Lemma lem1614471 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1614472 : term116 = term15.
Proof. exact (MK_COMB (@lem1614471) (@lem1614470)). Qed.
Lemma lem1614473 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1614474 (x : real) : (term286 x) = (term14 x).
Proof. exact (MK_COMB (@lem1614472) (@lem1614473 x)). Qed.
Lemma lem1614475 (x : real) : (term285 x) = (term14 x).
Proof. exact (TRANS (@lem1614467 x) (@lem1614474 x)). Qed.
Lemma lem1614476 (x : real) : (term14 x) = term6.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1614477 (x : real) : (term285 x) = term6.
Proof. exact (TRANS (@lem1614475 x) (@lem1614476 x)). Qed.
Lemma lem1614478 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1614479 (x : real) : (term287 x) = term119.
Proof. exact (MK_COMB (@lem1614478) (@lem1614477 x)). Qed.
Lemma lem1614480 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614481 (x : real) : (term284 x) = term120.
Proof. exact (MK_COMB (@lem1614479 x) (@lem1614480)). Qed.
Lemma lem1614482 (x : real) (y : real) (h1 : term528 x y) : term120.
Proof. exact (EQ_MP (@lem1614481 x) (@lem1614466 x y h1)). Qed.
Lemma lem1614484 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614485 : term120 = term121.
Proof. exact (@lem1614484 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1614486 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1614487 : term120 = False.
Proof. exact (TRANS (@lem1614485) (@lem1614486)). Qed.
Lemma lem1614488 (x : real) (y : real) (h1 : term528 x y) : False.
Proof. exact (EQ_MP (@lem1614487) (@lem1614482 x y h1)). Qed.
Lemma lem1614489 (x : real) (y : real) (h1 : term529 x y) : term529 x y.
Proof. exact (h1). Qed.
Lemma lem1614490 (x : real) (y : real) (h1 : term529 x y) : term501 x y.
Proof. exact (proj2 (@lem1614489 x y h1)). Qed.
Lemma lem1614492 (x : real) (y : real) (h1 : term529 x y) : term479 x y.
Proof. exact (proj2 (@lem1614490 x y h1)). Qed.
Lemma lem1614494 (x : real) (y : real) (h1 : term529 x y) : term225 x y.
Proof. exact (proj2 (@lem1614492 x y h1)). Qed.
Lemma lem1614495 (x : real) (y : real) (h1 : term529 x y) : term76 x y.
Proof. exact (proj1 (@lem1614492 x y h1)). Qed.
Lemma lem1614497 (x : real) (y : real) (h1 : term529 x y) : term84 x y.
Proof. exact (proj1 (@lem1614494 x y h1)). Qed.
Lemma lem1614501 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614502 : term92 = term93.
Proof. exact (@lem1614501 (NUMERAL 0) term64). Qed.
Lemma lem1614503 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1614504 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1614505 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1614504 h1) (fun h1 : term93 = True => @lem1614503)). Qed.
Lemma lem1614506 : term93 = True.
Proof. exact (EQ_MP (@lem1614505) (@lem1614503)). Qed.
Lemma lem1614507 : term92 = True.
Proof. exact (TRANS (@lem1614502) (@lem1614506)). Qed.
Lemma lem1614508 : True = term92.
Proof. exact (SYM (@lem1614507)). Qed.
Lemma lem1614509 : term92.
Proof. exact (EQ_MP (@lem1614508) (@lem0)). Qed.
Lemma lem1614510 (x : real) (y : real) (h1 : term529 x y) : term95 x y.
Proof. exact (conj (@lem1614509) (@lem1614497 x y h1)). Qed.
Lemma lem1614512 (x : real) (y : real) : term96 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1614513 (x : real) (y : real) : term97 x y.
Proof. exact (@lem1614512 term98 (term81 x y)). Qed.
Lemma lem1614514 (x : real) (y : real) (h1 : term529 x y) : term99 x y.
Proof. exact (@lem1614513 x y (@lem1614510 x y h1)). Qed.
Lemma lem1614515 (x : real) (y : real) : (term100 x y) = (term81 x y).
Proof. exact (@lem1483460 (term81 x y)). Qed.
Lemma lem1614516 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1614517 (x : real) (y : real) : (term101 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1614516) (@lem1614515 x y)). Qed.
Lemma lem1614518 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614519 (x : real) (y : real) : (term99 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1614517 x y) (@lem1614518)). Qed.
Lemma lem1614520 (x : real) (y : real) (h1 : term529 x y) : term84 x y.
Proof. exact (EQ_MP (@lem1614519 x y) (@lem1614514 x y h1)). Qed.
Lemma lem1614522 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614523 : term92 = term93.
Proof. exact (@lem1614522 (NUMERAL 0) term64). Qed.
Lemma lem1614524 : term94 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1614525 (h1 : term94 = (BIT1 0)) : term93 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1614526 : (term94 = (BIT1 0)) = (term93 = True).
Proof. exact (prop_ext (fun h1 : term94 = (BIT1 0) => @lem1614525 h1) (fun h1 : term93 = True => @lem1614524)). Qed.
Lemma lem1614527 : term93 = True.
Proof. exact (EQ_MP (@lem1614526) (@lem1614524)). Qed.
Lemma lem1614528 : term92 = True.
Proof. exact (TRANS (@lem1614523) (@lem1614527)). Qed.
Lemma lem1614529 : True = term92.
Proof. exact (SYM (@lem1614528)). Qed.
Lemma lem1614530 : term92.
Proof. exact (EQ_MP (@lem1614529) (@lem0)). Qed.
Lemma lem1614531 (x : real) (y : real) (h1 : term529 x y) : term102 x y.
Proof. exact (conj (@lem1614530) (@lem1614495 x y h1)). Qed.
Lemma lem1614533 (x : real) (y : real) : term103 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1614534 (x : real) (y : real) : term104 x y.
Proof. exact (@lem1614533 term98 (real_mul x y)). Qed.
Lemma lem1614535 (x : real) (y : real) (h1 : term529 x y) : term105 x y.
Proof. exact (@lem1614534 x y (@lem1614531 x y h1)). Qed.
Lemma lem1614536 (x : real) (y : real) : (term106 x y) = (real_mul x y).
Proof. exact (@lem1483460 (real_mul x y)). Qed.
Lemma lem1614537 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1614538 (x : real) (y : real) : (term107 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1614537) (@lem1614536 x y)). Qed.
Lemma lem1614539 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614540 (x : real) (y : real) : (term105 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1614538 x y) (@lem1614539)). Qed.
Lemma lem1614541 (x : real) (y : real) (h1 : term529 x y) : term76 x y.
Proof. exact (EQ_MP (@lem1614540 x y) (@lem1614535 x y h1)). Qed.
Lemma lem1614542 (x : real) (y : real) (h1 : term529 x y) : term87 x y.
Proof. exact (conj (@lem1614541 x y h1) (@lem1614520 x y h1)). Qed.
Lemma lem1614544 (x : real) (y : real) : term108 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1614545 (x : real) (y : real) : term109 x y.
Proof. exact (@lem1614544 (real_mul x y) (term81 x y)). Qed.
Lemma lem1614546 (x : real) (y : real) (h1 : term529 x y) : term110 x y.
Proof. exact (@lem1614545 x y (@lem1614542 x y h1)). Qed.
Lemma lem1614547 (x : real) (y : real) : (term111 x y) = (term112 x y).
Proof. exact (@lem1483442 term113 (real_mul x y)). Qed.
Lemma lem1614549 (m : nat) : (term114 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1614550 : term115 = term6.
Proof. exact (@lem1614549 term64). Qed.
Lemma lem1614551 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1614552 : term116 = term15.
Proof. exact (MK_COMB (@lem1614551) (@lem1614550)). Qed.
Lemma lem1614553 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1614554 (x : real) (y : real) : (term112 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem1614552) (@lem1614553 x y)). Qed.
Lemma lem1614555 (x : real) (y : real) : (term111 x y) = (term117 x y).
Proof. exact (TRANS (@lem1614547 x y) (@lem1614554 x y)). Qed.
Lemma lem1614556 (x : real) (y : real) : (term117 x y) = term6.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1614557 (x : real) (y : real) : (term111 x y) = term6.
Proof. exact (TRANS (@lem1614555 x y) (@lem1614556 x y)). Qed.
Lemma lem1614558 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1614559 (x : real) (y : real) : (term118 x y) = term119.
Proof. exact (MK_COMB (@lem1614558) (@lem1614557 x y)). Qed.
Lemma lem1614560 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1614561 (x : real) (y : real) : (term110 x y) = term120.
Proof. exact (MK_COMB (@lem1614559 x y) (@lem1614560)). Qed.
Lemma lem1614562 (x : real) (y : real) (h1 : term529 x y) : term120.
Proof. exact (EQ_MP (@lem1614561 x y) (@lem1614546 x y h1)). Qed.
Lemma lem1614564 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1614565 : term120 = term121.
Proof. exact (@lem1614564 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1614566 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1614567 : term120 = False.
Proof. exact (TRANS (@lem1614565) (@lem1614566)). Qed.
Lemma lem1614568 (x : real) (y : real) (h1 : term529 x y) : False.
Proof. exact (EQ_MP (@lem1614567) (@lem1614562 x y h1)). Qed.
Lemma lem1614569 (x : real) (y : real) (h1 : term499 x y) : False.
Proof. exact (or_elim (@lem1614408 x y h1) (fun h0 : term528 x y => @lem1614488 x y h0) (fun h0 : term529 x y => @lem1614568 x y h0)). Qed.
Lemma lem1614570 (x : real) (y : real) (h1 : term517 x y) : False.
Proof. exact (or_elim (@lem1614081 x y h1) (fun h0 : term514 x y => @lem1614407 x y h0) (fun h0 : term499 x y => @lem1614569 x y h0)). Qed.
Lemma lem1614572 (x : real) (y : real) (h1 : term517 x y) : term517 x y.
Proof. exact (h1). Qed.
Lemma lem1614573 (x : real) (y : real) (h1 : term517 x y) : (term517 x y) = False.
Proof. exact (prop_ext (fun h2 : term517 x y => @lem1614570 x y h1) (fun h2 : False => @lem1614572 x y h1)). Qed.
Lemma lem1614574 (x : real) (y : real) (h1 : term517 x y) : False.
Proof. exact (EQ_MP (@lem1614573 x y h1) (@lem1614572 x y h1)). Qed.
Lemma lem1614575 (x : real) (y : real) (h1 : term405 x y) : term405 x y.
Proof. exact (h1). Qed.
Lemma lem1614576 (x : real) (y : real) (h1 : term405 x y) : term517 x y.
Proof. exact (EQ_MP (@lem1614047 x y) (@lem1614575 x y h1)). Qed.
Lemma lem1614577 (x : real) (y : real) (h1 : term405 x y) : (term517 x y) = False.
Proof. exact (prop_ext (fun h2 : term517 x y => @lem1614574 x y h2) (fun h2 : False => @lem1614576 x y h1)). Qed.
Lemma lem1614578 (x : real) (y : real) (h1 : term405 x y) : False.
Proof. exact (EQ_MP (@lem1614577 x y h1) (@lem1614576 x y h1)). Qed.
Lemma lem1614579 (x : real) (y : real) : term530 x y.
Proof. exact (fun h0 : term405 x y => @lem1614578 x y h0). Qed.
Lemma lem1614580 (x : real) (y : real) : term531 x y.
Proof. exact (@lem1386578 (term532 x y)). Qed.
Lemma lem1614581 (x : real) (y : real) : term532 x y.
Proof. exact (@lem1614580 x y (@lem1614579 x y)). Qed.
Lemma lem1614582 (y : real) (x : real) (h1 : term9 x) : term406 x y.
Proof. exact (@lem1614581 x y (@lem1610563 x h1)). Qed.
Lemma lem1614583 (x : real) (y : real) (h1 : term9 x) (h2 : term9 y) : term402 x y.
Proof. exact (@lem1614582 y x h1 (@lem1610569 y h2)). Qed.
Lemma lem1614584 (y : real) (x : real) (h1 : term9 x) : term314 x y.
Proof. exact (@lem1613343 x y (@lem1610563 x h1)). Qed.
Lemma lem1614585 (y : real) (x : real) (h1 : term8 y) (h2 : term9 x) : term310 x y.
Proof. exact (@lem1614584 y x h2 (@lem1610568 y h1)). Qed.
Lemma lem1614586 (y : real) (x : real) (h1 : term8 x) : term151 x y.
Proof. exact (@lem1612448 x y (@lem1610562 x h1)). Qed.
Lemma lem1614587 (x : real) (y : real) (h1 : term8 x) (h2 : term9 y) : term147 x y.
Proof. exact (@lem1614586 y x h1 (@lem1610567 y h2)). Qed.
Lemma lem1614588 (y : real) (x : real) (h1 : term8 x) : term58 x y.
Proof. exact (@lem1611553 x y (@lem1610562 x h1)). Qed.
Lemma lem1614589 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : term54 x y.
Proof. exact (@lem1614588 y x h1 (@lem1610566 y h2)). Qed.
Lemma lem1614591 (y : real) (x : real) (h1 : term8 y) (h2 : term9 x) : (term18 x y) = (term39 x y).
Proof. exact (@lem1614585 y x h1 h2 (@lem1611283 y x h1 h2)). Qed.
Lemma lem1614592 (x : real) (y : real) (h1 : term8 x) (h2 : term9 y) : (term18 x y) = (term36 x y).
Proof. exact (@lem1614587 x y h1 h2 (@lem1611278 x y h1 h2)). Qed.
Lemma lem1614593 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : term18 x y.
Proof. exact (@lem1614589 x y h1 h2 (@lem1611273 x y h1 h2)). Qed.
Lemma lem1614594 (x : real) (y : real) (h1 : term9 x) (h2 : term9 y) : (term18 x y) = (term27 x y).
Proof. exact (@lem1614583 x y h1 h2 (@lem1611288 x y h1 h2)). Qed.
Lemma lem1614595 (y : real) (x : real) (h1 : term8 y) (h2 : term9 x) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1611233 x y h1) (@lem1614591 y x h1 h2)). Qed.
Lemma lem1614596 (x : real) (y : real) (h1 : term8 x) (h2 : term9 y) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1611088 y x h1) (@lem1614592 x y h1 h2)). Qed.
Lemma lem1614597 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1611034 x y h1 h2) (@lem1614593 x y h1 h2)). Qed.
Lemma lem1614598 (x : real) (y : real) (h1 : term9 x) (h2 : term9 y) : (term9 y) = ((term18 x y) = (term27 x y)).
Proof. exact (prop_ext (fun h3 : term9 y => @lem1614594 x y h1 h2) (fun h3 : (term18 x y) = (term27 x y) => @lem1610569 y h2)). Qed.
Lemma lem1614599 (x : real) (y : real) (h1 : term9 x) (h2 : term9 y) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1614598 x y h1 h2) (@lem1610569 y h2)). Qed.
Lemma lem1614600 (y : real) (x : real) (h1 : term8 y) (h2 : term9 x) : (term8 y) = ((term18 x y) = (term27 x y)).
Proof. exact (prop_ext (fun h3 : term8 y => @lem1614595 y x h1 h2) (fun h3 : (term18 x y) = (term27 x y) => @lem1610568 y h1)). Qed.
Lemma lem1614601 (y : real) (x : real) (h1 : term8 y) (h2 : term9 x) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1614600 y x h1 h2) (@lem1610568 y h1)). Qed.
Lemma lem1614602 (y : real) (x : real) (h1 : term7 y) (h2 : term9 x) : (term18 x y) = (term27 x y).
Proof. exact (or_elim (@lem1610556 y h1) (fun h0 : term8 y => @lem1614601 y x h0 h2) (fun h0 : term9 y => @lem1614599 x y h2 h0)). Qed.
Lemma lem1614603 (x : real) (y : real) (h1 : y = term6) : (y = term6) = ((term18 x y) = (term27 x y)).
Proof. exact (prop_ext (fun h2 : y = term6 => @lem1611181 x y h1) (fun h2 : (term18 x y) = (term27 x y) => @lem1610555 y h1)). Qed.
Lemma lem1614604 (x : real) (y : real) (h1 : y = term6) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1614603 x y h1) (@lem1610555 y h1)). Qed.
Lemma lem1614605 (y : real) (x : real) (h1 : term9 x) : (term18 x y) = (term27 x y).
Proof. exact (or_elim (@lem1610554 y) (fun h0 : y = term6 => @lem1614604 x y h0) (fun h0 : term7 y => @lem1614602 y x h0 h1)). Qed.
Lemma lem1614606 (x : real) (y : real) (h1 : term8 x) (h2 : term9 y) : (term9 y) = ((term18 x y) = (term27 x y)).
Proof. exact (prop_ext (fun h3 : term9 y => @lem1614596 x y h1 h2) (fun h3 : (term18 x y) = (term27 x y) => @lem1610567 y h2)). Qed.
Lemma lem1614607 (x : real) (y : real) (h1 : term8 x) (h2 : term9 y) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1614606 x y h1 h2) (@lem1610567 y h2)). Qed.
Lemma lem1614608 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : (term8 y) = ((term18 x y) = (term27 x y)).
Proof. exact (prop_ext (fun h3 : term8 y => @lem1614597 x y h1 h2) (fun h3 : (term18 x y) = (term27 x y) => @lem1610566 y h2)). Qed.
Lemma lem1614609 (x : real) (y : real) (h1 : term8 x) (h2 : term8 y) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1614608 x y h1 h2) (@lem1610566 y h2)). Qed.
Lemma lem1614610 (y : real) (x : real) (h1 : term7 y) (h2 : term8 x) : (term18 x y) = (term27 x y).
Proof. exact (or_elim (@lem1610556 y h1) (fun h0 : term8 y => @lem1614609 x y h2 h0) (fun h0 : term9 y => @lem1614607 x y h2 h0)). Qed.
Lemma lem1614611 (y : real) (x : real) (h1 : y = term6) (h2 : term8 x) : (y = term6) = ((term18 x y) = (term27 x y)).
Proof. exact (prop_ext (fun h3 : y = term6 => @lem1610977 y x h1 h2) (fun h3 : (term18 x y) = (term27 x y) => @lem1610555 y h1)). Qed.
Lemma lem1614612 (y : real) (x : real) (h1 : y = term6) (h2 : term8 x) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1614611 y x h1 h2) (@lem1610555 y h1)). Qed.
Lemma lem1614613 (y : real) (x : real) (h1 : term8 x) : (term18 x y) = (term27 x y).
Proof. exact (or_elim (@lem1610554 y) (fun h0 : y = term6 => @lem1614612 y x h0 h1) (fun h0 : term7 y => @lem1614610 y x h0 h1)). Qed.
Lemma lem1614614 (x : real) (y : real) (h1 : x = term6) (h2 : term8 y) : (term8 y) = ((term18 x y) = (term27 x y)).
Proof. exact (prop_ext (fun h3 : term8 y => @lem1610783 x y h1 h2) (fun h3 : (term18 x y) = (term27 x y) => @lem1610564 y h2)). Qed.
Lemma lem1614615 (x : real) (y : real) (h1 : x = term6) (h2 : term8 y) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1614614 x y h1 h2) (@lem1610564 y h2)). Qed.
Lemma lem1614616 (x : real) (y : real) (h1 : x = term6) (h2 : term7 y) : (term18 x y) = (term27 x y).
Proof. exact (or_elim (@lem1610556 y h2) (fun h0 : term8 y => @lem1614615 x y h1 h0) (fun h0 : term9 y => @lem1610883 y x h1)). Qed.
Lemma lem1614617 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (y = term6) = ((term18 x y) = (term27 x y)).
Proof. exact (prop_ext (fun h3 : y = term6 => @lem1610684 x y h1 h2) (fun h3 : (term18 x y) = (term27 x y) => @lem1610555 y h2)). Qed.
Lemma lem1614618 (x : real) (y : real) (h1 : x = term6) (h2 : y = term6) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1614617 x y h1 h2) (@lem1610555 y h2)). Qed.
Lemma lem1614619 (y : real) (x : real) (h1 : x = term6) : (term18 x y) = (term27 x y).
Proof. exact (or_elim (@lem1610554 y) (fun h0 : y = term6 => @lem1614618 x y h1 h0) (fun h0 : term7 y => @lem1614616 x y h1 h0)). Qed.
Lemma lem1614620 (y : real) (x : real) (h1 : term9 x) : (term9 x) = ((term18 x y) = (term27 x y)).
Proof. exact (prop_ext (fun h2 : term9 x => @lem1614605 y x h1) (fun h2 : (term18 x y) = (term27 x y) => @lem1610563 x h1)). Qed.
Lemma lem1614621 (y : real) (x : real) (h1 : term9 x) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1614620 y x h1) (@lem1610563 x h1)). Qed.
Lemma lem1614622 (y : real) (x : real) (h1 : term8 x) : (term8 x) = ((term18 x y) = (term27 x y)).
Proof. exact (prop_ext (fun h2 : term8 x => @lem1614613 y x h1) (fun h2 : (term18 x y) = (term27 x y) => @lem1610562 x h1)). Qed.
Lemma lem1614623 (y : real) (x : real) (h1 : term8 x) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1614622 y x h1) (@lem1610562 x h1)). Qed.
Lemma lem1614624 (y : real) (x : real) (h1 : term7 x) : (term18 x y) = (term27 x y).
Proof. exact (or_elim (@lem1610561 x h1) (fun h0 : term8 x => @lem1614623 y x h0) (fun h0 : term9 x => @lem1614621 y x h0)). Qed.
Lemma lem1614625 (y : real) (x : real) (h1 : x = term6) : (x = term6) = ((term18 x y) = (term27 x y)).
Proof. exact (prop_ext (fun h2 : x = term6 => @lem1614619 y x h1) (fun h2 : (term18 x y) = (term27 x y) => @lem1610560 x h1)). Qed.
Lemma lem1614626 (y : real) (x : real) (h1 : x = term6) : (term18 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1614625 y x h1) (@lem1610560 x h1)). Qed.
Lemma lem1614627 (x : real) (y : real) : (term18 x y) = (term27 x y).
Proof. exact (or_elim (@lem1610559 x) (fun h0 : x = term6 => @lem1614626 y x h0) (fun h0 : term7 x => @lem1614624 y x h0)). Qed.
Lemma lem1614632 (x : real) : term533 x.
Proof. exact (fun y : real => @lem1614627 x y). Qed.
Lemma lem1614637 : term534.
Proof. exact (fun x : real => @lem1614632 x). Qed.
