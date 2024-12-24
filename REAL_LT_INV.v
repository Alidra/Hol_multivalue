Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_INV_term_abbrevs.
Require Import REAL_INV_EQ_0_spec.
Require Import REAL_LT_MUL_spec.
Require Import REAL_LT_NEGTOTAL_spec.
Require Import REAL_LT_RNEG_spec.
Require Import REAL_MUL_LNEG_spec.
Require Import REAL_OF_NUM_LT_spec.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1338512_spec.
Require Import thm1340174_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483440_spec.
Require Import thm1483446_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483529_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm16933_spec.
Require Import thm17362_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm520356_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Lemma lem1589156 : term0.
Proof. exact (EQ_MP (@lem520356) (@lem0)). Qed.
Lemma lem1589157 : term1.
Proof. exact (proj2 (@lem1589156)). Qed.
Lemma lem1589158 : term2.
Proof. exact (proj2 (@lem1589157)). Qed.
Lemma lem1589159 : term3.
Proof. exact (proj2 (@lem1589158)). Qed.
Lemma lem1589201 : term4.
Proof. exact (proj1 (@lem1589159)). Qed.
Lemma lem1589202 (n : nat) : term5 n.
Proof. exact (@lem1589201 n). Qed.
Lemma lem1589203 (n : nat) : (term5 n) = ((term6 n) = False).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem1589210 : term7.
Proof. exact (proj1 (@lem1589156)). Qed.
Lemma lem1589211 (m : nat) : term8 m.
Proof. exact (@lem1589210 m). Qed.
Lemma lem1589212 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem1589213 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1589212 m) (@lem1589211 m)). Qed.
Lemma lem1589214 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem1589213 m n). Qed.
Lemma lem1589215 (m : nat) (n : nat) : (term10 m n) = ((term11 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem1589589 (m : nat) : term12 m.
Proof. exact (@lem1483667 m). Qed.
Lemma lem1589590 (m : nat) : (term12 m) = (term13 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem1589591 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem1589590 m) (@lem1589589 m)). Qed.
Lemma lem1589592 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem1589591 m n). Qed.
Lemma lem1589593 (m : nat) (n : nat) : (term14 m n) = ((term15 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem1589595 (x : real) : term16 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1589596 (x : real) : (term16 x) = ((term17 x) = x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1589598 (x : real) : term18 x.
Proof. exact (@lem1502267 x). Qed.
Lemma lem1589599 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1589600 (x : real) : term19 x.
Proof. exact (EQ_MP (@lem1589599 x) (@lem1589598 x)). Qed.
Lemma lem1589601 (x : real) (y : real) : term20 x y.
Proof. exact (@lem1589600 x y). Qed.
Lemma lem1589602 (x : real) (y : real) : (term20 x y) = ((term21 x y) = (term22 x y)).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1589604 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1589605 (x : real) (h1 : term23) : term24 x.
Proof. exact (@lem1589604 h1 x). Qed.
Lemma lem1589606 (x : real) : (term24 x) = (term25 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1589607 (x : real) (h1 : term23) : term25 x.
Proof. exact (EQ_MP (@lem1589606 x) (@lem1589605 x h1)). Qed.
Lemma lem1589608 (x : real) (h1 : term26 x) : term26 x.
Proof. exact (h1). Qed.
Lemma lem1589609 (x : real) (h1 : term23) (h2 : term26 x) : (term27 x) = term28.
Proof. exact (@lem1589607 x h1 (@lem1589608 x h2)). Qed.
Lemma lem1589610 (x : real) (h1 : term26 x) : term29 x.
Proof. exact (fun h0 : term23 => @lem1589609 x h0 h1). Qed.
Lemma lem1589611 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1589612 (x : real) (h1 : term23) (h2 : term26 x) : (term27 x) = term28.
Proof. exact (@lem1589610 x h2 (@lem1589611 h1)). Qed.
Lemma lem1589613 (x : real) (h1 : term23) : term25 x.
Proof. exact (fun h0 : term26 x => @lem1589612 x h1 h0). Qed.
Lemma lem1589614 (h1 : term23) : term23.
Proof. exact (fun x : real => @lem1589613 x h1). Qed.
Lemma lem1589615 : term30.
Proof. exact (fun h0 : term23 => @lem1589614 h0). Qed.
Lemma lem1589616 : term23.
Proof. exact (@lem1589615 (@lem1340174)). Qed.
Lemma lem1589617 (x : real) : term24 x.
Proof. exact (@lem1589616 x). Qed.
Lemma lem1589618 (x : real) : (term24 x) = (term25 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1589620 (x : real) : term31 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem1589621 (x : real) : (term31 x) = (term32 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1589622 (x : real) : term32 x.
Proof. exact (EQ_MP (@lem1589621 x) (@lem1589620 x)). Qed.
Lemma lem1589623 (x : real) (y : real) : term33 x y.
Proof. exact (@lem1589622 x y). Qed.
Lemma lem1589624 (x : real) (y : real) : (term33 x y) = ((term34 x y) = (term35 x y)).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem1589626 (h1 : term36) : term36.
Proof. exact (h1). Qed.
Lemma lem1589627 (x : real) (h1 : term36) : term37 x.
Proof. exact (@lem1589626 h1 x). Qed.
Lemma lem1589628 (x : real) : (term37 x) = (term38 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1589629 (x : real) (h1 : term36) : term38 x.
Proof. exact (EQ_MP (@lem1589628 x) (@lem1589627 x h1)). Qed.
Lemma lem1589630 (x : real) (y : real) (h1 : term36) : term39 x y.
Proof. exact (@lem1589629 x h1 y). Qed.
Lemma lem1589631 (x : real) (y : real) : (term39 x y) = (term40 x y).
Proof. exact (eq_refl (term39 x y)). Qed.
Lemma lem1589632 (x : real) (y : real) (h1 : term36) : term40 x y.
Proof. exact (EQ_MP (@lem1589631 x y) (@lem1589630 x y h1)). Qed.
Lemma lem1589633 (x : real) (y : real) (h1 : term41 x y) : term41 x y.
Proof. exact (h1). Qed.
Lemma lem1589634 (x : real) (y : real) (h1 : term36) (h2 : term41 x y) : term42 x y.
Proof. exact (@lem1589632 x y h1 (@lem1589633 x y h2)). Qed.
Lemma lem1589635 (x : real) (y : real) (h1 : term41 x y) : term43 x y.
Proof. exact (fun h0 : term36 => @lem1589634 x y h0 h1). Qed.
Lemma lem1589636 (h1 : term36) : term36.
Proof. exact (h1). Qed.
Lemma lem1589637 (x : real) (y : real) (h1 : term36) (h2 : term41 x y) : term42 x y.
Proof. exact (@lem1589635 x y h2 (@lem1589636 h1)). Qed.
Lemma lem1589638 (x : real) (y : real) (h1 : term36) : term40 x y.
Proof. exact (fun h0 : term41 x y => @lem1589637 x y h1 h0). Qed.
Lemma lem1589639 (x : real) (h1 : term36) : term38 x.
Proof. exact (fun y : real => @lem1589638 x y h1). Qed.
Lemma lem1589640 (h1 : term36) : term36.
Proof. exact (fun x : real => @lem1589639 x h1). Qed.
Lemma lem1589641 : term44.
Proof. exact (fun h0 : term36 => @lem1589640 h0). Qed.
Lemma lem1589642 : term36.
Proof. exact (@lem1589641 (@lem1487565)). Qed.
Lemma lem1589643 (x : real) : term37 x.
Proof. exact (@lem1589642 x). Qed.
Lemma lem1589644 (x : real) : (term37 x) = (term38 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1589645 (x : real) : term38 x.
Proof. exact (EQ_MP (@lem1589644 x) (@lem1589643 x)). Qed.
Lemma lem1589646 (x : real) (y : real) : term39 x y.
Proof. exact (@lem1589645 x y). Qed.
Lemma lem1589647 (x : real) (y : real) : (term39 x y) = (term40 x y).
Proof. exact (eq_refl (term39 x y)). Qed.
Lemma lem1589649 (x : real) : term45 x.
Proof. exact (@lem1588944 x). Qed.
Lemma lem1589650 (x : real) : (term45 x) = (((real_inv x) = term46) = (x = term46)).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1589652 (x : real) : term47 x.
Proof. exact (@lem1499257 (real_inv x)). Qed.
Lemma lem1589653 (x : real) : (term47 x) = (term48 x).
Proof. exact (eq_refl (term47 x)). Qed.
Lemma lem1589654 (x : real) : term48 x.
Proof. exact (EQ_MP (@lem1589653 x) (@lem1589652 x)). Qed.
Lemma lem1589655 (x : real) (h1 : (real_inv x) = term46) : (real_inv x) = term46.
Proof. exact (h1). Qed.
Lemma lem1589656 (x : real) (h1 : term49 x) : term49 x.
Proof. exact (h1). Qed.
Lemma lem1589657 (x : real) (h1 : term50 x) : term50 x.
Proof. exact (h1). Qed.
Lemma lem1589658 (x : real) (h1 : term51 x) : term51 x.
Proof. exact (h1). Qed.
Lemma lem1589662 (x : real) (h1 : (real_inv x) = term46) : (real_inv x) = term46.
Proof. exact (h1). Qed.
Lemma lem1589663 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1589664 (x : real) (h1 : (real_inv x) = term46) : (term50 x) = term53.
Proof. exact (MK_COMB (@lem1589663) (@lem1589662 x h1)). Qed.
Lemma lem1589665 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1589666 (x : real) (h1 : (real_inv x) = term46) : (term55 x) = (term56 x).
Proof. exact (MK_COMB (@lem1589665 x) (@lem1589664 x h1)). Qed.
Lemma lem1589669 (x : real) (h1 : (real_inv x) = term46) : (term56 x) = (term55 x).
Proof. exact (SYM (@lem1589666 x h1)). Qed.
Lemma lem1589670 (x : real) : (term50 x) = ((term50 x) = True).
Proof. exact (@lem7 (term50 x)). Qed.
Lemma lem1589675 (x : real) (h1 : term50 x) : (term50 x) = True.
Proof. exact (EQ_MP (@lem1589670 x) (@lem1589657 x h1)). Qed.
Lemma lem1589676 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1589677 (x : real) (h1 : term50 x) : (term55 x) = (term57 x).
Proof. exact (MK_COMB (@lem1589676 x) (@lem1589675 x h1)). Qed.
Lemma lem1589679 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1589680 (x : real) : (term57 x) = True.
Proof. exact (@lem1589679 (term58 x)). Qed.
Lemma lem1589681 (x : real) (h1 : term50 x) : (term55 x) = True.
Proof. exact (TRANS (@lem1589677 x h1) (@lem1589680 x)). Qed.
Lemma lem1589682 (x : real) (h1 : term50 x) : True = (term55 x).
Proof. exact (SYM (@lem1589681 x h1)). Qed.
Lemma lem1589683 (x : real) (h1 : term50 x) : term55 x.
Proof. exact (EQ_MP (@lem1589682 x h1) (@lem0)). Qed.
Lemma lem1589691 (x : real) : ((real_inv x) = term46) = (x = term46).
Proof. exact (EQ_MP (@lem1589650 x) (@lem1589649 x)). Qed.
Lemma lem1589698 (x : real) (h1 : (real_inv x) = term46) : x = term46.
Proof. exact (EQ_MP (@lem1589691 x) (@lem1589655 x h1)). Qed.
Lemma lem1589699 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1589700 (x : real) (h1 : (real_inv x) = term46) : (term58 x) = term53.
Proof. exact (MK_COMB (@lem1589699) (@lem1589698 x h1)). Qed.
Lemma lem1589701 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1589702 (x : real) (h1 : (real_inv x) = term46) : (term54 x) = term59.
Proof. exact (MK_COMB (@lem1589701) (@lem1589700 x h1)). Qed.
Lemma lem1589703 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1589704 (x : real) (h1 : (real_inv x) = term46) : (term56 x) = term60.
Proof. exact (MK_COMB (@lem1589702 x h1) (@lem1589703)). Qed.
Lemma lem1589706 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1589707 : term60 = True.
Proof. exact (@lem1589706 term53). Qed.
Lemma lem1589708 (x : real) (h1 : (real_inv x) = term46) : (term56 x) = True.
Proof. exact (TRANS (@lem1589704 x h1) (@lem1589707)). Qed.
Lemma lem1589709 (x : real) (h1 : (real_inv x) = term46) : True = (term56 x).
Proof. exact (SYM (@lem1589708 x h1)). Qed.
Lemma lem1589710 (x : real) (h1 : (real_inv x) = term46) : term56 x.
Proof. exact (EQ_MP (@lem1589709 x h1) (@lem0)). Qed.
Lemma lem1589711 (x : real) (h1 : term58 x) : term58 x.
Proof. exact (h1). Qed.
Lemma lem1589712 (x : real) (h1 : term61 x) : term61 x.
Proof. exact (h1). Qed.
Lemma lem1589714 (x : real) (y : real) : term40 x y.
Proof. exact (EQ_MP (@lem1589647 x y) (@lem1589646 x y)). Qed.
Lemma lem1589715 (x : real) : term62 x.
Proof. exact (@lem1589714 (term63 x) x). Qed.
Lemma lem1589716 (x : real) : (term51 x) = ((term51 x) = True).
Proof. exact (@lem7 (term51 x)). Qed.
Lemma lem1589718 (x : real) : (term58 x) = ((term58 x) = True).
Proof. exact (@lem7 (term58 x)). Qed.
Lemma lem1589723 (x : real) (h1 : term51 x) : (term51 x) = True.
Proof. exact (EQ_MP (@lem1589716 x) (@lem1589658 x h1)). Qed.
Lemma lem1589724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1589725 (x : real) (h1 : term51 x) : (term64 x) = (and True).
Proof. exact (MK_COMB (@lem1589724) (@lem1589723 x h1)). Qed.
Lemma lem1589727 (x : real) (h1 : term58 x) : (term58 x) = True.
Proof. exact (EQ_MP (@lem1589718 x) (@lem1589711 x h1)). Qed.
Lemma lem1589728 (x : real) (h1 : term58 x) (h2 : term51 x) : (term65 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1589725 x h2) (@lem1589727 x h1)). Qed.
Lemma lem1589730 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1589731 : (True /\ True) = True.
Proof. exact (@lem1589730 True). Qed.
Lemma lem1589732 (x : real) (h1 : term58 x) (h2 : term51 x) : (term65 x) = True.
Proof. exact (TRANS (@lem1589728 x h1 h2) (@lem1589731)). Qed.
Lemma lem1589733 (x : real) (h1 : term58 x) (h2 : term51 x) : True = (term65 x).
Proof. exact (SYM (@lem1589732 x h1 h2)). Qed.
Lemma lem1589734 (x : real) (h1 : term58 x) (h2 : term51 x) : term65 x.
Proof. exact (EQ_MP (@lem1589733 x h1 h2) (@lem0)). Qed.
Lemma lem1589735 (x : real) (h1 : term58 x) (h2 : term51 x) : term61 x.
Proof. exact (@lem1589715 x (@lem1589734 x h1 h2)). Qed.
Lemma lem1589739 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (EQ_MP (@lem1589624 x y) (@lem1589623 x y)). Qed.
Lemma lem1589740 (x : real) : (term66 x) = (term67 x).
Proof. exact (@lem1589739 (real_inv x) x). Qed.
Lemma lem1589741 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1589742 (x : real) : (term61 x) = (term68 x).
Proof. exact (MK_COMB (@lem1589741) (@lem1589740 x)). Qed.
Lemma lem1589743 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1589744 (x : real) : (term69 x) = (term70 x).
Proof. exact (MK_COMB (@lem1589743) (@lem1589742 x)). Qed.
Lemma lem1589745 (x : real) : (term50 x) = (term50 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1589746 (x : real) : (term71 x) = (term72 x).
Proof. exact (MK_COMB (@lem1589744 x) (@lem1589745 x)). Qed.
Lemma lem1589749 (x : real) : (term72 x) = (term71 x).
Proof. exact (SYM (@lem1589746 x)). Qed.
Lemma lem1589750 (x : real) (h1 : (term27 x) = term28) : (term27 x) = term28.
Proof. exact (h1). Qed.
Lemma lem1589751 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1589752 (x : real) (h1 : (term27 x) = term28) : (term74 x) = (term75 x).
Proof. exact (MK_COMB (@lem1589751 x) (@lem1589750 x h1)). Qed.
Lemma lem1589753 (x : real) : (term75 x) = (term76 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem1589754 (x : real) : (term77 x) = (term77 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem1589755 (x : real) : ((term74 x) = (term75 x)) = ((term74 x) = (term76 x)).
Proof. exact (MK_COMB (@lem1589754 x) (@lem1589753 x)). Qed.
Lemma lem1589756 (x : real) : (term74 x) = (term72 x).
Proof. exact (eq_refl (term74 x)). Qed.
Lemma lem1589757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1589758 (x : real) : (term77 x) = (term78 x).
Proof. exact (MK_COMB (@lem1589757) (@lem1589756 x)). Qed.
Lemma lem1589759 (x : real) : (term76 x) = (term76 x).
Proof. exact (eq_refl (term76 x)). Qed.
Lemma lem1589760 (x : real) : ((term74 x) = (term76 x)) = ((term72 x) = (term76 x)).
Proof. exact (MK_COMB (@lem1589758 x) (@lem1589759 x)). Qed.
Lemma lem1589761 (x : real) : ((term74 x) = (term75 x)) = ((term72 x) = (term76 x)).
Proof. exact (TRANS (@lem1589755 x) (@lem1589760 x)). Qed.
Lemma lem1589762 (x : real) (h1 : (term27 x) = term28) : (term72 x) = (term76 x).
Proof. exact (EQ_MP (@lem1589761 x) (@lem1589752 x h1)). Qed.
Lemma lem1589763 (x : real) (h1 : (term27 x) = term28) : (term76 x) = (term72 x).
Proof. exact (SYM (@lem1589762 x h1)). Qed.
Lemma lem1589765 (x : real) : term25 x.
Proof. exact (EQ_MP (@lem1589618 x) (@lem1589617 x)). Qed.
Lemma lem1589774 (x : real) : (term79 x) = (x = term46).
Proof. exact (@lem16933 (x = term46)). Qed.
Lemma lem1589776 (x : real) : (term80 x) = (term80 x).
Proof. exact (eq_refl (term80 x)). Qed.
Lemma lem1589777 (x : real) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem1589776 x) (@lem1589774 x)). Qed.
Lemma lem1589778 (x : real) : (term83 x) = (term81 x).
Proof. exact (@lem17362 (term58 x) (term26 x)). Qed.
Lemma lem1589786 (x : real) : (term83 x) = (term82 x).
Proof. exact (TRANS (@lem1589778 x) (@lem1589777 x)). Qed.
Lemma lem1589787 (x : real) : (term58 x) = (term84 x).
Proof. exact (@lem1483521 x term46). Qed.
Lemma lem1589793 (x : real) : (term85 x) = (term86 x).
Proof. exact (@lem1483519 x term46). Qed.
Lemma lem1589795 (x : nat) : (term87 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1589796 : term88 = term46.
Proof. exact (@lem1589795 term89). Qed.
Lemma lem1589797 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1589798 (x : real) : (term86 x) = (term90 x).
Proof. exact (MK_COMB (@lem1589797 x) (@lem1589796)). Qed.
Lemma lem1589799 (x : real) : (term90 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1589800 (x : real) : (term86 x) = x.
Proof. exact (TRANS (@lem1589798 x) (@lem1589799 x)). Qed.
Lemma lem1589802 (x : real) : (term85 x) = x.
Proof. exact (TRANS (@lem1589793 x) (@lem1589800 x)). Qed.
Lemma lem1589803 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1589804 (x : real) : (term91 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1589803) (@lem1589802 x)). Qed.
Lemma lem1589805 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1589806 (x : real) : (term84 x) = (term92 x).
Proof. exact (MK_COMB (@lem1589804 x) (@lem1589805)). Qed.
Lemma lem1589807 (x : real) : (term58 x) = (term92 x).
Proof. exact (TRANS (@lem1589787 x) (@lem1589806 x)). Qed.
Lemma lem1589808 (x : real) : (x = term46) = ((term85 x) = term46).
Proof. exact (@lem1483529 x term46). Qed.
Lemma lem1589814 (x : real) : (term85 x) = (term86 x).
Proof. exact (@lem1483519 x term46). Qed.
Lemma lem1589816 (x : nat) : (term87 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1589817 : term88 = term46.
Proof. exact (@lem1589816 term89). Qed.
Lemma lem1589818 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1589819 (x : real) : (term86 x) = (term90 x).
Proof. exact (MK_COMB (@lem1589818 x) (@lem1589817)). Qed.
Lemma lem1589820 (x : real) : (term90 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1589821 (x : real) : (term86 x) = x.
Proof. exact (TRANS (@lem1589819 x) (@lem1589820 x)). Qed.
Lemma lem1589823 (x : real) : (term85 x) = x.
Proof. exact (TRANS (@lem1589814 x) (@lem1589821 x)). Qed.
Lemma lem1589824 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1589825 (x : real) : (term93 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1589824) (@lem1589823 x)). Qed.
Lemma lem1589826 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1589827 (x : real) : ((term85 x) = term46) = (x = term46).
Proof. exact (MK_COMB (@lem1589825 x) (@lem1589826)). Qed.
Lemma lem1589828 (x : real) : (x = term46) = (x = term46).
Proof. exact (TRANS (@lem1589808 x) (@lem1589827 x)). Qed.
Lemma lem1589829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1589830 (x : real) : (term80 x) = (term94 x).
Proof. exact (MK_COMB (@lem1589829) (@lem1589807 x)). Qed.
Lemma lem1589831 (x : real) : (term82 x) = (term95 x).
Proof. exact (MK_COMB (@lem1589830 x) (@lem1589828 x)). Qed.
Lemma lem1589846 (x : real) : (term83 x) = (term95 x).
Proof. exact (TRANS (@lem1589786 x) (@lem1589831 x)). Qed.
Lemma lem1589850 (x : real) (h1 : term95 x) : term95 x.
Proof. exact (h1). Qed.
Lemma lem1589851 (x : real) (h1 : term95 x) : x = term46.
Proof. exact (proj2 (@lem1589850 x h1)). Qed.
Lemma lem1589852 (x : real) (h1 : term95 x) : term92 x.
Proof. exact (proj1 (@lem1589850 x h1)). Qed.
Lemma lem1589854 (n : nat) (m : nat) : (term96 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1589855 : term97 = term98.
Proof. exact (@lem1589854 (NUMERAL 0) term89). Qed.
Lemma lem1589856 : term99 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1589857 (h1 : term99 = (BIT1 0)) : term98 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1589858 : (term99 = (BIT1 0)) = (term98 = True).
Proof. exact (prop_ext (fun h1 : term99 = (BIT1 0) => @lem1589857 h1) (fun h1 : term98 = True => @lem1589856)). Qed.
Lemma lem1589859 : term98 = True.
Proof. exact (EQ_MP (@lem1589858) (@lem1589856)). Qed.
Lemma lem1589860 : term97 = True.
Proof. exact (TRANS (@lem1589855) (@lem1589859)). Qed.
Lemma lem1589861 : True = term97.
Proof. exact (SYM (@lem1589860)). Qed.
Lemma lem1589862 : term97.
Proof. exact (EQ_MP (@lem1589861) (@lem0)). Qed.
Lemma lem1589863 (x : real) (h1 : term95 x) : term100 x.
Proof. exact (conj (@lem1589862) (@lem1589852 x h1)). Qed.
Lemma lem1589865 (x : real) (y : real) : term101 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1589866 (x : real) : term102 x.
Proof. exact (@lem1589865 term28 x). Qed.
Lemma lem1589867 (x : real) (h1 : term95 x) : term103 x.
Proof. exact (@lem1589866 x (@lem1589863 x h1)). Qed.
Lemma lem1589868 (x : real) : (term104 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1589869 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1589870 (x : real) : (term105 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1589869) (@lem1589868 x)). Qed.
Lemma lem1589871 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1589872 (x : real) : (term103 x) = (term92 x).
Proof. exact (MK_COMB (@lem1589870 x) (@lem1589871)). Qed.
Lemma lem1589873 (x : real) (h1 : term95 x) : term92 x.
Proof. exact (EQ_MP (@lem1589872 x) (@lem1589867 x h1)). Qed.
Lemma lem1589875 (y : real) : term106 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1589876 (x : real) : term106 x.
Proof. exact (@lem1589875 x). Qed.
Lemma lem1589877 (x : real) (h1 : term95 x) : term107 x.
Proof. exact (@lem1589876 x (@lem1589851 x h1)). Qed.
Lemma lem1589878 (x : real) (h1 : term95 x) : term108 x.
Proof. exact (@lem1589877 x h1 term109). Qed.
Lemma lem1589879 (x : real) : (term108 x) = ((term110 x) = term46).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1589886 (x : real) (h1 : term95 x) : (term110 x) = term46.
Proof. exact (EQ_MP (@lem1589879 x) (@lem1589878 x h1)). Qed.
Lemma lem1589887 (x : real) (h1 : term95 x) : term111 x.
Proof. exact (conj (@lem1589886 x h1) (@lem1589873 x h1)). Qed.
Lemma lem1589889 (x : real) (y : real) : term112 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1589890 (x : real) : term113 x.
Proof. exact (@lem1589889 (term110 x) x). Qed.
Lemma lem1589891 (x : real) (h1 : term95 x) : term114 x.
Proof. exact (@lem1589890 x (@lem1589887 x h1)). Qed.
Lemma lem1589892 (x : real) : (term115 x) = (term116 x).
Proof. exact (@lem1483440 term109 x). Qed.
Lemma lem1589894 (m : nat) : (term117 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1589895 : term118 = term46.
Proof. exact (@lem1589894 term89). Qed.
Lemma lem1589896 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1589897 : term119 = term120.
Proof. exact (MK_COMB (@lem1589896) (@lem1589895)). Qed.
Lemma lem1589898 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1589899 (x : real) : (term116 x) = (term121 x).
Proof. exact (MK_COMB (@lem1589897) (@lem1589898 x)). Qed.
Lemma lem1589900 (x : real) : (term115 x) = (term121 x).
Proof. exact (TRANS (@lem1589892 x) (@lem1589899 x)). Qed.
Lemma lem1589901 (x : real) : (term121 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1589902 (x : real) : (term115 x) = term46.
Proof. exact (TRANS (@lem1589900 x) (@lem1589901 x)). Qed.
Lemma lem1589903 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1589904 (x : real) : (term122 x) = term123.
Proof. exact (MK_COMB (@lem1589903) (@lem1589902 x)). Qed.
Lemma lem1589905 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1589906 (x : real) : (term114 x) = term124.
Proof. exact (MK_COMB (@lem1589904 x) (@lem1589905)). Qed.
Lemma lem1589907 (x : real) (h1 : term95 x) : term124.
Proof. exact (EQ_MP (@lem1589906 x) (@lem1589891 x h1)). Qed.
Lemma lem1589909 (n : nat) (m : nat) : (term96 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1589910 : term124 = term125.
Proof. exact (@lem1589909 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1589911 : term125 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1589912 : term124 = False.
Proof. exact (TRANS (@lem1589910) (@lem1589911)). Qed.
Lemma lem1589913 (x : real) (h1 : term95 x) : False.
Proof. exact (EQ_MP (@lem1589912) (@lem1589907 x h1)). Qed.
Lemma lem1589915 (x : real) (h1 : term95 x) : term95 x.
Proof. exact (h1). Qed.
Lemma lem1589916 (x : real) (h1 : term95 x) : (term95 x) = False.
Proof. exact (prop_ext (fun h2 : term95 x => @lem1589913 x h1) (fun h2 : False => @lem1589915 x h1)). Qed.
Lemma lem1589917 (x : real) (h1 : term95 x) : False.
Proof. exact (EQ_MP (@lem1589916 x h1) (@lem1589915 x h1)). Qed.
Lemma lem1589918 (x : real) (h1 : term83 x) : term83 x.
Proof. exact (h1). Qed.
Lemma lem1589919 (x : real) (h1 : term83 x) : term95 x.
Proof. exact (EQ_MP (@lem1589846 x) (@lem1589918 x h1)). Qed.
Lemma lem1589920 (x : real) (h1 : term83 x) : (term95 x) = False.
Proof. exact (prop_ext (fun h2 : term95 x => @lem1589917 x h2) (fun h2 : False => @lem1589919 x h1)). Qed.
Lemma lem1589921 (x : real) (h1 : term83 x) : False.
Proof. exact (EQ_MP (@lem1589920 x h1) (@lem1589919 x h1)). Qed.
Lemma lem1589922 (x : real) : term126 x.
Proof. exact (fun h0 : term83 x => @lem1589921 x h0). Qed.
Lemma lem1589923 (x : real) : term127 x.
Proof. exact (@lem1386578 (term128 x)). Qed.
Lemma lem1589924 (x : real) : term128 x.
Proof. exact (@lem1589923 x (@lem1589922 x)). Qed.
Lemma lem1589925 (x : real) (h1 : term58 x) : term26 x.
Proof. exact (@lem1589924 x (@lem1589711 x h1)). Qed.
Lemma lem1589926 (x : real) (h1 : term58 x) : (term27 x) = term28.
Proof. exact (@lem1589765 x (@lem1589925 x h1)). Qed.
Lemma lem1589930 (x : real) (y : real) : (term21 x y) = (term22 x y).
Proof. exact (EQ_MP (@lem1589602 x y) (@lem1589601 x y)). Qed.
Lemma lem1589931 : term129 = term130.
Proof. exact (@lem1589930 term46 term28). Qed.
Lemma lem1589933 (x : real) : (term17 x) = x.
Proof. exact (EQ_MP (@lem1589596 x) (@lem1589595 x)). Qed.
Lemma lem1589934 : term131 = term28.
Proof. exact (@lem1589933 term28). Qed.
Lemma lem1589935 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1589936 : term132 = term133.
Proof. exact (MK_COMB (@lem1589935) (@lem1589934)). Qed.
Lemma lem1589937 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1589938 : term130 = term134.
Proof. exact (MK_COMB (@lem1589936) (@lem1589937)). Qed.
Lemma lem1589940 (m : nat) (n : nat) : (term15 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1589593 m n) (@lem1589592 m n)). Qed.
Lemma lem1589941 : term134 = term135.
Proof. exact (@lem1589940 term89 (NUMERAL 0)). Qed.
Lemma lem1589943 (m : nat) (n : nat) : (term11 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1589215 m n) (@lem1589214 m n)). Qed.
Lemma lem1589944 : term135 = term136.
Proof. exact (@lem1589943 (BIT1 0) 0). Qed.
Lemma lem1589946 (n : nat) : (term6 n) = False.
Proof. exact (EQ_MP (@lem1589203 n) (@lem1589202 n)). Qed.
Lemma lem1589947 : term136 = False.
Proof. exact (@lem1589946 0). Qed.
Lemma lem1589948 : term135 = False.
Proof. exact (TRANS (@lem1589944) (@lem1589947)). Qed.
Lemma lem1589949 : term134 = False.
Proof. exact (TRANS (@lem1589941) (@lem1589948)). Qed.
Lemma lem1589950 : term130 = False.
Proof. exact (TRANS (@lem1589938) (@lem1589949)). Qed.
Lemma lem1589951 : term129 = False.
Proof. exact (TRANS (@lem1589931) (@lem1589950)). Qed.
Lemma lem1589952 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1589953 : term137 = (imp False).
Proof. exact (MK_COMB (@lem1589952) (@lem1589951)). Qed.
Lemma lem1589954 (x : real) : (term50 x) = (term50 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1589955 (x : real) : (term76 x) = (term138 x).
Proof. exact (MK_COMB (@lem1589953) (@lem1589954 x)). Qed.
Lemma lem1589957 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1589958 (x : real) : (term138 x) = True.
Proof. exact (@lem1589957 (term50 x)). Qed.
Lemma lem1589959 (x : real) : (term76 x) = True.
Proof. exact (TRANS (@lem1589955 x) (@lem1589958 x)). Qed.
Lemma lem1589960 (x : real) : True = (term76 x).
Proof. exact (SYM (@lem1589959 x)). Qed.
Lemma lem1589961 (x : real) : term76 x.
Proof. exact (EQ_MP (@lem1589960 x) (@lem0)). Qed.
Lemma lem1589962 (x : real) (h1 : (term27 x) = term28) : term72 x.
Proof. exact (EQ_MP (@lem1589763 x h1) (@lem1589961 x)). Qed.
Lemma lem1589963 (x : real) (h1 : term58 x) : ((term27 x) = term28) = (term72 x).
Proof. exact (prop_ext (fun h2 : (term27 x) = term28 => @lem1589962 x h2) (fun h2 : term72 x => @lem1589926 x h1)). Qed.
Lemma lem1589964 (x : real) (h1 : term58 x) : term72 x.
Proof. exact (EQ_MP (@lem1589963 x h1) (@lem1589926 x h1)). Qed.
Lemma lem1589965 (x : real) (h1 : term58 x) : term71 x.
Proof. exact (EQ_MP (@lem1589749 x) (@lem1589964 x h1)). Qed.
Lemma lem1589966 (x : real) (h1 : term58 x) (h2 : term61 x) : term50 x.
Proof. exact (@lem1589965 x h1 (@lem1589712 x h2)). Qed.
Lemma lem1589967 (x : real) (h1 : term58 x) (h2 : term51 x) : (term61 x) = (term50 x).
Proof. exact (prop_ext (fun h3 : term61 x => @lem1589966 x h1 h3) (fun h3 : term50 x => @lem1589735 x h1 h2)). Qed.
Lemma lem1589968 (x : real) (h1 : term58 x) (h2 : term51 x) : term50 x.
Proof. exact (EQ_MP (@lem1589967 x h1 h2) (@lem1589735 x h1 h2)). Qed.
Lemma lem1589970 (x : real) (h1 : term51 x) : term55 x.
Proof. exact (fun h0 : term58 x => @lem1589968 x h0 h1). Qed.
Lemma lem1589971 (x : real) (h1 : (real_inv x) = term46) : term55 x.
Proof. exact (EQ_MP (@lem1589669 x h1) (@lem1589710 x h1)). Qed.
Lemma lem1589972 (x : real) (h1 : term51 x) : (term51 x) = (term55 x).
Proof. exact (prop_ext (fun h2 : term51 x => @lem1589970 x h1) (fun h2 : term55 x => @lem1589658 x h1)). Qed.
Lemma lem1589973 (x : real) (h1 : term51 x) : term55 x.
Proof. exact (EQ_MP (@lem1589972 x h1) (@lem1589658 x h1)). Qed.
Lemma lem1589974 (x : real) (h1 : term50 x) : (term50 x) = (term55 x).
Proof. exact (prop_ext (fun h2 : term50 x => @lem1589683 x h1) (fun h2 : term55 x => @lem1589657 x h1)). Qed.
Lemma lem1589975 (x : real) (h1 : term50 x) : term55 x.
Proof. exact (EQ_MP (@lem1589974 x h1) (@lem1589657 x h1)). Qed.
Lemma lem1589976 (x : real) (h1 : term49 x) : term55 x.
Proof. exact (or_elim (@lem1589656 x h1) (fun h0 : term50 x => @lem1589975 x h0) (fun h0 : term51 x => @lem1589973 x h0)). Qed.
Lemma lem1589977 (x : real) (h1 : (real_inv x) = term46) : ((real_inv x) = term46) = (term55 x).
Proof. exact (prop_ext (fun h2 : (real_inv x) = term46 => @lem1589971 x h1) (fun h2 : term55 x => @lem1589655 x h1)). Qed.
Lemma lem1589978 (x : real) (h1 : (real_inv x) = term46) : term55 x.
Proof. exact (EQ_MP (@lem1589977 x h1) (@lem1589655 x h1)). Qed.
Lemma lem1589979 (x : real) : term55 x.
Proof. exact (or_elim (@lem1589654 x) (fun h0 : (real_inv x) = term46 => @lem1589978 x h0) (fun h0 : term49 x => @lem1589976 x h0)). Qed.
Lemma lem1589984 : term139.
Proof. exact (fun x : real => @lem1589979 x). Qed.
