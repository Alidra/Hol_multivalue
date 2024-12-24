Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_POS_BOUND_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import INT_POS_spec.
Require Import IN_INSERT_spec.
Require Import LE_0_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import NSUM_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19158_spec.
Require Import thm19490_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm2318495_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem6940566 (x : nat) (y : nat) (b : nat) : (term0 x y b) = (term1 x y b).
Proof. exact (@lem17045 (term2 y) (term3 x y b)). Qed.
Lemma lem6940568 (x : nat) : (term4 x) = (term4 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem6940569 (x : nat) (y : nat) (b : nat) : (term5 x y b) = (term6 x y b).
Proof. exact (MK_COMB (@lem6940568 x) (@lem6940566 x y b)). Qed.
Lemma lem6940570 (x : nat) (y : nat) (b : nat) : (term7 x y b) = (term5 x y b).
Proof. exact (@lem17045 (term2 x) (term8 x y b)). Qed.
Lemma lem6940571 (x : nat) (y : nat) (b : nat) : (term7 x y b) = (term6 x y b).
Proof. exact (TRANS (@lem6940570 x y b) (@lem6940569 x y b)). Qed.
Lemma lem6940576 (x : nat) (y : nat) (b : nat) : (term9 x y b) = (term9 x y b).
Proof. exact (eq_refl (term9 x y b)). Qed.
Lemma lem6940577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6940578 (x : nat) (y : nat) (b : nat) : (term10 x y b) = (term11 x y b).
Proof. exact (MK_COMB (@lem6940577) (@lem6940571 x y b)). Qed.
Lemma lem6940579 (x : nat) (y : nat) (b : nat) : (term12 x y b) = (term13 x y b).
Proof. exact (MK_COMB (@lem6940578 x y b) (@lem6940576 x y b)). Qed.
Lemma lem6940580 (x : nat) (y : nat) (b : nat) : (term14 x y b) = (term12 x y b).
Proof. exact (@lem17265 (term15 x y b) (term9 x y b)). Qed.
Lemma lem6940650 (x : nat) (y : nat) (b : nat) : (term14 x y b) = (term13 x y b).
Proof. exact (TRANS (@lem6940580 x y b) (@lem6940579 x y b)). Qed.
Lemma lem6940652 (m : nat) (n : nat) : (Peano.le m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6940653 (x : nat) : (term2 x) = (term17 x).
Proof. exact (@lem6940652 (NUMERAL 0) x). Qed.
Lemma lem6940654 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6940655 (x : nat) : (term18 x) = (term19 x).
Proof. exact (MK_COMB (@lem6940654) (@lem6940653 x)). Qed.
Lemma lem6940656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6940657 (x : nat) : (term4 x) = (term20 x).
Proof. exact (MK_COMB (@lem6940656) (@lem6940655 x)). Qed.
Lemma lem6940659 (m : nat) (n : nat) : (Peano.le m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6940660 (y : nat) : (term2 y) = (term17 y).
Proof. exact (@lem6940659 (NUMERAL 0) y). Qed.
Lemma lem6940661 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6940662 (y : nat) : (term18 y) = (term19 y).
Proof. exact (MK_COMB (@lem6940661) (@lem6940660 y)). Qed.
Lemma lem6940663 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6940664 (y : nat) : (term4 y) = (term20 y).
Proof. exact (MK_COMB (@lem6940663) (@lem6940662 y)). Qed.
Lemma lem6940666 (m : nat) (n : nat) : (Peano.le m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6940667 (x : nat) (y : nat) (b : nat) : (term3 x y b) = (term21 x y b).
Proof. exact (@lem6940666 (Nat.add x y) b). Qed.
Lemma lem6940669 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6940670 (x : nat) (y : nat) : (term22 x y) = (term23 x y).
Proof. exact (@lem6940669 x y). Qed.
Lemma lem6940671 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem6940672 (x : nat) (y : nat) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem6940671) (@lem6940670 x y)). Qed.
Lemma lem6940673 (b : nat) : (int_of_num b) = (int_of_num b).
Proof. exact (eq_refl (int_of_num b)). Qed.
Lemma lem6940674 (x : nat) (y : nat) (b : nat) : (term21 x y b) = (term26 x y b).
Proof. exact (MK_COMB (@lem6940672 x y) (@lem6940673 b)). Qed.
Lemma lem6940675 (x : nat) (y : nat) (b : nat) : (term3 x y b) = (term26 x y b).
Proof. exact (TRANS (@lem6940667 x y b) (@lem6940674 x y b)). Qed.
Lemma lem6940676 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6940677 (x : nat) (y : nat) (b : nat) : (term27 x y b) = (term28 x y b).
Proof. exact (MK_COMB (@lem6940676) (@lem6940675 x y b)). Qed.
Lemma lem6940678 (x : nat) (y : nat) (b : nat) : (term1 x y b) = (term29 x y b).
Proof. exact (MK_COMB (@lem6940664 y) (@lem6940677 x y b)). Qed.
Lemma lem6940679 (x : nat) (y : nat) (b : nat) : (term6 x y b) = (term30 x y b).
Proof. exact (MK_COMB (@lem6940657 x) (@lem6940678 x y b)). Qed.
Lemma lem6940680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6940681 (x : nat) (y : nat) (b : nat) : (term11 x y b) = (term31 x y b).
Proof. exact (MK_COMB (@lem6940680) (@lem6940679 x y b)). Qed.
Lemma lem6940683 (m : nat) (n : nat) : (Peano.le m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6940684 (x : nat) (b : nat) : (Peano.le x b) = (term16 x b).
Proof. exact (@lem6940683 x b). Qed.
Lemma lem6940685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6940686 (x : nat) (b : nat) : (term32 x b) = (term33 x b).
Proof. exact (MK_COMB (@lem6940685) (@lem6940684 x b)). Qed.
Lemma lem6940688 (m : nat) (n : nat) : (Peano.le m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem6940689 (y : nat) (b : nat) : (Peano.le y b) = (term16 y b).
Proof. exact (@lem6940688 y b). Qed.
Lemma lem6940690 (x : nat) (y : nat) (b : nat) : (term9 x y b) = (term34 x y b).
Proof. exact (MK_COMB (@lem6940686 x b) (@lem6940689 y b)). Qed.
Lemma lem6940691 (x : nat) (y : nat) (b : nat) : (term13 x y b) = (term35 x y b).
Proof. exact (MK_COMB (@lem6940681 x y b) (@lem6940690 x y b)). Qed.
Lemma lem6940692 (x : nat) (y : nat) (b : nat) : (term14 x y b) = (term35 x y b).
Proof. exact (TRANS (@lem6940650 x y b) (@lem6940691 x y b)). Qed.
Lemma lem6940693 (b : nat) : term36 b.
Proof. exact (@lem2307535 b). Qed.
Lemma lem6940694 (b : nat) : (term36 b) = (term17 b).
Proof. exact (eq_refl (term36 b)). Qed.
Lemma lem6940695 (b : nat) : term17 b.
Proof. exact (EQ_MP (@lem6940694 b) (@lem6940693 b)). Qed.
Lemma lem6940696 (x : nat) : term36 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem6940697 (x : nat) : (term36 x) = (term17 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem6940698 (x : nat) : term17 x.
Proof. exact (EQ_MP (@lem6940697 x) (@lem6940696 x)). Qed.
Lemma lem6940699 (y : nat) : term36 y.
Proof. exact (@lem2307535 y). Qed.
Lemma lem6940700 (y : nat) : (term36 y) = (term17 y).
Proof. exact (eq_refl (term36 y)). Qed.
Lemma lem6940701 (y : nat) : term17 y.
Proof. exact (EQ_MP (@lem6940700 y) (@lem6940699 y)). Qed.
Lemma lem6940702 (_92532 : int) (_92533 : int) (_92531 : int) : (term37 _92532 _92533 _92531) = (term38 _92532 _92533 _92531).
Proof. exact (@lem2318604 (term38 _92532 _92533 _92531)). Qed.
Lemma lem6940727 (_92532 : int) : (term39 _92532) = (term40 _92532).
Proof. exact (@lem16933 (term40 _92532)). Qed.
Lemma lem6940730 (_92533 : int) : (term39 _92533) = (term40 _92533).
Proof. exact (@lem16933 (term40 _92533)). Qed.
Lemma lem6940733 (_92532 : int) (_92533 : int) (_92531 : int) : (term41 _92532 _92533 _92531) = (term42 _92532 _92533 _92531).
Proof. exact (@lem16933 (term42 _92532 _92533 _92531)). Qed.
Lemma lem6940734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6940735 (_92533 : int) : (term43 _92533) = (term44 _92533).
Proof. exact (MK_COMB (@lem6940734) (@lem6940730 _92533)). Qed.
Lemma lem6940736 (_92532 : int) (_92533 : int) (_92531 : int) : (term45 _92532 _92533 _92531) = (term46 _92532 _92533 _92531).
Proof. exact (MK_COMB (@lem6940735 _92533) (@lem6940733 _92532 _92533 _92531)). Qed.
Lemma lem6940737 (_92532 : int) (_92533 : int) (_92531 : int) : (term47 _92532 _92533 _92531) = (term45 _92532 _92533 _92531).
Proof. exact (@lem17160 (term48 _92533) (term49 _92532 _92533 _92531)). Qed.
Lemma lem6940738 (_92532 : int) (_92533 : int) (_92531 : int) : (term47 _92532 _92533 _92531) = (term46 _92532 _92533 _92531).
Proof. exact (TRANS (@lem6940737 _92532 _92533 _92531) (@lem6940736 _92532 _92533 _92531)). Qed.
Lemma lem6940739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6940740 (_92532 : int) : (term43 _92532) = (term44 _92532).
Proof. exact (MK_COMB (@lem6940739) (@lem6940727 _92532)). Qed.
Lemma lem6940741 (_92532 : int) (_92533 : int) (_92531 : int) : (term50 _92532 _92533 _92531) = (term51 _92532 _92533 _92531).
Proof. exact (MK_COMB (@lem6940740 _92532) (@lem6940738 _92532 _92533 _92531)). Qed.
Lemma lem6940742 (_92532 : int) (_92533 : int) (_92531 : int) : (term52 _92532 _92533 _92531) = (term50 _92532 _92533 _92531).
Proof. exact (@lem17160 (term48 _92532) (term53 _92532 _92533 _92531)). Qed.
Lemma lem6940743 (_92532 : int) (_92533 : int) (_92531 : int) : (term52 _92532 _92533 _92531) = (term51 _92532 _92533 _92531).
Proof. exact (TRANS (@lem6940742 _92532 _92533 _92531) (@lem6940741 _92532 _92533 _92531)). Qed.
Lemma lem6940750 (_92532 : int) (_92533 : int) (_92531 : int) : (term54 _92532 _92533 _92531) = (term55 _92532 _92533 _92531).
Proof. exact (@lem17045 (int_le _92532 _92531) (int_le _92533 _92531)). Qed.
Lemma lem6940751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6940752 (_92532 : int) (_92533 : int) (_92531 : int) : (term56 _92532 _92533 _92531) = (term57 _92532 _92533 _92531).
Proof. exact (MK_COMB (@lem6940751) (@lem6940743 _92532 _92533 _92531)). Qed.
Lemma lem6940753 (_92532 : int) (_92533 : int) (_92531 : int) : (term58 _92532 _92533 _92531) = (term59 _92532 _92533 _92531).
Proof. exact (MK_COMB (@lem6940752 _92532 _92533 _92531) (@lem6940750 _92532 _92533 _92531)). Qed.
Lemma lem6940754 (_92532 : int) (_92533 : int) (_92531 : int) : (term60 _92532 _92533 _92531) = (term58 _92532 _92533 _92531).
Proof. exact (@lem17160 (term61 _92532 _92533 _92531) (term62 _92532 _92533 _92531)). Qed.
Lemma lem6940755 (_92532 : int) (_92533 : int) (_92531 : int) : (term60 _92532 _92533 _92531) = (term59 _92532 _92533 _92531).
Proof. exact (TRANS (@lem6940754 _92532 _92533 _92531) (@lem6940753 _92532 _92533 _92531)). Qed.
Lemma lem6940757 (_92533 : int) : (term44 _92533) = (term44 _92533).
Proof. exact (eq_refl (term44 _92533)). Qed.
Lemma lem6940758 (_92532 : int) (_92533 : int) (_92531 : int) : (term63 _92532 _92533 _92531) = (term64 _92532 _92533 _92531).
Proof. exact (MK_COMB (@lem6940757 _92533) (@lem6940755 _92532 _92533 _92531)). Qed.
Lemma lem6940759 (_92532 : int) (_92533 : int) (_92531 : int) : (term65 _92532 _92533 _92531) = (term63 _92532 _92533 _92531).
Proof. exact (@lem17362 (term40 _92533) (term66 _92532 _92533 _92531)). Qed.
Lemma lem6940760 (_92532 : int) (_92533 : int) (_92531 : int) : (term65 _92532 _92533 _92531) = (term64 _92532 _92533 _92531).
Proof. exact (TRANS (@lem6940759 _92532 _92533 _92531) (@lem6940758 _92532 _92533 _92531)). Qed.
Lemma lem6940762 (_92532 : int) : (term44 _92532) = (term44 _92532).
Proof. exact (eq_refl (term44 _92532)). Qed.
Lemma lem6940763 (_92532 : int) (_92533 : int) (_92531 : int) : (term67 _92532 _92533 _92531) = (term68 _92532 _92533 _92531).
Proof. exact (MK_COMB (@lem6940762 _92532) (@lem6940760 _92532 _92533 _92531)). Qed.
Lemma lem6940764 (_92532 : int) (_92533 : int) (_92531 : int) : (term69 _92532 _92533 _92531) = (term67 _92532 _92533 _92531).
Proof. exact (@lem17362 (term40 _92532) (term70 _92532 _92533 _92531)). Qed.
Lemma lem6940765 (_92532 : int) (_92533 : int) (_92531 : int) : (term69 _92532 _92533 _92531) = (term68 _92532 _92533 _92531).
Proof. exact (TRANS (@lem6940764 _92532 _92533 _92531) (@lem6940763 _92532 _92533 _92531)). Qed.
Lemma lem6940767 (_92531 : int) : (term44 _92531) = (term44 _92531).
Proof. exact (eq_refl (term44 _92531)). Qed.
Lemma lem6940768 (_92532 : int) (_92533 : int) (_92531 : int) : (term71 _92532 _92533 _92531) = (term72 _92532 _92533 _92531).
Proof. exact (MK_COMB (@lem6940767 _92531) (@lem6940765 _92532 _92533 _92531)). Qed.
Lemma lem6940769 (_92532 : int) (_92533 : int) (_92531 : int) : (term73 _92532 _92533 _92531) = (term71 _92532 _92533 _92531).
Proof. exact (@lem17362 (term40 _92531) (term74 _92532 _92533 _92531)). Qed.
Lemma lem6940805 (_92532 : int) (_92533 : int) (_92531 : int) : (term73 _92532 _92533 _92531) = (term72 _92532 _92533 _92531).
Proof. exact (TRANS (@lem6940769 _92532 _92533 _92531) (@lem6940768 _92532 _92533 _92531)). Qed.
Lemma lem6940808 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6940809 (_92531 : int) : (term40 _92531) = (term76 _92531).
Proof. exact (@lem6940808 term77 _92531). Qed.
Lemma lem6940811 (n : nat) : (term78 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6940812 : term79 = term80.
Proof. exact (@lem6940811 (NUMERAL 0)). Qed.
Lemma lem6940813 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6940814 : term81 = term82.
Proof. exact (MK_COMB (@lem6940813) (@lem6940812)). Qed.
Lemma lem6940815 (_92531 : int) : (real_of_int _92531) = (real_of_int _92531).
Proof. exact (eq_refl (real_of_int _92531)). Qed.
Lemma lem6940816 (_92531 : int) : (term76 _92531) = (term83 _92531).
Proof. exact (MK_COMB (@lem6940814) (@lem6940815 _92531)). Qed.
Lemma lem6940818 (_92531 : int) : (term40 _92531) = (term83 _92531).
Proof. exact (TRANS (@lem6940809 _92531) (@lem6940816 _92531)). Qed.
Lemma lem6940821 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6940822 (_92532 : int) : (term40 _92532) = (term76 _92532).
Proof. exact (@lem6940821 term77 _92532). Qed.
Lemma lem6940824 (n : nat) : (term78 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6940825 : term79 = term80.
Proof. exact (@lem6940824 (NUMERAL 0)). Qed.
Lemma lem6940826 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6940827 : term81 = term82.
Proof. exact (MK_COMB (@lem6940826) (@lem6940825)). Qed.
Lemma lem6940828 (_92532 : int) : (real_of_int _92532) = (real_of_int _92532).
Proof. exact (eq_refl (real_of_int _92532)). Qed.
Lemma lem6940829 (_92532 : int) : (term76 _92532) = (term83 _92532).
Proof. exact (MK_COMB (@lem6940827) (@lem6940828 _92532)). Qed.
Lemma lem6940831 (_92532 : int) : (term40 _92532) = (term83 _92532).
Proof. exact (TRANS (@lem6940822 _92532) (@lem6940829 _92532)). Qed.
Lemma lem6940834 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6940835 (_92533 : int) : (term40 _92533) = (term76 _92533).
Proof. exact (@lem6940834 term77 _92533). Qed.
Lemma lem6940837 (n : nat) : (term78 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6940838 : term79 = term80.
Proof. exact (@lem6940837 (NUMERAL 0)). Qed.
Lemma lem6940839 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6940840 : term81 = term82.
Proof. exact (MK_COMB (@lem6940839) (@lem6940838)). Qed.
Lemma lem6940841 (_92533 : int) : (real_of_int _92533) = (real_of_int _92533).
Proof. exact (eq_refl (real_of_int _92533)). Qed.
Lemma lem6940842 (_92533 : int) : (term76 _92533) = (term83 _92533).
Proof. exact (MK_COMB (@lem6940840) (@lem6940841 _92533)). Qed.
Lemma lem6940844 (_92533 : int) : (term40 _92533) = (term83 _92533).
Proof. exact (TRANS (@lem6940835 _92533) (@lem6940842 _92533)). Qed.
Lemma lem6940847 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6940848 (_92532 : int) : (term40 _92532) = (term76 _92532).
Proof. exact (@lem6940847 term77 _92532). Qed.
Lemma lem6940850 (n : nat) : (term78 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6940851 : term79 = term80.
Proof. exact (@lem6940850 (NUMERAL 0)). Qed.
Lemma lem6940852 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6940853 : term81 = term82.
Proof. exact (MK_COMB (@lem6940852) (@lem6940851)). Qed.
Lemma lem6940854 (_92532 : int) : (real_of_int _92532) = (real_of_int _92532).
Proof. exact (eq_refl (real_of_int _92532)). Qed.
Lemma lem6940855 (_92532 : int) : (term76 _92532) = (term83 _92532).
Proof. exact (MK_COMB (@lem6940853) (@lem6940854 _92532)). Qed.
Lemma lem6940857 (_92532 : int) : (term40 _92532) = (term83 _92532).
Proof. exact (TRANS (@lem6940848 _92532) (@lem6940855 _92532)). Qed.
Lemma lem6940860 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6940861 (_92533 : int) : (term40 _92533) = (term76 _92533).
Proof. exact (@lem6940860 term77 _92533). Qed.
Lemma lem6940863 (n : nat) : (term78 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6940864 : term79 = term80.
Proof. exact (@lem6940863 (NUMERAL 0)). Qed.
Lemma lem6940865 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6940866 : term81 = term82.
Proof. exact (MK_COMB (@lem6940865) (@lem6940864)). Qed.
Lemma lem6940867 (_92533 : int) : (real_of_int _92533) = (real_of_int _92533).
Proof. exact (eq_refl (real_of_int _92533)). Qed.
Lemma lem6940868 (_92533 : int) : (term76 _92533) = (term83 _92533).
Proof. exact (MK_COMB (@lem6940866) (@lem6940867 _92533)). Qed.
Lemma lem6940870 (_92533 : int) : (term40 _92533) = (term83 _92533).
Proof. exact (TRANS (@lem6940861 _92533) (@lem6940868 _92533)). Qed.
Lemma lem6940873 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6940874 (_92532 : int) (_92533 : int) (_92531 : int) : (term42 _92532 _92533 _92531) = (term84 _92532 _92533 _92531).
Proof. exact (@lem6940873 (int_add _92532 _92533) _92531). Qed.
Lemma lem6940876 (x : int) (y : int) : (term85 x y) = (term86 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6940877 (_92532 : int) (_92533 : int) : (term85 _92532 _92533) = (term86 _92532 _92533).
Proof. exact (@lem6940876 _92532 _92533). Qed.
Lemma lem6940878 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6940879 (_92532 : int) (_92533 : int) : (term87 _92532 _92533) = (term88 _92532 _92533).
Proof. exact (MK_COMB (@lem6940878) (@lem6940877 _92532 _92533)). Qed.
Lemma lem6940880 (_92531 : int) : (real_of_int _92531) = (real_of_int _92531).
Proof. exact (eq_refl (real_of_int _92531)). Qed.
Lemma lem6940881 (_92532 : int) (_92533 : int) (_92531 : int) : (term84 _92532 _92533 _92531) = (term89 _92532 _92533 _92531).
Proof. exact (MK_COMB (@lem6940879 _92532 _92533) (@lem6940880 _92531)). Qed.
Lemma lem6940883 (_92532 : int) (_92533 : int) (_92531 : int) : (term42 _92532 _92533 _92531) = (term89 _92532 _92533 _92531).
Proof. exact (TRANS (@lem6940874 _92532 _92533 _92531) (@lem6940881 _92532 _92533 _92531)). Qed.
Lemma lem6940884 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6940885 (_92533 : int) : (term44 _92533) = (term90 _92533).
Proof. exact (MK_COMB (@lem6940884) (@lem6940870 _92533)). Qed.
Lemma lem6940886 (_92532 : int) (_92533 : int) (_92531 : int) : (term46 _92532 _92533 _92531) = (term91 _92532 _92533 _92531).
Proof. exact (MK_COMB (@lem6940885 _92533) (@lem6940883 _92532 _92533 _92531)). Qed.
Lemma lem6940887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6940888 (_92532 : int) : (term44 _92532) = (term90 _92532).
Proof. exact (MK_COMB (@lem6940887) (@lem6940857 _92532)). Qed.
Lemma lem6940889 (_92532 : int) (_92533 : int) (_92531 : int) : (term51 _92532 _92533 _92531) = (term92 _92532 _92533 _92531).
Proof. exact (MK_COMB (@lem6940888 _92532) (@lem6940886 _92532 _92533 _92531)). Qed.
Lemma lem6940891 (y : int) (x : int) : (term93 x y) = (term94 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem6940892 (_92531 : int) (_92532 : int) : (term93 _92532 _92531) = (term94 _92531 _92532).
Proof. exact (@lem6940891 _92531 _92532). Qed.
Lemma lem6940894 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6940895 (_92531 : int) (_92532 : int) : (term94 _92531 _92532) = (term95 _92531 _92532).
Proof. exact (@lem6940894 (term96 _92531) _92532). Qed.
Lemma lem6940897 (x : int) (y : int) : (term85 x y) = (term86 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6940898 (_92531 : int) : (term97 _92531) = (term98 _92531).
Proof. exact (@lem6940897 _92531 term99). Qed.
Lemma lem6940900 (n : nat) : (term78 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6940901 : term100 = term101.
Proof. exact (@lem6940900 term102). Qed.
Lemma lem6940902 (_92531 : int) : (term103 _92531) = (term103 _92531).
Proof. exact (eq_refl (term103 _92531)). Qed.
Lemma lem6940903 (_92531 : int) : (term98 _92531) = (term104 _92531).
Proof. exact (MK_COMB (@lem6940902 _92531) (@lem6940901)). Qed.
Lemma lem6940904 (_92531 : int) : (term97 _92531) = (term104 _92531).
Proof. exact (TRANS (@lem6940898 _92531) (@lem6940903 _92531)). Qed.
Lemma lem6940905 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6940906 (_92531 : int) : (term105 _92531) = (term106 _92531).
Proof. exact (MK_COMB (@lem6940905) (@lem6940904 _92531)). Qed.
Lemma lem6940907 (_92532 : int) : (real_of_int _92532) = (real_of_int _92532).
Proof. exact (eq_refl (real_of_int _92532)). Qed.
Lemma lem6940908 (_92531 : int) (_92532 : int) : (term95 _92531 _92532) = (term107 _92531 _92532).
Proof. exact (MK_COMB (@lem6940906 _92531) (@lem6940907 _92532)). Qed.
Lemma lem6940909 (_92531 : int) (_92532 : int) : (term94 _92531 _92532) = (term107 _92531 _92532).
Proof. exact (TRANS (@lem6940895 _92531 _92532) (@lem6940908 _92531 _92532)). Qed.
Lemma lem6940910 (_92531 : int) (_92532 : int) : (term93 _92532 _92531) = (term107 _92531 _92532).
Proof. exact (TRANS (@lem6940892 _92531 _92532) (@lem6940909 _92531 _92532)). Qed.
Lemma lem6940912 (y : int) (x : int) : (term93 x y) = (term94 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem6940913 (_92531 : int) (_92533 : int) : (term93 _92533 _92531) = (term94 _92531 _92533).
Proof. exact (@lem6940912 _92531 _92533). Qed.
Lemma lem6940915 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6940916 (_92531 : int) (_92533 : int) : (term94 _92531 _92533) = (term95 _92531 _92533).
Proof. exact (@lem6940915 (term96 _92531) _92533). Qed.
Lemma lem6940918 (x : int) (y : int) : (term85 x y) = (term86 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6940919 (_92531 : int) : (term97 _92531) = (term98 _92531).
Proof. exact (@lem6940918 _92531 term99). Qed.
Lemma lem6940921 (n : nat) : (term78 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6940922 : term100 = term101.
Proof. exact (@lem6940921 term102). Qed.
Lemma lem6940923 (_92531 : int) : (term103 _92531) = (term103 _92531).
Proof. exact (eq_refl (term103 _92531)). Qed.
Lemma lem6940924 (_92531 : int) : (term98 _92531) = (term104 _92531).
Proof. exact (MK_COMB (@lem6940923 _92531) (@lem6940922)). Qed.
Lemma lem6940925 (_92531 : int) : (term97 _92531) = (term104 _92531).
Proof. exact (TRANS (@lem6940919 _92531) (@lem6940924 _92531)). Qed.
Lemma lem6940926 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6940927 (_92531 : int) : (term105 _92531) = (term106 _92531).
Proof. exact (MK_COMB (@lem6940926) (@lem6940925 _92531)). Qed.
Lemma lem6940928 (_92533 : int) : (real_of_int _92533) = (real_of_int _92533).
Proof. exact (eq_refl (real_of_int _92533)). Qed.
Lemma lem6940929 (_92531 : int) (_92533 : int) : (term95 _92531 _92533) = (term107 _92531 _92533).
Proof. exact (MK_COMB (@lem6940927 _92531) (@lem6940928 _92533)). Qed.
Lemma lem6940930 (_92531 : int) (_92533 : int) : (term94 _92531 _92533) = (term107 _92531 _92533).
Proof. exact (TRANS (@lem6940916 _92531 _92533) (@lem6940929 _92531 _92533)). Qed.
Lemma lem6940931 (_92531 : int) (_92533 : int) : (term93 _92533 _92531) = (term107 _92531 _92533).
Proof. exact (TRANS (@lem6940913 _92531 _92533) (@lem6940930 _92531 _92533)). Qed.
Lemma lem6940932 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6940933 (_92531 : int) (_92532 : int) : (term108 _92532 _92531) = (term109 _92531 _92532).
Proof. exact (MK_COMB (@lem6940932) (@lem6940910 _92531 _92532)). Qed.
Lemma lem6940934 (_92532 : int) (_92531 : int) (_92533 : int) : (term55 _92532 _92533 _92531) = (term110 _92532 _92531 _92533).
Proof. exact (MK_COMB (@lem6940933 _92531 _92532) (@lem6940931 _92531 _92533)). Qed.
Lemma lem6940935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6940936 (_92532 : int) (_92533 : int) (_92531 : int) : (term57 _92532 _92533 _92531) = (term111 _92532 _92533 _92531).
Proof. exact (MK_COMB (@lem6940935) (@lem6940889 _92532 _92533 _92531)). Qed.
Lemma lem6940937 (_92532 : int) (_92531 : int) (_92533 : int) : (term59 _92532 _92533 _92531) = (term112 _92532 _92531 _92533).
Proof. exact (MK_COMB (@lem6940936 _92532 _92533 _92531) (@lem6940934 _92532 _92531 _92533)). Qed.
Lemma lem6940938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6940939 (_92533 : int) : (term44 _92533) = (term90 _92533).
Proof. exact (MK_COMB (@lem6940938) (@lem6940844 _92533)). Qed.
Lemma lem6940940 (_92532 : int) (_92531 : int) (_92533 : int) : (term64 _92532 _92533 _92531) = (term113 _92532 _92531 _92533).
Proof. exact (MK_COMB (@lem6940939 _92533) (@lem6940937 _92532 _92531 _92533)). Qed.
Lemma lem6940941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6940942 (_92532 : int) : (term44 _92532) = (term90 _92532).
Proof. exact (MK_COMB (@lem6940941) (@lem6940831 _92532)). Qed.
Lemma lem6940943 (_92532 : int) (_92531 : int) (_92533 : int) : (term68 _92532 _92533 _92531) = (term114 _92532 _92531 _92533).
Proof. exact (MK_COMB (@lem6940942 _92532) (@lem6940940 _92532 _92531 _92533)). Qed.
Lemma lem6940944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6940945 (_92531 : int) : (term44 _92531) = (term90 _92531).
Proof. exact (MK_COMB (@lem6940944) (@lem6940818 _92531)). Qed.
Lemma lem6940946 (_92532 : int) (_92531 : int) (_92533 : int) : (term72 _92532 _92533 _92531) = (term115 _92532 _92531 _92533).
Proof. exact (MK_COMB (@lem6940945 _92531) (@lem6940943 _92532 _92531 _92533)). Qed.
Lemma lem6940947 (_92532 : int) (_92531 : int) (_92533 : int) : (term73 _92532 _92533 _92531) = (term115 _92532 _92531 _92533).
Proof. exact (TRANS (@lem6940805 _92532 _92533 _92531) (@lem6940946 _92532 _92531 _92533)). Qed.
Lemma lem6940951 (t : Prop) : (term116 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6941027 (_92532 : int) (_92531 : int) (_92533 : int) : (term117 _92532 _92531 _92533) = (term115 _92532 _92531 _92533).
Proof. exact (@lem6940951 (term115 _92532 _92531 _92533)). Qed.
Lemma lem6941028 (_92531 : int) : (term83 _92531) = (term118 _92531).
Proof. exact (@lem1988287 (real_of_int _92531) term80). Qed.
Lemma lem6941034 (_92531 : int) : (term119 _92531) = (term120 _92531).
Proof. exact (@lem1982792 (real_of_int _92531) term80). Qed.
Lemma lem6941036 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941037 : term80 = term122.
Proof. exact (@lem6941036 (NUMERAL 0)). Qed.
Lemma lem6941039 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6941040 : term125 = term126.
Proof. exact (@lem6941039 term102). Qed.
Lemma lem6941041 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6941042 : term127 = term128.
Proof. exact (MK_COMB (@lem6941041) (@lem6941040)). Qed.
Lemma lem6941043 : term129 = term130.
Proof. exact (MK_COMB (@lem6941042) (@lem6941037)). Qed.
Lemma lem6941044 : term130 = term131.
Proof. exact (@lem1981613 term125 term80 term101 term101). Qed.
Lemma lem6941046 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6941047 : term134 = term135.
Proof. exact (@lem6941046 term102 term102). Qed.
Lemma lem6941048 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941049 : term137 = term102.
Proof. exact (EQ_MP (@lem6941048) (@lem940073)). Qed.
Lemma lem6941050 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941051 : term135 = term101.
Proof. exact (MK_COMB (@lem6941050) (@lem6941049)). Qed.
Lemma lem6941052 : term134 = term101.
Proof. exact (TRANS (@lem6941047) (@lem6941051)). Qed.
Lemma lem6941054 (x : nat) : (term138 x) = term80.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6941055 : term129 = term80.
Proof. exact (@lem6941054 term102). Qed.
Lemma lem6941056 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6941057 : term139 = term140.
Proof. exact (MK_COMB (@lem6941056) (@lem6941055)). Qed.
Lemma lem6941058 : term131 = term122.
Proof. exact (MK_COMB (@lem6941057) (@lem6941052)). Qed.
Lemma lem6941059 : term130 = term122.
Proof. exact (TRANS (@lem6941044) (@lem6941058)). Qed.
Lemma lem6941060 : term129 = term122.
Proof. exact (TRANS (@lem6941043) (@lem6941059)). Qed.
Lemma lem6941062 (x : real) : (term141 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6941063 : term122 = term80.
Proof. exact (@lem6941062 term80). Qed.
Lemma lem6941064 : term129 = term80.
Proof. exact (TRANS (@lem6941060) (@lem6941063)). Qed.
Lemma lem6941065 (_92531 : int) : (term103 _92531) = (term103 _92531).
Proof. exact (eq_refl (term103 _92531)). Qed.
Lemma lem6941066 (_92531 : int) : (term120 _92531) = (term142 _92531).
Proof. exact (MK_COMB (@lem6941065 _92531) (@lem6941064)). Qed.
Lemma lem6941067 (_92531 : int) : (term142 _92531) = (real_of_int _92531).
Proof. exact (@lem1982723 (real_of_int _92531)). Qed.
Lemma lem6941068 (_92531 : int) : (term120 _92531) = (real_of_int _92531).
Proof. exact (TRANS (@lem6941066 _92531) (@lem6941067 _92531)). Qed.
Lemma lem6941070 (_92531 : int) : (term119 _92531) = (real_of_int _92531).
Proof. exact (TRANS (@lem6941034 _92531) (@lem6941068 _92531)). Qed.
Lemma lem6941071 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6941072 (_92531 : int) : (term143 _92531) = (term144 _92531).
Proof. exact (MK_COMB (@lem6941071) (@lem6941070 _92531)). Qed.
Lemma lem6941073 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6941074 (_92531 : int) : (term118 _92531) = (term145 _92531).
Proof. exact (MK_COMB (@lem6941072 _92531) (@lem6941073)). Qed.
Lemma lem6941075 (_92531 : int) : (term83 _92531) = (term145 _92531).
Proof. exact (TRANS (@lem6941028 _92531) (@lem6941074 _92531)). Qed.
Lemma lem6941076 (_92532 : int) : (term83 _92532) = (term118 _92532).
Proof. exact (@lem1988287 (real_of_int _92532) term80). Qed.
Lemma lem6941082 (_92532 : int) : (term119 _92532) = (term120 _92532).
Proof. exact (@lem1982792 (real_of_int _92532) term80). Qed.
Lemma lem6941084 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941085 : term80 = term122.
Proof. exact (@lem6941084 (NUMERAL 0)). Qed.
Lemma lem6941087 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6941088 : term125 = term126.
Proof. exact (@lem6941087 term102). Qed.
Lemma lem6941089 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6941090 : term127 = term128.
Proof. exact (MK_COMB (@lem6941089) (@lem6941088)). Qed.
Lemma lem6941091 : term129 = term130.
Proof. exact (MK_COMB (@lem6941090) (@lem6941085)). Qed.
Lemma lem6941092 : term130 = term131.
Proof. exact (@lem1981613 term125 term80 term101 term101). Qed.
Lemma lem6941094 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6941095 : term134 = term135.
Proof. exact (@lem6941094 term102 term102). Qed.
Lemma lem6941096 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941097 : term137 = term102.
Proof. exact (EQ_MP (@lem6941096) (@lem940073)). Qed.
Lemma lem6941098 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941099 : term135 = term101.
Proof. exact (MK_COMB (@lem6941098) (@lem6941097)). Qed.
Lemma lem6941100 : term134 = term101.
Proof. exact (TRANS (@lem6941095) (@lem6941099)). Qed.
Lemma lem6941102 (x : nat) : (term138 x) = term80.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6941103 : term129 = term80.
Proof. exact (@lem6941102 term102). Qed.
Lemma lem6941104 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6941105 : term139 = term140.
Proof. exact (MK_COMB (@lem6941104) (@lem6941103)). Qed.
Lemma lem6941106 : term131 = term122.
Proof. exact (MK_COMB (@lem6941105) (@lem6941100)). Qed.
Lemma lem6941107 : term130 = term122.
Proof. exact (TRANS (@lem6941092) (@lem6941106)). Qed.
Lemma lem6941108 : term129 = term122.
Proof. exact (TRANS (@lem6941091) (@lem6941107)). Qed.
Lemma lem6941110 (x : real) : (term141 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6941111 : term122 = term80.
Proof. exact (@lem6941110 term80). Qed.
Lemma lem6941112 : term129 = term80.
Proof. exact (TRANS (@lem6941108) (@lem6941111)). Qed.
Lemma lem6941113 (_92532 : int) : (term103 _92532) = (term103 _92532).
Proof. exact (eq_refl (term103 _92532)). Qed.
Lemma lem6941114 (_92532 : int) : (term120 _92532) = (term142 _92532).
Proof. exact (MK_COMB (@lem6941113 _92532) (@lem6941112)). Qed.
Lemma lem6941115 (_92532 : int) : (term142 _92532) = (real_of_int _92532).
Proof. exact (@lem1982723 (real_of_int _92532)). Qed.
Lemma lem6941116 (_92532 : int) : (term120 _92532) = (real_of_int _92532).
Proof. exact (TRANS (@lem6941114 _92532) (@lem6941115 _92532)). Qed.
Lemma lem6941118 (_92532 : int) : (term119 _92532) = (real_of_int _92532).
Proof. exact (TRANS (@lem6941082 _92532) (@lem6941116 _92532)). Qed.
Lemma lem6941119 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6941120 (_92532 : int) : (term143 _92532) = (term144 _92532).
Proof. exact (MK_COMB (@lem6941119) (@lem6941118 _92532)). Qed.
Lemma lem6941121 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6941122 (_92532 : int) : (term118 _92532) = (term145 _92532).
Proof. exact (MK_COMB (@lem6941120 _92532) (@lem6941121)). Qed.
Lemma lem6941123 (_92532 : int) : (term83 _92532) = (term145 _92532).
Proof. exact (TRANS (@lem6941076 _92532) (@lem6941122 _92532)). Qed.
Lemma lem6941124 (_92533 : int) : (term83 _92533) = (term118 _92533).
Proof. exact (@lem1988287 (real_of_int _92533) term80). Qed.
Lemma lem6941130 (_92533 : int) : (term119 _92533) = (term120 _92533).
Proof. exact (@lem1982792 (real_of_int _92533) term80). Qed.
Lemma lem6941132 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941133 : term80 = term122.
Proof. exact (@lem6941132 (NUMERAL 0)). Qed.
Lemma lem6941135 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6941136 : term125 = term126.
Proof. exact (@lem6941135 term102). Qed.
Lemma lem6941137 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6941138 : term127 = term128.
Proof. exact (MK_COMB (@lem6941137) (@lem6941136)). Qed.
Lemma lem6941139 : term129 = term130.
Proof. exact (MK_COMB (@lem6941138) (@lem6941133)). Qed.
Lemma lem6941140 : term130 = term131.
Proof. exact (@lem1981613 term125 term80 term101 term101). Qed.
Lemma lem6941142 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6941143 : term134 = term135.
Proof. exact (@lem6941142 term102 term102). Qed.
Lemma lem6941144 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941145 : term137 = term102.
Proof. exact (EQ_MP (@lem6941144) (@lem940073)). Qed.
Lemma lem6941146 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941147 : term135 = term101.
Proof. exact (MK_COMB (@lem6941146) (@lem6941145)). Qed.
Lemma lem6941148 : term134 = term101.
Proof. exact (TRANS (@lem6941143) (@lem6941147)). Qed.
Lemma lem6941150 (x : nat) : (term138 x) = term80.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6941151 : term129 = term80.
Proof. exact (@lem6941150 term102). Qed.
Lemma lem6941152 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6941153 : term139 = term140.
Proof. exact (MK_COMB (@lem6941152) (@lem6941151)). Qed.
Lemma lem6941154 : term131 = term122.
Proof. exact (MK_COMB (@lem6941153) (@lem6941148)). Qed.
Lemma lem6941155 : term130 = term122.
Proof. exact (TRANS (@lem6941140) (@lem6941154)). Qed.
Lemma lem6941156 : term129 = term122.
Proof. exact (TRANS (@lem6941139) (@lem6941155)). Qed.
Lemma lem6941158 (x : real) : (term141 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6941159 : term122 = term80.
Proof. exact (@lem6941158 term80). Qed.
Lemma lem6941160 : term129 = term80.
Proof. exact (TRANS (@lem6941156) (@lem6941159)). Qed.
Lemma lem6941161 (_92533 : int) : (term103 _92533) = (term103 _92533).
Proof. exact (eq_refl (term103 _92533)). Qed.
Lemma lem6941162 (_92533 : int) : (term120 _92533) = (term142 _92533).
Proof. exact (MK_COMB (@lem6941161 _92533) (@lem6941160)). Qed.
Lemma lem6941163 (_92533 : int) : (term142 _92533) = (real_of_int _92533).
Proof. exact (@lem1982723 (real_of_int _92533)). Qed.
Lemma lem6941164 (_92533 : int) : (term120 _92533) = (real_of_int _92533).
Proof. exact (TRANS (@lem6941162 _92533) (@lem6941163 _92533)). Qed.
Lemma lem6941166 (_92533 : int) : (term119 _92533) = (real_of_int _92533).
Proof. exact (TRANS (@lem6941130 _92533) (@lem6941164 _92533)). Qed.
Lemma lem6941167 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6941168 (_92533 : int) : (term143 _92533) = (term144 _92533).
Proof. exact (MK_COMB (@lem6941167) (@lem6941166 _92533)). Qed.
Lemma lem6941169 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6941170 (_92533 : int) : (term118 _92533) = (term145 _92533).
Proof. exact (MK_COMB (@lem6941168 _92533) (@lem6941169)). Qed.
Lemma lem6941171 (_92533 : int) : (term83 _92533) = (term145 _92533).
Proof. exact (TRANS (@lem6941124 _92533) (@lem6941170 _92533)). Qed.
Lemma lem6941172 (_92532 : int) : (term83 _92532) = (term118 _92532).
Proof. exact (@lem1988287 (real_of_int _92532) term80). Qed.
Lemma lem6941178 (_92532 : int) : (term119 _92532) = (term120 _92532).
Proof. exact (@lem1982792 (real_of_int _92532) term80). Qed.
Lemma lem6941180 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941181 : term80 = term122.
Proof. exact (@lem6941180 (NUMERAL 0)). Qed.
Lemma lem6941183 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6941184 : term125 = term126.
Proof. exact (@lem6941183 term102). Qed.
Lemma lem6941185 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6941186 : term127 = term128.
Proof. exact (MK_COMB (@lem6941185) (@lem6941184)). Qed.
Lemma lem6941187 : term129 = term130.
Proof. exact (MK_COMB (@lem6941186) (@lem6941181)). Qed.
Lemma lem6941188 : term130 = term131.
Proof. exact (@lem1981613 term125 term80 term101 term101). Qed.
Lemma lem6941190 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6941191 : term134 = term135.
Proof. exact (@lem6941190 term102 term102). Qed.
Lemma lem6941192 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941193 : term137 = term102.
Proof. exact (EQ_MP (@lem6941192) (@lem940073)). Qed.
Lemma lem6941194 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941195 : term135 = term101.
Proof. exact (MK_COMB (@lem6941194) (@lem6941193)). Qed.
Lemma lem6941196 : term134 = term101.
Proof. exact (TRANS (@lem6941191) (@lem6941195)). Qed.
Lemma lem6941198 (x : nat) : (term138 x) = term80.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6941199 : term129 = term80.
Proof. exact (@lem6941198 term102). Qed.
Lemma lem6941200 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6941201 : term139 = term140.
Proof. exact (MK_COMB (@lem6941200) (@lem6941199)). Qed.
Lemma lem6941202 : term131 = term122.
Proof. exact (MK_COMB (@lem6941201) (@lem6941196)). Qed.
Lemma lem6941203 : term130 = term122.
Proof. exact (TRANS (@lem6941188) (@lem6941202)). Qed.
Lemma lem6941204 : term129 = term122.
Proof. exact (TRANS (@lem6941187) (@lem6941203)). Qed.
Lemma lem6941206 (x : real) : (term141 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6941207 : term122 = term80.
Proof. exact (@lem6941206 term80). Qed.
Lemma lem6941208 : term129 = term80.
Proof. exact (TRANS (@lem6941204) (@lem6941207)). Qed.
Lemma lem6941209 (_92532 : int) : (term103 _92532) = (term103 _92532).
Proof. exact (eq_refl (term103 _92532)). Qed.
Lemma lem6941210 (_92532 : int) : (term120 _92532) = (term142 _92532).
Proof. exact (MK_COMB (@lem6941209 _92532) (@lem6941208)). Qed.
Lemma lem6941211 (_92532 : int) : (term142 _92532) = (real_of_int _92532).
Proof. exact (@lem1982723 (real_of_int _92532)). Qed.
Lemma lem6941212 (_92532 : int) : (term120 _92532) = (real_of_int _92532).
Proof. exact (TRANS (@lem6941210 _92532) (@lem6941211 _92532)). Qed.
Lemma lem6941214 (_92532 : int) : (term119 _92532) = (real_of_int _92532).
Proof. exact (TRANS (@lem6941178 _92532) (@lem6941212 _92532)). Qed.
Lemma lem6941215 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6941216 (_92532 : int) : (term143 _92532) = (term144 _92532).
Proof. exact (MK_COMB (@lem6941215) (@lem6941214 _92532)). Qed.
Lemma lem6941217 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6941218 (_92532 : int) : (term118 _92532) = (term145 _92532).
Proof. exact (MK_COMB (@lem6941216 _92532) (@lem6941217)). Qed.
Lemma lem6941219 (_92532 : int) : (term83 _92532) = (term145 _92532).
Proof. exact (TRANS (@lem6941172 _92532) (@lem6941218 _92532)). Qed.
Lemma lem6941220 (_92533 : int) : (term83 _92533) = (term118 _92533).
Proof. exact (@lem1988287 (real_of_int _92533) term80). Qed.
Lemma lem6941226 (_92533 : int) : (term119 _92533) = (term120 _92533).
Proof. exact (@lem1982792 (real_of_int _92533) term80). Qed.
Lemma lem6941228 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941229 : term80 = term122.
Proof. exact (@lem6941228 (NUMERAL 0)). Qed.
Lemma lem6941231 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6941232 : term125 = term126.
Proof. exact (@lem6941231 term102). Qed.
Lemma lem6941233 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6941234 : term127 = term128.
Proof. exact (MK_COMB (@lem6941233) (@lem6941232)). Qed.
Lemma lem6941235 : term129 = term130.
Proof. exact (MK_COMB (@lem6941234) (@lem6941229)). Qed.
Lemma lem6941236 : term130 = term131.
Proof. exact (@lem1981613 term125 term80 term101 term101). Qed.
Lemma lem6941238 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6941239 : term134 = term135.
Proof. exact (@lem6941238 term102 term102). Qed.
Lemma lem6941240 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941241 : term137 = term102.
Proof. exact (EQ_MP (@lem6941240) (@lem940073)). Qed.
Lemma lem6941242 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941243 : term135 = term101.
Proof. exact (MK_COMB (@lem6941242) (@lem6941241)). Qed.
Lemma lem6941244 : term134 = term101.
Proof. exact (TRANS (@lem6941239) (@lem6941243)). Qed.
Lemma lem6941246 (x : nat) : (term138 x) = term80.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6941247 : term129 = term80.
Proof. exact (@lem6941246 term102). Qed.
Lemma lem6941248 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6941249 : term139 = term140.
Proof. exact (MK_COMB (@lem6941248) (@lem6941247)). Qed.
Lemma lem6941250 : term131 = term122.
Proof. exact (MK_COMB (@lem6941249) (@lem6941244)). Qed.
Lemma lem6941251 : term130 = term122.
Proof. exact (TRANS (@lem6941236) (@lem6941250)). Qed.
Lemma lem6941252 : term129 = term122.
Proof. exact (TRANS (@lem6941235) (@lem6941251)). Qed.
Lemma lem6941254 (x : real) : (term141 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6941255 : term122 = term80.
Proof. exact (@lem6941254 term80). Qed.
Lemma lem6941256 : term129 = term80.
Proof. exact (TRANS (@lem6941252) (@lem6941255)). Qed.
Lemma lem6941257 (_92533 : int) : (term103 _92533) = (term103 _92533).
Proof. exact (eq_refl (term103 _92533)). Qed.
Lemma lem6941258 (_92533 : int) : (term120 _92533) = (term142 _92533).
Proof. exact (MK_COMB (@lem6941257 _92533) (@lem6941256)). Qed.
Lemma lem6941259 (_92533 : int) : (term142 _92533) = (real_of_int _92533).
Proof. exact (@lem1982723 (real_of_int _92533)). Qed.
Lemma lem6941260 (_92533 : int) : (term120 _92533) = (real_of_int _92533).
Proof. exact (TRANS (@lem6941258 _92533) (@lem6941259 _92533)). Qed.
Lemma lem6941262 (_92533 : int) : (term119 _92533) = (real_of_int _92533).
Proof. exact (TRANS (@lem6941226 _92533) (@lem6941260 _92533)). Qed.
Lemma lem6941263 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6941264 (_92533 : int) : (term143 _92533) = (term144 _92533).
Proof. exact (MK_COMB (@lem6941263) (@lem6941262 _92533)). Qed.
Lemma lem6941265 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6941266 (_92533 : int) : (term118 _92533) = (term145 _92533).
Proof. exact (MK_COMB (@lem6941264 _92533) (@lem6941265)). Qed.
Lemma lem6941267 (_92533 : int) : (term83 _92533) = (term145 _92533).
Proof. exact (TRANS (@lem6941220 _92533) (@lem6941266 _92533)). Qed.
Lemma lem6941268 (_92531 : int) (_92532 : int) (_92533 : int) : (term89 _92532 _92533 _92531) = (term146 _92531 _92532 _92533).
Proof. exact (@lem1988287 (real_of_int _92531) (term86 _92532 _92533)). Qed.
Lemma lem6941280 (_92531 : int) (_92532 : int) (_92533 : int) : (term147 _92531 _92532 _92533) = (term148 _92531 _92532 _92533).
Proof. exact (@lem1982792 (real_of_int _92531) (term86 _92532 _92533)). Qed.
Lemma lem6941287 (_92532 : int) (_92533 : int) : (term149 _92532 _92533) = (term150 _92532 _92533).
Proof. exact (@lem1982781 (real_of_int _92532) term125 (real_of_int _92533)). Qed.
Lemma lem6941288 (_92531 : int) : (term103 _92531) = (term103 _92531).
Proof. exact (eq_refl (term103 _92531)). Qed.
Lemma lem6941291 (_92531 : int) (_92532 : int) (_92533 : int) : (term148 _92531 _92532 _92533) = (term151 _92531 _92532 _92533).
Proof. exact (MK_COMB (@lem6941288 _92531) (@lem6941287 _92532 _92533)). Qed.
Lemma lem6941293 (_92531 : int) (_92532 : int) (_92533 : int) : (term147 _92531 _92532 _92533) = (term151 _92531 _92532 _92533).
Proof. exact (TRANS (@lem6941280 _92531 _92532 _92533) (@lem6941291 _92531 _92532 _92533)). Qed.
Lemma lem6941294 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6941295 (_92531 : int) (_92532 : int) (_92533 : int) : (term152 _92531 _92532 _92533) = (term153 _92531 _92532 _92533).
Proof. exact (MK_COMB (@lem6941294) (@lem6941293 _92531 _92532 _92533)). Qed.
Lemma lem6941296 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6941297 (_92531 : int) (_92532 : int) (_92533 : int) : (term146 _92531 _92532 _92533) = (term154 _92531 _92532 _92533).
Proof. exact (MK_COMB (@lem6941295 _92531 _92532 _92533) (@lem6941296)). Qed.
Lemma lem6941298 (_92531 : int) (_92532 : int) (_92533 : int) : (term89 _92532 _92533 _92531) = (term154 _92531 _92532 _92533).
Proof. exact (TRANS (@lem6941268 _92531 _92532 _92533) (@lem6941297 _92531 _92532 _92533)). Qed.
Lemma lem6941299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6941300 (_92533 : int) : (term90 _92533) = (term155 _92533).
Proof. exact (MK_COMB (@lem6941299) (@lem6941267 _92533)). Qed.
Lemma lem6941301 (_92531 : int) (_92532 : int) (_92533 : int) : (term91 _92532 _92533 _92531) = (term156 _92531 _92532 _92533).
Proof. exact (MK_COMB (@lem6941300 _92533) (@lem6941298 _92531 _92532 _92533)). Qed.
Lemma lem6941302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6941303 (_92532 : int) : (term90 _92532) = (term155 _92532).
Proof. exact (MK_COMB (@lem6941302) (@lem6941219 _92532)). Qed.
Lemma lem6941304 (_92531 : int) (_92532 : int) (_92533 : int) : (term92 _92532 _92533 _92531) = (term157 _92531 _92532 _92533).
Proof. exact (MK_COMB (@lem6941303 _92532) (@lem6941301 _92531 _92532 _92533)). Qed.
Lemma lem6941305 (_92532 : int) (_92531 : int) : (term107 _92531 _92532) = (term158 _92532 _92531).
Proof. exact (@lem1988287 (real_of_int _92532) (term104 _92531)). Qed.
Lemma lem6941317 (_92532 : int) (_92531 : int) : (term159 _92532 _92531) = (term160 _92532 _92531).
Proof. exact (@lem1982792 (real_of_int _92532) (term104 _92531)). Qed.
Lemma lem6941318 (_92531 : int) : (term161 _92531) = (term162 _92531).
Proof. exact (@lem1982781 (real_of_int _92531) term125 term101). Qed.
Lemma lem6941320 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941321 : term101 = term163.
Proof. exact (@lem6941320 term102). Qed.
Lemma lem6941323 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6941324 : term125 = term126.
Proof. exact (@lem6941323 term102). Qed.
Lemma lem6941325 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6941326 : term127 = term128.
Proof. exact (MK_COMB (@lem6941325) (@lem6941324)). Qed.
Lemma lem6941327 : term164 = term165.
Proof. exact (MK_COMB (@lem6941326) (@lem6941321)). Qed.
Lemma lem6941328 : term165 = term166.
Proof. exact (@lem1981613 term125 term101 term101 term101). Qed.
Lemma lem6941330 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6941331 : term134 = term135.
Proof. exact (@lem6941330 term102 term102). Qed.
Lemma lem6941332 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941333 : term137 = term102.
Proof. exact (EQ_MP (@lem6941332) (@lem940073)). Qed.
Lemma lem6941334 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941335 : term135 = term101.
Proof. exact (MK_COMB (@lem6941334) (@lem6941333)). Qed.
Lemma lem6941336 : term134 = term101.
Proof. exact (TRANS (@lem6941331) (@lem6941335)). Qed.
Lemma lem6941338 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6941339 : term164 = term169.
Proof. exact (@lem6941338 term102 term102). Qed.
Lemma lem6941340 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941341 : term137 = term102.
Proof. exact (EQ_MP (@lem6941340) (@lem940073)). Qed.
Lemma lem6941342 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941343 : term135 = term101.
Proof. exact (MK_COMB (@lem6941342) (@lem6941341)). Qed.
Lemma lem6941344 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6941345 : term169 = term125.
Proof. exact (MK_COMB (@lem6941344) (@lem6941343)). Qed.
Lemma lem6941346 : term164 = term125.
Proof. exact (TRANS (@lem6941339) (@lem6941345)). Qed.
Lemma lem6941347 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6941348 : term170 = term171.
Proof. exact (MK_COMB (@lem6941347) (@lem6941346)). Qed.
Lemma lem6941349 : term166 = term126.
Proof. exact (MK_COMB (@lem6941348) (@lem6941336)). Qed.
Lemma lem6941350 : term165 = term126.
Proof. exact (TRANS (@lem6941328) (@lem6941349)). Qed.
Lemma lem6941351 : term164 = term126.
Proof. exact (TRANS (@lem6941327) (@lem6941350)). Qed.
Lemma lem6941353 (x : real) : (term141 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6941354 : term126 = term125.
Proof. exact (@lem6941353 term125). Qed.
Lemma lem6941355 : term164 = term125.
Proof. exact (TRANS (@lem6941351) (@lem6941354)). Qed.
Lemma lem6941358 (_92531 : int) : (term172 _92531) = (term172 _92531).
Proof. exact (eq_refl (term172 _92531)). Qed.
Lemma lem6941359 (_92531 : int) : (term162 _92531) = (term173 _92531).
Proof. exact (MK_COMB (@lem6941358 _92531) (@lem6941355)). Qed.
Lemma lem6941360 (_92531 : int) : (term161 _92531) = (term173 _92531).
Proof. exact (TRANS (@lem6941318 _92531) (@lem6941359 _92531)). Qed.
Lemma lem6941361 (_92532 : int) : (term103 _92532) = (term103 _92532).
Proof. exact (eq_refl (term103 _92532)). Qed.
Lemma lem6941362 (_92532 : int) (_92531 : int) : (term160 _92532 _92531) = (term174 _92532 _92531).
Proof. exact (MK_COMB (@lem6941361 _92532) (@lem6941360 _92531)). Qed.
Lemma lem6941367 (_92531 : int) (_92532 : int) : (term174 _92532 _92531) = (term175 _92531 _92532).
Proof. exact (@lem1982757 (term176 _92531) (real_of_int _92532) term125). Qed.
Lemma lem6941368 (_92531 : int) (_92532 : int) : (term160 _92532 _92531) = (term175 _92531 _92532).
Proof. exact (TRANS (@lem6941362 _92532 _92531) (@lem6941367 _92531 _92532)). Qed.
Lemma lem6941370 (_92531 : int) (_92532 : int) : (term159 _92532 _92531) = (term175 _92531 _92532).
Proof. exact (TRANS (@lem6941317 _92532 _92531) (@lem6941368 _92531 _92532)). Qed.
Lemma lem6941371 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6941372 (_92531 : int) (_92532 : int) : (term177 _92532 _92531) = (term178 _92531 _92532).
Proof. exact (MK_COMB (@lem6941371) (@lem6941370 _92531 _92532)). Qed.
Lemma lem6941373 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6941374 (_92531 : int) (_92532 : int) : (term158 _92532 _92531) = (term179 _92531 _92532).
Proof. exact (MK_COMB (@lem6941372 _92531 _92532) (@lem6941373)). Qed.
Lemma lem6941375 (_92531 : int) (_92532 : int) : (term107 _92531 _92532) = (term179 _92531 _92532).
Proof. exact (TRANS (@lem6941305 _92532 _92531) (@lem6941374 _92531 _92532)). Qed.
Lemma lem6941376 (_92533 : int) (_92531 : int) : (term107 _92531 _92533) = (term158 _92533 _92531).
Proof. exact (@lem1988287 (real_of_int _92533) (term104 _92531)). Qed.
Lemma lem6941388 (_92533 : int) (_92531 : int) : (term159 _92533 _92531) = (term160 _92533 _92531).
Proof. exact (@lem1982792 (real_of_int _92533) (term104 _92531)). Qed.
Lemma lem6941389 (_92531 : int) : (term161 _92531) = (term162 _92531).
Proof. exact (@lem1982781 (real_of_int _92531) term125 term101). Qed.
Lemma lem6941391 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941392 : term101 = term163.
Proof. exact (@lem6941391 term102). Qed.
Lemma lem6941394 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6941395 : term125 = term126.
Proof. exact (@lem6941394 term102). Qed.
Lemma lem6941396 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6941397 : term127 = term128.
Proof. exact (MK_COMB (@lem6941396) (@lem6941395)). Qed.
Lemma lem6941398 : term164 = term165.
Proof. exact (MK_COMB (@lem6941397) (@lem6941392)). Qed.
Lemma lem6941399 : term165 = term166.
Proof. exact (@lem1981613 term125 term101 term101 term101). Qed.
Lemma lem6941401 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6941402 : term134 = term135.
Proof. exact (@lem6941401 term102 term102). Qed.
Lemma lem6941403 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941404 : term137 = term102.
Proof. exact (EQ_MP (@lem6941403) (@lem940073)). Qed.
Lemma lem6941405 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941406 : term135 = term101.
Proof. exact (MK_COMB (@lem6941405) (@lem6941404)). Qed.
Lemma lem6941407 : term134 = term101.
Proof. exact (TRANS (@lem6941402) (@lem6941406)). Qed.
Lemma lem6941409 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6941410 : term164 = term169.
Proof. exact (@lem6941409 term102 term102). Qed.
Lemma lem6941411 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941412 : term137 = term102.
Proof. exact (EQ_MP (@lem6941411) (@lem940073)). Qed.
Lemma lem6941413 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941414 : term135 = term101.
Proof. exact (MK_COMB (@lem6941413) (@lem6941412)). Qed.
Lemma lem6941415 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6941416 : term169 = term125.
Proof. exact (MK_COMB (@lem6941415) (@lem6941414)). Qed.
Lemma lem6941417 : term164 = term125.
Proof. exact (TRANS (@lem6941410) (@lem6941416)). Qed.
Lemma lem6941418 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6941419 : term170 = term171.
Proof. exact (MK_COMB (@lem6941418) (@lem6941417)). Qed.
Lemma lem6941420 : term166 = term126.
Proof. exact (MK_COMB (@lem6941419) (@lem6941407)). Qed.
Lemma lem6941421 : term165 = term126.
Proof. exact (TRANS (@lem6941399) (@lem6941420)). Qed.
Lemma lem6941422 : term164 = term126.
Proof. exact (TRANS (@lem6941398) (@lem6941421)). Qed.
Lemma lem6941424 (x : real) : (term141 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6941425 : term126 = term125.
Proof. exact (@lem6941424 term125). Qed.
Lemma lem6941426 : term164 = term125.
Proof. exact (TRANS (@lem6941422) (@lem6941425)). Qed.
Lemma lem6941429 (_92531 : int) : (term172 _92531) = (term172 _92531).
Proof. exact (eq_refl (term172 _92531)). Qed.
Lemma lem6941430 (_92531 : int) : (term162 _92531) = (term173 _92531).
Proof. exact (MK_COMB (@lem6941429 _92531) (@lem6941426)). Qed.
Lemma lem6941431 (_92531 : int) : (term161 _92531) = (term173 _92531).
Proof. exact (TRANS (@lem6941389 _92531) (@lem6941430 _92531)). Qed.
Lemma lem6941432 (_92533 : int) : (term103 _92533) = (term103 _92533).
Proof. exact (eq_refl (term103 _92533)). Qed.
Lemma lem6941433 (_92533 : int) (_92531 : int) : (term160 _92533 _92531) = (term174 _92533 _92531).
Proof. exact (MK_COMB (@lem6941432 _92533) (@lem6941431 _92531)). Qed.
Lemma lem6941438 (_92531 : int) (_92533 : int) : (term174 _92533 _92531) = (term175 _92531 _92533).
Proof. exact (@lem1982757 (term176 _92531) (real_of_int _92533) term125). Qed.
Lemma lem6941439 (_92531 : int) (_92533 : int) : (term160 _92533 _92531) = (term175 _92531 _92533).
Proof. exact (TRANS (@lem6941433 _92533 _92531) (@lem6941438 _92531 _92533)). Qed.
Lemma lem6941441 (_92531 : int) (_92533 : int) : (term159 _92533 _92531) = (term175 _92531 _92533).
Proof. exact (TRANS (@lem6941388 _92533 _92531) (@lem6941439 _92531 _92533)). Qed.
Lemma lem6941442 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6941443 (_92531 : int) (_92533 : int) : (term177 _92533 _92531) = (term178 _92531 _92533).
Proof. exact (MK_COMB (@lem6941442) (@lem6941441 _92531 _92533)). Qed.
Lemma lem6941444 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6941445 (_92531 : int) (_92533 : int) : (term158 _92533 _92531) = (term179 _92531 _92533).
Proof. exact (MK_COMB (@lem6941443 _92531 _92533) (@lem6941444)). Qed.
Lemma lem6941446 (_92531 : int) (_92533 : int) : (term107 _92531 _92533) = (term179 _92531 _92533).
Proof. exact (TRANS (@lem6941376 _92533 _92531) (@lem6941445 _92531 _92533)). Qed.
Lemma lem6941447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6941448 (_92531 : int) (_92532 : int) : (term109 _92531 _92532) = (term180 _92531 _92532).
Proof. exact (MK_COMB (@lem6941447) (@lem6941375 _92531 _92532)). Qed.
Lemma lem6941449 (_92532 : int) (_92531 : int) (_92533 : int) : (term110 _92532 _92531 _92533) = (term181 _92532 _92531 _92533).
Proof. exact (MK_COMB (@lem6941448 _92531 _92532) (@lem6941446 _92531 _92533)). Qed.
Lemma lem6941450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6941451 (_92531 : int) (_92532 : int) (_92533 : int) : (term111 _92532 _92533 _92531) = (term182 _92531 _92532 _92533).
Proof. exact (MK_COMB (@lem6941450) (@lem6941304 _92531 _92532 _92533)). Qed.
Lemma lem6941452 (_92532 : int) (_92531 : int) (_92533 : int) : (term112 _92532 _92531 _92533) = (term183 _92532 _92531 _92533).
Proof. exact (MK_COMB (@lem6941451 _92531 _92532 _92533) (@lem6941449 _92532 _92531 _92533)). Qed.
Lemma lem6941453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6941454 (_92533 : int) : (term90 _92533) = (term155 _92533).
Proof. exact (MK_COMB (@lem6941453) (@lem6941171 _92533)). Qed.
Lemma lem6941455 (_92532 : int) (_92531 : int) (_92533 : int) : (term113 _92532 _92531 _92533) = (term184 _92532 _92531 _92533).
Proof. exact (MK_COMB (@lem6941454 _92533) (@lem6941452 _92532 _92531 _92533)). Qed.
Lemma lem6941456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6941457 (_92532 : int) : (term90 _92532) = (term155 _92532).
Proof. exact (MK_COMB (@lem6941456) (@lem6941123 _92532)). Qed.
Lemma lem6941458 (_92532 : int) (_92531 : int) (_92533 : int) : (term114 _92532 _92531 _92533) = (term185 _92532 _92531 _92533).
Proof. exact (MK_COMB (@lem6941457 _92532) (@lem6941455 _92532 _92531 _92533)). Qed.
Lemma lem6941459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6941460 (_92531 : int) : (term90 _92531) = (term155 _92531).
Proof. exact (MK_COMB (@lem6941459) (@lem6941075 _92531)). Qed.
Lemma lem6941461 (_92532 : int) (_92531 : int) (_92533 : int) : (term115 _92532 _92531 _92533) = (term186 _92532 _92531 _92533).
Proof. exact (MK_COMB (@lem6941460 _92531) (@lem6941458 _92532 _92531 _92533)). Qed.
Lemma lem6941468 (_92532 : int) (_92531 : int) (_92533 : int) : (term117 _92532 _92531 _92533) = (term186 _92532 _92531 _92533).
Proof. exact (TRANS (@lem6941027 _92532 _92531 _92533) (@lem6941461 _92532 _92531 _92533)). Qed.
Lemma lem6941497 (_92532 : int) (_92531 : int) (_92533 : int) : (term183 _92532 _92531 _92533) = (term187 _92532 _92531 _92533).
Proof. exact (@lem19158 (term179 _92531 _92532) (term157 _92531 _92532 _92533) (term179 _92531 _92533)). Qed.
Lemma lem6941500 (_92533 : int) : (term155 _92533) = (term155 _92533).
Proof. exact (eq_refl (term155 _92533)). Qed.
Lemma lem6941501 (_92532 : int) (_92531 : int) (_92533 : int) : (term184 _92532 _92531 _92533) = (term188 _92532 _92531 _92533).
Proof. exact (MK_COMB (@lem6941500 _92533) (@lem6941497 _92532 _92531 _92533)). Qed.
Lemma lem6941508 (_92532 : int) (_92531 : int) (_92533 : int) : (term188 _92532 _92531 _92533) = (term189 _92532 _92531 _92533).
Proof. exact (@lem19158 (term190 _92533 _92531 _92532) (term145 _92533) (term191 _92532 _92531 _92533)). Qed.
Lemma lem6941509 (_92532 : int) (_92531 : int) (_92533 : int) : (term184 _92532 _92531 _92533) = (term189 _92532 _92531 _92533).
Proof. exact (TRANS (@lem6941501 _92532 _92531 _92533) (@lem6941508 _92532 _92531 _92533)). Qed.
Lemma lem6941512 (_92532 : int) : (term155 _92532) = (term155 _92532).
Proof. exact (eq_refl (term155 _92532)). Qed.
Lemma lem6941513 (_92532 : int) (_92531 : int) (_92533 : int) : (term185 _92532 _92531 _92533) = (term192 _92532 _92531 _92533).
Proof. exact (MK_COMB (@lem6941512 _92532) (@lem6941509 _92532 _92531 _92533)). Qed.
Lemma lem6941520 (_92532 : int) (_92531 : int) (_92533 : int) : (term192 _92532 _92531 _92533) = (term193 _92532 _92531 _92533).
Proof. exact (@lem19158 (term194 _92533 _92531 _92532) (term145 _92532) (term195 _92532 _92531 _92533)). Qed.
Lemma lem6941521 (_92532 : int) (_92531 : int) (_92533 : int) : (term185 _92532 _92531 _92533) = (term193 _92532 _92531 _92533).
Proof. exact (TRANS (@lem6941513 _92532 _92531 _92533) (@lem6941520 _92532 _92531 _92533)). Qed.
Lemma lem6941524 (_92531 : int) : (term155 _92531) = (term155 _92531).
Proof. exact (eq_refl (term155 _92531)). Qed.
Lemma lem6941525 (_92532 : int) (_92531 : int) (_92533 : int) : (term186 _92532 _92531 _92533) = (term196 _92532 _92531 _92533).
Proof. exact (MK_COMB (@lem6941524 _92531) (@lem6941521 _92532 _92531 _92533)). Qed.
Lemma lem6941532 (_92532 : int) (_92531 : int) (_92533 : int) : (term196 _92532 _92531 _92533) = (term197 _92532 _92531 _92533).
Proof. exact (@lem19158 (term198 _92533 _92531 _92532) (term145 _92531) (term199 _92532 _92531 _92533)). Qed.
Lemma lem6941533 (_92532 : int) (_92531 : int) (_92533 : int) : (term186 _92532 _92531 _92533) = (term197 _92532 _92531 _92533).
Proof. exact (TRANS (@lem6941525 _92532 _92531 _92533) (@lem6941532 _92532 _92531 _92533)). Qed.
Lemma lem6941534 (_92532 : int) (_92531 : int) (_92533 : int) : (term117 _92532 _92531 _92533) = (term197 _92532 _92531 _92533).
Proof. exact (TRANS (@lem6941468 _92532 _92531 _92533) (@lem6941533 _92532 _92531 _92533)). Qed.
Lemma lem6941544 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term197 _92532 _92531 _92533) : term197 _92532 _92531 _92533.
Proof. exact (h1). Qed.
Lemma lem6941545 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term200 _92533 _92531 _92532.
Proof. exact (h1). Qed.
Lemma lem6941546 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term198 _92533 _92531 _92532.
Proof. exact (proj2 (@lem6941545 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941548 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term194 _92533 _92531 _92532.
Proof. exact (proj2 (@lem6941546 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941550 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term190 _92533 _92531 _92532.
Proof. exact (proj2 (@lem6941548 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941552 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term179 _92531 _92532.
Proof. exact (proj2 (@lem6941550 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941553 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term157 _92531 _92532 _92533.
Proof. exact (proj1 (@lem6941550 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941554 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term156 _92531 _92532 _92533.
Proof. exact (proj2 (@lem6941553 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941556 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term154 _92531 _92532 _92533.
Proof. exact (proj2 (@lem6941554 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941557 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term145 _92533.
Proof. exact (proj1 (@lem6941554 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941559 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6941560 : term201 = term202.
Proof. exact (@lem6941559 term80 term101). Qed.
Lemma lem6941562 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941563 : term101 = term163.
Proof. exact (@lem6941562 term102). Qed.
Lemma lem6941565 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941566 : term80 = term122.
Proof. exact (@lem6941565 (NUMERAL 0)). Qed.
Lemma lem6941567 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6941568 : term203 = term204.
Proof. exact (MK_COMB (@lem6941567) (@lem6941566)). Qed.
Lemma lem6941569 : term202 = term205.
Proof. exact (MK_COMB (@lem6941568) (@lem6941563)). Qed.
Lemma lem6941570 : term206.
Proof. exact (@lem1980255 term80 term101 term101 term101). Qed.
Lemma lem6941572 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941573 : term202 = term208.
Proof. exact (@lem6941572 (NUMERAL 0) term102). Qed.
Lemma lem6941574 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941575 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941576 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941575 h1) (fun h1 : term208 = True => @lem6941574)). Qed.
Lemma lem6941577 : term208 = True.
Proof. exact (EQ_MP (@lem6941576) (@lem6941574)). Qed.
Lemma lem6941578 : term202 = True.
Proof. exact (TRANS (@lem6941573) (@lem6941577)). Qed.
Lemma lem6941579 : True = term202.
Proof. exact (SYM (@lem6941578)). Qed.
Lemma lem6941580 : term202.
Proof. exact (EQ_MP (@lem6941579) (@lem0)). Qed.
Lemma lem6941581 : term210.
Proof. exact (@lem6941570 (@lem6941580)). Qed.
Lemma lem6941583 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941584 : term202 = term208.
Proof. exact (@lem6941583 (NUMERAL 0) term102). Qed.
Lemma lem6941585 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941586 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941587 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941586 h1) (fun h1 : term208 = True => @lem6941585)). Qed.
Lemma lem6941588 : term208 = True.
Proof. exact (EQ_MP (@lem6941587) (@lem6941585)). Qed.
Lemma lem6941589 : term202 = True.
Proof. exact (TRANS (@lem6941584) (@lem6941588)). Qed.
Lemma lem6941590 : True = term202.
Proof. exact (SYM (@lem6941589)). Qed.
Lemma lem6941591 : term202.
Proof. exact (EQ_MP (@lem6941590) (@lem0)). Qed.
Lemma lem6941592 : term205 = term211.
Proof. exact (@lem6941581 (@lem6941591)). Qed.
Lemma lem6941594 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6941595 : term134 = term135.
Proof. exact (@lem6941594 term102 term102). Qed.
Lemma lem6941596 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941597 : term137 = term102.
Proof. exact (EQ_MP (@lem6941596) (@lem940073)). Qed.
Lemma lem6941598 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941599 : term135 = term101.
Proof. exact (MK_COMB (@lem6941598) (@lem6941597)). Qed.
Lemma lem6941600 : term134 = term101.
Proof. exact (TRANS (@lem6941595) (@lem6941599)). Qed.
Lemma lem6941602 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6941603 : term213 = term80.
Proof. exact (@lem6941602 term102). Qed.
Lemma lem6941604 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6941605 : term214 = term203.
Proof. exact (MK_COMB (@lem6941604) (@lem6941603)). Qed.
Lemma lem6941606 : term211 = term202.
Proof. exact (MK_COMB (@lem6941605) (@lem6941600)). Qed.
Lemma lem6941608 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941609 : term202 = term208.
Proof. exact (@lem6941608 (NUMERAL 0) term102). Qed.
Lemma lem6941610 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941611 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941612 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941611 h1) (fun h1 : term208 = True => @lem6941610)). Qed.
Lemma lem6941613 : term208 = True.
Proof. exact (EQ_MP (@lem6941612) (@lem6941610)). Qed.
Lemma lem6941614 : term202 = True.
Proof. exact (TRANS (@lem6941609) (@lem6941613)). Qed.
Lemma lem6941615 : term211 = True.
Proof. exact (TRANS (@lem6941606) (@lem6941614)). Qed.
Lemma lem6941616 : term205 = True.
Proof. exact (TRANS (@lem6941592) (@lem6941615)). Qed.
Lemma lem6941617 : term202 = True.
Proof. exact (TRANS (@lem6941569) (@lem6941616)). Qed.
Lemma lem6941618 : term201 = True.
Proof. exact (TRANS (@lem6941560) (@lem6941617)). Qed.
Lemma lem6941619 : True = term201.
Proof. exact (SYM (@lem6941618)). Qed.
Lemma lem6941620 : term201.
Proof. exact (EQ_MP (@lem6941619) (@lem0)). Qed.
Lemma lem6941621 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term215 _92533.
Proof. exact (conj (@lem6941620) (@lem6941557 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941623 (x : real) (y : real) : term216 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6941624 (_92533 : int) : term217 _92533.
Proof. exact (@lem6941623 term101 (real_of_int _92533)). Qed.
Lemma lem6941625 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term218 _92533.
Proof. exact (@lem6941624 _92533 (@lem6941621 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941626 (_92533 : int) : (term219 _92533) = (real_of_int _92533).
Proof. exact (@lem1982733 (real_of_int _92533)). Qed.
Lemma lem6941627 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6941628 (_92533 : int) : (term220 _92533) = (term144 _92533).
Proof. exact (MK_COMB (@lem6941627) (@lem6941626 _92533)). Qed.
Lemma lem6941629 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6941630 (_92533 : int) : (term218 _92533) = (term145 _92533).
Proof. exact (MK_COMB (@lem6941628 _92533) (@lem6941629)). Qed.
Lemma lem6941631 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term145 _92533.
Proof. exact (EQ_MP (@lem6941630 _92533) (@lem6941625 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941633 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6941634 : term201 = term202.
Proof. exact (@lem6941633 term80 term101). Qed.
Lemma lem6941636 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941637 : term101 = term163.
Proof. exact (@lem6941636 term102). Qed.
Lemma lem6941639 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941640 : term80 = term122.
Proof. exact (@lem6941639 (NUMERAL 0)). Qed.
Lemma lem6941641 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6941642 : term203 = term204.
Proof. exact (MK_COMB (@lem6941641) (@lem6941640)). Qed.
Lemma lem6941643 : term202 = term205.
Proof. exact (MK_COMB (@lem6941642) (@lem6941637)). Qed.
Lemma lem6941644 : term206.
Proof. exact (@lem1980255 term80 term101 term101 term101). Qed.
Lemma lem6941646 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941647 : term202 = term208.
Proof. exact (@lem6941646 (NUMERAL 0) term102). Qed.
Lemma lem6941648 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941649 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941650 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941649 h1) (fun h1 : term208 = True => @lem6941648)). Qed.
Lemma lem6941651 : term208 = True.
Proof. exact (EQ_MP (@lem6941650) (@lem6941648)). Qed.
Lemma lem6941652 : term202 = True.
Proof. exact (TRANS (@lem6941647) (@lem6941651)). Qed.
Lemma lem6941653 : True = term202.
Proof. exact (SYM (@lem6941652)). Qed.
Lemma lem6941654 : term202.
Proof. exact (EQ_MP (@lem6941653) (@lem0)). Qed.
Lemma lem6941655 : term210.
Proof. exact (@lem6941644 (@lem6941654)). Qed.
Lemma lem6941657 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941658 : term202 = term208.
Proof. exact (@lem6941657 (NUMERAL 0) term102). Qed.
Lemma lem6941659 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941660 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941661 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941660 h1) (fun h1 : term208 = True => @lem6941659)). Qed.
Lemma lem6941662 : term208 = True.
Proof. exact (EQ_MP (@lem6941661) (@lem6941659)). Qed.
Lemma lem6941663 : term202 = True.
Proof. exact (TRANS (@lem6941658) (@lem6941662)). Qed.
Lemma lem6941664 : True = term202.
Proof. exact (SYM (@lem6941663)). Qed.
Lemma lem6941665 : term202.
Proof. exact (EQ_MP (@lem6941664) (@lem0)). Qed.
Lemma lem6941666 : term205 = term211.
Proof. exact (@lem6941655 (@lem6941665)). Qed.
Lemma lem6941668 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6941669 : term134 = term135.
Proof. exact (@lem6941668 term102 term102). Qed.
Lemma lem6941670 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941671 : term137 = term102.
Proof. exact (EQ_MP (@lem6941670) (@lem940073)). Qed.
Lemma lem6941672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941673 : term135 = term101.
Proof. exact (MK_COMB (@lem6941672) (@lem6941671)). Qed.
Lemma lem6941674 : term134 = term101.
Proof. exact (TRANS (@lem6941669) (@lem6941673)). Qed.
Lemma lem6941676 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6941677 : term213 = term80.
Proof. exact (@lem6941676 term102). Qed.
Lemma lem6941678 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6941679 : term214 = term203.
Proof. exact (MK_COMB (@lem6941678) (@lem6941677)). Qed.
Lemma lem6941680 : term211 = term202.
Proof. exact (MK_COMB (@lem6941679) (@lem6941674)). Qed.
Lemma lem6941682 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941683 : term202 = term208.
Proof. exact (@lem6941682 (NUMERAL 0) term102). Qed.
Lemma lem6941684 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941685 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941686 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941685 h1) (fun h1 : term208 = True => @lem6941684)). Qed.
Lemma lem6941687 : term208 = True.
Proof. exact (EQ_MP (@lem6941686) (@lem6941684)). Qed.
Lemma lem6941688 : term202 = True.
Proof. exact (TRANS (@lem6941683) (@lem6941687)). Qed.
Lemma lem6941689 : term211 = True.
Proof. exact (TRANS (@lem6941680) (@lem6941688)). Qed.
Lemma lem6941690 : term205 = True.
Proof. exact (TRANS (@lem6941666) (@lem6941689)). Qed.
Lemma lem6941691 : term202 = True.
Proof. exact (TRANS (@lem6941643) (@lem6941690)). Qed.
Lemma lem6941692 : term201 = True.
Proof. exact (TRANS (@lem6941634) (@lem6941691)). Qed.
Lemma lem6941693 : True = term201.
Proof. exact (SYM (@lem6941692)). Qed.
Lemma lem6941694 : term201.
Proof. exact (EQ_MP (@lem6941693) (@lem0)). Qed.
Lemma lem6941695 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term221 _92531 _92532 _92533.
Proof. exact (conj (@lem6941694) (@lem6941556 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941697 (x : real) (y : real) : term216 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6941698 (_92531 : int) (_92532 : int) (_92533 : int) : term222 _92531 _92532 _92533.
Proof. exact (@lem6941697 term101 (term151 _92531 _92532 _92533)). Qed.
Lemma lem6941699 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term223 _92531 _92532 _92533.
Proof. exact (@lem6941698 _92531 _92532 _92533 (@lem6941695 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941700 (_92531 : int) (_92532 : int) (_92533 : int) : (term224 _92531 _92532 _92533) = (term151 _92531 _92532 _92533).
Proof. exact (@lem1982733 (term151 _92531 _92532 _92533)). Qed.
Lemma lem6941701 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6941702 (_92531 : int) (_92532 : int) (_92533 : int) : (term225 _92531 _92532 _92533) = (term153 _92531 _92532 _92533).
Proof. exact (MK_COMB (@lem6941701) (@lem6941700 _92531 _92532 _92533)). Qed.
Lemma lem6941703 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6941704 (_92531 : int) (_92532 : int) (_92533 : int) : (term223 _92531 _92532 _92533) = (term154 _92531 _92532 _92533).
Proof. exact (MK_COMB (@lem6941702 _92531 _92532 _92533) (@lem6941703)). Qed.
Lemma lem6941705 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term154 _92531 _92532 _92533.
Proof. exact (EQ_MP (@lem6941704 _92531 _92532 _92533) (@lem6941699 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941707 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6941708 : term201 = term202.
Proof. exact (@lem6941707 term80 term101). Qed.
Lemma lem6941710 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941711 : term101 = term163.
Proof. exact (@lem6941710 term102). Qed.
Lemma lem6941713 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941714 : term80 = term122.
Proof. exact (@lem6941713 (NUMERAL 0)). Qed.
Lemma lem6941715 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6941716 : term203 = term204.
Proof. exact (MK_COMB (@lem6941715) (@lem6941714)). Qed.
Lemma lem6941717 : term202 = term205.
Proof. exact (MK_COMB (@lem6941716) (@lem6941711)). Qed.
Lemma lem6941718 : term206.
Proof. exact (@lem1980255 term80 term101 term101 term101). Qed.
Lemma lem6941720 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941721 : term202 = term208.
Proof. exact (@lem6941720 (NUMERAL 0) term102). Qed.
Lemma lem6941722 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941723 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941724 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941723 h1) (fun h1 : term208 = True => @lem6941722)). Qed.
Lemma lem6941725 : term208 = True.
Proof. exact (EQ_MP (@lem6941724) (@lem6941722)). Qed.
Lemma lem6941726 : term202 = True.
Proof. exact (TRANS (@lem6941721) (@lem6941725)). Qed.
Lemma lem6941727 : True = term202.
Proof. exact (SYM (@lem6941726)). Qed.
Lemma lem6941728 : term202.
Proof. exact (EQ_MP (@lem6941727) (@lem0)). Qed.
Lemma lem6941729 : term210.
Proof. exact (@lem6941718 (@lem6941728)). Qed.
Lemma lem6941731 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941732 : term202 = term208.
Proof. exact (@lem6941731 (NUMERAL 0) term102). Qed.
Lemma lem6941733 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941734 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941735 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941734 h1) (fun h1 : term208 = True => @lem6941733)). Qed.
Lemma lem6941736 : term208 = True.
Proof. exact (EQ_MP (@lem6941735) (@lem6941733)). Qed.
Lemma lem6941737 : term202 = True.
Proof. exact (TRANS (@lem6941732) (@lem6941736)). Qed.
Lemma lem6941738 : True = term202.
Proof. exact (SYM (@lem6941737)). Qed.
Lemma lem6941739 : term202.
Proof. exact (EQ_MP (@lem6941738) (@lem0)). Qed.
Lemma lem6941740 : term205 = term211.
Proof. exact (@lem6941729 (@lem6941739)). Qed.
Lemma lem6941742 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6941743 : term134 = term135.
Proof. exact (@lem6941742 term102 term102). Qed.
Lemma lem6941744 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941745 : term137 = term102.
Proof. exact (EQ_MP (@lem6941744) (@lem940073)). Qed.
Lemma lem6941746 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941747 : term135 = term101.
Proof. exact (MK_COMB (@lem6941746) (@lem6941745)). Qed.
Lemma lem6941748 : term134 = term101.
Proof. exact (TRANS (@lem6941743) (@lem6941747)). Qed.
Lemma lem6941750 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6941751 : term213 = term80.
Proof. exact (@lem6941750 term102). Qed.
Lemma lem6941752 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6941753 : term214 = term203.
Proof. exact (MK_COMB (@lem6941752) (@lem6941751)). Qed.
Lemma lem6941754 : term211 = term202.
Proof. exact (MK_COMB (@lem6941753) (@lem6941748)). Qed.
Lemma lem6941756 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941757 : term202 = term208.
Proof. exact (@lem6941756 (NUMERAL 0) term102). Qed.
Lemma lem6941758 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941759 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941760 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941759 h1) (fun h1 : term208 = True => @lem6941758)). Qed.
Lemma lem6941761 : term208 = True.
Proof. exact (EQ_MP (@lem6941760) (@lem6941758)). Qed.
Lemma lem6941762 : term202 = True.
Proof. exact (TRANS (@lem6941757) (@lem6941761)). Qed.
Lemma lem6941763 : term211 = True.
Proof. exact (TRANS (@lem6941754) (@lem6941762)). Qed.
Lemma lem6941764 : term205 = True.
Proof. exact (TRANS (@lem6941740) (@lem6941763)). Qed.
Lemma lem6941765 : term202 = True.
Proof. exact (TRANS (@lem6941717) (@lem6941764)). Qed.
Lemma lem6941766 : term201 = True.
Proof. exact (TRANS (@lem6941708) (@lem6941765)). Qed.
Lemma lem6941767 : True = term201.
Proof. exact (SYM (@lem6941766)). Qed.
Lemma lem6941768 : term201.
Proof. exact (EQ_MP (@lem6941767) (@lem0)). Qed.
Lemma lem6941769 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term226 _92531 _92532.
Proof. exact (conj (@lem6941768) (@lem6941552 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941771 (x : real) (y : real) : term216 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6941772 (_92531 : int) (_92532 : int) : term227 _92531 _92532.
Proof. exact (@lem6941771 term101 (term175 _92531 _92532)). Qed.
Lemma lem6941773 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term228 _92531 _92532.
Proof. exact (@lem6941772 _92531 _92532 (@lem6941769 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941774 (_92531 : int) (_92532 : int) : (term229 _92531 _92532) = (term175 _92531 _92532).
Proof. exact (@lem1982733 (term175 _92531 _92532)). Qed.
Lemma lem6941775 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6941776 (_92531 : int) (_92532 : int) : (term230 _92531 _92532) = (term178 _92531 _92532).
Proof. exact (MK_COMB (@lem6941775) (@lem6941774 _92531 _92532)). Qed.
Lemma lem6941777 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6941778 (_92531 : int) (_92532 : int) : (term228 _92531 _92532) = (term179 _92531 _92532).
Proof. exact (MK_COMB (@lem6941776 _92531 _92532) (@lem6941777)). Qed.
Lemma lem6941779 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term179 _92531 _92532.
Proof. exact (EQ_MP (@lem6941778 _92531 _92532) (@lem6941773 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941780 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term231 _92531 _92532 _92533.
Proof. exact (conj (@lem6941779 _92533 _92531 _92532 h1) (@lem6941705 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941782 (x : real) (y : real) : term232 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6941783 (_92531 : int) (_92532 : int) (_92533 : int) : term233 _92531 _92532 _92533.
Proof. exact (@lem6941782 (term175 _92531 _92532) (term151 _92531 _92532 _92533)). Qed.
Lemma lem6941784 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term234 _92531 _92532 _92533.
Proof. exact (@lem6941783 _92531 _92532 _92533 (@lem6941780 _92533 _92531 _92532 h1)). Qed.
Lemma lem6941785 (_92531 : int) (_92532 : int) (_92533 : int) : (term235 _92531 _92532 _92533) = (term236 _92531 _92532 _92533).
Proof. exact (@lem1982753 (term176 _92531) (real_of_int _92531) (term237 _92532) (term150 _92532 _92533)). Qed.
Lemma lem6941786 (_92531 : int) : (term238 _92531) = (term239 _92531).
Proof. exact (@lem1982713 term125 (real_of_int _92531)). Qed.
Lemma lem6941788 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941789 : term101 = term163.
Proof. exact (@lem6941788 term102). Qed.
Lemma lem6941791 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6941792 : term125 = term126.
Proof. exact (@lem6941791 term102). Qed.
Lemma lem6941793 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6941794 : term240 = term241.
Proof. exact (MK_COMB (@lem6941793) (@lem6941792)). Qed.
Lemma lem6941795 : term242 = term243.
Proof. exact (MK_COMB (@lem6941794) (@lem6941789)). Qed.
Lemma lem6941796 : term244.
Proof. exact (@lem1981473 term125 term101 term101 term101 term80 term101). Qed.
Lemma lem6941798 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941799 : term202 = term208.
Proof. exact (@lem6941798 (NUMERAL 0) term102). Qed.
Lemma lem6941800 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941801 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941802 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941801 h1) (fun h1 : term208 = True => @lem6941800)). Qed.
Lemma lem6941803 : term208 = True.
Proof. exact (EQ_MP (@lem6941802) (@lem6941800)). Qed.
Lemma lem6941804 : term202 = True.
Proof. exact (TRANS (@lem6941799) (@lem6941803)). Qed.
Lemma lem6941805 : True = term202.
Proof. exact (SYM (@lem6941804)). Qed.
Lemma lem6941806 : term202.
Proof. exact (EQ_MP (@lem6941805) (@lem0)). Qed.
Lemma lem6941807 : term245.
Proof. exact (@lem6941796 (@lem6941806)). Qed.
Lemma lem6941809 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941810 : term202 = term208.
Proof. exact (@lem6941809 (NUMERAL 0) term102). Qed.
Lemma lem6941811 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941812 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941813 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941812 h1) (fun h1 : term208 = True => @lem6941811)). Qed.
Lemma lem6941814 : term208 = True.
Proof. exact (EQ_MP (@lem6941813) (@lem6941811)). Qed.
Lemma lem6941815 : term202 = True.
Proof. exact (TRANS (@lem6941810) (@lem6941814)). Qed.
Lemma lem6941816 : True = term202.
Proof. exact (SYM (@lem6941815)). Qed.
Lemma lem6941817 : term202.
Proof. exact (EQ_MP (@lem6941816) (@lem0)). Qed.
Lemma lem6941818 : term246.
Proof. exact (@lem6941807 (@lem6941817)). Qed.
Lemma lem6941820 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941821 : term202 = term208.
Proof. exact (@lem6941820 (NUMERAL 0) term102). Qed.
Lemma lem6941822 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941823 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941824 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941823 h1) (fun h1 : term208 = True => @lem6941822)). Qed.
Lemma lem6941825 : term208 = True.
Proof. exact (EQ_MP (@lem6941824) (@lem6941822)). Qed.
Lemma lem6941826 : term202 = True.
Proof. exact (TRANS (@lem6941821) (@lem6941825)). Qed.
Lemma lem6941827 : True = term202.
Proof. exact (SYM (@lem6941826)). Qed.
Lemma lem6941828 : term202.
Proof. exact (EQ_MP (@lem6941827) (@lem0)). Qed.
Lemma lem6941829 : term247.
Proof. exact (@lem6941818 (@lem6941828)). Qed.
Lemma lem6941831 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6941832 : term134 = term135.
Proof. exact (@lem6941831 term102 term102). Qed.
Lemma lem6941833 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941834 : term137 = term102.
Proof. exact (EQ_MP (@lem6941833) (@lem940073)). Qed.
Lemma lem6941835 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941836 : term135 = term101.
Proof. exact (MK_COMB (@lem6941835) (@lem6941834)). Qed.
Lemma lem6941837 : term134 = term101.
Proof. exact (TRANS (@lem6941832) (@lem6941836)). Qed.
Lemma lem6941839 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6941840 : term164 = term169.
Proof. exact (@lem6941839 term102 term102). Qed.
Lemma lem6941841 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941842 : term137 = term102.
Proof. exact (EQ_MP (@lem6941841) (@lem940073)). Qed.
Lemma lem6941843 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941844 : term135 = term101.
Proof. exact (MK_COMB (@lem6941843) (@lem6941842)). Qed.
Lemma lem6941845 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6941846 : term169 = term125.
Proof. exact (MK_COMB (@lem6941845) (@lem6941844)). Qed.
Lemma lem6941847 : term164 = term125.
Proof. exact (TRANS (@lem6941840) (@lem6941846)). Qed.
Lemma lem6941848 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6941849 : term248 = term240.
Proof. exact (MK_COMB (@lem6941848) (@lem6941847)). Qed.
Lemma lem6941850 : term249 = term242.
Proof. exact (MK_COMB (@lem6941849) (@lem6941837)). Qed.
Lemma lem6941852 (m : nat) : (term250 m) = term80.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6941853 : term242 = term80.
Proof. exact (@lem6941852 term102). Qed.
Lemma lem6941854 : term249 = term80.
Proof. exact (TRANS (@lem6941850) (@lem6941853)). Qed.
Lemma lem6941855 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6941856 : term251 = term252.
Proof. exact (MK_COMB (@lem6941855) (@lem6941854)). Qed.
Lemma lem6941857 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem6941858 : term253 = term213.
Proof. exact (MK_COMB (@lem6941856) (@lem6941857)). Qed.
Lemma lem6941860 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6941861 : term213 = term80.
Proof. exact (@lem6941860 term102). Qed.
Lemma lem6941862 : term253 = term80.
Proof. exact (TRANS (@lem6941858) (@lem6941861)). Qed.
Lemma lem6941864 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6941865 : term134 = term135.
Proof. exact (@lem6941864 term102 term102). Qed.
Lemma lem6941866 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941867 : term137 = term102.
Proof. exact (EQ_MP (@lem6941866) (@lem940073)). Qed.
Lemma lem6941868 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941869 : term135 = term101.
Proof. exact (MK_COMB (@lem6941868) (@lem6941867)). Qed.
Lemma lem6941870 : term134 = term101.
Proof. exact (TRANS (@lem6941865) (@lem6941869)). Qed.
Lemma lem6941871 : term252 = term252.
Proof. exact (eq_refl term252). Qed.
Lemma lem6941872 : term254 = term213.
Proof. exact (MK_COMB (@lem6941871) (@lem6941870)). Qed.
Lemma lem6941874 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6941875 : term213 = term80.
Proof. exact (@lem6941874 term102). Qed.
Lemma lem6941876 : term254 = term80.
Proof. exact (TRANS (@lem6941872) (@lem6941875)). Qed.
Lemma lem6941877 : term80 = term254.
Proof. exact (SYM (@lem6941876)). Qed.
Lemma lem6941878 : term253 = term254.
Proof. exact (TRANS (@lem6941862) (@lem6941877)). Qed.
Lemma lem6941879 : term243 = term122.
Proof. exact (@lem6941829 (@lem6941878)). Qed.
Lemma lem6941880 : term242 = term122.
Proof. exact (TRANS (@lem6941795) (@lem6941879)). Qed.
Lemma lem6941882 (x : real) : (term141 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6941883 : term122 = term80.
Proof. exact (@lem6941882 term80). Qed.
Lemma lem6941884 : term242 = term80.
Proof. exact (TRANS (@lem6941880) (@lem6941883)). Qed.
Lemma lem6941885 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6941886 : term255 = term252.
Proof. exact (MK_COMB (@lem6941885) (@lem6941884)). Qed.
Lemma lem6941887 (_92531 : int) : (real_of_int _92531) = (real_of_int _92531).
Proof. exact (eq_refl (real_of_int _92531)). Qed.
Lemma lem6941888 (_92531 : int) : (term239 _92531) = (term256 _92531).
Proof. exact (MK_COMB (@lem6941886) (@lem6941887 _92531)). Qed.
Lemma lem6941889 (_92531 : int) : (term238 _92531) = (term256 _92531).
Proof. exact (TRANS (@lem6941786 _92531) (@lem6941888 _92531)). Qed.
Lemma lem6941890 (_92531 : int) : (term256 _92531) = term80.
Proof. exact (@lem1982719 (real_of_int _92531)). Qed.
Lemma lem6941891 (_92531 : int) : (term238 _92531) = term80.
Proof. exact (TRANS (@lem6941889 _92531) (@lem6941890 _92531)). Qed.
Lemma lem6941892 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6941893 (_92531 : int) : (term257 _92531) = term258.
Proof. exact (MK_COMB (@lem6941892) (@lem6941891 _92531)). Qed.
Lemma lem6941894 (_92532 : int) (_92533 : int) : (term259 _92532 _92533) = (term260 _92532 _92533).
Proof. exact (@lem1982753 (real_of_int _92532) (term176 _92532) term125 (term176 _92533)). Qed.
Lemma lem6941895 (_92532 : int) : (term261 _92532) = (term239 _92532).
Proof. exact (@lem1982715 term125 (real_of_int _92532)). Qed.
Lemma lem6941897 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6941898 : term101 = term163.
Proof. exact (@lem6941897 term102). Qed.
Lemma lem6941900 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6941901 : term125 = term126.
Proof. exact (@lem6941900 term102). Qed.
Lemma lem6941902 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6941903 : term240 = term241.
Proof. exact (MK_COMB (@lem6941902) (@lem6941901)). Qed.
Lemma lem6941904 : term242 = term243.
Proof. exact (MK_COMB (@lem6941903) (@lem6941898)). Qed.
Lemma lem6941905 : term244.
Proof. exact (@lem1981473 term125 term101 term101 term101 term80 term101). Qed.
Lemma lem6941907 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941908 : term202 = term208.
Proof. exact (@lem6941907 (NUMERAL 0) term102). Qed.
Lemma lem6941909 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941910 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941911 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941910 h1) (fun h1 : term208 = True => @lem6941909)). Qed.
Lemma lem6941912 : term208 = True.
Proof. exact (EQ_MP (@lem6941911) (@lem6941909)). Qed.
Lemma lem6941913 : term202 = True.
Proof. exact (TRANS (@lem6941908) (@lem6941912)). Qed.
Lemma lem6941914 : True = term202.
Proof. exact (SYM (@lem6941913)). Qed.
Lemma lem6941915 : term202.
Proof. exact (EQ_MP (@lem6941914) (@lem0)). Qed.
Lemma lem6941916 : term245.
Proof. exact (@lem6941905 (@lem6941915)). Qed.
Lemma lem6941918 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941919 : term202 = term208.
Proof. exact (@lem6941918 (NUMERAL 0) term102). Qed.
Lemma lem6941920 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941921 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941922 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941921 h1) (fun h1 : term208 = True => @lem6941920)). Qed.
Lemma lem6941923 : term208 = True.
Proof. exact (EQ_MP (@lem6941922) (@lem6941920)). Qed.
Lemma lem6941924 : term202 = True.
Proof. exact (TRANS (@lem6941919) (@lem6941923)). Qed.
Lemma lem6941925 : True = term202.
Proof. exact (SYM (@lem6941924)). Qed.
Lemma lem6941926 : term202.
Proof. exact (EQ_MP (@lem6941925) (@lem0)). Qed.
Lemma lem6941927 : term246.
Proof. exact (@lem6941916 (@lem6941926)). Qed.
Lemma lem6941929 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6941930 : term202 = term208.
Proof. exact (@lem6941929 (NUMERAL 0) term102). Qed.
Lemma lem6941931 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6941932 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6941933 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6941932 h1) (fun h1 : term208 = True => @lem6941931)). Qed.
Lemma lem6941934 : term208 = True.
Proof. exact (EQ_MP (@lem6941933) (@lem6941931)). Qed.
Lemma lem6941935 : term202 = True.
Proof. exact (TRANS (@lem6941930) (@lem6941934)). Qed.
Lemma lem6941936 : True = term202.
Proof. exact (SYM (@lem6941935)). Qed.
Lemma lem6941937 : term202.
Proof. exact (EQ_MP (@lem6941936) (@lem0)). Qed.
Lemma lem6941938 : term247.
Proof. exact (@lem6941927 (@lem6941937)). Qed.
Lemma lem6941940 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6941941 : term134 = term135.
Proof. exact (@lem6941940 term102 term102). Qed.
Lemma lem6941942 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941943 : term137 = term102.
Proof. exact (EQ_MP (@lem6941942) (@lem940073)). Qed.
Lemma lem6941944 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941945 : term135 = term101.
Proof. exact (MK_COMB (@lem6941944) (@lem6941943)). Qed.
Lemma lem6941946 : term134 = term101.
Proof. exact (TRANS (@lem6941941) (@lem6941945)). Qed.
Lemma lem6941948 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6941949 : term164 = term169.
Proof. exact (@lem6941948 term102 term102). Qed.
Lemma lem6941950 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941951 : term137 = term102.
Proof. exact (EQ_MP (@lem6941950) (@lem940073)). Qed.
Lemma lem6941952 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941953 : term135 = term101.
Proof. exact (MK_COMB (@lem6941952) (@lem6941951)). Qed.
Lemma lem6941954 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6941955 : term169 = term125.
Proof. exact (MK_COMB (@lem6941954) (@lem6941953)). Qed.
Lemma lem6941956 : term164 = term125.
Proof. exact (TRANS (@lem6941949) (@lem6941955)). Qed.
Lemma lem6941957 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6941958 : term248 = term240.
Proof. exact (MK_COMB (@lem6941957) (@lem6941956)). Qed.
Lemma lem6941959 : term249 = term242.
Proof. exact (MK_COMB (@lem6941958) (@lem6941946)). Qed.
Lemma lem6941961 (m : nat) : (term250 m) = term80.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6941962 : term242 = term80.
Proof. exact (@lem6941961 term102). Qed.
Lemma lem6941963 : term249 = term80.
Proof. exact (TRANS (@lem6941959) (@lem6941962)). Qed.
Lemma lem6941964 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6941965 : term251 = term252.
Proof. exact (MK_COMB (@lem6941964) (@lem6941963)). Qed.
Lemma lem6941966 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem6941967 : term253 = term213.
Proof. exact (MK_COMB (@lem6941965) (@lem6941966)). Qed.
Lemma lem6941969 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6941970 : term213 = term80.
Proof. exact (@lem6941969 term102). Qed.
Lemma lem6941971 : term253 = term80.
Proof. exact (TRANS (@lem6941967) (@lem6941970)). Qed.
Lemma lem6941973 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6941974 : term134 = term135.
Proof. exact (@lem6941973 term102 term102). Qed.
Lemma lem6941975 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6941976 : term137 = term102.
Proof. exact (EQ_MP (@lem6941975) (@lem940073)). Qed.
Lemma lem6941977 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6941978 : term135 = term101.
Proof. exact (MK_COMB (@lem6941977) (@lem6941976)). Qed.
Lemma lem6941979 : term134 = term101.
Proof. exact (TRANS (@lem6941974) (@lem6941978)). Qed.
Lemma lem6941980 : term252 = term252.
Proof. exact (eq_refl term252). Qed.
Lemma lem6941981 : term254 = term213.
Proof. exact (MK_COMB (@lem6941980) (@lem6941979)). Qed.
Lemma lem6941983 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6941984 : term213 = term80.
Proof. exact (@lem6941983 term102). Qed.
Lemma lem6941985 : term254 = term80.
Proof. exact (TRANS (@lem6941981) (@lem6941984)). Qed.
Lemma lem6941986 : term80 = term254.
Proof. exact (SYM (@lem6941985)). Qed.
Lemma lem6941987 : term253 = term254.
Proof. exact (TRANS (@lem6941971) (@lem6941986)). Qed.
Lemma lem6941988 : term243 = term122.
Proof. exact (@lem6941938 (@lem6941987)). Qed.
Lemma lem6941989 : term242 = term122.
Proof. exact (TRANS (@lem6941904) (@lem6941988)). Qed.
Lemma lem6941991 (x : real) : (term141 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6941992 : term122 = term80.
Proof. exact (@lem6941991 term80). Qed.
Lemma lem6941993 : term242 = term80.
Proof. exact (TRANS (@lem6941989) (@lem6941992)). Qed.
Lemma lem6941994 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6941995 : term255 = term252.
Proof. exact (MK_COMB (@lem6941994) (@lem6941993)). Qed.
Lemma lem6941996 (_92532 : int) : (real_of_int _92532) = (real_of_int _92532).
Proof. exact (eq_refl (real_of_int _92532)). Qed.
Lemma lem6941997 (_92532 : int) : (term239 _92532) = (term256 _92532).
Proof. exact (MK_COMB (@lem6941995) (@lem6941996 _92532)). Qed.
Lemma lem6941998 (_92532 : int) : (term261 _92532) = (term256 _92532).
Proof. exact (TRANS (@lem6941895 _92532) (@lem6941997 _92532)). Qed.
Lemma lem6941999 (_92532 : int) : (term256 _92532) = term80.
Proof. exact (@lem1982719 (real_of_int _92532)). Qed.
Lemma lem6942000 (_92532 : int) : (term261 _92532) = term80.
Proof. exact (TRANS (@lem6941998 _92532) (@lem6941999 _92532)). Qed.
Lemma lem6942001 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6942002 (_92532 : int) : (term262 _92532) = term258.
Proof. exact (MK_COMB (@lem6942001) (@lem6942000 _92532)). Qed.
Lemma lem6942003 (_92533 : int) : (term263 _92533) = (term173 _92533).
Proof. exact (@lem1982761 (term176 _92533) term125). Qed.
Lemma lem6942004 (_92532 : int) (_92533 : int) : (term260 _92532 _92533) = (term264 _92533).
Proof. exact (MK_COMB (@lem6942002 _92532) (@lem6942003 _92533)). Qed.
Lemma lem6942005 (_92532 : int) (_92533 : int) : (term259 _92532 _92533) = (term264 _92533).
Proof. exact (TRANS (@lem6941894 _92532 _92533) (@lem6942004 _92532 _92533)). Qed.
Lemma lem6942006 (_92533 : int) : (term264 _92533) = (term173 _92533).
Proof. exact (@lem1982721 (term173 _92533)). Qed.
Lemma lem6942007 (_92532 : int) (_92533 : int) : (term259 _92532 _92533) = (term173 _92533).
Proof. exact (TRANS (@lem6942005 _92532 _92533) (@lem6942006 _92533)). Qed.
Lemma lem6942008 (_92531 : int) (_92532 : int) (_92533 : int) : (term236 _92531 _92532 _92533) = (term264 _92533).
Proof. exact (MK_COMB (@lem6941893 _92531) (@lem6942007 _92532 _92533)). Qed.
Lemma lem6942009 (_92531 : int) (_92532 : int) (_92533 : int) : (term235 _92531 _92532 _92533) = (term264 _92533).
Proof. exact (TRANS (@lem6941785 _92531 _92532 _92533) (@lem6942008 _92531 _92532 _92533)). Qed.
Lemma lem6942010 (_92533 : int) : (term264 _92533) = (term173 _92533).
Proof. exact (@lem1982721 (term173 _92533)). Qed.
Lemma lem6942011 (_92531 : int) (_92532 : int) (_92533 : int) : (term235 _92531 _92532 _92533) = (term173 _92533).
Proof. exact (TRANS (@lem6942009 _92531 _92532 _92533) (@lem6942010 _92533)). Qed.
Lemma lem6942012 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6942013 (_92531 : int) (_92532 : int) (_92533 : int) : (term265 _92531 _92532 _92533) = (term266 _92533).
Proof. exact (MK_COMB (@lem6942012) (@lem6942011 _92531 _92532 _92533)). Qed.
Lemma lem6942014 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6942015 (_92531 : int) (_92532 : int) (_92533 : int) : (term234 _92531 _92532 _92533) = (term267 _92533).
Proof. exact (MK_COMB (@lem6942013 _92531 _92532 _92533) (@lem6942014)). Qed.
Lemma lem6942016 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term267 _92533.
Proof. exact (EQ_MP (@lem6942015 _92531 _92532 _92533) (@lem6941784 _92533 _92531 _92532 h1)). Qed.
Lemma lem6942018 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6942019 : term201 = term202.
Proof. exact (@lem6942018 term80 term101). Qed.
Lemma lem6942021 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942022 : term101 = term163.
Proof. exact (@lem6942021 term102). Qed.
Lemma lem6942024 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942025 : term80 = term122.
Proof. exact (@lem6942024 (NUMERAL 0)). Qed.
Lemma lem6942026 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6942027 : term203 = term204.
Proof. exact (MK_COMB (@lem6942026) (@lem6942025)). Qed.
Lemma lem6942028 : term202 = term205.
Proof. exact (MK_COMB (@lem6942027) (@lem6942022)). Qed.
Lemma lem6942029 : term206.
Proof. exact (@lem1980255 term80 term101 term101 term101). Qed.
Lemma lem6942031 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942032 : term202 = term208.
Proof. exact (@lem6942031 (NUMERAL 0) term102). Qed.
Lemma lem6942033 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942034 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942035 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942034 h1) (fun h1 : term208 = True => @lem6942033)). Qed.
Lemma lem6942036 : term208 = True.
Proof. exact (EQ_MP (@lem6942035) (@lem6942033)). Qed.
Lemma lem6942037 : term202 = True.
Proof. exact (TRANS (@lem6942032) (@lem6942036)). Qed.
Lemma lem6942038 : True = term202.
Proof. exact (SYM (@lem6942037)). Qed.
Lemma lem6942039 : term202.
Proof. exact (EQ_MP (@lem6942038) (@lem0)). Qed.
Lemma lem6942040 : term210.
Proof. exact (@lem6942029 (@lem6942039)). Qed.
Lemma lem6942042 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942043 : term202 = term208.
Proof. exact (@lem6942042 (NUMERAL 0) term102). Qed.
Lemma lem6942044 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942045 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942046 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942045 h1) (fun h1 : term208 = True => @lem6942044)). Qed.
Lemma lem6942047 : term208 = True.
Proof. exact (EQ_MP (@lem6942046) (@lem6942044)). Qed.
Lemma lem6942048 : term202 = True.
Proof. exact (TRANS (@lem6942043) (@lem6942047)). Qed.
Lemma lem6942049 : True = term202.
Proof. exact (SYM (@lem6942048)). Qed.
Lemma lem6942050 : term202.
Proof. exact (EQ_MP (@lem6942049) (@lem0)). Qed.
Lemma lem6942051 : term205 = term211.
Proof. exact (@lem6942040 (@lem6942050)). Qed.
Lemma lem6942053 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6942054 : term134 = term135.
Proof. exact (@lem6942053 term102 term102). Qed.
Lemma lem6942055 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942056 : term137 = term102.
Proof. exact (EQ_MP (@lem6942055) (@lem940073)). Qed.
Lemma lem6942057 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942058 : term135 = term101.
Proof. exact (MK_COMB (@lem6942057) (@lem6942056)). Qed.
Lemma lem6942059 : term134 = term101.
Proof. exact (TRANS (@lem6942054) (@lem6942058)). Qed.
Lemma lem6942061 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6942062 : term213 = term80.
Proof. exact (@lem6942061 term102). Qed.
Lemma lem6942063 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6942064 : term214 = term203.
Proof. exact (MK_COMB (@lem6942063) (@lem6942062)). Qed.
Lemma lem6942065 : term211 = term202.
Proof. exact (MK_COMB (@lem6942064) (@lem6942059)). Qed.
Lemma lem6942067 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942068 : term202 = term208.
Proof. exact (@lem6942067 (NUMERAL 0) term102). Qed.
Lemma lem6942069 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942070 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942071 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942070 h1) (fun h1 : term208 = True => @lem6942069)). Qed.
Lemma lem6942072 : term208 = True.
Proof. exact (EQ_MP (@lem6942071) (@lem6942069)). Qed.
Lemma lem6942073 : term202 = True.
Proof. exact (TRANS (@lem6942068) (@lem6942072)). Qed.
Lemma lem6942074 : term211 = True.
Proof. exact (TRANS (@lem6942065) (@lem6942073)). Qed.
Lemma lem6942075 : term205 = True.
Proof. exact (TRANS (@lem6942051) (@lem6942074)). Qed.
Lemma lem6942076 : term202 = True.
Proof. exact (TRANS (@lem6942028) (@lem6942075)). Qed.
Lemma lem6942077 : term201 = True.
Proof. exact (TRANS (@lem6942019) (@lem6942076)). Qed.
Lemma lem6942078 : True = term201.
Proof. exact (SYM (@lem6942077)). Qed.
Lemma lem6942079 : term201.
Proof. exact (EQ_MP (@lem6942078) (@lem0)). Qed.
Lemma lem6942080 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term268 _92533.
Proof. exact (conj (@lem6942079) (@lem6942016 _92533 _92531 _92532 h1)). Qed.
Lemma lem6942082 (x : real) (y : real) : term216 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6942083 (_92533 : int) : term269 _92533.
Proof. exact (@lem6942082 term101 (term173 _92533)). Qed.
Lemma lem6942084 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term270 _92533.
Proof. exact (@lem6942083 _92533 (@lem6942080 _92533 _92531 _92532 h1)). Qed.
Lemma lem6942085 (_92533 : int) : (term271 _92533) = (term173 _92533).
Proof. exact (@lem1982733 (term173 _92533)). Qed.
Lemma lem6942086 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6942087 (_92533 : int) : (term272 _92533) = (term266 _92533).
Proof. exact (MK_COMB (@lem6942086) (@lem6942085 _92533)). Qed.
Lemma lem6942088 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6942089 (_92533 : int) : (term270 _92533) = (term267 _92533).
Proof. exact (MK_COMB (@lem6942087 _92533) (@lem6942088)). Qed.
Lemma lem6942090 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term267 _92533.
Proof. exact (EQ_MP (@lem6942089 _92533) (@lem6942084 _92533 _92531 _92532 h1)). Qed.
Lemma lem6942091 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term273 _92533.
Proof. exact (conj (@lem6942090 _92533 _92531 _92532 h1) (@lem6941631 _92533 _92531 _92532 h1)). Qed.
Lemma lem6942093 (x : real) (y : real) : term232 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6942094 (_92533 : int) : term274 _92533.
Proof. exact (@lem6942093 (term173 _92533) (real_of_int _92533)). Qed.
Lemma lem6942095 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term275 _92533.
Proof. exact (@lem6942094 _92533 (@lem6942091 _92533 _92531 _92532 h1)). Qed.
Lemma lem6942096 (_92533 : int) : (term276 _92533) = (term277 _92533).
Proof. exact (@lem1982759 (term176 _92533) (real_of_int _92533) term125). Qed.
Lemma lem6942097 (_92533 : int) : (term238 _92533) = (term239 _92533).
Proof. exact (@lem1982713 term125 (real_of_int _92533)). Qed.
Lemma lem6942099 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942100 : term101 = term163.
Proof. exact (@lem6942099 term102). Qed.
Lemma lem6942102 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6942103 : term125 = term126.
Proof. exact (@lem6942102 term102). Qed.
Lemma lem6942104 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6942105 : term240 = term241.
Proof. exact (MK_COMB (@lem6942104) (@lem6942103)). Qed.
Lemma lem6942106 : term242 = term243.
Proof. exact (MK_COMB (@lem6942105) (@lem6942100)). Qed.
Lemma lem6942107 : term244.
Proof. exact (@lem1981473 term125 term101 term101 term101 term80 term101). Qed.
Lemma lem6942109 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942110 : term202 = term208.
Proof. exact (@lem6942109 (NUMERAL 0) term102). Qed.
Lemma lem6942111 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942112 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942113 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942112 h1) (fun h1 : term208 = True => @lem6942111)). Qed.
Lemma lem6942114 : term208 = True.
Proof. exact (EQ_MP (@lem6942113) (@lem6942111)). Qed.
Lemma lem6942115 : term202 = True.
Proof. exact (TRANS (@lem6942110) (@lem6942114)). Qed.
Lemma lem6942116 : True = term202.
Proof. exact (SYM (@lem6942115)). Qed.
Lemma lem6942117 : term202.
Proof. exact (EQ_MP (@lem6942116) (@lem0)). Qed.
Lemma lem6942118 : term245.
Proof. exact (@lem6942107 (@lem6942117)). Qed.
Lemma lem6942120 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942121 : term202 = term208.
Proof. exact (@lem6942120 (NUMERAL 0) term102). Qed.
Lemma lem6942122 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942123 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942124 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942123 h1) (fun h1 : term208 = True => @lem6942122)). Qed.
Lemma lem6942125 : term208 = True.
Proof. exact (EQ_MP (@lem6942124) (@lem6942122)). Qed.
Lemma lem6942126 : term202 = True.
Proof. exact (TRANS (@lem6942121) (@lem6942125)). Qed.
Lemma lem6942127 : True = term202.
Proof. exact (SYM (@lem6942126)). Qed.
Lemma lem6942128 : term202.
Proof. exact (EQ_MP (@lem6942127) (@lem0)). Qed.
Lemma lem6942129 : term246.
Proof. exact (@lem6942118 (@lem6942128)). Qed.
Lemma lem6942131 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942132 : term202 = term208.
Proof. exact (@lem6942131 (NUMERAL 0) term102). Qed.
Lemma lem6942133 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942134 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942135 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942134 h1) (fun h1 : term208 = True => @lem6942133)). Qed.
Lemma lem6942136 : term208 = True.
Proof. exact (EQ_MP (@lem6942135) (@lem6942133)). Qed.
Lemma lem6942137 : term202 = True.
Proof. exact (TRANS (@lem6942132) (@lem6942136)). Qed.
Lemma lem6942138 : True = term202.
Proof. exact (SYM (@lem6942137)). Qed.
Lemma lem6942139 : term202.
Proof. exact (EQ_MP (@lem6942138) (@lem0)). Qed.
Lemma lem6942140 : term247.
Proof. exact (@lem6942129 (@lem6942139)). Qed.
Lemma lem6942142 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6942143 : term134 = term135.
Proof. exact (@lem6942142 term102 term102). Qed.
Lemma lem6942144 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942145 : term137 = term102.
Proof. exact (EQ_MP (@lem6942144) (@lem940073)). Qed.
Lemma lem6942146 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942147 : term135 = term101.
Proof. exact (MK_COMB (@lem6942146) (@lem6942145)). Qed.
Lemma lem6942148 : term134 = term101.
Proof. exact (TRANS (@lem6942143) (@lem6942147)). Qed.
Lemma lem6942150 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6942151 : term164 = term169.
Proof. exact (@lem6942150 term102 term102). Qed.
Lemma lem6942152 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942153 : term137 = term102.
Proof. exact (EQ_MP (@lem6942152) (@lem940073)). Qed.
Lemma lem6942154 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942155 : term135 = term101.
Proof. exact (MK_COMB (@lem6942154) (@lem6942153)). Qed.
Lemma lem6942156 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6942157 : term169 = term125.
Proof. exact (MK_COMB (@lem6942156) (@lem6942155)). Qed.
Lemma lem6942158 : term164 = term125.
Proof. exact (TRANS (@lem6942151) (@lem6942157)). Qed.
Lemma lem6942159 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6942160 : term248 = term240.
Proof. exact (MK_COMB (@lem6942159) (@lem6942158)). Qed.
Lemma lem6942161 : term249 = term242.
Proof. exact (MK_COMB (@lem6942160) (@lem6942148)). Qed.
Lemma lem6942163 (m : nat) : (term250 m) = term80.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6942164 : term242 = term80.
Proof. exact (@lem6942163 term102). Qed.
Lemma lem6942165 : term249 = term80.
Proof. exact (TRANS (@lem6942161) (@lem6942164)). Qed.
Lemma lem6942166 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6942167 : term251 = term252.
Proof. exact (MK_COMB (@lem6942166) (@lem6942165)). Qed.
Lemma lem6942168 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem6942169 : term253 = term213.
Proof. exact (MK_COMB (@lem6942167) (@lem6942168)). Qed.
Lemma lem6942171 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6942172 : term213 = term80.
Proof. exact (@lem6942171 term102). Qed.
Lemma lem6942173 : term253 = term80.
Proof. exact (TRANS (@lem6942169) (@lem6942172)). Qed.
Lemma lem6942175 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6942176 : term134 = term135.
Proof. exact (@lem6942175 term102 term102). Qed.
Lemma lem6942177 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942178 : term137 = term102.
Proof. exact (EQ_MP (@lem6942177) (@lem940073)). Qed.
Lemma lem6942179 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942180 : term135 = term101.
Proof. exact (MK_COMB (@lem6942179) (@lem6942178)). Qed.
Lemma lem6942181 : term134 = term101.
Proof. exact (TRANS (@lem6942176) (@lem6942180)). Qed.
Lemma lem6942182 : term252 = term252.
Proof. exact (eq_refl term252). Qed.
Lemma lem6942183 : term254 = term213.
Proof. exact (MK_COMB (@lem6942182) (@lem6942181)). Qed.
Lemma lem6942185 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6942186 : term213 = term80.
Proof. exact (@lem6942185 term102). Qed.
Lemma lem6942187 : term254 = term80.
Proof. exact (TRANS (@lem6942183) (@lem6942186)). Qed.
Lemma lem6942188 : term80 = term254.
Proof. exact (SYM (@lem6942187)). Qed.
Lemma lem6942189 : term253 = term254.
Proof. exact (TRANS (@lem6942173) (@lem6942188)). Qed.
Lemma lem6942190 : term243 = term122.
Proof. exact (@lem6942140 (@lem6942189)). Qed.
Lemma lem6942191 : term242 = term122.
Proof. exact (TRANS (@lem6942106) (@lem6942190)). Qed.
Lemma lem6942193 (x : real) : (term141 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6942194 : term122 = term80.
Proof. exact (@lem6942193 term80). Qed.
Lemma lem6942195 : term242 = term80.
Proof. exact (TRANS (@lem6942191) (@lem6942194)). Qed.
Lemma lem6942196 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6942197 : term255 = term252.
Proof. exact (MK_COMB (@lem6942196) (@lem6942195)). Qed.
Lemma lem6942198 (_92533 : int) : (real_of_int _92533) = (real_of_int _92533).
Proof. exact (eq_refl (real_of_int _92533)). Qed.
Lemma lem6942199 (_92533 : int) : (term239 _92533) = (term256 _92533).
Proof. exact (MK_COMB (@lem6942197) (@lem6942198 _92533)). Qed.
Lemma lem6942200 (_92533 : int) : (term238 _92533) = (term256 _92533).
Proof. exact (TRANS (@lem6942097 _92533) (@lem6942199 _92533)). Qed.
Lemma lem6942201 (_92533 : int) : (term256 _92533) = term80.
Proof. exact (@lem1982719 (real_of_int _92533)). Qed.
Lemma lem6942202 (_92533 : int) : (term238 _92533) = term80.
Proof. exact (TRANS (@lem6942200 _92533) (@lem6942201 _92533)). Qed.
Lemma lem6942203 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6942204 (_92533 : int) : (term257 _92533) = term258.
Proof. exact (MK_COMB (@lem6942203) (@lem6942202 _92533)). Qed.
Lemma lem6942205 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem6942206 (_92533 : int) : (term277 _92533) = term278.
Proof. exact (MK_COMB (@lem6942204 _92533) (@lem6942205)). Qed.
Lemma lem6942207 (_92533 : int) : (term276 _92533) = term278.
Proof. exact (TRANS (@lem6942096 _92533) (@lem6942206 _92533)). Qed.
Lemma lem6942208 : term278 = term125.
Proof. exact (@lem1982721 term125). Qed.
Lemma lem6942209 (_92533 : int) : (term276 _92533) = term125.
Proof. exact (TRANS (@lem6942207 _92533) (@lem6942208)). Qed.
Lemma lem6942210 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6942211 (_92533 : int) : (term279 _92533) = term280.
Proof. exact (MK_COMB (@lem6942210) (@lem6942209 _92533)). Qed.
Lemma lem6942212 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6942213 (_92533 : int) : (term275 _92533) = term281.
Proof. exact (MK_COMB (@lem6942211 _92533) (@lem6942212)). Qed.
Lemma lem6942214 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : term281.
Proof. exact (EQ_MP (@lem6942213 _92533) (@lem6942095 _92533 _92531 _92532 h1)). Qed.
Lemma lem6942216 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6942217 : term281 = term282.
Proof. exact (@lem6942216 term80 term125). Qed.
Lemma lem6942219 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6942220 : term125 = term126.
Proof. exact (@lem6942219 term102). Qed.
Lemma lem6942222 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942223 : term80 = term122.
Proof. exact (@lem6942222 (NUMERAL 0)). Qed.
Lemma lem6942224 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6942225 : term82 = term283.
Proof. exact (MK_COMB (@lem6942224) (@lem6942223)). Qed.
Lemma lem6942226 : term282 = term284.
Proof. exact (MK_COMB (@lem6942225) (@lem6942220)). Qed.
Lemma lem6942227 : term285.
Proof. exact (@lem1980026 term80 term101 term125 term101). Qed.
Lemma lem6942229 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942230 : term202 = term208.
Proof. exact (@lem6942229 (NUMERAL 0) term102). Qed.
Lemma lem6942231 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942232 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942233 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942232 h1) (fun h1 : term208 = True => @lem6942231)). Qed.
Lemma lem6942234 : term208 = True.
Proof. exact (EQ_MP (@lem6942233) (@lem6942231)). Qed.
Lemma lem6942235 : term202 = True.
Proof. exact (TRANS (@lem6942230) (@lem6942234)). Qed.
Lemma lem6942236 : True = term202.
Proof. exact (SYM (@lem6942235)). Qed.
Lemma lem6942237 : term202.
Proof. exact (EQ_MP (@lem6942236) (@lem0)). Qed.
Lemma lem6942238 : term286.
Proof. exact (@lem6942227 (@lem6942237)). Qed.
Lemma lem6942240 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942241 : term202 = term208.
Proof. exact (@lem6942240 (NUMERAL 0) term102). Qed.
Lemma lem6942242 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942243 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942244 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942243 h1) (fun h1 : term208 = True => @lem6942242)). Qed.
Lemma lem6942245 : term208 = True.
Proof. exact (EQ_MP (@lem6942244) (@lem6942242)). Qed.
Lemma lem6942246 : term202 = True.
Proof. exact (TRANS (@lem6942241) (@lem6942245)). Qed.
Lemma lem6942247 : True = term202.
Proof. exact (SYM (@lem6942246)). Qed.
Lemma lem6942248 : term202.
Proof. exact (EQ_MP (@lem6942247) (@lem0)). Qed.
Lemma lem6942249 : term284 = term287.
Proof. exact (@lem6942238 (@lem6942248)). Qed.
Lemma lem6942251 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6942252 : term164 = term169.
Proof. exact (@lem6942251 term102 term102). Qed.
Lemma lem6942253 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942254 : term137 = term102.
Proof. exact (EQ_MP (@lem6942253) (@lem940073)). Qed.
Lemma lem6942255 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942256 : term135 = term101.
Proof. exact (MK_COMB (@lem6942255) (@lem6942254)). Qed.
Lemma lem6942257 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6942258 : term169 = term125.
Proof. exact (MK_COMB (@lem6942257) (@lem6942256)). Qed.
Lemma lem6942259 : term164 = term125.
Proof. exact (TRANS (@lem6942252) (@lem6942258)). Qed.
Lemma lem6942261 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6942262 : term213 = term80.
Proof. exact (@lem6942261 term102). Qed.
Lemma lem6942263 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6942264 : term288 = term82.
Proof. exact (MK_COMB (@lem6942263) (@lem6942262)). Qed.
Lemma lem6942265 : term287 = term282.
Proof. exact (MK_COMB (@lem6942264) (@lem6942259)). Qed.
Lemma lem6942267 (m : nat) (n : nat) : (term289 m n) = (term290 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6942268 : term282 = term291.
Proof. exact (@lem6942267 (NUMERAL 0) term102). Qed.
Lemma lem6942269 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942270 (h1 : term209 = (BIT1 0)) : (term102 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6942271 : (term209 = (BIT1 0)) = ((term102 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942270 h1) (fun h1 : (term102 = (NUMERAL 0)) = False => @lem6942269)). Qed.
Lemma lem6942272 : (term102 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6942271) (@lem6942269)). Qed.
Lemma lem6942273 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6942274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6942275 : term292 = (and True).
Proof. exact (MK_COMB (@lem6942274) (@lem6942273)). Qed.
Lemma lem6942276 : term291 = (True /\ False).
Proof. exact (MK_COMB (@lem6942275) (@lem6942272)). Qed.
Lemma lem6942278 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6942279 : term291 = False.
Proof. exact (TRANS (@lem6942276) (@lem6942278)). Qed.
Lemma lem6942280 : term282 = False.
Proof. exact (TRANS (@lem6942268) (@lem6942279)). Qed.
Lemma lem6942281 : term287 = False.
Proof. exact (TRANS (@lem6942265) (@lem6942280)). Qed.
Lemma lem6942282 : term284 = False.
Proof. exact (TRANS (@lem6942249) (@lem6942281)). Qed.
Lemma lem6942283 : term282 = False.
Proof. exact (TRANS (@lem6942226) (@lem6942282)). Qed.
Lemma lem6942284 : term281 = False.
Proof. exact (TRANS (@lem6942217) (@lem6942283)). Qed.
Lemma lem6942285 (_92533 : int) (_92531 : int) (_92532 : int) (h1 : term200 _92533 _92531 _92532) : False.
Proof. exact (EQ_MP (@lem6942284) (@lem6942214 _92533 _92531 _92532 h1)). Qed.
Lemma lem6942286 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term293 _92532 _92531 _92533.
Proof. exact (h1). Qed.
Lemma lem6942287 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term199 _92532 _92531 _92533.
Proof. exact (proj2 (@lem6942286 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942289 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term195 _92532 _92531 _92533.
Proof. exact (proj2 (@lem6942287 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942291 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term191 _92532 _92531 _92533.
Proof. exact (proj2 (@lem6942289 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942293 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term179 _92531 _92533.
Proof. exact (proj2 (@lem6942291 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942294 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term157 _92531 _92532 _92533.
Proof. exact (proj1 (@lem6942291 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942295 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term156 _92531 _92532 _92533.
Proof. exact (proj2 (@lem6942294 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942296 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term145 _92532.
Proof. exact (proj1 (@lem6942294 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942297 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term154 _92531 _92532 _92533.
Proof. exact (proj2 (@lem6942295 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942300 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6942301 : term201 = term202.
Proof. exact (@lem6942300 term80 term101). Qed.
Lemma lem6942303 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942304 : term101 = term163.
Proof. exact (@lem6942303 term102). Qed.
Lemma lem6942306 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942307 : term80 = term122.
Proof. exact (@lem6942306 (NUMERAL 0)). Qed.
Lemma lem6942308 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6942309 : term203 = term204.
Proof. exact (MK_COMB (@lem6942308) (@lem6942307)). Qed.
Lemma lem6942310 : term202 = term205.
Proof. exact (MK_COMB (@lem6942309) (@lem6942304)). Qed.
Lemma lem6942311 : term206.
Proof. exact (@lem1980255 term80 term101 term101 term101). Qed.
Lemma lem6942313 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942314 : term202 = term208.
Proof. exact (@lem6942313 (NUMERAL 0) term102). Qed.
Lemma lem6942315 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942316 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942317 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942316 h1) (fun h1 : term208 = True => @lem6942315)). Qed.
Lemma lem6942318 : term208 = True.
Proof. exact (EQ_MP (@lem6942317) (@lem6942315)). Qed.
Lemma lem6942319 : term202 = True.
Proof. exact (TRANS (@lem6942314) (@lem6942318)). Qed.
Lemma lem6942320 : True = term202.
Proof. exact (SYM (@lem6942319)). Qed.
Lemma lem6942321 : term202.
Proof. exact (EQ_MP (@lem6942320) (@lem0)). Qed.
Lemma lem6942322 : term210.
Proof. exact (@lem6942311 (@lem6942321)). Qed.
Lemma lem6942324 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942325 : term202 = term208.
Proof. exact (@lem6942324 (NUMERAL 0) term102). Qed.
Lemma lem6942326 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942327 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942328 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942327 h1) (fun h1 : term208 = True => @lem6942326)). Qed.
Lemma lem6942329 : term208 = True.
Proof. exact (EQ_MP (@lem6942328) (@lem6942326)). Qed.
Lemma lem6942330 : term202 = True.
Proof. exact (TRANS (@lem6942325) (@lem6942329)). Qed.
Lemma lem6942331 : True = term202.
Proof. exact (SYM (@lem6942330)). Qed.
Lemma lem6942332 : term202.
Proof. exact (EQ_MP (@lem6942331) (@lem0)). Qed.
Lemma lem6942333 : term205 = term211.
Proof. exact (@lem6942322 (@lem6942332)). Qed.
Lemma lem6942335 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6942336 : term134 = term135.
Proof. exact (@lem6942335 term102 term102). Qed.
Lemma lem6942337 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942338 : term137 = term102.
Proof. exact (EQ_MP (@lem6942337) (@lem940073)). Qed.
Lemma lem6942339 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942340 : term135 = term101.
Proof. exact (MK_COMB (@lem6942339) (@lem6942338)). Qed.
Lemma lem6942341 : term134 = term101.
Proof. exact (TRANS (@lem6942336) (@lem6942340)). Qed.
Lemma lem6942343 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6942344 : term213 = term80.
Proof. exact (@lem6942343 term102). Qed.
Lemma lem6942345 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6942346 : term214 = term203.
Proof. exact (MK_COMB (@lem6942345) (@lem6942344)). Qed.
Lemma lem6942347 : term211 = term202.
Proof. exact (MK_COMB (@lem6942346) (@lem6942341)). Qed.
Lemma lem6942349 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942350 : term202 = term208.
Proof. exact (@lem6942349 (NUMERAL 0) term102). Qed.
Lemma lem6942351 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942352 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942353 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942352 h1) (fun h1 : term208 = True => @lem6942351)). Qed.
Lemma lem6942354 : term208 = True.
Proof. exact (EQ_MP (@lem6942353) (@lem6942351)). Qed.
Lemma lem6942355 : term202 = True.
Proof. exact (TRANS (@lem6942350) (@lem6942354)). Qed.
Lemma lem6942356 : term211 = True.
Proof. exact (TRANS (@lem6942347) (@lem6942355)). Qed.
Lemma lem6942357 : term205 = True.
Proof. exact (TRANS (@lem6942333) (@lem6942356)). Qed.
Lemma lem6942358 : term202 = True.
Proof. exact (TRANS (@lem6942310) (@lem6942357)). Qed.
Lemma lem6942359 : term201 = True.
Proof. exact (TRANS (@lem6942301) (@lem6942358)). Qed.
Lemma lem6942360 : True = term201.
Proof. exact (SYM (@lem6942359)). Qed.
Lemma lem6942361 : term201.
Proof. exact (EQ_MP (@lem6942360) (@lem0)). Qed.
Lemma lem6942362 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term215 _92532.
Proof. exact (conj (@lem6942361) (@lem6942296 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942364 (x : real) (y : real) : term216 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6942365 (_92532 : int) : term217 _92532.
Proof. exact (@lem6942364 term101 (real_of_int _92532)). Qed.
Lemma lem6942366 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term218 _92532.
Proof. exact (@lem6942365 _92532 (@lem6942362 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942367 (_92532 : int) : (term219 _92532) = (real_of_int _92532).
Proof. exact (@lem1982733 (real_of_int _92532)). Qed.
Lemma lem6942368 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6942369 (_92532 : int) : (term220 _92532) = (term144 _92532).
Proof. exact (MK_COMB (@lem6942368) (@lem6942367 _92532)). Qed.
Lemma lem6942370 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6942371 (_92532 : int) : (term218 _92532) = (term145 _92532).
Proof. exact (MK_COMB (@lem6942369 _92532) (@lem6942370)). Qed.
Lemma lem6942372 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term145 _92532.
Proof. exact (EQ_MP (@lem6942371 _92532) (@lem6942366 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942374 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6942375 : term201 = term202.
Proof. exact (@lem6942374 term80 term101). Qed.
Lemma lem6942377 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942378 : term101 = term163.
Proof. exact (@lem6942377 term102). Qed.
Lemma lem6942380 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942381 : term80 = term122.
Proof. exact (@lem6942380 (NUMERAL 0)). Qed.
Lemma lem6942382 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6942383 : term203 = term204.
Proof. exact (MK_COMB (@lem6942382) (@lem6942381)). Qed.
Lemma lem6942384 : term202 = term205.
Proof. exact (MK_COMB (@lem6942383) (@lem6942378)). Qed.
Lemma lem6942385 : term206.
Proof. exact (@lem1980255 term80 term101 term101 term101). Qed.
Lemma lem6942387 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942388 : term202 = term208.
Proof. exact (@lem6942387 (NUMERAL 0) term102). Qed.
Lemma lem6942389 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942390 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942391 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942390 h1) (fun h1 : term208 = True => @lem6942389)). Qed.
Lemma lem6942392 : term208 = True.
Proof. exact (EQ_MP (@lem6942391) (@lem6942389)). Qed.
Lemma lem6942393 : term202 = True.
Proof. exact (TRANS (@lem6942388) (@lem6942392)). Qed.
Lemma lem6942394 : True = term202.
Proof. exact (SYM (@lem6942393)). Qed.
Lemma lem6942395 : term202.
Proof. exact (EQ_MP (@lem6942394) (@lem0)). Qed.
Lemma lem6942396 : term210.
Proof. exact (@lem6942385 (@lem6942395)). Qed.
Lemma lem6942398 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942399 : term202 = term208.
Proof. exact (@lem6942398 (NUMERAL 0) term102). Qed.
Lemma lem6942400 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942401 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942402 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942401 h1) (fun h1 : term208 = True => @lem6942400)). Qed.
Lemma lem6942403 : term208 = True.
Proof. exact (EQ_MP (@lem6942402) (@lem6942400)). Qed.
Lemma lem6942404 : term202 = True.
Proof. exact (TRANS (@lem6942399) (@lem6942403)). Qed.
Lemma lem6942405 : True = term202.
Proof. exact (SYM (@lem6942404)). Qed.
Lemma lem6942406 : term202.
Proof. exact (EQ_MP (@lem6942405) (@lem0)). Qed.
Lemma lem6942407 : term205 = term211.
Proof. exact (@lem6942396 (@lem6942406)). Qed.
Lemma lem6942409 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6942410 : term134 = term135.
Proof. exact (@lem6942409 term102 term102). Qed.
Lemma lem6942411 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942412 : term137 = term102.
Proof. exact (EQ_MP (@lem6942411) (@lem940073)). Qed.
Lemma lem6942413 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942414 : term135 = term101.
Proof. exact (MK_COMB (@lem6942413) (@lem6942412)). Qed.
Lemma lem6942415 : term134 = term101.
Proof. exact (TRANS (@lem6942410) (@lem6942414)). Qed.
Lemma lem6942417 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6942418 : term213 = term80.
Proof. exact (@lem6942417 term102). Qed.
Lemma lem6942419 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6942420 : term214 = term203.
Proof. exact (MK_COMB (@lem6942419) (@lem6942418)). Qed.
Lemma lem6942421 : term211 = term202.
Proof. exact (MK_COMB (@lem6942420) (@lem6942415)). Qed.
Lemma lem6942423 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942424 : term202 = term208.
Proof. exact (@lem6942423 (NUMERAL 0) term102). Qed.
Lemma lem6942425 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942426 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942427 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942426 h1) (fun h1 : term208 = True => @lem6942425)). Qed.
Lemma lem6942428 : term208 = True.
Proof. exact (EQ_MP (@lem6942427) (@lem6942425)). Qed.
Lemma lem6942429 : term202 = True.
Proof. exact (TRANS (@lem6942424) (@lem6942428)). Qed.
Lemma lem6942430 : term211 = True.
Proof. exact (TRANS (@lem6942421) (@lem6942429)). Qed.
Lemma lem6942431 : term205 = True.
Proof. exact (TRANS (@lem6942407) (@lem6942430)). Qed.
Lemma lem6942432 : term202 = True.
Proof. exact (TRANS (@lem6942384) (@lem6942431)). Qed.
Lemma lem6942433 : term201 = True.
Proof. exact (TRANS (@lem6942375) (@lem6942432)). Qed.
Lemma lem6942434 : True = term201.
Proof. exact (SYM (@lem6942433)). Qed.
Lemma lem6942435 : term201.
Proof. exact (EQ_MP (@lem6942434) (@lem0)). Qed.
Lemma lem6942436 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term221 _92531 _92532 _92533.
Proof. exact (conj (@lem6942435) (@lem6942297 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942438 (x : real) (y : real) : term216 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6942439 (_92531 : int) (_92532 : int) (_92533 : int) : term222 _92531 _92532 _92533.
Proof. exact (@lem6942438 term101 (term151 _92531 _92532 _92533)). Qed.
Lemma lem6942440 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term223 _92531 _92532 _92533.
Proof. exact (@lem6942439 _92531 _92532 _92533 (@lem6942436 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942441 (_92531 : int) (_92532 : int) (_92533 : int) : (term224 _92531 _92532 _92533) = (term151 _92531 _92532 _92533).
Proof. exact (@lem1982733 (term151 _92531 _92532 _92533)). Qed.
Lemma lem6942442 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6942443 (_92531 : int) (_92532 : int) (_92533 : int) : (term225 _92531 _92532 _92533) = (term153 _92531 _92532 _92533).
Proof. exact (MK_COMB (@lem6942442) (@lem6942441 _92531 _92532 _92533)). Qed.
Lemma lem6942444 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6942445 (_92531 : int) (_92532 : int) (_92533 : int) : (term223 _92531 _92532 _92533) = (term154 _92531 _92532 _92533).
Proof. exact (MK_COMB (@lem6942443 _92531 _92532 _92533) (@lem6942444)). Qed.
Lemma lem6942446 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term154 _92531 _92532 _92533.
Proof. exact (EQ_MP (@lem6942445 _92531 _92532 _92533) (@lem6942440 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942448 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6942449 : term201 = term202.
Proof. exact (@lem6942448 term80 term101). Qed.
Lemma lem6942451 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942452 : term101 = term163.
Proof. exact (@lem6942451 term102). Qed.
Lemma lem6942454 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942455 : term80 = term122.
Proof. exact (@lem6942454 (NUMERAL 0)). Qed.
Lemma lem6942456 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6942457 : term203 = term204.
Proof. exact (MK_COMB (@lem6942456) (@lem6942455)). Qed.
Lemma lem6942458 : term202 = term205.
Proof. exact (MK_COMB (@lem6942457) (@lem6942452)). Qed.
Lemma lem6942459 : term206.
Proof. exact (@lem1980255 term80 term101 term101 term101). Qed.
Lemma lem6942461 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942462 : term202 = term208.
Proof. exact (@lem6942461 (NUMERAL 0) term102). Qed.
Lemma lem6942463 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942464 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942465 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942464 h1) (fun h1 : term208 = True => @lem6942463)). Qed.
Lemma lem6942466 : term208 = True.
Proof. exact (EQ_MP (@lem6942465) (@lem6942463)). Qed.
Lemma lem6942467 : term202 = True.
Proof. exact (TRANS (@lem6942462) (@lem6942466)). Qed.
Lemma lem6942468 : True = term202.
Proof. exact (SYM (@lem6942467)). Qed.
Lemma lem6942469 : term202.
Proof. exact (EQ_MP (@lem6942468) (@lem0)). Qed.
Lemma lem6942470 : term210.
Proof. exact (@lem6942459 (@lem6942469)). Qed.
Lemma lem6942472 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942473 : term202 = term208.
Proof. exact (@lem6942472 (NUMERAL 0) term102). Qed.
Lemma lem6942474 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942475 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942476 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942475 h1) (fun h1 : term208 = True => @lem6942474)). Qed.
Lemma lem6942477 : term208 = True.
Proof. exact (EQ_MP (@lem6942476) (@lem6942474)). Qed.
Lemma lem6942478 : term202 = True.
Proof. exact (TRANS (@lem6942473) (@lem6942477)). Qed.
Lemma lem6942479 : True = term202.
Proof. exact (SYM (@lem6942478)). Qed.
Lemma lem6942480 : term202.
Proof. exact (EQ_MP (@lem6942479) (@lem0)). Qed.
Lemma lem6942481 : term205 = term211.
Proof. exact (@lem6942470 (@lem6942480)). Qed.
Lemma lem6942483 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6942484 : term134 = term135.
Proof. exact (@lem6942483 term102 term102). Qed.
Lemma lem6942485 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942486 : term137 = term102.
Proof. exact (EQ_MP (@lem6942485) (@lem940073)). Qed.
Lemma lem6942487 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942488 : term135 = term101.
Proof. exact (MK_COMB (@lem6942487) (@lem6942486)). Qed.
Lemma lem6942489 : term134 = term101.
Proof. exact (TRANS (@lem6942484) (@lem6942488)). Qed.
Lemma lem6942491 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6942492 : term213 = term80.
Proof. exact (@lem6942491 term102). Qed.
Lemma lem6942493 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6942494 : term214 = term203.
Proof. exact (MK_COMB (@lem6942493) (@lem6942492)). Qed.
Lemma lem6942495 : term211 = term202.
Proof. exact (MK_COMB (@lem6942494) (@lem6942489)). Qed.
Lemma lem6942497 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942498 : term202 = term208.
Proof. exact (@lem6942497 (NUMERAL 0) term102). Qed.
Lemma lem6942499 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942500 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942501 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942500 h1) (fun h1 : term208 = True => @lem6942499)). Qed.
Lemma lem6942502 : term208 = True.
Proof. exact (EQ_MP (@lem6942501) (@lem6942499)). Qed.
Lemma lem6942503 : term202 = True.
Proof. exact (TRANS (@lem6942498) (@lem6942502)). Qed.
Lemma lem6942504 : term211 = True.
Proof. exact (TRANS (@lem6942495) (@lem6942503)). Qed.
Lemma lem6942505 : term205 = True.
Proof. exact (TRANS (@lem6942481) (@lem6942504)). Qed.
Lemma lem6942506 : term202 = True.
Proof. exact (TRANS (@lem6942458) (@lem6942505)). Qed.
Lemma lem6942507 : term201 = True.
Proof. exact (TRANS (@lem6942449) (@lem6942506)). Qed.
Lemma lem6942508 : True = term201.
Proof. exact (SYM (@lem6942507)). Qed.
Lemma lem6942509 : term201.
Proof. exact (EQ_MP (@lem6942508) (@lem0)). Qed.
Lemma lem6942510 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term226 _92531 _92533.
Proof. exact (conj (@lem6942509) (@lem6942293 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942512 (x : real) (y : real) : term216 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6942513 (_92531 : int) (_92533 : int) : term227 _92531 _92533.
Proof. exact (@lem6942512 term101 (term175 _92531 _92533)). Qed.
Lemma lem6942514 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term228 _92531 _92533.
Proof. exact (@lem6942513 _92531 _92533 (@lem6942510 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942515 (_92531 : int) (_92533 : int) : (term229 _92531 _92533) = (term175 _92531 _92533).
Proof. exact (@lem1982733 (term175 _92531 _92533)). Qed.
Lemma lem6942516 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6942517 (_92531 : int) (_92533 : int) : (term230 _92531 _92533) = (term178 _92531 _92533).
Proof. exact (MK_COMB (@lem6942516) (@lem6942515 _92531 _92533)). Qed.
Lemma lem6942518 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6942519 (_92531 : int) (_92533 : int) : (term228 _92531 _92533) = (term179 _92531 _92533).
Proof. exact (MK_COMB (@lem6942517 _92531 _92533) (@lem6942518)). Qed.
Lemma lem6942520 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term179 _92531 _92533.
Proof. exact (EQ_MP (@lem6942519 _92531 _92533) (@lem6942514 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942521 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term294 _92531 _92532 _92533.
Proof. exact (conj (@lem6942520 _92532 _92531 _92533 h1) (@lem6942446 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942523 (x : real) (y : real) : term232 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6942524 (_92531 : int) (_92532 : int) (_92533 : int) : term295 _92531 _92532 _92533.
Proof. exact (@lem6942523 (term175 _92531 _92533) (term151 _92531 _92532 _92533)). Qed.
Lemma lem6942525 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term296 _92531 _92532 _92533.
Proof. exact (@lem6942524 _92531 _92532 _92533 (@lem6942521 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942526 (_92531 : int) (_92532 : int) (_92533 : int) : (term297 _92531 _92532 _92533) = (term298 _92531 _92532 _92533).
Proof. exact (@lem1982753 (term176 _92531) (real_of_int _92531) (term237 _92533) (term150 _92532 _92533)). Qed.
Lemma lem6942527 (_92531 : int) : (term238 _92531) = (term239 _92531).
Proof. exact (@lem1982713 term125 (real_of_int _92531)). Qed.
Lemma lem6942529 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942530 : term101 = term163.
Proof. exact (@lem6942529 term102). Qed.
Lemma lem6942532 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6942533 : term125 = term126.
Proof. exact (@lem6942532 term102). Qed.
Lemma lem6942534 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6942535 : term240 = term241.
Proof. exact (MK_COMB (@lem6942534) (@lem6942533)). Qed.
Lemma lem6942536 : term242 = term243.
Proof. exact (MK_COMB (@lem6942535) (@lem6942530)). Qed.
Lemma lem6942537 : term244.
Proof. exact (@lem1981473 term125 term101 term101 term101 term80 term101). Qed.
Lemma lem6942539 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942540 : term202 = term208.
Proof. exact (@lem6942539 (NUMERAL 0) term102). Qed.
Lemma lem6942541 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942542 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942543 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942542 h1) (fun h1 : term208 = True => @lem6942541)). Qed.
Lemma lem6942544 : term208 = True.
Proof. exact (EQ_MP (@lem6942543) (@lem6942541)). Qed.
Lemma lem6942545 : term202 = True.
Proof. exact (TRANS (@lem6942540) (@lem6942544)). Qed.
Lemma lem6942546 : True = term202.
Proof. exact (SYM (@lem6942545)). Qed.
Lemma lem6942547 : term202.
Proof. exact (EQ_MP (@lem6942546) (@lem0)). Qed.
Lemma lem6942548 : term245.
Proof. exact (@lem6942537 (@lem6942547)). Qed.
Lemma lem6942550 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942551 : term202 = term208.
Proof. exact (@lem6942550 (NUMERAL 0) term102). Qed.
Lemma lem6942552 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942553 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942554 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942553 h1) (fun h1 : term208 = True => @lem6942552)). Qed.
Lemma lem6942555 : term208 = True.
Proof. exact (EQ_MP (@lem6942554) (@lem6942552)). Qed.
Lemma lem6942556 : term202 = True.
Proof. exact (TRANS (@lem6942551) (@lem6942555)). Qed.
Lemma lem6942557 : True = term202.
Proof. exact (SYM (@lem6942556)). Qed.
Lemma lem6942558 : term202.
Proof. exact (EQ_MP (@lem6942557) (@lem0)). Qed.
Lemma lem6942559 : term246.
Proof. exact (@lem6942548 (@lem6942558)). Qed.
Lemma lem6942561 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942562 : term202 = term208.
Proof. exact (@lem6942561 (NUMERAL 0) term102). Qed.
Lemma lem6942563 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942564 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942565 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942564 h1) (fun h1 : term208 = True => @lem6942563)). Qed.
Lemma lem6942566 : term208 = True.
Proof. exact (EQ_MP (@lem6942565) (@lem6942563)). Qed.
Lemma lem6942567 : term202 = True.
Proof. exact (TRANS (@lem6942562) (@lem6942566)). Qed.
Lemma lem6942568 : True = term202.
Proof. exact (SYM (@lem6942567)). Qed.
Lemma lem6942569 : term202.
Proof. exact (EQ_MP (@lem6942568) (@lem0)). Qed.
Lemma lem6942570 : term247.
Proof. exact (@lem6942559 (@lem6942569)). Qed.
Lemma lem6942572 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6942573 : term134 = term135.
Proof. exact (@lem6942572 term102 term102). Qed.
Lemma lem6942574 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942575 : term137 = term102.
Proof. exact (EQ_MP (@lem6942574) (@lem940073)). Qed.
Lemma lem6942576 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942577 : term135 = term101.
Proof. exact (MK_COMB (@lem6942576) (@lem6942575)). Qed.
Lemma lem6942578 : term134 = term101.
Proof. exact (TRANS (@lem6942573) (@lem6942577)). Qed.
Lemma lem6942580 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6942581 : term164 = term169.
Proof. exact (@lem6942580 term102 term102). Qed.
Lemma lem6942582 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942583 : term137 = term102.
Proof. exact (EQ_MP (@lem6942582) (@lem940073)). Qed.
Lemma lem6942584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942585 : term135 = term101.
Proof. exact (MK_COMB (@lem6942584) (@lem6942583)). Qed.
Lemma lem6942586 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6942587 : term169 = term125.
Proof. exact (MK_COMB (@lem6942586) (@lem6942585)). Qed.
Lemma lem6942588 : term164 = term125.
Proof. exact (TRANS (@lem6942581) (@lem6942587)). Qed.
Lemma lem6942589 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6942590 : term248 = term240.
Proof. exact (MK_COMB (@lem6942589) (@lem6942588)). Qed.
Lemma lem6942591 : term249 = term242.
Proof. exact (MK_COMB (@lem6942590) (@lem6942578)). Qed.
Lemma lem6942593 (m : nat) : (term250 m) = term80.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6942594 : term242 = term80.
Proof. exact (@lem6942593 term102). Qed.
Lemma lem6942595 : term249 = term80.
Proof. exact (TRANS (@lem6942591) (@lem6942594)). Qed.
Lemma lem6942596 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6942597 : term251 = term252.
Proof. exact (MK_COMB (@lem6942596) (@lem6942595)). Qed.
Lemma lem6942598 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem6942599 : term253 = term213.
Proof. exact (MK_COMB (@lem6942597) (@lem6942598)). Qed.
Lemma lem6942601 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6942602 : term213 = term80.
Proof. exact (@lem6942601 term102). Qed.
Lemma lem6942603 : term253 = term80.
Proof. exact (TRANS (@lem6942599) (@lem6942602)). Qed.
Lemma lem6942605 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6942606 : term134 = term135.
Proof. exact (@lem6942605 term102 term102). Qed.
Lemma lem6942607 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942608 : term137 = term102.
Proof. exact (EQ_MP (@lem6942607) (@lem940073)). Qed.
Lemma lem6942609 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942610 : term135 = term101.
Proof. exact (MK_COMB (@lem6942609) (@lem6942608)). Qed.
Lemma lem6942611 : term134 = term101.
Proof. exact (TRANS (@lem6942606) (@lem6942610)). Qed.
Lemma lem6942612 : term252 = term252.
Proof. exact (eq_refl term252). Qed.
Lemma lem6942613 : term254 = term213.
Proof. exact (MK_COMB (@lem6942612) (@lem6942611)). Qed.
Lemma lem6942615 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6942616 : term213 = term80.
Proof. exact (@lem6942615 term102). Qed.
Lemma lem6942617 : term254 = term80.
Proof. exact (TRANS (@lem6942613) (@lem6942616)). Qed.
Lemma lem6942618 : term80 = term254.
Proof. exact (SYM (@lem6942617)). Qed.
Lemma lem6942619 : term253 = term254.
Proof. exact (TRANS (@lem6942603) (@lem6942618)). Qed.
Lemma lem6942620 : term243 = term122.
Proof. exact (@lem6942570 (@lem6942619)). Qed.
Lemma lem6942621 : term242 = term122.
Proof. exact (TRANS (@lem6942536) (@lem6942620)). Qed.
Lemma lem6942623 (x : real) : (term141 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6942624 : term122 = term80.
Proof. exact (@lem6942623 term80). Qed.
Lemma lem6942625 : term242 = term80.
Proof. exact (TRANS (@lem6942621) (@lem6942624)). Qed.
Lemma lem6942626 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6942627 : term255 = term252.
Proof. exact (MK_COMB (@lem6942626) (@lem6942625)). Qed.
Lemma lem6942628 (_92531 : int) : (real_of_int _92531) = (real_of_int _92531).
Proof. exact (eq_refl (real_of_int _92531)). Qed.
Lemma lem6942629 (_92531 : int) : (term239 _92531) = (term256 _92531).
Proof. exact (MK_COMB (@lem6942627) (@lem6942628 _92531)). Qed.
Lemma lem6942630 (_92531 : int) : (term238 _92531) = (term256 _92531).
Proof. exact (TRANS (@lem6942527 _92531) (@lem6942629 _92531)). Qed.
Lemma lem6942631 (_92531 : int) : (term256 _92531) = term80.
Proof. exact (@lem1982719 (real_of_int _92531)). Qed.
Lemma lem6942632 (_92531 : int) : (term238 _92531) = term80.
Proof. exact (TRANS (@lem6942630 _92531) (@lem6942631 _92531)). Qed.
Lemma lem6942633 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6942634 (_92531 : int) : (term257 _92531) = term258.
Proof. exact (MK_COMB (@lem6942633) (@lem6942632 _92531)). Qed.
Lemma lem6942635 (_92532 : int) (_92533 : int) : (term299 _92532 _92533) = (term300 _92532 _92533).
Proof. exact (@lem1982757 (term176 _92532) (term237 _92533) (term176 _92533)). Qed.
Lemma lem6942636 (_92533 : int) : (term301 _92533) = (term302 _92533).
Proof. exact (@lem1982759 (real_of_int _92533) (term176 _92533) term125). Qed.
Lemma lem6942637 (_92533 : int) : (term261 _92533) = (term239 _92533).
Proof. exact (@lem1982715 term125 (real_of_int _92533)). Qed.
Lemma lem6942639 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942640 : term101 = term163.
Proof. exact (@lem6942639 term102). Qed.
Lemma lem6942642 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6942643 : term125 = term126.
Proof. exact (@lem6942642 term102). Qed.
Lemma lem6942644 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6942645 : term240 = term241.
Proof. exact (MK_COMB (@lem6942644) (@lem6942643)). Qed.
Lemma lem6942646 : term242 = term243.
Proof. exact (MK_COMB (@lem6942645) (@lem6942640)). Qed.
Lemma lem6942647 : term244.
Proof. exact (@lem1981473 term125 term101 term101 term101 term80 term101). Qed.
Lemma lem6942649 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942650 : term202 = term208.
Proof. exact (@lem6942649 (NUMERAL 0) term102). Qed.
Lemma lem6942651 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942652 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942653 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942652 h1) (fun h1 : term208 = True => @lem6942651)). Qed.
Lemma lem6942654 : term208 = True.
Proof. exact (EQ_MP (@lem6942653) (@lem6942651)). Qed.
Lemma lem6942655 : term202 = True.
Proof. exact (TRANS (@lem6942650) (@lem6942654)). Qed.
Lemma lem6942656 : True = term202.
Proof. exact (SYM (@lem6942655)). Qed.
Lemma lem6942657 : term202.
Proof. exact (EQ_MP (@lem6942656) (@lem0)). Qed.
Lemma lem6942658 : term245.
Proof. exact (@lem6942647 (@lem6942657)). Qed.
Lemma lem6942660 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942661 : term202 = term208.
Proof. exact (@lem6942660 (NUMERAL 0) term102). Qed.
Lemma lem6942662 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942663 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942664 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942663 h1) (fun h1 : term208 = True => @lem6942662)). Qed.
Lemma lem6942665 : term208 = True.
Proof. exact (EQ_MP (@lem6942664) (@lem6942662)). Qed.
Lemma lem6942666 : term202 = True.
Proof. exact (TRANS (@lem6942661) (@lem6942665)). Qed.
Lemma lem6942667 : True = term202.
Proof. exact (SYM (@lem6942666)). Qed.
Lemma lem6942668 : term202.
Proof. exact (EQ_MP (@lem6942667) (@lem0)). Qed.
Lemma lem6942669 : term246.
Proof. exact (@lem6942658 (@lem6942668)). Qed.
Lemma lem6942671 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942672 : term202 = term208.
Proof. exact (@lem6942671 (NUMERAL 0) term102). Qed.
Lemma lem6942673 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942674 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942675 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942674 h1) (fun h1 : term208 = True => @lem6942673)). Qed.
Lemma lem6942676 : term208 = True.
Proof. exact (EQ_MP (@lem6942675) (@lem6942673)). Qed.
Lemma lem6942677 : term202 = True.
Proof. exact (TRANS (@lem6942672) (@lem6942676)). Qed.
Lemma lem6942678 : True = term202.
Proof. exact (SYM (@lem6942677)). Qed.
Lemma lem6942679 : term202.
Proof. exact (EQ_MP (@lem6942678) (@lem0)). Qed.
Lemma lem6942680 : term247.
Proof. exact (@lem6942669 (@lem6942679)). Qed.
Lemma lem6942682 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6942683 : term134 = term135.
Proof. exact (@lem6942682 term102 term102). Qed.
Lemma lem6942684 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942685 : term137 = term102.
Proof. exact (EQ_MP (@lem6942684) (@lem940073)). Qed.
Lemma lem6942686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942687 : term135 = term101.
Proof. exact (MK_COMB (@lem6942686) (@lem6942685)). Qed.
Lemma lem6942688 : term134 = term101.
Proof. exact (TRANS (@lem6942683) (@lem6942687)). Qed.
Lemma lem6942690 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6942691 : term164 = term169.
Proof. exact (@lem6942690 term102 term102). Qed.
Lemma lem6942692 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942693 : term137 = term102.
Proof. exact (EQ_MP (@lem6942692) (@lem940073)). Qed.
Lemma lem6942694 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942695 : term135 = term101.
Proof. exact (MK_COMB (@lem6942694) (@lem6942693)). Qed.
Lemma lem6942696 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6942697 : term169 = term125.
Proof. exact (MK_COMB (@lem6942696) (@lem6942695)). Qed.
Lemma lem6942698 : term164 = term125.
Proof. exact (TRANS (@lem6942691) (@lem6942697)). Qed.
Lemma lem6942699 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6942700 : term248 = term240.
Proof. exact (MK_COMB (@lem6942699) (@lem6942698)). Qed.
Lemma lem6942701 : term249 = term242.
Proof. exact (MK_COMB (@lem6942700) (@lem6942688)). Qed.
Lemma lem6942703 (m : nat) : (term250 m) = term80.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6942704 : term242 = term80.
Proof. exact (@lem6942703 term102). Qed.
Lemma lem6942705 : term249 = term80.
Proof. exact (TRANS (@lem6942701) (@lem6942704)). Qed.
Lemma lem6942706 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6942707 : term251 = term252.
Proof. exact (MK_COMB (@lem6942706) (@lem6942705)). Qed.
Lemma lem6942708 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem6942709 : term253 = term213.
Proof. exact (MK_COMB (@lem6942707) (@lem6942708)). Qed.
Lemma lem6942711 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6942712 : term213 = term80.
Proof. exact (@lem6942711 term102). Qed.
Lemma lem6942713 : term253 = term80.
Proof. exact (TRANS (@lem6942709) (@lem6942712)). Qed.
Lemma lem6942715 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6942716 : term134 = term135.
Proof. exact (@lem6942715 term102 term102). Qed.
Lemma lem6942717 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942718 : term137 = term102.
Proof. exact (EQ_MP (@lem6942717) (@lem940073)). Qed.
Lemma lem6942719 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942720 : term135 = term101.
Proof. exact (MK_COMB (@lem6942719) (@lem6942718)). Qed.
Lemma lem6942721 : term134 = term101.
Proof. exact (TRANS (@lem6942716) (@lem6942720)). Qed.
Lemma lem6942722 : term252 = term252.
Proof. exact (eq_refl term252). Qed.
Lemma lem6942723 : term254 = term213.
Proof. exact (MK_COMB (@lem6942722) (@lem6942721)). Qed.
Lemma lem6942725 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6942726 : term213 = term80.
Proof. exact (@lem6942725 term102). Qed.
Lemma lem6942727 : term254 = term80.
Proof. exact (TRANS (@lem6942723) (@lem6942726)). Qed.
Lemma lem6942728 : term80 = term254.
Proof. exact (SYM (@lem6942727)). Qed.
Lemma lem6942729 : term253 = term254.
Proof. exact (TRANS (@lem6942713) (@lem6942728)). Qed.
Lemma lem6942730 : term243 = term122.
Proof. exact (@lem6942680 (@lem6942729)). Qed.
Lemma lem6942731 : term242 = term122.
Proof. exact (TRANS (@lem6942646) (@lem6942730)). Qed.
Lemma lem6942733 (x : real) : (term141 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6942734 : term122 = term80.
Proof. exact (@lem6942733 term80). Qed.
Lemma lem6942735 : term242 = term80.
Proof. exact (TRANS (@lem6942731) (@lem6942734)). Qed.
Lemma lem6942736 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6942737 : term255 = term252.
Proof. exact (MK_COMB (@lem6942736) (@lem6942735)). Qed.
Lemma lem6942738 (_92533 : int) : (real_of_int _92533) = (real_of_int _92533).
Proof. exact (eq_refl (real_of_int _92533)). Qed.
Lemma lem6942739 (_92533 : int) : (term239 _92533) = (term256 _92533).
Proof. exact (MK_COMB (@lem6942737) (@lem6942738 _92533)). Qed.
Lemma lem6942740 (_92533 : int) : (term261 _92533) = (term256 _92533).
Proof. exact (TRANS (@lem6942637 _92533) (@lem6942739 _92533)). Qed.
Lemma lem6942741 (_92533 : int) : (term256 _92533) = term80.
Proof. exact (@lem1982719 (real_of_int _92533)). Qed.
Lemma lem6942742 (_92533 : int) : (term261 _92533) = term80.
Proof. exact (TRANS (@lem6942740 _92533) (@lem6942741 _92533)). Qed.
Lemma lem6942743 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6942744 (_92533 : int) : (term262 _92533) = term258.
Proof. exact (MK_COMB (@lem6942743) (@lem6942742 _92533)). Qed.
Lemma lem6942745 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem6942746 (_92533 : int) : (term302 _92533) = term278.
Proof. exact (MK_COMB (@lem6942744 _92533) (@lem6942745)). Qed.
Lemma lem6942747 (_92533 : int) : (term301 _92533) = term278.
Proof. exact (TRANS (@lem6942636 _92533) (@lem6942746 _92533)). Qed.
Lemma lem6942748 : term278 = term125.
Proof. exact (@lem1982721 term125). Qed.
Lemma lem6942749 (_92533 : int) : (term301 _92533) = term125.
Proof. exact (TRANS (@lem6942747 _92533) (@lem6942748)). Qed.
Lemma lem6942750 (_92532 : int) : (term172 _92532) = (term172 _92532).
Proof. exact (eq_refl (term172 _92532)). Qed.
Lemma lem6942751 (_92533 : int) (_92532 : int) : (term300 _92532 _92533) = (term173 _92532).
Proof. exact (MK_COMB (@lem6942750 _92532) (@lem6942749 _92533)). Qed.
Lemma lem6942752 (_92533 : int) (_92532 : int) : (term299 _92532 _92533) = (term173 _92532).
Proof. exact (TRANS (@lem6942635 _92532 _92533) (@lem6942751 _92533 _92532)). Qed.
Lemma lem6942753 (_92531 : int) (_92533 : int) (_92532 : int) : (term298 _92531 _92532 _92533) = (term264 _92532).
Proof. exact (MK_COMB (@lem6942634 _92531) (@lem6942752 _92533 _92532)). Qed.
Lemma lem6942754 (_92531 : int) (_92533 : int) (_92532 : int) : (term297 _92531 _92532 _92533) = (term264 _92532).
Proof. exact (TRANS (@lem6942526 _92531 _92532 _92533) (@lem6942753 _92531 _92533 _92532)). Qed.
Lemma lem6942755 (_92532 : int) : (term264 _92532) = (term173 _92532).
Proof. exact (@lem1982721 (term173 _92532)). Qed.
Lemma lem6942756 (_92531 : int) (_92533 : int) (_92532 : int) : (term297 _92531 _92532 _92533) = (term173 _92532).
Proof. exact (TRANS (@lem6942754 _92531 _92533 _92532) (@lem6942755 _92532)). Qed.
Lemma lem6942757 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6942758 (_92531 : int) (_92533 : int) (_92532 : int) : (term303 _92531 _92532 _92533) = (term266 _92532).
Proof. exact (MK_COMB (@lem6942757) (@lem6942756 _92531 _92533 _92532)). Qed.
Lemma lem6942759 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6942760 (_92531 : int) (_92533 : int) (_92532 : int) : (term296 _92531 _92532 _92533) = (term267 _92532).
Proof. exact (MK_COMB (@lem6942758 _92531 _92533 _92532) (@lem6942759)). Qed.
Lemma lem6942761 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term267 _92532.
Proof. exact (EQ_MP (@lem6942760 _92531 _92533 _92532) (@lem6942525 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942763 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6942764 : term201 = term202.
Proof. exact (@lem6942763 term80 term101). Qed.
Lemma lem6942766 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942767 : term101 = term163.
Proof. exact (@lem6942766 term102). Qed.
Lemma lem6942769 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942770 : term80 = term122.
Proof. exact (@lem6942769 (NUMERAL 0)). Qed.
Lemma lem6942771 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6942772 : term203 = term204.
Proof. exact (MK_COMB (@lem6942771) (@lem6942770)). Qed.
Lemma lem6942773 : term202 = term205.
Proof. exact (MK_COMB (@lem6942772) (@lem6942767)). Qed.
Lemma lem6942774 : term206.
Proof. exact (@lem1980255 term80 term101 term101 term101). Qed.
Lemma lem6942776 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942777 : term202 = term208.
Proof. exact (@lem6942776 (NUMERAL 0) term102). Qed.
Lemma lem6942778 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942779 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942780 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942779 h1) (fun h1 : term208 = True => @lem6942778)). Qed.
Lemma lem6942781 : term208 = True.
Proof. exact (EQ_MP (@lem6942780) (@lem6942778)). Qed.
Lemma lem6942782 : term202 = True.
Proof. exact (TRANS (@lem6942777) (@lem6942781)). Qed.
Lemma lem6942783 : True = term202.
Proof. exact (SYM (@lem6942782)). Qed.
Lemma lem6942784 : term202.
Proof. exact (EQ_MP (@lem6942783) (@lem0)). Qed.
Lemma lem6942785 : term210.
Proof. exact (@lem6942774 (@lem6942784)). Qed.
Lemma lem6942787 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942788 : term202 = term208.
Proof. exact (@lem6942787 (NUMERAL 0) term102). Qed.
Lemma lem6942789 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942790 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942791 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942790 h1) (fun h1 : term208 = True => @lem6942789)). Qed.
Lemma lem6942792 : term208 = True.
Proof. exact (EQ_MP (@lem6942791) (@lem6942789)). Qed.
Lemma lem6942793 : term202 = True.
Proof. exact (TRANS (@lem6942788) (@lem6942792)). Qed.
Lemma lem6942794 : True = term202.
Proof. exact (SYM (@lem6942793)). Qed.
Lemma lem6942795 : term202.
Proof. exact (EQ_MP (@lem6942794) (@lem0)). Qed.
Lemma lem6942796 : term205 = term211.
Proof. exact (@lem6942785 (@lem6942795)). Qed.
Lemma lem6942798 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6942799 : term134 = term135.
Proof. exact (@lem6942798 term102 term102). Qed.
Lemma lem6942800 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942801 : term137 = term102.
Proof. exact (EQ_MP (@lem6942800) (@lem940073)). Qed.
Lemma lem6942802 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942803 : term135 = term101.
Proof. exact (MK_COMB (@lem6942802) (@lem6942801)). Qed.
Lemma lem6942804 : term134 = term101.
Proof. exact (TRANS (@lem6942799) (@lem6942803)). Qed.
Lemma lem6942806 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6942807 : term213 = term80.
Proof. exact (@lem6942806 term102). Qed.
Lemma lem6942808 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6942809 : term214 = term203.
Proof. exact (MK_COMB (@lem6942808) (@lem6942807)). Qed.
Lemma lem6942810 : term211 = term202.
Proof. exact (MK_COMB (@lem6942809) (@lem6942804)). Qed.
Lemma lem6942812 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942813 : term202 = term208.
Proof. exact (@lem6942812 (NUMERAL 0) term102). Qed.
Lemma lem6942814 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942815 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942816 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942815 h1) (fun h1 : term208 = True => @lem6942814)). Qed.
Lemma lem6942817 : term208 = True.
Proof. exact (EQ_MP (@lem6942816) (@lem6942814)). Qed.
Lemma lem6942818 : term202 = True.
Proof. exact (TRANS (@lem6942813) (@lem6942817)). Qed.
Lemma lem6942819 : term211 = True.
Proof. exact (TRANS (@lem6942810) (@lem6942818)). Qed.
Lemma lem6942820 : term205 = True.
Proof. exact (TRANS (@lem6942796) (@lem6942819)). Qed.
Lemma lem6942821 : term202 = True.
Proof. exact (TRANS (@lem6942773) (@lem6942820)). Qed.
Lemma lem6942822 : term201 = True.
Proof. exact (TRANS (@lem6942764) (@lem6942821)). Qed.
Lemma lem6942823 : True = term201.
Proof. exact (SYM (@lem6942822)). Qed.
Lemma lem6942824 : term201.
Proof. exact (EQ_MP (@lem6942823) (@lem0)). Qed.
Lemma lem6942825 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term268 _92532.
Proof. exact (conj (@lem6942824) (@lem6942761 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942827 (x : real) (y : real) : term216 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6942828 (_92532 : int) : term269 _92532.
Proof. exact (@lem6942827 term101 (term173 _92532)). Qed.
Lemma lem6942829 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term270 _92532.
Proof. exact (@lem6942828 _92532 (@lem6942825 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942830 (_92532 : int) : (term271 _92532) = (term173 _92532).
Proof. exact (@lem1982733 (term173 _92532)). Qed.
Lemma lem6942831 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6942832 (_92532 : int) : (term272 _92532) = (term266 _92532).
Proof. exact (MK_COMB (@lem6942831) (@lem6942830 _92532)). Qed.
Lemma lem6942833 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6942834 (_92532 : int) : (term270 _92532) = (term267 _92532).
Proof. exact (MK_COMB (@lem6942832 _92532) (@lem6942833)). Qed.
Lemma lem6942835 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term267 _92532.
Proof. exact (EQ_MP (@lem6942834 _92532) (@lem6942829 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942836 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term273 _92532.
Proof. exact (conj (@lem6942835 _92532 _92531 _92533 h1) (@lem6942372 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942838 (x : real) (y : real) : term232 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6942839 (_92532 : int) : term274 _92532.
Proof. exact (@lem6942838 (term173 _92532) (real_of_int _92532)). Qed.
Lemma lem6942840 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term275 _92532.
Proof. exact (@lem6942839 _92532 (@lem6942836 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942841 (_92532 : int) : (term276 _92532) = (term277 _92532).
Proof. exact (@lem1982759 (term176 _92532) (real_of_int _92532) term125). Qed.
Lemma lem6942842 (_92532 : int) : (term238 _92532) = (term239 _92532).
Proof. exact (@lem1982713 term125 (real_of_int _92532)). Qed.
Lemma lem6942844 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942845 : term101 = term163.
Proof. exact (@lem6942844 term102). Qed.
Lemma lem6942847 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6942848 : term125 = term126.
Proof. exact (@lem6942847 term102). Qed.
Lemma lem6942849 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6942850 : term240 = term241.
Proof. exact (MK_COMB (@lem6942849) (@lem6942848)). Qed.
Lemma lem6942851 : term242 = term243.
Proof. exact (MK_COMB (@lem6942850) (@lem6942845)). Qed.
Lemma lem6942852 : term244.
Proof. exact (@lem1981473 term125 term101 term101 term101 term80 term101). Qed.
Lemma lem6942854 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942855 : term202 = term208.
Proof. exact (@lem6942854 (NUMERAL 0) term102). Qed.
Lemma lem6942856 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942857 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942858 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942857 h1) (fun h1 : term208 = True => @lem6942856)). Qed.
Lemma lem6942859 : term208 = True.
Proof. exact (EQ_MP (@lem6942858) (@lem6942856)). Qed.
Lemma lem6942860 : term202 = True.
Proof. exact (TRANS (@lem6942855) (@lem6942859)). Qed.
Lemma lem6942861 : True = term202.
Proof. exact (SYM (@lem6942860)). Qed.
Lemma lem6942862 : term202.
Proof. exact (EQ_MP (@lem6942861) (@lem0)). Qed.
Lemma lem6942863 : term245.
Proof. exact (@lem6942852 (@lem6942862)). Qed.
Lemma lem6942865 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942866 : term202 = term208.
Proof. exact (@lem6942865 (NUMERAL 0) term102). Qed.
Lemma lem6942867 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942868 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942869 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942868 h1) (fun h1 : term208 = True => @lem6942867)). Qed.
Lemma lem6942870 : term208 = True.
Proof. exact (EQ_MP (@lem6942869) (@lem6942867)). Qed.
Lemma lem6942871 : term202 = True.
Proof. exact (TRANS (@lem6942866) (@lem6942870)). Qed.
Lemma lem6942872 : True = term202.
Proof. exact (SYM (@lem6942871)). Qed.
Lemma lem6942873 : term202.
Proof. exact (EQ_MP (@lem6942872) (@lem0)). Qed.
Lemma lem6942874 : term246.
Proof. exact (@lem6942863 (@lem6942873)). Qed.
Lemma lem6942876 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942877 : term202 = term208.
Proof. exact (@lem6942876 (NUMERAL 0) term102). Qed.
Lemma lem6942878 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942879 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942880 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942879 h1) (fun h1 : term208 = True => @lem6942878)). Qed.
Lemma lem6942881 : term208 = True.
Proof. exact (EQ_MP (@lem6942880) (@lem6942878)). Qed.
Lemma lem6942882 : term202 = True.
Proof. exact (TRANS (@lem6942877) (@lem6942881)). Qed.
Lemma lem6942883 : True = term202.
Proof. exact (SYM (@lem6942882)). Qed.
Lemma lem6942884 : term202.
Proof. exact (EQ_MP (@lem6942883) (@lem0)). Qed.
Lemma lem6942885 : term247.
Proof. exact (@lem6942874 (@lem6942884)). Qed.
Lemma lem6942887 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6942888 : term134 = term135.
Proof. exact (@lem6942887 term102 term102). Qed.
Lemma lem6942889 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942890 : term137 = term102.
Proof. exact (EQ_MP (@lem6942889) (@lem940073)). Qed.
Lemma lem6942891 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942892 : term135 = term101.
Proof. exact (MK_COMB (@lem6942891) (@lem6942890)). Qed.
Lemma lem6942893 : term134 = term101.
Proof. exact (TRANS (@lem6942888) (@lem6942892)). Qed.
Lemma lem6942895 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6942896 : term164 = term169.
Proof. exact (@lem6942895 term102 term102). Qed.
Lemma lem6942897 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942898 : term137 = term102.
Proof. exact (EQ_MP (@lem6942897) (@lem940073)). Qed.
Lemma lem6942899 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942900 : term135 = term101.
Proof. exact (MK_COMB (@lem6942899) (@lem6942898)). Qed.
Lemma lem6942901 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6942902 : term169 = term125.
Proof. exact (MK_COMB (@lem6942901) (@lem6942900)). Qed.
Lemma lem6942903 : term164 = term125.
Proof. exact (TRANS (@lem6942896) (@lem6942902)). Qed.
Lemma lem6942904 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6942905 : term248 = term240.
Proof. exact (MK_COMB (@lem6942904) (@lem6942903)). Qed.
Lemma lem6942906 : term249 = term242.
Proof. exact (MK_COMB (@lem6942905) (@lem6942893)). Qed.
Lemma lem6942908 (m : nat) : (term250 m) = term80.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6942909 : term242 = term80.
Proof. exact (@lem6942908 term102). Qed.
Lemma lem6942910 : term249 = term80.
Proof. exact (TRANS (@lem6942906) (@lem6942909)). Qed.
Lemma lem6942911 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6942912 : term251 = term252.
Proof. exact (MK_COMB (@lem6942911) (@lem6942910)). Qed.
Lemma lem6942913 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem6942914 : term253 = term213.
Proof. exact (MK_COMB (@lem6942912) (@lem6942913)). Qed.
Lemma lem6942916 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6942917 : term213 = term80.
Proof. exact (@lem6942916 term102). Qed.
Lemma lem6942918 : term253 = term80.
Proof. exact (TRANS (@lem6942914) (@lem6942917)). Qed.
Lemma lem6942920 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6942921 : term134 = term135.
Proof. exact (@lem6942920 term102 term102). Qed.
Lemma lem6942922 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942923 : term137 = term102.
Proof. exact (EQ_MP (@lem6942922) (@lem940073)). Qed.
Lemma lem6942924 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6942925 : term135 = term101.
Proof. exact (MK_COMB (@lem6942924) (@lem6942923)). Qed.
Lemma lem6942926 : term134 = term101.
Proof. exact (TRANS (@lem6942921) (@lem6942925)). Qed.
Lemma lem6942927 : term252 = term252.
Proof. exact (eq_refl term252). Qed.
Lemma lem6942928 : term254 = term213.
Proof. exact (MK_COMB (@lem6942927) (@lem6942926)). Qed.
Lemma lem6942930 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6942931 : term213 = term80.
Proof. exact (@lem6942930 term102). Qed.
Lemma lem6942932 : term254 = term80.
Proof. exact (TRANS (@lem6942928) (@lem6942931)). Qed.
Lemma lem6942933 : term80 = term254.
Proof. exact (SYM (@lem6942932)). Qed.
Lemma lem6942934 : term253 = term254.
Proof. exact (TRANS (@lem6942918) (@lem6942933)). Qed.
Lemma lem6942935 : term243 = term122.
Proof. exact (@lem6942885 (@lem6942934)). Qed.
Lemma lem6942936 : term242 = term122.
Proof. exact (TRANS (@lem6942851) (@lem6942935)). Qed.
Lemma lem6942938 (x : real) : (term141 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6942939 : term122 = term80.
Proof. exact (@lem6942938 term80). Qed.
Lemma lem6942940 : term242 = term80.
Proof. exact (TRANS (@lem6942936) (@lem6942939)). Qed.
Lemma lem6942941 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6942942 : term255 = term252.
Proof. exact (MK_COMB (@lem6942941) (@lem6942940)). Qed.
Lemma lem6942943 (_92532 : int) : (real_of_int _92532) = (real_of_int _92532).
Proof. exact (eq_refl (real_of_int _92532)). Qed.
Lemma lem6942944 (_92532 : int) : (term239 _92532) = (term256 _92532).
Proof. exact (MK_COMB (@lem6942942) (@lem6942943 _92532)). Qed.
Lemma lem6942945 (_92532 : int) : (term238 _92532) = (term256 _92532).
Proof. exact (TRANS (@lem6942842 _92532) (@lem6942944 _92532)). Qed.
Lemma lem6942946 (_92532 : int) : (term256 _92532) = term80.
Proof. exact (@lem1982719 (real_of_int _92532)). Qed.
Lemma lem6942947 (_92532 : int) : (term238 _92532) = term80.
Proof. exact (TRANS (@lem6942945 _92532) (@lem6942946 _92532)). Qed.
Lemma lem6942948 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6942949 (_92532 : int) : (term257 _92532) = term258.
Proof. exact (MK_COMB (@lem6942948) (@lem6942947 _92532)). Qed.
Lemma lem6942950 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem6942951 (_92532 : int) : (term277 _92532) = term278.
Proof. exact (MK_COMB (@lem6942949 _92532) (@lem6942950)). Qed.
Lemma lem6942952 (_92532 : int) : (term276 _92532) = term278.
Proof. exact (TRANS (@lem6942841 _92532) (@lem6942951 _92532)). Qed.
Lemma lem6942953 : term278 = term125.
Proof. exact (@lem1982721 term125). Qed.
Lemma lem6942954 (_92532 : int) : (term276 _92532) = term125.
Proof. exact (TRANS (@lem6942952 _92532) (@lem6942953)). Qed.
Lemma lem6942955 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6942956 (_92532 : int) : (term279 _92532) = term280.
Proof. exact (MK_COMB (@lem6942955) (@lem6942954 _92532)). Qed.
Lemma lem6942957 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6942958 (_92532 : int) : (term275 _92532) = term281.
Proof. exact (MK_COMB (@lem6942956 _92532) (@lem6942957)). Qed.
Lemma lem6942959 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : term281.
Proof. exact (EQ_MP (@lem6942958 _92532) (@lem6942840 _92532 _92531 _92533 h1)). Qed.
Lemma lem6942961 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6942962 : term281 = term282.
Proof. exact (@lem6942961 term80 term125). Qed.
Lemma lem6942964 (x : nat) : (term123 x) = (term124 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6942965 : term125 = term126.
Proof. exact (@lem6942964 term102). Qed.
Lemma lem6942967 (x : nat) : (real_of_num x) = (term121 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6942968 : term80 = term122.
Proof. exact (@lem6942967 (NUMERAL 0)). Qed.
Lemma lem6942969 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6942970 : term82 = term283.
Proof. exact (MK_COMB (@lem6942969) (@lem6942968)). Qed.
Lemma lem6942971 : term282 = term284.
Proof. exact (MK_COMB (@lem6942970) (@lem6942965)). Qed.
Lemma lem6942972 : term285.
Proof. exact (@lem1980026 term80 term101 term125 term101). Qed.
Lemma lem6942974 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942975 : term202 = term208.
Proof. exact (@lem6942974 (NUMERAL 0) term102). Qed.
Lemma lem6942976 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942977 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942978 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942977 h1) (fun h1 : term208 = True => @lem6942976)). Qed.
Lemma lem6942979 : term208 = True.
Proof. exact (EQ_MP (@lem6942978) (@lem6942976)). Qed.
Lemma lem6942980 : term202 = True.
Proof. exact (TRANS (@lem6942975) (@lem6942979)). Qed.
Lemma lem6942981 : True = term202.
Proof. exact (SYM (@lem6942980)). Qed.
Lemma lem6942982 : term202.
Proof. exact (EQ_MP (@lem6942981) (@lem0)). Qed.
Lemma lem6942983 : term286.
Proof. exact (@lem6942972 (@lem6942982)). Qed.
Lemma lem6942985 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6942986 : term202 = term208.
Proof. exact (@lem6942985 (NUMERAL 0) term102). Qed.
Lemma lem6942987 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6942988 (h1 : term209 = (BIT1 0)) : term208 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6942989 : (term209 = (BIT1 0)) = (term208 = True).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6942988 h1) (fun h1 : term208 = True => @lem6942987)). Qed.
Lemma lem6942990 : term208 = True.
Proof. exact (EQ_MP (@lem6942989) (@lem6942987)). Qed.
Lemma lem6942991 : term202 = True.
Proof. exact (TRANS (@lem6942986) (@lem6942990)). Qed.
Lemma lem6942992 : True = term202.
Proof. exact (SYM (@lem6942991)). Qed.
Lemma lem6942993 : term202.
Proof. exact (EQ_MP (@lem6942992) (@lem0)). Qed.
Lemma lem6942994 : term284 = term287.
Proof. exact (@lem6942983 (@lem6942993)). Qed.
Lemma lem6942996 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6942997 : term164 = term169.
Proof. exact (@lem6942996 term102 term102). Qed.
Lemma lem6942998 : (term136 = (BIT1 0)) = (term137 = term102).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6942999 : term137 = term102.
Proof. exact (EQ_MP (@lem6942998) (@lem940073)). Qed.
Lemma lem6943000 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6943001 : term135 = term101.
Proof. exact (MK_COMB (@lem6943000) (@lem6942999)). Qed.
Lemma lem6943002 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6943003 : term169 = term125.
Proof. exact (MK_COMB (@lem6943002) (@lem6943001)). Qed.
Lemma lem6943004 : term164 = term125.
Proof. exact (TRANS (@lem6942997) (@lem6943003)). Qed.
Lemma lem6943006 (x : nat) : (term212 x) = term80.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6943007 : term213 = term80.
Proof. exact (@lem6943006 term102). Qed.
Lemma lem6943008 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6943009 : term288 = term82.
Proof. exact (MK_COMB (@lem6943008) (@lem6943007)). Qed.
Lemma lem6943010 : term287 = term282.
Proof. exact (MK_COMB (@lem6943009) (@lem6943004)). Qed.
Lemma lem6943012 (m : nat) (n : nat) : (term289 m n) = (term290 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6943013 : term282 = term291.
Proof. exact (@lem6943012 (NUMERAL 0) term102). Qed.
Lemma lem6943014 : term209 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6943015 (h1 : term209 = (BIT1 0)) : (term102 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6943016 : (term209 = (BIT1 0)) = ((term102 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term209 = (BIT1 0) => @lem6943015 h1) (fun h1 : (term102 = (NUMERAL 0)) = False => @lem6943014)). Qed.
Lemma lem6943017 : (term102 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6943016) (@lem6943014)). Qed.
Lemma lem6943018 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6943019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6943020 : term292 = (and True).
Proof. exact (MK_COMB (@lem6943019) (@lem6943018)). Qed.
Lemma lem6943021 : term291 = (True /\ False).
Proof. exact (MK_COMB (@lem6943020) (@lem6943017)). Qed.
Lemma lem6943023 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6943024 : term291 = False.
Proof. exact (TRANS (@lem6943021) (@lem6943023)). Qed.
Lemma lem6943025 : term282 = False.
Proof. exact (TRANS (@lem6943013) (@lem6943024)). Qed.
Lemma lem6943026 : term287 = False.
Proof. exact (TRANS (@lem6943010) (@lem6943025)). Qed.
Lemma lem6943027 : term284 = False.
Proof. exact (TRANS (@lem6942994) (@lem6943026)). Qed.
Lemma lem6943028 : term282 = False.
Proof. exact (TRANS (@lem6942971) (@lem6943027)). Qed.
Lemma lem6943029 : term281 = False.
Proof. exact (TRANS (@lem6942962) (@lem6943028)). Qed.
Lemma lem6943030 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term293 _92532 _92531 _92533) : False.
Proof. exact (EQ_MP (@lem6943029) (@lem6942959 _92532 _92531 _92533 h1)). Qed.
Lemma lem6943031 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term197 _92532 _92531 _92533) : False.
Proof. exact (or_elim (@lem6941544 _92532 _92531 _92533 h1) (fun h0 : term200 _92533 _92531 _92532 => @lem6942285 _92533 _92531 _92532 h0) (fun h0 : term293 _92532 _92531 _92533 => @lem6943030 _92532 _92531 _92533 h0)). Qed.
Lemma lem6943033 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term197 _92532 _92531 _92533) : term197 _92532 _92531 _92533.
Proof. exact (h1). Qed.
Lemma lem6943034 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term197 _92532 _92531 _92533) : (term197 _92532 _92531 _92533) = False.
Proof. exact (prop_ext (fun h2 : term197 _92532 _92531 _92533 => @lem6943031 _92532 _92531 _92533 h1) (fun h2 : False => @lem6943033 _92532 _92531 _92533 h1)). Qed.
Lemma lem6943035 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term197 _92532 _92531 _92533) : False.
Proof. exact (EQ_MP (@lem6943034 _92532 _92531 _92533 h1) (@lem6943033 _92532 _92531 _92533 h1)). Qed.
Lemma lem6943036 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term117 _92532 _92531 _92533) : term117 _92532 _92531 _92533.
Proof. exact (h1). Qed.
Lemma lem6943037 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term117 _92532 _92531 _92533) : term197 _92532 _92531 _92533.
Proof. exact (EQ_MP (@lem6941534 _92532 _92531 _92533) (@lem6943036 _92532 _92531 _92533 h1)). Qed.
Lemma lem6943038 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term117 _92532 _92531 _92533) : (term197 _92532 _92531 _92533) = False.
Proof. exact (prop_ext (fun h2 : term197 _92532 _92531 _92533 => @lem6943035 _92532 _92531 _92533 h2) (fun h2 : False => @lem6943037 _92532 _92531 _92533 h1)). Qed.
Lemma lem6943039 (_92532 : int) (_92531 : int) (_92533 : int) (h1 : term117 _92532 _92531 _92533) : False.
Proof. exact (EQ_MP (@lem6943038 _92532 _92531 _92533 h1) (@lem6943037 _92532 _92531 _92533 h1)). Qed.
Lemma lem6943040 (_92532 : int) (_92531 : int) (_92533 : int) : term304 _92532 _92531 _92533.
Proof. exact (fun h0 : term117 _92532 _92531 _92533 => @lem6943039 _92532 _92531 _92533 h0). Qed.
Lemma lem6943041 (_92532 : int) (_92531 : int) (_92533 : int) : term305 _92532 _92531 _92533.
Proof. exact (@lem1386578 (term306 _92532 _92531 _92533)). Qed.
Lemma lem6943044 (_92532 : int) (_92531 : int) (_92533 : int) : term306 _92532 _92531 _92533.
Proof. exact (@lem6943041 _92532 _92531 _92533 (@lem6943040 _92532 _92531 _92533)). Qed.
Lemma lem6943045 (_92532 : int) (_92533 : int) (_92531 : int) : (term115 _92532 _92531 _92533) = (term73 _92532 _92533 _92531).
Proof. exact (SYM (@lem6940947 _92532 _92531 _92533)). Qed.
Lemma lem6943046 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6943047 (_92532 : int) (_92533 : int) (_92531 : int) : (term306 _92532 _92531 _92533) = (term37 _92532 _92533 _92531).
Proof. exact (MK_COMB (@lem6943046) (@lem6943045 _92532 _92533 _92531)). Qed.
Lemma lem6943048 (_92532 : int) (_92533 : int) (_92531 : int) : term37 _92532 _92533 _92531.
Proof. exact (EQ_MP (@lem6943047 _92532 _92533 _92531) (@lem6943044 _92532 _92531 _92533)). Qed.
Lemma lem6943049 (_92532 : int) (_92533 : int) (_92531 : int) : term38 _92532 _92533 _92531.
Proof. exact (EQ_MP (@lem6940702 _92532 _92533 _92531) (@lem6943048 _92532 _92533 _92531)). Qed.
Lemma lem6943050 (x : nat) (y : nat) (b : nat) : term307 x y b.
Proof. exact (@lem6943049 (int_of_num x) (int_of_num y) (int_of_num b)). Qed.
Lemma lem6943051 (x : nat) (y : nat) (b : nat) : term308 x y b.
Proof. exact (@lem6943050 x y b (@lem6940695 b)). Qed.
Lemma lem6943052 (x : nat) (y : nat) (b : nat) : term309 x y b.
Proof. exact (@lem6943051 x y b (@lem6940698 x)). Qed.
Lemma lem6943053 (x : nat) (y : nat) (b : nat) : term35 x y b.
Proof. exact (@lem6943052 x y b (@lem6940701 y)). Qed.
Lemma lem6943054 (x : nat) (y : nat) (b : nat) : (term35 x y b) = (term14 x y b).
Proof. exact (SYM (@lem6940692 x y b)). Qed.
Lemma lem6943055 (x : nat) (y : nat) (b : nat) : term14 x y b.
Proof. exact (EQ_MP (@lem6943054 x y b) (@lem6943053 x y b)). Qed.
Lemma lem6943056 (t1 : Prop) : term310 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6943057 (t1 : Prop) : (term310 t1) = (term311 t1).
Proof. exact (eq_refl (term310 t1)). Qed.
Lemma lem6943058 (t1 : Prop) : term311 t1.
Proof. exact (EQ_MP (@lem6943057 t1) (@lem6943056 t1)). Qed.
Lemma lem6943059 (t1 : Prop) (t2 : Prop) : term312 t1 t2.
Proof. exact (@lem6943058 t1 t2). Qed.
Lemma lem6943060 (t1 : Prop) (t2 : Prop) : (term312 t1 t2) = (term313 t1 t2).
Proof. exact (eq_refl (term312 t1 t2)). Qed.
Lemma lem6943061 (t1 : Prop) (t2 : Prop) : term313 t1 t2.
Proof. exact (EQ_MP (@lem6943060 t1 t2) (@lem6943059 t1 t2)). Qed.
Lemma lem6943062 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term314 t1 t2 t3.
Proof. exact (@lem6943061 t1 t2 t3). Qed.
Lemma lem6943063 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term314 t1 t2 t3) = ((term315 t1 t2 t3) = (term316 t1 t2 t3)).
Proof. exact (eq_refl (term314 t1 t2 t3)). Qed.
Lemma lem6943064 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term315 t1 t2 t3) = (term316 t1 t2 t3).
Proof. exact (EQ_MP (@lem6943063 t1 t2 t3) (@lem6943062 t1 t2 t3)). Qed.
Lemma lem6943065 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term316 t1 t2 t3) = (term315 t1 t2 t3).
Proof. exact (SYM (@lem6943064 t1 t2 t3)). Qed.
Lemma lem6943066 (x : nat) (y : nat) : term317 x y.
Proof. exact (fun b : nat => @lem6943055 x y b). Qed.
Lemma lem6943067 (x : nat) : term318 x.
Proof. exact (fun y : nat => @lem6943066 x y). Qed.
Lemma lem6943068 : term319.
Proof. exact (fun x : nat => @lem6943067 x). Qed.
Lemma lem6943069 {A : Type'} (x : A) : term320 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem6943070 {A : Type'} (x : A) : (term320 A x) = (term321 A x).
Proof. exact (eq_refl (term320 A x)). Qed.
Lemma lem6943071 {A : Type'} (x : A) : term321 A x.
Proof. exact (EQ_MP (@lem6943070 A x) (@lem6943069 A x)). Qed.
Lemma lem6943072 {A : Type'} (x : A) (y : A) : term322 A x y.
Proof. exact (@lem6943071 A x y). Qed.
Lemma lem6943073 {A : Type'} (y : A) (x : A) : (term322 A x y) = (term323 A y x).
Proof. exact (eq_refl (term322 A x y)). Qed.
Lemma lem6943074 {A : Type'} (y : A) (x : A) : term323 A y x.
Proof. exact (EQ_MP (@lem6943073 A y x) (@lem6943072 A x y)). Qed.
Lemma lem6943075 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term324 A y x s.
Proof. exact (@lem6943074 A y x s). Qed.
Lemma lem6943076 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term324 A y x s) = ((term325 A x y s) = (term326 A y x s)).
Proof. exact (eq_refl (term324 A y x s)). Qed.
Lemma lem6943078 {A : Type'} (x : A) : term327 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem6943079 {A : Type'} (x : A) : (term327 A x) = (term328 A x).
Proof. exact (eq_refl (term327 A x)). Qed.
Lemma lem6943080 {A : Type'} (x : A) : term328 A x.
Proof. exact (EQ_MP (@lem6943079 A x) (@lem6943078 A x)). Qed.
Lemma lem6943081 {A : Type'} (x : A) : term329 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem6943083 {_126525 : Type'} : term330 _126525.
Proof. exact (proj2 (@lem6924916 Prop _126525)). Qed.
Lemma lem6943084 {_126525 : Type'} (x : _126525) : term331 _126525 x.
Proof. exact (@lem6943083 _126525 x). Qed.
Lemma lem6943085 {_126525 : Type'} (x : _126525) : (term331 _126525 x) = (term332 _126525 x).
Proof. exact (eq_refl (term331 _126525 x)). Qed.
Lemma lem6943086 {_126525 : Type'} (x : _126525) : term332 _126525 x.
Proof. exact (EQ_MP (@lem6943085 _126525 x) (@lem6943084 _126525 x)). Qed.
Lemma lem6943087 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term333 _126525 x f.
Proof. exact (@lem6943086 _126525 x f). Qed.
Lemma lem6943088 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term333 _126525 x f) = (term334 _126525 x f).
Proof. exact (eq_refl (term333 _126525 x f)). Qed.
Lemma lem6943089 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term334 _126525 x f.
Proof. exact (EQ_MP (@lem6943088 _126525 x f) (@lem6943087 _126525 x f)). Qed.
Lemma lem6943090 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) : term335 _126525 x f s.
Proof. exact (@lem6943089 _126525 x f s). Qed.
Lemma lem6943091 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term335 _126525 x f s) = (term336 _126525 x s f).
Proof. exact (eq_refl (term335 _126525 x f s)). Qed.
Lemma lem6943092 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term336 _126525 x s f.
Proof. exact (EQ_MP (@lem6943091 _126525 x s f) (@lem6943090 _126525 x f s)). Qed.
Lemma lem6943093 {_126525 : Type'} (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : @FINITE _126525 s.
Proof. exact (h1). Qed.
Lemma lem6943094 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : (term337 _126525 x s f) = (term338 _126525 x s f).
Proof. exact (@lem6943092 _126525 x s f (@lem6943093 _126525 s h1)). Qed.
Lemma lem6943100 {_126486 : Type'} : term339 _126486.
Proof. exact (proj1 (@lem6924916 _126486 Prop)). Qed.
Lemma lem6943101 {_126486 : Type'} (f : _126486 -> nat) : term340 _126486 f.
Proof. exact (@lem6943100 _126486 f). Qed.
Lemma lem6943102 {_126486 : Type'} (f : _126486 -> nat) : (term340 _126486 f) = ((@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0)).
Proof. exact (eq_refl (term340 _126486 f)). Qed.
Lemma lem6943104 {A : Type'} (h1 : term341 A) : term341 A.
Proof. exact (h1). Qed.
Lemma lem6943105 {A : Type'} (P : type686 A) (h1 : term341 A) : term342 A P.
Proof. exact (@lem6943104 A h1 P). Qed.
Lemma lem6943106 {A : Type'} (P : type686 A) : (term342 A P) = (term343 A P).
Proof. exact (eq_refl (term342 A P)). Qed.
Lemma lem6943107 {A : Type'} (P : type686 A) (h1 : term341 A) : term343 A P.
Proof. exact (EQ_MP (@lem6943106 A P) (@lem6943105 A P h1)). Qed.
Lemma lem6943108 {A : Type'} (P : type686 A) (h1 : term344 A P) : term344 A P.
Proof. exact (h1). Qed.
Lemma lem6943109 {A : Type'} (P : type686 A) (h1 : term341 A) (h2 : term344 A P) : term345 A P.
Proof. exact (@lem6943107 A P h1 (@lem6943108 A P h2)). Qed.
Lemma lem6943110 {A : Type'} (P : type686 A) (h1 : term344 A P) : term346 A P.
Proof. exact (fun h0 : term341 A => @lem6943109 A P h0 h1). Qed.
Lemma lem6943111 {A : Type'} (h1 : term341 A) : term341 A.
Proof. exact (h1). Qed.
Lemma lem6943112 {A : Type'} (P : type686 A) (h1 : term341 A) (h2 : term344 A P) : term345 A P.
Proof. exact (@lem6943110 A P h2 (@lem6943111 A h1)). Qed.
Lemma lem6943113 {A : Type'} (P : type686 A) (h1 : term341 A) : term343 A P.
Proof. exact (fun h0 : term344 A P => @lem6943112 A P h1 h0). Qed.
Lemma lem6943114 {A : Type'} (h1 : term341 A) : term341 A.
Proof. exact (fun P : type686 A => @lem6943113 A P h1). Qed.
Lemma lem6943115 {A : Type'} : term347 A.
Proof. exact (fun h0 : term341 A => @lem6943114 A h0). Qed.
Lemma lem6943116 {A : Type'} : term341 A.
Proof. exact (@lem6943115 A (@lem3558722 A)). Qed.
Lemma lem6943117 {A : Type'} (P : type686 A) : term342 A P.
Proof. exact (@lem6943116 A P). Qed.
Lemma lem6943118 {A : Type'} (P : type686 A) : (term342 A P) = (term343 A P).
Proof. exact (eq_refl (term342 A P)). Qed.
Lemma lem6943125 (p : Prop) (q : Prop) (r : Prop) : (term348 p q r) = (term349 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem6943126 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term350 A s f b) = (term351 A s f b).
Proof. exact (@lem6943125 (@FINITE A s) (term352 A s f b) (term353 A s f b)). Qed.
Lemma lem6943137 {A : Type'} (f : A -> nat) (b : nat) : (term354 A f b) = (term355 A f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6943126 A s f b)). Qed.
Lemma lem6943138 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6943139 {A : Type'} (f : A -> nat) (b : nat) : (term356 A f b) = (term357 A f b).
Proof. exact (MK_COMB (@lem6943138 A) (@lem6943137 A f b)). Qed.
Lemma lem6943144 {A : Type'} (f : A -> nat) (b : nat) : (term357 A f b) = (term356 A f b).
Proof. exact (SYM (@lem6943139 A f b)). Qed.
Lemma lem6943146 {A : Type'} (P : type686 A) : term343 A P.
Proof. exact (EQ_MP (@lem6943118 A P) (@lem6943117 A P)). Qed.
Lemma lem6943147 {A : Type'} (P : type686 A) : term343 A P.
Proof. exact (@lem6943146 A P). Qed.
Lemma lem6943148 {A : Type'} (f : A -> nat) (b : nat) : term358 A f b.
Proof. exact (@lem6943147 A (term359 A f b)). Qed.
Lemma lem6943149 {A : Type'} (f : A -> nat) (b : nat) : (term360 A f b) = (term361 A f b).
Proof. exact (eq_refl (term360 A f b)). Qed.
Lemma lem6943150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6943151 {A : Type'} (f : A -> nat) (b : nat) : (term362 A f b) = (term363 A f b).
Proof. exact (MK_COMB (@lem6943150) (@lem6943149 A f b)). Qed.
Lemma lem6943152 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term364 A f b s) = (term365 A s f b).
Proof. exact (eq_refl (term364 A f b s)). Qed.
Lemma lem6943153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6943154 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term366 A f b s) = (term367 A s f b).
Proof. exact (MK_COMB (@lem6943153) (@lem6943152 A s f b)). Qed.
Lemma lem6943155 {A : Type'} (x : A) (s : A -> Prop) : (term368 A x s) = (term368 A x s).
Proof. exact (eq_refl (term368 A x s)). Qed.
Lemma lem6943156 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) : (term369 A f b x s) = (term370 A f b x s).
Proof. exact (MK_COMB (@lem6943154 A s f b) (@lem6943155 A x s)). Qed.
Lemma lem6943157 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6943158 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) : (term371 A f b x s) = (term372 A f b x s).
Proof. exact (MK_COMB (@lem6943157) (@lem6943156 A f b x s)). Qed.
Lemma lem6943159 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term373 A f b x s) = (term374 A x s f b).
Proof. exact (eq_refl (term373 A f b x s)). Qed.
Lemma lem6943160 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term375 A f b x s) = (term376 A x s f b).
Proof. exact (MK_COMB (@lem6943158 A f b x s) (@lem6943159 A x s f b)). Qed.
Lemma lem6943161 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term377 A f b x) = (term378 A x f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6943160 A x s f b)). Qed.
Lemma lem6943162 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6943163 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term379 A f b x) = (term380 A x f b).
Proof. exact (MK_COMB (@lem6943162 A) (@lem6943161 A x f b)). Qed.
Lemma lem6943164 {A : Type'} (f : A -> nat) (b : nat) : (term381 A f b) = (term382 A f b).
Proof. exact (fun_ext (fun x : A => @lem6943163 A x f b)). Qed.
Lemma lem6943165 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6943166 {A : Type'} (f : A -> nat) (b : nat) : (term383 A f b) = (term384 A f b).
Proof. exact (MK_COMB (@lem6943165 A) (@lem6943164 A f b)). Qed.
Lemma lem6943167 {A : Type'} (f : A -> nat) (b : nat) : (term385 A f b) = (term386 A f b).
Proof. exact (MK_COMB (@lem6943151 A f b) (@lem6943166 A f b)). Qed.
Lemma lem6943168 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6943169 {A : Type'} (f : A -> nat) (b : nat) : (term387 A f b) = (term388 A f b).
Proof. exact (MK_COMB (@lem6943168) (@lem6943167 A f b)). Qed.
Lemma lem6943170 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term364 A f b s) = (term365 A s f b).
Proof. exact (eq_refl (term364 A f b s)). Qed.
Lemma lem6943171 {A : Type'} (s : A -> Prop) : (term389 A s) = (term389 A s).
Proof. exact (eq_refl (term389 A s)). Qed.
Lemma lem6943172 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term390 A f b s) = (term351 A s f b).
Proof. exact (MK_COMB (@lem6943171 A s) (@lem6943170 A s f b)). Qed.
Lemma lem6943173 {A : Type'} (f : A -> nat) (b : nat) : (term391 A f b) = (term355 A f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6943172 A s f b)). Qed.
Lemma lem6943174 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6943175 {A : Type'} (f : A -> nat) (b : nat) : (term392 A f b) = (term357 A f b).
Proof. exact (MK_COMB (@lem6943174 A) (@lem6943173 A f b)). Qed.
Lemma lem6943176 {A : Type'} (f : A -> nat) (b : nat) : (term358 A f b) = (term393 A f b).
Proof. exact (MK_COMB (@lem6943169 A f b) (@lem6943175 A f b)). Qed.
Lemma lem6943177 {A : Type'} (f : A -> nat) (b : nat) : term393 A f b.
Proof. exact (EQ_MP (@lem6943176 A f b) (@lem6943148 A f b)). Qed.
Lemma lem6943183 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term394 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6943184 (p : Prop) (q : Prop) (p' : Prop) : term395 p q p'.
Proof. exact (fun q' : Prop => @lem6943183 p q p' q'). Qed.
Lemma lem6943185 (p : Prop) (q : Prop) : term396 p q.
Proof. exact (fun p' : Prop => @lem6943184 p q p'). Qed.
Lemma lem6943186 {A : Type'} (f : A -> nat) (b : nat) : term397 A f b.
Proof. exact (@lem6943185 (term398 A f b) (term399 A f b)). Qed.
Lemma lem6943187 {A : Type'} (f : A -> nat) (b : nat) (p' : Prop) : term400 A f b p'.
Proof. exact (@lem6943186 A f b p'). Qed.
Lemma lem6943188 {A : Type'} (f : A -> nat) (b : nat) (p' : Prop) : (term400 A f b p') = (term401 A f b p').
Proof. exact (eq_refl (term400 A f b p')). Qed.
Lemma lem6943189 {A : Type'} (f : A -> nat) (b : nat) (p' : Prop) : term401 A f b p'.
Proof. exact (EQ_MP (@lem6943188 A f b p') (@lem6943187 A f b p')). Qed.
Lemma lem6943190 {A : Type'} (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : term402 A f b p' q'.
Proof. exact (@lem6943189 A f b p' q'). Qed.
Lemma lem6943191 {A : Type'} (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : (term402 A f b p' q') = (term403 A f b p' q').
Proof. exact (eq_refl (term402 A f b p' q')). Qed.
Lemma lem6943192 {A : Type'} (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : term403 A f b p' q'.
Proof. exact (EQ_MP (@lem6943191 A f b p' q') (@lem6943190 A f b p' q')). Qed.
Lemma lem6943194 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6943102 _126486 f) (@lem6943101 _126486 f)). Qed.
Lemma lem6943195 {A : Type'} (f : A -> nat) : (@nsum A (@EMPTY A) f) = (NUMERAL 0).
Proof. exact (@lem6943194 A f). Qed.
Lemma lem6943196 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6943197 {A : Type'} (f : A -> nat) : (term404 A f) = term405.
Proof. exact (MK_COMB (@lem6943196) (@lem6943195 A f)). Qed.
Lemma lem6943198 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6943199 {A : Type'} (f : A -> nat) (b : nat) : (term398 A f b) = (term2 b).
Proof. exact (MK_COMB (@lem6943197 A f) (@lem6943198 b)). Qed.
Lemma lem6943200 {A : Type'} (f : A -> nat) (b : nat) (q' : Prop) : term406 A f b q'.
Proof. exact (@lem6943192 A f b (term2 b) q'). Qed.
Lemma lem6943201 {A : Type'} (f : A -> nat) (b : nat) (q' : Prop) : term407 A f b q'.
Proof. exact (@lem6943200 A f b q' (@lem6943199 A f b)). Qed.
Lemma lem6943212 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term394 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6943213 (p : Prop) (q : Prop) (p' : Prop) : term395 p q p'.
Proof. exact (fun q' : Prop => @lem6943212 p q p' q'). Qed.
Lemma lem6943214 (p : Prop) (q : Prop) : term396 p q.
Proof. exact (fun p' : Prop => @lem6943213 p q p'). Qed.
Lemma lem6943215 {A : Type'} (f : A -> nat) (x : A) (b : nat) : term408 A f x b.
Proof. exact (@lem6943214 (@IN A x (@EMPTY A)) (term409 A f x b)). Qed.
Lemma lem6943216 {A : Type'} (f : A -> nat) (x : A) (b : nat) (p' : Prop) : term410 A f x b p'.
Proof. exact (@lem6943215 A f x b p'). Qed.
Lemma lem6943217 {A : Type'} (f : A -> nat) (x : A) (b : nat) (p' : Prop) : (term410 A f x b p') = (term411 A f x b p').
Proof. exact (eq_refl (term410 A f x b p')). Qed.
Lemma lem6943218 {A : Type'} (f : A -> nat) (x : A) (b : nat) (p' : Prop) : term411 A f x b p'.
Proof. exact (EQ_MP (@lem6943217 A f x b p') (@lem6943216 A f x b p')). Qed.
Lemma lem6943219 {A : Type'} (f : A -> nat) (x : A) (b : nat) (p' : Prop) (q' : Prop) : term412 A f x b p' q'.
Proof. exact (@lem6943218 A f x b p' q'). Qed.
Lemma lem6943220 {A : Type'} (f : A -> nat) (x : A) (b : nat) (p' : Prop) (q' : Prop) : (term412 A f x b p' q') = (term413 A f x b p' q').
Proof. exact (eq_refl (term412 A f x b p' q')). Qed.
Lemma lem6943221 {A : Type'} (f : A -> nat) (x : A) (b : nat) (p' : Prop) (q' : Prop) : term413 A f x b p' q'.
Proof. exact (EQ_MP (@lem6943220 A f x b p' q') (@lem6943219 A f x b p' q')). Qed.
Lemma lem6943223 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6943081 A x (@lem6943080 A x)). Qed.
Lemma lem6943224 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6943223 A x). Qed.
Lemma lem6943225 {A : Type'} (f : A -> nat) (x : A) (b : nat) (q' : Prop) : term414 A f x b q'.
Proof. exact (@lem6943221 A f x b False q'). Qed.
Lemma lem6943226 {A : Type'} (f : A -> nat) (x : A) (b : nat) (q' : Prop) : term415 A f x b q'.
Proof. exact (@lem6943225 A f x b q' (@lem6943224 A x)). Qed.
Lemma lem6943230 {A : Type'} (f : A -> nat) (x : A) (b : nat) : (term409 A f x b) = (term409 A f x b).
Proof. exact (eq_refl (term409 A f x b)). Qed.
Lemma lem6943231 {A : Type'} (f : A -> nat) (x : A) (b : nat) : term416 A f x b.
Proof. exact (fun h0 : False => @lem6943230 A f x b). Qed.
Lemma lem6943232 {A : Type'} (f : A -> nat) (x : A) (b : nat) : term417 A f x b.
Proof. exact (@lem6943226 A f x b (term409 A f x b)). Qed.
Lemma lem6943233 {A : Type'} (f : A -> nat) (x : A) (b : nat) : (term418 A f x b) = (term419 A f x b).
Proof. exact (@lem6943232 A f x b (@lem6943231 A f x b)). Qed.
Lemma lem6943235 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem6943236 {A : Type'} (f : A -> nat) (x : A) (b : nat) : (term419 A f x b) = True.
Proof. exact (@lem6943235 (term409 A f x b)). Qed.
Lemma lem6943237 {A : Type'} (f : A -> nat) (x : A) (b : nat) : (term418 A f x b) = True.
Proof. exact (TRANS (@lem6943233 A f x b) (@lem6943236 A f x b)). Qed.
Lemma lem6943238 {A : Type'} (f : A -> nat) (b : nat) : (term420 A f b) = (term421 A).
Proof. exact (fun_ext (fun x : A => @lem6943237 A f x b)). Qed.
Lemma lem6943239 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6943240 {A : Type'} (f : A -> nat) (b : nat) : (term399 A f b) = (term422 A).
Proof. exact (MK_COMB (@lem6943239 A) (@lem6943238 A f b)). Qed.
Lemma lem6943242 {A : Type'} (t : Prop) : (term423 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6943243 {A : Type'} (t : Prop) : (term423 A t) = t.
Proof. exact (@lem6943242 A t). Qed.
Lemma lem6943244 {A : Type'} : (term422 A) = True.
Proof. exact (@lem6943243 A True). Qed.
Lemma lem6943245 {A : Type'} (f : A -> nat) (b : nat) : (term399 A f b) = True.
Proof. exact (TRANS (@lem6943240 A f b) (@lem6943244 A)). Qed.
Lemma lem6943246 {A : Type'} (f : A -> nat) (b : nat) : term424 A f b.
Proof. exact (fun h0 : term2 b => @lem6943245 A f b). Qed.
Lemma lem6943247 {A : Type'} (f : A -> nat) (b : nat) : term425 A f b.
Proof. exact (@lem6943201 A f b True). Qed.
Lemma lem6943248 {A : Type'} (f : A -> nat) (b : nat) : (term361 A f b) = (term426 b).
Proof. exact (@lem6943247 A f b (@lem6943246 A f b)). Qed.
Lemma lem6943250 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6943251 (b : nat) : (term426 b) = True.
Proof. exact (@lem6943250 (term2 b)). Qed.
Lemma lem6943252 {A : Type'} (f : A -> nat) (b : nat) : (term361 A f b) = True.
Proof. exact (TRANS (@lem6943248 A f b) (@lem6943251 b)). Qed.
Lemma lem6943253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6943254 {A : Type'} (f : A -> nat) (b : nat) : (term363 A f b) = (and True).
Proof. exact (MK_COMB (@lem6943253) (@lem6943252 A f b)). Qed.
Lemma lem6943266 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term394 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6943267 (p : Prop) (q : Prop) (p' : Prop) : term395 p q p'.
Proof. exact (fun q' : Prop => @lem6943266 p q p' q'). Qed.
Lemma lem6943268 (p : Prop) (q : Prop) : term396 p q.
Proof. exact (fun p' : Prop => @lem6943267 p q p'). Qed.
Lemma lem6943269 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : term427 A x s f b.
Proof. exact (@lem6943268 (term370 A f b x s) (term374 A x s f b)). Qed.
Lemma lem6943270 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : term428 A x s f b p'.
Proof. exact (@lem6943269 A x s f b p'). Qed.
Lemma lem6943271 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : (term428 A x s f b p') = (term429 A x s f b p').
Proof. exact (eq_refl (term428 A x s f b p')). Qed.
Lemma lem6943272 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : term429 A x s f b p'.
Proof. exact (EQ_MP (@lem6943271 A x s f b p') (@lem6943270 A x s f b p')). Qed.
Lemma lem6943273 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : term430 A x s f b p' q'.
Proof. exact (@lem6943272 A x s f b p' q'). Qed.
Lemma lem6943274 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : (term430 A x s f b p' q') = (term431 A x s f b p' q').
Proof. exact (eq_refl (term430 A x s f b p' q')). Qed.
Lemma lem6943275 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : term431 A x s f b p' q'.
Proof. exact (EQ_MP (@lem6943274 A x s f b p' q') (@lem6943273 A x s f b p' q')). Qed.
Lemma lem6943357 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) : (term370 A f b x s) = (term370 A f b x s).
Proof. exact (eq_refl (term370 A f b x s)). Qed.
Lemma lem6943358 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (q' : Prop) : term432 A f b x s q'.
Proof. exact (@lem6943275 A x s f b (term370 A f b x s) q'). Qed.
Lemma lem6943359 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (q' : Prop) : term433 A f b x s q'.
Proof. exact (@lem6943358 A f b x s q' (@lem6943357 A f b x s)). Qed.
Lemma lem6943360 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : term370 A f b x s.
Proof. exact (h1). Qed.
Lemma lem6943361 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : term368 A x s.
Proof. exact (proj2 (@lem6943360 A f b x s h1)). Qed.
Lemma lem6943362 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : @FINITE A s.
Proof. exact (proj2 (@lem6943361 A f b x s h1)). Qed.
Lemma lem6943363 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6943365 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : term434 A x s.
Proof. exact (proj1 (@lem6943361 A f b x s h1)). Qed.
Lemma lem6943366 {A : Type'} (x : A) (s : A -> Prop) : term435 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem6943391 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term394 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6943392 (p : Prop) (q : Prop) (p' : Prop) : term395 p q p'.
Proof. exact (fun q' : Prop => @lem6943391 p q p' q'). Qed.
Lemma lem6943393 (p : Prop) (q : Prop) : term396 p q.
Proof. exact (fun p' : Prop => @lem6943392 p q p'). Qed.
Lemma lem6943394 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : term436 A x s f b.
Proof. exact (@lem6943393 (term437 A x s f b) (term438 A x s f b)). Qed.
Lemma lem6943395 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : term439 A x s f b p'.
Proof. exact (@lem6943394 A x s f b p'). Qed.
Lemma lem6943396 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : (term439 A x s f b p') = (term440 A x s f b p').
Proof. exact (eq_refl (term439 A x s f b p')). Qed.
Lemma lem6943397 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : term440 A x s f b p'.
Proof. exact (EQ_MP (@lem6943396 A x s f b p') (@lem6943395 A x s f b p')). Qed.
Lemma lem6943398 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : term441 A x s f b p' q'.
Proof. exact (@lem6943397 A x s f b p' q'). Qed.
Lemma lem6943399 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : (term441 A x s f b p' q') = (term442 A x s f b p' q').
Proof. exact (eq_refl (term441 A x s f b p' q')). Qed.
Lemma lem6943400 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : term442 A x s f b p' q'.
Proof. exact (EQ_MP (@lem6943399 A x s f b p' q') (@lem6943398 A x s f b p' q')). Qed.
Lemma lem6943402 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term336 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem6943094 _126525 x f s h0). Qed.
Lemma lem6943403 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : term336 A x s f.
Proof. exact (@lem6943402 A x s f). Qed.
Lemma lem6943405 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6943363 A s) (@lem6943362 A f b x s h1)). Qed.
Lemma lem6943406 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : True = (@FINITE A s).
Proof. exact (SYM (@lem6943405 A f b x s h1)). Qed.
Lemma lem6943407 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : @FINITE A s.
Proof. exact (EQ_MP (@lem6943406 A f b x s h1) (@lem0)). Qed.
Lemma lem6943408 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : (term337 A x s f) = (term338 A x s f).
Proof. exact (@lem6943403 A x s f (@lem6943407 A f b x s h1)). Qed.
Lemma lem6943410 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term443 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6943411 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term444 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6943410 _2963 g t e g' t' e'). Qed.
Lemma lem6943412 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term445 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6943411 _2963 g t e g' t'). Qed.
Lemma lem6943413 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term446 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6943412 _2963 g t e g'). Qed.
Lemma lem6943414 (g : Prop) (t : nat) (e : nat) : term447 g t e.
Proof. exact (@lem6943413 nat g t e). Qed.
Lemma lem6943415 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : term448 A x s f.
Proof. exact (@lem6943414 (@IN A x s) (@nsum A s f) (term449 A x s f)). Qed.
Lemma lem6943416 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) : term450 A x s f g'.
Proof. exact (@lem6943415 A x s f g'). Qed.
Lemma lem6943417 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) : (term450 A x s f g') = (term451 A x s f g').
Proof. exact (eq_refl (term450 A x s f g')). Qed.
Lemma lem6943418 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) : term451 A x s f g'.
Proof. exact (EQ_MP (@lem6943417 A x s f g') (@lem6943416 A x s f g')). Qed.
Lemma lem6943419 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) : term452 A x s f g' t'.
Proof. exact (@lem6943418 A x s f g' t'). Qed.
Lemma lem6943420 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) : (term452 A x s f g' t') = (term453 A x s f g' t').
Proof. exact (eq_refl (term452 A x s f g' t')). Qed.
Lemma lem6943421 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) : term453 A x s f g' t'.
Proof. exact (EQ_MP (@lem6943420 A x s f g' t') (@lem6943419 A x s f g' t')). Qed.
Lemma lem6943422 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : term454 A x s f g' t' e'.
Proof. exact (@lem6943421 A x s f g' t' e'). Qed.
Lemma lem6943423 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : (term454 A x s f g' t' e') = (term455 A x s f g' t' e').
Proof. exact (eq_refl (term454 A x s f g' t' e')). Qed.
Lemma lem6943424 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : term455 A x s f g' t' e'.
Proof. exact (EQ_MP (@lem6943423 A x s f g' t' e') (@lem6943422 A x s f g' t' e')). Qed.
Lemma lem6943426 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : (@IN A x s) = False.
Proof. exact (@lem6943366 A x s (@lem6943365 A f b x s h1)). Qed.
Lemma lem6943427 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (t' : nat) (e' : nat) : term456 A x s f t' e'.
Proof. exact (@lem6943424 A x s f False t' e'). Qed.
Lemma lem6943428 {A : Type'} (t' : nat) (e' : nat) (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : term457 A x s f t' e'.
Proof. exact (@lem6943427 A x s f t' e' (@lem6943426 A f b x s h1)). Qed.
Lemma lem6943432 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@nsum A s f).
Proof. exact (eq_refl (@nsum A s f)). Qed.
Lemma lem6943433 {A : Type'} (s : A -> Prop) (f : A -> nat) : term458 A s f.
Proof. exact (fun h0 : False => @lem6943432 A s f). Qed.
Lemma lem6943434 {A : Type'} (e' : nat) (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : term459 A x s f e'.
Proof. exact (@lem6943428 A (@nsum A s f) e' f b x s h1). Qed.
Lemma lem6943435 {A : Type'} (e' : nat) (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : term460 A x s f e'.
Proof. exact (@lem6943434 A e' f b x s h1 (@lem6943433 A s f)). Qed.
Lemma lem6943441 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : (term449 A x s f) = (term449 A x s f).
Proof. exact (eq_refl (term449 A x s f)). Qed.
Lemma lem6943442 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : term461 A x s f.
Proof. exact (fun h0 : ~ False => @lem6943441 A x s f). Qed.
Lemma lem6943443 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : term462 A x s f.
Proof. exact (@lem6943435 A (term449 A x s f) f b x s h1). Qed.
Lemma lem6943444 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : (term338 A x s f) = (term463 A x s f).
Proof. exact (@lem6943443 A f b x s h1 (@lem6943442 A x s f)). Qed.
Lemma lem6943446 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6943447 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem6943446 nat t1 t2). Qed.
Lemma lem6943448 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : (term463 A x s f) = (term449 A x s f).
Proof. exact (@lem6943447 (@nsum A s f) (term449 A x s f)). Qed.
Lemma lem6943449 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : (term338 A x s f) = (term449 A x s f).
Proof. exact (TRANS (@lem6943444 A f b x s h1) (@lem6943448 A x s f)). Qed.
Lemma lem6943450 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : (term337 A x s f) = (term449 A x s f).
Proof. exact (TRANS (@lem6943408 A f b x s h1) (@lem6943449 A f b x s h1)). Qed.
Lemma lem6943451 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6943452 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : (term464 A x s f) = (term465 A x s f).
Proof. exact (MK_COMB (@lem6943451) (@lem6943450 A f b x s h1)). Qed.
Lemma lem6943453 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6943454 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : (term437 A x s f b) = (term466 A x s f b).
Proof. exact (MK_COMB (@lem6943452 A f b x s h1) (@lem6943453 b)). Qed.
Lemma lem6943455 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (q' : Prop) : term467 A x s f b q'.
Proof. exact (@lem6943400 A x s f b (term466 A x s f b) q'). Qed.
Lemma lem6943456 {A : Type'} (q' : Prop) (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : term468 A x s f b q'.
Proof. exact (@lem6943455 A x s f b q' (@lem6943454 A f b x s h1)). Qed.
Lemma lem6943467 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term394 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6943468 (p : Prop) (q : Prop) (p' : Prop) : term395 p q p'.
Proof. exact (fun q' : Prop => @lem6943467 p q p' q'). Qed.
Lemma lem6943469 (p : Prop) (q : Prop) : term396 p q.
Proof. exact (fun p' : Prop => @lem6943468 p q p'). Qed.
Lemma lem6943470 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : term469 A x s f x' b.
Proof. exact (@lem6943469 (term325 A x' x s) (term409 A f x' b)). Qed.
Lemma lem6943471 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (p' : Prop) : term470 A x s f x' b p'.
Proof. exact (@lem6943470 A x s f x' b p'). Qed.
Lemma lem6943472 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (p' : Prop) : (term470 A x s f x' b p') = (term471 A x s f x' b p').
Proof. exact (eq_refl (term470 A x s f x' b p')). Qed.
Lemma lem6943473 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (p' : Prop) : term471 A x s f x' b p'.
Proof. exact (EQ_MP (@lem6943472 A x s f x' b p') (@lem6943471 A x s f x' b p')). Qed.
Lemma lem6943474 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (p' : Prop) (q' : Prop) : term472 A x s f x' b p' q'.
Proof. exact (@lem6943473 A x s f x' b p' q'). Qed.
Lemma lem6943475 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (p' : Prop) (q' : Prop) : (term472 A x s f x' b p' q') = (term473 A x s f x' b p' q').
Proof. exact (eq_refl (term472 A x s f x' b p' q')). Qed.
Lemma lem6943476 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (p' : Prop) (q' : Prop) : term473 A x s f x' b p' q'.
Proof. exact (EQ_MP (@lem6943475 A x s f x' b p' q') (@lem6943474 A x s f x' b p' q')). Qed.
Lemma lem6943478 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term325 A x y s) = (term326 A y x s).
Proof. exact (EQ_MP (@lem6943076 A y x s) (@lem6943075 A y x s)). Qed.
Lemma lem6943479 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term325 A x y s) = (term326 A y x s).
Proof. exact (@lem6943478 A y x s). Qed.
Lemma lem6943480 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term325 A x' x s) = (term326 A x x' s).
Proof. exact (@lem6943479 A x x' s). Qed.
Lemma lem6943485 {A : Type'} (f : A -> nat) (b : nat) (x : A) (x' : A) (s : A -> Prop) (q' : Prop) : term474 A f b x x' s q'.
Proof. exact (@lem6943476 A x s f x' b (term326 A x x' s) q'). Qed.
Lemma lem6943486 {A : Type'} (f : A -> nat) (b : nat) (x : A) (x' : A) (s : A -> Prop) (q' : Prop) : term475 A f b x x' s q'.
Proof. exact (@lem6943485 A f b x x' s q' (@lem6943480 A x x' s)). Qed.
Lemma lem6943497 {A : Type'} (f : A -> nat) (x' : A) (b : nat) : (term409 A f x' b) = (term409 A f x' b).
Proof. exact (eq_refl (term409 A f x' b)). Qed.
Lemma lem6943498 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : term476 A x s f x' b.
Proof. exact (fun h0 : term326 A x x' s => @lem6943497 A f x' b). Qed.
Lemma lem6943499 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : term477 A x s f x' b.
Proof. exact (@lem6943486 A f b x x' s (term409 A f x' b)). Qed.
Lemma lem6943500 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term478 A x s f x' b) = (term479 A x s f x' b).
Proof. exact (@lem6943499 A x s f x' b (@lem6943498 A x s f x' b)). Qed.
Lemma lem6943546 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term480 A x s f b) = (term481 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem6943500 A x s f x' b)). Qed.
Lemma lem6943592 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6943593 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term438 A x s f b) = (term482 A x s f b).
Proof. exact (MK_COMB (@lem6943592 A) (@lem6943546 A x s f b)). Qed.
Lemma lem6943643 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : term483 A x s f b.
Proof. exact (fun h0 : term466 A x s f b => @lem6943593 A x s f b). Qed.
Lemma lem6943644 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : term484 A x s f b.
Proof. exact (@lem6943456 A (term482 A x s f b) f b x s h1). Qed.
Lemma lem6943645 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term370 A f b x s) : (term374 A x s f b) = (term485 A x s f b).
Proof. exact (@lem6943644 A f b x s h1 (@lem6943643 A x s f b)). Qed.
Lemma lem6943767 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : term486 A x s f b.
Proof. exact (fun h0 : term370 A f b x s => @lem6943645 A f b x s h0). Qed.
Lemma lem6943768 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : term487 A x s f b.
Proof. exact (@lem6943359 A f b x s (term485 A x s f b)). Qed.
Lemma lem6943769 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term376 A x s f b) = (term488 A x s f b).
Proof. exact (@lem6943768 A x s f b (@lem6943767 A x s f b)). Qed.
Lemma lem6944194 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term378 A x f b) = (term489 A x f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6943769 A x s f b)). Qed.
Lemma lem6944619 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6944620 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term380 A x f b) = (term490 A x f b).
Proof. exact (MK_COMB (@lem6944619 A) (@lem6944194 A x f b)). Qed.
Lemma lem6945049 {A : Type'} (f : A -> nat) (b : nat) : (term382 A f b) = (term491 A f b).
Proof. exact (fun_ext (fun x : A => @lem6944620 A x f b)). Qed.
Lemma lem6945478 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6945479 {A : Type'} (f : A -> nat) (b : nat) : (term384 A f b) = (term492 A f b).
Proof. exact (MK_COMB (@lem6945478 A) (@lem6945049 A f b)). Qed.
Lemma lem6945912 {A : Type'} (f : A -> nat) (b : nat) : (term386 A f b) = (term493 A f b).
Proof. exact (MK_COMB (@lem6943254 A f b) (@lem6945479 A f b)). Qed.
Lemma lem6945914 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6945915 {A : Type'} (f : A -> nat) (b : nat) : (term493 A f b) = (term492 A f b).
Proof. exact (@lem6945914 (term492 A f b)). Qed.
Lemma lem6946348 {A : Type'} (f : A -> nat) (b : nat) : (term386 A f b) = (term492 A f b).
Proof. exact (TRANS (@lem6945912 A f b) (@lem6945915 A f b)). Qed.
Lemma lem6946349 {A : Type'} (f : A -> nat) (b : nat) : (term492 A f b) = (term386 A f b).
Proof. exact (SYM (@lem6946348 A f b)). Qed.
Lemma lem6946351 (p : Prop) : p = (term494 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6946352 {A : Type'} (f : A -> nat) (b : nat) : (term492 A f b) = (term495 A f b).
Proof. exact (@lem6946351 (term492 A f b)). Qed.
Lemma lem6946353 {A : Type'} (f : A -> nat) (b : nat) : (term495 A f b) = (term492 A f b).
Proof. exact (SYM (@lem6946352 A f b)). Qed.
Lemma lem6946354 {A : Type'} (f : A -> nat) (b : nat) (h1 : term496 A f b) : term496 A f b.
Proof. exact (h1). Qed.
Lemma lem6946357 {A : Type'} (f : A -> nat) (b : nat) (h1 : term497 A f b) : term497 A f b.
Proof. exact (h1). Qed.
Lemma lem6946358 {A : Type'} (f : A -> nat) (b : nat) : term498 A f b.
Proof. exact (fun h0 : term497 A f b => @lem6946357 A f b h0). Qed.
Lemma lem6946359 {A : Type'} (f : A -> nat) (b : nat) (h1 : term498 A f b) : term498 A f b.
Proof. exact (h1). Qed.
Lemma lem6946360 {A : Type'} (f : A -> nat) (b : nat) (h1 : term497 A f b) : term497 A f b.
Proof. exact (h1). Qed.
Lemma lem6946361 {A : Type'} (f : A -> nat) (b : nat) (h1 : term497 A f b) (h2 : term498 A f b) : term497 A f b.
Proof. exact (@lem6946359 A f b h2 (@lem6946360 A f b h1)). Qed.
Lemma lem6946362 {A : Type'} (f : A -> nat) (b : nat) (h1 : term497 A f b) : term499 A f b.
Proof. exact (fun h0 : term498 A f b => @lem6946361 A f b h1 h0). Qed.
Lemma lem6946363 {A : Type'} (f : A -> nat) (b : nat) (h1 : term498 A f b) : term498 A f b.
Proof. exact (h1). Qed.
Lemma lem6946364 {A : Type'} (f : A -> nat) (b : nat) (h1 : term497 A f b) (h2 : term498 A f b) : term497 A f b.
Proof. exact (@lem6946362 A f b h1 (@lem6946363 A f b h2)). Qed.
Lemma lem6946365 {A : Type'} (f : A -> nat) (b : nat) (h1 : term498 A f b) : term498 A f b.
Proof. exact (fun h0 : term497 A f b => @lem6946364 A f b h0 h1). Qed.
Lemma lem6946366 {A : Type'} (f : A -> nat) (b : nat) : term500 A f b.
Proof. exact (fun h0 : term498 A f b => @lem6946365 A f b h0). Qed.
Lemma lem6946369 {A : Type'} (f : A -> nat) (b : nat) : term498 A f b.
Proof. exact (@lem6946366 A f b (@lem6946358 A f b)). Qed.
Lemma lem6946370 {A : Type'} (f : A -> nat) (b : nat) : term498 A f b.
Proof. exact (@lem6946369 A f b). Qed.
Lemma lem6946436 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6946437 : term501 = term502.
Proof. exact (@lem6946436 term503). Qed.
Lemma lem6946442 : term504 = term504.
Proof. exact (eq_refl term504). Qed.
Lemma lem6946443 : term505 = term506.
Proof. exact (MK_COMB (@lem6946442) (@lem6946437)). Qed.
Lemma lem6946446 {A : Type'} (f : A -> nat) (b : nat) : (term507 A f b) = (term507 A f b).
Proof. exact (eq_refl (term507 A f b)). Qed.
Lemma lem6946447 {A : Type'} (f : A -> nat) (b : nat) : (term497 A f b) = (term508 A f b).
Proof. exact (MK_COMB (@lem6946446 A f b) (@lem6946443)). Qed.
Lemma lem6946450 {A : Type'} (b : nat) : (term509 A b) = (term510 A b).
Proof. exact (fun_ext (fun f : A -> nat => @lem6946447 A f b)). Qed.
Lemma lem6946451 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6946452 {A : Type'} (b : nat) : (term511 A b) = (term512 A b).
Proof. exact (MK_COMB (@lem6946451 A) (@lem6946450 A b)). Qed.
Lemma lem6946457 {A : Type'} : (term513 A) = (term514 A).
Proof. exact (fun_ext (fun b : nat => @lem6946452 A b)). Qed.
Lemma lem6946458 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6946467 {A : Type'} : (term515 A) = (term516 A).
Proof. exact (MK_COMB (@lem6946458) (@lem6946457 A)). Qed.
Lemma lem6946468 (n : nat) : (term2 n) = (term2 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem6946469 : term517 = term517.
Proof. exact (fun_ext (fun n : nat => @lem6946468 n)). Qed.
Lemma lem6946470 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6946471 : term503 = term503.
Proof. exact (MK_COMB (@lem6946470) (@lem6946469)). Qed.
Lemma lem6946472 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6946473 : term502 = term502.
Proof. exact (MK_COMB (@lem6946472) (@lem6946471)). Qed.
Lemma lem6946490 (x : nat) (y : nat) (b : nat) : (term14 x y b) = (term14 x y b).
Proof. exact (eq_refl (term14 x y b)). Qed.
Lemma lem6946491 (x : nat) (y : nat) : (term518 x y) = (term518 x y).
Proof. exact (fun_ext (fun b : nat => @lem6946490 x y b)). Qed.
Lemma lem6946492 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6946493 (x : nat) (y : nat) : (term317 x y) = (term317 x y).
Proof. exact (MK_COMB (@lem6946492) (@lem6946491 x y)). Qed.
Lemma lem6946494 (x : nat) : (term519 x) = (term519 x).
Proof. exact (fun_ext (fun y : nat => @lem6946493 x y)). Qed.
Lemma lem6946495 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6946496 (x : nat) : (term318 x) = (term318 x).
Proof. exact (MK_COMB (@lem6946495) (@lem6946494 x)). Qed.
Lemma lem6946497 : term520 = term520.
Proof. exact (fun_ext (fun x : nat => @lem6946496 x)). Qed.
Lemma lem6946498 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6946499 : term319 = term319.
Proof. exact (MK_COMB (@lem6946498) (@lem6946497)). Qed.
Lemma lem6946500 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6946501 : term504 = term504.
Proof. exact (MK_COMB (@lem6946500) (@lem6946499)). Qed.
Lemma lem6946502 : term506 = term506.
Proof. exact (MK_COMB (@lem6946501) (@lem6946473)). Qed.
Lemma lem6946511 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term479 A x s f x' b) = (term479 A x s f x' b).
Proof. exact (eq_refl (term479 A x s f x' b)). Qed.
Lemma lem6946512 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term481 A x s f b) = (term481 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem6946511 A x s f x' b)). Qed.
Lemma lem6946513 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6946514 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term482 A x s f b) = (term482 A x s f b).
Proof. exact (MK_COMB (@lem6946513 A) (@lem6946512 A x s f b)). Qed.
Lemma lem6946517 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term521 A x s f b) = (term521 A x s f b).
Proof. exact (eq_refl (term521 A x s f b)). Qed.
Lemma lem6946518 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term485 A x s f b) = (term485 A x s f b).
Proof. exact (MK_COMB (@lem6946517 A x s f b) (@lem6946514 A x s f b)). Qed.
Lemma lem6946525 {A : Type'} (x : A) (s : A -> Prop) : (term368 A x s) = (term368 A x s).
Proof. exact (eq_refl (term368 A x s)). Qed.
Lemma lem6946530 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term522 A s f x b) = (term522 A s f x b).
Proof. exact (eq_refl (term522 A s f x b)). Qed.
Lemma lem6946531 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term523 A s f b) = (term523 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6946530 A s f x b)). Qed.
Lemma lem6946532 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6946533 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term353 A s f b) = (term353 A s f b).
Proof. exact (MK_COMB (@lem6946532 A) (@lem6946531 A s f b)). Qed.
Lemma lem6946536 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term524 A s f b) = (term524 A s f b).
Proof. exact (eq_refl (term524 A s f b)). Qed.
Lemma lem6946537 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term365 A s f b) = (term365 A s f b).
Proof. exact (MK_COMB (@lem6946536 A s f b) (@lem6946533 A s f b)). Qed.
Lemma lem6946538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6946539 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term367 A s f b) = (term367 A s f b).
Proof. exact (MK_COMB (@lem6946538) (@lem6946537 A s f b)). Qed.
Lemma lem6946540 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) : (term370 A f b x s) = (term370 A f b x s).
Proof. exact (MK_COMB (@lem6946539 A s f b) (@lem6946525 A x s)). Qed.
Lemma lem6946541 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6946542 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) : (term372 A f b x s) = (term372 A f b x s).
Proof. exact (MK_COMB (@lem6946541) (@lem6946540 A f b x s)). Qed.
Lemma lem6946543 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term488 A x s f b) = (term488 A x s f b).
Proof. exact (MK_COMB (@lem6946542 A f b x s) (@lem6946518 A x s f b)). Qed.
Lemma lem6946544 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term489 A x f b) = (term489 A x f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6946543 A x s f b)). Qed.
Lemma lem6946545 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6946546 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term490 A x f b) = (term490 A x f b).
Proof. exact (MK_COMB (@lem6946545 A) (@lem6946544 A x f b)). Qed.
Lemma lem6946547 {A : Type'} (f : A -> nat) (b : nat) : (term491 A f b) = (term491 A f b).
Proof. exact (fun_ext (fun x : A => @lem6946546 A x f b)). Qed.
Lemma lem6946548 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6946549 {A : Type'} (f : A -> nat) (b : nat) : (term492 A f b) = (term492 A f b).
Proof. exact (MK_COMB (@lem6946548 A) (@lem6946547 A f b)). Qed.
Lemma lem6946550 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6946551 {A : Type'} (f : A -> nat) (b : nat) : (term496 A f b) = (term496 A f b).
Proof. exact (MK_COMB (@lem6946550) (@lem6946549 A f b)). Qed.
Lemma lem6946552 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6946553 {A : Type'} (f : A -> nat) (b : nat) : (term507 A f b) = (term507 A f b).
Proof. exact (MK_COMB (@lem6946552) (@lem6946551 A f b)). Qed.
Lemma lem6946554 {A : Type'} (f : A -> nat) (b : nat) : (term508 A f b) = (term508 A f b).
Proof. exact (MK_COMB (@lem6946553 A f b) (@lem6946502)). Qed.
Lemma lem6946555 {A : Type'} (b : nat) : (term510 A b) = (term510 A b).
Proof. exact (fun_ext (fun f : A -> nat => @lem6946554 A f b)). Qed.
Lemma lem6946556 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6946557 {A : Type'} (b : nat) : (term512 A b) = (term512 A b).
Proof. exact (MK_COMB (@lem6946556 A) (@lem6946555 A b)). Qed.
Lemma lem6946558 {A : Type'} : (term514 A) = (term514 A).
Proof. exact (fun_ext (fun b : nat => @lem6946557 A b)). Qed.
Lemma lem6946559 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6946560 {A : Type'} : (term516 A) = (term516 A).
Proof. exact (MK_COMB (@lem6946559) (@lem6946558 A)). Qed.
Lemma lem6946651 {A : Type'} : (term515 A) = (term516 A).
Proof. exact (TRANS (@lem6946467 A) (@lem6946560 A)). Qed.
Lemma lem6946652 {A : Type'} : (term516 A) = (term515 A).
Proof. exact (SYM (@lem6946651 A)). Qed.
Lemma lem6946653 {A : Type'} (f : A -> nat) (b : nat) (h1 : term496 A f b) : term496 A f b.
Proof. exact (h1). Qed.
Lemma lem6946654 (h1 : term319) : term319.
Proof. exact (h1). Qed.
Lemma lem6946655 (h1 : term503) : term503.
Proof. exact (h1). Qed.
Lemma lem6946663 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term522 A s f x b) = (term525 A s f x b).
Proof. exact (@lem17265 (@IN A x s) (term409 A f x b)). Qed.
Lemma lem6946664 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term523 A s f b) = (term526 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6946663 A s f x b)). Qed.
Lemma lem6946665 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6946666 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term353 A s f b) = (term527 A s f b).
Proof. exact (MK_COMB (@lem6946665 A) (@lem6946664 A s f b)). Qed.
Lemma lem6946668 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term528 A s f b) = (term528 A s f b).
Proof. exact (eq_refl (term528 A s f b)). Qed.
Lemma lem6946669 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term529 A s f b) = (term530 A s f b).
Proof. exact (MK_COMB (@lem6946668 A s f b) (@lem6946666 A s f b)). Qed.
Lemma lem6946670 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term365 A s f b) = (term529 A s f b).
Proof. exact (@lem17265 (term352 A s f b) (term353 A s f b)). Qed.
Lemma lem6946671 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term365 A s f b) = (term530 A s f b).
Proof. exact (TRANS (@lem6946670 A s f b) (@lem6946669 A s f b)). Qed.
Lemma lem6946676 {A : Type'} (x : A) (s : A -> Prop) : (term368 A x s) = (term368 A x s).
Proof. exact (eq_refl (term368 A x s)). Qed.
Lemma lem6946677 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6946678 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term367 A s f b) = (term531 A s f b).
Proof. exact (MK_COMB (@lem6946677) (@lem6946671 A s f b)). Qed.
Lemma lem6946679 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) : (term370 A f b x s) = (term532 A f b x s).
Proof. exact (MK_COMB (@lem6946678 A s f b) (@lem6946676 A x s)). Qed.
Lemma lem6946691 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term533 A x s f x' b) = (term534 A x s f x' b).
Proof. exact (@lem17362 (term326 A x x' s) (term409 A f x' b)). Qed.
Lemma lem6946692 {A : Type'} (P : A -> Prop) : (term535 A P) = (term536 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6946693 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term537 A x s f b) = (term538 A x s f b).
Proof. exact (@lem6946692 A (term481 A x s f b)). Qed.
Lemma lem6946694 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term539 A x s f b x') = (term479 A x s f x' b).
Proof. exact (eq_refl (term539 A x s f b x')). Qed.
Lemma lem6946695 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6946696 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term540 A x s f b x') = (term533 A x s f x' b).
Proof. exact (MK_COMB (@lem6946695) (@lem6946694 A x s f x' b)). Qed.
Lemma lem6946697 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term540 A x s f b x') = (term534 A x s f x' b).
Proof. exact (TRANS (@lem6946696 A x s f x' b) (@lem6946691 A x s f x' b)). Qed.
Lemma lem6946698 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term541 A x s f b) = (term542 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem6946697 A x s f x' b)). Qed.
Lemma lem6946699 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6946700 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term538 A x s f b) = (term543 A x s f b).
Proof. exact (MK_COMB (@lem6946699 A) (@lem6946698 A x s f b)). Qed.
Lemma lem6946701 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term537 A x s f b) = (term543 A x s f b).
Proof. exact (TRANS (@lem6946693 A x s f b) (@lem6946700 A x s f b)). Qed.
Lemma lem6946703 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term544 A x s f b) = (term544 A x s f b).
Proof. exact (eq_refl (term544 A x s f b)). Qed.
Lemma lem6946704 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term545 A x s f b) = (term546 A x s f b).
Proof. exact (MK_COMB (@lem6946703 A x s f b) (@lem6946701 A x s f b)). Qed.
Lemma lem6946705 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term547 A x s f b) = (term545 A x s f b).
Proof. exact (@lem17362 (term466 A x s f b) (term482 A x s f b)). Qed.
Lemma lem6946706 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term547 A x s f b) = (term546 A x s f b).
Proof. exact (TRANS (@lem6946705 A x s f b) (@lem6946704 A x s f b)). Qed.
Lemma lem6946707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6946708 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) : (term548 A f b x s) = (term549 A f b x s).
Proof. exact (MK_COMB (@lem6946707) (@lem6946679 A f b x s)). Qed.
Lemma lem6946709 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term550 A x s f b) = (term551 A x s f b).
Proof. exact (MK_COMB (@lem6946708 A f b x s) (@lem6946706 A x s f b)). Qed.
Lemma lem6946710 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term552 A x s f b) = (term550 A x s f b).
Proof. exact (@lem17362 (term370 A f b x s) (term485 A x s f b)). Qed.
Lemma lem6946711 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term552 A x s f b) = (term551 A x s f b).
Proof. exact (TRANS (@lem6946710 A x s f b) (@lem6946709 A x s f b)). Qed.
Lemma lem6946712 {A : Type'} (P : type686 A) : (term553 A P) = (term554 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem6946713 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term555 A x f b) = (term556 A x f b).
Proof. exact (@lem6946712 A (term489 A x f b)). Qed.
Lemma lem6946714 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term557 A x f b s) = (term488 A x s f b).
Proof. exact (eq_refl (term557 A x f b s)). Qed.
Lemma lem6946715 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6946716 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term558 A x f b s) = (term552 A x s f b).
Proof. exact (MK_COMB (@lem6946715) (@lem6946714 A x s f b)). Qed.
Lemma lem6946717 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term558 A x f b s) = (term551 A x s f b).
Proof. exact (TRANS (@lem6946716 A x s f b) (@lem6946711 A x s f b)). Qed.
Lemma lem6946718 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term559 A x f b) = (term560 A x f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6946717 A x s f b)). Qed.
Lemma lem6946719 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem6946720 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term556 A x f b) = (term561 A x f b).
Proof. exact (MK_COMB (@lem6946719 A) (@lem6946718 A x f b)). Qed.
Lemma lem6946721 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term555 A x f b) = (term561 A x f b).
Proof. exact (TRANS (@lem6946713 A x f b) (@lem6946720 A x f b)). Qed.
Lemma lem6946722 {A : Type'} (P : A -> Prop) : (term535 A P) = (term536 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6946723 {A : Type'} (f : A -> nat) (b : nat) : (term496 A f b) = (term562 A f b).
Proof. exact (@lem6946722 A (term491 A f b)). Qed.
Lemma lem6946724 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term563 A f b x) = (term490 A x f b).
Proof. exact (eq_refl (term563 A f b x)). Qed.
Lemma lem6946725 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6946726 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term564 A f b x) = (term555 A x f b).
Proof. exact (MK_COMB (@lem6946725) (@lem6946724 A x f b)). Qed.
Lemma lem6946727 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term564 A f b x) = (term561 A x f b).
Proof. exact (TRANS (@lem6946726 A x f b) (@lem6946721 A x f b)). Qed.
Lemma lem6946728 {A : Type'} (f : A -> nat) (b : nat) : (term565 A f b) = (term566 A f b).
Proof. exact (fun_ext (fun x : A => @lem6946727 A x f b)). Qed.
Lemma lem6946729 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6946730 {A : Type'} (f : A -> nat) (b : nat) : (term562 A f b) = (term567 A f b).
Proof. exact (MK_COMB (@lem6946729 A) (@lem6946728 A f b)). Qed.
Lemma lem6946731 {A : Type'} (f : A -> nat) (b : nat) : (term496 A f b) = (term567 A f b).
Proof. exact (TRANS (@lem6946723 A f b) (@lem6946730 A f b)). Qed.
Lemma lem6946882 {A : Type'} (P : Prop) (Q : A -> Prop) : (term568 A P Q) = (term569 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem6946883 {A : Type'} (P : Prop) (Q : A -> Prop) : (term568 A P Q) = (term569 A P Q).
Proof. exact (@lem6946882 A P Q). Qed.
Lemma lem6946884 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term570 A x s f b) = (term571 A x s f b).
Proof. exact (@lem6946883 A (term466 A x s f b) (term542 A x s f b)). Qed.
Lemma lem6946885 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term572 A x s f b x') = (term534 A x s f x' b).
Proof. exact (eq_refl (term572 A x s f b x')). Qed.
Lemma lem6946886 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term573 A x s f b) = (term542 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem6946885 A x s f x' b)). Qed.
Lemma lem6946887 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6946888 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term574 A x s f b) = (term543 A x s f b).
Proof. exact (MK_COMB (@lem6946887 A) (@lem6946886 A x s f b)). Qed.
Lemma lem6946889 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term544 A x s f b) = (term544 A x s f b).
Proof. exact (eq_refl (term544 A x s f b)). Qed.
Lemma lem6946890 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term570 A x s f b) = (term546 A x s f b).
Proof. exact (MK_COMB (@lem6946889 A x s f b) (@lem6946888 A x s f b)). Qed.
Lemma lem6946891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6946892 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term575 A x s f b) = (term576 A x s f b).
Proof. exact (MK_COMB (@lem6946891) (@lem6946890 A x s f b)). Qed.
Lemma lem6946893 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term572 A x s f b x') = (term534 A x s f x' b).
Proof. exact (eq_refl (term572 A x s f b x')). Qed.
Lemma lem6946894 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term544 A x s f b) = (term544 A x s f b).
Proof. exact (eq_refl (term544 A x s f b)). Qed.
Lemma lem6946895 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term577 A x s f b x') = (term578 A x s f x' b).
Proof. exact (MK_COMB (@lem6946894 A x s f b) (@lem6946893 A x s f x' b)). Qed.
Lemma lem6946896 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term579 A x s f b) = (term580 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem6946895 A x s f x' b)). Qed.
Lemma lem6946897 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6946898 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term571 A x s f b) = (term581 A x s f b).
Proof. exact (MK_COMB (@lem6946897 A) (@lem6946896 A x s f b)). Qed.
Lemma lem6946899 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : ((term570 A x s f b) = (term571 A x s f b)) = ((term546 A x s f b) = (term581 A x s f b)).
Proof. exact (MK_COMB (@lem6946892 A x s f b) (@lem6946898 A x s f b)). Qed.
Lemma lem6946900 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term546 A x s f b) = (term581 A x s f b).
Proof. exact (EQ_MP (@lem6946899 A x s f b) (@lem6946884 A x s f b)). Qed.
Lemma lem6946901 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) : (term549 A f b x s) = (term549 A f b x s).
Proof. exact (eq_refl (term549 A f b x s)). Qed.
Lemma lem6946902 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term551 A x s f b) = (term582 A x s f b).
Proof. exact (MK_COMB (@lem6946901 A f b x s) (@lem6946900 A x s f b)). Qed.
Lemma lem6946904 {A : Type'} (P : Prop) (Q : A -> Prop) : (term568 A P Q) = (term569 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem6946905 {A : Type'} (P : Prop) (Q : A -> Prop) : (term568 A P Q) = (term569 A P Q).
Proof. exact (@lem6946904 A P Q). Qed.
Lemma lem6946906 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term583 A x s f b) = (term584 A x s f b).
Proof. exact (@lem6946905 A (term532 A f b x s) (term580 A x s f b)). Qed.
Lemma lem6946907 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term585 A x s f b x') = (term578 A x s f x' b).
Proof. exact (eq_refl (term585 A x s f b x')). Qed.
Lemma lem6946908 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term586 A x s f b) = (term580 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem6946907 A x s f x' b)). Qed.
Lemma lem6946909 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6946910 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term587 A x s f b) = (term581 A x s f b).
Proof. exact (MK_COMB (@lem6946909 A) (@lem6946908 A x s f b)). Qed.
Lemma lem6946911 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) : (term549 A f b x s) = (term549 A f b x s).
Proof. exact (eq_refl (term549 A f b x s)). Qed.
Lemma lem6946912 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term583 A x s f b) = (term582 A x s f b).
Proof. exact (MK_COMB (@lem6946911 A f b x s) (@lem6946910 A x s f b)). Qed.
Lemma lem6946913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6946914 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term588 A x s f b) = (term589 A x s f b).
Proof. exact (MK_COMB (@lem6946913) (@lem6946912 A x s f b)). Qed.
Lemma lem6946915 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term585 A x s f b x') = (term578 A x s f x' b).
Proof. exact (eq_refl (term585 A x s f b x')). Qed.
Lemma lem6946916 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) : (term549 A f b x s) = (term549 A f b x s).
Proof. exact (eq_refl (term549 A f b x s)). Qed.
Lemma lem6946917 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term590 A x s f b x') = (term591 A x s f x' b).
Proof. exact (MK_COMB (@lem6946916 A f b x s) (@lem6946915 A x s f x' b)). Qed.
Lemma lem6946918 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term592 A x s f b) = (term593 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem6946917 A x s f x' b)). Qed.
Lemma lem6946919 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6946920 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term584 A x s f b) = (term594 A x s f b).
Proof. exact (MK_COMB (@lem6946919 A) (@lem6946918 A x s f b)). Qed.
Lemma lem6946921 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : ((term583 A x s f b) = (term584 A x s f b)) = ((term582 A x s f b) = (term594 A x s f b)).
Proof. exact (MK_COMB (@lem6946914 A x s f b) (@lem6946920 A x s f b)). Qed.
Lemma lem6946922 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term582 A x s f b) = (term594 A x s f b).
Proof. exact (EQ_MP (@lem6946921 A x s f b) (@lem6946906 A x s f b)). Qed.
Lemma lem6946923 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term551 A x s f b) = (term594 A x s f b).
Proof. exact (TRANS (@lem6946902 A x s f b) (@lem6946922 A x s f b)). Qed.
Lemma lem6946924 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term560 A x f b) = (term595 A x f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6946923 A x s f b)). Qed.
Lemma lem6946925 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem6946926 {A : Type'} (x : A) (f : A -> nat) (b : nat) : (term561 A x f b) = (term596 A x f b).
Proof. exact (MK_COMB (@lem6946925 A) (@lem6946924 A x f b)). Qed.
Lemma lem6946927 {A : Type'} (f : A -> nat) (b : nat) : (term566 A f b) = (term597 A f b).
Proof. exact (fun_ext (fun x : A => @lem6946926 A x f b)). Qed.
Lemma lem6946928 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6946930 {A : Type'} (f : A -> nat) (b : nat) : (term567 A f b) = (term598 A f b).
Proof. exact (MK_COMB (@lem6946928 A) (@lem6946927 A f b)). Qed.
Lemma lem6946931 {A : Type'} (f : A -> nat) (b : nat) : (term496 A f b) = (term598 A f b).
Proof. exact (TRANS (@lem6946731 A f b) (@lem6946930 A f b)). Qed.
Lemma lem6946932 {A : Type'} (f : A -> nat) (b : nat) (h1 : term496 A f b) : term598 A f b.
Proof. exact (EQ_MP (@lem6946931 A f b) (@lem6946653 A f b h1)). Qed.
Lemma lem6946940 (x : nat) (y : nat) (b : nat) : (term0 x y b) = (term1 x y b).
Proof. exact (@lem17045 (term2 y) (term3 x y b)). Qed.
Lemma lem6946942 (x : nat) : (term4 x) = (term4 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem6946943 (x : nat) (y : nat) (b : nat) : (term5 x y b) = (term6 x y b).
Proof. exact (MK_COMB (@lem6946942 x) (@lem6946940 x y b)). Qed.
Lemma lem6946944 (x : nat) (y : nat) (b : nat) : (term7 x y b) = (term5 x y b).
Proof. exact (@lem17045 (term2 x) (term8 x y b)). Qed.
Lemma lem6946945 (x : nat) (y : nat) (b : nat) : (term7 x y b) = (term6 x y b).
Proof. exact (TRANS (@lem6946944 x y b) (@lem6946943 x y b)). Qed.
Lemma lem6946950 (x : nat) (y : nat) (b : nat) : (term9 x y b) = (term9 x y b).
Proof. exact (eq_refl (term9 x y b)). Qed.
Lemma lem6946951 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6946952 (x : nat) (y : nat) (b : nat) : (term10 x y b) = (term11 x y b).
Proof. exact (MK_COMB (@lem6946951) (@lem6946945 x y b)). Qed.
Lemma lem6946953 (x : nat) (y : nat) (b : nat) : (term12 x y b) = (term13 x y b).
Proof. exact (MK_COMB (@lem6946952 x y b) (@lem6946950 x y b)). Qed.
Lemma lem6946954 (x : nat) (y : nat) (b : nat) : (term14 x y b) = (term12 x y b).
Proof. exact (@lem17265 (term15 x y b) (term9 x y b)). Qed.
Lemma lem6946955 (x : nat) (y : nat) (b : nat) : (term14 x y b) = (term13 x y b).
Proof. exact (TRANS (@lem6946954 x y b) (@lem6946953 x y b)). Qed.
Lemma lem6946956 (x : nat) (y : nat) : (term518 x y) = (term599 x y).
Proof. exact (fun_ext (fun b : nat => @lem6946955 x y b)). Qed.
Lemma lem6946957 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6946958 (x : nat) (y : nat) : (term317 x y) = (term600 x y).
Proof. exact (MK_COMB (@lem6946957) (@lem6946956 x y)). Qed.
Lemma lem6946959 (x : nat) : (term519 x) = (term601 x).
Proof. exact (fun_ext (fun y : nat => @lem6946958 x y)). Qed.
Lemma lem6946960 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6946961 (x : nat) : (term318 x) = (term602 x).
Proof. exact (MK_COMB (@lem6946960) (@lem6946959 x)). Qed.
Lemma lem6946962 : term520 = term603.
Proof. exact (fun_ext (fun x : nat => @lem6946961 x)). Qed.
Lemma lem6946963 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947024 : term319 = term604.
Proof. exact (MK_COMB (@lem6946963) (@lem6946962)). Qed.
Lemma lem6947025 (h1 : term319) : term604.
Proof. exact (EQ_MP (@lem6947024) (@lem6946654 h1)). Qed.
Lemma lem6947026 (n : nat) : (term2 n) = (term2 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem6947027 : term517 = term517.
Proof. exact (fun_ext (fun n : nat => @lem6947026 n)). Qed.
Lemma lem6947028 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947037 : term503 = term503.
Proof. exact (MK_COMB (@lem6947028) (@lem6947027)). Qed.
Lemma lem6947038 (h1 : term503) : term503.
Proof. exact (EQ_MP (@lem6947037) (@lem6946655 h1)). Qed.
Lemma lem6947039 {A : Type'} (x : A) (f : A -> nat) (b : nat) (h1 : term596 A x f b) : term596 A x f b.
Proof. exact (h1). Qed.
Lemma lem6947040 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term594 A x s f b) : term594 A x s f b.
Proof. exact (h1). Qed.
Lemma lem6947041 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term591 A x s f x' b.
Proof. exact (h1). Qed.
Lemma lem6947092 (x : nat) (y : nat) (b : nat) : (term13 x y b) = (term13 x y b).
Proof. exact (eq_refl (term13 x y b)). Qed.
Lemma lem6947093 (x : nat) (y : nat) : (term599 x y) = (term599 x y).
Proof. exact (fun_ext (fun b : nat => @lem6947092 x y b)). Qed.
Lemma lem6947094 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947095 (x : nat) (y : nat) : (term600 x y) = (term600 x y).
Proof. exact (MK_COMB (@lem6947094) (@lem6947093 x y)). Qed.
Lemma lem6947096 (x : nat) : (term601 x) = (term601 x).
Proof. exact (fun_ext (fun y : nat => @lem6947095 x y)). Qed.
Lemma lem6947097 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947098 (x : nat) : (term602 x) = (term602 x).
Proof. exact (MK_COMB (@lem6947097) (@lem6947096 x)). Qed.
Lemma lem6947099 : term603 = term603.
Proof. exact (fun_ext (fun x : nat => @lem6947098 x)). Qed.
Lemma lem6947100 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947101 : term604 = term604.
Proof. exact (MK_COMB (@lem6947100) (@lem6947099)). Qed.
Lemma lem6947102 (h1 : term319) : term604.
Proof. exact (EQ_MP (@lem6947101) (@lem6947025 h1)). Qed.
Lemma lem6947109 (n : nat) : (term2 n) = (term2 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem6947110 : term517 = term517.
Proof. exact (fun_ext (fun n : nat => @lem6947109 n)). Qed.
Lemma lem6947111 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947112 : term503 = term503.
Proof. exact (MK_COMB (@lem6947111) (@lem6947110)). Qed.
Lemma lem6947113 (h1 : term503) : term503.
Proof. exact (EQ_MP (@lem6947112) (@lem6947038 h1)). Qed.
Lemma lem6947114 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6947115 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6947120 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6947121 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem6947120 A nat f x). Qed.
Lemma lem6947123 {A : Type'} (f : A -> nat) (x' : A) : (f x') = (@I (A -> nat) f x').
Proof. exact (@lem6947121 A f x'). Qed.
Lemma lem6947124 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6947125 {A : Type'} (f : A -> nat) (x' : A) : (term605 A f x') = (term606 A f x').
Proof. exact (MK_COMB (@lem6947115) (@lem6947123 A f x')). Qed.
Lemma lem6947126 {A : Type'} (f : A -> nat) (x' : A) (b : nat) : (term409 A f x' b) = (term607 A f x' b).
Proof. exact (MK_COMB (@lem6947125 A f x') (@lem6947124 b)). Qed.
Lemma lem6947127 {A : Type'} (f : A -> nat) (x' : A) (b : nat) : (term608 A f x' b) = (term609 A f x' b).
Proof. exact (MK_COMB (@lem6947114) (@lem6947126 A f x' b)). Qed.
Lemma lem6947142 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term610 A x x' s) = (term610 A x x' s).
Proof. exact (eq_refl (term610 A x x' s)). Qed.
Lemma lem6947143 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term534 A x s f x' b) = (term611 A x s f x' b).
Proof. exact (MK_COMB (@lem6947142 A x x' s) (@lem6947127 A f x' b)). Qed.
Lemma lem6947144 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6947145 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem6947150 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6947152 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem6947150 A nat f x). Qed.
Lemma lem6947157 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@nsum A s f).
Proof. exact (eq_refl (@nsum A s f)). Qed.
Lemma lem6947158 {A : Type'} (f : A -> nat) (x : A) : (term612 A f x) = (term613 A f x).
Proof. exact (MK_COMB (@lem6947145) (@lem6947152 A f x)). Qed.
Lemma lem6947159 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : (term449 A x s f) = (term614 A x s f).
Proof. exact (MK_COMB (@lem6947158 A f x) (@lem6947157 A s f)). Qed.
Lemma lem6947160 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6947161 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : (term465 A x s f) = (term615 A x s f).
Proof. exact (MK_COMB (@lem6947144) (@lem6947159 A x s f)). Qed.
Lemma lem6947162 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term466 A x s f b) = (term616 A x s f b).
Proof. exact (MK_COMB (@lem6947161 A x s f) (@lem6947160 b)). Qed.
Lemma lem6947163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6947164 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term544 A x s f b) = (term617 A x s f b).
Proof. exact (MK_COMB (@lem6947163) (@lem6947162 A x s f b)). Qed.
Lemma lem6947165 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term578 A x s f x' b) = (term618 A x s f x' b).
Proof. exact (MK_COMB (@lem6947164 A x s f b) (@lem6947143 A x s f x' b)). Qed.
Lemma lem6947178 {A : Type'} (x : A) (s : A -> Prop) : (term368 A x s) = (term368 A x s).
Proof. exact (eq_refl (term368 A x s)). Qed.
Lemma lem6947179 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6947184 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6947186 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem6947184 A nat f x). Qed.
Lemma lem6947187 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6947188 {A : Type'} (f : A -> nat) (x : A) : (term605 A f x) = (term606 A f x).
Proof. exact (MK_COMB (@lem6947179) (@lem6947186 A f x)). Qed.
Lemma lem6947189 {A : Type'} (f : A -> nat) (x : A) (b : nat) : (term409 A f x b) = (term607 A f x b).
Proof. exact (MK_COMB (@lem6947188 A f x) (@lem6947187 b)). Qed.
Lemma lem6947198 {A : Type'} (x : A) (s : A -> Prop) : (term619 A x s) = (term619 A x s).
Proof. exact (eq_refl (term619 A x s)). Qed.
Lemma lem6947199 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term525 A s f x b) = (term620 A s f x b).
Proof. exact (MK_COMB (@lem6947198 A x s) (@lem6947189 A f x b)). Qed.
Lemma lem6947200 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term526 A s f b) = (term621 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6947199 A s f x b)). Qed.
Lemma lem6947201 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6947202 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term527 A s f b) = (term622 A s f b).
Proof. exact (MK_COMB (@lem6947201 A) (@lem6947200 A s f b)). Qed.
Lemma lem6947215 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term528 A s f b) = (term528 A s f b).
Proof. exact (eq_refl (term528 A s f b)). Qed.
Lemma lem6947216 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term530 A s f b) = (term623 A s f b).
Proof. exact (MK_COMB (@lem6947215 A s f b) (@lem6947202 A s f b)). Qed.
Lemma lem6947217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6947218 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term531 A s f b) = (term624 A s f b).
Proof. exact (MK_COMB (@lem6947217) (@lem6947216 A s f b)). Qed.
Lemma lem6947219 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) : (term532 A f b x s) = (term625 A f b x s).
Proof. exact (MK_COMB (@lem6947218 A s f b) (@lem6947178 A x s)). Qed.
Lemma lem6947220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6947221 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) : (term549 A f b x s) = (term626 A f b x s).
Proof. exact (MK_COMB (@lem6947220) (@lem6947219 A f b x s)). Qed.
Lemma lem6947222 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) : (term591 A x s f x' b) = (term627 A x s f x' b).
Proof. exact (MK_COMB (@lem6947221 A f b x s) (@lem6947165 A x s f x' b)). Qed.
Lemma lem6947223 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term627 A x s f x' b.
Proof. exact (EQ_MP (@lem6947222 A x s f x' b) (@lem6947041 A x s f x' b h1)). Qed.
Lemma lem6947224 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term618 A x s f x' b.
Proof. exact (proj2 (@lem6947223 A x s f x' b h1)). Qed.
Lemma lem6947225 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term625 A f b x s.
Proof. exact (proj1 (@lem6947223 A x s f x' b h1)). Qed.
Lemma lem6947226 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term611 A x s f x' b.
Proof. exact (proj2 (@lem6947224 A x s f x' b h1)). Qed.
Lemma lem6947229 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term326 A x x' s.
Proof. exact (proj1 (@lem6947226 A x s f x' b h1)). Qed.
Lemma lem6947231 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term623 A s f b.
Proof. exact (proj1 (@lem6947225 A x s f x' b h1)). Qed.
Lemma lem6947235 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term622 A s f b) : term622 A s f b.
Proof. exact (h1). Qed.
Lemma lem6947269 (x : nat) (y : nat) (b : nat) : (term13 x y b) = (term628 x y b).
Proof. exact (@lem19490 (Peano.le x b) (term6 x y b) (Peano.le y b)). Qed.
Lemma lem6947270 (x : nat) (y : nat) : (term599 x y) = (term629 x y).
Proof. exact (fun_ext (fun b : nat => @lem6947269 x y b)). Qed.
Lemma lem6947271 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947272 (x : nat) (y : nat) : (term600 x y) = (term630 x y).
Proof. exact (MK_COMB (@lem6947271) (@lem6947270 x y)). Qed.
Lemma lem6947273 (x : nat) : (term601 x) = (term631 x).
Proof. exact (fun_ext (fun y : nat => @lem6947272 x y)). Qed.
Lemma lem6947274 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947275 (x : nat) : (term602 x) = (term632 x).
Proof. exact (MK_COMB (@lem6947274) (@lem6947273 x)). Qed.
Lemma lem6947276 : term603 = term633.
Proof. exact (fun_ext (fun x : nat => @lem6947275 x)). Qed.
Lemma lem6947277 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947279 : term604 = term634.
Proof. exact (MK_COMB (@lem6947277) (@lem6947276)). Qed.
Lemma lem6947280 (h1 : term319) : term634.
Proof. exact (EQ_MP (@lem6947279) (@lem6947102 h1)). Qed.
Lemma lem6947282 (n : nat) : (term2 n) = (term2 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem6947283 : term517 = term517.
Proof. exact (fun_ext (fun n : nat => @lem6947282 n)). Qed.
Lemma lem6947284 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947286 : term503 = term503.
Proof. exact (MK_COMB (@lem6947284) (@lem6947283)). Qed.
Lemma lem6947287 (h1 : term503) : term503.
Proof. exact (EQ_MP (@lem6947286) (@lem6947113 h1)). Qed.
Lemma lem6947307 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term635 A s f b) : term635 A s f b.
Proof. exact (h1). Qed.
Lemma lem6947341 (x : nat) (y : nat) (b : nat) : (term13 x y b) = (term628 x y b).
Proof. exact (@lem19490 (Peano.le x b) (term6 x y b) (Peano.le y b)). Qed.
Lemma lem6947342 (x : nat) (y : nat) : (term599 x y) = (term629 x y).
Proof. exact (fun_ext (fun b : nat => @lem6947341 x y b)). Qed.
Lemma lem6947343 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947344 (x : nat) (y : nat) : (term600 x y) = (term630 x y).
Proof. exact (MK_COMB (@lem6947343) (@lem6947342 x y)). Qed.
Lemma lem6947345 (x : nat) : (term601 x) = (term631 x).
Proof. exact (fun_ext (fun y : nat => @lem6947344 x y)). Qed.
Lemma lem6947346 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947347 (x : nat) : (term602 x) = (term632 x).
Proof. exact (MK_COMB (@lem6947346) (@lem6947345 x)). Qed.
Lemma lem6947348 : term603 = term633.
Proof. exact (fun_ext (fun x : nat => @lem6947347 x)). Qed.
Lemma lem6947349 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947351 : term604 = term634.
Proof. exact (MK_COMB (@lem6947349) (@lem6947348)). Qed.
Lemma lem6947352 (h1 : term319) : term634.
Proof. exact (EQ_MP (@lem6947351) (@lem6947102 h1)). Qed.
Lemma lem6947354 (n : nat) : (term2 n) = (term2 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem6947355 : term517 = term517.
Proof. exact (fun_ext (fun n : nat => @lem6947354 n)). Qed.
Lemma lem6947356 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947358 : term503 = term503.
Proof. exact (MK_COMB (@lem6947356) (@lem6947355)). Qed.
Lemma lem6947359 (h1 : term503) : term503.
Proof. exact (EQ_MP (@lem6947358) (@lem6947113 h1)). Qed.
Lemma lem6947379 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term635 A s f b) : term635 A s f b.
Proof. exact (h1). Qed.
Lemma lem6947413 (x : nat) (y : nat) (b : nat) : (term13 x y b) = (term628 x y b).
Proof. exact (@lem19490 (Peano.le x b) (term6 x y b) (Peano.le y b)). Qed.
Lemma lem6947414 (x : nat) (y : nat) : (term599 x y) = (term629 x y).
Proof. exact (fun_ext (fun b : nat => @lem6947413 x y b)). Qed.
Lemma lem6947415 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947416 (x : nat) (y : nat) : (term600 x y) = (term630 x y).
Proof. exact (MK_COMB (@lem6947415) (@lem6947414 x y)). Qed.
Lemma lem6947417 (x : nat) : (term601 x) = (term631 x).
Proof. exact (fun_ext (fun y : nat => @lem6947416 x y)). Qed.
Lemma lem6947418 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947419 (x : nat) : (term602 x) = (term632 x).
Proof. exact (MK_COMB (@lem6947418) (@lem6947417 x)). Qed.
Lemma lem6947420 : term603 = term633.
Proof. exact (fun_ext (fun x : nat => @lem6947419 x)). Qed.
Lemma lem6947421 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947423 : term604 = term634.
Proof. exact (MK_COMB (@lem6947421) (@lem6947420)). Qed.
Lemma lem6947424 (h1 : term319) : term634.
Proof. exact (EQ_MP (@lem6947423) (@lem6947102 h1)). Qed.
Lemma lem6947426 (n : nat) : (term2 n) = (term2 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem6947427 : term517 = term517.
Proof. exact (fun_ext (fun n : nat => @lem6947426 n)). Qed.
Lemma lem6947428 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6947430 : term503 = term503.
Proof. exact (MK_COMB (@lem6947428) (@lem6947427)). Qed.
Lemma lem6947431 (h1 : term503) : term503.
Proof. exact (EQ_MP (@lem6947430) (@lem6947113 h1)). Qed.
Lemma lem6947464 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem6947536 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term620 A s f x b) = (term620 A s f x b).
Proof. exact (eq_refl (term620 A s f x b)). Qed.
Lemma lem6947537 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term621 A s f b) = (term621 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6947536 A s f x b)). Qed.
Lemma lem6947538 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6947540 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term622 A s f b) = (term622 A s f b).
Proof. exact (MK_COMB (@lem6947538 A) (@lem6947537 A s f b)). Qed.
Lemma lem6947541 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term622 A s f b) : term622 A s f b.
Proof. exact (EQ_MP (@lem6947540 A s f b) (@lem6947235 A s f b h1)). Qed.
Lemma lem6947545 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : @IN A x' s.
Proof. exact (h1). Qed.
Lemma lem6947546 (_92537 : nat) (h1 : term319) : term636 _92537.
Proof. exact (@lem6947280 h1 _92537). Qed.
Lemma lem6947547 (_92537 : nat) : (term636 _92537) = (term632 _92537).
Proof. exact (eq_refl (term636 _92537)). Qed.
Lemma lem6947548 (_92537 : nat) (h1 : term319) : term632 _92537.
Proof. exact (EQ_MP (@lem6947547 _92537) (@lem6947546 _92537 h1)). Qed.
Lemma lem6947549 (_92537 : nat) (_92538 : nat) (h1 : term319) : term637 _92537 _92538.
Proof. exact (@lem6947548 _92537 h1 _92538). Qed.
Lemma lem6947550 (_92537 : nat) (_92538 : nat) : (term637 _92537 _92538) = (term630 _92537 _92538).
Proof. exact (eq_refl (term637 _92537 _92538)). Qed.
Lemma lem6947551 (_92537 : nat) (_92538 : nat) (h1 : term319) : term630 _92537 _92538.
Proof. exact (EQ_MP (@lem6947550 _92537 _92538) (@lem6947549 _92537 _92538 h1)). Qed.
Lemma lem6947552 (_92537 : nat) (_92538 : nat) (_92539 : nat) (h1 : term319) : term638 _92537 _92538 _92539.
Proof. exact (@lem6947551 _92537 _92538 h1 _92539). Qed.
Lemma lem6947553 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term638 _92537 _92538 _92539) = (term628 _92537 _92538 _92539).
Proof. exact (eq_refl (term638 _92537 _92538 _92539)). Qed.
Lemma lem6947554 (_92537 : nat) (_92538 : nat) (_92539 : nat) (h1 : term319) : term628 _92537 _92538 _92539.
Proof. exact (EQ_MP (@lem6947553 _92537 _92538 _92539) (@lem6947552 _92537 _92538 _92539 h1)). Qed.
Lemma lem6947555 (_92540 : nat) (h1 : term503) : term639 _92540.
Proof. exact (@lem6947287 h1 _92540). Qed.
Lemma lem6947556 (_92540 : nat) : (term639 _92540) = (term2 _92540).
Proof. exact (eq_refl (term639 _92540)). Qed.
Lemma lem6947558 (_92541 : nat) (h1 : term319) : term636 _92541.
Proof. exact (@lem6947352 h1 _92541). Qed.
Lemma lem6947559 (_92541 : nat) : (term636 _92541) = (term632 _92541).
Proof. exact (eq_refl (term636 _92541)). Qed.
Lemma lem6947560 (_92541 : nat) (h1 : term319) : term632 _92541.
Proof. exact (EQ_MP (@lem6947559 _92541) (@lem6947558 _92541 h1)). Qed.
Lemma lem6947561 (_92541 : nat) (_92542 : nat) (h1 : term319) : term637 _92541 _92542.
Proof. exact (@lem6947560 _92541 h1 _92542). Qed.
Lemma lem6947562 (_92541 : nat) (_92542 : nat) : (term637 _92541 _92542) = (term630 _92541 _92542).
Proof. exact (eq_refl (term637 _92541 _92542)). Qed.
Lemma lem6947563 (_92541 : nat) (_92542 : nat) (h1 : term319) : term630 _92541 _92542.
Proof. exact (EQ_MP (@lem6947562 _92541 _92542) (@lem6947561 _92541 _92542 h1)). Qed.
Lemma lem6947564 (_92541 : nat) (_92542 : nat) (_92543 : nat) (h1 : term319) : term638 _92541 _92542 _92543.
Proof. exact (@lem6947563 _92541 _92542 h1 _92543). Qed.
Lemma lem6947565 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term638 _92541 _92542 _92543) = (term628 _92541 _92542 _92543).
Proof. exact (eq_refl (term638 _92541 _92542 _92543)). Qed.
Lemma lem6947566 (_92541 : nat) (_92542 : nat) (_92543 : nat) (h1 : term319) : term628 _92541 _92542 _92543.
Proof. exact (EQ_MP (@lem6947565 _92541 _92542 _92543) (@lem6947564 _92541 _92542 _92543 h1)). Qed.
Lemma lem6947567 (_92544 : nat) (h1 : term503) : term639 _92544.
Proof. exact (@lem6947359 h1 _92544). Qed.
Lemma lem6947568 (_92544 : nat) : (term639 _92544) = (term2 _92544).
Proof. exact (eq_refl (term639 _92544)). Qed.
Lemma lem6947570 (_92545 : nat) (h1 : term319) : term636 _92545.
Proof. exact (@lem6947424 h1 _92545). Qed.
Lemma lem6947571 (_92545 : nat) : (term636 _92545) = (term632 _92545).
Proof. exact (eq_refl (term636 _92545)). Qed.
Lemma lem6947572 (_92545 : nat) (h1 : term319) : term632 _92545.
Proof. exact (EQ_MP (@lem6947571 _92545) (@lem6947570 _92545 h1)). Qed.
Lemma lem6947573 (_92545 : nat) (_92546 : nat) (h1 : term319) : term637 _92545 _92546.
Proof. exact (@lem6947572 _92545 h1 _92546). Qed.
Lemma lem6947574 (_92545 : nat) (_92546 : nat) : (term637 _92545 _92546) = (term630 _92545 _92546).
Proof. exact (eq_refl (term637 _92545 _92546)). Qed.
Lemma lem6947575 (_92545 : nat) (_92546 : nat) (h1 : term319) : term630 _92545 _92546.
Proof. exact (EQ_MP (@lem6947574 _92545 _92546) (@lem6947573 _92545 _92546 h1)). Qed.
Lemma lem6947576 (_92545 : nat) (_92546 : nat) (_92547 : nat) (h1 : term319) : term638 _92545 _92546 _92547.
Proof. exact (@lem6947575 _92545 _92546 h1 _92547). Qed.
Lemma lem6947577 (_92545 : nat) (_92546 : nat) (_92547 : nat) : (term638 _92545 _92546 _92547) = (term628 _92545 _92546 _92547).
Proof. exact (eq_refl (term638 _92545 _92546 _92547)). Qed.
Lemma lem6947578 (_92545 : nat) (_92546 : nat) (_92547 : nat) (h1 : term319) : term628 _92545 _92546 _92547.
Proof. exact (EQ_MP (@lem6947577 _92545 _92546 _92547) (@lem6947576 _92545 _92546 _92547 h1)). Qed.
Lemma lem6947579 (_92548 : nat) (h1 : term503) : term639 _92548.
Proof. exact (@lem6947431 h1 _92548). Qed.
Lemma lem6947580 (_92548 : nat) : (term639 _92548) = (term2 _92548).
Proof. exact (eq_refl (term639 _92548)). Qed.
Lemma lem6947597 {A : Type'} (_92554 : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term622 A s f b) : term640 A s f b _92554.
Proof. exact (@lem6947541 A s f b h1 _92554). Qed.
Lemma lem6947598 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92554 : A) (b : nat) : (term640 A s f b _92554) = (term620 A s f _92554 b).
Proof. exact (eq_refl (term640 A s f b _92554)). Qed.
Lemma lem6947600 (_92537 : nat) (_92538 : nat) (_92539 : nat) (h1 : term319) : term641 _92537 _92538 _92539.
Proof. exact (proj2 (@lem6947554 _92537 _92538 _92539 h1)). Qed.
Lemma lem6947602 (_92541 : nat) (_92542 : nat) (_92543 : nat) (h1 : term319) : term641 _92541 _92542 _92543.
Proof. exact (proj2 (@lem6947566 _92541 _92542 _92543 h1)). Qed.
Lemma lem6947605 (_92546 : nat) (_92545 : nat) (_92547 : nat) (h1 : term319) : term642 _92546 _92545 _92547.
Proof. exact (proj1 (@lem6947578 _92545 _92546 _92547 h1)). Qed.
Lemma lem6947619 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term635 A s f b) : term635 A s f b.
Proof. exact (h1). Qed.
Lemma lem6947643 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term641 _92537 _92538 _92539) = (term643 _92537 _92538 _92539).
Proof. exact (@lem6943065 (term18 _92537) (term1 _92537 _92538 _92539) (Peano.le _92538 _92539)). Qed.
Lemma lem6947650 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term644 _92537 _92538 _92539) = (term645 _92537 _92538 _92539).
Proof. exact (@lem6943065 (term18 _92538) (term27 _92537 _92538 _92539) (Peano.le _92538 _92539)). Qed.
Lemma lem6947651 (_92537 : nat) : (term4 _92537) = (term4 _92537).
Proof. exact (eq_refl (term4 _92537)). Qed.
Lemma lem6947654 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term643 _92537 _92538 _92539) = (term646 _92537 _92538 _92539).
Proof. exact (MK_COMB (@lem6947651 _92537) (@lem6947650 _92537 _92538 _92539)). Qed.
Lemma lem6947656 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term641 _92537 _92538 _92539) = (term646 _92537 _92538 _92539).
Proof. exact (TRANS (@lem6947643 _92537 _92538 _92539) (@lem6947654 _92537 _92538 _92539)). Qed.
Lemma lem6947669 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term635 A s f b) : term635 A s f b.
Proof. exact (h1). Qed.
Lemma lem6947693 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term641 _92541 _92542 _92543) = (term643 _92541 _92542 _92543).
Proof. exact (@lem6943065 (term18 _92541) (term1 _92541 _92542 _92543) (Peano.le _92542 _92543)). Qed.
Lemma lem6947700 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term644 _92541 _92542 _92543) = (term645 _92541 _92542 _92543).
Proof. exact (@lem6943065 (term18 _92542) (term27 _92541 _92542 _92543) (Peano.le _92542 _92543)). Qed.
Lemma lem6947701 (_92541 : nat) : (term4 _92541) = (term4 _92541).
Proof. exact (eq_refl (term4 _92541)). Qed.
Lemma lem6947704 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term643 _92541 _92542 _92543) = (term646 _92541 _92542 _92543).
Proof. exact (MK_COMB (@lem6947701 _92541) (@lem6947700 _92541 _92542 _92543)). Qed.
Lemma lem6947706 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term641 _92541 _92542 _92543) = (term646 _92541 _92542 _92543).
Proof. exact (TRANS (@lem6947693 _92541 _92542 _92543) (@lem6947704 _92541 _92542 _92543)). Qed.
Lemma lem6947707 (_92541 : nat) (_92542 : nat) (_92543 : nat) (h1 : term319) : term646 _92541 _92542 _92543.
Proof. exact (EQ_MP (@lem6947706 _92541 _92542 _92543) (@lem6947602 _92541 _92542 _92543 h1)). Qed.
Lemma lem6947713 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term609 A f x' b.
Proof. exact (proj2 (@lem6947226 A x s f x' b h1)). Qed.
Lemma lem6947725 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem6947729 (_92546 : nat) (_92545 : nat) (_92547 : nat) : (term642 _92546 _92545 _92547) = (term647 _92546 _92545 _92547).
Proof. exact (@lem6943065 (term18 _92545) (term1 _92545 _92546 _92547) (Peano.le _92545 _92547)). Qed.
Lemma lem6947736 (_92546 : nat) (_92545 : nat) (_92547 : nat) : (term648 _92546 _92545 _92547) = (term649 _92546 _92545 _92547).
Proof. exact (@lem6943065 (term18 _92546) (term27 _92545 _92546 _92547) (Peano.le _92545 _92547)). Qed.
Lemma lem6947737 (_92545 : nat) : (term4 _92545) = (term4 _92545).
Proof. exact (eq_refl (term4 _92545)). Qed.
Lemma lem6947740 (_92546 : nat) (_92545 : nat) (_92547 : nat) : (term647 _92546 _92545 _92547) = (term650 _92546 _92545 _92547).
Proof. exact (MK_COMB (@lem6947737 _92545) (@lem6947736 _92546 _92545 _92547)). Qed.
Lemma lem6947742 (_92546 : nat) (_92545 : nat) (_92547 : nat) : (term642 _92546 _92545 _92547) = (term650 _92546 _92545 _92547).
Proof. exact (TRANS (@lem6947729 _92546 _92545 _92547) (@lem6947740 _92546 _92545 _92547)). Qed.
Lemma lem6947767 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term609 A f x' b.
Proof. exact (proj2 (@lem6947226 A x s f x' b h1)). Qed.
Lemma lem6947777 {A : Type'} (_92554 : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term622 A s f b) : term620 A s f _92554 b.
Proof. exact (EQ_MP (@lem6947598 A s f _92554 b) (@lem6947597 A _92554 s f b h1)). Qed.
Lemma lem6947779 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : @IN A x' s.
Proof. exact (h1). Qed.
Lemma lem6947912 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term635 A s f b) : term635 A s f b.
Proof. exact (h1). Qed.
Lemma lem6947940 (_92537 : nat) (_92538 : nat) (_92539 : nat) (h1 : term319) : term646 _92537 _92538 _92539.
Proof. exact (EQ_MP (@lem6947656 _92537 _92538 _92539) (@lem6947600 _92537 _92538 _92539 h1)). Qed.
Lemma lem6947983 {A : Type'} (f : A -> nat) (b : nat) : (term651 A f b) = (term651 A f b).
Proof. exact (eq_refl (term651 A f b)). Qed.
Lemma lem6947984 {A : Type'} (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : x' = x) : (term652 A f b x') = (term652 A f b x).
Proof. exact (MK_COMB (@lem6947983 A f b) (@lem6947725 A x' x h1)). Qed.
Lemma lem6947985 {A : Type'} (f : A -> nat) (x : A) (b : nat) : (term652 A f b x) = (term609 A f x b).
Proof. exact (eq_refl (term652 A f b x)). Qed.
Lemma lem6947986 {A : Type'} (f : A -> nat) (b : nat) (x' : A) : (term653 A f b x') = (term653 A f b x').
Proof. exact (eq_refl (term653 A f b x')). Qed.
Lemma lem6947987 {A : Type'} (x' : A) (f : A -> nat) (x : A) (b : nat) : ((term652 A f b x') = (term652 A f b x)) = ((term652 A f b x') = (term609 A f x b)).
Proof. exact (MK_COMB (@lem6947986 A f b x') (@lem6947985 A f x b)). Qed.
Lemma lem6947988 {A : Type'} (f : A -> nat) (x' : A) (b : nat) : (term652 A f b x') = (term609 A f x' b).
Proof. exact (eq_refl (term652 A f b x')). Qed.
Lemma lem6947989 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6947990 {A : Type'} (f : A -> nat) (x' : A) (b : nat) : (term653 A f b x') = (term654 A f x' b).
Proof. exact (MK_COMB (@lem6947989) (@lem6947988 A f x' b)). Qed.
Lemma lem6947991 {A : Type'} (f : A -> nat) (x : A) (b : nat) : (term609 A f x b) = (term609 A f x b).
Proof. exact (eq_refl (term609 A f x b)). Qed.
Lemma lem6947992 {A : Type'} (x' : A) (f : A -> nat) (x : A) (b : nat) : ((term652 A f b x') = (term609 A f x b)) = ((term609 A f x' b) = (term609 A f x b)).
Proof. exact (MK_COMB (@lem6947990 A f x' b) (@lem6947991 A f x b)). Qed.
Lemma lem6947993 {A : Type'} (x' : A) (f : A -> nat) (x : A) (b : nat) : ((term652 A f b x') = (term652 A f b x)) = ((term609 A f x' b) = (term609 A f x b)).
Proof. exact (TRANS (@lem6947987 A x' f x b) (@lem6947992 A x' f x b)). Qed.
Lemma lem6947994 {A : Type'} (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : x' = x) : (term609 A f x' b) = (term609 A f x b).
Proof. exact (EQ_MP (@lem6947993 A x' f x b) (@lem6947984 A f b x' x h1)). Qed.
Lemma lem6947995 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : term591 A x s f x' b) (h2 : x' = x) : term609 A f x b.
Proof. exact (EQ_MP (@lem6947994 A f b x' x h2) (@lem6947713 A x s f x' b h1)). Qed.
Lemma lem6948051 (_92546 : nat) (_92545 : nat) (_92547 : nat) (h1 : term319) : term650 _92546 _92545 _92547.
Proof. exact (EQ_MP (@lem6947742 _92546 _92545 _92547) (@lem6947605 _92546 _92545 _92547 h1)). Qed.
Lemma lem6948067 (_92540 : nat) (h1 : term503) : term2 _92540.
Proof. exact (EQ_MP (@lem6947556 _92540) (@lem6947555 _92540 h1)). Qed.
Lemma lem6948068 {A : Type'} (f : A -> nat) (x : A) (h1 : term503) : term655 A f x.
Proof. exact (@lem6948067 (@I (A -> nat) f x) h1). Qed.
Lemma lem6948069 {A : Type'} (f : A -> nat) (x : A) (h1 : term503) : term656 A f x.
Proof. exact (fun h0 : term657 A f x => @lem6948068 A f x h1). Qed.
Lemma lem6948071 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948072 {A : Type'} (f : A -> nat) (x : A) : (term656 A f x) = (term655 A f x).
Proof. exact (@lem6948071 (term655 A f x)). Qed.
Lemma lem6948073 {A : Type'} (f : A -> nat) (x : A) (h1 : term503) : term655 A f x.
Proof. exact (EQ_MP (@lem6948072 A f x) (@lem6948069 A f x h1)). Qed.
Lemma lem6948075 (_92540 : nat) (h1 : term503) : term2 _92540.
Proof. exact (EQ_MP (@lem6947556 _92540) (@lem6947555 _92540 h1)). Qed.
Lemma lem6948076 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term503) : term659 A s f.
Proof. exact (@lem6948075 (@nsum A s f) h1). Qed.
Lemma lem6948077 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term503) : term660 A s f.
Proof. exact (fun h0 : term661 A s f => @lem6948076 A s f h1). Qed.
Lemma lem6948079 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948080 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term660 A s f) = (term659 A s f).
Proof. exact (@lem6948079 (term659 A s f)). Qed.
Lemma lem6948081 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term503) : term659 A s f.
Proof. exact (EQ_MP (@lem6948080 A s f) (@lem6948077 A s f h1)). Qed.
Lemma lem6948083 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term616 A x s f b.
Proof. exact (proj1 (@lem6947224 A x s f x' b h1)). Qed.
Lemma lem6948084 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term662 A x s f b.
Proof. exact (fun h0 : term663 A x s f b => @lem6948083 A x s f x' b h1). Qed.
Lemma lem6948086 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948087 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term662 A x s f b) = (term616 A x s f b).
Proof. exact (@lem6948086 (term616 A x s f b)). Qed.
Lemma lem6948088 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term616 A x s f b.
Proof. exact (EQ_MP (@lem6948087 A x s f b) (@lem6948084 A x s f x' b h1)). Qed.
Lemma lem6948104 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948105 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term645 _92537 _92538 _92539) = (term664 _92537 _92538 _92539).
Proof. exact (@lem6948104 (term27 _92537 _92538 _92539) (term18 _92538) (Peano.le _92538 _92539)). Qed.
Lemma lem6948119 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6948120 (_92539 : nat) (_92538 : nat) : (term665 _92538 _92539) = (term666 _92539 _92538).
Proof. exact (@lem6948119 (Peano.le _92538 _92539) (term18 _92538)). Qed.
Lemma lem6948126 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term667 _92537 _92538 _92539) = (term667 _92537 _92538 _92539).
Proof. exact (eq_refl (term667 _92537 _92538 _92539)). Qed.
Lemma lem6948127 (_92537 : nat) (_92539 : nat) (_92538 : nat) : (term664 _92537 _92538 _92539) = (term668 _92537 _92539 _92538).
Proof. exact (MK_COMB (@lem6948126 _92537 _92538 _92539) (@lem6948120 _92539 _92538)). Qed.
Lemma lem6948131 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948132 (_92537 : nat) (_92539 : nat) (_92538 : nat) : (term668 _92537 _92539 _92538) = (term669 _92537 _92539 _92538).
Proof. exact (@lem6948131 (Peano.le _92538 _92539) (term27 _92537 _92538 _92539) (term18 _92538)). Qed.
Lemma lem6948148 (_92537 : nat) (_92539 : nat) (_92538 : nat) : (term664 _92537 _92538 _92539) = (term669 _92537 _92539 _92538).
Proof. exact (TRANS (@lem6948127 _92537 _92539 _92538) (@lem6948132 _92537 _92539 _92538)). Qed.
Lemma lem6948149 (_92537 : nat) (_92539 : nat) (_92538 : nat) : (term645 _92537 _92538 _92539) = (term669 _92537 _92539 _92538).
Proof. exact (TRANS (@lem6948105 _92537 _92538 _92539) (@lem6948148 _92537 _92539 _92538)). Qed.
Lemma lem6948150 (_92537 : nat) : (term4 _92537) = (term4 _92537).
Proof. exact (eq_refl (term4 _92537)). Qed.
Lemma lem6948151 (_92537 : nat) (_92539 : nat) (_92538 : nat) : (term646 _92537 _92538 _92539) = (term670 _92537 _92539 _92538).
Proof. exact (MK_COMB (@lem6948150 _92537) (@lem6948149 _92537 _92539 _92538)). Qed.
Lemma lem6948155 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948156 (_92537 : nat) (_92539 : nat) (_92538 : nat) : (term670 _92537 _92539 _92538) = (term671 _92537 _92539 _92538).
Proof. exact (@lem6948155 (Peano.le _92538 _92539) (term18 _92537) (term672 _92537 _92539 _92538)). Qed.
Lemma lem6948170 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948171 (_92539 : nat) (_92537 : nat) (_92538 : nat) : (term673 _92537 _92539 _92538) = (term674 _92539 _92537 _92538).
Proof. exact (@lem6948170 (term27 _92537 _92538 _92539) (term18 _92537) (term18 _92538)). Qed.
Lemma lem6948187 (_92538 : nat) (_92539 : nat) : (term675 _92538 _92539) = (term675 _92538 _92539).
Proof. exact (eq_refl (term675 _92538 _92539)). Qed.
Lemma lem6948188 (_92539 : nat) (_92537 : nat) (_92538 : nat) : (term671 _92537 _92539 _92538) = (term676 _92539 _92537 _92538).
Proof. exact (MK_COMB (@lem6948187 _92538 _92539) (@lem6948171 _92539 _92537 _92538)). Qed.
Lemma lem6948199 (_92539 : nat) (_92537 : nat) (_92538 : nat) : (term670 _92537 _92539 _92538) = (term676 _92539 _92537 _92538).
Proof. exact (TRANS (@lem6948156 _92537 _92539 _92538) (@lem6948188 _92539 _92537 _92538)). Qed.
Lemma lem6948200 (_92539 : nat) (_92537 : nat) (_92538 : nat) : (term646 _92537 _92538 _92539) = (term676 _92539 _92537 _92538).
Proof. exact (TRANS (@lem6948151 _92537 _92539 _92538) (@lem6948199 _92539 _92537 _92538)). Qed.
Lemma lem6948201 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6948202 (_92539 : nat) (_92537 : nat) (_92538 : nat) : (term677 _92537 _92538 _92539) = (term678 _92539 _92537 _92538).
Proof. exact (MK_COMB (@lem6948201) (@lem6948200 _92539 _92537 _92538)). Qed.
Lemma lem6948226 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6948227 (_92537 : nat) (_92539 : nat) (_92538 : nat) : (term1 _92537 _92538 _92539) = (term672 _92537 _92539 _92538).
Proof. exact (@lem6948226 (term27 _92537 _92538 _92539) (term18 _92538)). Qed.
Lemma lem6948233 (_92537 : nat) : (term4 _92537) = (term4 _92537).
Proof. exact (eq_refl (term4 _92537)). Qed.
Lemma lem6948234 (_92537 : nat) (_92539 : nat) (_92538 : nat) : (term6 _92537 _92538 _92539) = (term673 _92537 _92539 _92538).
Proof. exact (MK_COMB (@lem6948233 _92537) (@lem6948227 _92537 _92539 _92538)). Qed.
Lemma lem6948238 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948239 (_92539 : nat) (_92537 : nat) (_92538 : nat) : (term673 _92537 _92539 _92538) = (term674 _92539 _92537 _92538).
Proof. exact (@lem6948238 (term27 _92537 _92538 _92539) (term18 _92537) (term18 _92538)). Qed.
Lemma lem6948255 (_92539 : nat) (_92537 : nat) (_92538 : nat) : (term6 _92537 _92538 _92539) = (term674 _92539 _92537 _92538).
Proof. exact (TRANS (@lem6948234 _92537 _92539 _92538) (@lem6948239 _92539 _92537 _92538)). Qed.
Lemma lem6948256 (_92538 : nat) (_92539 : nat) : (term675 _92538 _92539) = (term675 _92538 _92539).
Proof. exact (eq_refl (term675 _92538 _92539)). Qed.
Lemma lem6948257 (_92539 : nat) (_92537 : nat) (_92538 : nat) : (term679 _92537 _92538 _92539) = (term676 _92539 _92537 _92538).
Proof. exact (MK_COMB (@lem6948256 _92538 _92539) (@lem6948255 _92539 _92537 _92538)). Qed.
Lemma lem6948268 (_92539 : nat) (_92537 : nat) (_92538 : nat) : ((term646 _92537 _92538 _92539) = (term679 _92537 _92538 _92539)) = ((term676 _92539 _92537 _92538) = (term676 _92539 _92537 _92538)).
Proof. exact (MK_COMB (@lem6948202 _92539 _92537 _92538) (@lem6948257 _92539 _92537 _92538)). Qed.
Lemma lem6948270 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6948271 (x : Prop) : (x = x) = True.
Proof. exact (@lem6948270 Prop x). Qed.
Lemma lem6948272 (_92539 : nat) (_92537 : nat) (_92538 : nat) : ((term676 _92539 _92537 _92538) = (term676 _92539 _92537 _92538)) = True.
Proof. exact (@lem6948271 (term676 _92539 _92537 _92538)). Qed.
Lemma lem6948273 (_92537 : nat) (_92538 : nat) (_92539 : nat) : ((term646 _92537 _92538 _92539) = (term679 _92537 _92538 _92539)) = True.
Proof. exact (TRANS (@lem6948268 _92539 _92537 _92538) (@lem6948272 _92539 _92537 _92538)). Qed.
Lemma lem6948274 (_92537 : nat) (_92538 : nat) (_92539 : nat) : True = ((term646 _92537 _92538 _92539) = (term679 _92537 _92538 _92539)).
Proof. exact (SYM (@lem6948273 _92537 _92538 _92539)). Qed.
Lemma lem6948275 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term646 _92537 _92538 _92539) = (term679 _92537 _92538 _92539).
Proof. exact (EQ_MP (@lem6948274 _92537 _92538 _92539) (@lem0)). Qed.
Lemma lem6948276 (_92537 : nat) (_92538 : nat) (_92539 : nat) (h1 : term319) : term679 _92537 _92538 _92539.
Proof. exact (EQ_MP (@lem6948275 _92537 _92538 _92539) (@lem6947940 _92537 _92538 _92539 h1)). Qed.
Lemma lem6948278 (b : Prop) (a : Prop) : (a \/ b) = (term680 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6948279 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term679 _92537 _92538 _92539) = (term681 _92537 _92538 _92539).
Proof. exact (@lem6948278 (term6 _92537 _92538 _92539) (Peano.le _92538 _92539)). Qed.
Lemma lem6948281 (a : Prop) (b : Prop) : (term682 a b) = (term683 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6948282 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term684 _92537 _92538 _92539) = (term685 _92537 _92538 _92539).
Proof. exact (@lem6948281 (term18 _92537) (term1 _92537 _92538 _92539)). Qed.
Lemma lem6948284 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6948285 (_92537 : nat) : (term686 _92537) = (term2 _92537).
Proof. exact (@lem6948284 (term2 _92537)). Qed.
Lemma lem6948286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6948287 (_92537 : nat) : (term687 _92537) = (term688 _92537).
Proof. exact (MK_COMB (@lem6948286) (@lem6948285 _92537)). Qed.
Lemma lem6948289 (a : Prop) (b : Prop) : (term682 a b) = (term683 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6948290 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term689 _92537 _92538 _92539) = (term690 _92537 _92538 _92539).
Proof. exact (@lem6948289 (term18 _92538) (term27 _92537 _92538 _92539)). Qed.
Lemma lem6948292 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6948293 (_92538 : nat) : (term686 _92538) = (term2 _92538).
Proof. exact (@lem6948292 (term2 _92538)). Qed.
Lemma lem6948294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6948295 (_92538 : nat) : (term687 _92538) = (term688 _92538).
Proof. exact (MK_COMB (@lem6948294) (@lem6948293 _92538)). Qed.
Lemma lem6948297 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6948298 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term691 _92537 _92538 _92539) = (term3 _92537 _92538 _92539).
Proof. exact (@lem6948297 (term3 _92537 _92538 _92539)). Qed.
Lemma lem6948299 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term690 _92537 _92538 _92539) = (term8 _92537 _92538 _92539).
Proof. exact (MK_COMB (@lem6948295 _92538) (@lem6948298 _92537 _92538 _92539)). Qed.
Lemma lem6948300 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term689 _92537 _92538 _92539) = (term8 _92537 _92538 _92539).
Proof. exact (TRANS (@lem6948290 _92537 _92538 _92539) (@lem6948299 _92537 _92538 _92539)). Qed.
Lemma lem6948301 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term685 _92537 _92538 _92539) = (term15 _92537 _92538 _92539).
Proof. exact (MK_COMB (@lem6948287 _92537) (@lem6948300 _92537 _92538 _92539)). Qed.
Lemma lem6948302 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term684 _92537 _92538 _92539) = (term15 _92537 _92538 _92539).
Proof. exact (TRANS (@lem6948282 _92537 _92538 _92539) (@lem6948301 _92537 _92538 _92539)). Qed.
Lemma lem6948303 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6948304 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term692 _92537 _92538 _92539) = (term693 _92537 _92538 _92539).
Proof. exact (MK_COMB (@lem6948303) (@lem6948302 _92537 _92538 _92539)). Qed.
Lemma lem6948305 (_92538 : nat) (_92539 : nat) : (Peano.le _92538 _92539) = (Peano.le _92538 _92539).
Proof. exact (eq_refl (Peano.le _92538 _92539)). Qed.
Lemma lem6948306 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term681 _92537 _92538 _92539) = (term694 _92537 _92538 _92539).
Proof. exact (MK_COMB (@lem6948304 _92537 _92538 _92539) (@lem6948305 _92538 _92539)). Qed.
Lemma lem6948307 (_92537 : nat) (_92538 : nat) (_92539 : nat) : (term679 _92537 _92538 _92539) = (term694 _92537 _92538 _92539).
Proof. exact (TRANS (@lem6948279 _92537 _92538 _92539) (@lem6948306 _92537 _92538 _92539)). Qed.
Lemma lem6948309 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term503) (h2 : term591 A x s f x' b) : term695 A x s f b.
Proof. exact (conj (@lem6948081 A s f h1) (@lem6948088 A x s f x' b h2)). Qed.
Lemma lem6948310 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term503) (h2 : term591 A x s f x' b) : term696 A x s f b.
Proof. exact (conj (@lem6948073 A f x h1) (@lem6948309 A x s f x' b h1 h2)). Qed.
Lemma lem6948312 (_92537 : nat) (_92538 : nat) (_92539 : nat) (h1 : term319) : term694 _92537 _92538 _92539.
Proof. exact (EQ_MP (@lem6948307 _92537 _92538 _92539) (@lem6948276 _92537 _92538 _92539 h1)). Qed.
Lemma lem6948313 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term319) : term697 A x s f b.
Proof. exact (@lem6948312 (@I (A -> nat) f x) (@nsum A s f) b h1). Qed.
Lemma lem6948316 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) : term352 A s f b.
Proof. exact (@lem6948313 A x s f b h1 (@lem6948310 A x s f x' b h2 h3)). Qed.
Lemma lem6948317 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) : term698 A s f b.
Proof. exact (fun h0 : term635 A s f b => @lem6948316 A x s f x' b h1 h2 h3). Qed.
Lemma lem6948319 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948320 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term698 A s f b) = (term352 A s f b).
Proof. exact (@lem6948319 (term352 A s f b)). Qed.
Lemma lem6948321 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) : term352 A s f b.
Proof. exact (EQ_MP (@lem6948320 A s f b) (@lem6948317 A x s f x' b h1 h2 h3)). Qed.
Lemma lem6948324 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6948326 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term635 A s f b) = (term699 A s f b).
Proof. exact (@lem6948324 (term352 A s f b)). Qed.
Lemma lem6948329 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term635 A s f b) : term699 A s f b.
Proof. exact (EQ_MP (@lem6948326 A s f b) (@lem6947912 A s f b h1)). Qed.
Lemma lem6948332 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : False.
Proof. exact (@lem6948329 A s f b h3 (@lem6948321 A x s f x' b h1 h2 h4)). Qed.
Lemma lem6948333 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : term700.
Proof. exact (fun h0 : ~ False => @lem6948332 A x s f x' b h1 h2 h3 h4). Qed.
Lemma lem6948335 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948336 : term700 = False.
Proof. exact (@lem6948335 False). Qed.
Lemma lem6948337 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : False.
Proof. exact (EQ_MP (@lem6948336) (@lem6948333 A x s f x' b h1 h2 h3 h4)). Qed.
Lemma lem6948339 (_92544 : nat) (h1 : term503) : term2 _92544.
Proof. exact (EQ_MP (@lem6947568 _92544) (@lem6947567 _92544 h1)). Qed.
Lemma lem6948340 {A : Type'} (f : A -> nat) (x : A) (h1 : term503) : term655 A f x.
Proof. exact (@lem6948339 (@I (A -> nat) f x) h1). Qed.
Lemma lem6948341 {A : Type'} (f : A -> nat) (x : A) (h1 : term503) : term656 A f x.
Proof. exact (fun h0 : term657 A f x => @lem6948340 A f x h1). Qed.
Lemma lem6948343 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948344 {A : Type'} (f : A -> nat) (x : A) : (term656 A f x) = (term655 A f x).
Proof. exact (@lem6948343 (term655 A f x)). Qed.
Lemma lem6948345 {A : Type'} (f : A -> nat) (x : A) (h1 : term503) : term655 A f x.
Proof. exact (EQ_MP (@lem6948344 A f x) (@lem6948341 A f x h1)). Qed.
Lemma lem6948347 (_92544 : nat) (h1 : term503) : term2 _92544.
Proof. exact (EQ_MP (@lem6947568 _92544) (@lem6947567 _92544 h1)). Qed.
Lemma lem6948348 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term503) : term659 A s f.
Proof. exact (@lem6948347 (@nsum A s f) h1). Qed.
Lemma lem6948349 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term503) : term660 A s f.
Proof. exact (fun h0 : term661 A s f => @lem6948348 A s f h1). Qed.
Lemma lem6948351 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948352 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term660 A s f) = (term659 A s f).
Proof. exact (@lem6948351 (term659 A s f)). Qed.
Lemma lem6948353 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term503) : term659 A s f.
Proof. exact (EQ_MP (@lem6948352 A s f) (@lem6948349 A s f h1)). Qed.
Lemma lem6948355 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term616 A x s f b.
Proof. exact (proj1 (@lem6947224 A x s f x' b h1)). Qed.
Lemma lem6948356 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term662 A x s f b.
Proof. exact (fun h0 : term663 A x s f b => @lem6948355 A x s f x' b h1). Qed.
Lemma lem6948358 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948359 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term662 A x s f b) = (term616 A x s f b).
Proof. exact (@lem6948358 (term616 A x s f b)). Qed.
Lemma lem6948360 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term616 A x s f b.
Proof. exact (EQ_MP (@lem6948359 A x s f b) (@lem6948356 A x s f x' b h1)). Qed.
Lemma lem6948376 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948377 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term645 _92541 _92542 _92543) = (term664 _92541 _92542 _92543).
Proof. exact (@lem6948376 (term27 _92541 _92542 _92543) (term18 _92542) (Peano.le _92542 _92543)). Qed.
Lemma lem6948391 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6948392 (_92543 : nat) (_92542 : nat) : (term665 _92542 _92543) = (term666 _92543 _92542).
Proof. exact (@lem6948391 (Peano.le _92542 _92543) (term18 _92542)). Qed.
Lemma lem6948398 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term667 _92541 _92542 _92543) = (term667 _92541 _92542 _92543).
Proof. exact (eq_refl (term667 _92541 _92542 _92543)). Qed.
Lemma lem6948399 (_92541 : nat) (_92543 : nat) (_92542 : nat) : (term664 _92541 _92542 _92543) = (term668 _92541 _92543 _92542).
Proof. exact (MK_COMB (@lem6948398 _92541 _92542 _92543) (@lem6948392 _92543 _92542)). Qed.
Lemma lem6948403 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948404 (_92541 : nat) (_92543 : nat) (_92542 : nat) : (term668 _92541 _92543 _92542) = (term669 _92541 _92543 _92542).
Proof. exact (@lem6948403 (Peano.le _92542 _92543) (term27 _92541 _92542 _92543) (term18 _92542)). Qed.
Lemma lem6948420 (_92541 : nat) (_92543 : nat) (_92542 : nat) : (term664 _92541 _92542 _92543) = (term669 _92541 _92543 _92542).
Proof. exact (TRANS (@lem6948399 _92541 _92543 _92542) (@lem6948404 _92541 _92543 _92542)). Qed.
Lemma lem6948421 (_92541 : nat) (_92543 : nat) (_92542 : nat) : (term645 _92541 _92542 _92543) = (term669 _92541 _92543 _92542).
Proof. exact (TRANS (@lem6948377 _92541 _92542 _92543) (@lem6948420 _92541 _92543 _92542)). Qed.
Lemma lem6948422 (_92541 : nat) : (term4 _92541) = (term4 _92541).
Proof. exact (eq_refl (term4 _92541)). Qed.
Lemma lem6948423 (_92541 : nat) (_92543 : nat) (_92542 : nat) : (term646 _92541 _92542 _92543) = (term670 _92541 _92543 _92542).
Proof. exact (MK_COMB (@lem6948422 _92541) (@lem6948421 _92541 _92543 _92542)). Qed.
Lemma lem6948427 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948428 (_92541 : nat) (_92543 : nat) (_92542 : nat) : (term670 _92541 _92543 _92542) = (term671 _92541 _92543 _92542).
Proof. exact (@lem6948427 (Peano.le _92542 _92543) (term18 _92541) (term672 _92541 _92543 _92542)). Qed.
Lemma lem6948442 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948443 (_92543 : nat) (_92541 : nat) (_92542 : nat) : (term673 _92541 _92543 _92542) = (term674 _92543 _92541 _92542).
Proof. exact (@lem6948442 (term27 _92541 _92542 _92543) (term18 _92541) (term18 _92542)). Qed.
Lemma lem6948459 (_92542 : nat) (_92543 : nat) : (term675 _92542 _92543) = (term675 _92542 _92543).
Proof. exact (eq_refl (term675 _92542 _92543)). Qed.
Lemma lem6948460 (_92543 : nat) (_92541 : nat) (_92542 : nat) : (term671 _92541 _92543 _92542) = (term676 _92543 _92541 _92542).
Proof. exact (MK_COMB (@lem6948459 _92542 _92543) (@lem6948443 _92543 _92541 _92542)). Qed.
Lemma lem6948471 (_92543 : nat) (_92541 : nat) (_92542 : nat) : (term670 _92541 _92543 _92542) = (term676 _92543 _92541 _92542).
Proof. exact (TRANS (@lem6948428 _92541 _92543 _92542) (@lem6948460 _92543 _92541 _92542)). Qed.
Lemma lem6948472 (_92543 : nat) (_92541 : nat) (_92542 : nat) : (term646 _92541 _92542 _92543) = (term676 _92543 _92541 _92542).
Proof. exact (TRANS (@lem6948423 _92541 _92543 _92542) (@lem6948471 _92543 _92541 _92542)). Qed.
Lemma lem6948473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6948474 (_92543 : nat) (_92541 : nat) (_92542 : nat) : (term677 _92541 _92542 _92543) = (term678 _92543 _92541 _92542).
Proof. exact (MK_COMB (@lem6948473) (@lem6948472 _92543 _92541 _92542)). Qed.
Lemma lem6948498 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6948499 (_92541 : nat) (_92543 : nat) (_92542 : nat) : (term1 _92541 _92542 _92543) = (term672 _92541 _92543 _92542).
Proof. exact (@lem6948498 (term27 _92541 _92542 _92543) (term18 _92542)). Qed.
Lemma lem6948505 (_92541 : nat) : (term4 _92541) = (term4 _92541).
Proof. exact (eq_refl (term4 _92541)). Qed.
Lemma lem6948506 (_92541 : nat) (_92543 : nat) (_92542 : nat) : (term6 _92541 _92542 _92543) = (term673 _92541 _92543 _92542).
Proof. exact (MK_COMB (@lem6948505 _92541) (@lem6948499 _92541 _92543 _92542)). Qed.
Lemma lem6948510 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948511 (_92543 : nat) (_92541 : nat) (_92542 : nat) : (term673 _92541 _92543 _92542) = (term674 _92543 _92541 _92542).
Proof. exact (@lem6948510 (term27 _92541 _92542 _92543) (term18 _92541) (term18 _92542)). Qed.
Lemma lem6948527 (_92543 : nat) (_92541 : nat) (_92542 : nat) : (term6 _92541 _92542 _92543) = (term674 _92543 _92541 _92542).
Proof. exact (TRANS (@lem6948506 _92541 _92543 _92542) (@lem6948511 _92543 _92541 _92542)). Qed.
Lemma lem6948528 (_92542 : nat) (_92543 : nat) : (term675 _92542 _92543) = (term675 _92542 _92543).
Proof. exact (eq_refl (term675 _92542 _92543)). Qed.
Lemma lem6948529 (_92543 : nat) (_92541 : nat) (_92542 : nat) : (term679 _92541 _92542 _92543) = (term676 _92543 _92541 _92542).
Proof. exact (MK_COMB (@lem6948528 _92542 _92543) (@lem6948527 _92543 _92541 _92542)). Qed.
Lemma lem6948540 (_92543 : nat) (_92541 : nat) (_92542 : nat) : ((term646 _92541 _92542 _92543) = (term679 _92541 _92542 _92543)) = ((term676 _92543 _92541 _92542) = (term676 _92543 _92541 _92542)).
Proof. exact (MK_COMB (@lem6948474 _92543 _92541 _92542) (@lem6948529 _92543 _92541 _92542)). Qed.
Lemma lem6948542 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6948543 (x : Prop) : (x = x) = True.
Proof. exact (@lem6948542 Prop x). Qed.
Lemma lem6948544 (_92543 : nat) (_92541 : nat) (_92542 : nat) : ((term676 _92543 _92541 _92542) = (term676 _92543 _92541 _92542)) = True.
Proof. exact (@lem6948543 (term676 _92543 _92541 _92542)). Qed.
Lemma lem6948545 (_92541 : nat) (_92542 : nat) (_92543 : nat) : ((term646 _92541 _92542 _92543) = (term679 _92541 _92542 _92543)) = True.
Proof. exact (TRANS (@lem6948540 _92543 _92541 _92542) (@lem6948544 _92543 _92541 _92542)). Qed.
Lemma lem6948546 (_92541 : nat) (_92542 : nat) (_92543 : nat) : True = ((term646 _92541 _92542 _92543) = (term679 _92541 _92542 _92543)).
Proof. exact (SYM (@lem6948545 _92541 _92542 _92543)). Qed.
Lemma lem6948547 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term646 _92541 _92542 _92543) = (term679 _92541 _92542 _92543).
Proof. exact (EQ_MP (@lem6948546 _92541 _92542 _92543) (@lem0)). Qed.
Lemma lem6948548 (_92541 : nat) (_92542 : nat) (_92543 : nat) (h1 : term319) : term679 _92541 _92542 _92543.
Proof. exact (EQ_MP (@lem6948547 _92541 _92542 _92543) (@lem6947707 _92541 _92542 _92543 h1)). Qed.
Lemma lem6948550 (b : Prop) (a : Prop) : (a \/ b) = (term680 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6948551 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term679 _92541 _92542 _92543) = (term681 _92541 _92542 _92543).
Proof. exact (@lem6948550 (term6 _92541 _92542 _92543) (Peano.le _92542 _92543)). Qed.
Lemma lem6948553 (a : Prop) (b : Prop) : (term682 a b) = (term683 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6948554 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term684 _92541 _92542 _92543) = (term685 _92541 _92542 _92543).
Proof. exact (@lem6948553 (term18 _92541) (term1 _92541 _92542 _92543)). Qed.
Lemma lem6948556 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6948557 (_92541 : nat) : (term686 _92541) = (term2 _92541).
Proof. exact (@lem6948556 (term2 _92541)). Qed.
Lemma lem6948558 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6948559 (_92541 : nat) : (term687 _92541) = (term688 _92541).
Proof. exact (MK_COMB (@lem6948558) (@lem6948557 _92541)). Qed.
Lemma lem6948561 (a : Prop) (b : Prop) : (term682 a b) = (term683 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6948562 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term689 _92541 _92542 _92543) = (term690 _92541 _92542 _92543).
Proof. exact (@lem6948561 (term18 _92542) (term27 _92541 _92542 _92543)). Qed.
Lemma lem6948564 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6948565 (_92542 : nat) : (term686 _92542) = (term2 _92542).
Proof. exact (@lem6948564 (term2 _92542)). Qed.
Lemma lem6948566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6948567 (_92542 : nat) : (term687 _92542) = (term688 _92542).
Proof. exact (MK_COMB (@lem6948566) (@lem6948565 _92542)). Qed.
Lemma lem6948569 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6948570 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term691 _92541 _92542 _92543) = (term3 _92541 _92542 _92543).
Proof. exact (@lem6948569 (term3 _92541 _92542 _92543)). Qed.
Lemma lem6948571 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term690 _92541 _92542 _92543) = (term8 _92541 _92542 _92543).
Proof. exact (MK_COMB (@lem6948567 _92542) (@lem6948570 _92541 _92542 _92543)). Qed.
Lemma lem6948572 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term689 _92541 _92542 _92543) = (term8 _92541 _92542 _92543).
Proof. exact (TRANS (@lem6948562 _92541 _92542 _92543) (@lem6948571 _92541 _92542 _92543)). Qed.
Lemma lem6948573 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term685 _92541 _92542 _92543) = (term15 _92541 _92542 _92543).
Proof. exact (MK_COMB (@lem6948559 _92541) (@lem6948572 _92541 _92542 _92543)). Qed.
Lemma lem6948574 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term684 _92541 _92542 _92543) = (term15 _92541 _92542 _92543).
Proof. exact (TRANS (@lem6948554 _92541 _92542 _92543) (@lem6948573 _92541 _92542 _92543)). Qed.
Lemma lem6948575 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6948576 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term692 _92541 _92542 _92543) = (term693 _92541 _92542 _92543).
Proof. exact (MK_COMB (@lem6948575) (@lem6948574 _92541 _92542 _92543)). Qed.
Lemma lem6948577 (_92542 : nat) (_92543 : nat) : (Peano.le _92542 _92543) = (Peano.le _92542 _92543).
Proof. exact (eq_refl (Peano.le _92542 _92543)). Qed.
Lemma lem6948578 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term681 _92541 _92542 _92543) = (term694 _92541 _92542 _92543).
Proof. exact (MK_COMB (@lem6948576 _92541 _92542 _92543) (@lem6948577 _92542 _92543)). Qed.
Lemma lem6948579 (_92541 : nat) (_92542 : nat) (_92543 : nat) : (term679 _92541 _92542 _92543) = (term694 _92541 _92542 _92543).
Proof. exact (TRANS (@lem6948551 _92541 _92542 _92543) (@lem6948578 _92541 _92542 _92543)). Qed.
Lemma lem6948581 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term503) (h2 : term591 A x s f x' b) : term695 A x s f b.
Proof. exact (conj (@lem6948353 A s f h1) (@lem6948360 A x s f x' b h2)). Qed.
Lemma lem6948582 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term503) (h2 : term591 A x s f x' b) : term696 A x s f b.
Proof. exact (conj (@lem6948345 A f x h1) (@lem6948581 A x s f x' b h1 h2)). Qed.
Lemma lem6948584 (_92541 : nat) (_92542 : nat) (_92543 : nat) (h1 : term319) : term694 _92541 _92542 _92543.
Proof. exact (EQ_MP (@lem6948579 _92541 _92542 _92543) (@lem6948548 _92541 _92542 _92543 h1)). Qed.
Lemma lem6948585 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term319) : term697 A x s f b.
Proof. exact (@lem6948584 (@I (A -> nat) f x) (@nsum A s f) b h1). Qed.
Lemma lem6948588 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) : term352 A s f b.
Proof. exact (@lem6948585 A x s f b h1 (@lem6948582 A x s f x' b h2 h3)). Qed.
Lemma lem6948589 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) : term698 A s f b.
Proof. exact (fun h0 : term635 A s f b => @lem6948588 A x s f x' b h1 h2 h3). Qed.
Lemma lem6948591 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948592 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term698 A s f b) = (term352 A s f b).
Proof. exact (@lem6948591 (term352 A s f b)). Qed.
Lemma lem6948593 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) : term352 A s f b.
Proof. exact (EQ_MP (@lem6948592 A s f b) (@lem6948589 A x s f x' b h1 h2 h3)). Qed.
Lemma lem6948596 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6948598 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term635 A s f b) = (term699 A s f b).
Proof. exact (@lem6948596 (term352 A s f b)). Qed.
Lemma lem6948601 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term635 A s f b) : term699 A s f b.
Proof. exact (EQ_MP (@lem6948598 A s f b) (@lem6947669 A s f b h1)). Qed.
Lemma lem6948604 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : False.
Proof. exact (@lem6948601 A s f b h3 (@lem6948593 A x s f x' b h1 h2 h4)). Qed.
Lemma lem6948605 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : term700.
Proof. exact (fun h0 : ~ False => @lem6948604 A x s f x' b h1 h2 h3 h4). Qed.
Lemma lem6948607 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948608 : term700 = False.
Proof. exact (@lem6948607 False). Qed.
Lemma lem6948609 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : False.
Proof. exact (EQ_MP (@lem6948608) (@lem6948605 A x s f x' b h1 h2 h3 h4)). Qed.
Lemma lem6948611 (_92548 : nat) (h1 : term503) : term2 _92548.
Proof. exact (EQ_MP (@lem6947580 _92548) (@lem6947579 _92548 h1)). Qed.
Lemma lem6948612 {A : Type'} (f : A -> nat) (x : A) (h1 : term503) : term655 A f x.
Proof. exact (@lem6948611 (@I (A -> nat) f x) h1). Qed.
Lemma lem6948613 {A : Type'} (f : A -> nat) (x : A) (h1 : term503) : term656 A f x.
Proof. exact (fun h0 : term657 A f x => @lem6948612 A f x h1). Qed.
Lemma lem6948615 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948616 {A : Type'} (f : A -> nat) (x : A) : (term656 A f x) = (term655 A f x).
Proof. exact (@lem6948615 (term655 A f x)). Qed.
Lemma lem6948617 {A : Type'} (f : A -> nat) (x : A) (h1 : term503) : term655 A f x.
Proof. exact (EQ_MP (@lem6948616 A f x) (@lem6948613 A f x h1)). Qed.
Lemma lem6948619 (_92548 : nat) (h1 : term503) : term2 _92548.
Proof. exact (EQ_MP (@lem6947580 _92548) (@lem6947579 _92548 h1)). Qed.
Lemma lem6948620 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term503) : term659 A s f.
Proof. exact (@lem6948619 (@nsum A s f) h1). Qed.
Lemma lem6948621 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term503) : term660 A s f.
Proof. exact (fun h0 : term661 A s f => @lem6948620 A s f h1). Qed.
Lemma lem6948623 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948624 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term660 A s f) = (term659 A s f).
Proof. exact (@lem6948623 (term659 A s f)). Qed.
Lemma lem6948625 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term503) : term659 A s f.
Proof. exact (EQ_MP (@lem6948624 A s f) (@lem6948621 A s f h1)). Qed.
Lemma lem6948627 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term616 A x s f b.
Proof. exact (proj1 (@lem6947224 A x s f x' b h1)). Qed.
Lemma lem6948628 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term662 A x s f b.
Proof. exact (fun h0 : term663 A x s f b => @lem6948627 A x s f x' b h1). Qed.
Lemma lem6948630 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948631 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term662 A x s f b) = (term616 A x s f b).
Proof. exact (@lem6948630 (term616 A x s f b)). Qed.
Lemma lem6948632 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term616 A x s f b.
Proof. exact (EQ_MP (@lem6948631 A x s f b) (@lem6948628 A x s f x' b h1)). Qed.
Lemma lem6948648 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948649 (_92546 : nat) (_92545 : nat) (_92547 : nat) : (term649 _92546 _92545 _92547) = (term701 _92546 _92545 _92547).
Proof. exact (@lem6948648 (term27 _92545 _92546 _92547) (term18 _92546) (Peano.le _92545 _92547)). Qed.
Lemma lem6948663 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6948664 (_92545 : nat) (_92547 : nat) (_92546 : nat) : (term702 _92546 _92545 _92547) = (term703 _92545 _92547 _92546).
Proof. exact (@lem6948663 (Peano.le _92545 _92547) (term18 _92546)). Qed.
Lemma lem6948670 (_92545 : nat) (_92546 : nat) (_92547 : nat) : (term667 _92545 _92546 _92547) = (term667 _92545 _92546 _92547).
Proof. exact (eq_refl (term667 _92545 _92546 _92547)). Qed.
Lemma lem6948671 (_92545 : nat) (_92547 : nat) (_92546 : nat) : (term701 _92546 _92545 _92547) = (term704 _92545 _92547 _92546).
Proof. exact (MK_COMB (@lem6948670 _92545 _92546 _92547) (@lem6948664 _92545 _92547 _92546)). Qed.
Lemma lem6948675 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948676 (_92545 : nat) (_92547 : nat) (_92546 : nat) : (term704 _92545 _92547 _92546) = (term705 _92545 _92547 _92546).
Proof. exact (@lem6948675 (Peano.le _92545 _92547) (term27 _92545 _92546 _92547) (term18 _92546)). Qed.
Lemma lem6948692 (_92545 : nat) (_92547 : nat) (_92546 : nat) : (term701 _92546 _92545 _92547) = (term705 _92545 _92547 _92546).
Proof. exact (TRANS (@lem6948671 _92545 _92547 _92546) (@lem6948676 _92545 _92547 _92546)). Qed.
Lemma lem6948693 (_92545 : nat) (_92547 : nat) (_92546 : nat) : (term649 _92546 _92545 _92547) = (term705 _92545 _92547 _92546).
Proof. exact (TRANS (@lem6948649 _92546 _92545 _92547) (@lem6948692 _92545 _92547 _92546)). Qed.
Lemma lem6948694 (_92545 : nat) : (term4 _92545) = (term4 _92545).
Proof. exact (eq_refl (term4 _92545)). Qed.
Lemma lem6948695 (_92545 : nat) (_92547 : nat) (_92546 : nat) : (term650 _92546 _92545 _92547) = (term706 _92545 _92547 _92546).
Proof. exact (MK_COMB (@lem6948694 _92545) (@lem6948693 _92545 _92547 _92546)). Qed.
Lemma lem6948699 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948700 (_92545 : nat) (_92547 : nat) (_92546 : nat) : (term706 _92545 _92547 _92546) = (term707 _92545 _92547 _92546).
Proof. exact (@lem6948699 (Peano.le _92545 _92547) (term18 _92545) (term672 _92545 _92547 _92546)). Qed.
Lemma lem6948714 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948715 (_92547 : nat) (_92545 : nat) (_92546 : nat) : (term673 _92545 _92547 _92546) = (term674 _92547 _92545 _92546).
Proof. exact (@lem6948714 (term27 _92545 _92546 _92547) (term18 _92545) (term18 _92546)). Qed.
Lemma lem6948731 (_92545 : nat) (_92547 : nat) : (term675 _92545 _92547) = (term675 _92545 _92547).
Proof. exact (eq_refl (term675 _92545 _92547)). Qed.
Lemma lem6948732 (_92547 : nat) (_92545 : nat) (_92546 : nat) : (term707 _92545 _92547 _92546) = (term708 _92547 _92545 _92546).
Proof. exact (MK_COMB (@lem6948731 _92545 _92547) (@lem6948715 _92547 _92545 _92546)). Qed.
Lemma lem6948743 (_92547 : nat) (_92545 : nat) (_92546 : nat) : (term706 _92545 _92547 _92546) = (term708 _92547 _92545 _92546).
Proof. exact (TRANS (@lem6948700 _92545 _92547 _92546) (@lem6948732 _92547 _92545 _92546)). Qed.
Lemma lem6948744 (_92547 : nat) (_92545 : nat) (_92546 : nat) : (term650 _92546 _92545 _92547) = (term708 _92547 _92545 _92546).
Proof. exact (TRANS (@lem6948695 _92545 _92547 _92546) (@lem6948743 _92547 _92545 _92546)). Qed.
Lemma lem6948745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6948746 (_92547 : nat) (_92545 : nat) (_92546 : nat) : (term709 _92546 _92545 _92547) = (term710 _92547 _92545 _92546).
Proof. exact (MK_COMB (@lem6948745) (@lem6948744 _92547 _92545 _92546)). Qed.
Lemma lem6948770 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6948771 (_92545 : nat) (_92547 : nat) (_92546 : nat) : (term1 _92545 _92546 _92547) = (term672 _92545 _92547 _92546).
Proof. exact (@lem6948770 (term27 _92545 _92546 _92547) (term18 _92546)). Qed.
Lemma lem6948777 (_92545 : nat) : (term4 _92545) = (term4 _92545).
Proof. exact (eq_refl (term4 _92545)). Qed.
Lemma lem6948778 (_92545 : nat) (_92547 : nat) (_92546 : nat) : (term6 _92545 _92546 _92547) = (term673 _92545 _92547 _92546).
Proof. exact (MK_COMB (@lem6948777 _92545) (@lem6948771 _92545 _92547 _92546)). Qed.
Lemma lem6948782 (q : Prop) (p : Prop) (r : Prop) : (term315 p q r) = (term315 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6948783 (_92547 : nat) (_92545 : nat) (_92546 : nat) : (term673 _92545 _92547 _92546) = (term674 _92547 _92545 _92546).
Proof. exact (@lem6948782 (term27 _92545 _92546 _92547) (term18 _92545) (term18 _92546)). Qed.
Lemma lem6948799 (_92547 : nat) (_92545 : nat) (_92546 : nat) : (term6 _92545 _92546 _92547) = (term674 _92547 _92545 _92546).
Proof. exact (TRANS (@lem6948778 _92545 _92547 _92546) (@lem6948783 _92547 _92545 _92546)). Qed.
Lemma lem6948800 (_92545 : nat) (_92547 : nat) : (term675 _92545 _92547) = (term675 _92545 _92547).
Proof. exact (eq_refl (term675 _92545 _92547)). Qed.
Lemma lem6948801 (_92547 : nat) (_92545 : nat) (_92546 : nat) : (term711 _92545 _92546 _92547) = (term708 _92547 _92545 _92546).
Proof. exact (MK_COMB (@lem6948800 _92545 _92547) (@lem6948799 _92547 _92545 _92546)). Qed.
Lemma lem6948812 (_92547 : nat) (_92545 : nat) (_92546 : nat) : ((term650 _92546 _92545 _92547) = (term711 _92545 _92546 _92547)) = ((term708 _92547 _92545 _92546) = (term708 _92547 _92545 _92546)).
Proof. exact (MK_COMB (@lem6948746 _92547 _92545 _92546) (@lem6948801 _92547 _92545 _92546)). Qed.
Lemma lem6948814 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6948815 (x : Prop) : (x = x) = True.
Proof. exact (@lem6948814 Prop x). Qed.
Lemma lem6948816 (_92547 : nat) (_92545 : nat) (_92546 : nat) : ((term708 _92547 _92545 _92546) = (term708 _92547 _92545 _92546)) = True.
Proof. exact (@lem6948815 (term708 _92547 _92545 _92546)). Qed.
Lemma lem6948817 (_92545 : nat) (_92546 : nat) (_92547 : nat) : ((term650 _92546 _92545 _92547) = (term711 _92545 _92546 _92547)) = True.
Proof. exact (TRANS (@lem6948812 _92547 _92545 _92546) (@lem6948816 _92547 _92545 _92546)). Qed.
Lemma lem6948818 (_92545 : nat) (_92546 : nat) (_92547 : nat) : True = ((term650 _92546 _92545 _92547) = (term711 _92545 _92546 _92547)).
Proof. exact (SYM (@lem6948817 _92545 _92546 _92547)). Qed.
Lemma lem6948819 (_92545 : nat) (_92546 : nat) (_92547 : nat) : (term650 _92546 _92545 _92547) = (term711 _92545 _92546 _92547).
Proof. exact (EQ_MP (@lem6948818 _92545 _92546 _92547) (@lem0)). Qed.
Lemma lem6948820 (_92545 : nat) (_92546 : nat) (_92547 : nat) (h1 : term319) : term711 _92545 _92546 _92547.
Proof. exact (EQ_MP (@lem6948819 _92545 _92546 _92547) (@lem6948051 _92546 _92545 _92547 h1)). Qed.
Lemma lem6948822 (b : Prop) (a : Prop) : (a \/ b) = (term680 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6948823 (_92546 : nat) (_92545 : nat) (_92547 : nat) : (term711 _92545 _92546 _92547) = (term712 _92546 _92545 _92547).
Proof. exact (@lem6948822 (term6 _92545 _92546 _92547) (Peano.le _92545 _92547)). Qed.
Lemma lem6948825 (a : Prop) (b : Prop) : (term682 a b) = (term683 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6948826 (_92545 : nat) (_92546 : nat) (_92547 : nat) : (term684 _92545 _92546 _92547) = (term685 _92545 _92546 _92547).
Proof. exact (@lem6948825 (term18 _92545) (term1 _92545 _92546 _92547)). Qed.
Lemma lem6948828 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6948829 (_92545 : nat) : (term686 _92545) = (term2 _92545).
Proof. exact (@lem6948828 (term2 _92545)). Qed.
Lemma lem6948830 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6948831 (_92545 : nat) : (term687 _92545) = (term688 _92545).
Proof. exact (MK_COMB (@lem6948830) (@lem6948829 _92545)). Qed.
Lemma lem6948833 (a : Prop) (b : Prop) : (term682 a b) = (term683 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6948834 (_92545 : nat) (_92546 : nat) (_92547 : nat) : (term689 _92545 _92546 _92547) = (term690 _92545 _92546 _92547).
Proof. exact (@lem6948833 (term18 _92546) (term27 _92545 _92546 _92547)). Qed.
Lemma lem6948836 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6948837 (_92546 : nat) : (term686 _92546) = (term2 _92546).
Proof. exact (@lem6948836 (term2 _92546)). Qed.
Lemma lem6948838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6948839 (_92546 : nat) : (term687 _92546) = (term688 _92546).
Proof. exact (MK_COMB (@lem6948838) (@lem6948837 _92546)). Qed.
Lemma lem6948841 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6948842 (_92545 : nat) (_92546 : nat) (_92547 : nat) : (term691 _92545 _92546 _92547) = (term3 _92545 _92546 _92547).
Proof. exact (@lem6948841 (term3 _92545 _92546 _92547)). Qed.
Lemma lem6948843 (_92545 : nat) (_92546 : nat) (_92547 : nat) : (term690 _92545 _92546 _92547) = (term8 _92545 _92546 _92547).
Proof. exact (MK_COMB (@lem6948839 _92546) (@lem6948842 _92545 _92546 _92547)). Qed.
Lemma lem6948844 (_92545 : nat) (_92546 : nat) (_92547 : nat) : (term689 _92545 _92546 _92547) = (term8 _92545 _92546 _92547).
Proof. exact (TRANS (@lem6948834 _92545 _92546 _92547) (@lem6948843 _92545 _92546 _92547)). Qed.
Lemma lem6948845 (_92545 : nat) (_92546 : nat) (_92547 : nat) : (term685 _92545 _92546 _92547) = (term15 _92545 _92546 _92547).
Proof. exact (MK_COMB (@lem6948831 _92545) (@lem6948844 _92545 _92546 _92547)). Qed.
Lemma lem6948846 (_92545 : nat) (_92546 : nat) (_92547 : nat) : (term684 _92545 _92546 _92547) = (term15 _92545 _92546 _92547).
Proof. exact (TRANS (@lem6948826 _92545 _92546 _92547) (@lem6948845 _92545 _92546 _92547)). Qed.
Lemma lem6948847 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6948848 (_92545 : nat) (_92546 : nat) (_92547 : nat) : (term692 _92545 _92546 _92547) = (term693 _92545 _92546 _92547).
Proof. exact (MK_COMB (@lem6948847) (@lem6948846 _92545 _92546 _92547)). Qed.
Lemma lem6948849 (_92545 : nat) (_92547 : nat) : (Peano.le _92545 _92547) = (Peano.le _92545 _92547).
Proof. exact (eq_refl (Peano.le _92545 _92547)). Qed.
Lemma lem6948850 (_92546 : nat) (_92545 : nat) (_92547 : nat) : (term712 _92546 _92545 _92547) = (term713 _92546 _92545 _92547).
Proof. exact (MK_COMB (@lem6948848 _92545 _92546 _92547) (@lem6948849 _92545 _92547)). Qed.
Lemma lem6948851 (_92546 : nat) (_92545 : nat) (_92547 : nat) : (term711 _92545 _92546 _92547) = (term713 _92546 _92545 _92547).
Proof. exact (TRANS (@lem6948823 _92546 _92545 _92547) (@lem6948850 _92546 _92545 _92547)). Qed.
Lemma lem6948853 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term503) (h2 : term591 A x s f x' b) : term695 A x s f b.
Proof. exact (conj (@lem6948625 A s f h1) (@lem6948632 A x s f x' b h2)). Qed.
Lemma lem6948854 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term503) (h2 : term591 A x s f x' b) : term696 A x s f b.
Proof. exact (conj (@lem6948617 A f x h1) (@lem6948853 A x s f x' b h1 h2)). Qed.
Lemma lem6948856 (_92546 : nat) (_92545 : nat) (_92547 : nat) (h1 : term319) : term713 _92546 _92545 _92547.
Proof. exact (EQ_MP (@lem6948851 _92546 _92545 _92547) (@lem6948820 _92545 _92546 _92547 h1)). Qed.
Lemma lem6948857 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) (h1 : term319) : term714 A s f x b.
Proof. exact (@lem6948856 (@nsum A s f) (@I (A -> nat) f x) b h1). Qed.
Lemma lem6948860 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) : term607 A f x b.
Proof. exact (@lem6948857 A s f x b h1 (@lem6948854 A x s f x' b h2 h3)). Qed.
Lemma lem6948861 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) : term715 A f x b.
Proof. exact (fun h0 : term609 A f x b => @lem6948860 A x s f x' b h1 h2 h3). Qed.
Lemma lem6948863 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948864 {A : Type'} (f : A -> nat) (x : A) (b : nat) : (term715 A f x b) = (term607 A f x b).
Proof. exact (@lem6948863 (term607 A f x b)). Qed.
Lemma lem6948865 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) : term607 A f x b.
Proof. exact (EQ_MP (@lem6948864 A f x b) (@lem6948861 A x s f x' b h1 h2 h3)). Qed.
Lemma lem6948868 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6948870 {A : Type'} (f : A -> nat) (x : A) (b : nat) : (term609 A f x b) = (term716 A f x b).
Proof. exact (@lem6948868 (term607 A f x b)). Qed.
Lemma lem6948873 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : term591 A x s f x' b) (h2 : x' = x) : term716 A f x b.
Proof. exact (EQ_MP (@lem6948870 A f x b) (@lem6947995 A s f b x' x h1 h2)). Qed.
Lemma lem6948876 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) (h4 : x' = x) : False.
Proof. exact (@lem6948873 A s f b x' x h3 h4 (@lem6948865 A x s f x' b h1 h2 h3)). Qed.
Lemma lem6948877 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) (h4 : x' = x) : term700.
Proof. exact (fun h0 : ~ False => @lem6948876 A s f b x' x h1 h2 h3 h4). Qed.
Lemma lem6948879 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948880 : term700 = False.
Proof. exact (@lem6948879 False). Qed.
Lemma lem6948883 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : @IN A x' s.
Proof. exact (h1). Qed.
Lemma lem6948884 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : term717 A x' s.
Proof. exact (fun h0 : term434 A x' s => @lem6948883 A x' s h1). Qed.
Lemma lem6948886 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948887 {A : Type'} (x' : A) (s : A -> Prop) : (term717 A x' s) = (@IN A x' s).
Proof. exact (@lem6948886 (@IN A x' s)). Qed.
Lemma lem6948888 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : @IN A x' s.
Proof. exact (EQ_MP (@lem6948887 A x' s) (@lem6948884 A x' s h1)). Qed.
Lemma lem6948894 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6948895 {A : Type'} (f : A -> nat) (b : nat) (_92554 : A) (s : A -> Prop) : (term620 A s f _92554 b) = (term718 A f b _92554 s).
Proof. exact (@lem6948894 (term607 A f _92554 b) (term434 A _92554 s)). Qed.
Lemma lem6948901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6948902 {A : Type'} (f : A -> nat) (b : nat) (_92554 : A) (s : A -> Prop) : (term719 A s f _92554 b) = (term720 A f b _92554 s).
Proof. exact (MK_COMB (@lem6948901) (@lem6948895 A f b _92554 s)). Qed.
Lemma lem6948908 {A : Type'} (f : A -> nat) (b : nat) (_92554 : A) (s : A -> Prop) : (term718 A f b _92554 s) = (term718 A f b _92554 s).
Proof. exact (eq_refl (term718 A f b _92554 s)). Qed.
Lemma lem6948909 {A : Type'} (f : A -> nat) (b : nat) (_92554 : A) (s : A -> Prop) : ((term620 A s f _92554 b) = (term718 A f b _92554 s)) = ((term718 A f b _92554 s) = (term718 A f b _92554 s)).
Proof. exact (MK_COMB (@lem6948902 A f b _92554 s) (@lem6948908 A f b _92554 s)). Qed.
Lemma lem6948911 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6948912 (x : Prop) : (x = x) = True.
Proof. exact (@lem6948911 Prop x). Qed.
Lemma lem6948913 {A : Type'} (f : A -> nat) (b : nat) (_92554 : A) (s : A -> Prop) : ((term718 A f b _92554 s) = (term718 A f b _92554 s)) = True.
Proof. exact (@lem6948912 (term718 A f b _92554 s)). Qed.
Lemma lem6948914 {A : Type'} (f : A -> nat) (b : nat) (_92554 : A) (s : A -> Prop) : ((term620 A s f _92554 b) = (term718 A f b _92554 s)) = True.
Proof. exact (TRANS (@lem6948909 A f b _92554 s) (@lem6948913 A f b _92554 s)). Qed.
Lemma lem6948915 {A : Type'} (f : A -> nat) (b : nat) (_92554 : A) (s : A -> Prop) : True = ((term620 A s f _92554 b) = (term718 A f b _92554 s)).
Proof. exact (SYM (@lem6948914 A f b _92554 s)). Qed.
Lemma lem6948916 {A : Type'} (f : A -> nat) (b : nat) (_92554 : A) (s : A -> Prop) : (term620 A s f _92554 b) = (term718 A f b _92554 s).
Proof. exact (EQ_MP (@lem6948915 A f b _92554 s) (@lem0)). Qed.
Lemma lem6948917 {A : Type'} (_92554 : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term622 A s f b) : term718 A f b _92554 s.
Proof. exact (EQ_MP (@lem6948916 A f b _92554 s) (@lem6947777 A _92554 s f b h1)). Qed.
Lemma lem6948919 (b : Prop) (a : Prop) : (a \/ b) = (term680 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6948920 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92554 : A) (b : nat) : (term718 A f b _92554 s) = (term721 A s f _92554 b).
Proof. exact (@lem6948919 (term434 A _92554 s) (term607 A f _92554 b)). Qed.
Lemma lem6948922 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6948923 {A : Type'} (_92554 : A) (s : A -> Prop) : (term722 A _92554 s) = (@IN A _92554 s).
Proof. exact (@lem6948922 (@IN A _92554 s)). Qed.
Lemma lem6948924 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6948925 {A : Type'} (_92554 : A) (s : A -> Prop) : (term723 A _92554 s) = (term724 A _92554 s).
Proof. exact (MK_COMB (@lem6948924) (@lem6948923 A _92554 s)). Qed.
Lemma lem6948926 {A : Type'} (f : A -> nat) (_92554 : A) (b : nat) : (term607 A f _92554 b) = (term607 A f _92554 b).
Proof. exact (eq_refl (term607 A f _92554 b)). Qed.
Lemma lem6948927 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92554 : A) (b : nat) : (term721 A s f _92554 b) = (term725 A s f _92554 b).
Proof. exact (MK_COMB (@lem6948925 A _92554 s) (@lem6948926 A f _92554 b)). Qed.
Lemma lem6948928 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92554 : A) (b : nat) : (term718 A f b _92554 s) = (term725 A s f _92554 b).
Proof. exact (TRANS (@lem6948920 A s f _92554 b) (@lem6948927 A s f _92554 b)). Qed.
Lemma lem6948931 {A : Type'} (_92554 : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term622 A s f b) : term725 A s f _92554 b.
Proof. exact (EQ_MP (@lem6948928 A s f _92554 b) (@lem6948917 A _92554 s f b h1)). Qed.
Lemma lem6948932 {A : Type'} (_92554 : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term622 A s f b) : term725 A s f _92554 b.
Proof. exact (@lem6948931 A _92554 s f b h1). Qed.
Lemma lem6948933 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term622 A s f b) : term725 A s f x' b.
Proof. exact (@lem6948932 A x' s f b h1). Qed.
Lemma lem6948936 {A : Type'} (f : A -> nat) (b : nat) (x' : A) (s : A -> Prop) (h1 : term622 A s f b) (h2 : @IN A x' s) : term607 A f x' b.
Proof. exact (@lem6948933 A x' s f b h1 (@lem6948888 A x' s h2)). Qed.
Lemma lem6948937 {A : Type'} (f : A -> nat) (b : nat) (x' : A) (s : A -> Prop) (h1 : term622 A s f b) (h2 : @IN A x' s) : term715 A f x' b.
Proof. exact (fun h0 : term609 A f x' b => @lem6948936 A f b x' s h1 h2). Qed.
Lemma lem6948939 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948940 {A : Type'} (f : A -> nat) (x' : A) (b : nat) : (term715 A f x' b) = (term607 A f x' b).
Proof. exact (@lem6948939 (term607 A f x' b)). Qed.
Lemma lem6948941 {A : Type'} (f : A -> nat) (b : nat) (x' : A) (s : A -> Prop) (h1 : term622 A s f b) (h2 : @IN A x' s) : term607 A f x' b.
Proof. exact (EQ_MP (@lem6948940 A f x' b) (@lem6948937 A f b x' s h1 h2)). Qed.
Lemma lem6948944 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6948946 {A : Type'} (f : A -> nat) (x' : A) (b : nat) : (term609 A f x' b) = (term716 A f x' b).
Proof. exact (@lem6948944 (term607 A f x' b)). Qed.
Lemma lem6948949 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term591 A x s f x' b) : term716 A f x' b.
Proof. exact (EQ_MP (@lem6948946 A f x' b) (@lem6947767 A x s f x' b h1)). Qed.
Lemma lem6948952 {A : Type'} (x : A) (f : A -> nat) (b : nat) (x' : A) (s : A -> Prop) (h1 : term622 A s f b) (h2 : term591 A x s f x' b) (h3 : @IN A x' s) : False.
Proof. exact (@lem6948949 A x s f x' b h2 (@lem6948941 A f b x' s h1 h3)). Qed.
Lemma lem6948953 {A : Type'} (x : A) (f : A -> nat) (b : nat) (x' : A) (s : A -> Prop) (h1 : term622 A s f b) (h2 : term591 A x s f x' b) (h3 : @IN A x' s) : term700.
Proof. exact (fun h0 : ~ False => @lem6948952 A x f b x' s h1 h2 h3). Qed.
Lemma lem6948955 (p : Prop) : (term658 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6948956 : term700 = False.
Proof. exact (@lem6948955 False). Qed.
Lemma lem6948957 {A : Type'} (x : A) (f : A -> nat) (b : nat) (x' : A) (s : A -> Prop) (h1 : term622 A s f b) (h2 : term591 A x s f x' b) (h3 : @IN A x' s) : False.
Proof. exact (EQ_MP (@lem6948956) (@lem6948953 A x f b x' s h1 h2 h3)). Qed.
Lemma lem6948958 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) (h4 : x' = x) : False.
Proof. exact (EQ_MP (@lem6948880) (@lem6948877 A s f b x' x h1 h2 h3 h4)). Qed.
Lemma lem6948959 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : (term635 A s f b) = False.
Proof. exact (prop_ext (fun h5 : term635 A s f b => @lem6948337 A x s f x' b h1 h2 h3 h4) (fun h5 : False => @lem6947912 A s f b h3)). Qed.
Lemma lem6948961 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : False.
Proof. exact (EQ_MP (@lem6948959 A x s f x' b h1 h2 h3 h4) (@lem6947912 A s f b h3)). Qed.
Lemma lem6948962 {A : Type'} (x : A) (f : A -> nat) (b : nat) (x' : A) (s : A -> Prop) (h1 : term622 A s f b) (h2 : term591 A x s f x' b) (h3 : @IN A x' s) : (@IN A x' s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x' s => @lem6948957 A x f b x' s h1 h2 h3) (fun h4 : False => @lem6947779 A x' s h3)). Qed.
Lemma lem6948963 {A : Type'} (x : A) (f : A -> nat) (b : nat) (x' : A) (s : A -> Prop) (h1 : term622 A s f b) (h2 : term591 A x s f x' b) (h3 : @IN A x' s) : False.
Proof. exact (EQ_MP (@lem6948962 A x f b x' s h1 h2 h3) (@lem6947779 A x' s h3)). Qed.
Lemma lem6948964 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) (h4 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h5 : x' = x => @lem6948958 A s f b x' x h1 h2 h3 h4) (fun h5 : False => @lem6947725 A x' x h4)). Qed.
Lemma lem6948965 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) (h4 : x' = x) : False.
Proof. exact (EQ_MP (@lem6948964 A s f b x' x h1 h2 h3 h4) (@lem6947725 A x' x h4)). Qed.
Lemma lem6948966 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : (term635 A s f b) = False.
Proof. exact (prop_ext (fun h5 : term635 A s f b => @lem6948609 A x s f x' b h1 h2 h3 h4) (fun h5 : False => @lem6947669 A s f b h3)). Qed.
Lemma lem6948967 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : False.
Proof. exact (EQ_MP (@lem6948966 A x s f x' b h1 h2 h3 h4) (@lem6947669 A s f b h3)). Qed.
Lemma lem6948968 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : (term635 A s f b) = False.
Proof. exact (prop_ext (fun h5 : term635 A s f b => @lem6948961 A x s f x' b h1 h2 h3 h4) (fun h5 : False => @lem6947619 A s f b h3)). Qed.
Lemma lem6948969 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : False.
Proof. exact (EQ_MP (@lem6948968 A x s f x' b h1 h2 h3 h4) (@lem6947619 A s f b h3)). Qed.
Lemma lem6948970 {A : Type'} (x : A) (f : A -> nat) (b : nat) (x' : A) (s : A -> Prop) (h1 : term622 A s f b) (h2 : term591 A x s f x' b) (h3 : @IN A x' s) : (@IN A x' s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x' s => @lem6948963 A x f b x' s h1 h2 h3) (fun h4 : False => @lem6947545 A x' s h3)). Qed.
Lemma lem6948971 {A : Type'} (x : A) (f : A -> nat) (b : nat) (x' : A) (s : A -> Prop) (h1 : term622 A s f b) (h2 : term591 A x s f x' b) (h3 : @IN A x' s) : False.
Proof. exact (EQ_MP (@lem6948970 A x f b x' s h1 h2 h3) (@lem6947545 A x' s h3)). Qed.
Lemma lem6948972 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) (h4 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h5 : x' = x => @lem6948965 A s f b x' x h1 h2 h3 h4) (fun h5 : False => @lem6947464 A x' x h4)). Qed.
Lemma lem6948973 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) (h4 : x' = x) : False.
Proof. exact (EQ_MP (@lem6948972 A s f b x' x h1 h2 h3 h4) (@lem6947464 A x' x h4)). Qed.
Lemma lem6948974 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : (term635 A s f b) = False.
Proof. exact (prop_ext (fun h5 : term635 A s f b => @lem6948967 A x s f x' b h1 h2 h3 h4) (fun h5 : False => @lem6947379 A s f b h3)). Qed.
Lemma lem6948975 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : False.
Proof. exact (EQ_MP (@lem6948974 A x s f x' b h1 h2 h3 h4) (@lem6947379 A s f b h3)). Qed.
Lemma lem6948976 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : (term635 A s f b) = False.
Proof. exact (prop_ext (fun h5 : term635 A s f b => @lem6948969 A x s f x' b h1 h2 h3 h4) (fun h5 : False => @lem6947307 A s f b h3)). Qed.
Lemma lem6948977 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : False.
Proof. exact (EQ_MP (@lem6948976 A x s f x' b h1 h2 h3 h4) (@lem6947307 A s f b h3)). Qed.
Lemma lem6948978 {A : Type'} (x : A) (f : A -> nat) (b : nat) (x' : A) (s : A -> Prop) (h1 : term622 A s f b) (h2 : term591 A x s f x' b) (h3 : @IN A x' s) : (@IN A x' s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x' s => @lem6948971 A x f b x' s h1 h2 h3) (fun h4 : False => @lem6947545 A x' s h3)). Qed.
Lemma lem6948979 {A : Type'} (x : A) (f : A -> nat) (b : nat) (x' : A) (s : A -> Prop) (h1 : term622 A s f b) (h2 : term591 A x s f x' b) (h3 : @IN A x' s) : False.
Proof. exact (EQ_MP (@lem6948978 A x f b x' s h1 h2 h3) (@lem6947545 A x' s h3)). Qed.
Lemma lem6948980 {A : Type'} (x : A) (f : A -> nat) (b : nat) (x' : A) (s : A -> Prop) (h1 : term622 A s f b) (h2 : term591 A x s f x' b) (h3 : @IN A x' s) : (term622 A s f b) = False.
Proof. exact (prop_ext (fun h4 : term622 A s f b => @lem6948979 A x f b x' s h1 h2 h3) (fun h4 : False => @lem6947541 A s f b h1)). Qed.
Lemma lem6948981 {A : Type'} (x : A) (f : A -> nat) (b : nat) (x' : A) (s : A -> Prop) (h1 : term622 A s f b) (h2 : term591 A x s f x' b) (h3 : @IN A x' s) : False.
Proof. exact (EQ_MP (@lem6948980 A x f b x' s h1 h2 h3) (@lem6947541 A s f b h1)). Qed.
Lemma lem6948982 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) (h4 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h5 : x' = x => @lem6948973 A s f b x' x h1 h2 h3 h4) (fun h5 : False => @lem6947464 A x' x h4)). Qed.
Lemma lem6948983 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) (h4 : x' = x) : False.
Proof. exact (EQ_MP (@lem6948982 A s f b x' x h1 h2 h3 h4) (@lem6947464 A x' x h4)). Qed.
Lemma lem6948984 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) (h4 : x' = x) : term503 = False.
Proof. exact (prop_ext (fun h5 : term503 => @lem6948983 A s f b x' x h1 h2 h3 h4) (fun h5 : False => @lem6947431 h2)). Qed.
Lemma lem6948985 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x' : A) (x : A) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) (h4 : x' = x) : False.
Proof. exact (EQ_MP (@lem6948984 A s f b x' x h1 h2 h3 h4) (@lem6947431 h2)). Qed.
Lemma lem6948986 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : (term635 A s f b) = False.
Proof. exact (prop_ext (fun h5 : term635 A s f b => @lem6948975 A x s f x' b h1 h2 h3 h4) (fun h5 : False => @lem6947379 A s f b h3)). Qed.
Lemma lem6948987 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : False.
Proof. exact (EQ_MP (@lem6948986 A x s f x' b h1 h2 h3 h4) (@lem6947379 A s f b h3)). Qed.
Lemma lem6948988 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : term503 = False.
Proof. exact (prop_ext (fun h5 : term503 => @lem6948987 A x s f x' b h1 h2 h3 h4) (fun h5 : False => @lem6947359 h2)). Qed.
Lemma lem6948989 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : False.
Proof. exact (EQ_MP (@lem6948988 A x s f x' b h1 h2 h3 h4) (@lem6947359 h2)). Qed.
Lemma lem6948990 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : (term635 A s f b) = False.
Proof. exact (prop_ext (fun h5 : term635 A s f b => @lem6948977 A x s f x' b h1 h2 h3 h4) (fun h5 : False => @lem6947307 A s f b h3)). Qed.
Lemma lem6948991 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : False.
Proof. exact (EQ_MP (@lem6948990 A x s f x' b h1 h2 h3 h4) (@lem6947307 A s f b h3)). Qed.
Lemma lem6948992 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : term503 = False.
Proof. exact (prop_ext (fun h5 : term503 => @lem6948991 A x s f x' b h1 h2 h3 h4) (fun h5 : False => @lem6947287 h2)). Qed.
Lemma lem6948993 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : False.
Proof. exact (EQ_MP (@lem6948992 A x s f x' b h1 h2 h3 h4) (@lem6947287 h2)). Qed.
Lemma lem6948994 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term622 A s f b) (h2 : term319) (h3 : term503) (h4 : term591 A x s f x' b) : False.
Proof. exact (or_elim (@lem6947229 A x s f x' b h4) (fun h0 : x' = x => @lem6948985 A s f b x' x h2 h3 h4 h0) (fun h0 : @IN A x' s => @lem6948981 A x f b x' s h1 h4 h0)). Qed.
Lemma lem6948995 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term635 A s f b) (h4 : term591 A x s f x' b) : False.
Proof. exact (or_elim (@lem6947229 A x s f x' b h4) (fun h0 : x' = x => @lem6948993 A x s f x' b h1 h2 h3 h4) (fun h0 : @IN A x' s => @lem6948989 A x s f x' b h1 h2 h3 h4)). Qed.
Lemma lem6948996 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) : False.
Proof. exact (or_elim (@lem6947231 A x s f x' b h3) (fun h0 : term635 A s f b => @lem6948995 A x s f x' b h1 h2 h0 h3) (fun h0 : term622 A s f b => @lem6948994 A x s f x' b h0 h1 h2 h3)). Qed.
Lemma lem6948997 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) : term503 = False.
Proof. exact (prop_ext (fun h4 : term503 => @lem6948996 A x s f x' b h1 h2 h3) (fun h4 : False => @lem6947113 h2)). Qed.
Lemma lem6948998 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (x' : A) (b : nat) (h1 : term319) (h2 : term503) (h3 : term591 A x s f x' b) : False.
Proof. exact (EQ_MP (@lem6948997 A x s f x' b h1 h2 h3) (@lem6947113 h2)). Qed.
Lemma lem6948999 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term319) (h2 : term503) (h3 : term594 A x s f b) : False.
Proof. exact (ex_elim (@lem6947040 A x s f b h3) (fun x' : A => fun h0 : term593 A x s f b x' => @lem6948998 A x s f x' b h1 h2 h0)). Qed.
Lemma lem6949000 {A : Type'} (x : A) (f : A -> nat) (b : nat) (h1 : term319) (h2 : term503) (h3 : term596 A x f b) : False.
Proof. exact (ex_elim (@lem6947039 A x f b h3) (fun s : A -> Prop => fun h0 : term595 A x f b s => @lem6948999 A x s f b h1 h2 h0)). Qed.
Lemma lem6949001 {A : Type'} (f : A -> nat) (b : nat) (h1 : term319) (h2 : term503) (h3 : term496 A f b) : False.
Proof. exact (ex_elim (@lem6946932 A f b h3) (fun x : A => fun h0 : term597 A f b x => @lem6949000 A x f b h1 h2 h0)). Qed.
Lemma lem6949002 {A : Type'} (f : A -> nat) (b : nat) (h1 : term319) (h2 : term503) (h3 : term496 A f b) : term503 = False.
Proof. exact (prop_ext (fun h4 : term503 => @lem6949001 A f b h1 h2 h3) (fun h4 : False => @lem6947038 h2)). Qed.
Lemma lem6949003 {A : Type'} (f : A -> nat) (b : nat) (h1 : term319) (h2 : term503) (h3 : term496 A f b) : False.
Proof. exact (EQ_MP (@lem6949002 A f b h1 h2 h3) (@lem6947038 h2)). Qed.
Lemma lem6949004 {A : Type'} (f : A -> nat) (b : nat) (h1 : term319) (h2 : term496 A f b) : term501.
Proof. exact (fun h0 : term503 => @lem6949003 A f b h1 h0 h2). Qed.
Lemma lem6949005 : term501 = term502.
Proof. exact (@lem69 term503). Qed.
Lemma lem6949006 {A : Type'} (f : A -> nat) (b : nat) (h1 : term319) (h2 : term496 A f b) : term502.
Proof. exact (EQ_MP (@lem6949005) (@lem6949004 A f b h1 h2)). Qed.
Lemma lem6949007 {A : Type'} (f : A -> nat) (b : nat) (h1 : term496 A f b) : term506.
Proof. exact (fun h0 : term319 => @lem6949006 A f b h0 h1). Qed.
Lemma lem6949008 {A : Type'} (f : A -> nat) (b : nat) : term508 A f b.
Proof. exact (fun h0 : term496 A f b => @lem6949007 A f b h0). Qed.
Lemma lem6949013 {A : Type'} (b : nat) : term512 A b.
Proof. exact (fun f : A -> nat => @lem6949008 A f b). Qed.
Lemma lem6949018 {A : Type'} : term516 A.
Proof. exact (fun b : nat => @lem6949013 A b). Qed.
Lemma lem6949019 {A : Type'} : term515 A.
Proof. exact (EQ_MP (@lem6946652 A) (@lem6949018 A)). Qed.
Lemma lem6949020 {A : Type'} (b : nat) : term726 A b.
Proof. exact (@lem6949019 A b). Qed.
Lemma lem6949021 {A : Type'} (b : nat) : (term726 A b) = (term511 A b).
Proof. exact (eq_refl (term726 A b)). Qed.
Lemma lem6949022 {A : Type'} (b : nat) : term511 A b.
Proof. exact (EQ_MP (@lem6949021 A b) (@lem6949020 A b)). Qed.
Lemma lem6949023 {A : Type'} (b : nat) (f : A -> nat) : term727 A b f.
Proof. exact (@lem6949022 A b f). Qed.
Lemma lem6949024 {A : Type'} (f : A -> nat) (b : nat) : (term727 A b f) = (term497 A f b).
Proof. exact (eq_refl (term727 A b f)). Qed.
Lemma lem6949025 {A : Type'} (f : A -> nat) (b : nat) : term497 A f b.
Proof. exact (EQ_MP (@lem6949024 A f b) (@lem6949023 A b f)). Qed.
Lemma lem6949027 {A : Type'} (f : A -> nat) (b : nat) : term497 A f b.
Proof. exact (@lem6946370 A f b (@lem6949025 A f b)). Qed.
Lemma lem6949028 {A : Type'} (f : A -> nat) (b : nat) (h1 : term496 A f b) : term505.
Proof. exact (@lem6949027 A f b (@lem6946354 A f b h1)). Qed.
Lemma lem6949029 {A : Type'} (f : A -> nat) (b : nat) (h1 : term496 A f b) : term501.
Proof. exact (@lem6949028 A f b h1 (@lem6943068)). Qed.
Lemma lem6949030 {A : Type'} (f : A -> nat) (b : nat) (h1 : term496 A f b) : False.
Proof. exact (@lem6949029 A f b h1 (@lem91499)). Qed.
Lemma lem6949031 {A : Type'} (f : A -> nat) (b : nat) (h1 : term496 A f b) : (term496 A f b) = False.
Proof. exact (prop_ext (fun h2 : term496 A f b => @lem6949030 A f b h1) (fun h2 : False => @lem6946354 A f b h1)). Qed.
Lemma lem6949032 {A : Type'} (f : A -> nat) (b : nat) (h1 : term496 A f b) : False.
Proof. exact (EQ_MP (@lem6949031 A f b h1) (@lem6946354 A f b h1)). Qed.
Lemma lem6949033 {A : Type'} (f : A -> nat) (b : nat) : term495 A f b.
Proof. exact (fun h0 : term496 A f b => @lem6949032 A f b h0). Qed.
Lemma lem6949034 {A : Type'} (f : A -> nat) (b : nat) : term492 A f b.
Proof. exact (EQ_MP (@lem6946353 A f b) (@lem6949033 A f b)). Qed.
Lemma lem6949035 {A : Type'} (f : A -> nat) (b : nat) : term386 A f b.
Proof. exact (EQ_MP (@lem6946349 A f b) (@lem6949034 A f b)). Qed.
Lemma lem6949036 {A : Type'} (f : A -> nat) (b : nat) : term357 A f b.
Proof. exact (@lem6943177 A f b (@lem6949035 A f b)). Qed.
Lemma lem6949037 {A : Type'} (f : A -> nat) (b : nat) : term356 A f b.
Proof. exact (EQ_MP (@lem6943144 A f b) (@lem6949036 A f b)). Qed.
Lemma lem6949042 {A : Type'} (f : A -> nat) : term728 A f.
Proof. exact (fun b : nat => @lem6949037 A f b). Qed.
Lemma lem6949047 {A : Type'} : term729 A.
Proof. exact (fun f : A -> nat => @lem6949042 A f). Qed.
