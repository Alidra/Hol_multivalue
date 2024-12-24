Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_ANTISYM_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm16933_spec.
Require Import thm18392_spec.
Require Import thm912739_spec.
Lemma lem1493618 (y : real) (x : real) : (term0 y x) = (term1 y x).
Proof. exact (@lem16933 (term1 y x)). Qed.
Lemma lem1493619 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1493620 (x : real) : (term4 x) = (term5 x).
Proof. exact (@lem1493619 (term6 x)). Qed.
Lemma lem1493621 (y : real) (x : real) : (term7 x y) = (term8 y x).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1493622 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1493623 (y : real) (x : real) : (term9 x y) = (term0 y x).
Proof. exact (MK_COMB (@lem1493622) (@lem1493621 y x)). Qed.
Lemma lem1493624 (y : real) (x : real) : (term9 x y) = (term1 y x).
Proof. exact (TRANS (@lem1493623 y x) (@lem1493618 y x)). Qed.
Lemma lem1493625 (x : real) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1493624 y x)). Qed.
Lemma lem1493626 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493627 (x : real) : (term5 x) = (term12 x).
Proof. exact (MK_COMB (@lem1493626) (@lem1493625 x)). Qed.
Lemma lem1493628 (x : real) : (term4 x) = (term12 x).
Proof. exact (TRANS (@lem1493620 x) (@lem1493627 x)). Qed.
Lemma lem1493629 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1493630 : term13 = term14.
Proof. exact (@lem1493629 term15). Qed.
Lemma lem1493631 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1493632 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1493633 (x : real) : (term18 x) = (term4 x).
Proof. exact (MK_COMB (@lem1493632) (@lem1493631 x)). Qed.
Lemma lem1493634 (x : real) : (term18 x) = (term12 x).
Proof. exact (TRANS (@lem1493633 x) (@lem1493628 x)). Qed.
Lemma lem1493635 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1493634 x)). Qed.
Lemma lem1493636 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493637 : term14 = term21.
Proof. exact (MK_COMB (@lem1493636) (@lem1493635)). Qed.
Lemma lem1493639 : term13 = term21.
Proof. exact (TRANS (@lem1493630) (@lem1493637)). Qed.
Lemma lem1493644 (y : real) (x : real) : (term1 y x) = (term1 y x).
Proof. exact (eq_refl (term1 y x)). Qed.
Lemma lem1493645 (x : real) : (term11 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1493644 y x)). Qed.
Lemma lem1493646 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493647 (x : real) : (term12 x) = (term12 x).
Proof. exact (MK_COMB (@lem1493646) (@lem1493645 x)). Qed.
Lemma lem1493648 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1493647 x)). Qed.
Lemma lem1493649 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493650 : term21 = term21.
Proof. exact (MK_COMB (@lem1493649) (@lem1493648)). Qed.
Lemma lem1493651 : term13 = term21.
Proof. exact (TRANS (@lem1493639) (@lem1493650)). Qed.
Lemma lem1493652 (y : real) (x : real) : (real_lt x y) = (term22 y x).
Proof. exact (@lem1483521 y x). Qed.
Lemma lem1493658 (y : real) (x : real) : (real_sub y x) = (term23 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1493663 (x : real) (y : real) : (term23 y x) = (term24 x y).
Proof. exact (@lem1483488 (term25 x) y). Qed.
Lemma lem1493665 (x : real) (y : real) : (real_sub y x) = (term24 x y).
Proof. exact (TRANS (@lem1493658 y x) (@lem1493663 x y)). Qed.
Lemma lem1493666 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1493667 (x : real) (y : real) : (term26 y x) = (term27 x y).
Proof. exact (MK_COMB (@lem1493666) (@lem1493665 x y)). Qed.
Lemma lem1493668 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1493669 (x : real) (y : real) : (term22 y x) = (term29 x y).
Proof. exact (MK_COMB (@lem1493667 x y) (@lem1493668)). Qed.
Lemma lem1493670 (x : real) (y : real) : (real_lt x y) = (term29 x y).
Proof. exact (TRANS (@lem1493652 y x) (@lem1493669 x y)). Qed.
Lemma lem1493671 (x : real) (y : real) : (real_lt y x) = (term22 x y).
Proof. exact (@lem1483521 x y). Qed.
Lemma lem1493684 (x : real) (y : real) : (real_sub x y) = (term23 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1493685 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1493686 (x : real) (y : real) : (term26 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1493685) (@lem1493684 x y)). Qed.
Lemma lem1493687 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1493688 (x : real) (y : real) : (term22 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1493686 x y) (@lem1493687)). Qed.
Lemma lem1493689 (x : real) (y : real) : (real_lt y x) = (term31 x y).
Proof. exact (TRANS (@lem1493671 x y) (@lem1493688 x y)). Qed.
Lemma lem1493690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1493691 (x : real) (y : real) : (term32 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1493690) (@lem1493670 x y)). Qed.
Lemma lem1493692 (x : real) (y : real) : (term1 y x) = (term34 x y).
Proof. exact (MK_COMB (@lem1493691 x y) (@lem1493689 x y)). Qed.
Lemma lem1493693 (x : real) : (term11 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem1493692 x y)). Qed.
Lemma lem1493694 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493695 (x : real) : (term12 x) = (term36 x).
Proof. exact (MK_COMB (@lem1493694) (@lem1493693 x)). Qed.
Lemma lem1493696 : term20 = term37.
Proof. exact (fun_ext (fun x : real => @lem1493695 x)). Qed.
Lemma lem1493697 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493698 : term21 = term38.
Proof. exact (MK_COMB (@lem1493697) (@lem1493696)). Qed.
Lemma lem1493757 : term13 = term38.
Proof. exact (TRANS (@lem1493651) (@lem1493698)). Qed.
Lemma lem1493764 (x : real) (y : real) : (term34 x y) = (term34 x y).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem1493765 (x : real) : (term35 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem1493764 x y)). Qed.
Lemma lem1493766 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493767 (x : real) : (term36 x) = (term36 x).
Proof. exact (MK_COMB (@lem1493766) (@lem1493765 x)). Qed.
Lemma lem1493768 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1493767 x)). Qed.
Lemma lem1493769 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493770 : term38 = term38.
Proof. exact (MK_COMB (@lem1493769) (@lem1493768)). Qed.
Lemma lem1493771 : term13 = term38.
Proof. exact (TRANS (@lem1493757) (@lem1493770)). Qed.
Lemma lem1493775 (x : real) (y : real) (h1 : term34 x y) : term34 x y.
Proof. exact (h1). Qed.
Lemma lem1493776 (x : real) (y : real) (h1 : term34 x y) : term31 x y.
Proof. exact (proj2 (@lem1493775 x y h1)). Qed.
Lemma lem1493777 (x : real) (y : real) (h1 : term34 x y) : term29 x y.
Proof. exact (proj1 (@lem1493775 x y h1)). Qed.
Lemma lem1493779 (n : nat) (m : nat) : (term39 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1493780 : term40 = term41.
Proof. exact (@lem1493779 (NUMERAL 0) term42). Qed.
Lemma lem1493781 : term43 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1493782 (h1 : term43 = (BIT1 0)) : term41 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1493783 : (term43 = (BIT1 0)) = (term41 = True).
Proof. exact (prop_ext (fun h1 : term43 = (BIT1 0) => @lem1493782 h1) (fun h1 : term41 = True => @lem1493781)). Qed.
Lemma lem1493784 : term41 = True.
Proof. exact (EQ_MP (@lem1493783) (@lem1493781)). Qed.
Lemma lem1493785 : term40 = True.
Proof. exact (TRANS (@lem1493780) (@lem1493784)). Qed.
Lemma lem1493786 : True = term40.
Proof. exact (SYM (@lem1493785)). Qed.
Lemma lem1493787 : term40.
Proof. exact (EQ_MP (@lem1493786) (@lem0)). Qed.
Lemma lem1493788 (x : real) (y : real) (h1 : term34 x y) : term44 x y.
Proof. exact (conj (@lem1493787) (@lem1493777 x y h1)). Qed.
Lemma lem1493790 (x : real) (y : real) : term45 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1493791 (x : real) (y : real) : term46 x y.
Proof. exact (@lem1493790 term47 (term24 x y)). Qed.
Lemma lem1493792 (x : real) (y : real) (h1 : term34 x y) : term48 x y.
Proof. exact (@lem1493791 x y (@lem1493788 x y h1)). Qed.
Lemma lem1493793 (x : real) (y : real) : (term49 x y) = (term24 x y).
Proof. exact (@lem1483460 (term24 x y)). Qed.
Lemma lem1493794 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1493795 (x : real) (y : real) : (term50 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1493794) (@lem1493793 x y)). Qed.
Lemma lem1493796 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1493797 (x : real) (y : real) : (term48 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1493795 x y) (@lem1493796)). Qed.
Lemma lem1493798 (x : real) (y : real) (h1 : term34 x y) : term29 x y.
Proof. exact (EQ_MP (@lem1493797 x y) (@lem1493792 x y h1)). Qed.
Lemma lem1493800 (n : nat) (m : nat) : (term39 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1493801 : term40 = term41.
Proof. exact (@lem1493800 (NUMERAL 0) term42). Qed.
Lemma lem1493802 : term43 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1493803 (h1 : term43 = (BIT1 0)) : term41 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1493804 : (term43 = (BIT1 0)) = (term41 = True).
Proof. exact (prop_ext (fun h1 : term43 = (BIT1 0) => @lem1493803 h1) (fun h1 : term41 = True => @lem1493802)). Qed.
Lemma lem1493805 : term41 = True.
Proof. exact (EQ_MP (@lem1493804) (@lem1493802)). Qed.
Lemma lem1493806 : term40 = True.
Proof. exact (TRANS (@lem1493801) (@lem1493805)). Qed.
Lemma lem1493807 : True = term40.
Proof. exact (SYM (@lem1493806)). Qed.
Lemma lem1493808 : term40.
Proof. exact (EQ_MP (@lem1493807) (@lem0)). Qed.
Lemma lem1493809 (x : real) (y : real) (h1 : term34 x y) : term51 x y.
Proof. exact (conj (@lem1493808) (@lem1493776 x y h1)). Qed.
Lemma lem1493811 (x : real) (y : real) : term45 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1493812 (x : real) (y : real) : term52 x y.
Proof. exact (@lem1493811 term47 (term23 x y)). Qed.
Lemma lem1493813 (x : real) (y : real) (h1 : term34 x y) : term53 x y.
Proof. exact (@lem1493812 x y (@lem1493809 x y h1)). Qed.
Lemma lem1493814 (x : real) (y : real) : (term54 x y) = (term23 x y).
Proof. exact (@lem1483460 (term23 x y)). Qed.
Lemma lem1493815 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1493816 (x : real) (y : real) : (term55 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1493815) (@lem1493814 x y)). Qed.
Lemma lem1493817 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1493818 (x : real) (y : real) : (term53 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1493816 x y) (@lem1493817)). Qed.
Lemma lem1493819 (x : real) (y : real) (h1 : term34 x y) : term31 x y.
Proof. exact (EQ_MP (@lem1493818 x y) (@lem1493813 x y h1)). Qed.
Lemma lem1493820 (x : real) (y : real) (h1 : term34 x y) : term56 x y.
Proof. exact (conj (@lem1493819 x y h1) (@lem1493798 x y h1)). Qed.
Lemma lem1493822 (x : real) (y : real) : term57 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1493823 (x : real) (y : real) : term58 x y.
Proof. exact (@lem1493822 (term23 x y) (term24 x y)). Qed.
Lemma lem1493824 (x : real) (y : real) (h1 : term34 x y) : term59 x y.
Proof. exact (@lem1493823 x y (@lem1493820 x y h1)). Qed.
Lemma lem1493825 (x : real) (y : real) : (term60 x y) = (term61 x y).
Proof. exact (@lem1483480 x (term25 x) (term25 y) y). Qed.
Lemma lem1493826 (x : real) : (term62 x) = (term63 x).
Proof. exact (@lem1483442 term64 x). Qed.
Lemma lem1493828 (m : nat) : (term65 m) = term28.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1493829 : term66 = term28.
Proof. exact (@lem1493828 term42). Qed.
Lemma lem1493830 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1493831 : term67 = term68.
Proof. exact (MK_COMB (@lem1493830) (@lem1493829)). Qed.
Lemma lem1493832 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1493833 (x : real) : (term63 x) = (term69 x).
Proof. exact (MK_COMB (@lem1493831) (@lem1493832 x)). Qed.
Lemma lem1493834 (x : real) : (term62 x) = (term69 x).
Proof. exact (TRANS (@lem1493826 x) (@lem1493833 x)). Qed.
Lemma lem1493835 (x : real) : (term69 x) = term28.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1493836 (x : real) : (term62 x) = term28.
Proof. exact (TRANS (@lem1493834 x) (@lem1493835 x)). Qed.
Lemma lem1493837 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1493838 (x : real) : (term70 x) = term71.
Proof. exact (MK_COMB (@lem1493837) (@lem1493836 x)). Qed.
Lemma lem1493839 (y : real) : (term72 y) = (term63 y).
Proof. exact (@lem1483440 term64 y). Qed.
Lemma lem1493841 (m : nat) : (term65 m) = term28.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1493842 : term66 = term28.
Proof. exact (@lem1493841 term42). Qed.
Lemma lem1493843 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1493844 : term67 = term68.
Proof. exact (MK_COMB (@lem1493843) (@lem1493842)). Qed.
Lemma lem1493845 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1493846 (y : real) : (term63 y) = (term69 y).
Proof. exact (MK_COMB (@lem1493844) (@lem1493845 y)). Qed.
Lemma lem1493847 (y : real) : (term72 y) = (term69 y).
Proof. exact (TRANS (@lem1493839 y) (@lem1493846 y)). Qed.
Lemma lem1493848 (y : real) : (term69 y) = term28.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1493849 (y : real) : (term72 y) = term28.
Proof. exact (TRANS (@lem1493847 y) (@lem1493848 y)). Qed.
Lemma lem1493850 (x : real) (y : real) : (term61 x y) = term73.
Proof. exact (MK_COMB (@lem1493838 x) (@lem1493849 y)). Qed.
Lemma lem1493851 (x : real) (y : real) : (term60 x y) = term73.
Proof. exact (TRANS (@lem1493825 x y) (@lem1493850 x y)). Qed.
Lemma lem1493852 : term73 = term28.
Proof. exact (@lem1483448 term28). Qed.
Lemma lem1493853 (x : real) (y : real) : (term60 x y) = term28.
Proof. exact (TRANS (@lem1493851 x y) (@lem1493852)). Qed.
Lemma lem1493854 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1493855 (x : real) (y : real) : (term74 x y) = term75.
Proof. exact (MK_COMB (@lem1493854) (@lem1493853 x y)). Qed.
Lemma lem1493856 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1493857 (x : real) (y : real) : (term59 x y) = term76.
Proof. exact (MK_COMB (@lem1493855 x y) (@lem1493856)). Qed.
Lemma lem1493858 (x : real) (y : real) (h1 : term34 x y) : term76.
Proof. exact (EQ_MP (@lem1493857 x y) (@lem1493824 x y h1)). Qed.
Lemma lem1493860 (n : nat) (m : nat) : (term39 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1493861 : term76 = term77.
Proof. exact (@lem1493860 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1493862 : term77 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1493863 : term76 = False.
Proof. exact (TRANS (@lem1493861) (@lem1493862)). Qed.
Lemma lem1493864 (x : real) (y : real) (h1 : term34 x y) : False.
Proof. exact (EQ_MP (@lem1493863) (@lem1493858 x y h1)). Qed.
Lemma lem1493866 (x : real) (y : real) (h1 : term34 x y) : term34 x y.
Proof. exact (h1). Qed.
Lemma lem1493867 (x : real) (y : real) (h1 : term34 x y) : (term34 x y) = False.
Proof. exact (prop_ext (fun h2 : term34 x y => @lem1493864 x y h1) (fun h2 : False => @lem1493866 x y h1)). Qed.
Lemma lem1493868 (x : real) (y : real) (h1 : term34 x y) : False.
Proof. exact (EQ_MP (@lem1493867 x y h1) (@lem1493866 x y h1)). Qed.
Lemma lem1493869 (x : real) (h1 : term36 x) : term36 x.
Proof. exact (h1). Qed.
Lemma lem1493870 (x : real) (h1 : term36 x) : False.
Proof. exact (ex_elim (@lem1493869 x h1) (fun y : real => fun h0 : term35 x y => @lem1493868 x y h0)). Qed.
Lemma lem1493871 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1493872 (h1 : term38) : False.
Proof. exact (ex_elim (@lem1493871 h1) (fun x : real => fun h0 : term37 x => @lem1493870 x h0)). Qed.
Lemma lem1493873 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1493874 (h1 : term13) : term38.
Proof. exact (EQ_MP (@lem1493771) (@lem1493873 h1)). Qed.
Lemma lem1493875 (h1 : term13) : term38 = False.
Proof. exact (prop_ext (fun h2 : term38 => @lem1493872 h2) (fun h2 : False => @lem1493874 h1)). Qed.
Lemma lem1493876 (h1 : term13) : False.
Proof. exact (EQ_MP (@lem1493875 h1) (@lem1493874 h1)). Qed.
Lemma lem1493877 : term78.
Proof. exact (fun h0 : term13 => @lem1493876 h0). Qed.
Lemma lem1493878 : term79.
Proof. exact (@lem1386578 term80). Qed.
Lemma lem1493879 : term80.
Proof. exact (@lem1493878 (@lem1493877)). Qed.
