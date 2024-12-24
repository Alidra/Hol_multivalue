Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ADD_SUB_term_abbrevs.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483486_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Lemma lem1507660 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1507661 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1507660 (term4 x)). Qed.
Lemma lem1507662 (x : real) (y : real) : (term5 x y) = ((term6 y x) = y).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1507663 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1507665 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem1507663) (@lem1507662 x y)). Qed.
Lemma lem1507666 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1507665 x y)). Qed.
Lemma lem1507667 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507668 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1507667) (@lem1507666 x)). Qed.
Lemma lem1507669 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1507661 x) (@lem1507668 x)). Qed.
Lemma lem1507670 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1507671 : term12 = term13.
Proof. exact (@lem1507670 term14). Qed.
Lemma lem1507672 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1507673 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1507674 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1507673) (@lem1507672 x)). Qed.
Lemma lem1507675 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1507674 x) (@lem1507669 x)). Qed.
Lemma lem1507676 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1507675 x)). Qed.
Lemma lem1507677 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507678 : term13 = term20.
Proof. exact (MK_COMB (@lem1507677) (@lem1507676)). Qed.
Lemma lem1507680 : term12 = term20.
Proof. exact (TRANS (@lem1507671) (@lem1507678)). Qed.
Lemma lem1507683 (x : real) (y : real) : (term8 x y) = (term8 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1507684 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1507683 x y)). Qed.
Lemma lem1507685 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507686 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1507685) (@lem1507684 x)). Qed.
Lemma lem1507687 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1507686 x)). Qed.
Lemma lem1507688 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507689 : term20 = term20.
Proof. exact (MK_COMB (@lem1507688) (@lem1507687)). Qed.
Lemma lem1507690 : term12 = term20.
Proof. exact (TRANS (@lem1507680) (@lem1507689)). Qed.
Lemma lem1507691 (x : real) (y : real) : (term8 x y) = (term21 x y).
Proof. exact (@lem1483554 (term6 y x) y). Qed.
Lemma lem1507692 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1507704 (y : real) (x : real) : (term6 y x) = (term22 y x).
Proof. exact (@lem1483519 (real_add x y) x). Qed.
Lemma lem1507708 (x : real) (y : real) : (term22 y x) = (term23 x y).
Proof. exact (@lem1483486 x (term24 x) y). Qed.
Lemma lem1507709 (x : real) : (term25 x) = (term26 x).
Proof. exact (@lem1483442 term27 x). Qed.
Lemma lem1507711 (m : nat) : (term28 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1507712 : term30 = term29.
Proof. exact (@lem1507711 term31). Qed.
Lemma lem1507713 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1507714 : term32 = term33.
Proof. exact (MK_COMB (@lem1507713) (@lem1507712)). Qed.
Lemma lem1507715 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1507716 (x : real) : (term26 x) = (term34 x).
Proof. exact (MK_COMB (@lem1507714) (@lem1507715 x)). Qed.
Lemma lem1507717 (x : real) : (term25 x) = (term34 x).
Proof. exact (TRANS (@lem1507709 x) (@lem1507716 x)). Qed.
Lemma lem1507718 (x : real) : (term34 x) = term29.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1507719 (x : real) : (term25 x) = term29.
Proof. exact (TRANS (@lem1507717 x) (@lem1507718 x)). Qed.
Lemma lem1507720 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1507721 (x : real) : (term35 x) = term36.
Proof. exact (MK_COMB (@lem1507720) (@lem1507719 x)). Qed.
Lemma lem1507722 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1507723 (x : real) (y : real) : (term23 x y) = (term37 y).
Proof. exact (MK_COMB (@lem1507721 x) (@lem1507722 y)). Qed.
Lemma lem1507724 (x : real) (y : real) : (term22 y x) = (term37 y).
Proof. exact (TRANS (@lem1507708 x y) (@lem1507723 x y)). Qed.
Lemma lem1507725 (y : real) : (term37 y) = y.
Proof. exact (@lem1483448 y). Qed.
Lemma lem1507727 (x : real) (y : real) : (term22 y x) = y.
Proof. exact (TRANS (@lem1507724 x y) (@lem1507725 y)). Qed.
Lemma lem1507729 (x : real) (y : real) : (term6 y x) = y.
Proof. exact (TRANS (@lem1507704 y x) (@lem1507727 x y)). Qed.
Lemma lem1507730 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1507731 (x : real) (y : real) : (term38 y x) = (real_sub y).
Proof. exact (MK_COMB (@lem1507730) (@lem1507729 x y)). Qed.
Lemma lem1507732 (x : real) (y : real) : (term39 x y) = (real_sub y y).
Proof. exact (MK_COMB (@lem1507731 x y) (@lem1507692 y)). Qed.
Lemma lem1507733 (y : real) : (real_sub y y) = (term25 y).
Proof. exact (@lem1483519 y y). Qed.
Lemma lem1507737 (y : real) : (term25 y) = (term26 y).
Proof. exact (@lem1483442 term27 y). Qed.
Lemma lem1507739 (m : nat) : (term28 m) = term29.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1507740 : term30 = term29.
Proof. exact (@lem1507739 term31). Qed.
Lemma lem1507741 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1507742 : term32 = term33.
Proof. exact (MK_COMB (@lem1507741) (@lem1507740)). Qed.
Lemma lem1507743 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1507744 (y : real) : (term26 y) = (term34 y).
Proof. exact (MK_COMB (@lem1507742) (@lem1507743 y)). Qed.
Lemma lem1507745 (y : real) : (term25 y) = (term34 y).
Proof. exact (TRANS (@lem1507737 y) (@lem1507744 y)). Qed.
Lemma lem1507746 (y : real) : (term34 y) = term29.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1507748 (y : real) : (term25 y) = term29.
Proof. exact (TRANS (@lem1507745 y) (@lem1507746 y)). Qed.
Lemma lem1507749 (y : real) : (real_sub y y) = term29.
Proof. exact (TRANS (@lem1507733 y) (@lem1507748 y)). Qed.
Lemma lem1507750 (x : real) (y : real) : (term39 x y) = term29.
Proof. exact (TRANS (@lem1507732 x y) (@lem1507749 y)). Qed.
Lemma lem1507751 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1507752 (x : real) (y : real) : (term40 x y) = term41.
Proof. exact (MK_COMB (@lem1507751) (@lem1507750 x y)). Qed.
Lemma lem1507753 : term41 = term42.
Proof. exact (@lem1483512 term29). Qed.
Lemma lem1507755 (x : nat) : (term43 x) = term29.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1507756 : term42 = term29.
Proof. exact (@lem1507755 term31). Qed.
Lemma lem1507757 : term41 = term29.
Proof. exact (TRANS (@lem1507753) (@lem1507756)). Qed.
Lemma lem1507758 (x : real) (y : real) : (term44 x y) = (term44 x y).
Proof. exact (eq_refl (term44 x y)). Qed.
Lemma lem1507759 (x : real) (y : real) : ((term40 x y) = term41) = ((term40 x y) = term29).
Proof. exact (MK_COMB (@lem1507758 x y) (@lem1507757)). Qed.
Lemma lem1507760 (x : real) (y : real) : (term40 x y) = term29.
Proof. exact (EQ_MP (@lem1507759 x y) (@lem1507752 x y)). Qed.
Lemma lem1507761 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1507762 (x : real) (y : real) : (term45 x y) = term46.
Proof. exact (MK_COMB (@lem1507761) (@lem1507760 x y)). Qed.
Lemma lem1507763 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1507764 (x : real) (y : real) : (term47 x y) = term48.
Proof. exact (MK_COMB (@lem1507762 x y) (@lem1507763)). Qed.
Lemma lem1507765 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1507766 (x : real) (y : real) : (term49 x y) = term46.
Proof. exact (MK_COMB (@lem1507765) (@lem1507750 x y)). Qed.
Lemma lem1507767 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1507768 (x : real) (y : real) : (term50 x y) = term48.
Proof. exact (MK_COMB (@lem1507766 x y) (@lem1507767)). Qed.
Lemma lem1507769 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1507770 (x : real) (y : real) : (term51 x y) = term52.
Proof. exact (MK_COMB (@lem1507769) (@lem1507768 x y)). Qed.
Lemma lem1507771 (x : real) (y : real) : (term21 x y) = term53.
Proof. exact (MK_COMB (@lem1507770 x y) (@lem1507764 x y)). Qed.
Lemma lem1507772 (x : real) (y : real) : (term8 x y) = term53.
Proof. exact (TRANS (@lem1507691 x y) (@lem1507771 x y)). Qed.
Lemma lem1507773 (x : real) : (term10 x) = term54.
Proof. exact (fun_ext (fun y : real => @lem1507772 x y)). Qed.
Lemma lem1507774 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507775 (x : real) : (term11 x) = term55.
Proof. exact (MK_COMB (@lem1507774) (@lem1507773 x)). Qed.
Lemma lem1507776 : term19 = term56.
Proof. exact (fun_ext (fun x : real => @lem1507775 x)). Qed.
Lemma lem1507777 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507778 : term20 = term57.
Proof. exact (MK_COMB (@lem1507777) (@lem1507776)). Qed.
Lemma lem1507779 : term12 = term57.
Proof. exact (TRANS (@lem1507690) (@lem1507778)). Qed.
Lemma lem1507781 {A : Type'} (t : Prop) : (term58 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1507782 (t : Prop) : (term59 t) = t.
Proof. exact (@lem1507781 real t). Qed.
Lemma lem1507783 : term57 = term55.
Proof. exact (@lem1507782 term55). Qed.
Lemma lem1507785 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term60 A P Q) = (term61 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1507786 (P : real -> Prop) (Q : real -> Prop) : (term62 P Q) = (term63 P Q).
Proof. exact (@lem1507785 real P Q). Qed.
Lemma lem1507787 : term64 = term65.
Proof. exact (@lem1507786 term66 term66). Qed.
Lemma lem1507788 (y : real) : (term67 y) = term48.
Proof. exact (eq_refl (term67 y)). Qed.
Lemma lem1507789 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1507790 (y : real) : (term68 y) = term52.
Proof. exact (MK_COMB (@lem1507789) (@lem1507788 y)). Qed.
Lemma lem1507791 (y : real) : (term67 y) = term48.
Proof. exact (eq_refl (term67 y)). Qed.
Lemma lem1507792 (y : real) : (term69 y) = term53.
Proof. exact (MK_COMB (@lem1507790 y) (@lem1507791 y)). Qed.
Lemma lem1507793 : term70 = term54.
Proof. exact (fun_ext (fun y : real => @lem1507792 y)). Qed.
Lemma lem1507794 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507795 : term64 = term55.
Proof. exact (MK_COMB (@lem1507794) (@lem1507793)). Qed.
Lemma lem1507796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1507797 : term71 = term72.
Proof. exact (MK_COMB (@lem1507796) (@lem1507795)). Qed.
Lemma lem1507798 (y : real) : (term67 y) = term48.
Proof. exact (eq_refl (term67 y)). Qed.
Lemma lem1507799 : term73 = term66.
Proof. exact (fun_ext (fun y : real => @lem1507798 y)). Qed.
Lemma lem1507800 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507801 : term74 = term75.
Proof. exact (MK_COMB (@lem1507800) (@lem1507799)). Qed.
Lemma lem1507802 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1507803 : term76 = term77.
Proof. exact (MK_COMB (@lem1507802) (@lem1507801)). Qed.
Lemma lem1507804 (y : real) : (term67 y) = term48.
Proof. exact (eq_refl (term67 y)). Qed.
Lemma lem1507805 : term73 = term66.
Proof. exact (fun_ext (fun y : real => @lem1507804 y)). Qed.
Lemma lem1507806 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507807 : term74 = term75.
Proof. exact (MK_COMB (@lem1507806) (@lem1507805)). Qed.
Lemma lem1507808 : term65 = term78.
Proof. exact (MK_COMB (@lem1507803) (@lem1507807)). Qed.
Lemma lem1507809 : (term64 = term65) = (term55 = term78).
Proof. exact (MK_COMB (@lem1507797) (@lem1507808)). Qed.
Lemma lem1507810 : term55 = term78.
Proof. exact (EQ_MP (@lem1507809) (@lem1507787)). Qed.
Lemma lem1507811 : term57 = term78.
Proof. exact (TRANS (@lem1507783) (@lem1507810)). Qed.
Lemma lem1507813 {A : Type'} (t : Prop) : (term58 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1507814 (t : Prop) : (term59 t) = t.
Proof. exact (@lem1507813 real t). Qed.
Lemma lem1507815 : term75 = term48.
Proof. exact (@lem1507814 term48). Qed.
Lemma lem1507816 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1507817 : term77 = term52.
Proof. exact (MK_COMB (@lem1507816) (@lem1507815)). Qed.
Lemma lem1507819 {A : Type'} (t : Prop) : (term58 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1507820 (t : Prop) : (term59 t) = t.
Proof. exact (@lem1507819 real t). Qed.
Lemma lem1507821 : term75 = term48.
Proof. exact (@lem1507820 term48). Qed.
Lemma lem1507822 : term78 = term53.
Proof. exact (MK_COMB (@lem1507817) (@lem1507821)). Qed.
Lemma lem1507825 : term57 = term53.
Proof. exact (TRANS (@lem1507811) (@lem1507822)). Qed.
Lemma lem1507834 : term12 = term53.
Proof. exact (TRANS (@lem1507779) (@lem1507825)). Qed.
Lemma lem1507844 (h1 : term53) : term53.
Proof. exact (h1). Qed.
Lemma lem1507845 (h1 : term48) : term48.
Proof. exact (h1). Qed.
Lemma lem1507847 (n : nat) (m : nat) : (term79 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1507848 : term48 = term80.
Proof. exact (@lem1507847 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1507849 : term80 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1507850 : term48 = False.
Proof. exact (TRANS (@lem1507848) (@lem1507849)). Qed.
Lemma lem1507851 (h1 : term48) : False.
Proof. exact (EQ_MP (@lem1507850) (@lem1507845 h1)). Qed.
Lemma lem1507852 (h1 : term48) : term48.
Proof. exact (h1). Qed.
Lemma lem1507854 (n : nat) (m : nat) : (term79 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1507855 : term48 = term80.
Proof. exact (@lem1507854 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1507856 : term80 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1507857 : term48 = False.
Proof. exact (TRANS (@lem1507855) (@lem1507856)). Qed.
Lemma lem1507858 (h1 : term48) : False.
Proof. exact (EQ_MP (@lem1507857) (@lem1507852 h1)). Qed.
Lemma lem1507859 (h1 : term53) : False.
Proof. exact (or_elim (@lem1507844 h1) (fun h0 : term48 => @lem1507851 h0) (fun h0 : term48 => @lem1507858 h0)). Qed.
Lemma lem1507861 (h1 : term53) : term53.
Proof. exact (h1). Qed.
Lemma lem1507862 (h1 : term53) : term53 = False.
Proof. exact (prop_ext (fun h2 : term53 => @lem1507859 h1) (fun h2 : False => @lem1507861 h1)). Qed.
Lemma lem1507863 (h1 : term53) : False.
Proof. exact (EQ_MP (@lem1507862 h1) (@lem1507861 h1)). Qed.
Lemma lem1507864 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1507865 (h1 : term12) : term53.
Proof. exact (EQ_MP (@lem1507834) (@lem1507864 h1)). Qed.
Lemma lem1507866 (h1 : term12) : term53 = False.
Proof. exact (prop_ext (fun h2 : term53 => @lem1507863 h2) (fun h2 : False => @lem1507865 h1)). Qed.
Lemma lem1507867 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1507866 h1) (@lem1507865 h1)). Qed.
Lemma lem1507868 : term81.
Proof. exact (fun h0 : term12 => @lem1507867 h0). Qed.
Lemma lem1507869 : term82.
Proof. exact (@lem1386578 term83). Qed.
Lemma lem1507870 : term83.
Proof. exact (@lem1507869 (@lem1507868)). Qed.
