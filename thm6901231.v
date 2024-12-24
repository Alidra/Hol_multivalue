Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6901231_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_EQ_1_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm6898615_spec.
Require Import thm6898616_spec.
Require Import thm69_spec.
Lemma lem6898645 {A : Type'} (P : A -> Prop) (x : A) : term0 A P x.
Proof. exact (EQ_MP (@lem6898616 A P x) (@lem6898615 A P x)). Qed.
Lemma lem6898646 (P : nat -> Prop) (x : nat) : term1 P x.
Proof. exact (@lem6898645 nat P x). Qed.
Lemma lem6898647 : term2.
Proof. exact (@lem6898646 term3 term4). Qed.
Lemma lem6898649 (p : Prop) : p = (term5 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6898650 : term6 = term7.
Proof. exact (@lem6898649 term6). Qed.
Lemma lem6898651 : term7 = term6.
Proof. exact (SYM (@lem6898650)). Qed.
Lemma lem6898652 (h1 : term8) : term8.
Proof. exact (h1). Qed.
Lemma lem6898655 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem6898656 : term10.
Proof. exact (fun h0 : term9 => @lem6898655 h0). Qed.
Lemma lem6898657 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem6898658 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem6898659 (h1 : term9) (h2 : term10) : term9.
Proof. exact (@lem6898657 h2 (@lem6898658 h1)). Qed.
Lemma lem6898660 (h1 : term9) : term11.
Proof. exact (fun h0 : term10 => @lem6898659 h1 h0). Qed.
Lemma lem6898661 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem6898662 (h1 : term9) (h2 : term10) : term9.
Proof. exact (@lem6898660 h1 (@lem6898661 h2)). Qed.
Lemma lem6898663 (h1 : term10) : term10.
Proof. exact (fun h0 : term9 => @lem6898662 h0 h1). Qed.
Lemma lem6898664 : term12.
Proof. exact (fun h0 : term10 => @lem6898663 h0). Qed.
Lemma lem6898667 : term10.
Proof. exact (@lem6898664 (@lem6898656)). Qed.
Lemma lem6898675 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term13 A P Q) = (term14 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem6898676 (P : nat -> Prop) (Q : nat -> Prop) : (term15 P Q) = (term16 P Q).
Proof. exact (@lem6898675 nat P Q). Qed.
Lemma lem6898677 (x : nat) : (term17 x) = (term18 x).
Proof. exact (@lem6898676 (term19 x) (term20 x)). Qed.
Lemma lem6898678 (x : nat) (y : nat) : (term21 x y) = ((Nat.mul x y) = y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem6898679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6898680 (x : nat) (y : nat) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem6898679) (@lem6898678 x y)). Qed.
Lemma lem6898681 (x : nat) (y : nat) : (term24 x y) = ((Nat.mul y x) = y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem6898682 (x : nat) (y : nat) : (term25 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem6898680 x y) (@lem6898681 x y)). Qed.
Lemma lem6898683 (x : nat) : (term27 x) = (term28 x).
Proof. exact (fun_ext (fun y : nat => @lem6898682 x y)). Qed.
Lemma lem6898684 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898685 (x : nat) : (term17 x) = (term29 x).
Proof. exact (MK_COMB (@lem6898684) (@lem6898683 x)). Qed.
Lemma lem6898686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6898687 (x : nat) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem6898686) (@lem6898685 x)). Qed.
Lemma lem6898688 (x : nat) (y : nat) : (term21 x y) = ((Nat.mul x y) = y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem6898689 (x : nat) : (term32 x) = (term19 x).
Proof. exact (fun_ext (fun y : nat => @lem6898688 x y)). Qed.
Lemma lem6898690 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898691 (x : nat) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem6898690) (@lem6898689 x)). Qed.
Lemma lem6898692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6898693 (x : nat) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem6898692) (@lem6898691 x)). Qed.
Lemma lem6898694 (x : nat) (y : nat) : (term24 x y) = ((Nat.mul y x) = y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem6898695 (x : nat) : (term37 x) = (term20 x).
Proof. exact (fun_ext (fun y : nat => @lem6898694 x y)). Qed.
Lemma lem6898696 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898697 (x : nat) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem6898696) (@lem6898695 x)). Qed.
Lemma lem6898698 (x : nat) : (term18 x) = (term40 x).
Proof. exact (MK_COMB (@lem6898693 x) (@lem6898697 x)). Qed.
Lemma lem6898699 (x : nat) : ((term17 x) = (term18 x)) = ((term29 x) = (term40 x)).
Proof. exact (MK_COMB (@lem6898687 x) (@lem6898698 x)). Qed.
Lemma lem6898700 (x : nat) : (term29 x) = (term40 x).
Proof. exact (EQ_MP (@lem6898699 x) (@lem6898677 x)). Qed.
Lemma lem6898711 : term3 = term41.
Proof. exact (fun_ext (fun x : nat => @lem6898700 x)). Qed.
Lemma lem6898712 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6898713 (y : nat) : (term42 y) = (term43 y).
Proof. exact (MK_COMB (@lem6898711) (@lem6898712 y)). Qed.
Lemma lem6898714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6898715 (y : nat) : (term44 y) = (term45 y).
Proof. exact (MK_COMB (@lem6898714) (@lem6898713 y)). Qed.
Lemma lem6898716 (y : nat) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6898717 (y : nat) : ((term42 y) = (y = term4)) = ((term43 y) = (y = term4)).
Proof. exact (MK_COMB (@lem6898715 y) (@lem6898716 y)). Qed.
Lemma lem6898718 : term46 = term47.
Proof. exact (fun_ext (fun y : nat => @lem6898717 y)). Qed.
Lemma lem6898719 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898720 : term6 = term48.
Proof. exact (MK_COMB (@lem6898719) (@lem6898718)). Qed.
Lemma lem6898725 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6898726 : term8 = term49.
Proof. exact (MK_COMB (@lem6898725) (@lem6898720)). Qed.
Lemma lem6898727 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6898728 : term50 = term51.
Proof. exact (MK_COMB (@lem6898727) (@lem6898726)). Qed.
Lemma lem6898742 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6898743 : term52 = term53.
Proof. exact (@lem6898742 term54). Qed.
Lemma lem6898786 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem6898787 : term56 = term57.
Proof. exact (MK_COMB (@lem6898786) (@lem6898743)). Qed.
Lemma lem6898790 : term9 = term58.
Proof. exact (MK_COMB (@lem6898728) (@lem6898787)). Qed.
Lemma lem6898793 (y : nat) : (term43 y) = (term40 y).
Proof. exact (eq_refl (term43 y)). Qed.
Lemma lem6898794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6898795 (y : nat) : (term45 y) = (term59 y).
Proof. exact (MK_COMB (@lem6898794) (@lem6898793 y)). Qed.
Lemma lem6898796 (y : nat) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6898797 (y : nat) : ((term43 y) = (y = term4)) = ((term40 y) = (y = term4)).
Proof. exact (MK_COMB (@lem6898795 y) (@lem6898796 y)). Qed.
Lemma lem6898798 : term47 = term60.
Proof. exact (fun_ext (fun y : nat => @lem6898797 y)). Qed.
Lemma lem6898799 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898800 : term48 = term61.
Proof. exact (MK_COMB (@lem6898799) (@lem6898798)). Qed.
Lemma lem6898801 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6898802 : term49 = term62.
Proof. exact (MK_COMB (@lem6898801) (@lem6898800)). Qed.
Lemma lem6898803 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6898804 : term51 = term63.
Proof. exact (MK_COMB (@lem6898803) (@lem6898802)). Qed.
Lemma lem6898805 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem6898806 : term58 = term64.
Proof. exact (MK_COMB (@lem6898804) (@lem6898805)). Qed.
Lemma lem6898809 : term9 = term64.
Proof. exact (TRANS (@lem6898790) (@lem6898806)). Qed.
Lemma lem6898810 (m : nat) (n : nat) : ((term65 m n) = (term66 m n)) = ((term65 m n) = (term66 m n)).
Proof. exact (eq_refl ((term65 m n) = (term66 m n))). Qed.
Lemma lem6898811 (m : nat) : (term67 m) = (term67 m).
Proof. exact (fun_ext (fun n : nat => @lem6898810 m n)). Qed.
Lemma lem6898812 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898813 (m : nat) : (term68 m) = (term68 m).
Proof. exact (MK_COMB (@lem6898812) (@lem6898811 m)). Qed.
Lemma lem6898814 : term69 = term69.
Proof. exact (fun_ext (fun m : nat => @lem6898813 m)). Qed.
Lemma lem6898815 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898816 : term70 = term70.
Proof. exact (MK_COMB (@lem6898815) (@lem6898814)). Qed.
Lemma lem6898817 (m : nat) (n : nat) : ((term71 m n) = (term72 m n)) = ((term71 m n) = (term72 m n)).
Proof. exact (eq_refl ((term71 m n) = (term72 m n))). Qed.
Lemma lem6898818 (m : nat) : (term73 m) = (term73 m).
Proof. exact (fun_ext (fun n : nat => @lem6898817 m n)). Qed.
Lemma lem6898819 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898820 (m : nat) : (term74 m) = (term74 m).
Proof. exact (MK_COMB (@lem6898819) (@lem6898818 m)). Qed.
Lemma lem6898821 : term75 = term75.
Proof. exact (fun_ext (fun m : nat => @lem6898820 m)). Qed.
Lemma lem6898822 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898823 : term76 = term76.
Proof. exact (MK_COMB (@lem6898822) (@lem6898821)). Qed.
Lemma lem6898824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6898825 : term77 = term77.
Proof. exact (MK_COMB (@lem6898824) (@lem6898823)). Qed.
Lemma lem6898826 : term78 = term78.
Proof. exact (MK_COMB (@lem6898825) (@lem6898816)). Qed.
Lemma lem6898827 (m : nat) : ((term79 m) = m) = ((term79 m) = m).
Proof. exact (eq_refl ((term79 m) = m)). Qed.
Lemma lem6898828 : term80 = term80.
Proof. exact (fun_ext (fun m : nat => @lem6898827 m)). Qed.
Lemma lem6898829 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898830 : term81 = term81.
Proof. exact (MK_COMB (@lem6898829) (@lem6898828)). Qed.
Lemma lem6898831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6898832 : term82 = term82.
Proof. exact (MK_COMB (@lem6898831) (@lem6898830)). Qed.
Lemma lem6898833 : term83 = term83.
Proof. exact (MK_COMB (@lem6898832) (@lem6898826)). Qed.
Lemma lem6898834 (n : nat) : ((term84 n) = n) = ((term84 n) = n).
Proof. exact (eq_refl ((term84 n) = n)). Qed.
Lemma lem6898835 : term85 = term85.
Proof. exact (fun_ext (fun n : nat => @lem6898834 n)). Qed.
Lemma lem6898836 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898837 : term86 = term86.
Proof. exact (MK_COMB (@lem6898836) (@lem6898835)). Qed.
Lemma lem6898838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6898839 : term87 = term87.
Proof. exact (MK_COMB (@lem6898838) (@lem6898837)). Qed.
Lemma lem6898840 : term88 = term88.
Proof. exact (MK_COMB (@lem6898839) (@lem6898833)). Qed.
Lemma lem6898841 (m : nat) : ((term89 m) = (NUMERAL 0)) = ((term89 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term89 m) = (NUMERAL 0))). Qed.
Lemma lem6898842 : term90 = term90.
Proof. exact (fun_ext (fun m : nat => @lem6898841 m)). Qed.
Lemma lem6898843 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898844 : term91 = term91.
Proof. exact (MK_COMB (@lem6898843) (@lem6898842)). Qed.
Lemma lem6898845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6898846 : term92 = term92.
Proof. exact (MK_COMB (@lem6898845) (@lem6898844)). Qed.
Lemma lem6898847 : term93 = term93.
Proof. exact (MK_COMB (@lem6898846) (@lem6898840)). Qed.
Lemma lem6898848 (n : nat) : ((term94 n) = (NUMERAL 0)) = ((term94 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term94 n) = (NUMERAL 0))). Qed.
Lemma lem6898849 : term95 = term95.
Proof. exact (fun_ext (fun n : nat => @lem6898848 n)). Qed.
Lemma lem6898850 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898851 : term96 = term96.
Proof. exact (MK_COMB (@lem6898850) (@lem6898849)). Qed.
Lemma lem6898852 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6898853 : term97 = term97.
Proof. exact (MK_COMB (@lem6898852) (@lem6898851)). Qed.
Lemma lem6898854 : term54 = term54.
Proof. exact (MK_COMB (@lem6898853) (@lem6898847)). Qed.
Lemma lem6898855 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6898856 : term53 = term53.
Proof. exact (MK_COMB (@lem6898855) (@lem6898854)). Qed.
Lemma lem6898865 (m : nat) (n : nat) : (((Nat.mul m n) = term4) = (term98 m n)) = (((Nat.mul m n) = term4) = (term98 m n)).
Proof. exact (eq_refl (((Nat.mul m n) = term4) = (term98 m n))). Qed.
Lemma lem6898866 (m : nat) : (term99 m) = (term99 m).
Proof. exact (fun_ext (fun n : nat => @lem6898865 m n)). Qed.
Lemma lem6898867 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898868 (m : nat) : (term100 m) = (term100 m).
Proof. exact (MK_COMB (@lem6898867) (@lem6898866 m)). Qed.
Lemma lem6898869 : term101 = term101.
Proof. exact (fun_ext (fun m : nat => @lem6898868 m)). Qed.
Lemma lem6898870 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898871 : term102 = term102.
Proof. exact (MK_COMB (@lem6898870) (@lem6898869)). Qed.
Lemma lem6898872 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6898873 : term55 = term55.
Proof. exact (MK_COMB (@lem6898872) (@lem6898871)). Qed.
Lemma lem6898874 : term57 = term57.
Proof. exact (MK_COMB (@lem6898873) (@lem6898856)). Qed.
Lemma lem6898875 (y : nat) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6898876 (y : nat) (y' : nat) : ((Nat.mul y' y) = y') = ((Nat.mul y' y) = y').
Proof. exact (eq_refl ((Nat.mul y' y) = y')). Qed.
Lemma lem6898877 (y : nat) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : nat => @lem6898876 y y')). Qed.
Lemma lem6898878 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898879 (y : nat) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6898878) (@lem6898877 y)). Qed.
Lemma lem6898880 (y : nat) (y' : nat) : ((Nat.mul y y') = y') = ((Nat.mul y y') = y').
Proof. exact (eq_refl ((Nat.mul y y') = y')). Qed.
Lemma lem6898881 (y : nat) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : nat => @lem6898880 y y')). Qed.
Lemma lem6898882 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898883 (y : nat) : (term34 y) = (term34 y).
Proof. exact (MK_COMB (@lem6898882) (@lem6898881 y)). Qed.
Lemma lem6898884 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6898885 (y : nat) : (term36 y) = (term36 y).
Proof. exact (MK_COMB (@lem6898884) (@lem6898883 y)). Qed.
Lemma lem6898886 (y : nat) : (term40 y) = (term40 y).
Proof. exact (MK_COMB (@lem6898885 y) (@lem6898879 y)). Qed.
Lemma lem6898887 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6898888 (y : nat) : (term59 y) = (term59 y).
Proof. exact (MK_COMB (@lem6898887) (@lem6898886 y)). Qed.
Lemma lem6898889 (y : nat) : ((term40 y) = (y = term4)) = ((term40 y) = (y = term4)).
Proof. exact (MK_COMB (@lem6898888 y) (@lem6898875 y)). Qed.
Lemma lem6898890 : term60 = term60.
Proof. exact (fun_ext (fun y : nat => @lem6898889 y)). Qed.
Lemma lem6898891 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6898892 : term61 = term61.
Proof. exact (MK_COMB (@lem6898891) (@lem6898890)). Qed.
Lemma lem6898893 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6898894 : term62 = term62.
Proof. exact (MK_COMB (@lem6898893) (@lem6898892)). Qed.
Lemma lem6898895 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6898896 : term63 = term63.
Proof. exact (MK_COMB (@lem6898895) (@lem6898894)). Qed.
Lemma lem6898897 : term64 = term64.
Proof. exact (MK_COMB (@lem6898896) (@lem6898874)). Qed.
Lemma lem6898996 : term9 = term64.
Proof. exact (TRANS (@lem6898809) (@lem6898897)). Qed.
Lemma lem6898997 : term64 = term9.
Proof. exact (SYM (@lem6898996)). Qed.
Lemma lem6898998 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem6898999 (h1 : term102) : term102.
Proof. exact (h1). Qed.
Lemma lem6899000 (h1 : term54) : term54.
Proof. exact (h1). Qed.
Lemma lem6899002 (y : nat) (y' : nat) : ((Nat.mul y y') = y') = ((Nat.mul y y') = y').
Proof. exact (eq_refl ((Nat.mul y y') = y')). Qed.
Lemma lem6899003 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem6899004 (y : nat) : (term105 y) = (term106 y).
Proof. exact (@lem6899003 (term19 y)). Qed.
Lemma lem6899005 (y : nat) (y' : nat) : (term21 y y') = ((Nat.mul y y') = y').
Proof. exact (eq_refl (term21 y y')). Qed.
Lemma lem6899006 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6899008 (y : nat) (y' : nat) : (term107 y y') = (term108 y y').
Proof. exact (MK_COMB (@lem6899006) (@lem6899005 y y')). Qed.
Lemma lem6899009 (y : nat) : (term109 y) = (term110 y).
Proof. exact (fun_ext (fun y' : nat => @lem6899008 y y')). Qed.
Lemma lem6899010 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899011 (y : nat) : (term106 y) = (term111 y).
Proof. exact (MK_COMB (@lem6899010) (@lem6899009 y)). Qed.
Lemma lem6899012 (y : nat) : (term105 y) = (term111 y).
Proof. exact (TRANS (@lem6899004 y) (@lem6899011 y)). Qed.
Lemma lem6899013 (y : nat) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : nat => @lem6899002 y y')). Qed.
Lemma lem6899014 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899015 (y : nat) : (term34 y) = (term34 y).
Proof. exact (MK_COMB (@lem6899014) (@lem6899013 y)). Qed.
Lemma lem6899017 (y : nat) (y' : nat) : ((Nat.mul y' y) = y') = ((Nat.mul y' y) = y').
Proof. exact (eq_refl ((Nat.mul y' y) = y')). Qed.
Lemma lem6899018 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem6899019 (y : nat) : (term112 y) = (term113 y).
Proof. exact (@lem6899018 (term20 y)). Qed.
Lemma lem6899020 (y : nat) (y' : nat) : (term24 y y') = ((Nat.mul y' y) = y').
Proof. exact (eq_refl (term24 y y')). Qed.
Lemma lem6899021 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6899023 (y : nat) (y' : nat) : (term114 y y') = (term115 y y').
Proof. exact (MK_COMB (@lem6899021) (@lem6899020 y y')). Qed.
Lemma lem6899024 (y : nat) : (term116 y) = (term117 y).
Proof. exact (fun_ext (fun y' : nat => @lem6899023 y y')). Qed.
Lemma lem6899025 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899026 (y : nat) : (term113 y) = (term118 y).
Proof. exact (MK_COMB (@lem6899025) (@lem6899024 y)). Qed.
Lemma lem6899027 (y : nat) : (term112 y) = (term118 y).
Proof. exact (TRANS (@lem6899019 y) (@lem6899026 y)). Qed.
Lemma lem6899028 (y : nat) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : nat => @lem6899017 y y')). Qed.
Lemma lem6899029 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899030 (y : nat) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6899029) (@lem6899028 y)). Qed.
Lemma lem6899031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6899032 (y : nat) : (term119 y) = (term120 y).
Proof. exact (MK_COMB (@lem6899031) (@lem6899012 y)). Qed.
Lemma lem6899033 (y : nat) : (term121 y) = (term122 y).
Proof. exact (MK_COMB (@lem6899032 y) (@lem6899027 y)). Qed.
Lemma lem6899034 (y : nat) : (term123 y) = (term121 y).
Proof. exact (@lem17045 (term34 y) (term39 y)). Qed.
Lemma lem6899035 (y : nat) : (term123 y) = (term122 y).
Proof. exact (TRANS (@lem6899034 y) (@lem6899033 y)). Qed.
Lemma lem6899036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899037 (y : nat) : (term36 y) = (term36 y).
Proof. exact (MK_COMB (@lem6899036) (@lem6899015 y)). Qed.
Lemma lem6899038 (y : nat) : (term40 y) = (term40 y).
Proof. exact (MK_COMB (@lem6899037 y) (@lem6899030 y)). Qed.
Lemma lem6899039 (y : nat) : (term124 y) = (term124 y).
Proof. exact (eq_refl (term124 y)). Qed.
Lemma lem6899040 (y : nat) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6899041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899042 (y : nat) : (term125 y) = (term126 y).
Proof. exact (MK_COMB (@lem6899041) (@lem6899035 y)). Qed.
Lemma lem6899043 (y : nat) : (term127 y) = (term128 y).
Proof. exact (MK_COMB (@lem6899042 y) (@lem6899040 y)). Qed.
Lemma lem6899044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899045 (y : nat) : (term129 y) = (term129 y).
Proof. exact (MK_COMB (@lem6899044) (@lem6899038 y)). Qed.
Lemma lem6899046 (y : nat) : (term130 y) = (term130 y).
Proof. exact (MK_COMB (@lem6899045 y) (@lem6899039 y)). Qed.
Lemma lem6899047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6899048 (y : nat) : (term131 y) = (term131 y).
Proof. exact (MK_COMB (@lem6899047) (@lem6899046 y)). Qed.
Lemma lem6899049 (y : nat) : (term132 y) = (term133 y).
Proof. exact (MK_COMB (@lem6899048 y) (@lem6899043 y)). Qed.
Lemma lem6899050 (y : nat) : (term134 y) = (term132 y).
Proof. exact (@lem17646 (term40 y) (y = term4)). Qed.
Lemma lem6899051 (y : nat) : (term134 y) = (term133 y).
Proof. exact (TRANS (@lem6899050 y) (@lem6899049 y)). Qed.
Lemma lem6899052 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem6899053 : term62 = term135.
Proof. exact (@lem6899052 term60). Qed.
Lemma lem6899054 (y : nat) : (term136 y) = ((term40 y) = (y = term4)).
Proof. exact (eq_refl (term136 y)). Qed.
Lemma lem6899055 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6899056 (y : nat) : (term137 y) = (term134 y).
Proof. exact (MK_COMB (@lem6899055) (@lem6899054 y)). Qed.
Lemma lem6899057 (y : nat) : (term137 y) = (term133 y).
Proof. exact (TRANS (@lem6899056 y) (@lem6899051 y)). Qed.
Lemma lem6899058 : term138 = term139.
Proof. exact (fun_ext (fun y : nat => @lem6899057 y)). Qed.
Lemma lem6899059 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899060 : term135 = term140.
Proof. exact (MK_COMB (@lem6899059) (@lem6899058)). Qed.
Lemma lem6899061 : term62 = term140.
Proof. exact (TRANS (@lem6899053) (@lem6899060)). Qed.
Lemma lem6899063 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem6899064 (P : nat -> Prop) (Q : nat -> Prop) : (term143 P Q) = (term144 P Q).
Proof. exact (@lem6899063 nat P Q). Qed.
Lemma lem6899065 : term145 = term146.
Proof. exact (@lem6899064 term147 term148). Qed.
Lemma lem6899066 (y : nat) : (term149 y) = (term130 y).
Proof. exact (eq_refl (term149 y)). Qed.
Lemma lem6899067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6899068 (y : nat) : (term150 y) = (term131 y).
Proof. exact (MK_COMB (@lem6899067) (@lem6899066 y)). Qed.
Lemma lem6899069 (y : nat) : (term151 y) = (term128 y).
Proof. exact (eq_refl (term151 y)). Qed.
Lemma lem6899070 (y : nat) : (term152 y) = (term133 y).
Proof. exact (MK_COMB (@lem6899068 y) (@lem6899069 y)). Qed.
Lemma lem6899071 : term153 = term139.
Proof. exact (fun_ext (fun y : nat => @lem6899070 y)). Qed.
Lemma lem6899072 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899073 : term145 = term140.
Proof. exact (MK_COMB (@lem6899072) (@lem6899071)). Qed.
Lemma lem6899074 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6899075 : term154 = term155.
Proof. exact (MK_COMB (@lem6899074) (@lem6899073)). Qed.
Lemma lem6899076 (y : nat) : (term149 y) = (term130 y).
Proof. exact (eq_refl (term149 y)). Qed.
Lemma lem6899077 : term156 = term147.
Proof. exact (fun_ext (fun y : nat => @lem6899076 y)). Qed.
Lemma lem6899078 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899079 : term157 = term158.
Proof. exact (MK_COMB (@lem6899078) (@lem6899077)). Qed.
Lemma lem6899080 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6899081 : term159 = term160.
Proof. exact (MK_COMB (@lem6899080) (@lem6899079)). Qed.
Lemma lem6899082 (y : nat) : (term151 y) = (term128 y).
Proof. exact (eq_refl (term151 y)). Qed.
Lemma lem6899083 : term161 = term148.
Proof. exact (fun_ext (fun y : nat => @lem6899082 y)). Qed.
Lemma lem6899084 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899085 : term162 = term163.
Proof. exact (MK_COMB (@lem6899084) (@lem6899083)). Qed.
Lemma lem6899086 : term146 = term164.
Proof. exact (MK_COMB (@lem6899081) (@lem6899085)). Qed.
Lemma lem6899087 : (term145 = term146) = (term140 = term164).
Proof. exact (MK_COMB (@lem6899075) (@lem6899086)). Qed.
Lemma lem6899088 : term140 = term164.
Proof. exact (EQ_MP (@lem6899087) (@lem6899065)). Qed.
Lemma lem6899202 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term142 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6899203 (P : nat -> Prop) (Q : nat -> Prop) : (term144 P Q) = (term143 P Q).
Proof. exact (@lem6899202 nat P Q). Qed.
Lemma lem6899204 (y : nat) : (term165 y) = (term166 y).
Proof. exact (@lem6899203 (term110 y) (term117 y)). Qed.
Lemma lem6899205 (y : nat) (y' : nat) : (term167 y y') = (term108 y y').
Proof. exact (eq_refl (term167 y y')). Qed.
Lemma lem6899206 (y : nat) : (term168 y) = (term110 y).
Proof. exact (fun_ext (fun y' : nat => @lem6899205 y y')). Qed.
Lemma lem6899207 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899208 (y : nat) : (term169 y) = (term111 y).
Proof. exact (MK_COMB (@lem6899207) (@lem6899206 y)). Qed.
Lemma lem6899209 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6899210 (y : nat) : (term170 y) = (term120 y).
Proof. exact (MK_COMB (@lem6899209) (@lem6899208 y)). Qed.
Lemma lem6899211 (y : nat) (y' : nat) : (term171 y y') = (term115 y y').
Proof. exact (eq_refl (term171 y y')). Qed.
Lemma lem6899212 (y : nat) : (term172 y) = (term117 y).
Proof. exact (fun_ext (fun y' : nat => @lem6899211 y y')). Qed.
Lemma lem6899213 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899214 (y : nat) : (term173 y) = (term118 y).
Proof. exact (MK_COMB (@lem6899213) (@lem6899212 y)). Qed.
Lemma lem6899215 (y : nat) : (term165 y) = (term122 y).
Proof. exact (MK_COMB (@lem6899210 y) (@lem6899214 y)). Qed.
Lemma lem6899216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6899217 (y : nat) : (term174 y) = (term175 y).
Proof. exact (MK_COMB (@lem6899216) (@lem6899215 y)). Qed.
Lemma lem6899218 (y : nat) (y' : nat) : (term167 y y') = (term108 y y').
Proof. exact (eq_refl (term167 y y')). Qed.
Lemma lem6899219 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6899220 (y : nat) (y' : nat) : (term176 y y') = (term177 y y').
Proof. exact (MK_COMB (@lem6899219) (@lem6899218 y y')). Qed.
Lemma lem6899221 (y : nat) (y' : nat) : (term171 y y') = (term115 y y').
Proof. exact (eq_refl (term171 y y')). Qed.
Lemma lem6899222 (y : nat) (y' : nat) : (term178 y y') = (term179 y y').
Proof. exact (MK_COMB (@lem6899220 y y') (@lem6899221 y y')). Qed.
Lemma lem6899223 (y : nat) : (term180 y) = (term181 y).
Proof. exact (fun_ext (fun y' : nat => @lem6899222 y y')). Qed.
Lemma lem6899224 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899225 (y : nat) : (term166 y) = (term182 y).
Proof. exact (MK_COMB (@lem6899224) (@lem6899223 y)). Qed.
Lemma lem6899226 (y : nat) : ((term165 y) = (term166 y)) = ((term122 y) = (term182 y)).
Proof. exact (MK_COMB (@lem6899217 y) (@lem6899225 y)). Qed.
Lemma lem6899227 (y : nat) : (term122 y) = (term182 y).
Proof. exact (EQ_MP (@lem6899226 y) (@lem6899204 y)). Qed.
Lemma lem6899228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899229 (y : nat) : (term126 y) = (term183 y).
Proof. exact (MK_COMB (@lem6899228) (@lem6899227 y)). Qed.
Lemma lem6899230 (y : nat) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6899231 (y : nat) : (term128 y) = (term184 y).
Proof. exact (MK_COMB (@lem6899229 y) (@lem6899230 y)). Qed.
Lemma lem6899233 {A : Type'} (P : A -> Prop) (Q : Prop) : (term185 A P Q) = (term186 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6899234 (P : nat -> Prop) (Q : Prop) : (term187 P Q) = (term188 P Q).
Proof. exact (@lem6899233 nat P Q). Qed.
Lemma lem6899235 (y : nat) : (term189 y) = (term190 y).
Proof. exact (@lem6899234 (term181 y) (y = term4)). Qed.
Lemma lem6899236 (y : nat) (y' : nat) : (term191 y y') = (term179 y y').
Proof. exact (eq_refl (term191 y y')). Qed.
Lemma lem6899237 (y : nat) : (term192 y) = (term181 y).
Proof. exact (fun_ext (fun y' : nat => @lem6899236 y y')). Qed.
Lemma lem6899238 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899239 (y : nat) : (term193 y) = (term182 y).
Proof. exact (MK_COMB (@lem6899238) (@lem6899237 y)). Qed.
Lemma lem6899240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899241 (y : nat) : (term194 y) = (term183 y).
Proof. exact (MK_COMB (@lem6899240) (@lem6899239 y)). Qed.
Lemma lem6899242 (y : nat) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6899243 (y : nat) : (term189 y) = (term184 y).
Proof. exact (MK_COMB (@lem6899241 y) (@lem6899242 y)). Qed.
Lemma lem6899244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6899245 (y : nat) : (term195 y) = (term196 y).
Proof. exact (MK_COMB (@lem6899244) (@lem6899243 y)). Qed.
Lemma lem6899246 (y : nat) (y' : nat) : (term191 y y') = (term179 y y').
Proof. exact (eq_refl (term191 y y')). Qed.
Lemma lem6899247 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899248 (y : nat) (y' : nat) : (term197 y y') = (term198 y y').
Proof. exact (MK_COMB (@lem6899247) (@lem6899246 y y')). Qed.
Lemma lem6899249 (y : nat) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6899250 (y' : nat) (y : nat) : (term199 y' y) = (term200 y' y).
Proof. exact (MK_COMB (@lem6899248 y y') (@lem6899249 y)). Qed.
Lemma lem6899251 (y : nat) : (term201 y) = (term202 y).
Proof. exact (fun_ext (fun y' : nat => @lem6899250 y' y)). Qed.
Lemma lem6899252 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899253 (y : nat) : (term190 y) = (term203 y).
Proof. exact (MK_COMB (@lem6899252) (@lem6899251 y)). Qed.
Lemma lem6899254 (y : nat) : ((term189 y) = (term190 y)) = ((term184 y) = (term203 y)).
Proof. exact (MK_COMB (@lem6899245 y) (@lem6899253 y)). Qed.
Lemma lem6899255 (y : nat) : (term184 y) = (term203 y).
Proof. exact (EQ_MP (@lem6899254 y) (@lem6899235 y)). Qed.
Lemma lem6899256 (y : nat) : (term128 y) = (term203 y).
Proof. exact (TRANS (@lem6899231 y) (@lem6899255 y)). Qed.
Lemma lem6899257 : term148 = term204.
Proof. exact (fun_ext (fun y : nat => @lem6899256 y)). Qed.
Lemma lem6899258 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899259 : term163 = term205.
Proof. exact (MK_COMB (@lem6899258) (@lem6899257)). Qed.
Lemma lem6899260 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem6899261 : term164 = term206.
Proof. exact (MK_COMB (@lem6899260) (@lem6899259)). Qed.
Lemma lem6899263 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term142 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6899264 (P : nat -> Prop) (Q : nat -> Prop) : (term144 P Q) = (term143 P Q).
Proof. exact (@lem6899263 nat P Q). Qed.
Lemma lem6899265 : term207 = term208.
Proof. exact (@lem6899264 term147 term204). Qed.
Lemma lem6899266 (y : nat) : (term149 y) = (term130 y).
Proof. exact (eq_refl (term149 y)). Qed.
Lemma lem6899267 : term156 = term147.
Proof. exact (fun_ext (fun y : nat => @lem6899266 y)). Qed.
Lemma lem6899268 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899269 : term157 = term158.
Proof. exact (MK_COMB (@lem6899268) (@lem6899267)). Qed.
Lemma lem6899270 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6899271 : term159 = term160.
Proof. exact (MK_COMB (@lem6899270) (@lem6899269)). Qed.
Lemma lem6899272 (y : nat) : (term209 y) = (term203 y).
Proof. exact (eq_refl (term209 y)). Qed.
Lemma lem6899273 : term210 = term204.
Proof. exact (fun_ext (fun y : nat => @lem6899272 y)). Qed.
Lemma lem6899274 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899275 : term211 = term205.
Proof. exact (MK_COMB (@lem6899274) (@lem6899273)). Qed.
Lemma lem6899276 : term207 = term206.
Proof. exact (MK_COMB (@lem6899271) (@lem6899275)). Qed.
Lemma lem6899277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6899278 : term212 = term213.
Proof. exact (MK_COMB (@lem6899277) (@lem6899276)). Qed.
Lemma lem6899279 (y : nat) : (term149 y) = (term130 y).
Proof. exact (eq_refl (term149 y)). Qed.
Lemma lem6899280 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6899281 (y : nat) : (term150 y) = (term131 y).
Proof. exact (MK_COMB (@lem6899280) (@lem6899279 y)). Qed.
Lemma lem6899282 (y : nat) : (term209 y) = (term203 y).
Proof. exact (eq_refl (term209 y)). Qed.
Lemma lem6899283 (y : nat) : (term214 y) = (term215 y).
Proof. exact (MK_COMB (@lem6899281 y) (@lem6899282 y)). Qed.
Lemma lem6899284 : term216 = term217.
Proof. exact (fun_ext (fun y : nat => @lem6899283 y)). Qed.
Lemma lem6899285 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899286 : term208 = term218.
Proof. exact (MK_COMB (@lem6899285) (@lem6899284)). Qed.
Lemma lem6899287 : (term207 = term208) = (term206 = term218).
Proof. exact (MK_COMB (@lem6899278) (@lem6899286)). Qed.
Lemma lem6899288 : term206 = term218.
Proof. exact (EQ_MP (@lem6899287) (@lem6899265)). Qed.
Lemma lem6899290 {A : Type'} (P : Prop) (Q : A -> Prop) : (term219 A P Q) = (term220 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6899291 (P : Prop) (Q : nat -> Prop) : (term221 P Q) = (term222 P Q).
Proof. exact (@lem6899290 nat P Q). Qed.
Lemma lem6899292 (y : nat) : (term223 y) = (term224 y).
Proof. exact (@lem6899291 (term130 y) (term202 y)). Qed.
Lemma lem6899293 (y' : nat) (y : nat) : (term225 y y') = (term200 y' y).
Proof. exact (eq_refl (term225 y y')). Qed.
Lemma lem6899294 (y : nat) : (term226 y) = (term202 y).
Proof. exact (fun_ext (fun y' : nat => @lem6899293 y' y)). Qed.
Lemma lem6899295 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899296 (y : nat) : (term227 y) = (term203 y).
Proof. exact (MK_COMB (@lem6899295) (@lem6899294 y)). Qed.
Lemma lem6899297 (y : nat) : (term131 y) = (term131 y).
Proof. exact (eq_refl (term131 y)). Qed.
Lemma lem6899298 (y : nat) : (term223 y) = (term215 y).
Proof. exact (MK_COMB (@lem6899297 y) (@lem6899296 y)). Qed.
Lemma lem6899299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6899300 (y : nat) : (term228 y) = (term229 y).
Proof. exact (MK_COMB (@lem6899299) (@lem6899298 y)). Qed.
Lemma lem6899301 (y' : nat) (y : nat) : (term225 y y') = (term200 y' y).
Proof. exact (eq_refl (term225 y y')). Qed.
Lemma lem6899302 (y : nat) : (term131 y) = (term131 y).
Proof. exact (eq_refl (term131 y)). Qed.
Lemma lem6899303 (y' : nat) (y : nat) : (term230 y y') = (term231 y' y).
Proof. exact (MK_COMB (@lem6899302 y) (@lem6899301 y' y)). Qed.
Lemma lem6899304 (y : nat) : (term232 y) = (term233 y).
Proof. exact (fun_ext (fun y' : nat => @lem6899303 y' y)). Qed.
Lemma lem6899305 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899306 (y : nat) : (term224 y) = (term234 y).
Proof. exact (MK_COMB (@lem6899305) (@lem6899304 y)). Qed.
Lemma lem6899307 (y : nat) : ((term223 y) = (term224 y)) = ((term215 y) = (term234 y)).
Proof. exact (MK_COMB (@lem6899300 y) (@lem6899306 y)). Qed.
Lemma lem6899308 (y : nat) : (term215 y) = (term234 y).
Proof. exact (EQ_MP (@lem6899307 y) (@lem6899292 y)). Qed.
Lemma lem6899309 : term217 = term235.
Proof. exact (fun_ext (fun y : nat => @lem6899308 y)). Qed.
Lemma lem6899310 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6899311 : term218 = term236.
Proof. exact (MK_COMB (@lem6899310) (@lem6899309)). Qed.
Lemma lem6899312 : term206 = term236.
Proof. exact (TRANS (@lem6899288) (@lem6899311)). Qed.
Lemma lem6899313 : term164 = term236.
Proof. exact (TRANS (@lem6899261) (@lem6899312)). Qed.
Lemma lem6899314 : term140 = term236.
Proof. exact (TRANS (@lem6899088) (@lem6899313)). Qed.
Lemma lem6899315 : term62 = term236.
Proof. exact (TRANS (@lem6899061) (@lem6899314)). Qed.
Lemma lem6899316 (h1 : term62) : term236.
Proof. exact (EQ_MP (@lem6899315) (@lem6898998 h1)). Qed.
Lemma lem6899327 (m : nat) (n : nat) : (term237 m n) = (term238 m n).
Proof. exact (@lem17045 (m = term4) (n = term4)). Qed.
Lemma lem6899333 (m : nat) (n : nat) : (term239 m n) = (term239 m n).
Proof. exact (eq_refl (term239 m n)). Qed.
Lemma lem6899335 (m : nat) (n : nat) : (term240 m n) = (term240 m n).
Proof. exact (eq_refl (term240 m n)). Qed.
Lemma lem6899336 (m : nat) (n : nat) : (term241 m n) = (term242 m n).
Proof. exact (MK_COMB (@lem6899335 m n) (@lem6899327 m n)). Qed.
Lemma lem6899337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899338 (m : nat) (n : nat) : (term243 m n) = (term244 m n).
Proof. exact (MK_COMB (@lem6899337) (@lem6899336 m n)). Qed.
Lemma lem6899339 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (MK_COMB (@lem6899338 m n) (@lem6899333 m n)). Qed.
Lemma lem6899340 (m : nat) (n : nat) : (((Nat.mul m n) = term4) = (term98 m n)) = (term245 m n).
Proof. exact (@lem17784 ((Nat.mul m n) = term4) (term98 m n)). Qed.
Lemma lem6899341 (m : nat) (n : nat) : (((Nat.mul m n) = term4) = (term98 m n)) = (term246 m n).
Proof. exact (TRANS (@lem6899340 m n) (@lem6899339 m n)). Qed.
Lemma lem6899342 (m : nat) : (term99 m) = (term247 m).
Proof. exact (fun_ext (fun n : nat => @lem6899341 m n)). Qed.
Lemma lem6899343 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899344 (m : nat) : (term100 m) = (term248 m).
Proof. exact (MK_COMB (@lem6899343) (@lem6899342 m)). Qed.
Lemma lem6899345 : term101 = term249.
Proof. exact (fun_ext (fun m : nat => @lem6899344 m)). Qed.
Lemma lem6899346 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899347 : term102 = term250.
Proof. exact (MK_COMB (@lem6899346) (@lem6899345)). Qed.
Lemma lem6899353 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term13 A P Q) = (term14 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6899354 (P : nat -> Prop) (Q : nat -> Prop) : (term15 P Q) = (term16 P Q).
Proof. exact (@lem6899353 nat P Q). Qed.
Lemma lem6899355 (m : nat) : (term251 m) = (term252 m).
Proof. exact (@lem6899354 (term253 m) (term254 m)). Qed.
Lemma lem6899356 (m : nat) (n : nat) : (term255 m n) = (term242 m n).
Proof. exact (eq_refl (term255 m n)). Qed.
Lemma lem6899357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899358 (m : nat) (n : nat) : (term256 m n) = (term244 m n).
Proof. exact (MK_COMB (@lem6899357) (@lem6899356 m n)). Qed.
Lemma lem6899359 (m : nat) (n : nat) : (term257 m n) = (term239 m n).
Proof. exact (eq_refl (term257 m n)). Qed.
Lemma lem6899360 (m : nat) (n : nat) : (term258 m n) = (term246 m n).
Proof. exact (MK_COMB (@lem6899358 m n) (@lem6899359 m n)). Qed.
Lemma lem6899361 (m : nat) : (term259 m) = (term247 m).
Proof. exact (fun_ext (fun n : nat => @lem6899360 m n)). Qed.
Lemma lem6899362 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899363 (m : nat) : (term251 m) = (term248 m).
Proof. exact (MK_COMB (@lem6899362) (@lem6899361 m)). Qed.
Lemma lem6899364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6899365 (m : nat) : (term260 m) = (term261 m).
Proof. exact (MK_COMB (@lem6899364) (@lem6899363 m)). Qed.
Lemma lem6899366 (m : nat) (n : nat) : (term255 m n) = (term242 m n).
Proof. exact (eq_refl (term255 m n)). Qed.
Lemma lem6899367 (m : nat) : (term262 m) = (term253 m).
Proof. exact (fun_ext (fun n : nat => @lem6899366 m n)). Qed.
Lemma lem6899368 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899369 (m : nat) : (term263 m) = (term264 m).
Proof. exact (MK_COMB (@lem6899368) (@lem6899367 m)). Qed.
Lemma lem6899370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899371 (m : nat) : (term265 m) = (term266 m).
Proof. exact (MK_COMB (@lem6899370) (@lem6899369 m)). Qed.
Lemma lem6899372 (m : nat) (n : nat) : (term257 m n) = (term239 m n).
Proof. exact (eq_refl (term257 m n)). Qed.
Lemma lem6899373 (m : nat) : (term267 m) = (term254 m).
Proof. exact (fun_ext (fun n : nat => @lem6899372 m n)). Qed.
Lemma lem6899374 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899375 (m : nat) : (term268 m) = (term269 m).
Proof. exact (MK_COMB (@lem6899374) (@lem6899373 m)). Qed.
Lemma lem6899376 (m : nat) : (term252 m) = (term270 m).
Proof. exact (MK_COMB (@lem6899371 m) (@lem6899375 m)). Qed.
Lemma lem6899377 (m : nat) : ((term251 m) = (term252 m)) = ((term248 m) = (term270 m)).
Proof. exact (MK_COMB (@lem6899365 m) (@lem6899376 m)). Qed.
Lemma lem6899378 (m : nat) : (term248 m) = (term270 m).
Proof. exact (EQ_MP (@lem6899377 m) (@lem6899355 m)). Qed.
Lemma lem6899475 : term249 = term271.
Proof. exact (fun_ext (fun m : nat => @lem6899378 m)). Qed.
Lemma lem6899476 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899477 : term250 = term272.
Proof. exact (MK_COMB (@lem6899476) (@lem6899475)). Qed.
Lemma lem6899479 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term13 A P Q) = (term14 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6899480 (P : nat -> Prop) (Q : nat -> Prop) : (term15 P Q) = (term16 P Q).
Proof. exact (@lem6899479 nat P Q). Qed.
Lemma lem6899481 : term273 = term274.
Proof. exact (@lem6899480 term275 term276). Qed.
Lemma lem6899482 (m : nat) : (term277 m) = (term264 m).
Proof. exact (eq_refl (term277 m)). Qed.
Lemma lem6899483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899484 (m : nat) : (term278 m) = (term266 m).
Proof. exact (MK_COMB (@lem6899483) (@lem6899482 m)). Qed.
Lemma lem6899485 (m : nat) : (term279 m) = (term269 m).
Proof. exact (eq_refl (term279 m)). Qed.
Lemma lem6899486 (m : nat) : (term280 m) = (term270 m).
Proof. exact (MK_COMB (@lem6899484 m) (@lem6899485 m)). Qed.
Lemma lem6899487 : term281 = term271.
Proof. exact (fun_ext (fun m : nat => @lem6899486 m)). Qed.
Lemma lem6899488 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899489 : term273 = term272.
Proof. exact (MK_COMB (@lem6899488) (@lem6899487)). Qed.
Lemma lem6899490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6899491 : term282 = term283.
Proof. exact (MK_COMB (@lem6899490) (@lem6899489)). Qed.
Lemma lem6899492 (m : nat) : (term277 m) = (term264 m).
Proof. exact (eq_refl (term277 m)). Qed.
Lemma lem6899493 : term284 = term275.
Proof. exact (fun_ext (fun m : nat => @lem6899492 m)). Qed.
Lemma lem6899494 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899495 : term285 = term286.
Proof. exact (MK_COMB (@lem6899494) (@lem6899493)). Qed.
Lemma lem6899496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899497 : term287 = term288.
Proof. exact (MK_COMB (@lem6899496) (@lem6899495)). Qed.
Lemma lem6899498 (m : nat) : (term279 m) = (term269 m).
Proof. exact (eq_refl (term279 m)). Qed.
Lemma lem6899499 : term289 = term276.
Proof. exact (fun_ext (fun m : nat => @lem6899498 m)). Qed.
Lemma lem6899500 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899501 : term290 = term291.
Proof. exact (MK_COMB (@lem6899500) (@lem6899499)). Qed.
Lemma lem6899502 : term274 = term292.
Proof. exact (MK_COMB (@lem6899497) (@lem6899501)). Qed.
Lemma lem6899503 : (term273 = term274) = (term272 = term292).
Proof. exact (MK_COMB (@lem6899491) (@lem6899502)). Qed.
Lemma lem6899504 : term272 = term292.
Proof. exact (EQ_MP (@lem6899503) (@lem6899481)). Qed.
Lemma lem6899611 : term250 = term292.
Proof. exact (TRANS (@lem6899477) (@lem6899504)). Qed.
Lemma lem6899612 : term102 = term292.
Proof. exact (TRANS (@lem6899347) (@lem6899611)). Qed.
Lemma lem6899613 (h1 : term102) : term292.
Proof. exact (EQ_MP (@lem6899612) (@lem6898999 h1)). Qed.
Lemma lem6899614 (n : nat) : ((term94 n) = (NUMERAL 0)) = ((term94 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term94 n) = (NUMERAL 0))). Qed.
Lemma lem6899615 : term95 = term95.
Proof. exact (fun_ext (fun n : nat => @lem6899614 n)). Qed.
Lemma lem6899616 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899617 : term96 = term96.
Proof. exact (MK_COMB (@lem6899616) (@lem6899615)). Qed.
Lemma lem6899618 (m : nat) : ((term89 m) = (NUMERAL 0)) = ((term89 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term89 m) = (NUMERAL 0))). Qed.
Lemma lem6899619 : term90 = term90.
Proof. exact (fun_ext (fun m : nat => @lem6899618 m)). Qed.
Lemma lem6899620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899621 : term91 = term91.
Proof. exact (MK_COMB (@lem6899620) (@lem6899619)). Qed.
Lemma lem6899622 (n : nat) : ((term84 n) = n) = ((term84 n) = n).
Proof. exact (eq_refl ((term84 n) = n)). Qed.
Lemma lem6899623 : term85 = term85.
Proof. exact (fun_ext (fun n : nat => @lem6899622 n)). Qed.
Lemma lem6899624 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899625 : term86 = term86.
Proof. exact (MK_COMB (@lem6899624) (@lem6899623)). Qed.
Lemma lem6899626 (m : nat) : ((term79 m) = m) = ((term79 m) = m).
Proof. exact (eq_refl ((term79 m) = m)). Qed.
Lemma lem6899627 : term80 = term80.
Proof. exact (fun_ext (fun m : nat => @lem6899626 m)). Qed.
Lemma lem6899628 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899629 : term81 = term81.
Proof. exact (MK_COMB (@lem6899628) (@lem6899627)). Qed.
Lemma lem6899630 (m : nat) (n : nat) : ((term71 m n) = (term72 m n)) = ((term71 m n) = (term72 m n)).
Proof. exact (eq_refl ((term71 m n) = (term72 m n))). Qed.
Lemma lem6899631 (m : nat) : (term73 m) = (term73 m).
Proof. exact (fun_ext (fun n : nat => @lem6899630 m n)). Qed.
Lemma lem6899632 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899633 (m : nat) : (term74 m) = (term74 m).
Proof. exact (MK_COMB (@lem6899632) (@lem6899631 m)). Qed.
Lemma lem6899634 : term75 = term75.
Proof. exact (fun_ext (fun m : nat => @lem6899633 m)). Qed.
Lemma lem6899635 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899636 : term76 = term76.
Proof. exact (MK_COMB (@lem6899635) (@lem6899634)). Qed.
Lemma lem6899637 (m : nat) (n : nat) : ((term65 m n) = (term66 m n)) = ((term65 m n) = (term66 m n)).
Proof. exact (eq_refl ((term65 m n) = (term66 m n))). Qed.
Lemma lem6899638 (m : nat) : (term67 m) = (term67 m).
Proof. exact (fun_ext (fun n : nat => @lem6899637 m n)). Qed.
Lemma lem6899639 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899640 (m : nat) : (term68 m) = (term68 m).
Proof. exact (MK_COMB (@lem6899639) (@lem6899638 m)). Qed.
Lemma lem6899641 : term69 = term69.
Proof. exact (fun_ext (fun m : nat => @lem6899640 m)). Qed.
Lemma lem6899642 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899643 : term70 = term70.
Proof. exact (MK_COMB (@lem6899642) (@lem6899641)). Qed.
Lemma lem6899644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899645 : term77 = term77.
Proof. exact (MK_COMB (@lem6899644) (@lem6899636)). Qed.
Lemma lem6899646 : term78 = term78.
Proof. exact (MK_COMB (@lem6899645) (@lem6899643)). Qed.
Lemma lem6899647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899648 : term82 = term82.
Proof. exact (MK_COMB (@lem6899647) (@lem6899629)). Qed.
Lemma lem6899649 : term83 = term83.
Proof. exact (MK_COMB (@lem6899648) (@lem6899646)). Qed.
Lemma lem6899650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899651 : term87 = term87.
Proof. exact (MK_COMB (@lem6899650) (@lem6899625)). Qed.
Lemma lem6899652 : term88 = term88.
Proof. exact (MK_COMB (@lem6899651) (@lem6899649)). Qed.
Lemma lem6899653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899654 : term92 = term92.
Proof. exact (MK_COMB (@lem6899653) (@lem6899621)). Qed.
Lemma lem6899655 : term93 = term93.
Proof. exact (MK_COMB (@lem6899654) (@lem6899652)). Qed.
Lemma lem6899656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899657 : term97 = term97.
Proof. exact (MK_COMB (@lem6899656) (@lem6899617)). Qed.
Lemma lem6899694 : term54 = term54.
Proof. exact (MK_COMB (@lem6899657) (@lem6899655)). Qed.
Lemma lem6899695 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem6899694) (@lem6899000 h1)). Qed.
Lemma lem6899696 (y : nat) (h1 : term234 y) : term234 y.
Proof. exact (h1). Qed.
Lemma lem6899697 (y' : nat) (y : nat) (h1 : term231 y' y) : term231 y' y.
Proof. exact (h1). Qed.
Lemma lem6899736 (m : nat) (n : nat) : (term239 m n) = (term239 m n).
Proof. exact (eq_refl (term239 m n)). Qed.
Lemma lem6899737 (m : nat) : (term254 m) = (term254 m).
Proof. exact (fun_ext (fun n : nat => @lem6899736 m n)). Qed.
Lemma lem6899738 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899739 (m : nat) : (term269 m) = (term269 m).
Proof. exact (MK_COMB (@lem6899738) (@lem6899737 m)). Qed.
Lemma lem6899740 : term276 = term276.
Proof. exact (fun_ext (fun m : nat => @lem6899739 m)). Qed.
Lemma lem6899741 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899742 : term291 = term291.
Proof. exact (MK_COMB (@lem6899741) (@lem6899740)). Qed.
Lemma lem6899783 (m : nat) (n : nat) : (term242 m n) = (term242 m n).
Proof. exact (eq_refl (term242 m n)). Qed.
Lemma lem6899784 (m : nat) : (term253 m) = (term253 m).
Proof. exact (fun_ext (fun n : nat => @lem6899783 m n)). Qed.
Lemma lem6899785 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899786 (m : nat) : (term264 m) = (term264 m).
Proof. exact (MK_COMB (@lem6899785) (@lem6899784 m)). Qed.
Lemma lem6899787 : term275 = term275.
Proof. exact (fun_ext (fun m : nat => @lem6899786 m)). Qed.
Lemma lem6899788 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899789 : term286 = term286.
Proof. exact (MK_COMB (@lem6899788) (@lem6899787)). Qed.
Lemma lem6899790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899791 : term288 = term288.
Proof. exact (MK_COMB (@lem6899790) (@lem6899789)). Qed.
Lemma lem6899792 : term292 = term292.
Proof. exact (MK_COMB (@lem6899791) (@lem6899742)). Qed.
Lemma lem6899793 (h1 : term102) : term292.
Proof. exact (EQ_MP (@lem6899792) (@lem6899613 h1)). Qed.
Lemma lem6899812 (m : nat) (n : nat) : ((term65 m n) = (term66 m n)) = ((term65 m n) = (term66 m n)).
Proof. exact (eq_refl ((term65 m n) = (term66 m n))). Qed.
Lemma lem6899813 (m : nat) : (term67 m) = (term67 m).
Proof. exact (fun_ext (fun n : nat => @lem6899812 m n)). Qed.
Lemma lem6899814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899815 (m : nat) : (term68 m) = (term68 m).
Proof. exact (MK_COMB (@lem6899814) (@lem6899813 m)). Qed.
Lemma lem6899816 : term69 = term69.
Proof. exact (fun_ext (fun m : nat => @lem6899815 m)). Qed.
Lemma lem6899817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899818 : term70 = term70.
Proof. exact (MK_COMB (@lem6899817) (@lem6899816)). Qed.
Lemma lem6899837 (m : nat) (n : nat) : ((term71 m n) = (term72 m n)) = ((term71 m n) = (term72 m n)).
Proof. exact (eq_refl ((term71 m n) = (term72 m n))). Qed.
Lemma lem6899838 (m : nat) : (term73 m) = (term73 m).
Proof. exact (fun_ext (fun n : nat => @lem6899837 m n)). Qed.
Lemma lem6899839 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899840 (m : nat) : (term74 m) = (term74 m).
Proof. exact (MK_COMB (@lem6899839) (@lem6899838 m)). Qed.
Lemma lem6899841 : term75 = term75.
Proof. exact (fun_ext (fun m : nat => @lem6899840 m)). Qed.
Lemma lem6899842 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899843 : term76 = term76.
Proof. exact (MK_COMB (@lem6899842) (@lem6899841)). Qed.
Lemma lem6899844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899845 : term77 = term77.
Proof. exact (MK_COMB (@lem6899844) (@lem6899843)). Qed.
Lemma lem6899846 : term78 = term78.
Proof. exact (MK_COMB (@lem6899845) (@lem6899818)). Qed.
Lemma lem6899859 (m : nat) : ((term79 m) = m) = ((term79 m) = m).
Proof. exact (eq_refl ((term79 m) = m)). Qed.
Lemma lem6899860 : term80 = term80.
Proof. exact (fun_ext (fun m : nat => @lem6899859 m)). Qed.
Lemma lem6899861 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899862 : term81 = term81.
Proof. exact (MK_COMB (@lem6899861) (@lem6899860)). Qed.
Lemma lem6899863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899864 : term82 = term82.
Proof. exact (MK_COMB (@lem6899863) (@lem6899862)). Qed.
Lemma lem6899865 : term83 = term83.
Proof. exact (MK_COMB (@lem6899864) (@lem6899846)). Qed.
Lemma lem6899878 (n : nat) : ((term84 n) = n) = ((term84 n) = n).
Proof. exact (eq_refl ((term84 n) = n)). Qed.
Lemma lem6899879 : term85 = term85.
Proof. exact (fun_ext (fun n : nat => @lem6899878 n)). Qed.
Lemma lem6899880 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899881 : term86 = term86.
Proof. exact (MK_COMB (@lem6899880) (@lem6899879)). Qed.
Lemma lem6899882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899883 : term87 = term87.
Proof. exact (MK_COMB (@lem6899882) (@lem6899881)). Qed.
Lemma lem6899884 : term88 = term88.
Proof. exact (MK_COMB (@lem6899883) (@lem6899865)). Qed.
Lemma lem6899897 (m : nat) : ((term89 m) = (NUMERAL 0)) = ((term89 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term89 m) = (NUMERAL 0))). Qed.
Lemma lem6899898 : term90 = term90.
Proof. exact (fun_ext (fun m : nat => @lem6899897 m)). Qed.
Lemma lem6899899 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899900 : term91 = term91.
Proof. exact (MK_COMB (@lem6899899) (@lem6899898)). Qed.
Lemma lem6899901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899902 : term92 = term92.
Proof. exact (MK_COMB (@lem6899901) (@lem6899900)). Qed.
Lemma lem6899903 : term93 = term93.
Proof. exact (MK_COMB (@lem6899902) (@lem6899884)). Qed.
Lemma lem6899916 (n : nat) : ((term94 n) = (NUMERAL 0)) = ((term94 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term94 n) = (NUMERAL 0))). Qed.
Lemma lem6899917 : term95 = term95.
Proof. exact (fun_ext (fun n : nat => @lem6899916 n)). Qed.
Lemma lem6899918 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899919 : term96 = term96.
Proof. exact (MK_COMB (@lem6899918) (@lem6899917)). Qed.
Lemma lem6899920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899921 : term97 = term97.
Proof. exact (MK_COMB (@lem6899920) (@lem6899919)). Qed.
Lemma lem6899922 : term54 = term54.
Proof. exact (MK_COMB (@lem6899921) (@lem6899903)). Qed.
Lemma lem6899923 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem6899922) (@lem6899695 h1)). Qed.
Lemma lem6899960 (y' : nat) (y : nat) : (term200 y' y) = (term200 y' y).
Proof. exact (eq_refl (term200 y' y)). Qed.
Lemma lem6899971 (y : nat) : (term124 y) = (term124 y).
Proof. exact (eq_refl (term124 y)). Qed.
Lemma lem6899980 (y : nat) (y' : nat) : ((Nat.mul y' y) = y') = ((Nat.mul y' y) = y').
Proof. exact (eq_refl ((Nat.mul y' y) = y')). Qed.
Lemma lem6899981 (y : nat) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : nat => @lem6899980 y y')). Qed.
Lemma lem6899982 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899983 (y : nat) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6899982) (@lem6899981 y)). Qed.
Lemma lem6899992 (y : nat) (y' : nat) : ((Nat.mul y y') = y') = ((Nat.mul y y') = y').
Proof. exact (eq_refl ((Nat.mul y y') = y')). Qed.
Lemma lem6899993 (y : nat) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : nat => @lem6899992 y y')). Qed.
Lemma lem6899994 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6899995 (y : nat) : (term34 y) = (term34 y).
Proof. exact (MK_COMB (@lem6899994) (@lem6899993 y)). Qed.
Lemma lem6899996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6899997 (y : nat) : (term36 y) = (term36 y).
Proof. exact (MK_COMB (@lem6899996) (@lem6899995 y)). Qed.
Lemma lem6899998 (y : nat) : (term40 y) = (term40 y).
Proof. exact (MK_COMB (@lem6899997 y) (@lem6899983 y)). Qed.
Lemma lem6899999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6900000 (y : nat) : (term129 y) = (term129 y).
Proof. exact (MK_COMB (@lem6899999) (@lem6899998 y)). Qed.
Lemma lem6900001 (y : nat) : (term130 y) = (term130 y).
Proof. exact (MK_COMB (@lem6900000 y) (@lem6899971 y)). Qed.
Lemma lem6900002 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6900003 (y : nat) : (term131 y) = (term131 y).
Proof. exact (MK_COMB (@lem6900002) (@lem6900001 y)). Qed.
Lemma lem6900004 (y' : nat) (y : nat) : (term231 y' y) = (term231 y' y).
Proof. exact (MK_COMB (@lem6900003 y) (@lem6899960 y' y)). Qed.
Lemma lem6900005 (y' : nat) (y : nat) (h1 : term231 y' y) : term231 y' y.
Proof. exact (EQ_MP (@lem6900004 y' y) (@lem6899697 y' y h1)). Qed.
Lemma lem6900006 (h1 : term54) : term93.
Proof. exact (proj2 (@lem6899923 h1)). Qed.
Lemma lem6900008 (h1 : term54) : term88.
Proof. exact (proj2 (@lem6900006 h1)). Qed.
Lemma lem6900010 (h1 : term54) : term83.
Proof. exact (proj2 (@lem6900008 h1)). Qed.
Lemma lem6900011 (h1 : term54) : term86.
Proof. exact (proj1 (@lem6900008 h1)). Qed.
Lemma lem6900013 (h1 : term54) : term81.
Proof. exact (proj1 (@lem6900010 h1)). Qed.
Lemma lem6900016 (h1 : term102) : term291.
Proof. exact (proj2 (@lem6899793 h1)). Qed.
Lemma lem6900018 (y : nat) (h1 : term130 y) : term130 y.
Proof. exact (h1). Qed.
Lemma lem6900019 (y' : nat) (y : nat) (h1 : term200 y' y) : term200 y' y.
Proof. exact (h1). Qed.
Lemma lem6900021 (y : nat) (h1 : term130 y) : term40 y.
Proof. exact (proj1 (@lem6900018 y h1)). Qed.
Lemma lem6900022 (y : nat) (h1 : term130 y) : term39 y.
Proof. exact (proj2 (@lem6900021 y h1)). Qed.
Lemma lem6900025 (y' : nat) (y : nat) (h1 : term200 y' y) : term179 y y'.
Proof. exact (proj1 (@lem6900019 y' y h1)). Qed.
Lemma lem6900115 (m : nat) (n : nat) : (term239 m n) = (term293 m n).
Proof. exact (@lem19490 (m = term4) (term294 m n) (n = term4)). Qed.
Lemma lem6900116 (m : nat) : (term254 m) = (term295 m).
Proof. exact (fun_ext (fun n : nat => @lem6900115 m n)). Qed.
Lemma lem6900117 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6900118 (m : nat) : (term269 m) = (term296 m).
Proof. exact (MK_COMB (@lem6900117) (@lem6900116 m)). Qed.
Lemma lem6900119 : term276 = term297.
Proof. exact (fun_ext (fun m : nat => @lem6900118 m)). Qed.
Lemma lem6900120 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6900122 : term291 = term298.
Proof. exact (MK_COMB (@lem6900120) (@lem6900119)). Qed.
Lemma lem6900123 (h1 : term102) : term298.
Proof. exact (EQ_MP (@lem6900122) (@lem6900016 h1)). Qed.
Lemma lem6900136 (y : nat) (y' : nat) : ((Nat.mul y' y) = y') = ((Nat.mul y' y) = y').
Proof. exact (eq_refl ((Nat.mul y' y) = y')). Qed.
Lemma lem6900137 (y : nat) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : nat => @lem6900136 y y')). Qed.
Lemma lem6900138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6900140 (y : nat) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6900138) (@lem6900137 y)). Qed.
Lemma lem6900141 (y : nat) (h1 : term130 y) : term39 y.
Proof. exact (EQ_MP (@lem6900140 y) (@lem6900022 y h1)). Qed.
Lemma lem6900157 (n : nat) : ((term84 n) = n) = ((term84 n) = n).
Proof. exact (eq_refl ((term84 n) = n)). Qed.
Lemma lem6900158 : term85 = term85.
Proof. exact (fun_ext (fun n : nat => @lem6900157 n)). Qed.
Lemma lem6900159 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6900161 : term86 = term86.
Proof. exact (MK_COMB (@lem6900159) (@lem6900158)). Qed.
Lemma lem6900162 (h1 : term54) : term86.
Proof. exact (EQ_MP (@lem6900161) (@lem6900011 h1)). Qed.
Lemma lem6900245 (y : nat) (y' : nat) (h1 : term108 y y') : term108 y y'.
Proof. exact (h1). Qed.
Lemma lem6900268 (m : nat) : ((term79 m) = m) = ((term79 m) = m).
Proof. exact (eq_refl ((term79 m) = m)). Qed.
Lemma lem6900269 : term80 = term80.
Proof. exact (fun_ext (fun m : nat => @lem6900268 m)). Qed.
Lemma lem6900270 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6900272 : term81 = term81.
Proof. exact (MK_COMB (@lem6900270) (@lem6900269)). Qed.
Lemma lem6900273 (h1 : term54) : term81.
Proof. exact (EQ_MP (@lem6900272) (@lem6900013 h1)). Qed.
Lemma lem6900349 (y : nat) (y' : nat) (h1 : term115 y y') : term115 y y'.
Proof. exact (h1). Qed.
Lemma lem6900380 (_92048 : nat) (h1 : term102) : term299 _92048.
Proof. exact (@lem6900123 h1 _92048). Qed.
Lemma lem6900381 (_92048 : nat) : (term299 _92048) = (term296 _92048).
Proof. exact (eq_refl (term299 _92048)). Qed.
Lemma lem6900382 (_92048 : nat) (h1 : term102) : term296 _92048.
Proof. exact (EQ_MP (@lem6900381 _92048) (@lem6900380 _92048 h1)). Qed.
Lemma lem6900383 (_92048 : nat) (_92049 : nat) (h1 : term102) : term300 _92048 _92049.
Proof. exact (@lem6900382 _92048 h1 _92049). Qed.
Lemma lem6900384 (_92048 : nat) (_92049 : nat) : (term300 _92048 _92049) = (term293 _92048 _92049).
Proof. exact (eq_refl (term300 _92048 _92049)). Qed.
Lemma lem6900385 (_92048 : nat) (_92049 : nat) (h1 : term102) : term293 _92048 _92049.
Proof. exact (EQ_MP (@lem6900384 _92048 _92049) (@lem6900383 _92048 _92049 h1)). Qed.
Lemma lem6900389 (_92051 : nat) (y : nat) (h1 : term130 y) : term24 y _92051.
Proof. exact (@lem6900141 y h1 _92051). Qed.
Lemma lem6900390 (y : nat) (_92051 : nat) : (term24 y _92051) = ((Nat.mul _92051 y) = _92051).
Proof. exact (eq_refl (term24 y _92051)). Qed.
Lemma lem6900398 (_92054 : nat) (h1 : term54) : term301 _92054.
Proof. exact (@lem6900162 h1 _92054). Qed.
Lemma lem6900399 (_92054 : nat) : (term301 _92054) = ((term84 _92054) = _92054).
Proof. exact (eq_refl (term301 _92054)). Qed.
Lemma lem6900437 (_92067 : nat) (h1 : term54) : term302 _92067.
Proof. exact (@lem6900273 h1 _92067). Qed.
Lemma lem6900438 (_92067 : nat) : (term302 _92067) = ((term79 _92067) = _92067).
Proof. exact (eq_refl (term302 _92067)). Qed.
Lemma lem6900493 (y : nat) (h1 : term130 y) : term124 y.
Proof. exact (proj2 (@lem6900018 y h1)). Qed.
Lemma lem6900509 (_92048 : nat) (_92049 : nat) (h1 : term102) : term303 _92048 _92049.
Proof. exact (proj2 (@lem6900385 _92048 _92049 h1)). Qed.
Lemma lem6900533 (y' : nat) (y : nat) (h1 : term200 y' y) : y = term4.
Proof. exact (proj2 (@lem6900019 y' y h1)). Qed.
Lemma lem6900535 (y : nat) (y' : nat) (h1 : term108 y y') : term108 y y'.
Proof. exact (h1). Qed.
Lemma lem6900571 (y' : nat) (y : nat) (h1 : term200 y' y) : y = term4.
Proof. exact (proj2 (@lem6900019 y' y h1)). Qed.
Lemma lem6900573 (y : nat) (y' : nat) (h1 : term115 y y') : term115 y y'.
Proof. exact (h1). Qed.
Lemma lem6900698 (y' : nat) : (term304 y') = (term304 y').
Proof. exact (eq_refl (term304 y')). Qed.
Lemma lem6900699 (y' : nat) (y : nat) (h1 : term200 y' y) : (term305 y' y) = (term306 y').
Proof. exact (MK_COMB (@lem6900698 y') (@lem6900533 y' y h1)). Qed.
Lemma lem6900700 (y' : nat) : (term306 y') = (term307 y').
Proof. exact (eq_refl (term306 y')). Qed.
Lemma lem6900701 (y' : nat) (y : nat) : (term308 y' y) = (term308 y' y).
Proof. exact (eq_refl (term308 y' y)). Qed.
Lemma lem6900702 (y : nat) (y' : nat) : ((term305 y' y) = (term306 y')) = ((term305 y' y) = (term307 y')).
Proof. exact (MK_COMB (@lem6900701 y' y) (@lem6900700 y')). Qed.
Lemma lem6900703 (y : nat) (y' : nat) : (term305 y' y) = (term108 y y').
Proof. exact (eq_refl (term305 y' y)). Qed.
Lemma lem6900704 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6900705 (y : nat) (y' : nat) : (term308 y' y) = (term309 y y').
Proof. exact (MK_COMB (@lem6900704) (@lem6900703 y y')). Qed.
Lemma lem6900706 (y' : nat) : (term307 y') = (term307 y').
Proof. exact (eq_refl (term307 y')). Qed.
Lemma lem6900707 (y : nat) (y' : nat) : ((term305 y' y) = (term307 y')) = ((term108 y y') = (term307 y')).
Proof. exact (MK_COMB (@lem6900705 y y') (@lem6900706 y')). Qed.
Lemma lem6900708 (y : nat) (y' : nat) : ((term305 y' y) = (term306 y')) = ((term108 y y') = (term307 y')).
Proof. exact (TRANS (@lem6900702 y y') (@lem6900707 y y')). Qed.
Lemma lem6900709 (y' : nat) (y : nat) (h1 : term200 y' y) : (term108 y y') = (term307 y').
Proof. exact (EQ_MP (@lem6900708 y y') (@lem6900699 y' y h1)). Qed.
Lemma lem6900710 (y' : nat) (y : nat) (h1 : term108 y y') (h2 : term200 y' y) : term307 y'.
Proof. exact (EQ_MP (@lem6900709 y' y h2) (@lem6900535 y y' h1)). Qed.
Lemma lem6900851 (y' : nat) : (term310 y') = (term310 y').
Proof. exact (eq_refl (term310 y')). Qed.
Lemma lem6900852 (y' : nat) (y : nat) (h1 : term200 y' y) : (term311 y' y) = (term312 y').
Proof. exact (MK_COMB (@lem6900851 y') (@lem6900571 y' y h1)). Qed.
Lemma lem6900853 (y' : nat) : (term312 y') = (term313 y').
Proof. exact (eq_refl (term312 y')). Qed.
Lemma lem6900854 (y' : nat) (y : nat) : (term314 y' y) = (term314 y' y).
Proof. exact (eq_refl (term314 y' y)). Qed.
Lemma lem6900855 (y : nat) (y' : nat) : ((term311 y' y) = (term312 y')) = ((term311 y' y) = (term313 y')).
Proof. exact (MK_COMB (@lem6900854 y' y) (@lem6900853 y')). Qed.
Lemma lem6900856 (y : nat) (y' : nat) : (term311 y' y) = (term115 y y').
Proof. exact (eq_refl (term311 y' y)). Qed.
Lemma lem6900857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6900858 (y : nat) (y' : nat) : (term314 y' y) = (term315 y y').
Proof. exact (MK_COMB (@lem6900857) (@lem6900856 y y')). Qed.
Lemma lem6900859 (y' : nat) : (term313 y') = (term313 y').
Proof. exact (eq_refl (term313 y')). Qed.
Lemma lem6900860 (y : nat) (y' : nat) : ((term311 y' y) = (term313 y')) = ((term115 y y') = (term313 y')).
Proof. exact (MK_COMB (@lem6900858 y y') (@lem6900859 y')). Qed.
Lemma lem6900861 (y : nat) (y' : nat) : ((term311 y' y) = (term312 y')) = ((term115 y y') = (term313 y')).
Proof. exact (TRANS (@lem6900855 y y') (@lem6900860 y y')). Qed.
Lemma lem6900862 (y' : nat) (y : nat) (h1 : term200 y' y) : (term115 y y') = (term313 y').
Proof. exact (EQ_MP (@lem6900861 y y') (@lem6900852 y' y h1)). Qed.
Lemma lem6900863 (y' : nat) (y : nat) (h1 : term115 y y') (h2 : term200 y' y) : term313 y'.
Proof. exact (EQ_MP (@lem6900862 y' y h2) (@lem6900573 y y' h1)). Qed.
Lemma lem6900949 (_92051 : nat) (y : nat) (h1 : term130 y) : (Nat.mul _92051 y) = _92051.
Proof. exact (EQ_MP (@lem6900390 y _92051) (@lem6900389 _92051 y h1)). Qed.
Lemma lem6900950 (y : nat) (h1 : term130 y) : (term84 y) = term4.
Proof. exact (@lem6900949 term4 y h1). Qed.
Lemma lem6900951 (y : nat) (h1 : term130 y) : term316 y.
Proof. exact (fun h0 : term317 y => @lem6900950 y h1). Qed.
Lemma lem6900953 (p : Prop) : (term318 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6900954 (y : nat) : (term316 y) = ((term84 y) = term4).
Proof. exact (@lem6900953 ((term84 y) = term4)). Qed.
Lemma lem6900955 (y : nat) (h1 : term130 y) : (term84 y) = term4.
Proof. exact (EQ_MP (@lem6900954 y) (@lem6900951 y h1)). Qed.
Lemma lem6900961 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6900962 (_92048 : nat) (_92049 : nat) : (term303 _92048 _92049) = (term319 _92048 _92049).
Proof. exact (@lem6900961 (_92049 = term4) (term294 _92048 _92049)). Qed.
Lemma lem6900972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6900973 (_92048 : nat) (_92049 : nat) : (term320 _92048 _92049) = (term321 _92048 _92049).
Proof. exact (MK_COMB (@lem6900972) (@lem6900962 _92048 _92049)). Qed.
Lemma lem6900983 (_92048 : nat) (_92049 : nat) : (term319 _92048 _92049) = (term319 _92048 _92049).
Proof. exact (eq_refl (term319 _92048 _92049)). Qed.
Lemma lem6900984 (_92048 : nat) (_92049 : nat) : ((term303 _92048 _92049) = (term319 _92048 _92049)) = ((term319 _92048 _92049) = (term319 _92048 _92049)).
Proof. exact (MK_COMB (@lem6900973 _92048 _92049) (@lem6900983 _92048 _92049)). Qed.
Lemma lem6900986 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6900987 (x : Prop) : (x = x) = True.
Proof. exact (@lem6900986 Prop x). Qed.
Lemma lem6900988 (_92048 : nat) (_92049 : nat) : ((term319 _92048 _92049) = (term319 _92048 _92049)) = True.
Proof. exact (@lem6900987 (term319 _92048 _92049)). Qed.
Lemma lem6900989 (_92048 : nat) (_92049 : nat) : ((term303 _92048 _92049) = (term319 _92048 _92049)) = True.
Proof. exact (TRANS (@lem6900984 _92048 _92049) (@lem6900988 _92048 _92049)). Qed.
Lemma lem6900990 (_92048 : nat) (_92049 : nat) : True = ((term303 _92048 _92049) = (term319 _92048 _92049)).
Proof. exact (SYM (@lem6900989 _92048 _92049)). Qed.
Lemma lem6900991 (_92048 : nat) (_92049 : nat) : (term303 _92048 _92049) = (term319 _92048 _92049).
Proof. exact (EQ_MP (@lem6900990 _92048 _92049) (@lem0)). Qed.
Lemma lem6900992 (_92048 : nat) (_92049 : nat) (h1 : term102) : term319 _92048 _92049.
Proof. exact (EQ_MP (@lem6900991 _92048 _92049) (@lem6900509 _92048 _92049 h1)). Qed.
Lemma lem6900994 (b : Prop) (a : Prop) : (a \/ b) = (term322 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6900995 (_92048 : nat) (_92049 : nat) : (term319 _92048 _92049) = (term323 _92048 _92049).
Proof. exact (@lem6900994 (term294 _92048 _92049) (_92049 = term4)). Qed.
Lemma lem6900997 (a : Prop) : (term324 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6900998 (_92048 : nat) (_92049 : nat) : (term325 _92048 _92049) = ((Nat.mul _92048 _92049) = term4).
Proof. exact (@lem6900997 ((Nat.mul _92048 _92049) = term4)). Qed.
Lemma lem6900999 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6901000 (_92048 : nat) (_92049 : nat) : (term326 _92048 _92049) = (term327 _92048 _92049).
Proof. exact (MK_COMB (@lem6900999) (@lem6900998 _92048 _92049)). Qed.
Lemma lem6901001 (_92049 : nat) : (_92049 = term4) = (_92049 = term4).
Proof. exact (eq_refl (_92049 = term4)). Qed.
Lemma lem6901002 (_92048 : nat) (_92049 : nat) : (term323 _92048 _92049) = (term328 _92048 _92049).
Proof. exact (MK_COMB (@lem6901000 _92048 _92049) (@lem6901001 _92049)). Qed.
Lemma lem6901003 (_92048 : nat) (_92049 : nat) : (term319 _92048 _92049) = (term328 _92048 _92049).
Proof. exact (TRANS (@lem6900995 _92048 _92049) (@lem6901002 _92048 _92049)). Qed.
Lemma lem6901006 (_92048 : nat) (_92049 : nat) (h1 : term102) : term328 _92048 _92049.
Proof. exact (EQ_MP (@lem6901003 _92048 _92049) (@lem6900992 _92048 _92049 h1)). Qed.
Lemma lem6901007 (y : nat) (h1 : term102) : term329 y.
Proof. exact (@lem6901006 term4 y h1). Qed.
Lemma lem6901010 (y : nat) (h1 : term102) (h2 : term130 y) : y = term4.
Proof. exact (@lem6901007 y h1 (@lem6900955 y h2)). Qed.
Lemma lem6901011 (y : nat) (h1 : term102) (h2 : term130 y) : term330 y.
Proof. exact (fun h0 : term124 y => @lem6901010 y h1 h2). Qed.
Lemma lem6901013 (p : Prop) : (term318 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6901014 (y : nat) : (term330 y) = (y = term4).
Proof. exact (@lem6901013 (y = term4)). Qed.
Lemma lem6901015 (y : nat) (h1 : term102) (h2 : term130 y) : y = term4.
Proof. exact (EQ_MP (@lem6901014 y) (@lem6901011 y h1 h2)). Qed.
Lemma lem6901018 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6901020 (y : nat) : (term124 y) = (term331 y).
Proof. exact (@lem6901018 (y = term4)). Qed.
Lemma lem6901023 (y : nat) (h1 : term130 y) : term331 y.
Proof. exact (EQ_MP (@lem6901020 y) (@lem6900493 y h1)). Qed.
Lemma lem6901026 (y : nat) (h1 : term102) (h2 : term130 y) : False.
Proof. exact (@lem6901023 y h2 (@lem6901015 y h1 h2)). Qed.
Lemma lem6901027 (y : nat) (h1 : term102) (h2 : term130 y) : term332.
Proof. exact (fun h0 : ~ False => @lem6901026 y h1 h2). Qed.
Lemma lem6901029 (p : Prop) : (term318 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6901030 : term332 = False.
Proof. exact (@lem6901029 False). Qed.
Lemma lem6901031 (y : nat) (h1 : term102) (h2 : term130 y) : False.
Proof. exact (EQ_MP (@lem6901030) (@lem6901027 y h1 h2)). Qed.
Lemma lem6901089 (_92054 : nat) (h1 : term54) : (term84 _92054) = _92054.
Proof. exact (EQ_MP (@lem6900399 _92054) (@lem6900398 _92054 h1)). Qed.
Lemma lem6901090 (y' : nat) (h1 : term54) : (term84 y') = y'.
Proof. exact (@lem6901089 y' h1). Qed.
Lemma lem6901091 (y' : nat) (h1 : term54) : term333 y'.
Proof. exact (fun h0 : term307 y' => @lem6901090 y' h1). Qed.
Lemma lem6901093 (p : Prop) : (term318 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6901094 (y' : nat) : (term333 y') = ((term84 y') = y').
Proof. exact (@lem6901093 ((term84 y') = y')). Qed.
Lemma lem6901095 (y' : nat) (h1 : term54) : (term84 y') = y'.
Proof. exact (EQ_MP (@lem6901094 y') (@lem6901091 y' h1)). Qed.
Lemma lem6901098 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6901100 (y' : nat) : (term307 y') = (term334 y').
Proof. exact (@lem6901098 ((term84 y') = y')). Qed.
Lemma lem6901103 (y' : nat) (y : nat) (h1 : term108 y y') (h2 : term200 y' y) : term334 y'.
Proof. exact (EQ_MP (@lem6901100 y') (@lem6900710 y' y h1 h2)). Qed.
Lemma lem6901106 (y' : nat) (y : nat) (h1 : term108 y y') (h2 : term54) (h3 : term200 y' y) : False.
Proof. exact (@lem6901103 y' y h1 h3 (@lem6901095 y' h2)). Qed.
Lemma lem6901107 (y' : nat) (y : nat) (h1 : term108 y y') (h2 : term54) (h3 : term200 y' y) : term332.
Proof. exact (fun h0 : ~ False => @lem6901106 y' y h1 h2 h3). Qed.
Lemma lem6901109 (p : Prop) : (term318 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6901110 : term332 = False.
Proof. exact (@lem6901109 False). Qed.
Lemma lem6901169 (_92067 : nat) (h1 : term54) : (term79 _92067) = _92067.
Proof. exact (EQ_MP (@lem6900438 _92067) (@lem6900437 _92067 h1)). Qed.
Lemma lem6901170 (y' : nat) (h1 : term54) : (term79 y') = y'.
Proof. exact (@lem6901169 y' h1). Qed.
Lemma lem6901171 (y' : nat) (h1 : term54) : term335 y'.
Proof. exact (fun h0 : term313 y' => @lem6901170 y' h1). Qed.
Lemma lem6901173 (p : Prop) : (term318 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6901174 (y' : nat) : (term335 y') = ((term79 y') = y').
Proof. exact (@lem6901173 ((term79 y') = y')). Qed.
Lemma lem6901175 (y' : nat) (h1 : term54) : (term79 y') = y'.
Proof. exact (EQ_MP (@lem6901174 y') (@lem6901171 y' h1)). Qed.
Lemma lem6901178 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6901180 (y' : nat) : (term313 y') = (term336 y').
Proof. exact (@lem6901178 ((term79 y') = y')). Qed.
Lemma lem6901183 (y' : nat) (y : nat) (h1 : term115 y y') (h2 : term200 y' y) : term336 y'.
Proof. exact (EQ_MP (@lem6901180 y') (@lem6900863 y' y h1 h2)). Qed.
Lemma lem6901186 (y' : nat) (y : nat) (h1 : term115 y y') (h2 : term54) (h3 : term200 y' y) : False.
Proof. exact (@lem6901183 y' y h1 h3 (@lem6901175 y' h2)). Qed.
Lemma lem6901187 (y' : nat) (y : nat) (h1 : term115 y y') (h2 : term54) (h3 : term200 y' y) : term332.
Proof. exact (fun h0 : ~ False => @lem6901186 y' y h1 h2 h3). Qed.
Lemma lem6901189 (p : Prop) : (term318 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6901190 : term332 = False.
Proof. exact (@lem6901189 False). Qed.
Lemma lem6901192 (y' : nat) (y : nat) (h1 : term115 y y') (h2 : term54) (h3 : term200 y' y) : False.
Proof. exact (EQ_MP (@lem6901190) (@lem6901187 y' y h1 h2 h3)). Qed.
Lemma lem6901193 (y' : nat) (y : nat) (h1 : term108 y y') (h2 : term54) (h3 : term200 y' y) : False.
Proof. exact (EQ_MP (@lem6901110) (@lem6901107 y' y h1 h2 h3)). Qed.
Lemma lem6901194 (y' : nat) (y : nat) (h1 : term115 y y') (h2 : term54) (h3 : term200 y' y) : (term115 y y') = False.
Proof. exact (prop_ext (fun h4 : term115 y y' => @lem6901192 y' y h1 h2 h3) (fun h4 : False => @lem6900573 y y' h1)). Qed.
Lemma lem6901195 (y' : nat) (y : nat) (h1 : term115 y y') (h2 : term54) (h3 : term200 y' y) : False.
Proof. exact (EQ_MP (@lem6901194 y' y h1 h2 h3) (@lem6900573 y y' h1)). Qed.
Lemma lem6901196 (y' : nat) (y : nat) (h1 : term108 y y') (h2 : term54) (h3 : term200 y' y) : (term108 y y') = False.
Proof. exact (prop_ext (fun h4 : term108 y y' => @lem6901193 y' y h1 h2 h3) (fun h4 : False => @lem6900535 y y' h1)). Qed.
Lemma lem6901197 (y' : nat) (y : nat) (h1 : term108 y y') (h2 : term54) (h3 : term200 y' y) : False.
Proof. exact (EQ_MP (@lem6901196 y' y h1 h2 h3) (@lem6900535 y y' h1)). Qed.
Lemma lem6901198 (y' : nat) (y : nat) (h1 : term115 y y') (h2 : term54) (h3 : term200 y' y) : (term115 y y') = False.
Proof. exact (prop_ext (fun h4 : term115 y y' => @lem6901195 y' y h1 h2 h3) (fun h4 : False => @lem6900349 y y' h1)). Qed.
Lemma lem6901199 (y' : nat) (y : nat) (h1 : term115 y y') (h2 : term54) (h3 : term200 y' y) : False.
Proof. exact (EQ_MP (@lem6901198 y' y h1 h2 h3) (@lem6900349 y y' h1)). Qed.
Lemma lem6901200 (y' : nat) (y : nat) (h1 : term108 y y') (h2 : term54) (h3 : term200 y' y) : (term108 y y') = False.
Proof. exact (prop_ext (fun h4 : term108 y y' => @lem6901197 y' y h1 h2 h3) (fun h4 : False => @lem6900245 y y' h1)). Qed.
Lemma lem6901201 (y' : nat) (y : nat) (h1 : term108 y y') (h2 : term54) (h3 : term200 y' y) : False.
Proof. exact (EQ_MP (@lem6901200 y' y h1 h2 h3) (@lem6900245 y y' h1)). Qed.
Lemma lem6901202 (y' : nat) (y : nat) (h1 : term115 y y') (h2 : term54) (h3 : term200 y' y) : (term115 y y') = False.
Proof. exact (prop_ext (fun h4 : term115 y y' => @lem6901199 y' y h1 h2 h3) (fun h4 : False => @lem6900349 y y' h1)). Qed.
Lemma lem6901203 (y' : nat) (y : nat) (h1 : term115 y y') (h2 : term54) (h3 : term200 y' y) : False.
Proof. exact (EQ_MP (@lem6901202 y' y h1 h2 h3) (@lem6900349 y y' h1)). Qed.
Lemma lem6901204 (y' : nat) (y : nat) (h1 : term108 y y') (h2 : term54) (h3 : term200 y' y) : (term108 y y') = False.
Proof. exact (prop_ext (fun h4 : term108 y y' => @lem6901201 y' y h1 h2 h3) (fun h4 : False => @lem6900245 y y' h1)). Qed.
Lemma lem6901205 (y' : nat) (y : nat) (h1 : term108 y y') (h2 : term54) (h3 : term200 y' y) : False.
Proof. exact (EQ_MP (@lem6901204 y' y h1 h2 h3) (@lem6900245 y y' h1)). Qed.
Lemma lem6901206 (y' : nat) (y : nat) (h1 : term54) (h2 : term200 y' y) : False.
Proof. exact (or_elim (@lem6900025 y' y h2) (fun h0 : term108 y y' => @lem6901205 y' y h0 h1 h2) (fun h0 : term115 y y' => @lem6901203 y' y h0 h1 h2)). Qed.
Lemma lem6901207 (y' : nat) (y : nat) (h1 : term102) (h2 : term54) (h3 : term231 y' y) : False.
Proof. exact (or_elim (@lem6900005 y' y h3) (fun h0 : term130 y => @lem6901031 y h1 h0) (fun h0 : term200 y' y => @lem6901206 y' y h2 h0)). Qed.
Lemma lem6901208 (y' : nat) (y : nat) (h1 : term102) (h2 : term54) (h3 : term231 y' y) : (term231 y' y) = False.
Proof. exact (prop_ext (fun h4 : term231 y' y => @lem6901207 y' y h1 h2 h3) (fun h4 : False => @lem6900005 y' y h3)). Qed.
Lemma lem6901209 (y' : nat) (y : nat) (h1 : term102) (h2 : term54) (h3 : term231 y' y) : False.
Proof. exact (EQ_MP (@lem6901208 y' y h1 h2 h3) (@lem6900005 y' y h3)). Qed.
Lemma lem6901210 (y' : nat) (y : nat) (h1 : term102) (h2 : term54) (h3 : term231 y' y) : term54 = False.
Proof. exact (prop_ext (fun h4 : term54 => @lem6901209 y' y h1 h2 h3) (fun h4 : False => @lem6899923 h2)). Qed.
Lemma lem6901211 (y' : nat) (y : nat) (h1 : term102) (h2 : term54) (h3 : term231 y' y) : False.
Proof. exact (EQ_MP (@lem6901210 y' y h1 h2 h3) (@lem6899923 h2)). Qed.
Lemma lem6901212 (y : nat) (h1 : term102) (h2 : term234 y) (h3 : term54) : False.
Proof. exact (ex_elim (@lem6899696 y h2) (fun y' : nat => fun h0 : term233 y y' => @lem6901211 y' y h1 h3 h0)). Qed.
Lemma lem6901213 (h1 : term102) (h2 : term62) (h3 : term54) : False.
Proof. exact (ex_elim (@lem6899316 h2) (fun y : nat => fun h0 : term235 y => @lem6901212 y h1 h0 h3)). Qed.
Lemma lem6901214 (h1 : term102) (h2 : term62) (h3 : term54) : term54 = False.
Proof. exact (prop_ext (fun h4 : term54 => @lem6901213 h1 h2 h3) (fun h4 : False => @lem6899695 h3)). Qed.
Lemma lem6901215 (h1 : term102) (h2 : term62) (h3 : term54) : False.
Proof. exact (EQ_MP (@lem6901214 h1 h2 h3) (@lem6899695 h3)). Qed.
Lemma lem6901216 (h1 : term102) (h2 : term62) : term52.
Proof. exact (fun h0 : term54 => @lem6901215 h1 h2 h0). Qed.
Lemma lem6901217 : term52 = term53.
Proof. exact (@lem69 term54). Qed.
Lemma lem6901218 (h1 : term102) (h2 : term62) : term53.
Proof. exact (EQ_MP (@lem6901217) (@lem6901216 h1 h2)). Qed.
Lemma lem6901219 (h1 : term62) : term57.
Proof. exact (fun h0 : term102 => @lem6901218 h0 h1). Qed.
Lemma lem6901220 : term64.
Proof. exact (fun h0 : term62 => @lem6901219 h0). Qed.
Lemma lem6901221 : term9.
Proof. exact (EQ_MP (@lem6898997) (@lem6901220)). Qed.
Lemma lem6901223 : term9.
Proof. exact (@lem6898667 (@lem6901221)). Qed.
Lemma lem6901224 (h1 : term8) : term56.
Proof. exact (@lem6901223 (@lem6898652 h1)). Qed.
Lemma lem6901225 (h1 : term8) : term52.
Proof. exact (@lem6901224 h1 (@lem85714)). Qed.
Lemma lem6901226 (h1 : term8) : False.
Proof. exact (@lem6901225 h1 (@lem81645)). Qed.
Lemma lem6901227 (h1 : term8) : term8 = False.
Proof. exact (prop_ext (fun h2 : term8 => @lem6901226 h1) (fun h2 : False => @lem6898652 h1)). Qed.
Lemma lem6901228 (h1 : term8) : False.
Proof. exact (EQ_MP (@lem6901227 h1) (@lem6898652 h1)). Qed.
Lemma lem6901229 : term7.
Proof. exact (fun h0 : term8 => @lem6901228 h0). Qed.
Lemma lem6901230 : term6.
Proof. exact (EQ_MP (@lem6898651) (@lem6901229)). Qed.
Lemma lem6901231 : term337 = term4.
Proof. exact (@lem6898647 (@lem6901230)). Qed.
