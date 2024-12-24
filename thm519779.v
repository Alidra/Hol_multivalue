Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm519779_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm516558_spec.
Require Import thm516559_spec.
Require Import thm516562_spec.
Require Import thm516563_spec.
Require Import thm516565_spec.
Require Import thm516566_spec.
Require Import thm516571_spec.
Require Import thm516572_spec.
Require Import thm516577_spec.
Require Import thm516578_spec.
Require Import thm516580_spec.
Require Import thm516614_spec.
Require Import thm516615_spec.
Require Import thm516634_spec.
Require Import thm516635_spec.
Require Import thm516639_spec.
Require Import thm516640_spec.
Require Import thm516655_spec.
Require Import thm516656_spec.
Require Import thm516716_spec.
Require Import thm516717_spec.
Require Import thm516724_spec.
Require Import thm516725_spec.
Require Import thm516727_spec.
Require Import thm516728_spec.
Require Import thm516730_spec.
Require Import thm516731_spec.
Require Import thm516733_spec.
Require Import thm516734_spec.
Require Import thm516742_spec.
Require Import thm516743_spec.
Require Import thm516748_spec.
Require Import thm516749_spec.
Require Import thm516819_spec.
Require Import thm516820_spec.
Require Import thm516836_spec.
Require Import thm516837_spec.
Require Import thm516842_spec.
Require Import thm516843_spec.
Require Import thm516851_spec.
Require Import thm516852_spec.
Require Import thm516885_spec.
Require Import thm516886_spec.
Require Import thm516892_spec.
Require Import thm516893_spec.
Require Import thm516896_spec.
Require Import thm516897_spec.
Require Import thm516912_spec.
Require Import thm516913_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem517426 (n : nat) : (Peano.le 0 n) = True.
Proof. exact (EQ_MP (@lem516913 n) (@lem516912 n)). Qed.
Lemma lem517427 : (Peano.le 0 0) = True.
Proof. exact (@lem517426 0). Qed.
Lemma lem517428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517429 : term0 = (and True).
Proof. exact (MK_COMB (@lem517428) (@lem517427)). Qed.
Lemma lem517451 (n : nat) : (Peano.le 0 n) = True.
Proof. exact (EQ_MP (@lem516913 n) (@lem516912 n)). Qed.
Lemma lem517452 (n : nat) : (term1 n) = True.
Proof. exact (@lem517451 (Nat.add n n)). Qed.
Lemma lem517453 : term2 = term3.
Proof. exact (fun_ext (fun n : nat => @lem517452 n)). Qed.
Lemma lem517454 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517455 : term4 = term5.
Proof. exact (MK_COMB (@lem517454) (@lem517453)). Qed.
Lemma lem517457 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem517458 (t : Prop) : (term7 t) = t.
Proof. exact (@lem517457 nat t). Qed.
Lemma lem517459 : term5 = True.
Proof. exact (@lem517458 True). Qed.
Lemma lem517460 : term4 = True.
Proof. exact (TRANS (@lem517455) (@lem517459)). Qed.
Lemma lem517461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517462 : term8 = (and True).
Proof. exact (MK_COMB (@lem517461) (@lem517460)). Qed.
Lemma lem517470 (n : nat) : (Peano.le 0 n) = True.
Proof. exact (EQ_MP (@lem516913 n) (@lem516912 n)). Qed.
Lemma lem517471 (n : nat) : (term9 n) = True.
Proof. exact (@lem517470 (term10 n)). Qed.
Lemma lem517472 : term11 = term3.
Proof. exact (fun_ext (fun n : nat => @lem517471 n)). Qed.
Lemma lem517473 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517474 : term12 = term5.
Proof. exact (MK_COMB (@lem517473) (@lem517472)). Qed.
Lemma lem517476 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem517477 (t : Prop) : (term7 t) = t.
Proof. exact (@lem517476 nat t). Qed.
Lemma lem517478 : term5 = True.
Proof. exact (@lem517477 True). Qed.
Lemma lem517479 : term12 = True.
Proof. exact (TRANS (@lem517474) (@lem517478)). Qed.
Lemma lem517480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517481 : term13 = (and True).
Proof. exact (MK_COMB (@lem517480) (@lem517479)). Qed.
Lemma lem517528 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem517529 : term15 = term16.
Proof. exact (MK_COMB (@lem517481) (@lem517528)). Qed.
Lemma lem517531 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem517532 : term16 = term14.
Proof. exact (@lem517531 term14). Qed.
Lemma lem517579 : term15 = term14.
Proof. exact (TRANS (@lem517529) (@lem517532)). Qed.
Lemma lem517580 : term17 = term16.
Proof. exact (MK_COMB (@lem517462) (@lem517579)). Qed.
Lemma lem517582 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem517583 : term16 = term14.
Proof. exact (@lem517582 term14). Qed.
Lemma lem517630 : term17 = term14.
Proof. exact (TRANS (@lem517580) (@lem517583)). Qed.
Lemma lem517631 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem517632 : term19 = term20.
Proof. exact (MK_COMB (@lem517631) (@lem517630)). Qed.
Lemma lem517635 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem517636 : term22 = term23.
Proof. exact (MK_COMB (@lem517635) (@lem517632)). Qed.
Lemma lem517639 : term24 = term25.
Proof. exact (MK_COMB (@lem517429) (@lem517636)). Qed.
Lemma lem517641 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem517642 : term25 = term23.
Proof. exact (@lem517641 term23). Qed.
Lemma lem517703 : term24 = term23.
Proof. exact (TRANS (@lem517639) (@lem517642)). Qed.
Lemma lem517704 : term23 = term24.
Proof. exact (SYM (@lem517703)). Qed.
Lemma lem517714 (m : nat) : (Peano.le m 0) = (m = 0).
Proof. exact (EQ_MP (@lem516897 m) (@lem516896 m)). Qed.
Lemma lem517715 (n : nat) : (term26 n) = ((Nat.add n n) = 0).
Proof. exact (@lem517714 (Nat.add n n)). Qed.
Lemma lem517719 (n : nat) : (Nat.add n n) = (term27 n).
Proof. exact (EQ_MP (@lem516886 n) (@lem516885 n)). Qed.
Lemma lem517720 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem517721 (n : nat) : (term28 n) = (term29 n).
Proof. exact (MK_COMB (@lem517720) (@lem517719 n)). Qed.
Lemma lem517722 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem517723 (n : nat) : ((Nat.add n n) = 0) = ((term27 n) = 0).
Proof. exact (MK_COMB (@lem517721 n) (@lem517722)). Qed.
Lemma lem517726 (n : nat) : (term26 n) = ((term27 n) = 0).
Proof. exact (TRANS (@lem517715 n) (@lem517723 n)). Qed.
Lemma lem517727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem517728 (n : nat) : (term30 n) = (term31 n).
Proof. exact (MK_COMB (@lem517727) (@lem517726 n)). Qed.
Lemma lem517730 (m : nat) : (Peano.le m 0) = (m = 0).
Proof. exact (EQ_MP (@lem516897 m) (@lem516896 m)). Qed.
Lemma lem517731 (n : nat) : (Peano.le n 0) = (n = 0).
Proof. exact (@lem517730 n). Qed.
Lemma lem517734 (n : nat) : ((term26 n) = (Peano.le n 0)) = (((term27 n) = 0) = (n = 0)).
Proof. exact (MK_COMB (@lem517728 n) (@lem517731 n)). Qed.
Lemma lem517737 : term32 = term33.
Proof. exact (fun_ext (fun n : nat => @lem517734 n)). Qed.
Lemma lem517738 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517739 : term34 = term35.
Proof. exact (MK_COMB (@lem517738) (@lem517737)). Qed.
Lemma lem517744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517745 : term21 = term36.
Proof. exact (MK_COMB (@lem517744) (@lem517739)). Qed.
Lemma lem517753 (m : nat) : (Peano.le m 0) = (m = 0).
Proof. exact (EQ_MP (@lem516897 m) (@lem516896 m)). Qed.
Lemma lem517754 (n : nat) : (term37 n) = ((term10 n) = 0).
Proof. exact (@lem517753 (term10 n)). Qed.
Lemma lem517758 (n : nat) : (Nat.add n n) = (term27 n).
Proof. exact (EQ_MP (@lem516886 n) (@lem516885 n)). Qed.
Lemma lem517759 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem517760 (n : nat) : (term10 n) = (term38 n).
Proof. exact (MK_COMB (@lem517759) (@lem517758 n)). Qed.
Lemma lem517761 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem517762 (n : nat) : (term39 n) = (term40 n).
Proof. exact (MK_COMB (@lem517761) (@lem517760 n)). Qed.
Lemma lem517763 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem517764 (n : nat) : ((term10 n) = 0) = ((term38 n) = 0).
Proof. exact (MK_COMB (@lem517762 n) (@lem517763)). Qed.
Lemma lem517767 (n : nat) : (term37 n) = ((term38 n) = 0).
Proof. exact (TRANS (@lem517754 n) (@lem517764 n)). Qed.
Lemma lem517768 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem517769 (n : nat) : (term41 n) = (term42 n).
Proof. exact (MK_COMB (@lem517768) (@lem517767 n)). Qed.
Lemma lem517770 : term43 = term44.
Proof. exact (fun_ext (fun n : nat => @lem517769 n)). Qed.
Lemma lem517771 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517772 : term45 = term46.
Proof. exact (MK_COMB (@lem517771) (@lem517770)). Qed.
Lemma lem517777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517778 : term18 = term47.
Proof. exact (MK_COMB (@lem517777) (@lem517772)). Qed.
Lemma lem517792 (n : nat) : (Nat.add n n) = (term27 n).
Proof. exact (EQ_MP (@lem516886 n) (@lem516885 n)). Qed.
Lemma lem517793 (m : nat) : (Nat.add m m) = (term27 m).
Proof. exact (@lem517792 m). Qed.
Lemma lem517794 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem517795 (m : nat) : (term48 m) = (term49 m).
Proof. exact (MK_COMB (@lem517794) (@lem517793 m)). Qed.
Lemma lem517797 (n : nat) : (Nat.add n n) = (term27 n).
Proof. exact (EQ_MP (@lem516886 n) (@lem516885 n)). Qed.
Lemma lem517798 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem517795 m) (@lem517797 n)). Qed.
Lemma lem517799 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem517800 (m : nat) (n : nat) : (term52 m n) = (term53 m n).
Proof. exact (MK_COMB (@lem517799) (@lem517798 m n)). Qed.
Lemma lem517801 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem517802 (m : nat) (n : nat) : ((term50 m n) = (Peano.le m n)) = ((term51 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem517800 m n) (@lem517801 m n)). Qed.
Lemma lem517805 (m : nat) : (term54 m) = (term55 m).
Proof. exact (fun_ext (fun n : nat => @lem517802 m n)). Qed.
Lemma lem517806 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517807 (m : nat) : (term56 m) = (term57 m).
Proof. exact (MK_COMB (@lem517806) (@lem517805 m)). Qed.
Lemma lem517812 : term58 = term59.
Proof. exact (fun_ext (fun m : nat => @lem517807 m)). Qed.
Lemma lem517813 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517814 : term60 = term61.
Proof. exact (MK_COMB (@lem517813) (@lem517812)). Qed.
Lemma lem517819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517820 : term62 = term63.
Proof. exact (MK_COMB (@lem517819) (@lem517814)). Qed.
Lemma lem517834 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (EQ_MP (@lem516893 m n) (@lem516892 m n)). Qed.
Lemma lem517835 (m : nat) (n : nat) : (term66 m n) = (term67 m n).
Proof. exact (@lem517834 (Nat.add m m) (Nat.add n n)). Qed.
Lemma lem517841 (n : nat) : (Nat.add n n) = (term27 n).
Proof. exact (EQ_MP (@lem516886 n) (@lem516885 n)). Qed.
Lemma lem517842 (m : nat) : (Nat.add m m) = (term27 m).
Proof. exact (@lem517841 m). Qed.
Lemma lem517843 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem517844 (m : nat) : (term28 m) = (term29 m).
Proof. exact (MK_COMB (@lem517843) (@lem517842 m)). Qed.
Lemma lem517846 (n : nat) : (Nat.add n n) = (term27 n).
Proof. exact (EQ_MP (@lem516886 n) (@lem516885 n)). Qed.
Lemma lem517847 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem517848 (n : nat) : (term10 n) = (term38 n).
Proof. exact (MK_COMB (@lem517847) (@lem517846 n)). Qed.
Lemma lem517849 (m : nat) (n : nat) : ((Nat.add m m) = (term10 n)) = ((term27 m) = (term38 n)).
Proof. exact (MK_COMB (@lem517844 m) (@lem517848 n)). Qed.
Lemma lem517852 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem517853 (m : nat) (n : nat) : (term68 m n) = (term69 m n).
Proof. exact (MK_COMB (@lem517852) (@lem517849 m n)). Qed.
Lemma lem517855 (n : nat) : (Nat.add n n) = (term27 n).
Proof. exact (EQ_MP (@lem516886 n) (@lem516885 n)). Qed.
Lemma lem517856 (m : nat) : (Nat.add m m) = (term27 m).
Proof. exact (@lem517855 m). Qed.
Lemma lem517857 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem517858 (m : nat) : (term48 m) = (term49 m).
Proof. exact (MK_COMB (@lem517857) (@lem517856 m)). Qed.
Lemma lem517860 (n : nat) : (Nat.add n n) = (term27 n).
Proof. exact (EQ_MP (@lem516886 n) (@lem516885 n)). Qed.
Lemma lem517861 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem517858 m) (@lem517860 n)). Qed.
Lemma lem517862 (m : nat) (n : nat) : (term67 m n) = (term70 m n).
Proof. exact (MK_COMB (@lem517853 m n) (@lem517861 m n)). Qed.
Lemma lem517865 (m : nat) (n : nat) : (term66 m n) = (term70 m n).
Proof. exact (TRANS (@lem517835 m n) (@lem517862 m n)). Qed.
Lemma lem517866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem517867 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (MK_COMB (@lem517866) (@lem517865 m n)). Qed.
Lemma lem517868 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem517869 (m : nat) (n : nat) : ((term66 m n) = (Peano.le m n)) = ((term70 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem517867 m n) (@lem517868 m n)). Qed.
Lemma lem517872 (m : nat) : (term73 m) = (term74 m).
Proof. exact (fun_ext (fun n : nat => @lem517869 m n)). Qed.
Lemma lem517873 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517874 (m : nat) : (term75 m) = (term76 m).
Proof. exact (MK_COMB (@lem517873) (@lem517872 m)). Qed.
Lemma lem517879 : term77 = term78.
Proof. exact (fun_ext (fun m : nat => @lem517874 m)). Qed.
Lemma lem517880 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517881 : term79 = term80.
Proof. exact (MK_COMB (@lem517880) (@lem517879)). Qed.
Lemma lem517886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517887 : term81 = term82.
Proof. exact (MK_COMB (@lem517886) (@lem517881)). Qed.
Lemma lem517901 (n : nat) : (Nat.add n n) = (term27 n).
Proof. exact (EQ_MP (@lem516886 n) (@lem516885 n)). Qed.
Lemma lem517902 (m : nat) : (Nat.add m m) = (term27 m).
Proof. exact (@lem517901 m). Qed.
Lemma lem517903 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem517904 (m : nat) : (term10 m) = (term38 m).
Proof. exact (MK_COMB (@lem517903) (@lem517902 m)). Qed.
Lemma lem517905 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem517906 (m : nat) : (term83 m) = (term84 m).
Proof. exact (MK_COMB (@lem517905) (@lem517904 m)). Qed.
Lemma lem517908 (n : nat) : (Nat.add n n) = (term27 n).
Proof. exact (EQ_MP (@lem516886 n) (@lem516885 n)). Qed.
Lemma lem517909 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (MK_COMB (@lem517906 m) (@lem517908 n)). Qed.
Lemma lem517910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem517911 (m : nat) (n : nat) : (term87 m n) = (term88 m n).
Proof. exact (MK_COMB (@lem517910) (@lem517909 m n)). Qed.
Lemma lem517912 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem517913 (m : nat) (n : nat) : ((term85 m n) = (Peano.lt m n)) = ((term86 m n) = (Peano.lt m n)).
Proof. exact (MK_COMB (@lem517911 m n) (@lem517912 m n)). Qed.
Lemma lem517916 (m : nat) : (term89 m) = (term90 m).
Proof. exact (fun_ext (fun n : nat => @lem517913 m n)). Qed.
Lemma lem517917 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517918 (m : nat) : (term91 m) = (term92 m).
Proof. exact (MK_COMB (@lem517917) (@lem517916 m)). Qed.
Lemma lem517923 : term93 = term94.
Proof. exact (fun_ext (fun m : nat => @lem517918 m)). Qed.
Lemma lem517924 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517925 : term95 = term96.
Proof. exact (MK_COMB (@lem517924) (@lem517923)). Qed.
Lemma lem517930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517931 : term97 = term98.
Proof. exact (MK_COMB (@lem517930) (@lem517925)). Qed.
Lemma lem517943 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (EQ_MP (@lem516893 m n) (@lem516892 m n)). Qed.
Lemma lem517944 (m : nat) (n : nat) : (term99 m n) = (term100 m n).
Proof. exact (@lem517943 (term10 m) (Nat.add n n)). Qed.
Lemma lem517950 (n : nat) : (Nat.add n n) = (term27 n).
Proof. exact (EQ_MP (@lem516886 n) (@lem516885 n)). Qed.
Lemma lem517951 (m : nat) : (Nat.add m m) = (term27 m).
Proof. exact (@lem517950 m). Qed.
Lemma lem517952 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem517953 (m : nat) : (term10 m) = (term38 m).
Proof. exact (MK_COMB (@lem517952) (@lem517951 m)). Qed.
Lemma lem517954 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem517955 (m : nat) : (term39 m) = (term40 m).
Proof. exact (MK_COMB (@lem517954) (@lem517953 m)). Qed.
Lemma lem517957 (n : nat) : (Nat.add n n) = (term27 n).
Proof. exact (EQ_MP (@lem516886 n) (@lem516885 n)). Qed.
Lemma lem517958 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem517959 (n : nat) : (term10 n) = (term38 n).
Proof. exact (MK_COMB (@lem517958) (@lem517957 n)). Qed.
Lemma lem517960 (m : nat) (n : nat) : ((term10 m) = (term10 n)) = ((term38 m) = (term38 n)).
Proof. exact (MK_COMB (@lem517955 m) (@lem517959 n)). Qed.
Lemma lem517963 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem517964 (m : nat) (n : nat) : (term101 m n) = (term102 m n).
Proof. exact (MK_COMB (@lem517963) (@lem517960 m n)). Qed.
Lemma lem517966 (n : nat) : (Nat.add n n) = (term27 n).
Proof. exact (EQ_MP (@lem516886 n) (@lem516885 n)). Qed.
Lemma lem517967 (m : nat) : (Nat.add m m) = (term27 m).
Proof. exact (@lem517966 m). Qed.
Lemma lem517968 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem517969 (m : nat) : (term10 m) = (term38 m).
Proof. exact (MK_COMB (@lem517968) (@lem517967 m)). Qed.
Lemma lem517970 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem517971 (m : nat) : (term83 m) = (term84 m).
Proof. exact (MK_COMB (@lem517970) (@lem517969 m)). Qed.
Lemma lem517973 (n : nat) : (Nat.add n n) = (term27 n).
Proof. exact (EQ_MP (@lem516886 n) (@lem516885 n)). Qed.
Lemma lem517974 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (MK_COMB (@lem517971 m) (@lem517973 n)). Qed.
Lemma lem517975 (m : nat) (n : nat) : (term100 m n) = (term103 m n).
Proof. exact (MK_COMB (@lem517964 m n) (@lem517974 m n)). Qed.
Lemma lem517978 (m : nat) (n : nat) : (term99 m n) = (term103 m n).
Proof. exact (TRANS (@lem517944 m n) (@lem517975 m n)). Qed.
Lemma lem517979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem517980 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (MK_COMB (@lem517979) (@lem517978 m n)). Qed.
Lemma lem517981 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem517982 (m : nat) (n : nat) : ((term99 m n) = (Peano.le m n)) = ((term103 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem517980 m n) (@lem517981 m n)). Qed.
Lemma lem517985 (m : nat) : (term106 m) = (term107 m).
Proof. exact (fun_ext (fun n : nat => @lem517982 m n)). Qed.
Lemma lem517986 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517987 (m : nat) : (term108 m) = (term109 m).
Proof. exact (MK_COMB (@lem517986) (@lem517985 m)). Qed.
Lemma lem517992 : term110 = term111.
Proof. exact (fun_ext (fun m : nat => @lem517987 m)). Qed.
Lemma lem517993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517994 : term112 = term113.
Proof. exact (MK_COMB (@lem517993) (@lem517992)). Qed.
Lemma lem517999 : term114 = term115.
Proof. exact (MK_COMB (@lem517931) (@lem517994)). Qed.
Lemma lem518002 : term116 = term117.
Proof. exact (MK_COMB (@lem517887) (@lem517999)). Qed.
Lemma lem518005 : term14 = term118.
Proof. exact (MK_COMB (@lem517820) (@lem518002)). Qed.
Lemma lem518008 : term20 = term119.
Proof. exact (MK_COMB (@lem517778) (@lem518005)). Qed.
Lemma lem518011 : term23 = term120.
Proof. exact (MK_COMB (@lem517745) (@lem518008)). Qed.
Lemma lem518014 : term120 = term23.
Proof. exact (SYM (@lem518011)). Qed.
Lemma lem518024 (m : nat) (n : nat) : ((Nat.mul m n) = 0) = (term121 m n).
Proof. exact (EQ_MP (@lem516837 m n) (@lem516836 m n)). Qed.
Lemma lem518025 (n : nat) : ((term27 n) = 0) = (term122 n).
Proof. exact (@lem518024 term123 n). Qed.
Lemma lem518032 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem518033 (n : nat) : (term31 n) = (term124 n).
Proof. exact (MK_COMB (@lem518032) (@lem518025 n)). Qed.
Lemma lem518036 (n : nat) : (n = 0) = (n = 0).
Proof. exact (eq_refl (n = 0)). Qed.
Lemma lem518037 (n : nat) : (((term27 n) = 0) = (n = 0)) = ((term122 n) = (n = 0)).
Proof. exact (MK_COMB (@lem518033 n) (@lem518036 n)). Qed.
Lemma lem518040 : term33 = term125.
Proof. exact (fun_ext (fun n : nat => @lem518037 n)). Qed.
Lemma lem518041 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518042 : term35 = term126.
Proof. exact (MK_COMB (@lem518041) (@lem518040)). Qed.
Lemma lem518047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem518048 : term36 = term127.
Proof. exact (MK_COMB (@lem518047) (@lem518042)). Qed.
Lemma lem518056 (n : nat) : ((S n) = 0) = False.
Proof. exact (@lem516820 n (@lem516819 n)). Qed.
Lemma lem518057 (n : nat) : ((term38 n) = 0) = False.
Proof. exact (@lem518056 (term27 n)). Qed.
Lemma lem518058 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem518059 (n : nat) : (term42 n) = (~ False).
Proof. exact (MK_COMB (@lem518058) (@lem518057 n)). Qed.
Lemma lem518061 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem518062 (n : nat) : (term42 n) = True.
Proof. exact (TRANS (@lem518059 n) (@lem518061)). Qed.
Lemma lem518063 : term44 = term3.
Proof. exact (fun_ext (fun n : nat => @lem518062 n)). Qed.
Lemma lem518064 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518065 : term46 = term5.
Proof. exact (MK_COMB (@lem518064) (@lem518063)). Qed.
Lemma lem518067 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem518068 (t : Prop) : (term7 t) = t.
Proof. exact (@lem518067 nat t). Qed.
Lemma lem518069 : term5 = True.
Proof. exact (@lem518068 True). Qed.
Lemma lem518070 : term46 = True.
Proof. exact (TRANS (@lem518065) (@lem518069)). Qed.
Lemma lem518071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem518072 : term47 = (and True).
Proof. exact (MK_COMB (@lem518071) (@lem518070)). Qed.
Lemma lem518086 (m : nat) (n : nat) (p : nat) : (term128 n m p) = (term129 m n p).
Proof. exact (EQ_MP (@lem516852 m n p) (@lem516851 m n p)). Qed.
Lemma lem518087 (m : nat) (n : nat) : (term51 m n) = (term130 m n).
Proof. exact (@lem518086 term123 m n). Qed.
Lemma lem518092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem518093 (m : nat) (n : nat) : (term53 m n) = (term131 m n).
Proof. exact (MK_COMB (@lem518092) (@lem518087 m n)). Qed.
Lemma lem518094 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem518095 (m : nat) (n : nat) : ((term51 m n) = (Peano.le m n)) = ((term130 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem518093 m n) (@lem518094 m n)). Qed.
Lemma lem518098 (m : nat) : (term55 m) = (term132 m).
Proof. exact (fun_ext (fun n : nat => @lem518095 m n)). Qed.
Lemma lem518099 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518100 (m : nat) : (term57 m) = (term133 m).
Proof. exact (MK_COMB (@lem518099) (@lem518098 m)). Qed.
Lemma lem518105 : term59 = term134.
Proof. exact (fun_ext (fun m : nat => @lem518100 m)). Qed.
Lemma lem518106 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518107 : term61 = term135.
Proof. exact (MK_COMB (@lem518106) (@lem518105)). Qed.
Lemma lem518112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem518113 : term63 = term136.
Proof. exact (MK_COMB (@lem518112) (@lem518107)). Qed.
Lemma lem518131 (m : nat) (n : nat) (p : nat) : (term128 n m p) = (term129 m n p).
Proof. exact (EQ_MP (@lem516852 m n p) (@lem516851 m n p)). Qed.
Lemma lem518132 (m : nat) (n : nat) : (term51 m n) = (term130 m n).
Proof. exact (@lem518131 term123 m n). Qed.
Lemma lem518137 (m : nat) (n : nat) : (term69 m n) = (term69 m n).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem518138 (m : nat) (n : nat) : (term70 m n) = (term137 m n).
Proof. exact (MK_COMB (@lem518137 m n) (@lem518132 m n)). Qed.
Lemma lem518141 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem518142 (m : nat) (n : nat) : (term72 m n) = (term138 m n).
Proof. exact (MK_COMB (@lem518141) (@lem518138 m n)). Qed.
Lemma lem518143 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem518144 (m : nat) (n : nat) : ((term70 m n) = (Peano.le m n)) = ((term137 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem518142 m n) (@lem518143 m n)). Qed.
Lemma lem518147 (m : nat) : (term74 m) = (term139 m).
Proof. exact (fun_ext (fun n : nat => @lem518144 m n)). Qed.
Lemma lem518148 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518149 (m : nat) : (term76 m) = (term140 m).
Proof. exact (MK_COMB (@lem518148) (@lem518147 m)). Qed.
Lemma lem518154 : term78 = term141.
Proof. exact (fun_ext (fun m : nat => @lem518149 m)). Qed.
Lemma lem518155 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518156 : term80 = term142.
Proof. exact (MK_COMB (@lem518155) (@lem518154)). Qed.
Lemma lem518161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem518162 : term82 = term143.
Proof. exact (MK_COMB (@lem518161) (@lem518156)). Qed.
Lemma lem518188 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem516843 m n) (@lem516842 m n)). Qed.
Lemma lem518189 (m : nat) (n : nat) : ((term38 m) = (term38 n)) = ((term27 m) = (term27 n)).
Proof. exact (@lem518188 (term27 m) (term27 n)). Qed.
Lemma lem518192 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem518193 (m : nat) (n : nat) : (term102 m n) = (term144 m n).
Proof. exact (MK_COMB (@lem518192) (@lem518189 m n)). Qed.
Lemma lem518194 (m : nat) (n : nat) : (term86 m n) = (term86 m n).
Proof. exact (eq_refl (term86 m n)). Qed.
Lemma lem518195 (m : nat) (n : nat) : (term103 m n) = (term145 m n).
Proof. exact (MK_COMB (@lem518193 m n) (@lem518194 m n)). Qed.
Lemma lem518198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem518199 (m : nat) (n : nat) : (term105 m n) = (term146 m n).
Proof. exact (MK_COMB (@lem518198) (@lem518195 m n)). Qed.
Lemma lem518200 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem518201 (m : nat) (n : nat) : ((term103 m n) = (Peano.le m n)) = ((term145 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem518199 m n) (@lem518200 m n)). Qed.
Lemma lem518204 (m : nat) : (term107 m) = (term147 m).
Proof. exact (fun_ext (fun n : nat => @lem518201 m n)). Qed.
Lemma lem518205 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518206 (m : nat) : (term109 m) = (term148 m).
Proof. exact (MK_COMB (@lem518205) (@lem518204 m)). Qed.
Lemma lem518211 : term111 = term149.
Proof. exact (fun_ext (fun m : nat => @lem518206 m)). Qed.
Lemma lem518212 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518213 : term113 = term150.
Proof. exact (MK_COMB (@lem518212) (@lem518211)). Qed.
Lemma lem518218 : term98 = term98.
Proof. exact (eq_refl term98). Qed.
Lemma lem518219 : term115 = term151.
Proof. exact (MK_COMB (@lem518218) (@lem518213)). Qed.
Lemma lem518222 : term117 = term152.
Proof. exact (MK_COMB (@lem518162) (@lem518219)). Qed.
Lemma lem518225 : term118 = term153.
Proof. exact (MK_COMB (@lem518113) (@lem518222)). Qed.
Lemma lem518228 : term119 = term154.
Proof. exact (MK_COMB (@lem518072) (@lem518225)). Qed.
Lemma lem518230 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem518231 : term154 = term153.
Proof. exact (@lem518230 term153). Qed.
Lemma lem518294 : term119 = term153.
Proof. exact (TRANS (@lem518228) (@lem518231)). Qed.
Lemma lem518295 : term120 = term155.
Proof. exact (MK_COMB (@lem518048) (@lem518294)). Qed.
Lemma lem518298 : term155 = term120.
Proof. exact (SYM (@lem518295)). Qed.
Lemma lem518444 (m : nat) (n : nat) : (term156 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem516749 m n) (@lem516748 m n)). Qed.
Lemma lem518445 (m : nat) (n : nat) : (term86 m n) = (term157 m n).
Proof. exact (@lem518444 (term27 m) (term27 n)). Qed.
Lemma lem518446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem518447 (m : nat) (n : nat) : (term88 m n) = (term158 m n).
Proof. exact (MK_COMB (@lem518446) (@lem518445 m n)). Qed.
Lemma lem518448 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem518449 (m : nat) (n : nat) : ((term86 m n) = (Peano.lt m n)) = ((term157 m n) = (Peano.lt m n)).
Proof. exact (MK_COMB (@lem518447 m n) (@lem518448 m n)). Qed.
Lemma lem518452 (m : nat) : (term90 m) = (term159 m).
Proof. exact (fun_ext (fun n : nat => @lem518449 m n)). Qed.
Lemma lem518453 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518454 (m : nat) : (term92 m) = (term160 m).
Proof. exact (MK_COMB (@lem518453) (@lem518452 m)). Qed.
Lemma lem518459 : term94 = term161.
Proof. exact (fun_ext (fun m : nat => @lem518454 m)). Qed.
Lemma lem518460 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518461 : term96 = term162.
Proof. exact (MK_COMB (@lem518460) (@lem518459)). Qed.
Lemma lem518466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem518467 : term98 = term163.
Proof. exact (MK_COMB (@lem518466) (@lem518461)). Qed.
Lemma lem518483 (m : nat) (n : nat) : (term156 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem516749 m n) (@lem516748 m n)). Qed.
Lemma lem518484 (m : nat) (n : nat) : (term86 m n) = (term157 m n).
Proof. exact (@lem518483 (term27 m) (term27 n)). Qed.
Lemma lem518485 (m : nat) (n : nat) : (term144 m n) = (term144 m n).
Proof. exact (eq_refl (term144 m n)). Qed.
Lemma lem518486 (m : nat) (n : nat) : (term145 m n) = (term164 m n).
Proof. exact (MK_COMB (@lem518485 m n) (@lem518484 m n)). Qed.
Lemma lem518489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem518490 (m : nat) (n : nat) : (term146 m n) = (term165 m n).
Proof. exact (MK_COMB (@lem518489) (@lem518486 m n)). Qed.
Lemma lem518491 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem518492 (m : nat) (n : nat) : ((term145 m n) = (Peano.le m n)) = ((term164 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem518490 m n) (@lem518491 m n)). Qed.
Lemma lem518495 (m : nat) : (term147 m) = (term166 m).
Proof. exact (fun_ext (fun n : nat => @lem518492 m n)). Qed.
Lemma lem518496 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518497 (m : nat) : (term148 m) = (term167 m).
Proof. exact (MK_COMB (@lem518496) (@lem518495 m)). Qed.
Lemma lem518502 : term149 = term168.
Proof. exact (fun_ext (fun m : nat => @lem518497 m)). Qed.
Lemma lem518503 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518504 : term150 = term169.
Proof. exact (MK_COMB (@lem518503) (@lem518502)). Qed.
Lemma lem518509 : term151 = term170.
Proof. exact (MK_COMB (@lem518467) (@lem518504)). Qed.
Lemma lem518512 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem518513 : term152 = term171.
Proof. exact (MK_COMB (@lem518512) (@lem518509)). Qed.
Lemma lem518516 : term136 = term136.
Proof. exact (eq_refl term136). Qed.
Lemma lem518517 : term153 = term172.
Proof. exact (MK_COMB (@lem518516) (@lem518513)). Qed.
Lemma lem518520 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem518521 : term155 = term173.
Proof. exact (MK_COMB (@lem518520) (@lem518517)). Qed.
Lemma lem518524 : term173 = term155.
Proof. exact (SYM (@lem518521)). Qed.
Lemma lem518590 (m : nat) (n : nat) (p : nat) : (term174 n m p) = (term175 m n p).
Proof. exact (EQ_MP (@lem516743 m n p) (@lem516742 m n p)). Qed.
Lemma lem518591 (m : nat) (n : nat) : (term157 m n) = (term176 m n).
Proof. exact (@lem518590 term123 m n). Qed.
Lemma lem518596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem518597 (m : nat) (n : nat) : (term158 m n) = (term177 m n).
Proof. exact (MK_COMB (@lem518596) (@lem518591 m n)). Qed.
Lemma lem518598 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem518599 (m : nat) (n : nat) : ((term157 m n) = (Peano.lt m n)) = ((term176 m n) = (Peano.lt m n)).
Proof. exact (MK_COMB (@lem518597 m n) (@lem518598 m n)). Qed.
Lemma lem518602 (m : nat) : (term159 m) = (term178 m).
Proof. exact (fun_ext (fun n : nat => @lem518599 m n)). Qed.
Lemma lem518603 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518604 (m : nat) : (term160 m) = (term179 m).
Proof. exact (MK_COMB (@lem518603) (@lem518602 m)). Qed.
Lemma lem518609 : term161 = term180.
Proof. exact (fun_ext (fun m : nat => @lem518604 m)). Qed.
Lemma lem518610 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518611 : term162 = term181.
Proof. exact (MK_COMB (@lem518610) (@lem518609)). Qed.
Lemma lem518616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem518617 : term163 = term182.
Proof. exact (MK_COMB (@lem518616) (@lem518611)). Qed.
Lemma lem518633 (m : nat) (n : nat) (p : nat) : (term174 n m p) = (term175 m n p).
Proof. exact (EQ_MP (@lem516743 m n p) (@lem516742 m n p)). Qed.
Lemma lem518634 (m : nat) (n : nat) : (term157 m n) = (term176 m n).
Proof. exact (@lem518633 term123 m n). Qed.
Lemma lem518639 (m : nat) (n : nat) : (term144 m n) = (term144 m n).
Proof. exact (eq_refl (term144 m n)). Qed.
Lemma lem518640 (m : nat) (n : nat) : (term164 m n) = (term183 m n).
Proof. exact (MK_COMB (@lem518639 m n) (@lem518634 m n)). Qed.
Lemma lem518643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem518644 (m : nat) (n : nat) : (term165 m n) = (term184 m n).
Proof. exact (MK_COMB (@lem518643) (@lem518640 m n)). Qed.
Lemma lem518645 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem518646 (m : nat) (n : nat) : ((term164 m n) = (Peano.le m n)) = ((term183 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem518644 m n) (@lem518645 m n)). Qed.
Lemma lem518649 (m : nat) : (term166 m) = (term185 m).
Proof. exact (fun_ext (fun n : nat => @lem518646 m n)). Qed.
Lemma lem518650 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518651 (m : nat) : (term167 m) = (term186 m).
Proof. exact (MK_COMB (@lem518650) (@lem518649 m)). Qed.
Lemma lem518656 : term168 = term187.
Proof. exact (fun_ext (fun m : nat => @lem518651 m)). Qed.
Lemma lem518657 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518658 : term169 = term188.
Proof. exact (MK_COMB (@lem518657) (@lem518656)). Qed.
Lemma lem518663 : term170 = term189.
Proof. exact (MK_COMB (@lem518617) (@lem518658)). Qed.
Lemma lem518666 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem518667 : term171 = term190.
Proof. exact (MK_COMB (@lem518666) (@lem518663)). Qed.
Lemma lem518670 : term136 = term136.
Proof. exact (eq_refl term136). Qed.
Lemma lem518671 : term172 = term191.
Proof. exact (MK_COMB (@lem518670) (@lem518667)). Qed.
Lemma lem518674 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem518675 : term173 = term192.
Proof. exact (MK_COMB (@lem518674) (@lem518671)). Qed.
Lemma lem518678 : term192 = term173.
Proof. exact (SYM (@lem518675)). Qed.
Lemma lem518693 (h1 : term123 = term193) : term123 = term193.
Proof. exact (h1). Qed.
Lemma lem518694 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem518695 (h1 : term123 = term193) : term194 = term195.
Proof. exact (MK_COMB (@lem518694) (@lem518693 h1)). Qed.
Lemma lem518696 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem518697 (h1 : term123 = term193) : (term123 = 0) = (term193 = 0).
Proof. exact (MK_COMB (@lem518695 h1) (@lem518696)). Qed.
Lemma lem518700 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem518701 (h1 : term123 = term193) : term196 = term197.
Proof. exact (MK_COMB (@lem518700) (@lem518697 h1)). Qed.
Lemma lem518704 (n : nat) : (n = 0) = (n = 0).
Proof. exact (eq_refl (n = 0)). Qed.
Lemma lem518705 (n : nat) (h1 : term123 = term193) : (term122 n) = (term198 n).
Proof. exact (MK_COMB (@lem518701 h1) (@lem518704 n)). Qed.
Lemma lem518708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem518709 (n : nat) (h1 : term123 = term193) : (term124 n) = (term199 n).
Proof. exact (MK_COMB (@lem518708) (@lem518705 n h1)). Qed.
Lemma lem518712 (n : nat) : (n = 0) = (n = 0).
Proof. exact (eq_refl (n = 0)). Qed.
Lemma lem518713 (n : nat) (h1 : term123 = term193) : ((term122 n) = (n = 0)) = ((term198 n) = (n = 0)).
Proof. exact (MK_COMB (@lem518709 n h1) (@lem518712 n)). Qed.
Lemma lem518716 (h1 : term123 = term193) : term125 = term200.
Proof. exact (fun_ext (fun n : nat => @lem518713 n h1)). Qed.
Lemma lem518717 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518718 (h1 : term123 = term193) : term126 = term201.
Proof. exact (MK_COMB (@lem518717) (@lem518716 h1)). Qed.
Lemma lem518723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem518724 (h1 : term123 = term193) : term127 = term202.
Proof. exact (MK_COMB (@lem518723) (@lem518718 h1)). Qed.
Lemma lem518742 (h1 : term123 = term193) : term123 = term193.
Proof. exact (h1). Qed.
Lemma lem518743 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem518744 (h1 : term123 = term193) : term194 = term195.
Proof. exact (MK_COMB (@lem518743) (@lem518742 h1)). Qed.
Lemma lem518745 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem518746 (h1 : term123 = term193) : (term123 = (NUMERAL 0)) = (term193 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem518744 h1) (@lem518745)). Qed.
Lemma lem518749 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem518750 (h1 : term123 = term193) : term203 = term204.
Proof. exact (MK_COMB (@lem518749) (@lem518746 h1)). Qed.
Lemma lem518751 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem518752 (m : nat) (n : nat) (h1 : term123 = term193) : (term130 m n) = (term205 m n).
Proof. exact (MK_COMB (@lem518750 h1) (@lem518751 m n)). Qed.
Lemma lem518755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem518756 (m : nat) (n : nat) (h1 : term123 = term193) : (term131 m n) = (term206 m n).
Proof. exact (MK_COMB (@lem518755) (@lem518752 m n h1)). Qed.
Lemma lem518757 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem518758 (m : nat) (n : nat) (h1 : term123 = term193) : ((term130 m n) = (Peano.le m n)) = ((term205 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem518756 m n h1) (@lem518757 m n)). Qed.
Lemma lem518761 (m : nat) (h1 : term123 = term193) : (term132 m) = (term207 m).
Proof. exact (fun_ext (fun n : nat => @lem518758 m n h1)). Qed.
Lemma lem518762 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518763 (m : nat) (h1 : term123 = term193) : (term133 m) = (term208 m).
Proof. exact (MK_COMB (@lem518762) (@lem518761 m h1)). Qed.
Lemma lem518768 (h1 : term123 = term193) : term134 = term209.
Proof. exact (fun_ext (fun m : nat => @lem518763 m h1)). Qed.
Lemma lem518769 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518770 (h1 : term123 = term193) : term135 = term210.
Proof. exact (MK_COMB (@lem518769) (@lem518768 h1)). Qed.
Lemma lem518775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem518776 (h1 : term123 = term193) : term136 = term211.
Proof. exact (MK_COMB (@lem518775) (@lem518770 h1)). Qed.
Lemma lem518794 (h1 : term123 = term193) : term123 = term193.
Proof. exact (h1). Qed.
Lemma lem518795 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem518796 (h1 : term123 = term193) : term212 = term213.
Proof. exact (MK_COMB (@lem518795) (@lem518794 h1)). Qed.
Lemma lem518797 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem518798 (m : nat) (h1 : term123 = term193) : (term27 m) = (term214 m).
Proof. exact (MK_COMB (@lem518796 h1) (@lem518797 m)). Qed.
Lemma lem518799 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem518800 (m : nat) (h1 : term123 = term193) : (term29 m) = (term215 m).
Proof. exact (MK_COMB (@lem518799) (@lem518798 m h1)). Qed.
Lemma lem518802 (h1 : term123 = term193) : term123 = term193.
Proof. exact (h1). Qed.
Lemma lem518803 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem518804 (h1 : term123 = term193) : term212 = term213.
Proof. exact (MK_COMB (@lem518803) (@lem518802 h1)). Qed.
Lemma lem518805 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem518806 (n : nat) (h1 : term123 = term193) : (term27 n) = (term214 n).
Proof. exact (MK_COMB (@lem518804 h1) (@lem518805 n)). Qed.
Lemma lem518807 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem518808 (n : nat) (h1 : term123 = term193) : (term38 n) = (term216 n).
Proof. exact (MK_COMB (@lem518807) (@lem518806 n h1)). Qed.
Lemma lem518809 (m : nat) (n : nat) (h1 : term123 = term193) : ((term27 m) = (term38 n)) = ((term214 m) = (term216 n)).
Proof. exact (MK_COMB (@lem518800 m h1) (@lem518808 n h1)). Qed.
Lemma lem518812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem518813 (m : nat) (n : nat) (h1 : term123 = term193) : (term69 m n) = (term217 m n).
Proof. exact (MK_COMB (@lem518812) (@lem518809 m n h1)). Qed.
Lemma lem518819 (h1 : term123 = term193) : term123 = term193.
Proof. exact (h1). Qed.
Lemma lem518820 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem518821 (h1 : term123 = term193) : term194 = term195.
Proof. exact (MK_COMB (@lem518820) (@lem518819 h1)). Qed.
Lemma lem518822 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem518823 (h1 : term123 = term193) : (term123 = (NUMERAL 0)) = (term193 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem518821 h1) (@lem518822)). Qed.
Lemma lem518826 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem518827 (h1 : term123 = term193) : term203 = term204.
Proof. exact (MK_COMB (@lem518826) (@lem518823 h1)). Qed.
Lemma lem518828 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem518829 (m : nat) (n : nat) (h1 : term123 = term193) : (term130 m n) = (term205 m n).
Proof. exact (MK_COMB (@lem518827 h1) (@lem518828 m n)). Qed.
Lemma lem518832 (m : nat) (n : nat) (h1 : term123 = term193) : (term137 m n) = (term218 m n).
Proof. exact (MK_COMB (@lem518813 m n h1) (@lem518829 m n h1)). Qed.
Lemma lem518835 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem518836 (m : nat) (n : nat) (h1 : term123 = term193) : (term138 m n) = (term219 m n).
Proof. exact (MK_COMB (@lem518835) (@lem518832 m n h1)). Qed.
Lemma lem518837 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem518838 (m : nat) (n : nat) (h1 : term123 = term193) : ((term137 m n) = (Peano.le m n)) = ((term218 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem518836 m n h1) (@lem518837 m n)). Qed.
Lemma lem518841 (m : nat) (h1 : term123 = term193) : (term139 m) = (term220 m).
Proof. exact (fun_ext (fun n : nat => @lem518838 m n h1)). Qed.
Lemma lem518842 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518843 (m : nat) (h1 : term123 = term193) : (term140 m) = (term221 m).
Proof. exact (MK_COMB (@lem518842) (@lem518841 m h1)). Qed.
Lemma lem518848 (h1 : term123 = term193) : term141 = term222.
Proof. exact (fun_ext (fun m : nat => @lem518843 m h1)). Qed.
Lemma lem518849 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518850 (h1 : term123 = term193) : term142 = term223.
Proof. exact (MK_COMB (@lem518849) (@lem518848 h1)). Qed.
Lemma lem518855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem518856 (h1 : term123 = term193) : term143 = term224.
Proof. exact (MK_COMB (@lem518855) (@lem518850 h1)). Qed.
Lemma lem518874 (h1 : term123 = term193) : term123 = term193.
Proof. exact (h1). Qed.
Lemma lem518875 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem518876 (h1 : term123 = term193) : term194 = term195.
Proof. exact (MK_COMB (@lem518875) (@lem518874 h1)). Qed.
Lemma lem518877 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem518878 (h1 : term123 = term193) : (term123 = (NUMERAL 0)) = (term193 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem518876 h1) (@lem518877)). Qed.
Lemma lem518881 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem518882 (h1 : term123 = term193) : term225 = term226.
Proof. exact (MK_COMB (@lem518881) (@lem518878 h1)). Qed.
Lemma lem518883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem518884 (h1 : term123 = term193) : term227 = term228.
Proof. exact (MK_COMB (@lem518883) (@lem518882 h1)). Qed.
Lemma lem518885 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem518886 (m : nat) (n : nat) (h1 : term123 = term193) : (term176 m n) = (term229 m n).
Proof. exact (MK_COMB (@lem518884 h1) (@lem518885 m n)). Qed.
Lemma lem518889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem518890 (m : nat) (n : nat) (h1 : term123 = term193) : (term177 m n) = (term230 m n).
Proof. exact (MK_COMB (@lem518889) (@lem518886 m n h1)). Qed.
Lemma lem518891 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem518892 (m : nat) (n : nat) (h1 : term123 = term193) : ((term176 m n) = (Peano.lt m n)) = ((term229 m n) = (Peano.lt m n)).
Proof. exact (MK_COMB (@lem518890 m n h1) (@lem518891 m n)). Qed.
Lemma lem518895 (m : nat) (h1 : term123 = term193) : (term178 m) = (term231 m).
Proof. exact (fun_ext (fun n : nat => @lem518892 m n h1)). Qed.
Lemma lem518896 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518897 (m : nat) (h1 : term123 = term193) : (term179 m) = (term232 m).
Proof. exact (MK_COMB (@lem518896) (@lem518895 m h1)). Qed.
Lemma lem518902 (h1 : term123 = term193) : term180 = term233.
Proof. exact (fun_ext (fun m : nat => @lem518897 m h1)). Qed.
Lemma lem518903 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518904 (h1 : term123 = term193) : term181 = term234.
Proof. exact (MK_COMB (@lem518903) (@lem518902 h1)). Qed.
Lemma lem518909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem518910 (h1 : term123 = term193) : term182 = term235.
Proof. exact (MK_COMB (@lem518909) (@lem518904 h1)). Qed.
Lemma lem518926 (h1 : term123 = term193) : term123 = term193.
Proof. exact (h1). Qed.
Lemma lem518927 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem518928 (h1 : term123 = term193) : term212 = term213.
Proof. exact (MK_COMB (@lem518927) (@lem518926 h1)). Qed.
Lemma lem518929 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem518930 (m : nat) (h1 : term123 = term193) : (term27 m) = (term214 m).
Proof. exact (MK_COMB (@lem518928 h1) (@lem518929 m)). Qed.
Lemma lem518931 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem518932 (m : nat) (h1 : term123 = term193) : (term29 m) = (term215 m).
Proof. exact (MK_COMB (@lem518931) (@lem518930 m h1)). Qed.
Lemma lem518934 (h1 : term123 = term193) : term123 = term193.
Proof. exact (h1). Qed.
Lemma lem518935 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem518936 (h1 : term123 = term193) : term212 = term213.
Proof. exact (MK_COMB (@lem518935) (@lem518934 h1)). Qed.
Lemma lem518937 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem518938 (n : nat) (h1 : term123 = term193) : (term27 n) = (term214 n).
Proof. exact (MK_COMB (@lem518936 h1) (@lem518937 n)). Qed.
Lemma lem518939 (m : nat) (n : nat) (h1 : term123 = term193) : ((term27 m) = (term27 n)) = ((term214 m) = (term214 n)).
Proof. exact (MK_COMB (@lem518932 m h1) (@lem518938 n h1)). Qed.
Lemma lem518942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem518943 (m : nat) (n : nat) (h1 : term123 = term193) : (term144 m n) = (term236 m n).
Proof. exact (MK_COMB (@lem518942) (@lem518939 m n h1)). Qed.
Lemma lem518949 (h1 : term123 = term193) : term123 = term193.
Proof. exact (h1). Qed.
Lemma lem518950 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem518951 (h1 : term123 = term193) : term194 = term195.
Proof. exact (MK_COMB (@lem518950) (@lem518949 h1)). Qed.
Lemma lem518952 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem518953 (h1 : term123 = term193) : (term123 = (NUMERAL 0)) = (term193 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem518951 h1) (@lem518952)). Qed.
Lemma lem518956 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem518957 (h1 : term123 = term193) : term225 = term226.
Proof. exact (MK_COMB (@lem518956) (@lem518953 h1)). Qed.
Lemma lem518958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem518959 (h1 : term123 = term193) : term227 = term228.
Proof. exact (MK_COMB (@lem518958) (@lem518957 h1)). Qed.
Lemma lem518960 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem518961 (m : nat) (n : nat) (h1 : term123 = term193) : (term176 m n) = (term229 m n).
Proof. exact (MK_COMB (@lem518959 h1) (@lem518960 m n)). Qed.
Lemma lem518964 (m : nat) (n : nat) (h1 : term123 = term193) : (term183 m n) = (term237 m n).
Proof. exact (MK_COMB (@lem518943 m n h1) (@lem518961 m n h1)). Qed.
Lemma lem518967 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem518968 (m : nat) (n : nat) (h1 : term123 = term193) : (term184 m n) = (term238 m n).
Proof. exact (MK_COMB (@lem518967) (@lem518964 m n h1)). Qed.
Lemma lem518969 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem518970 (m : nat) (n : nat) (h1 : term123 = term193) : ((term183 m n) = (Peano.le m n)) = ((term237 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem518968 m n h1) (@lem518969 m n)). Qed.
Lemma lem518973 (m : nat) (h1 : term123 = term193) : (term185 m) = (term239 m).
Proof. exact (fun_ext (fun n : nat => @lem518970 m n h1)). Qed.
Lemma lem518974 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518975 (m : nat) (h1 : term123 = term193) : (term186 m) = (term240 m).
Proof. exact (MK_COMB (@lem518974) (@lem518973 m h1)). Qed.
Lemma lem518980 (h1 : term123 = term193) : term187 = term241.
Proof. exact (fun_ext (fun m : nat => @lem518975 m h1)). Qed.
Lemma lem518981 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem518982 (h1 : term123 = term193) : term188 = term242.
Proof. exact (MK_COMB (@lem518981) (@lem518980 h1)). Qed.
Lemma lem518987 (h1 : term123 = term193) : term189 = term243.
Proof. exact (MK_COMB (@lem518910 h1) (@lem518982 h1)). Qed.
Lemma lem518990 (h1 : term123 = term193) : term190 = term244.
Proof. exact (MK_COMB (@lem518856 h1) (@lem518987 h1)). Qed.
Lemma lem518993 (h1 : term123 = term193) : term191 = term245.
Proof. exact (MK_COMB (@lem518776 h1) (@lem518990 h1)). Qed.
Lemma lem518996 (h1 : term123 = term193) : term192 = term246.
Proof. exact (MK_COMB (@lem518724 h1) (@lem518993 h1)). Qed.
Lemma lem518999 (h1 : term123 = term193) : term246 = term192.
Proof. exact (SYM (@lem518996 h1)). Qed.
Lemma lem519003 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem516734 n) (@lem516733 n)). Qed.
Lemma lem519004 : term123 = term247.
Proof. exact (@lem519003 term247). Qed.
Lemma lem519006 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem516731 n) (@lem516730 n)). Qed.
Lemma lem519007 : term247 = term248.
Proof. exact (@lem519006 (BIT1 0)). Qed.
Lemma lem519008 : term123 = term248.
Proof. exact (TRANS (@lem519004) (@lem519007)). Qed.
Lemma lem519010 (n : nat) : (BIT1 n) = (term10 n).
Proof. exact (EQ_MP (@lem516728 n) (@lem516727 n)). Qed.
Lemma lem519011 : (BIT1 0) = term249.
Proof. exact (@lem519010 0). Qed.
Lemma lem519013 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem516725 n) (@lem516724 n)). Qed.
Lemma lem519014 : (Nat.add 0 0) = 0.
Proof. exact (@lem519013 0). Qed.
Lemma lem519015 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem519016 : term249 = (S 0).
Proof. exact (MK_COMB (@lem519015) (@lem519014)). Qed.
Lemma lem519017 : (BIT1 0) = (S 0).
Proof. exact (TRANS (@lem519011) (@lem519016)). Qed.
Lemma lem519018 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem519019 : term250 = term251.
Proof. exact (MK_COMB (@lem519018) (@lem519017)). Qed.
Lemma lem519021 (n : nat) : (BIT1 n) = (term10 n).
Proof. exact (EQ_MP (@lem516728 n) (@lem516727 n)). Qed.
Lemma lem519022 : (BIT1 0) = term249.
Proof. exact (@lem519021 0). Qed.
Lemma lem519024 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem516725 n) (@lem516724 n)). Qed.
Lemma lem519025 : (Nat.add 0 0) = 0.
Proof. exact (@lem519024 0). Qed.
Lemma lem519026 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem519027 : term249 = (S 0).
Proof. exact (MK_COMB (@lem519026) (@lem519025)). Qed.
Lemma lem519028 : (BIT1 0) = (S 0).
Proof. exact (TRANS (@lem519022) (@lem519027)). Qed.
Lemma lem519029 : term248 = term252.
Proof. exact (MK_COMB (@lem519019) (@lem519028)). Qed.
Lemma lem519031 (m : nat) (n : nat) : (term253 m n) = (term254 m n).
Proof. exact (EQ_MP (@lem516717 m n) (@lem516716 m n)). Qed.
Lemma lem519032 : term252 = term255.
Proof. exact (@lem519031 0 (S 0)). Qed.
Lemma lem519034 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem516725 n) (@lem516724 n)). Qed.
Lemma lem519035 : term256 = (S 0).
Proof. exact (@lem519034 (S 0)). Qed.
Lemma lem519036 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem519037 : term255 = term257.
Proof. exact (MK_COMB (@lem519036) (@lem519035)). Qed.
Lemma lem519038 : term252 = term257.
Proof. exact (TRANS (@lem519032) (@lem519037)). Qed.
Lemma lem519039 : term248 = term257.
Proof. exact (TRANS (@lem519029) (@lem519038)). Qed.
Lemma lem519040 : term123 = term257.
Proof. exact (TRANS (@lem519008) (@lem519039)). Qed.
Lemma lem519041 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem519042 : term194 = term258.
Proof. exact (MK_COMB (@lem519041) (@lem519040)). Qed.
Lemma lem519044 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem516734 n) (@lem516733 n)). Qed.
Lemma lem519045 : term259 = (BIT1 0).
Proof. exact (@lem519044 (BIT1 0)). Qed.
Lemma lem519047 (n : nat) : (BIT1 n) = (term10 n).
Proof. exact (EQ_MP (@lem516728 n) (@lem516727 n)). Qed.
Lemma lem519048 : (BIT1 0) = term249.
Proof. exact (@lem519047 0). Qed.
Lemma lem519049 : term259 = term249.
Proof. exact (TRANS (@lem519045) (@lem519048)). Qed.
Lemma lem519051 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem516725 n) (@lem516724 n)). Qed.
Lemma lem519052 : (Nat.add 0 0) = 0.
Proof. exact (@lem519051 0). Qed.
Lemma lem519053 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem519054 : term249 = (S 0).
Proof. exact (MK_COMB (@lem519053) (@lem519052)). Qed.
Lemma lem519055 : term259 = (S 0).
Proof. exact (TRANS (@lem519049) (@lem519054)). Qed.
Lemma lem519056 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem519057 : term193 = term257.
Proof. exact (MK_COMB (@lem519056) (@lem519055)). Qed.
Lemma lem519058 : (term123 = term193) = (term257 = term257).
Proof. exact (MK_COMB (@lem519042) (@lem519057)). Qed.
Lemma lem519060 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem519061 (x : nat) : (x = x) = True.
Proof. exact (@lem519060 nat x). Qed.
Lemma lem519062 : (term257 = term257) = True.
Proof. exact (@lem519061 term257). Qed.
Lemma lem519063 : (term123 = term193) = True.
Proof. exact (TRANS (@lem519058) (@lem519062)). Qed.
Lemma lem519064 : True = (term123 = term193).
Proof. exact (SYM (@lem519063)). Qed.
Lemma lem519065 : term123 = term193.
Proof. exact (EQ_MP (@lem519064) (@lem0)). Qed.
Lemma lem519077 (n : nat) : ((S n) = 0) = False.
Proof. exact (@lem516656 n (@lem516655 n)). Qed.
Lemma lem519078 : (term193 = 0) = False.
Proof. exact (@lem519077 term259). Qed.
Lemma lem519079 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem519080 : term197 = (or False).
Proof. exact (MK_COMB (@lem519079) (@lem519078)). Qed.
Lemma lem519083 (n : nat) : (n = 0) = (n = 0).
Proof. exact (eq_refl (n = 0)). Qed.
Lemma lem519084 (n : nat) : (term198 n) = (term260 n).
Proof. exact (MK_COMB (@lem519080) (@lem519083 n)). Qed.
Lemma lem519086 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem519087 (n : nat) : (term260 n) = (n = 0).
Proof. exact (@lem519086 (n = 0)). Qed.
Lemma lem519090 (n : nat) : (term198 n) = (n = 0).
Proof. exact (TRANS (@lem519084 n) (@lem519087 n)). Qed.
Lemma lem519091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem519092 (n : nat) : (term199 n) = (term261 n).
Proof. exact (MK_COMB (@lem519091) (@lem519090 n)). Qed.
Lemma lem519095 (n : nat) : (n = 0) = (n = 0).
Proof. exact (eq_refl (n = 0)). Qed.
Lemma lem519096 (n : nat) : ((term198 n) = (n = 0)) = ((n = 0) = (n = 0)).
Proof. exact (MK_COMB (@lem519092 n) (@lem519095 n)). Qed.
Lemma lem519098 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem519099 (x : Prop) : (x = x) = True.
Proof. exact (@lem519098 Prop x). Qed.
Lemma lem519100 (n : nat) : ((n = 0) = (n = 0)) = True.
Proof. exact (@lem519099 (n = 0)). Qed.
Lemma lem519101 (n : nat) : ((term198 n) = (n = 0)) = True.
Proof. exact (TRANS (@lem519096 n) (@lem519100 n)). Qed.
Lemma lem519102 : term200 = term3.
Proof. exact (fun_ext (fun n : nat => @lem519101 n)). Qed.
Lemma lem519103 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519104 : term201 = term5.
Proof. exact (MK_COMB (@lem519103) (@lem519102)). Qed.
Lemma lem519106 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem519107 (t : Prop) : (term7 t) = t.
Proof. exact (@lem519106 nat t). Qed.
Lemma lem519108 : term5 = True.
Proof. exact (@lem519107 True). Qed.
Lemma lem519109 : term201 = True.
Proof. exact (TRANS (@lem519104) (@lem519108)). Qed.
Lemma lem519110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem519111 : term202 = (and True).
Proof. exact (MK_COMB (@lem519110) (@lem519109)). Qed.
Lemma lem519127 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem516640 n (@lem516639 n)). Qed.
Lemma lem519128 : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem519127 term259). Qed.
Lemma lem519129 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem519130 : term204 = (or False).
Proof. exact (MK_COMB (@lem519129) (@lem519128)). Qed.
Lemma lem519131 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem519132 (m : nat) (n : nat) : (term205 m n) = (term262 m n).
Proof. exact (MK_COMB (@lem519130) (@lem519131 m n)). Qed.
Lemma lem519134 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem519135 (m : nat) (n : nat) : (term262 m n) = (Peano.le m n).
Proof. exact (@lem519134 (Peano.le m n)). Qed.
Lemma lem519136 (m : nat) (n : nat) : (term205 m n) = (Peano.le m n).
Proof. exact (TRANS (@lem519132 m n) (@lem519135 m n)). Qed.
Lemma lem519137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem519138 (m : nat) (n : nat) : (term206 m n) = (term263 m n).
Proof. exact (MK_COMB (@lem519137) (@lem519136 m n)). Qed.
Lemma lem519139 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem519140 (m : nat) (n : nat) : ((term205 m n) = (Peano.le m n)) = ((Peano.le m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem519138 m n) (@lem519139 m n)). Qed.
Lemma lem519142 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem519143 (x : Prop) : (x = x) = True.
Proof. exact (@lem519142 Prop x). Qed.
Lemma lem519144 (m : nat) (n : nat) : ((Peano.le m n) = (Peano.le m n)) = True.
Proof. exact (@lem519143 (Peano.le m n)). Qed.
Lemma lem519145 (m : nat) (n : nat) : ((term205 m n) = (Peano.le m n)) = True.
Proof. exact (TRANS (@lem519140 m n) (@lem519144 m n)). Qed.
Lemma lem519146 (m : nat) : (term207 m) = term3.
Proof. exact (fun_ext (fun n : nat => @lem519145 m n)). Qed.
Lemma lem519147 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519148 (m : nat) : (term208 m) = term5.
Proof. exact (MK_COMB (@lem519147) (@lem519146 m)). Qed.
Lemma lem519150 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem519151 (t : Prop) : (term7 t) = t.
Proof. exact (@lem519150 nat t). Qed.
Lemma lem519152 : term5 = True.
Proof. exact (@lem519151 True). Qed.
Lemma lem519153 (m : nat) : (term208 m) = True.
Proof. exact (TRANS (@lem519148 m) (@lem519152)). Qed.
Lemma lem519154 : term209 = term3.
Proof. exact (fun_ext (fun m : nat => @lem519153 m)). Qed.
Lemma lem519155 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519156 : term210 = term5.
Proof. exact (MK_COMB (@lem519155) (@lem519154)). Qed.
Lemma lem519158 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem519159 (t : Prop) : (term7 t) = t.
Proof. exact (@lem519158 nat t). Qed.
Lemma lem519160 : term5 = True.
Proof. exact (@lem519159 True). Qed.
Lemma lem519161 : term210 = True.
Proof. exact (TRANS (@lem519156) (@lem519160)). Qed.
Lemma lem519162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem519163 : term211 = (and True).
Proof. exact (MK_COMB (@lem519162) (@lem519161)). Qed.
Lemma lem519183 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem516640 n (@lem516639 n)). Qed.
Lemma lem519184 : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem519183 term259). Qed.
Lemma lem519185 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem519186 : term204 = (or False).
Proof. exact (MK_COMB (@lem519185) (@lem519184)). Qed.
Lemma lem519187 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem519188 (m : nat) (n : nat) : (term205 m n) = (term262 m n).
Proof. exact (MK_COMB (@lem519186) (@lem519187 m n)). Qed.
Lemma lem519190 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem519191 (m : nat) (n : nat) : (term262 m n) = (Peano.le m n).
Proof. exact (@lem519190 (Peano.le m n)). Qed.
Lemma lem519192 (m : nat) (n : nat) : (term205 m n) = (Peano.le m n).
Proof. exact (TRANS (@lem519188 m n) (@lem519191 m n)). Qed.
Lemma lem519193 (m : nat) (n : nat) : (term217 m n) = (term217 m n).
Proof. exact (eq_refl (term217 m n)). Qed.
Lemma lem519194 (m : nat) (n : nat) : (term218 m n) = (term264 m n).
Proof. exact (MK_COMB (@lem519193 m n) (@lem519192 m n)). Qed.
Lemma lem519197 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem519198 (m : nat) (n : nat) : (term219 m n) = (term265 m n).
Proof. exact (MK_COMB (@lem519197) (@lem519194 m n)). Qed.
Lemma lem519199 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem519200 (m : nat) (n : nat) : ((term218 m n) = (Peano.le m n)) = ((term264 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem519198 m n) (@lem519199 m n)). Qed.
Lemma lem519203 (m : nat) : (term220 m) = (term266 m).
Proof. exact (fun_ext (fun n : nat => @lem519200 m n)). Qed.
Lemma lem519204 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519205 (m : nat) : (term221 m) = (term267 m).
Proof. exact (MK_COMB (@lem519204) (@lem519203 m)). Qed.
Lemma lem519210 : term222 = term268.
Proof. exact (fun_ext (fun m : nat => @lem519205 m)). Qed.
Lemma lem519211 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519212 : term223 = term269.
Proof. exact (MK_COMB (@lem519211) (@lem519210)). Qed.
Lemma lem519217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem519218 : term224 = term270.
Proof. exact (MK_COMB (@lem519217) (@lem519212)). Qed.
Lemma lem519234 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem516640 n (@lem516639 n)). Qed.
Lemma lem519235 : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem519234 term259). Qed.
Lemma lem519236 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem519237 : term226 = (~ False).
Proof. exact (MK_COMB (@lem519236) (@lem519235)). Qed.
Lemma lem519239 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem519240 : term226 = True.
Proof. exact (TRANS (@lem519237) (@lem519239)). Qed.
Lemma lem519241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem519242 : term228 = (and True).
Proof. exact (MK_COMB (@lem519241) (@lem519240)). Qed.
Lemma lem519243 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem519244 (m : nat) (n : nat) : (term229 m n) = (term271 m n).
Proof. exact (MK_COMB (@lem519242) (@lem519243 m n)). Qed.
Lemma lem519246 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem519247 (m : nat) (n : nat) : (term271 m n) = (Peano.lt m n).
Proof. exact (@lem519246 (Peano.lt m n)). Qed.
Lemma lem519248 (m : nat) (n : nat) : (term229 m n) = (Peano.lt m n).
Proof. exact (TRANS (@lem519244 m n) (@lem519247 m n)). Qed.
Lemma lem519249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem519250 (m : nat) (n : nat) : (term230 m n) = (term272 m n).
Proof. exact (MK_COMB (@lem519249) (@lem519248 m n)). Qed.
Lemma lem519251 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem519252 (m : nat) (n : nat) : ((term229 m n) = (Peano.lt m n)) = ((Peano.lt m n) = (Peano.lt m n)).
Proof. exact (MK_COMB (@lem519250 m n) (@lem519251 m n)). Qed.
Lemma lem519254 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem519255 (x : Prop) : (x = x) = True.
Proof. exact (@lem519254 Prop x). Qed.
Lemma lem519256 (m : nat) (n : nat) : ((Peano.lt m n) = (Peano.lt m n)) = True.
Proof. exact (@lem519255 (Peano.lt m n)). Qed.
Lemma lem519257 (m : nat) (n : nat) : ((term229 m n) = (Peano.lt m n)) = True.
Proof. exact (TRANS (@lem519252 m n) (@lem519256 m n)). Qed.
Lemma lem519258 (m : nat) : (term231 m) = term3.
Proof. exact (fun_ext (fun n : nat => @lem519257 m n)). Qed.
Lemma lem519259 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519260 (m : nat) : (term232 m) = term5.
Proof. exact (MK_COMB (@lem519259) (@lem519258 m)). Qed.
Lemma lem519262 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem519263 (t : Prop) : (term7 t) = t.
Proof. exact (@lem519262 nat t). Qed.
Lemma lem519264 : term5 = True.
Proof. exact (@lem519263 True). Qed.
Lemma lem519265 (m : nat) : (term232 m) = True.
Proof. exact (TRANS (@lem519260 m) (@lem519264)). Qed.
Lemma lem519266 : term233 = term3.
Proof. exact (fun_ext (fun m : nat => @lem519265 m)). Qed.
Lemma lem519267 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519268 : term234 = term5.
Proof. exact (MK_COMB (@lem519267) (@lem519266)). Qed.
Lemma lem519270 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem519271 (t : Prop) : (term7 t) = t.
Proof. exact (@lem519270 nat t). Qed.
Lemma lem519272 : term5 = True.
Proof. exact (@lem519271 True). Qed.
Lemma lem519273 : term234 = True.
Proof. exact (TRANS (@lem519268) (@lem519272)). Qed.
Lemma lem519274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem519275 : term235 = (and True).
Proof. exact (MK_COMB (@lem519274) (@lem519273)). Qed.
Lemma lem519289 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term273 m n p).
Proof. exact (EQ_MP (@lem516635 m n p) (@lem516634 m n p)). Qed.
Lemma lem519290 (m : nat) (n : nat) : ((term214 m) = (term214 n)) = (term274 m n).
Proof. exact (@lem519289 term193 m n). Qed.
Lemma lem519294 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem516640 n (@lem516639 n)). Qed.
Lemma lem519295 : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem519294 term259). Qed.
Lemma lem519296 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem519297 : term204 = (or False).
Proof. exact (MK_COMB (@lem519296) (@lem519295)). Qed.
Lemma lem519300 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem519301 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (MK_COMB (@lem519297) (@lem519300 m n)). Qed.
Lemma lem519303 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem519304 (m : nat) (n : nat) : (term275 m n) = (m = n).
Proof. exact (@lem519303 (m = n)). Qed.
Lemma lem519307 (m : nat) (n : nat) : (term274 m n) = (m = n).
Proof. exact (TRANS (@lem519301 m n) (@lem519304 m n)). Qed.
Lemma lem519308 (m : nat) (n : nat) : ((term214 m) = (term214 n)) = (m = n).
Proof. exact (TRANS (@lem519290 m n) (@lem519307 m n)). Qed.
Lemma lem519309 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem519310 (m : nat) (n : nat) : (term236 m n) = (term276 m n).
Proof. exact (MK_COMB (@lem519309) (@lem519308 m n)). Qed.
Lemma lem519314 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem516640 n (@lem516639 n)). Qed.
Lemma lem519315 : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem519314 term259). Qed.
Lemma lem519316 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem519317 : term226 = (~ False).
Proof. exact (MK_COMB (@lem519316) (@lem519315)). Qed.
Lemma lem519319 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem519320 : term226 = True.
Proof. exact (TRANS (@lem519317) (@lem519319)). Qed.
Lemma lem519321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem519322 : term228 = (and True).
Proof. exact (MK_COMB (@lem519321) (@lem519320)). Qed.
Lemma lem519323 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem519324 (m : nat) (n : nat) : (term229 m n) = (term271 m n).
Proof. exact (MK_COMB (@lem519322) (@lem519323 m n)). Qed.
Lemma lem519326 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem519327 (m : nat) (n : nat) : (term271 m n) = (Peano.lt m n).
Proof. exact (@lem519326 (Peano.lt m n)). Qed.
Lemma lem519328 (m : nat) (n : nat) : (term229 m n) = (Peano.lt m n).
Proof. exact (TRANS (@lem519324 m n) (@lem519327 m n)). Qed.
Lemma lem519329 (m : nat) (n : nat) : (term237 m n) = (term277 m n).
Proof. exact (MK_COMB (@lem519310 m n) (@lem519328 m n)). Qed.
Lemma lem519332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem519333 (m : nat) (n : nat) : (term238 m n) = (term278 m n).
Proof. exact (MK_COMB (@lem519332) (@lem519329 m n)). Qed.
Lemma lem519334 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem519335 (m : nat) (n : nat) : ((term237 m n) = (Peano.le m n)) = ((term277 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem519333 m n) (@lem519334 m n)). Qed.
Lemma lem519338 (m : nat) : (term239 m) = (term279 m).
Proof. exact (fun_ext (fun n : nat => @lem519335 m n)). Qed.
Lemma lem519339 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519340 (m : nat) : (term240 m) = (term280 m).
Proof. exact (MK_COMB (@lem519339) (@lem519338 m)). Qed.
Lemma lem519345 : term241 = term281.
Proof. exact (fun_ext (fun m : nat => @lem519340 m)). Qed.
Lemma lem519346 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519347 : term242 = term282.
Proof. exact (MK_COMB (@lem519346) (@lem519345)). Qed.
Lemma lem519352 : term243 = term283.
Proof. exact (MK_COMB (@lem519275) (@lem519347)). Qed.
Lemma lem519354 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem519355 : term283 = term282.
Proof. exact (@lem519354 term282). Qed.
Lemma lem519370 : term243 = term282.
Proof. exact (TRANS (@lem519352) (@lem519355)). Qed.
Lemma lem519371 : term244 = term284.
Proof. exact (MK_COMB (@lem519218) (@lem519370)). Qed.
Lemma lem519374 : term245 = term285.
Proof. exact (MK_COMB (@lem519163) (@lem519371)). Qed.
Lemma lem519376 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem519377 : term285 = term284.
Proof. exact (@lem519376 term284). Qed.
Lemma lem519408 : term245 = term284.
Proof. exact (TRANS (@lem519374) (@lem519377)). Qed.
Lemma lem519409 : term246 = term285.
Proof. exact (MK_COMB (@lem519111) (@lem519408)). Qed.
Lemma lem519411 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem519412 : term285 = term284.
Proof. exact (@lem519411 term284). Qed.
Lemma lem519443 : term246 = term284.
Proof. exact (TRANS (@lem519409) (@lem519412)). Qed.
Lemma lem519444 : term284 = term246.
Proof. exact (SYM (@lem519443)). Qed.
Lemma lem519462 (m : nat) (n : nat) : (Peano.le m n) = (term277 m n).
Proof. exact (EQ_MP (@lem516615 m n) (@lem516614 m n)). Qed.
Lemma lem519467 (m : nat) (n : nat) : (term217 m n) = (term217 m n).
Proof. exact (eq_refl (term217 m n)). Qed.
Lemma lem519468 (m : nat) (n : nat) : (term264 m n) = (term286 m n).
Proof. exact (MK_COMB (@lem519467 m n) (@lem519462 m n)). Qed.
Lemma lem519471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem519472 (m : nat) (n : nat) : (term265 m n) = (term287 m n).
Proof. exact (MK_COMB (@lem519471) (@lem519468 m n)). Qed.
Lemma lem519474 (m : nat) (n : nat) : (Peano.le m n) = (term277 m n).
Proof. exact (EQ_MP (@lem516615 m n) (@lem516614 m n)). Qed.
Lemma lem519479 (m : nat) (n : nat) : ((term264 m n) = (Peano.le m n)) = ((term286 m n) = (term277 m n)).
Proof. exact (MK_COMB (@lem519472 m n) (@lem519474 m n)). Qed.
Lemma lem519482 (m : nat) : (term266 m) = (term288 m).
Proof. exact (fun_ext (fun n : nat => @lem519479 m n)). Qed.
Lemma lem519483 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519484 (m : nat) : (term267 m) = (term289 m).
Proof. exact (MK_COMB (@lem519483) (@lem519482 m)). Qed.
Lemma lem519489 : term268 = term290.
Proof. exact (fun_ext (fun m : nat => @lem519484 m)). Qed.
Lemma lem519490 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519491 : term269 = term291.
Proof. exact (MK_COMB (@lem519490) (@lem519489)). Qed.
Lemma lem519496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem519497 : term270 = term292.
Proof. exact (MK_COMB (@lem519496) (@lem519491)). Qed.
Lemma lem519513 (m : nat) (n : nat) : (Peano.le m n) = (term277 m n).
Proof. exact (EQ_MP (@lem516615 m n) (@lem516614 m n)). Qed.
Lemma lem519518 (m : nat) (n : nat) : (term278 m n) = (term278 m n).
Proof. exact (eq_refl (term278 m n)). Qed.
Lemma lem519519 (m : nat) (n : nat) : ((term277 m n) = (Peano.le m n)) = ((term277 m n) = (term277 m n)).
Proof. exact (MK_COMB (@lem519518 m n) (@lem519513 m n)). Qed.
Lemma lem519521 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem519522 (x : Prop) : (x = x) = True.
Proof. exact (@lem519521 Prop x). Qed.
Lemma lem519523 (m : nat) (n : nat) : ((term277 m n) = (term277 m n)) = True.
Proof. exact (@lem519522 (term277 m n)). Qed.
Lemma lem519524 (m : nat) (n : nat) : ((term277 m n) = (Peano.le m n)) = True.
Proof. exact (TRANS (@lem519519 m n) (@lem519523 m n)). Qed.
Lemma lem519525 (m : nat) : (term279 m) = term3.
Proof. exact (fun_ext (fun n : nat => @lem519524 m n)). Qed.
Lemma lem519526 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519527 (m : nat) : (term280 m) = term5.
Proof. exact (MK_COMB (@lem519526) (@lem519525 m)). Qed.
Lemma lem519529 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem519530 (t : Prop) : (term7 t) = t.
Proof. exact (@lem519529 nat t). Qed.
Lemma lem519531 : term5 = True.
Proof. exact (@lem519530 True). Qed.
Lemma lem519532 (m : nat) : (term280 m) = True.
Proof. exact (TRANS (@lem519527 m) (@lem519531)). Qed.
Lemma lem519533 : term281 = term3.
Proof. exact (fun_ext (fun m : nat => @lem519532 m)). Qed.
Lemma lem519534 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem519535 : term282 = term5.
Proof. exact (MK_COMB (@lem519534) (@lem519533)). Qed.
Lemma lem519537 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem519538 (t : Prop) : (term7 t) = t.
Proof. exact (@lem519537 nat t). Qed.
Lemma lem519539 : term5 = True.
Proof. exact (@lem519538 True). Qed.
Lemma lem519540 : term282 = True.
Proof. exact (TRANS (@lem519535) (@lem519539)). Qed.
Lemma lem519541 : term284 = term293.
Proof. exact (MK_COMB (@lem519497) (@lem519540)). Qed.
Lemma lem519543 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem519544 : term293 = term291.
Proof. exact (@lem519543 term291). Qed.
Lemma lem519567 : term284 = term291.
Proof. exact (TRANS (@lem519541) (@lem519544)). Qed.
Lemma lem519568 : term291 = term284.
Proof. exact (SYM (@lem519567)). Qed.
Lemma lem519569 (m : nat) (n : nat) (h1 : term294 m n) : term294 m n.
Proof. exact (h1). Qed.
Lemma lem519570 (m : nat) (n : nat) : term295 m n.
Proof. exact (@lem82 ((term214 m) = (term216 n))). Qed.
Lemma lem519588 (m : nat) (n : nat) (h1 : term294 m n) : ((term214 m) = (term216 n)) = False.
Proof. exact (@lem519570 m n (@lem519569 m n h1)). Qed.
Lemma lem519589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem519590 (m : nat) (n : nat) (h1 : term294 m n) : (term217 m n) = (or False).
Proof. exact (MK_COMB (@lem519589) (@lem519588 m n h1)). Qed.
Lemma lem519595 (m : nat) (n : nat) : (term277 m n) = (term277 m n).
Proof. exact (eq_refl (term277 m n)). Qed.
Lemma lem519596 (m : nat) (n : nat) (h1 : term294 m n) : (term286 m n) = (term296 m n).
Proof. exact (MK_COMB (@lem519590 m n h1) (@lem519595 m n)). Qed.
Lemma lem519598 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem519599 (m : nat) (n : nat) : (term296 m n) = (term277 m n).
Proof. exact (@lem519598 (term277 m n)). Qed.
Lemma lem519604 (m : nat) (n : nat) (h1 : term294 m n) : (term286 m n) = (term277 m n).
Proof. exact (TRANS (@lem519596 m n h1) (@lem519599 m n)). Qed.
Lemma lem519605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem519606 (m : nat) (n : nat) (h1 : term294 m n) : (term287 m n) = (term278 m n).
Proof. exact (MK_COMB (@lem519605) (@lem519604 m n h1)). Qed.
Lemma lem519611 (m : nat) (n : nat) : (term277 m n) = (term277 m n).
Proof. exact (eq_refl (term277 m n)). Qed.
Lemma lem519612 (m : nat) (n : nat) (h1 : term294 m n) : ((term286 m n) = (term277 m n)) = ((term277 m n) = (term277 m n)).
Proof. exact (MK_COMB (@lem519606 m n h1) (@lem519611 m n)). Qed.
Lemma lem519614 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem519615 (x : Prop) : (x = x) = True.
Proof. exact (@lem519614 Prop x). Qed.
Lemma lem519616 (m : nat) (n : nat) : ((term277 m n) = (term277 m n)) = True.
Proof. exact (@lem519615 (term277 m n)). Qed.
Lemma lem519617 (m : nat) (n : nat) (h1 : term294 m n) : ((term286 m n) = (term277 m n)) = True.
Proof. exact (TRANS (@lem519612 m n h1) (@lem519616 m n)). Qed.
Lemma lem519618 (m : nat) (n : nat) (h1 : term294 m n) : True = ((term286 m n) = (term277 m n)).
Proof. exact (SYM (@lem519617 m n h1)). Qed.
Lemma lem519619 (m : nat) (n : nat) (h1 : term294 m n) : (term286 m n) = (term277 m n).
Proof. exact (EQ_MP (@lem519618 m n h1) (@lem0)). Qed.
Lemma lem519620 (m : nat) (n : nat) (h1 : (term214 m) = (term216 n)) : (term214 m) = (term216 n).
Proof. exact (h1). Qed.
Lemma lem519621 (m : nat) (n : nat) (h1 : (term214 m) = (term216 n)) : (term297 m) = (term298 n).
Proof. exact (MK_COMB (@lem516580) (@lem519620 m n h1)). Qed.
Lemma lem519625 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem519626 (m : nat) (n : nat) : (term299 m n) = (term300 m n).
Proof. exact (@lem519625 ((term297 m) = (term298 n))). Qed.
Lemma lem519630 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (EQ_MP (@lem516578 m n) (@lem516577 m n)). Qed.
Lemma lem519631 (m : nat) : (term297 m) = (term303 m).
Proof. exact (@lem519630 term193 m). Qed.
Lemma lem519635 (n : nat) : (term304 n) = (term305 n).
Proof. exact (EQ_MP (@lem516559 n) (@lem516558 n)). Qed.
Lemma lem519636 : term306 = term307.
Proof. exact (@lem519635 term259). Qed.
Lemma lem519638 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem516566 n) (@lem516565 n)). Qed.
Lemma lem519639 : term259 = (BIT1 0).
Proof. exact (@lem519638 (BIT1 0)). Qed.
Lemma lem519641 (n : nat) : (BIT1 n) = (term10 n).
Proof. exact (EQ_MP (@lem516563 n) (@lem516562 n)). Qed.
Lemma lem519642 : (BIT1 0) = term249.
Proof. exact (@lem519641 0). Qed.
Lemma lem519643 : term259 = term249.
Proof. exact (TRANS (@lem519639) (@lem519642)). Qed.
Lemma lem519644 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem519645 : term308 = term309.
Proof. exact (MK_COMB (@lem519644) (@lem519643)). Qed.
Lemma lem519647 (n : nat) : (term304 n) = (term305 n).
Proof. exact (EQ_MP (@lem516559 n) (@lem516558 n)). Qed.
Lemma lem519648 : term309 = term310.
Proof. exact (@lem519647 (Nat.add 0 0)). Qed.
Lemma lem519650 (m : nat) (n : nat) : (term311 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (EQ_MP (@lem516572 m n) (@lem516571 m n)). Qed.
Lemma lem519651 : term312 = ((Coq.Arith.PeanoNat.Nat.Even 0) = (Coq.Arith.PeanoNat.Nat.Even 0)).
Proof. exact (@lem519650 0 0). Qed.
Lemma lem519653 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem519654 (x : Prop) : (x = x) = True.
Proof. exact (@lem519653 Prop x). Qed.
Lemma lem519655 : ((Coq.Arith.PeanoNat.Nat.Even 0) = (Coq.Arith.PeanoNat.Nat.Even 0)) = True.
Proof. exact (@lem519654 (Coq.Arith.PeanoNat.Nat.Even 0)). Qed.
Lemma lem519656 : term312 = True.
Proof. exact (TRANS (@lem519651) (@lem519655)). Qed.
Lemma lem519657 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem519658 : term310 = (~ True).
Proof. exact (MK_COMB (@lem519657) (@lem519656)). Qed.
Lemma lem519660 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem519661 : term310 = False.
Proof. exact (TRANS (@lem519658) (@lem519660)). Qed.
Lemma lem519662 : term309 = False.
Proof. exact (TRANS (@lem519648) (@lem519661)). Qed.
Lemma lem519663 : term308 = False.
Proof. exact (TRANS (@lem519645) (@lem519662)). Qed.
Lemma lem519664 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem519665 : term307 = (~ False).
Proof. exact (MK_COMB (@lem519664) (@lem519663)). Qed.
Lemma lem519667 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem519668 : term307 = True.
Proof. exact (TRANS (@lem519665) (@lem519667)). Qed.
Lemma lem519669 : term306 = True.
Proof. exact (TRANS (@lem519636) (@lem519668)). Qed.
Lemma lem519670 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem519671 : term313 = (or True).
Proof. exact (MK_COMB (@lem519670) (@lem519669)). Qed.
Lemma lem519672 (m : nat) : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem519673 (m : nat) : (term303 m) = (term314 m).
Proof. exact (MK_COMB (@lem519671) (@lem519672 m)). Qed.
Lemma lem519675 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem519676 (m : nat) : (term314 m) = True.
Proof. exact (@lem519675 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem519677 (m : nat) : (term303 m) = True.
Proof. exact (TRANS (@lem519673 m) (@lem519676 m)). Qed.
Lemma lem519678 (m : nat) : (term297 m) = True.
Proof. exact (TRANS (@lem519631 m) (@lem519677 m)). Qed.
Lemma lem519679 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem519680 (m : nat) : (term315 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem519679) (@lem519678 m)). Qed.
Lemma lem519682 (n : nat) : (term304 n) = (term305 n).
Proof. exact (EQ_MP (@lem516559 n) (@lem516558 n)). Qed.
Lemma lem519683 (n : nat) : (term298 n) = (term316 n).
Proof. exact (@lem519682 (term214 n)). Qed.
Lemma lem519685 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (EQ_MP (@lem516578 m n) (@lem516577 m n)). Qed.
Lemma lem519686 (n : nat) : (term297 n) = (term303 n).
Proof. exact (@lem519685 term193 n). Qed.
Lemma lem519690 (n : nat) : (term304 n) = (term305 n).
Proof. exact (EQ_MP (@lem516559 n) (@lem516558 n)). Qed.
Lemma lem519691 : term306 = term307.
Proof. exact (@lem519690 term259). Qed.
Lemma lem519693 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem516566 n) (@lem516565 n)). Qed.
Lemma lem519694 : term259 = (BIT1 0).
Proof. exact (@lem519693 (BIT1 0)). Qed.
Lemma lem519696 (n : nat) : (BIT1 n) = (term10 n).
Proof. exact (EQ_MP (@lem516563 n) (@lem516562 n)). Qed.
Lemma lem519697 : (BIT1 0) = term249.
Proof. exact (@lem519696 0). Qed.
Lemma lem519698 : term259 = term249.
Proof. exact (TRANS (@lem519694) (@lem519697)). Qed.
Lemma lem519699 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem519700 : term308 = term309.
Proof. exact (MK_COMB (@lem519699) (@lem519698)). Qed.
Lemma lem519702 (n : nat) : (term304 n) = (term305 n).
Proof. exact (EQ_MP (@lem516559 n) (@lem516558 n)). Qed.
Lemma lem519703 : term309 = term310.
Proof. exact (@lem519702 (Nat.add 0 0)). Qed.
Lemma lem519705 (m : nat) (n : nat) : (term311 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (EQ_MP (@lem516572 m n) (@lem516571 m n)). Qed.
Lemma lem519706 : term312 = ((Coq.Arith.PeanoNat.Nat.Even 0) = (Coq.Arith.PeanoNat.Nat.Even 0)).
Proof. exact (@lem519705 0 0). Qed.
Lemma lem519708 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem519709 (x : Prop) : (x = x) = True.
Proof. exact (@lem519708 Prop x). Qed.
Lemma lem519710 : ((Coq.Arith.PeanoNat.Nat.Even 0) = (Coq.Arith.PeanoNat.Nat.Even 0)) = True.
Proof. exact (@lem519709 (Coq.Arith.PeanoNat.Nat.Even 0)). Qed.
Lemma lem519711 : term312 = True.
Proof. exact (TRANS (@lem519706) (@lem519710)). Qed.
Lemma lem519712 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem519713 : term310 = (~ True).
Proof. exact (MK_COMB (@lem519712) (@lem519711)). Qed.
Lemma lem519715 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem519716 : term310 = False.
Proof. exact (TRANS (@lem519713) (@lem519715)). Qed.
Lemma lem519717 : term309 = False.
Proof. exact (TRANS (@lem519703) (@lem519716)). Qed.
Lemma lem519718 : term308 = False.
Proof. exact (TRANS (@lem519700) (@lem519717)). Qed.
Lemma lem519719 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem519720 : term307 = (~ False).
Proof. exact (MK_COMB (@lem519719) (@lem519718)). Qed.
Lemma lem519722 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem519723 : term307 = True.
Proof. exact (TRANS (@lem519720) (@lem519722)). Qed.
Lemma lem519724 : term306 = True.
Proof. exact (TRANS (@lem519691) (@lem519723)). Qed.
Lemma lem519725 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem519726 : term313 = (or True).
Proof. exact (MK_COMB (@lem519725) (@lem519724)). Qed.
Lemma lem519727 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem519728 (n : nat) : (term303 n) = (term314 n).
Proof. exact (MK_COMB (@lem519726) (@lem519727 n)). Qed.
Lemma lem519730 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem519731 (n : nat) : (term314 n) = True.
Proof. exact (@lem519730 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem519732 (n : nat) : (term303 n) = True.
Proof. exact (TRANS (@lem519728 n) (@lem519731 n)). Qed.
Lemma lem519733 (n : nat) : (term297 n) = True.
Proof. exact (TRANS (@lem519686 n) (@lem519732 n)). Qed.
Lemma lem519734 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem519735 (n : nat) : (term316 n) = (~ True).
Proof. exact (MK_COMB (@lem519734) (@lem519733 n)). Qed.
Lemma lem519737 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem519738 (n : nat) : (term316 n) = False.
Proof. exact (TRANS (@lem519735 n) (@lem519737)). Qed.
Lemma lem519739 (n : nat) : (term298 n) = False.
Proof. exact (TRANS (@lem519683 n) (@lem519738 n)). Qed.
Lemma lem519740 (m : nat) (n : nat) : ((term297 m) = (term298 n)) = (True = False).
Proof. exact (MK_COMB (@lem519680 m) (@lem519739 n)). Qed.
Lemma lem519742 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem519743 : (True = False) = False.
Proof. exact (@lem519742 False). Qed.
Lemma lem519744 (m : nat) (n : nat) : ((term297 m) = (term298 n)) = False.
Proof. exact (TRANS (@lem519740 m n) (@lem519743)). Qed.
Lemma lem519745 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem519746 (m : nat) (n : nat) : (term300 m n) = (~ False).
Proof. exact (MK_COMB (@lem519745) (@lem519744 m n)). Qed.
Lemma lem519748 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem519749 (m : nat) (n : nat) : (term300 m n) = True.
Proof. exact (TRANS (@lem519746 m n) (@lem519748)). Qed.
Lemma lem519750 (m : nat) (n : nat) : (term299 m n) = True.
Proof. exact (TRANS (@lem519626 m n) (@lem519749 m n)). Qed.
Lemma lem519751 (m : nat) (n : nat) : True = (term299 m n).
Proof. exact (SYM (@lem519750 m n)). Qed.
Lemma lem519752 (m : nat) (n : nat) : term299 m n.
Proof. exact (EQ_MP (@lem519751 m n) (@lem0)). Qed.
Lemma lem519753 (m : nat) (n : nat) (h1 : (term214 m) = (term216 n)) : False.
Proof. exact (@lem519752 m n (@lem519621 m n h1)). Qed.
Lemma lem519754 (m : nat) (n : nat) : term317 m n.
Proof. exact (fun h0 : (term214 m) = (term216 n) => @lem519753 m n h0). Qed.
Lemma lem519755 (m : nat) (n : nat) : (term317 m n) = (term294 m n).
Proof. exact (@lem69 ((term214 m) = (term216 n))). Qed.
Lemma lem519756 (m : nat) (n : nat) : term294 m n.
Proof. exact (EQ_MP (@lem519755 m n) (@lem519754 m n)). Qed.
Lemma lem519757 (m : nat) (n : nat) : (term294 m n) = ((term286 m n) = (term277 m n)).
Proof. exact (prop_ext (fun h1 : term294 m n => @lem519619 m n h1) (fun h1 : (term286 m n) = (term277 m n) => @lem519756 m n)). Qed.
Lemma lem519758 (m : nat) (n : nat) : (term286 m n) = (term277 m n).
Proof. exact (EQ_MP (@lem519757 m n) (@lem519756 m n)). Qed.
Lemma lem519763 (m : nat) : term289 m.
Proof. exact (fun n : nat => @lem519758 m n). Qed.
Lemma lem519768 : term291.
Proof. exact (fun m : nat => @lem519763 m). Qed.
Lemma lem519769 : term284.
Proof. exact (EQ_MP (@lem519568) (@lem519768)). Qed.
Lemma lem519770 : term246.
Proof. exact (EQ_MP (@lem519444) (@lem519769)). Qed.
Lemma lem519771 (h1 : term123 = term193) : term192.
Proof. exact (EQ_MP (@lem518999 h1) (@lem519770)). Qed.
Lemma lem519772 : (term123 = term193) = term192.
Proof. exact (prop_ext (fun h1 : term123 = term193 => @lem519771 h1) (fun h1 : term192 => @lem519065)). Qed.
Lemma lem519773 : term192.
Proof. exact (EQ_MP (@lem519772) (@lem519065)). Qed.
Lemma lem519774 : term173.
Proof. exact (EQ_MP (@lem518678) (@lem519773)). Qed.
Lemma lem519776 : term155.
Proof. exact (EQ_MP (@lem518524) (@lem519774)). Qed.
Lemma lem519777 : term120.
Proof. exact (EQ_MP (@lem518298) (@lem519776)). Qed.
Lemma lem519778 : term23.
Proof. exact (EQ_MP (@lem518014) (@lem519777)). Qed.
Lemma lem519779 : term24.
Proof. exact (EQ_MP (@lem517704) (@lem519778)). Qed.
