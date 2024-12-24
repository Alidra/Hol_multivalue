Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm523589_term_abbrevs.
Require Import ARITH_EQ_spec.
Require Import LE_SUC_LT_spec.
Require Import LT_MULT_LCANCEL_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm13473_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm522101_spec.
Require Import thm522102_spec.
Require Import thm522107_spec.
Require Import thm522108_spec.
Require Import thm522116_spec.
Require Import thm522117_spec.
Require Import thm522119_spec.
Require Import thm522120_spec.
Require Import thm522125_spec.
Require Import thm522126_spec.
Require Import thm522131_spec.
Require Import thm522132_spec.
Require Import thm522153_spec.
Require Import thm522154_spec.
Require Import thm522160_spec.
Require Import thm522161_spec.
Require Import thm522183_spec.
Require Import thm522184_spec.
Require Import thm522189_spec.
Require Import thm522190_spec.
Require Import thm522192_spec.
Require Import thm522193_spec.
Require Import thm522195_spec.
Require Import thm522196_spec.
Require Import thm522198_spec.
Require Import thm522199_spec.
Require Import thm7_spec.
Lemma lem522780 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem522199 n) (@lem522198 n)). Qed.
Lemma lem522781 (m : nat) : (BIT0 m) = (Nat.add m m).
Proof. exact (@lem522780 m). Qed.
Lemma lem522782 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem522783 (m : nat) : (term0 m) = (term1 m).
Proof. exact (MK_COMB (@lem522782) (@lem522781 m)). Qed.
Lemma lem522785 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem522199 n) (@lem522198 n)). Qed.
Lemma lem522786 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (MK_COMB (@lem522783 m) (@lem522785 n)). Qed.
Lemma lem522787 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem522788 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem522787) (@lem522786 m n)). Qed.
Lemma lem522790 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem522199 n) (@lem522198 n)). Qed.
Lemma lem522791 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (@lem522790 (Nat.sub m n)). Qed.
Lemma lem522792 (m : nat) (n : nat) : ((term2 m n) = (term6 m n)) = ((term3 m n) = (term7 m n)).
Proof. exact (MK_COMB (@lem522788 m n) (@lem522791 m n)). Qed.
Lemma lem522793 (m : nat) : (term8 m) = (term9 m).
Proof. exact (fun_ext (fun n : nat => @lem522792 m n)). Qed.
Lemma lem522794 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522795 (m : nat) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem522794) (@lem522793 m)). Qed.
Lemma lem522796 : term12 = term13.
Proof. exact (fun_ext (fun m : nat => @lem522795 m)). Qed.
Lemma lem522797 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522798 : term14 = term15.
Proof. exact (MK_COMB (@lem522797) (@lem522796)). Qed.
Lemma lem522799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem522800 : term16 = term17.
Proof. exact (MK_COMB (@lem522799) (@lem522798)). Qed.
Lemma lem522802 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem522199 n) (@lem522198 n)). Qed.
Lemma lem522803 (m : nat) : (BIT0 m) = (Nat.add m m).
Proof. exact (@lem522802 m). Qed.
Lemma lem522804 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem522805 (m : nat) : (term0 m) = (term1 m).
Proof. exact (MK_COMB (@lem522804) (@lem522803 m)). Qed.
Lemma lem522807 (n : nat) : (BIT1 n) = (term18 n).
Proof. exact (EQ_MP (@lem522196 n) (@lem522195 n)). Qed.
Lemma lem522808 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem522805 m) (@lem522807 n)). Qed.
Lemma lem522809 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem522810 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem522809) (@lem522808 m n)). Qed.
Lemma lem522812 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem522199 n) (@lem522198 n)). Qed.
Lemma lem522813 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (@lem522812 (Nat.sub m n)). Qed.
Lemma lem522814 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem522815 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (MK_COMB (@lem522814) (@lem522813 m n)). Qed.
Lemma lem522816 (m : nat) (n : nat) : ((term19 m n) = (term23 m n)) = ((term20 m n) = (term24 m n)).
Proof. exact (MK_COMB (@lem522810 m n) (@lem522815 m n)). Qed.
Lemma lem522817 (m : nat) : (term25 m) = (term26 m).
Proof. exact (fun_ext (fun n : nat => @lem522816 m n)). Qed.
Lemma lem522818 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522819 (m : nat) : (term27 m) = (term28 m).
Proof. exact (MK_COMB (@lem522818) (@lem522817 m)). Qed.
Lemma lem522820 : term29 = term30.
Proof. exact (fun_ext (fun m : nat => @lem522819 m)). Qed.
Lemma lem522821 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522822 : term31 = term32.
Proof. exact (MK_COMB (@lem522821) (@lem522820)). Qed.
Lemma lem522823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem522824 : term33 = term34.
Proof. exact (MK_COMB (@lem522823) (@lem522822)). Qed.
Lemma lem522826 (n : nat) : (BIT1 n) = (term18 n).
Proof. exact (EQ_MP (@lem522196 n) (@lem522195 n)). Qed.
Lemma lem522827 (m : nat) : (BIT1 m) = (term18 m).
Proof. exact (@lem522826 m). Qed.
Lemma lem522828 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem522829 (m : nat) : (term35 m) = (term36 m).
Proof. exact (MK_COMB (@lem522828) (@lem522827 m)). Qed.
Lemma lem522831 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem522199 n) (@lem522198 n)). Qed.
Lemma lem522832 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (MK_COMB (@lem522829 m) (@lem522831 n)). Qed.
Lemma lem522833 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem522834 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem522833) (@lem522832 m n)). Qed.
Lemma lem522836 (n : nat) : (BIT1 n) = (term18 n).
Proof. exact (EQ_MP (@lem522196 n) (@lem522195 n)). Qed.
Lemma lem522837 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (@lem522836 (Nat.sub m n)). Qed.
Lemma lem522838 (n : nat) (m : nat) : (term43 n m) = (term43 n m).
Proof. exact (eq_refl (term43 n m)). Qed.
Lemma lem522839 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem522838 n m) (@lem522837 m n)). Qed.
Lemma lem522840 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem522841 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem522839 m n) (@lem522840)). Qed.
Lemma lem522842 (m : nat) (n : nat) : ((term37 m n) = (term46 m n)) = ((term38 m n) = (term47 m n)).
Proof. exact (MK_COMB (@lem522834 m n) (@lem522841 m n)). Qed.
Lemma lem522843 (m : nat) : (term48 m) = (term49 m).
Proof. exact (fun_ext (fun n : nat => @lem522842 m n)). Qed.
Lemma lem522844 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522845 (m : nat) : (term50 m) = (term51 m).
Proof. exact (MK_COMB (@lem522844) (@lem522843 m)). Qed.
Lemma lem522846 : term52 = term53.
Proof. exact (fun_ext (fun m : nat => @lem522845 m)). Qed.
Lemma lem522847 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522848 : term54 = term55.
Proof. exact (MK_COMB (@lem522847) (@lem522846)). Qed.
Lemma lem522849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem522850 : term56 = term57.
Proof. exact (MK_COMB (@lem522849) (@lem522848)). Qed.
Lemma lem522852 (n : nat) : (BIT1 n) = (term18 n).
Proof. exact (EQ_MP (@lem522196 n) (@lem522195 n)). Qed.
Lemma lem522853 (m : nat) : (BIT1 m) = (term18 m).
Proof. exact (@lem522852 m). Qed.
Lemma lem522854 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem522855 (m : nat) : (term35 m) = (term36 m).
Proof. exact (MK_COMB (@lem522854) (@lem522853 m)). Qed.
Lemma lem522857 (n : nat) : (BIT1 n) = (term18 n).
Proof. exact (EQ_MP (@lem522196 n) (@lem522195 n)). Qed.
Lemma lem522858 (m : nat) (n : nat) : (term58 m n) = (term59 m n).
Proof. exact (MK_COMB (@lem522855 m) (@lem522857 n)). Qed.
Lemma lem522859 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem522860 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (MK_COMB (@lem522859) (@lem522858 m n)). Qed.
Lemma lem522862 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem522199 n) (@lem522198 n)). Qed.
Lemma lem522863 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (@lem522862 (Nat.sub m n)). Qed.
Lemma lem522864 (m : nat) (n : nat) : ((term58 m n) = (term6 m n)) = ((term59 m n) = (term7 m n)).
Proof. exact (MK_COMB (@lem522860 m n) (@lem522863 m n)). Qed.
Lemma lem522865 (m : nat) : (term62 m) = (term63 m).
Proof. exact (fun_ext (fun n : nat => @lem522864 m n)). Qed.
Lemma lem522866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522867 (m : nat) : (term64 m) = (term65 m).
Proof. exact (MK_COMB (@lem522866) (@lem522865 m)). Qed.
Lemma lem522868 : term66 = term67.
Proof. exact (fun_ext (fun m : nat => @lem522867 m)). Qed.
Lemma lem522869 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522870 : term68 = term69.
Proof. exact (MK_COMB (@lem522869) (@lem522868)). Qed.
Lemma lem522871 : term70 = term71.
Proof. exact (MK_COMB (@lem522850) (@lem522870)). Qed.
Lemma lem522872 : term72 = term73.
Proof. exact (MK_COMB (@lem522824) (@lem522871)). Qed.
Lemma lem522873 : term74 = term75.
Proof. exact (MK_COMB (@lem522800) (@lem522872)). Qed.
Lemma lem522874 : term75 = term74.
Proof. exact (SYM (@lem522873)). Qed.
Lemma lem522888 (n : nat) : (Nat.add n n) = (term76 n).
Proof. exact (EQ_MP (@lem522193 n) (@lem522192 n)). Qed.
Lemma lem522889 (m : nat) : (Nat.add m m) = (term76 m).
Proof. exact (@lem522888 m). Qed.
Lemma lem522890 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem522891 (m : nat) : (term1 m) = (term77 m).
Proof. exact (MK_COMB (@lem522890) (@lem522889 m)). Qed.
Lemma lem522893 (n : nat) : (Nat.add n n) = (term76 n).
Proof. exact (EQ_MP (@lem522193 n) (@lem522192 n)). Qed.
Lemma lem522894 (m : nat) (n : nat) : (term3 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem522891 m) (@lem522893 n)). Qed.
Lemma lem522895 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem522896 (m : nat) (n : nat) : (term5 m n) = (term79 m n).
Proof. exact (MK_COMB (@lem522895) (@lem522894 m n)). Qed.
Lemma lem522898 (n : nat) : (Nat.add n n) = (term76 n).
Proof. exact (EQ_MP (@lem522193 n) (@lem522192 n)). Qed.
Lemma lem522899 (m : nat) (n : nat) : (term7 m n) = (term80 m n).
Proof. exact (@lem522898 (Nat.sub m n)). Qed.
Lemma lem522901 (n : nat) (m : nat) (p : nat) : (term81 m n p) = (term82 n m p).
Proof. exact (EQ_MP (@lem522184 n m p) (@lem522183 n m p)). Qed.
Lemma lem522902 (m : nat) (n : nat) : (term80 m n) = (term78 m n).
Proof. exact (@lem522901 m term83 n). Qed.
Lemma lem522903 (m : nat) (n : nat) : (term7 m n) = (term78 m n).
Proof. exact (TRANS (@lem522899 m n) (@lem522902 m n)). Qed.
Lemma lem522904 (m : nat) (n : nat) : ((term3 m n) = (term7 m n)) = ((term78 m n) = (term78 m n)).
Proof. exact (MK_COMB (@lem522896 m n) (@lem522903 m n)). Qed.
Lemma lem522906 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem522907 (x : nat) : (x = x) = True.
Proof. exact (@lem522906 nat x). Qed.
Lemma lem522908 (m : nat) (n : nat) : ((term78 m n) = (term78 m n)) = True.
Proof. exact (@lem522907 (term78 m n)). Qed.
Lemma lem522909 (m : nat) (n : nat) : ((term3 m n) = (term7 m n)) = True.
Proof. exact (TRANS (@lem522904 m n) (@lem522908 m n)). Qed.
Lemma lem522910 (m : nat) : (term9 m) = term84.
Proof. exact (fun_ext (fun n : nat => @lem522909 m n)). Qed.
Lemma lem522911 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522912 (m : nat) : (term11 m) = term85.
Proof. exact (MK_COMB (@lem522911) (@lem522910 m)). Qed.
Lemma lem522914 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem522915 (t : Prop) : (term87 t) = t.
Proof. exact (@lem522914 nat t). Qed.
Lemma lem522916 : term85 = True.
Proof. exact (@lem522915 True). Qed.
Lemma lem522917 (m : nat) : (term11 m) = True.
Proof. exact (TRANS (@lem522912 m) (@lem522916)). Qed.
Lemma lem522918 : term13 = term84.
Proof. exact (fun_ext (fun m : nat => @lem522917 m)). Qed.
Lemma lem522919 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522920 : term15 = term85.
Proof. exact (MK_COMB (@lem522919) (@lem522918)). Qed.
Lemma lem522922 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem522923 (t : Prop) : (term87 t) = t.
Proof. exact (@lem522922 nat t). Qed.
Lemma lem522924 : term85 = True.
Proof. exact (@lem522923 True). Qed.
Lemma lem522925 : term15 = True.
Proof. exact (TRANS (@lem522920) (@lem522924)). Qed.
Lemma lem522926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem522927 : term17 = (and True).
Proof. exact (MK_COMB (@lem522926) (@lem522925)). Qed.
Lemma lem522941 (n : nat) : (Nat.add n n) = (term76 n).
Proof. exact (EQ_MP (@lem522193 n) (@lem522192 n)). Qed.
Lemma lem522942 (m : nat) : (Nat.add m m) = (term76 m).
Proof. exact (@lem522941 m). Qed.
Lemma lem522943 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem522944 (m : nat) : (term1 m) = (term77 m).
Proof. exact (MK_COMB (@lem522943) (@lem522942 m)). Qed.
Lemma lem522946 (n : nat) : (Nat.add n n) = (term76 n).
Proof. exact (EQ_MP (@lem522193 n) (@lem522192 n)). Qed.
Lemma lem522947 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem522948 (n : nat) : (term18 n) = (term88 n).
Proof. exact (MK_COMB (@lem522947) (@lem522946 n)). Qed.
Lemma lem522949 (m : nat) (n : nat) : (term20 m n) = (term89 m n).
Proof. exact (MK_COMB (@lem522944 m) (@lem522948 n)). Qed.
Lemma lem522950 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem522951 (m : nat) (n : nat) : (term22 m n) = (term90 m n).
Proof. exact (MK_COMB (@lem522950) (@lem522949 m n)). Qed.
Lemma lem522953 (n : nat) : (Nat.add n n) = (term76 n).
Proof. exact (EQ_MP (@lem522193 n) (@lem522192 n)). Qed.
Lemma lem522954 (m : nat) (n : nat) : (term7 m n) = (term80 m n).
Proof. exact (@lem522953 (Nat.sub m n)). Qed.
Lemma lem522956 (n : nat) (m : nat) (p : nat) : (term81 m n p) = (term82 n m p).
Proof. exact (EQ_MP (@lem522184 n m p) (@lem522183 n m p)). Qed.
Lemma lem522957 (m : nat) (n : nat) : (term80 m n) = (term78 m n).
Proof. exact (@lem522956 m term83 n). Qed.
Lemma lem522958 (m : nat) (n : nat) : (term7 m n) = (term78 m n).
Proof. exact (TRANS (@lem522954 m n) (@lem522957 m n)). Qed.
Lemma lem522959 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem522960 (m : nat) (n : nat) : (term24 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem522959) (@lem522958 m n)). Qed.
Lemma lem522961 (m : nat) (n : nat) : ((term20 m n) = (term24 m n)) = ((term89 m n) = (term91 m n)).
Proof. exact (MK_COMB (@lem522951 m n) (@lem522960 m n)). Qed.
Lemma lem522964 (m : nat) : (term26 m) = (term92 m).
Proof. exact (fun_ext (fun n : nat => @lem522961 m n)). Qed.
Lemma lem522965 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522966 (m : nat) : (term28 m) = (term93 m).
Proof. exact (MK_COMB (@lem522965) (@lem522964 m)). Qed.
Lemma lem522971 : term30 = term94.
Proof. exact (fun_ext (fun m : nat => @lem522966 m)). Qed.
Lemma lem522972 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522973 : term32 = term95.
Proof. exact (MK_COMB (@lem522972) (@lem522971)). Qed.
Lemma lem522978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem522979 : term34 = term96.
Proof. exact (MK_COMB (@lem522978) (@lem522973)). Qed.
Lemma lem522993 (n : nat) : (Nat.add n n) = (term76 n).
Proof. exact (EQ_MP (@lem522193 n) (@lem522192 n)). Qed.
Lemma lem522994 (m : nat) : (Nat.add m m) = (term76 m).
Proof. exact (@lem522993 m). Qed.
Lemma lem522995 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem522996 (m : nat) : (term18 m) = (term88 m).
Proof. exact (MK_COMB (@lem522995) (@lem522994 m)). Qed.
Lemma lem522997 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem522998 (m : nat) : (term36 m) = (term97 m).
Proof. exact (MK_COMB (@lem522997) (@lem522996 m)). Qed.
Lemma lem523000 (n : nat) : (Nat.add n n) = (term76 n).
Proof. exact (EQ_MP (@lem522193 n) (@lem522192 n)). Qed.
Lemma lem523001 (m : nat) (n : nat) : (term38 m n) = (term98 m n).
Proof. exact (MK_COMB (@lem522998 m) (@lem523000 n)). Qed.
Lemma lem523002 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem523003 (m : nat) (n : nat) : (term40 m n) = (term99 m n).
Proof. exact (MK_COMB (@lem523002) (@lem523001 m n)). Qed.
Lemma lem523005 (n : nat) : (Nat.add n n) = (term76 n).
Proof. exact (EQ_MP (@lem522193 n) (@lem522192 n)). Qed.
Lemma lem523006 (m : nat) (n : nat) : (term7 m n) = (term80 m n).
Proof. exact (@lem523005 (Nat.sub m n)). Qed.
Lemma lem523008 (n : nat) (m : nat) (p : nat) : (term81 m n p) = (term82 n m p).
Proof. exact (EQ_MP (@lem522184 n m p) (@lem522183 n m p)). Qed.
Lemma lem523009 (m : nat) (n : nat) : (term80 m n) = (term78 m n).
Proof. exact (@lem523008 m term83 n). Qed.
Lemma lem523010 (m : nat) (n : nat) : (term7 m n) = (term78 m n).
Proof. exact (TRANS (@lem523006 m n) (@lem523009 m n)). Qed.
Lemma lem523011 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem523012 (m : nat) (n : nat) : (term42 m n) = (term100 m n).
Proof. exact (MK_COMB (@lem523011) (@lem523010 m n)). Qed.
Lemma lem523013 (n : nat) (m : nat) : (term43 n m) = (term43 n m).
Proof. exact (eq_refl (term43 n m)). Qed.
Lemma lem523014 (m : nat) (n : nat) : (term45 m n) = (term101 m n).
Proof. exact (MK_COMB (@lem523013 n m) (@lem523012 m n)). Qed.
Lemma lem523015 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem523016 (m : nat) (n : nat) : (term47 m n) = (term102 m n).
Proof. exact (MK_COMB (@lem523014 m n) (@lem523015)). Qed.
Lemma lem523017 (m : nat) (n : nat) : ((term38 m n) = (term47 m n)) = ((term98 m n) = (term102 m n)).
Proof. exact (MK_COMB (@lem523003 m n) (@lem523016 m n)). Qed.
Lemma lem523020 (m : nat) : (term49 m) = (term103 m).
Proof. exact (fun_ext (fun n : nat => @lem523017 m n)). Qed.
Lemma lem523021 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem523022 (m : nat) : (term51 m) = (term104 m).
Proof. exact (MK_COMB (@lem523021) (@lem523020 m)). Qed.
Lemma lem523027 : term53 = term105.
Proof. exact (fun_ext (fun m : nat => @lem523022 m)). Qed.
Lemma lem523028 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem523029 : term55 = term106.
Proof. exact (MK_COMB (@lem523028) (@lem523027)). Qed.
Lemma lem523034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem523035 : term57 = term107.
Proof. exact (MK_COMB (@lem523034) (@lem523029)). Qed.
Lemma lem523047 (m : nat) (n : nat) : (term108 m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem522190 m n) (@lem522189 m n)). Qed.
Lemma lem523048 (m : nat) (n : nat) : (term59 m n) = (term3 m n).
Proof. exact (@lem523047 (Nat.add m m) (Nat.add n n)). Qed.
Lemma lem523050 (n : nat) : (Nat.add n n) = (term76 n).
Proof. exact (EQ_MP (@lem522193 n) (@lem522192 n)). Qed.
Lemma lem523051 (m : nat) : (Nat.add m m) = (term76 m).
Proof. exact (@lem523050 m). Qed.
Lemma lem523052 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem523053 (m : nat) : (term1 m) = (term77 m).
Proof. exact (MK_COMB (@lem523052) (@lem523051 m)). Qed.
Lemma lem523055 (n : nat) : (Nat.add n n) = (term76 n).
Proof. exact (EQ_MP (@lem522193 n) (@lem522192 n)). Qed.
Lemma lem523056 (m : nat) (n : nat) : (term3 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem523053 m) (@lem523055 n)). Qed.
Lemma lem523057 (m : nat) (n : nat) : (term59 m n) = (term78 m n).
Proof. exact (TRANS (@lem523048 m n) (@lem523056 m n)). Qed.
Lemma lem523058 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem523059 (m : nat) (n : nat) : (term61 m n) = (term79 m n).
Proof. exact (MK_COMB (@lem523058) (@lem523057 m n)). Qed.
Lemma lem523061 (n : nat) : (Nat.add n n) = (term76 n).
Proof. exact (EQ_MP (@lem522193 n) (@lem522192 n)). Qed.
Lemma lem523062 (m : nat) (n : nat) : (term7 m n) = (term80 m n).
Proof. exact (@lem523061 (Nat.sub m n)). Qed.
Lemma lem523064 (n : nat) (m : nat) (p : nat) : (term81 m n p) = (term82 n m p).
Proof. exact (EQ_MP (@lem522184 n m p) (@lem522183 n m p)). Qed.
Lemma lem523065 (m : nat) (n : nat) : (term80 m n) = (term78 m n).
Proof. exact (@lem523064 m term83 n). Qed.
Lemma lem523066 (m : nat) (n : nat) : (term7 m n) = (term78 m n).
Proof. exact (TRANS (@lem523062 m n) (@lem523065 m n)). Qed.
Lemma lem523067 (m : nat) (n : nat) : ((term59 m n) = (term7 m n)) = ((term78 m n) = (term78 m n)).
Proof. exact (MK_COMB (@lem523059 m n) (@lem523066 m n)). Qed.
Lemma lem523069 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem523070 (x : nat) : (x = x) = True.
Proof. exact (@lem523069 nat x). Qed.
Lemma lem523071 (m : nat) (n : nat) : ((term78 m n) = (term78 m n)) = True.
Proof. exact (@lem523070 (term78 m n)). Qed.
Lemma lem523072 (m : nat) (n : nat) : ((term59 m n) = (term7 m n)) = True.
Proof. exact (TRANS (@lem523067 m n) (@lem523071 m n)). Qed.
Lemma lem523073 (m : nat) : (term63 m) = term84.
Proof. exact (fun_ext (fun n : nat => @lem523072 m n)). Qed.
Lemma lem523074 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem523075 (m : nat) : (term65 m) = term85.
Proof. exact (MK_COMB (@lem523074) (@lem523073 m)). Qed.
Lemma lem523077 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem523078 (t : Prop) : (term87 t) = t.
Proof. exact (@lem523077 nat t). Qed.
Lemma lem523079 : term85 = True.
Proof. exact (@lem523078 True). Qed.
Lemma lem523080 (m : nat) : (term65 m) = True.
Proof. exact (TRANS (@lem523075 m) (@lem523079)). Qed.
Lemma lem523081 : term67 = term84.
Proof. exact (fun_ext (fun m : nat => @lem523080 m)). Qed.
Lemma lem523082 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem523083 : term69 = term85.
Proof. exact (MK_COMB (@lem523082) (@lem523081)). Qed.
Lemma lem523085 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem523086 (t : Prop) : (term87 t) = t.
Proof. exact (@lem523085 nat t). Qed.
Lemma lem523087 : term85 = True.
Proof. exact (@lem523086 True). Qed.
Lemma lem523088 : term69 = True.
Proof. exact (TRANS (@lem523083) (@lem523087)). Qed.
Lemma lem523089 : term71 = term109.
Proof. exact (MK_COMB (@lem523035) (@lem523088)). Qed.
Lemma lem523091 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem523092 : term109 = term106.
Proof. exact (@lem523091 term106). Qed.
Lemma lem523103 : term71 = term106.
Proof. exact (TRANS (@lem523089) (@lem523092)). Qed.
Lemma lem523104 : term73 = term110.
Proof. exact (MK_COMB (@lem522979) (@lem523103)). Qed.
Lemma lem523107 : term75 = term111.
Proof. exact (MK_COMB (@lem522927) (@lem523104)). Qed.
Lemma lem523109 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem523110 : term111 = term110.
Proof. exact (@lem523109 term110). Qed.
Lemma lem523133 : term75 = term110.
Proof. exact (TRANS (@lem523107) (@lem523110)). Qed.
Lemma lem523134 : term110 = term75.
Proof. exact (SYM (@lem523133)). Qed.
Lemma lem523148 (m : nat) (n : nat) : (term112 m n) = (term113 m n).
Proof. exact (EQ_MP (@lem522161 m n) (@lem522160 m n)). Qed.
Lemma lem523149 (m : nat) (n : nat) : (term89 m n) = (term91 m n).
Proof. exact (@lem523148 (term76 m) (term76 n)). Qed.
Lemma lem523150 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem523151 (m : nat) (n : nat) : (term90 m n) = (term114 m n).
Proof. exact (MK_COMB (@lem523150) (@lem523149 m n)). Qed.
Lemma lem523152 (m : nat) (n : nat) : (term91 m n) = (term91 m n).
Proof. exact (eq_refl (term91 m n)). Qed.
Lemma lem523153 (m : nat) (n : nat) : ((term89 m n) = (term91 m n)) = ((term91 m n) = (term91 m n)).
Proof. exact (MK_COMB (@lem523151 m n) (@lem523152 m n)). Qed.
Lemma lem523155 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem523156 (x : nat) : (x = x) = True.
Proof. exact (@lem523155 nat x). Qed.
Lemma lem523157 (m : nat) (n : nat) : ((term91 m n) = (term91 m n)) = True.
Proof. exact (@lem523156 (term91 m n)). Qed.
Lemma lem523158 (m : nat) (n : nat) : ((term89 m n) = (term91 m n)) = True.
Proof. exact (TRANS (@lem523153 m n) (@lem523157 m n)). Qed.
Lemma lem523159 (m : nat) : (term92 m) = term84.
Proof. exact (fun_ext (fun n : nat => @lem523158 m n)). Qed.
Lemma lem523160 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem523161 (m : nat) : (term93 m) = term85.
Proof. exact (MK_COMB (@lem523160) (@lem523159 m)). Qed.
Lemma lem523163 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem523164 (t : Prop) : (term87 t) = t.
Proof. exact (@lem523163 nat t). Qed.
Lemma lem523165 : term85 = True.
Proof. exact (@lem523164 True). Qed.
Lemma lem523166 (m : nat) : (term93 m) = True.
Proof. exact (TRANS (@lem523161 m) (@lem523165)). Qed.
Lemma lem523167 : term94 = term84.
Proof. exact (fun_ext (fun m : nat => @lem523166 m)). Qed.
Lemma lem523168 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem523169 : term95 = term85.
Proof. exact (MK_COMB (@lem523168) (@lem523167)). Qed.
Lemma lem523171 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem523172 (t : Prop) : (term87 t) = t.
Proof. exact (@lem523171 nat t). Qed.
Lemma lem523173 : term85 = True.
Proof. exact (@lem523172 True). Qed.
Lemma lem523174 : term95 = True.
Proof. exact (TRANS (@lem523169) (@lem523173)). Qed.
Lemma lem523175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem523176 : term96 = (and True).
Proof. exact (MK_COMB (@lem523175) (@lem523174)). Qed.
Lemma lem523187 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem523188 : term110 = term115.
Proof. exact (MK_COMB (@lem523176) (@lem523187)). Qed.
Lemma lem523190 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem523191 : term115 = term106.
Proof. exact (@lem523190 term106). Qed.
Lemma lem523202 : term110 = term106.
Proof. exact (TRANS (@lem523188) (@lem523191)). Qed.
Lemma lem523203 : term106 = term110.
Proof. exact (SYM (@lem523202)). Qed.
Lemma lem523204 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term116 _476 _475 _474 _477) = (term117 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem523205 (_474 : nat) (_475 : Prop) (m : nat) (n : nat) (_477 : nat) : (term118 m n _475 _474 _477) = (term119 _474 _475 m n _477).
Proof. exact (@lem523204 _474 _475 (term120 m n) _477). Qed.
Lemma lem523206 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (@lem523205 (term100 m n) (Peano.le n m) m n 0). Qed.
Lemma lem523207 (m : nat) (n : nat) : (term123 m n) = ((term98 m n) = 0).
Proof. exact (eq_refl (term123 m n)). Qed.
Lemma lem523208 (n : nat) (m : nat) : (term124 n m) = (term124 n m).
Proof. exact (eq_refl (term124 n m)). Qed.
Lemma lem523209 (m : nat) (n : nat) : (term125 m n) = (term126 m n).
Proof. exact (MK_COMB (@lem523208 n m) (@lem523207 m n)). Qed.
Lemma lem523210 (m : nat) (n : nat) : (term127 m n) = ((term98 m n) = (term100 m n)).
Proof. exact (eq_refl (term127 m n)). Qed.
Lemma lem523211 (n : nat) (m : nat) : (term128 n m) = (term128 n m).
Proof. exact (eq_refl (term128 n m)). Qed.
Lemma lem523212 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (MK_COMB (@lem523211 n m) (@lem523210 m n)). Qed.
Lemma lem523213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem523214 (m : nat) (n : nat) : (term131 m n) = (term132 m n).
Proof. exact (MK_COMB (@lem523213) (@lem523212 m n)). Qed.
Lemma lem523215 (m : nat) (n : nat) : (term122 m n) = (term133 m n).
Proof. exact (MK_COMB (@lem523214 m n) (@lem523209 m n)). Qed.
Lemma lem523216 (m : nat) (n : nat) : (term121 m n) = ((term98 m n) = (term102 m n)).
Proof. exact (eq_refl (term121 m n)). Qed.
Lemma lem523217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem523218 (m : nat) (n : nat) : (term134 m n) = (term135 m n).
Proof. exact (MK_COMB (@lem523217) (@lem523216 m n)). Qed.
Lemma lem523219 (m : nat) (n : nat) : ((term121 m n) = (term122 m n)) = (((term98 m n) = (term102 m n)) = (term133 m n)).
Proof. exact (MK_COMB (@lem523218 m n) (@lem523215 m n)). Qed.
Lemma lem523220 (m : nat) (n : nat) : ((term98 m n) = (term102 m n)) = (term133 m n).
Proof. exact (EQ_MP (@lem523219 m n) (@lem523206 m n)). Qed.
Lemma lem523221 (m : nat) (n : nat) : (term133 m n) = ((term98 m n) = (term102 m n)).
Proof. exact (SYM (@lem523220 m n)). Qed.
Lemma lem523222 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem523239 (n : nat) (m : nat) (h1 : term136 n m) : term136 n m.
Proof. exact (h1). Qed.
Lemma lem523261 (m : nat) (n : nat) : ((Nat.sub m n) = 0) = (Peano.le m n).
Proof. exact (EQ_MP (@lem522154 m n) (@lem522153 m n)). Qed.
Lemma lem523262 (m : nat) (n : nat) : ((term98 m n) = 0) = (term137 m n).
Proof. exact (@lem523261 (term88 m) (term76 n)). Qed.
Lemma lem523263 (m : nat) (n : nat) : (term137 m n) = ((term98 m n) = 0).
Proof. exact (SYM (@lem523262 m n)). Qed.
Lemma lem523265 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem523267 (n : nat) (m : nat) : (term136 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem522132 n m) (@lem522131 m n)). Qed.
Lemma lem523268 (m : nat) (n : nat) : (term136 n m) = (Peano.lt m n).
Proof. exact (@lem523267 m n). Qed.
Lemma lem523269 (n : nat) (m : nat) (h1 : term136 n m) : Peano.lt m n.
Proof. exact (EQ_MP (@lem523268 m n) (@lem523239 n m h1)). Qed.
Lemma lem523351 : term138.
Proof. exact (proj2 (@lem522076)). Qed.
Lemma lem523352 : term139.
Proof. exact (proj2 (@lem523351)). Qed.
Lemma lem523353 : term140.
Proof. exact (proj2 (@lem523352)). Qed.
Lemma lem523395 : term141.
Proof. exact (proj1 (@lem523353)). Qed.
Lemma lem523396 (n : nat) : term142 n.
Proof. exact (@lem523395 n). Qed.
Lemma lem523397 (n : nat) : (term142 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term142 n)). Qed.
Lemma lem523399 : term143.
Proof. exact (proj1 (@lem523352)). Qed.
Lemma lem523400 (n : nat) : term144 n.
Proof. exact (@lem523399 n). Qed.
Lemma lem523401 (n : nat) : (term144 n) = (((BIT0 n) = 0) = (n = 0)).
Proof. exact (eq_refl (term144 n)). Qed.
Lemma lem523404 : term145.
Proof. exact (proj1 (@lem522076)). Qed.
Lemma lem523405 (m : nat) : term146 m.
Proof. exact (@lem523404 m). Qed.
Lemma lem523406 (m : nat) : (term146 m) = (term147 m).
Proof. exact (eq_refl (term146 m)). Qed.
Lemma lem523407 (m : nat) : term147 m.
Proof. exact (EQ_MP (@lem523406 m) (@lem523405 m)). Qed.
Lemma lem523408 (m : nat) (n : nat) : term148 m n.
Proof. exact (@lem523407 m n). Qed.
Lemma lem523409 (m : nat) (n : nat) : (term148 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term148 m n)). Qed.
Lemma lem523411 (m : nat) : term149 m.
Proof. exact (@lem105882 m). Qed.
Lemma lem523412 (m : nat) : (term149 m) = (term150 m).
Proof. exact (eq_refl (term149 m)). Qed.
Lemma lem523413 (m : nat) : term150 m.
Proof. exact (EQ_MP (@lem523412 m) (@lem523411 m)). Qed.
Lemma lem523414 (m : nat) (n : nat) : term151 m n.
Proof. exact (@lem523413 m n). Qed.
Lemma lem523415 (m : nat) (n : nat) : (term151 m n) = (term152 m n).
Proof. exact (eq_refl (term151 m n)). Qed.
Lemma lem523416 (m : nat) (n : nat) : term152 m n.
Proof. exact (EQ_MP (@lem523415 m n) (@lem523414 m n)). Qed.
Lemma lem523417 (m : nat) (n : nat) (p : nat) : term153 m n p.
Proof. exact (@lem523416 m n p). Qed.
Lemma lem523418 (m : nat) (n : nat) (p : nat) : (term153 m n p) = ((term154 n m p) = (term155 m n p)).
Proof. exact (eq_refl (term153 m n p)). Qed.
Lemma lem523420 (m : nat) : term156 m.
Proof. exact (@lem91144 m). Qed.
Lemma lem523421 (m : nat) : (term156 m) = (term157 m).
Proof. exact (eq_refl (term156 m)). Qed.
Lemma lem523422 (m : nat) : term157 m.
Proof. exact (EQ_MP (@lem523421 m) (@lem523420 m)). Qed.
Lemma lem523423 (m : nat) (n : nat) : term158 m n.
Proof. exact (@lem523422 m n). Qed.
Lemma lem523424 (m : nat) (n : nat) : (term158 m n) = ((term159 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term158 m n)). Qed.
Lemma lem523426 (m : nat) (n : nat) : (Peano.lt m n) = ((Peano.lt m n) = True).
Proof. exact (@lem7 (Peano.lt m n)). Qed.
Lemma lem523429 (m : nat) (n : nat) : (term159 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem523424 m n) (@lem523423 m n)). Qed.
Lemma lem523430 (m : nat) (n : nat) : (term137 m n) = (term160 m n).
Proof. exact (@lem523429 (term76 m) (term76 n)). Qed.
Lemma lem523432 (m : nat) (n : nat) (p : nat) : (term154 n m p) = (term155 m n p).
Proof. exact (EQ_MP (@lem523418 m n p) (@lem523417 m n p)). Qed.
Lemma lem523433 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (@lem523432 term83 m n). Qed.
Lemma lem523436 (m : nat) (n : nat) : (term137 m n) = (term161 m n).
Proof. exact (TRANS (@lem523430 m n) (@lem523433 m n)). Qed.
Lemma lem523438 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem523409 m n) (@lem523408 m n)). Qed.
Lemma lem523439 : (term83 = (NUMERAL 0)) = (term162 = 0).
Proof. exact (@lem523438 term162 0). Qed.
Lemma lem523441 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem523401 n) (@lem523400 n)). Qed.
Lemma lem523442 : (term162 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem523441 (BIT1 0)). Qed.
Lemma lem523444 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem523397 n) (@lem523396 n)). Qed.
Lemma lem523445 : ((BIT1 0) = 0) = False.
Proof. exact (@lem523444 0). Qed.
Lemma lem523446 : (term162 = 0) = False.
Proof. exact (TRANS (@lem523442) (@lem523445)). Qed.
Lemma lem523447 : (term83 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem523439) (@lem523446)). Qed.
Lemma lem523448 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem523449 : term163 = (~ False).
Proof. exact (MK_COMB (@lem523448) (@lem523447)). Qed.
Lemma lem523451 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem523452 : term163 = True.
Proof. exact (TRANS (@lem523449) (@lem523451)). Qed.
Lemma lem523453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem523454 : term164 = (and True).
Proof. exact (MK_COMB (@lem523453) (@lem523452)). Qed.
Lemma lem523456 (n : nat) (m : nat) (h1 : term136 n m) : (Peano.lt m n) = True.
Proof. exact (EQ_MP (@lem523426 m n) (@lem523269 n m h1)). Qed.
Lemma lem523457 (n : nat) (m : nat) (h1 : term136 n m) : (term161 m n) = (True /\ True).
Proof. exact (MK_COMB (@lem523454) (@lem523456 n m h1)). Qed.
Lemma lem523459 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem523460 : (True /\ True) = True.
Proof. exact (@lem523459 True). Qed.
Lemma lem523461 (n : nat) (m : nat) (h1 : term136 n m) : (term161 m n) = True.
Proof. exact (TRANS (@lem523457 n m h1) (@lem523460)). Qed.
Lemma lem523462 (n : nat) (m : nat) (h1 : term136 n m) : (term137 m n) = True.
Proof. exact (TRANS (@lem523436 m n) (@lem523461 n m h1)). Qed.
Lemma lem523463 (n : nat) (m : nat) (h1 : term136 n m) : True = (term137 m n).
Proof. exact (SYM (@lem523462 n m h1)). Qed.
Lemma lem523464 (n : nat) (m : nat) (h1 : term136 n m) : term137 m n.
Proof. exact (EQ_MP (@lem523463 n m h1) (@lem0)). Qed.
Lemma lem523466 (n : nat) (m : nat) : (Peano.le m n) = (term165 n m).
Proof. exact (EQ_MP (@lem522126 n m) (@lem522125 m n)). Qed.
Lemma lem523467 (m : nat) (n : nat) : (Peano.le n m) = (term165 m n).
Proof. exact (@lem523466 m n). Qed.
Lemma lem523474 (n : nat) (m : nat) (h1 : Peano.le n m) : term165 m n.
Proof. exact (EQ_MP (@lem523467 m n) (@lem523265 n m h1)). Qed.
Lemma lem523475 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : m = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem523476 (n : nat) : (term166 n) = (term166 n).
Proof. exact (eq_refl (term166 n)). Qed.
Lemma lem523477 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term167 n m) = (term168 n d).
Proof. exact (MK_COMB (@lem523476 n) (@lem523475 m n d h1)). Qed.
Lemma lem523478 (d : nat) (n : nat) : (term168 n d) = ((term169 d n) = (term170 d n)).
Proof. exact (eq_refl (term168 n d)). Qed.
Lemma lem523479 (n : nat) (m : nat) : (term171 n m) = (term171 n m).
Proof. exact (eq_refl (term171 n m)). Qed.
Lemma lem523480 (m : nat) (d : nat) (n : nat) : ((term167 n m) = (term168 n d)) = ((term167 n m) = ((term169 d n) = (term170 d n))).
Proof. exact (MK_COMB (@lem523479 n m) (@lem523478 d n)). Qed.
Lemma lem523481 (m : nat) (n : nat) : (term167 n m) = ((term98 m n) = (term100 m n)).
Proof. exact (eq_refl (term167 n m)). Qed.
Lemma lem523482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem523483 (m : nat) (n : nat) : (term171 n m) = (term172 m n).
Proof. exact (MK_COMB (@lem523482) (@lem523481 m n)). Qed.
Lemma lem523484 (d : nat) (n : nat) : ((term169 d n) = (term170 d n)) = ((term169 d n) = (term170 d n)).
Proof. exact (eq_refl ((term169 d n) = (term170 d n))). Qed.
Lemma lem523485 (m : nat) (d : nat) (n : nat) : ((term167 n m) = ((term169 d n) = (term170 d n))) = (((term98 m n) = (term100 m n)) = ((term169 d n) = (term170 d n))).
Proof. exact (MK_COMB (@lem523483 m n) (@lem523484 d n)). Qed.
Lemma lem523486 (m : nat) (d : nat) (n : nat) : ((term167 n m) = (term168 n d)) = (((term98 m n) = (term100 m n)) = ((term169 d n) = (term170 d n))).
Proof. exact (TRANS (@lem523480 m d n) (@lem523485 m d n)). Qed.
Lemma lem523487 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : ((term98 m n) = (term100 m n)) = ((term169 d n) = (term170 d n)).
Proof. exact (EQ_MP (@lem523486 m d n) (@lem523477 m n d h1)). Qed.
Lemma lem523488 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : ((term169 d n) = (term170 d n)) = ((term98 m n) = (term100 m n)).
Proof. exact (SYM (@lem523487 m n d h1)). Qed.
Lemma lem523492 (m : nat) : (S m) = (term173 m).
Proof. exact (EQ_MP (@lem522120 m) (@lem522119 m)). Qed.
Lemma lem523493 (n : nat) (d : nat) : (term174 n d) = (term175 n d).
Proof. exact (@lem523492 (term176 n d)). Qed.
Lemma lem523495 (n : nat) (m : nat) (p : nat) : (term177 m n p) = (term178 n m p).
Proof. exact (EQ_MP (@lem522117 n m p) (@lem522116 n m p)). Qed.
Lemma lem523496 (n : nat) (d : nat) : (term176 n d) = (term179 n d).
Proof. exact (@lem523495 n term83 d). Qed.
Lemma lem523497 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem523498 (n : nat) (d : nat) : (term180 n d) = (term181 n d).
Proof. exact (MK_COMB (@lem523497) (@lem523496 n d)). Qed.
Lemma lem523499 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem523500 (n : nat) (d : nat) : (term175 n d) = (term183 n d).
Proof. exact (MK_COMB (@lem523498 n d) (@lem523499)). Qed.
Lemma lem523501 (n : nat) (d : nat) : (term174 n d) = (term183 n d).
Proof. exact (TRANS (@lem523493 n d) (@lem523500 n d)). Qed.
Lemma lem523502 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem523503 (n : nat) (d : nat) : (term184 n d) = (term185 n d).
Proof. exact (MK_COMB (@lem523502) (@lem523501 n d)). Qed.
Lemma lem523504 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem523505 (d : nat) (n : nat) : (term169 d n) = (term186 d n).
Proof. exact (MK_COMB (@lem523503 n d) (@lem523504 n)). Qed.
Lemma lem523506 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem523507 (d : nat) (n : nat) : (term187 d n) = (term188 d n).
Proof. exact (MK_COMB (@lem523506) (@lem523505 d n)). Qed.
Lemma lem523509 (m : nat) : (S m) = (term173 m).
Proof. exact (EQ_MP (@lem522120 m) (@lem522119 m)). Qed.
Lemma lem523510 (d : nat) (n : nat) : (term170 d n) = (term189 d n).
Proof. exact (@lem523509 (term190 d n)). Qed.
Lemma lem523512 (n : nat) (m : nat) (p : nat) : (term177 m n p) = (term178 n m p).
Proof. exact (EQ_MP (@lem522117 n m p) (@lem522116 n m p)). Qed.
Lemma lem523513 (n : nat) (d : nat) : (term176 n d) = (term179 n d).
Proof. exact (@lem523512 n term83 d). Qed.
Lemma lem523514 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem523515 (n : nat) (d : nat) : (term191 n d) = (term192 n d).
Proof. exact (MK_COMB (@lem523514) (@lem523513 n d)). Qed.
Lemma lem523516 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem523517 (d : nat) (n : nat) : (term190 d n) = (term193 d n).
Proof. exact (MK_COMB (@lem523515 n d) (@lem523516 n)). Qed.
Lemma lem523518 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem523519 (d : nat) (n : nat) : (term194 d n) = (term195 d n).
Proof. exact (MK_COMB (@lem523518) (@lem523517 d n)). Qed.
Lemma lem523520 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem523521 (d : nat) (n : nat) : (term189 d n) = (term196 d n).
Proof. exact (MK_COMB (@lem523519 d n) (@lem523520)). Qed.
Lemma lem523522 (d : nat) (n : nat) : (term170 d n) = (term196 d n).
Proof. exact (TRANS (@lem523510 d n) (@lem523521 d n)). Qed.
Lemma lem523523 (d : nat) (n : nat) : ((term169 d n) = (term170 d n)) = ((term186 d n) = (term196 d n)).
Proof. exact (MK_COMB (@lem523507 d n) (@lem523522 d n)). Qed.
Lemma lem523526 (d : nat) (n : nat) : ((term186 d n) = (term196 d n)) = ((term169 d n) = (term170 d n)).
Proof. exact (SYM (@lem523523 d n)). Qed.
Lemma lem523532 (m : nat) (n : nat) (p : nat) : (term197 m n p) = (term198 m n p).
Proof. exact (EQ_MP (@lem522102 m n p) (@lem522101 m n p)). Qed.
Lemma lem523533 (n : nat) (d : nat) : (term183 n d) = (term199 n d).
Proof. exact (@lem523532 (term76 n) (term76 d) term182). Qed.
Lemma lem523534 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem523535 (n : nat) (d : nat) : (term185 n d) = (term200 n d).
Proof. exact (MK_COMB (@lem523534) (@lem523533 n d)). Qed.
Lemma lem523536 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem523537 (d : nat) (n : nat) : (term186 d n) = (term201 d n).
Proof. exact (MK_COMB (@lem523535 n d) (@lem523536 n)). Qed.
Lemma lem523539 (m : nat) (n : nat) : (term202 n m) = n.
Proof. exact (EQ_MP (@lem522108 m n) (@lem522107 m n)). Qed.
Lemma lem523540 (n : nat) (d : nat) : (term201 d n) = (term203 d).
Proof. exact (@lem523539 (term76 n) (term203 d)). Qed.
Lemma lem523541 (n : nat) (d : nat) : (term186 d n) = (term203 d).
Proof. exact (TRANS (@lem523537 d n) (@lem523540 n d)). Qed.
Lemma lem523542 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem523543 (n : nat) (d : nat) : (term188 d n) = (term204 d).
Proof. exact (MK_COMB (@lem523542) (@lem523541 n d)). Qed.
Lemma lem523545 (m : nat) (n : nat) : (term202 n m) = n.
Proof. exact (EQ_MP (@lem522108 m n) (@lem522107 m n)). Qed.
Lemma lem523546 (n : nat) (d : nat) : (term193 d n) = (term76 d).
Proof. exact (@lem523545 (term76 n) (term76 d)). Qed.
Lemma lem523547 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem523548 (n : nat) (d : nat) : (term195 d n) = (term205 d).
Proof. exact (MK_COMB (@lem523547) (@lem523546 n d)). Qed.
Lemma lem523549 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem523550 (n : nat) (d : nat) : (term196 d n) = (term203 d).
Proof. exact (MK_COMB (@lem523548 n d) (@lem523549)). Qed.
Lemma lem523551 (n : nat) (d : nat) : ((term186 d n) = (term196 d n)) = ((term203 d) = (term203 d)).
Proof. exact (MK_COMB (@lem523543 n d) (@lem523550 n d)). Qed.
Lemma lem523553 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem523554 (x : nat) : (x = x) = True.
Proof. exact (@lem523553 nat x). Qed.
Lemma lem523555 (d : nat) : ((term203 d) = (term203 d)) = True.
Proof. exact (@lem523554 (term203 d)). Qed.
Lemma lem523556 (d : nat) (n : nat) : ((term186 d n) = (term196 d n)) = True.
Proof. exact (TRANS (@lem523551 n d) (@lem523555 d)). Qed.
Lemma lem523557 (d : nat) (n : nat) : True = ((term186 d n) = (term196 d n)).
Proof. exact (SYM (@lem523556 d n)). Qed.
Lemma lem523558 (d : nat) (n : nat) : (term186 d n) = (term196 d n).
Proof. exact (EQ_MP (@lem523557 d n) (@lem0)). Qed.
Lemma lem523559 (d : nat) (n : nat) : (term169 d n) = (term170 d n).
Proof. exact (EQ_MP (@lem523526 d n) (@lem523558 d n)). Qed.
Lemma lem523560 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term98 m n) = (term100 m n).
Proof. exact (EQ_MP (@lem523488 m n d h1) (@lem523559 d n)). Qed.
Lemma lem523562 (n : nat) (m : nat) (h1 : Peano.le n m) : (term98 m n) = (term100 m n).
Proof. exact (ex_elim (@lem523474 n m h1) (fun d : nat => fun h0 : term206 m n d => @lem523560 m n d h0)). Qed.
Lemma lem523563 (n : nat) (m : nat) (h1 : Peano.le n m) : (Peano.le n m) = ((term98 m n) = (term100 m n)).
Proof. exact (prop_ext (fun h2 : Peano.le n m => @lem523562 n m h1) (fun h2 : (term98 m n) = (term100 m n) => @lem523265 n m h1)). Qed.
Lemma lem523567 (n : nat) (m : nat) (h1 : term136 n m) : (term98 m n) = 0.
Proof. exact (EQ_MP (@lem523263 m n) (@lem523464 n m h1)). Qed.
Lemma lem523568 (n : nat) (m : nat) (h1 : term136 n m) : (term136 n m) = ((term98 m n) = 0).
Proof. exact (prop_ext (fun h2 : term136 n m => @lem523567 n m h1) (fun h2 : (term98 m n) = 0 => @lem523239 n m h1)). Qed.
Lemma lem523569 (n : nat) (m : nat) (h1 : term136 n m) : (term98 m n) = 0.
Proof. exact (EQ_MP (@lem523568 n m h1) (@lem523239 n m h1)). Qed.
Lemma lem523570 (m : nat) (n : nat) : term126 m n.
Proof. exact (fun h0 : term136 n m => @lem523569 n m h0). Qed.
Lemma lem523571 (n : nat) (m : nat) (h1 : Peano.le n m) : (term98 m n) = (term100 m n).
Proof. exact (EQ_MP (@lem523563 n m h1) (@lem523265 n m h1)). Qed.
Lemma lem523572 (n : nat) (m : nat) (h1 : Peano.le n m) : (Peano.le n m) = ((term98 m n) = (term100 m n)).
Proof. exact (prop_ext (fun h2 : Peano.le n m => @lem523571 n m h1) (fun h2 : (term98 m n) = (term100 m n) => @lem523222 n m h1)). Qed.
Lemma lem523573 (n : nat) (m : nat) (h1 : Peano.le n m) : (term98 m n) = (term100 m n).
Proof. exact (EQ_MP (@lem523572 n m h1) (@lem523222 n m h1)). Qed.
Lemma lem523574 (m : nat) (n : nat) : term130 m n.
Proof. exact (fun h0 : Peano.le n m => @lem523573 n m h0). Qed.
Lemma lem523575 (m : nat) (n : nat) : term133 m n.
Proof. exact (conj (@lem523574 m n) (@lem523570 m n)). Qed.
Lemma lem523576 (m : nat) (n : nat) : (term98 m n) = (term102 m n).
Proof. exact (EQ_MP (@lem523221 m n) (@lem523575 m n)). Qed.
Lemma lem523581 (m : nat) : term104 m.
Proof. exact (fun n : nat => @lem523576 m n). Qed.
Lemma lem523586 : term106.
Proof. exact (fun m : nat => @lem523581 m). Qed.
Lemma lem523587 : term110.
Proof. exact (EQ_MP (@lem523203) (@lem523586)). Qed.
Lemma lem523588 : term75.
Proof. exact (EQ_MP (@lem523134) (@lem523587)). Qed.
Lemma lem523589 : term74.
Proof. exact (EQ_MP (@lem522874) (@lem523588)). Qed.
