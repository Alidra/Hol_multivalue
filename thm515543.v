Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm515543_term_abbrevs.
Require Import ADD_AC_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm514292_spec.
Require Import thm514302_spec.
Require Import thm514303_spec.
Require Import thm514311_spec.
Require Import thm514312_spec.
Lemma lem514773 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem514774 (x : nat) : (x = x) = True.
Proof. exact (@lem514773 nat x). Qed.
Lemma lem514775 (m : nat) (n : nat) : ((Nat.mul m n) = (Nat.mul m n)) = True.
Proof. exact (@lem514774 (Nat.mul m n)). Qed.
Lemma lem514776 (m : nat) : (term0 m) = term1.
Proof. exact (fun_ext (fun n : nat => @lem514775 m n)). Qed.
Lemma lem514777 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514778 (m : nat) : (term2 m) = term3.
Proof. exact (MK_COMB (@lem514777) (@lem514776 m)). Qed.
Lemma lem514780 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem514781 (t : Prop) : (term5 t) = t.
Proof. exact (@lem514780 nat t). Qed.
Lemma lem514782 : term3 = True.
Proof. exact (@lem514781 True). Qed.
Lemma lem514783 (m : nat) : (term2 m) = True.
Proof. exact (TRANS (@lem514778 m) (@lem514782)). Qed.
Lemma lem514784 : term6 = term1.
Proof. exact (fun_ext (fun m : nat => @lem514783 m)). Qed.
Lemma lem514785 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514786 : term7 = term3.
Proof. exact (MK_COMB (@lem514785) (@lem514784)). Qed.
Lemma lem514788 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem514789 (t : Prop) : (term5 t) = t.
Proof. exact (@lem514788 nat t). Qed.
Lemma lem514790 : term3 = True.
Proof. exact (@lem514789 True). Qed.
Lemma lem514791 : term7 = True.
Proof. exact (TRANS (@lem514786) (@lem514790)). Qed.
Lemma lem514792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514793 : term8 = (and True).
Proof. exact (MK_COMB (@lem514792) (@lem514791)). Qed.
Lemma lem514797 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem514798 (x : nat) : (x = x) = True.
Proof. exact (@lem514797 nat x). Qed.
Lemma lem514799 : (0 = 0) = True.
Proof. exact (@lem514798 0). Qed.
Lemma lem514800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514801 : term9 = (and True).
Proof. exact (MK_COMB (@lem514800) (@lem514799)). Qed.
Lemma lem514805 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem514806 (t : Prop) : (term5 t) = t.
Proof. exact (@lem514805 nat t). Qed.
Lemma lem514807 : term10 = (0 = 0).
Proof. exact (@lem514806 (0 = 0)). Qed.
Lemma lem514809 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem514810 (x : nat) : (x = x) = True.
Proof. exact (@lem514809 nat x). Qed.
Lemma lem514811 : (0 = 0) = True.
Proof. exact (@lem514810 0). Qed.
Lemma lem514812 : term10 = True.
Proof. exact (TRANS (@lem514807) (@lem514811)). Qed.
Lemma lem514813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514814 : term11 = (and True).
Proof. exact (MK_COMB (@lem514813) (@lem514812)). Qed.
Lemma lem514818 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem514819 (t : Prop) : (term5 t) = t.
Proof. exact (@lem514818 nat t). Qed.
Lemma lem514820 : term10 = (0 = 0).
Proof. exact (@lem514819 (0 = 0)). Qed.
Lemma lem514822 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem514823 (x : nat) : (x = x) = True.
Proof. exact (@lem514822 nat x). Qed.
Lemma lem514824 : (0 = 0) = True.
Proof. exact (@lem514823 0). Qed.
Lemma lem514825 : term10 = True.
Proof. exact (TRANS (@lem514820) (@lem514824)). Qed.
Lemma lem514826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514827 : term11 = (and True).
Proof. exact (MK_COMB (@lem514826) (@lem514825)). Qed.
Lemma lem514831 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem514832 (t : Prop) : (term5 t) = t.
Proof. exact (@lem514831 nat t). Qed.
Lemma lem514833 : term10 = (0 = 0).
Proof. exact (@lem514832 (0 = 0)). Qed.
Lemma lem514835 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem514836 (x : nat) : (x = x) = True.
Proof. exact (@lem514835 nat x). Qed.
Lemma lem514837 : (0 = 0) = True.
Proof. exact (@lem514836 0). Qed.
Lemma lem514838 : term10 = True.
Proof. exact (TRANS (@lem514833) (@lem514837)). Qed.
Lemma lem514839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514840 : term11 = (and True).
Proof. exact (MK_COMB (@lem514839) (@lem514838)). Qed.
Lemma lem514844 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem514845 (t : Prop) : (term5 t) = t.
Proof. exact (@lem514844 nat t). Qed.
Lemma lem514846 : term10 = (0 = 0).
Proof. exact (@lem514845 (0 = 0)). Qed.
Lemma lem514848 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem514849 (x : nat) : (x = x) = True.
Proof. exact (@lem514848 nat x). Qed.
Lemma lem514850 : (0 = 0) = True.
Proof. exact (@lem514849 0). Qed.
Lemma lem514851 : term10 = True.
Proof. exact (TRANS (@lem514846) (@lem514850)). Qed.
Lemma lem514852 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514853 : term11 = (and True).
Proof. exact (MK_COMB (@lem514852) (@lem514851)). Qed.
Lemma lem514867 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term13 m n p).
Proof. exact (EQ_MP (@lem514303 m n p) (@lem514302 m n p)). Qed.
Lemma lem514868 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (@lem514867 m m (Nat.add n n)). Qed.
Lemma lem514873 (n : nat) (m : nat) (p : nat) : (term16 m n p) = (term17 n m p).
Proof. exact (EQ_MP (@lem514312 n m p) (@lem514311 n m p)). Qed.
Lemma lem514874 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (@lem514873 n m n). Qed.
Lemma lem514878 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem514879 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem514878) (@lem514874 m n)). Qed.
Lemma lem514881 (n : nat) (m : nat) (p : nat) : (term16 m n p) = (term17 n m p).
Proof. exact (EQ_MP (@lem514312 n m p) (@lem514311 n m p)). Qed.
Lemma lem514882 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (@lem514881 n m n). Qed.
Lemma lem514886 (m : nat) (n : nat) : (term15 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem514879 m n) (@lem514882 m n)). Qed.
Lemma lem514888 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem514889 (m : nat) (n : nat) : (term22 m n) = (term25 m n).
Proof. exact (@lem514888 (Nat.mul m n) (Nat.mul m n) (term19 m n)). Qed.
Lemma lem514905 (m : nat) (n : nat) : (term15 m n) = (term25 m n).
Proof. exact (TRANS (@lem514886 m n) (@lem514889 m n)). Qed.
Lemma lem514906 (m : nat) (n : nat) : (term14 m n) = (term25 m n).
Proof. exact (TRANS (@lem514868 m n) (@lem514905 m n)). Qed.
Lemma lem514907 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514908 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (MK_COMB (@lem514907) (@lem514906 m n)). Qed.
Lemma lem514910 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem514911 (m : nat) (n : nat) : (term22 m n) = (term25 m n).
Proof. exact (@lem514910 (Nat.mul m n) (Nat.mul m n) (term19 m n)). Qed.
Lemma lem514927 (m : nat) (n : nat) : ((term14 m n) = (term22 m n)) = ((term25 m n) = (term25 m n)).
Proof. exact (MK_COMB (@lem514908 m n) (@lem514911 m n)). Qed.
Lemma lem514929 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem514930 (x : nat) : (x = x) = True.
Proof. exact (@lem514929 nat x). Qed.
Lemma lem514931 (m : nat) (n : nat) : ((term25 m n) = (term25 m n)) = True.
Proof. exact (@lem514930 (term25 m n)). Qed.
Lemma lem514932 (m : nat) (n : nat) : ((term14 m n) = (term22 m n)) = True.
Proof. exact (TRANS (@lem514927 m n) (@lem514931 m n)). Qed.
Lemma lem514933 (m : nat) : (term28 m) = term1.
Proof. exact (fun_ext (fun n : nat => @lem514932 m n)). Qed.
Lemma lem514934 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514935 (m : nat) : (term29 m) = term3.
Proof. exact (MK_COMB (@lem514934) (@lem514933 m)). Qed.
Lemma lem514937 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem514938 (t : Prop) : (term5 t) = t.
Proof. exact (@lem514937 nat t). Qed.
Lemma lem514939 : term3 = True.
Proof. exact (@lem514938 True). Qed.
Lemma lem514940 (m : nat) : (term29 m) = True.
Proof. exact (TRANS (@lem514935 m) (@lem514939)). Qed.
Lemma lem514941 : term30 = term1.
Proof. exact (fun_ext (fun m : nat => @lem514940 m)). Qed.
Lemma lem514942 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514943 : term31 = term3.
Proof. exact (MK_COMB (@lem514942) (@lem514941)). Qed.
Lemma lem514945 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem514946 (t : Prop) : (term5 t) = t.
Proof. exact (@lem514945 nat t). Qed.
Lemma lem514947 : term3 = True.
Proof. exact (@lem514946 True). Qed.
Lemma lem514948 : term31 = True.
Proof. exact (TRANS (@lem514943) (@lem514947)). Qed.
Lemma lem514949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514950 : term32 = (and True).
Proof. exact (MK_COMB (@lem514949) (@lem514948)). Qed.
Lemma lem514964 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem514965 (m : nat) (n : nat) : (term33 m n) = (term34 m n).
Proof. exact (@lem514964 m m (term14 m n)). Qed.
Lemma lem514976 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term13 m n p).
Proof. exact (EQ_MP (@lem514303 m n p) (@lem514302 m n p)). Qed.
Lemma lem514977 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (@lem514976 m m (Nat.add n n)). Qed.
Lemma lem514982 (n : nat) (m : nat) (p : nat) : (term16 m n p) = (term17 n m p).
Proof. exact (EQ_MP (@lem514312 n m p) (@lem514311 n m p)). Qed.
Lemma lem514983 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (@lem514982 n m n). Qed.
Lemma lem514987 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem514988 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem514987) (@lem514983 m n)). Qed.
Lemma lem514990 (n : nat) (m : nat) (p : nat) : (term16 m n p) = (term17 n m p).
Proof. exact (EQ_MP (@lem514312 n m p) (@lem514311 n m p)). Qed.
Lemma lem514991 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (@lem514990 n m n). Qed.
Lemma lem514995 (m : nat) (n : nat) : (term15 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem514988 m n) (@lem514991 m n)). Qed.
Lemma lem514997 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem514998 (m : nat) (n : nat) : (term22 m n) = (term25 m n).
Proof. exact (@lem514997 (Nat.mul m n) (Nat.mul m n) (term19 m n)). Qed.
Lemma lem515014 (m : nat) (n : nat) : (term15 m n) = (term25 m n).
Proof. exact (TRANS (@lem514995 m n) (@lem514998 m n)). Qed.
Lemma lem515015 (m : nat) (n : nat) : (term14 m n) = (term25 m n).
Proof. exact (TRANS (@lem514977 m n) (@lem515014 m n)). Qed.
Lemma lem515016 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem515017 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem515016 m) (@lem515015 m n)). Qed.
Lemma lem515024 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem515025 (m : nat) (n : nat) : (term34 m n) = (term37 m n).
Proof. exact (MK_COMB (@lem515024 m) (@lem515017 m n)). Qed.
Lemma lem515032 (m : nat) (n : nat) : (term33 m n) = (term37 m n).
Proof. exact (TRANS (@lem514965 m n) (@lem515025 m n)). Qed.
Lemma lem515033 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515034 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (MK_COMB (@lem515033) (@lem515032 m n)). Qed.
Lemma lem515036 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem515037 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (@lem515036 m m (term22 m n)). Qed.
Lemma lem515051 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem515052 (m : nat) (n : nat) : (term22 m n) = (term25 m n).
Proof. exact (@lem515051 (Nat.mul m n) (Nat.mul m n) (term19 m n)). Qed.
Lemma lem515068 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem515069 (m : nat) (n : nat) : (term42 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem515068 m) (@lem515052 m n)). Qed.
Lemma lem515076 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem515077 (m : nat) (n : nat) : (term41 m n) = (term37 m n).
Proof. exact (MK_COMB (@lem515076 m) (@lem515069 m n)). Qed.
Lemma lem515084 (m : nat) (n : nat) : (term40 m n) = (term37 m n).
Proof. exact (TRANS (@lem515037 m n) (@lem515077 m n)). Qed.
Lemma lem515085 (m : nat) (n : nat) : ((term33 m n) = (term40 m n)) = ((term37 m n) = (term37 m n)).
Proof. exact (MK_COMB (@lem515034 m n) (@lem515084 m n)). Qed.
Lemma lem515087 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem515088 (x : nat) : (x = x) = True.
Proof. exact (@lem515087 nat x). Qed.
Lemma lem515089 (m : nat) (n : nat) : ((term37 m n) = (term37 m n)) = True.
Proof. exact (@lem515088 (term37 m n)). Qed.
Lemma lem515090 (m : nat) (n : nat) : ((term33 m n) = (term40 m n)) = True.
Proof. exact (TRANS (@lem515085 m n) (@lem515089 m n)). Qed.
Lemma lem515091 (m : nat) : (term43 m) = term1.
Proof. exact (fun_ext (fun n : nat => @lem515090 m n)). Qed.
Lemma lem515092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem515093 (m : nat) : (term44 m) = term3.
Proof. exact (MK_COMB (@lem515092) (@lem515091 m)). Qed.
Lemma lem515095 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem515096 (t : Prop) : (term5 t) = t.
Proof. exact (@lem515095 nat t). Qed.
Lemma lem515097 : term3 = True.
Proof. exact (@lem515096 True). Qed.
Lemma lem515098 (m : nat) : (term44 m) = True.
Proof. exact (TRANS (@lem515093 m) (@lem515097)). Qed.
Lemma lem515099 : term45 = term1.
Proof. exact (fun_ext (fun m : nat => @lem515098 m)). Qed.
Lemma lem515100 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem515101 : term46 = term3.
Proof. exact (MK_COMB (@lem515100) (@lem515099)). Qed.
Lemma lem515103 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem515104 (t : Prop) : (term5 t) = t.
Proof. exact (@lem515103 nat t). Qed.
Lemma lem515105 : term3 = True.
Proof. exact (@lem515104 True). Qed.
Lemma lem515106 : term46 = True.
Proof. exact (TRANS (@lem515101) (@lem515105)). Qed.
Lemma lem515107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem515108 : term47 = (and True).
Proof. exact (MK_COMB (@lem515107) (@lem515106)). Qed.
Lemma lem515122 (n : nat) (m : nat) (p : nat) : (term24 m n p) = (term24 n m p).
Proof. exact (proj2 (@lem514292 n m p)). Qed.
Lemma lem515123 (m : nat) (n : nat) : (term48 m n) = (term49 m n).
Proof. exact (@lem515122 n (term14 m n) n). Qed.
Lemma lem515131 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem515132 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (@lem515131 n (term14 m n)). Qed.
Lemma lem515137 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term13 m n p).
Proof. exact (EQ_MP (@lem514303 m n p) (@lem514302 m n p)). Qed.
Lemma lem515138 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (@lem515137 m m (Nat.add n n)). Qed.
Lemma lem515143 (n : nat) (m : nat) (p : nat) : (term16 m n p) = (term17 n m p).
Proof. exact (EQ_MP (@lem514312 n m p) (@lem514311 n m p)). Qed.
Lemma lem515144 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (@lem515143 n m n). Qed.
Lemma lem515148 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem515149 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem515148) (@lem515144 m n)). Qed.
Lemma lem515151 (n : nat) (m : nat) (p : nat) : (term16 m n p) = (term17 n m p).
Proof. exact (EQ_MP (@lem514312 n m p) (@lem514311 n m p)). Qed.
Lemma lem515152 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (@lem515151 n m n). Qed.
Lemma lem515156 (m : nat) (n : nat) : (term15 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem515149 m n) (@lem515152 m n)). Qed.
Lemma lem515158 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem515159 (m : nat) (n : nat) : (term22 m n) = (term25 m n).
Proof. exact (@lem515158 (Nat.mul m n) (Nat.mul m n) (term19 m n)). Qed.
Lemma lem515175 (m : nat) (n : nat) : (term15 m n) = (term25 m n).
Proof. exact (TRANS (@lem515156 m n) (@lem515159 m n)). Qed.
Lemma lem515176 (m : nat) (n : nat) : (term14 m n) = (term25 m n).
Proof. exact (TRANS (@lem515138 m n) (@lem515175 m n)). Qed.
Lemma lem515177 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem515178 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (MK_COMB (@lem515177 n) (@lem515176 m n)). Qed.
Lemma lem515185 (m : nat) (n : nat) : (term50 m n) = (term52 m n).
Proof. exact (TRANS (@lem515132 m n) (@lem515178 m n)). Qed.
Lemma lem515186 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem515187 (m : nat) (n : nat) : (term49 m n) = (term53 m n).
Proof. exact (MK_COMB (@lem515186 n) (@lem515185 m n)). Qed.
Lemma lem515194 (m : nat) (n : nat) : (term48 m n) = (term53 m n).
Proof. exact (TRANS (@lem515123 m n) (@lem515187 m n)). Qed.
Lemma lem515195 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515196 (m : nat) (n : nat) : (term54 m n) = (term55 m n).
Proof. exact (MK_COMB (@lem515195) (@lem515194 m n)). Qed.
Lemma lem515198 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem515199 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (@lem515198 n n (term22 m n)). Qed.
Lemma lem515213 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem515214 (m : nat) (n : nat) : (term22 m n) = (term25 m n).
Proof. exact (@lem515213 (Nat.mul m n) (Nat.mul m n) (term19 m n)). Qed.
Lemma lem515230 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem515231 (m : nat) (n : nat) : (term58 m n) = (term52 m n).
Proof. exact (MK_COMB (@lem515230 n) (@lem515214 m n)). Qed.
Lemma lem515238 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem515239 (m : nat) (n : nat) : (term57 m n) = (term53 m n).
Proof. exact (MK_COMB (@lem515238 n) (@lem515231 m n)). Qed.
Lemma lem515246 (m : nat) (n : nat) : (term56 m n) = (term53 m n).
Proof. exact (TRANS (@lem515199 m n) (@lem515239 m n)). Qed.
Lemma lem515247 (m : nat) (n : nat) : ((term48 m n) = (term56 m n)) = ((term53 m n) = (term53 m n)).
Proof. exact (MK_COMB (@lem515196 m n) (@lem515246 m n)). Qed.
Lemma lem515249 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem515250 (x : nat) : (x = x) = True.
Proof. exact (@lem515249 nat x). Qed.
Lemma lem515251 (m : nat) (n : nat) : ((term53 m n) = (term53 m n)) = True.
Proof. exact (@lem515250 (term53 m n)). Qed.
Lemma lem515252 (m : nat) (n : nat) : ((term48 m n) = (term56 m n)) = True.
Proof. exact (TRANS (@lem515247 m n) (@lem515251 m n)). Qed.
Lemma lem515253 (m : nat) : (term59 m) = term1.
Proof. exact (fun_ext (fun n : nat => @lem515252 m n)). Qed.
Lemma lem515254 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem515255 (m : nat) : (term60 m) = term3.
Proof. exact (MK_COMB (@lem515254) (@lem515253 m)). Qed.
Lemma lem515257 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem515258 (t : Prop) : (term5 t) = t.
Proof. exact (@lem515257 nat t). Qed.
Lemma lem515259 : term3 = True.
Proof. exact (@lem515258 True). Qed.
Lemma lem515260 (m : nat) : (term60 m) = True.
Proof. exact (TRANS (@lem515255 m) (@lem515259)). Qed.
Lemma lem515261 : term61 = term1.
Proof. exact (fun_ext (fun m : nat => @lem515260 m)). Qed.
Lemma lem515262 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem515263 : term62 = term3.
Proof. exact (MK_COMB (@lem515262) (@lem515261)). Qed.
Lemma lem515265 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem515266 (t : Prop) : (term5 t) = t.
Proof. exact (@lem515265 nat t). Qed.
Lemma lem515267 : term3 = True.
Proof. exact (@lem515266 True). Qed.
Lemma lem515268 : term62 = True.
Proof. exact (TRANS (@lem515263) (@lem515267)). Qed.
Lemma lem515269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem515270 : term63 = (and True).
Proof. exact (MK_COMB (@lem515269) (@lem515268)). Qed.
Lemma lem515282 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem515283 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (@lem515282 (Nat.add m m) (term14 m n) (Nat.add n n)). Qed.
Lemma lem515285 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem515286 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (@lem515285 m m (term48 m n)). Qed.
Lemma lem515293 (m : nat) (n : nat) : (term64 m n) = (term66 m n).
Proof. exact (TRANS (@lem515283 m n) (@lem515286 m n)). Qed.
Lemma lem515301 (n : nat) (m : nat) (p : nat) : (term24 m n p) = (term24 n m p).
Proof. exact (proj2 (@lem514292 n m p)). Qed.
Lemma lem515302 (m : nat) (n : nat) : (term48 m n) = (term49 m n).
Proof. exact (@lem515301 n (term14 m n) n). Qed.
Lemma lem515310 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem515311 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (@lem515310 n (term14 m n)). Qed.
Lemma lem515316 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term13 m n p).
Proof. exact (EQ_MP (@lem514303 m n p) (@lem514302 m n p)). Qed.
Lemma lem515317 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (@lem515316 m m (Nat.add n n)). Qed.
Lemma lem515322 (n : nat) (m : nat) (p : nat) : (term16 m n p) = (term17 n m p).
Proof. exact (EQ_MP (@lem514312 n m p) (@lem514311 n m p)). Qed.
Lemma lem515323 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (@lem515322 n m n). Qed.
Lemma lem515327 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem515328 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem515327) (@lem515323 m n)). Qed.
Lemma lem515330 (n : nat) (m : nat) (p : nat) : (term16 m n p) = (term17 n m p).
Proof. exact (EQ_MP (@lem514312 n m p) (@lem514311 n m p)). Qed.
Lemma lem515331 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (@lem515330 n m n). Qed.
Lemma lem515335 (m : nat) (n : nat) : (term15 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem515328 m n) (@lem515331 m n)). Qed.
Lemma lem515337 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem515338 (m : nat) (n : nat) : (term22 m n) = (term25 m n).
Proof. exact (@lem515337 (Nat.mul m n) (Nat.mul m n) (term19 m n)). Qed.
Lemma lem515354 (m : nat) (n : nat) : (term15 m n) = (term25 m n).
Proof. exact (TRANS (@lem515335 m n) (@lem515338 m n)). Qed.
Lemma lem515355 (m : nat) (n : nat) : (term14 m n) = (term25 m n).
Proof. exact (TRANS (@lem515317 m n) (@lem515354 m n)). Qed.
Lemma lem515356 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem515357 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (MK_COMB (@lem515356 n) (@lem515355 m n)). Qed.
Lemma lem515364 (m : nat) (n : nat) : (term50 m n) = (term52 m n).
Proof. exact (TRANS (@lem515311 m n) (@lem515357 m n)). Qed.
Lemma lem515365 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem515366 (m : nat) (n : nat) : (term49 m n) = (term53 m n).
Proof. exact (MK_COMB (@lem515365 n) (@lem515364 m n)). Qed.
Lemma lem515373 (m : nat) (n : nat) : (term48 m n) = (term53 m n).
Proof. exact (TRANS (@lem515302 m n) (@lem515366 m n)). Qed.
Lemma lem515374 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem515375 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (MK_COMB (@lem515374 m) (@lem515373 m n)). Qed.
Lemma lem515382 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem515383 (m : nat) (n : nat) : (term66 m n) = (term69 m n).
Proof. exact (MK_COMB (@lem515382 m) (@lem515375 m n)). Qed.
Lemma lem515390 (m : nat) (n : nat) : (term64 m n) = (term69 m n).
Proof. exact (TRANS (@lem515293 m n) (@lem515383 m n)). Qed.
Lemma lem515391 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515392 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem515391) (@lem515390 m n)). Qed.
Lemma lem515394 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem515395 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (@lem515394 m m (term56 m n)). Qed.
Lemma lem515409 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem515410 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (@lem515409 n n (term22 m n)). Qed.
Lemma lem515424 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term24 m n p).
Proof. exact (proj1 (@lem514292 n m p)). Qed.
Lemma lem515425 (m : nat) (n : nat) : (term22 m n) = (term25 m n).
Proof. exact (@lem515424 (Nat.mul m n) (Nat.mul m n) (term19 m n)). Qed.
Lemma lem515441 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem515442 (m : nat) (n : nat) : (term58 m n) = (term52 m n).
Proof. exact (MK_COMB (@lem515441 n) (@lem515425 m n)). Qed.
Lemma lem515449 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem515450 (m : nat) (n : nat) : (term57 m n) = (term53 m n).
Proof. exact (MK_COMB (@lem515449 n) (@lem515442 m n)). Qed.
Lemma lem515457 (m : nat) (n : nat) : (term56 m n) = (term53 m n).
Proof. exact (TRANS (@lem515410 m n) (@lem515450 m n)). Qed.
Lemma lem515458 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem515459 (m : nat) (n : nat) : (term74 m n) = (term68 m n).
Proof. exact (MK_COMB (@lem515458 m) (@lem515457 m n)). Qed.
Lemma lem515466 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem515467 (m : nat) (n : nat) : (term73 m n) = (term69 m n).
Proof. exact (MK_COMB (@lem515466 m) (@lem515459 m n)). Qed.
Lemma lem515474 (m : nat) (n : nat) : (term72 m n) = (term69 m n).
Proof. exact (TRANS (@lem515395 m n) (@lem515467 m n)). Qed.
Lemma lem515475 (m : nat) (n : nat) : ((term64 m n) = (term72 m n)) = ((term69 m n) = (term69 m n)).
Proof. exact (MK_COMB (@lem515392 m n) (@lem515474 m n)). Qed.
Lemma lem515477 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem515478 (x : nat) : (x = x) = True.
Proof. exact (@lem515477 nat x). Qed.
Lemma lem515479 (m : nat) (n : nat) : ((term69 m n) = (term69 m n)) = True.
Proof. exact (@lem515478 (term69 m n)). Qed.
Lemma lem515480 (m : nat) (n : nat) : ((term64 m n) = (term72 m n)) = True.
Proof. exact (TRANS (@lem515475 m n) (@lem515479 m n)). Qed.
Lemma lem515481 (m : nat) : (term75 m) = term1.
Proof. exact (fun_ext (fun n : nat => @lem515480 m n)). Qed.
Lemma lem515482 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem515483 (m : nat) : (term76 m) = term3.
Proof. exact (MK_COMB (@lem515482) (@lem515481 m)). Qed.
Lemma lem515485 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem515486 (t : Prop) : (term5 t) = t.
Proof. exact (@lem515485 nat t). Qed.
Lemma lem515487 : term3 = True.
Proof. exact (@lem515486 True). Qed.
Lemma lem515488 (m : nat) : (term76 m) = True.
Proof. exact (TRANS (@lem515483 m) (@lem515487)). Qed.
Lemma lem515489 : term77 = term1.
Proof. exact (fun_ext (fun m : nat => @lem515488 m)). Qed.
Lemma lem515490 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem515491 : term78 = term3.
Proof. exact (MK_COMB (@lem515490) (@lem515489)). Qed.
Lemma lem515493 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem515494 (t : Prop) : (term5 t) = t.
Proof. exact (@lem515493 nat t). Qed.
Lemma lem515495 : term3 = True.
Proof. exact (@lem515494 True). Qed.
Lemma lem515496 : term78 = True.
Proof. exact (TRANS (@lem515491) (@lem515495)). Qed.
Lemma lem515497 : term79 = (True /\ True).
Proof. exact (MK_COMB (@lem515270) (@lem515496)). Qed.
Lemma lem515499 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem515500 : (True /\ True) = True.
Proof. exact (@lem515499 True). Qed.
Lemma lem515501 : term79 = True.
Proof. exact (TRANS (@lem515497) (@lem515500)). Qed.
Lemma lem515502 : term80 = (True /\ True).
Proof. exact (MK_COMB (@lem515108) (@lem515501)). Qed.
Lemma lem515504 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem515505 : (True /\ True) = True.
Proof. exact (@lem515504 True). Qed.
Lemma lem515506 : term80 = True.
Proof. exact (TRANS (@lem515502) (@lem515505)). Qed.
Lemma lem515507 : term81 = (True /\ True).
Proof. exact (MK_COMB (@lem514950) (@lem515506)). Qed.
Lemma lem515509 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem515510 : (True /\ True) = True.
Proof. exact (@lem515509 True). Qed.
Lemma lem515511 : term81 = True.
Proof. exact (TRANS (@lem515507) (@lem515510)). Qed.
Lemma lem515512 : term82 = (True /\ True).
Proof. exact (MK_COMB (@lem514853) (@lem515511)). Qed.
Lemma lem515514 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem515515 : (True /\ True) = True.
Proof. exact (@lem515514 True). Qed.
Lemma lem515516 : term82 = True.
Proof. exact (TRANS (@lem515512) (@lem515515)). Qed.
Lemma lem515517 : term83 = (True /\ True).
Proof. exact (MK_COMB (@lem514840) (@lem515516)). Qed.
Lemma lem515519 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem515520 : (True /\ True) = True.
Proof. exact (@lem515519 True). Qed.
Lemma lem515521 : term83 = True.
Proof. exact (TRANS (@lem515517) (@lem515520)). Qed.
Lemma lem515522 : term84 = (True /\ True).
Proof. exact (MK_COMB (@lem514827) (@lem515521)). Qed.
Lemma lem515524 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem515525 : (True /\ True) = True.
Proof. exact (@lem515524 True). Qed.
Lemma lem515526 : term84 = True.
Proof. exact (TRANS (@lem515522) (@lem515525)). Qed.
Lemma lem515527 : term85 = (True /\ True).
Proof. exact (MK_COMB (@lem514814) (@lem515526)). Qed.
Lemma lem515529 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem515530 : (True /\ True) = True.
Proof. exact (@lem515529 True). Qed.
Lemma lem515531 : term85 = True.
Proof. exact (TRANS (@lem515527) (@lem515530)). Qed.
Lemma lem515532 : term86 = (True /\ True).
Proof. exact (MK_COMB (@lem514801) (@lem515531)). Qed.
Lemma lem515534 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem515535 : (True /\ True) = True.
Proof. exact (@lem515534 True). Qed.
Lemma lem515536 : term86 = True.
Proof. exact (TRANS (@lem515532) (@lem515535)). Qed.
Lemma lem515537 : term87 = (True /\ True).
Proof. exact (MK_COMB (@lem514793) (@lem515536)). Qed.
Lemma lem515539 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem515540 : (True /\ True) = True.
Proof. exact (@lem515539 True). Qed.
Lemma lem515541 : term87 = True.
Proof. exact (TRANS (@lem515537) (@lem515540)). Qed.
Lemma lem515542 : True = term87.
Proof. exact (SYM (@lem515541)). Qed.
Lemma lem515543 : term87.
Proof. exact (EQ_MP (@lem515542) (@lem0)). Qed.
