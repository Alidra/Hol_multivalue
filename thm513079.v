Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm513079_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import BIT0_spec.
Require Import BIT1_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Require Import thm75543_spec.
Lemma lem512872 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem512873 : (NUMERAL 0) = 0.
Proof. exact (@lem512872 0). Qed.
Lemma lem512874 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem512875 : term0 = (Nat.add 0).
Proof. exact (MK_COMB (@lem512874) (@lem512873)). Qed.
Lemma lem512876 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem512877 (n : nat) : (term1 n) = (Nat.add 0 n).
Proof. exact (MK_COMB (@lem512875) (@lem512876 n)). Qed.
Lemma lem512878 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem512879 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem512878) (@lem512877 n)). Qed.
Lemma lem512880 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem512881 (n : nat) : ((term1 n) = n) = ((Nat.add 0 n) = n).
Proof. exact (MK_COMB (@lem512879 n) (@lem512880 n)). Qed.
Lemma lem512882 : term4 = term5.
Proof. exact (fun_ext (fun n : nat => @lem512881 n)). Qed.
Lemma lem512883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem512884 : term6 = term7.
Proof. exact (MK_COMB (@lem512883) (@lem512882)). Qed.
Lemma lem512885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem512886 : term8 = term9.
Proof. exact (MK_COMB (@lem512885) (@lem512884)). Qed.
Lemma lem512888 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem512889 : (NUMERAL 0) = 0.
Proof. exact (@lem512888 0). Qed.
Lemma lem512890 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem512891 (m : nat) : (term10 m) = (Nat.add m 0).
Proof. exact (MK_COMB (@lem512890 m) (@lem512889)). Qed.
Lemma lem512892 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem512893 (m : nat) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem512892) (@lem512891 m)). Qed.
Lemma lem512894 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem512895 (m : nat) : ((term10 m) = m) = ((Nat.add m 0) = m).
Proof. exact (MK_COMB (@lem512893 m) (@lem512894 m)). Qed.
Lemma lem512896 : term13 = term14.
Proof. exact (fun_ext (fun m : nat => @lem512895 m)). Qed.
Lemma lem512897 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem512898 : term15 = term16.
Proof. exact (MK_COMB (@lem512897) (@lem512896)). Qed.
Lemma lem512899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem512900 : term17 = term18.
Proof. exact (MK_COMB (@lem512899) (@lem512898)). Qed.
Lemma lem512901 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem512902 : term20 = term21.
Proof. exact (MK_COMB (@lem512900) (@lem512901)). Qed.
Lemma lem512903 : term22 = term23.
Proof. exact (MK_COMB (@lem512886) (@lem512902)). Qed.
Lemma lem512904 : term23.
Proof. exact (EQ_MP (@lem512903) (@lem77629)). Qed.
Lemma lem512905 : term21.
Proof. exact (proj2 (@lem512904)). Qed.
Lemma lem512906 : term19.
Proof. exact (proj2 (@lem512905)). Qed.
Lemma lem512907 : term24.
Proof. exact (proj2 (@lem512906)). Qed.
Lemma lem512908 (m : nat) : term25 m.
Proof. exact (@lem512907 m). Qed.
Lemma lem512909 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem512910 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem512909 m) (@lem512908 m)). Qed.
Lemma lem512911 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem512910 m n). Qed.
Lemma lem512912 (m : nat) (n : nat) : (term27 m n) = ((term28 m n) = (term29 m n)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem512914 : term30.
Proof. exact (proj1 (@lem512906)). Qed.
Lemma lem512915 (m : nat) : term31 m.
Proof. exact (@lem512914 m). Qed.
Lemma lem512916 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem512917 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem512916 m) (@lem512915 m)). Qed.
Lemma lem512918 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem512917 m n). Qed.
Lemma lem512919 (m : nat) (n : nat) : (term33 m n) = ((term34 m n) = (term29 m n)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem512925 : term7.
Proof. exact (proj1 (@lem512904)). Qed.
Lemma lem512926 (n : nat) : term35 n.
Proof. exact (@lem512925 n). Qed.
Lemma lem512927 (n : nat) : (term35 n) = ((Nat.add 0 n) = n).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem512929 (n : nat) : term36 n.
Proof. exact (@lem80122 n). Qed.
Lemma lem512930 (n : nat) : (term36 n) = ((BIT1 n) = (term37 n)).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem512932 (n : nat) : term38 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem512933 (n : nat) : (term38 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term38 n)). Qed.
Lemma lem512935 (n : nat) : term39 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem512936 (n : nat) : (term39 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem512947 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512936 n) (@lem512935 n)). Qed.
Lemma lem512948 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem512949 (n : nat) : (term40 n) = (S n).
Proof. exact (MK_COMB (@lem512948) (@lem512947 n)). Qed.
Lemma lem512950 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem512951 (n : nat) : (term41 n) = (term42 n).
Proof. exact (MK_COMB (@lem512950) (@lem512949 n)). Qed.
Lemma lem512953 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512936 n) (@lem512935 n)). Qed.
Lemma lem512954 (n : nat) : (term43 n) = (S n).
Proof. exact (@lem512953 (S n)). Qed.
Lemma lem512955 (n : nat) : ((term40 n) = (term43 n)) = ((S n) = (S n)).
Proof. exact (MK_COMB (@lem512951 n) (@lem512954 n)). Qed.
Lemma lem512957 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem512958 (x : nat) : (x = x) = True.
Proof. exact (@lem512957 nat x). Qed.
Lemma lem512959 (n : nat) : ((S n) = (S n)) = True.
Proof. exact (@lem512958 (S n)). Qed.
Lemma lem512960 (n : nat) : ((term40 n) = (term43 n)) = True.
Proof. exact (TRANS (@lem512955 n) (@lem512959 n)). Qed.
Lemma lem512961 : term44 = term45.
Proof. exact (fun_ext (fun n : nat => @lem512960 n)). Qed.
Lemma lem512962 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem512963 : term46 = term47.
Proof. exact (MK_COMB (@lem512962) (@lem512961)). Qed.
Lemma lem512965 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem512966 (t : Prop) : (term49 t) = t.
Proof. exact (@lem512965 nat t). Qed.
Lemma lem512967 : term47 = True.
Proof. exact (@lem512966 True). Qed.
Lemma lem512968 : term46 = True.
Proof. exact (TRANS (@lem512963) (@lem512967)). Qed.
Lemma lem512969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem512970 : term50 = (and True).
Proof. exact (MK_COMB (@lem512969) (@lem512968)). Qed.
Lemma lem512976 (n : nat) : (BIT1 n) = (term37 n).
Proof. exact (EQ_MP (@lem512930 n) (@lem512929 n)). Qed.
Lemma lem512977 : (BIT1 0) = term51.
Proof. exact (@lem512976 0). Qed.
Lemma lem512979 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem512927 n) (@lem512926 n)). Qed.
Lemma lem512980 : (Nat.add 0 0) = 0.
Proof. exact (@lem512979 0). Qed.
Lemma lem512981 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem512982 : term51 = (S 0).
Proof. exact (MK_COMB (@lem512981) (@lem512980)). Qed.
Lemma lem512983 : (BIT1 0) = (S 0).
Proof. exact (TRANS (@lem512977) (@lem512982)). Qed.
Lemma lem512984 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem512985 : ((S 0) = (BIT1 0)) = ((S 0) = (S 0)).
Proof. exact (MK_COMB (@lem512984) (@lem512983)). Qed.
Lemma lem512987 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem512988 (x : nat) : (x = x) = True.
Proof. exact (@lem512987 nat x). Qed.
Lemma lem512989 : ((S 0) = (S 0)) = True.
Proof. exact (@lem512988 (S 0)). Qed.
Lemma lem512990 : ((S 0) = (BIT1 0)) = True.
Proof. exact (TRANS (@lem512985) (@lem512989)). Qed.
Lemma lem512991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem512992 : term53 = (and True).
Proof. exact (MK_COMB (@lem512991) (@lem512990)). Qed.
Lemma lem513002 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem512933 n) (@lem512932 n)). Qed.
Lemma lem513003 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem513004 (n : nat) : (term54 n) = (term37 n).
Proof. exact (MK_COMB (@lem513003) (@lem513002 n)). Qed.
Lemma lem513005 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513006 (n : nat) : (term55 n) = (term56 n).
Proof. exact (MK_COMB (@lem513005) (@lem513004 n)). Qed.
Lemma lem513008 (n : nat) : (BIT1 n) = (term37 n).
Proof. exact (EQ_MP (@lem512930 n) (@lem512929 n)). Qed.
Lemma lem513009 (n : nat) : ((term54 n) = (BIT1 n)) = ((term37 n) = (term37 n)).
Proof. exact (MK_COMB (@lem513006 n) (@lem513008 n)). Qed.
Lemma lem513011 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem513012 (x : nat) : (x = x) = True.
Proof. exact (@lem513011 nat x). Qed.
Lemma lem513013 (n : nat) : ((term37 n) = (term37 n)) = True.
Proof. exact (@lem513012 (term37 n)). Qed.
Lemma lem513014 (n : nat) : ((term54 n) = (BIT1 n)) = True.
Proof. exact (TRANS (@lem513009 n) (@lem513013 n)). Qed.
Lemma lem513015 : term57 = term45.
Proof. exact (fun_ext (fun n : nat => @lem513014 n)). Qed.
Lemma lem513016 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513017 : term58 = term47.
Proof. exact (MK_COMB (@lem513016) (@lem513015)). Qed.
Lemma lem513019 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem513020 (t : Prop) : (term49 t) = t.
Proof. exact (@lem513019 nat t). Qed.
Lemma lem513021 : term47 = True.
Proof. exact (@lem513020 True). Qed.
Lemma lem513022 : term58 = True.
Proof. exact (TRANS (@lem513017) (@lem513021)). Qed.
Lemma lem513023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513024 : term59 = (and True).
Proof. exact (MK_COMB (@lem513023) (@lem513022)). Qed.
Lemma lem513032 (n : nat) : (BIT1 n) = (term37 n).
Proof. exact (EQ_MP (@lem512930 n) (@lem512929 n)). Qed.
Lemma lem513033 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem513034 (n : nat) : (term60 n) = (term61 n).
Proof. exact (MK_COMB (@lem513033) (@lem513032 n)). Qed.
Lemma lem513035 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513036 (n : nat) : (term62 n) = (term63 n).
Proof. exact (MK_COMB (@lem513035) (@lem513034 n)). Qed.
Lemma lem513038 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem512933 n) (@lem512932 n)). Qed.
Lemma lem513039 (n : nat) : (term64 n) = (term65 n).
Proof. exact (@lem513038 (S n)). Qed.
Lemma lem513041 (m : nat) (n : nat) : (term34 m n) = (term29 m n).
Proof. exact (EQ_MP (@lem512919 m n) (@lem512918 m n)). Qed.
Lemma lem513042 (n : nat) : (term65 n) = (term66 n).
Proof. exact (@lem513041 n (S n)). Qed.
Lemma lem513043 (n : nat) : (term64 n) = (term66 n).
Proof. exact (TRANS (@lem513039 n) (@lem513042 n)). Qed.
Lemma lem513045 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (EQ_MP (@lem512912 m n) (@lem512911 m n)). Qed.
Lemma lem513046 (n : nat) : (term67 n) = (term37 n).
Proof. exact (@lem513045 n n). Qed.
Lemma lem513047 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem513048 (n : nat) : (term66 n) = (term61 n).
Proof. exact (MK_COMB (@lem513047) (@lem513046 n)). Qed.
Lemma lem513049 (n : nat) : (term64 n) = (term61 n).
Proof. exact (TRANS (@lem513043 n) (@lem513048 n)). Qed.
Lemma lem513050 (n : nat) : ((term60 n) = (term64 n)) = ((term61 n) = (term61 n)).
Proof. exact (MK_COMB (@lem513036 n) (@lem513049 n)). Qed.
Lemma lem513052 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem513053 (x : nat) : (x = x) = True.
Proof. exact (@lem513052 nat x). Qed.
Lemma lem513054 (n : nat) : ((term61 n) = (term61 n)) = True.
Proof. exact (@lem513053 (term61 n)). Qed.
Lemma lem513055 (n : nat) : ((term60 n) = (term64 n)) = True.
Proof. exact (TRANS (@lem513050 n) (@lem513054 n)). Qed.
Lemma lem513056 : term68 = term45.
Proof. exact (fun_ext (fun n : nat => @lem513055 n)). Qed.
Lemma lem513057 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513058 : term69 = term47.
Proof. exact (MK_COMB (@lem513057) (@lem513056)). Qed.
Lemma lem513060 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem513061 (t : Prop) : (term49 t) = t.
Proof. exact (@lem513060 nat t). Qed.
Lemma lem513062 : term47 = True.
Proof. exact (@lem513061 True). Qed.
Lemma lem513063 : term69 = True.
Proof. exact (TRANS (@lem513058) (@lem513062)). Qed.
Lemma lem513064 : term70 = (True /\ True).
Proof. exact (MK_COMB (@lem513024) (@lem513063)). Qed.
Lemma lem513066 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem513067 : (True /\ True) = True.
Proof. exact (@lem513066 True). Qed.
Lemma lem513068 : term70 = True.
Proof. exact (TRANS (@lem513064) (@lem513067)). Qed.
Lemma lem513069 : term71 = (True /\ True).
Proof. exact (MK_COMB (@lem512992) (@lem513068)). Qed.
Lemma lem513071 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem513072 : (True /\ True) = True.
Proof. exact (@lem513071 True). Qed.
Lemma lem513073 : term71 = True.
Proof. exact (TRANS (@lem513069) (@lem513072)). Qed.
Lemma lem513074 : term72 = (True /\ True).
Proof. exact (MK_COMB (@lem512970) (@lem513073)). Qed.
Lemma lem513076 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem513077 : (True /\ True) = True.
Proof. exact (@lem513076 True). Qed.
Lemma lem513078 : term72 = True.
Proof. exact (TRANS (@lem513074) (@lem513077)). Qed.
Lemma lem513079 : True = term72.
Proof. exact (SYM (@lem513078)). Qed.
