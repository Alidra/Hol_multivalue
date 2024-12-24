Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516204_term_abbrevs.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm515640_spec.
Require Import thm515641_spec.
Require Import thm515674_spec.
Require Import thm515675_spec.
Require Import thm515681_spec.
Require Import thm515682_spec.
Require Import thm515685_spec.
Require Import thm515686_spec.
Require Import thm515688_spec.
Require Import thm515689_spec.
Require Import thm515691_spec.
Require Import thm515692_spec.
Lemma lem515918 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem515692 n) (@lem515691 n)). Qed.
Lemma lem515919 : (Nat.pow 0) = (Nat.pow 0).
Proof. exact (eq_refl (Nat.pow 0)). Qed.
Lemma lem515920 (n : nat) : (term0 n) = (term1 n).
Proof. exact (MK_COMB (@lem515919) (@lem515918 n)). Qed.
Lemma lem515921 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515922 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem515921) (@lem515920 n)). Qed.
Lemma lem515923 (n : nat) : (term4 n) = (term4 n).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem515924 (n : nat) : ((term0 n) = (term4 n)) = ((term1 n) = (term4 n)).
Proof. exact (MK_COMB (@lem515922 n) (@lem515923 n)). Qed.
Lemma lem515925 (n : nat) : ((term1 n) = (term4 n)) = ((term0 n) = (term4 n)).
Proof. exact (SYM (@lem515924 n)). Qed.
Lemma lem515927 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem515692 n) (@lem515691 n)). Qed.
Lemma lem515928 (m : nat) : (term5 m) = (term5 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem515929 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem515928 m) (@lem515927 n)). Qed.
Lemma lem515930 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515931 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem515930) (@lem515929 m n)). Qed.
Lemma lem515932 (m : nat) (n : nat) : (term10 m n) = (term10 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem515933 (m : nat) (n : nat) : ((term6 m n) = (term10 m n)) = ((term7 m n) = (term10 m n)).
Proof. exact (MK_COMB (@lem515931 m n) (@lem515932 m n)). Qed.
Lemma lem515934 (m : nat) (n : nat) : ((term7 m n) = (term10 m n)) = ((term6 m n) = (term10 m n)).
Proof. exact (SYM (@lem515933 m n)). Qed.
Lemma lem515936 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem515692 n) (@lem515691 n)). Qed.
Lemma lem515937 (m : nat) : (term11 m) = (term11 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem515938 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem515937 m) (@lem515936 n)). Qed.
Lemma lem515939 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515940 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (MK_COMB (@lem515939) (@lem515938 m n)). Qed.
Lemma lem515941 (m : nat) (n : nat) : (term16 m n) = (term16 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem515942 (m : nat) (n : nat) : ((term12 m n) = (term16 m n)) = ((term13 m n) = (term16 m n)).
Proof. exact (MK_COMB (@lem515940 m n) (@lem515941 m n)). Qed.
Lemma lem515943 (m : nat) (n : nat) : ((term13 m n) = (term16 m n)) = ((term12 m n) = (term16 m n)).
Proof. exact (SYM (@lem515942 m n)). Qed.
Lemma lem515945 (n : nat) : (BIT1 n) = (term17 n).
Proof. exact (EQ_MP (@lem515689 n) (@lem515688 n)). Qed.
Lemma lem515946 : (Nat.pow 0) = (Nat.pow 0).
Proof. exact (eq_refl (Nat.pow 0)). Qed.
Lemma lem515947 (n : nat) : (term18 n) = (term19 n).
Proof. exact (MK_COMB (@lem515946) (@lem515945 n)). Qed.
Lemma lem515948 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515949 (n : nat) : (term20 n) = (term21 n).
Proof. exact (MK_COMB (@lem515948) (@lem515947 n)). Qed.
Lemma lem515950 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem515951 (n : nat) : ((term18 n) = 0) = ((term19 n) = 0).
Proof. exact (MK_COMB (@lem515949 n) (@lem515950)). Qed.
Lemma lem515952 (n : nat) : ((term19 n) = 0) = ((term18 n) = 0).
Proof. exact (SYM (@lem515951 n)). Qed.
Lemma lem515954 (n : nat) : (BIT1 n) = (term17 n).
Proof. exact (EQ_MP (@lem515689 n) (@lem515688 n)). Qed.
Lemma lem515955 (m : nat) : (term5 m) = (term5 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem515956 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem515955 m) (@lem515954 n)). Qed.
Lemma lem515957 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515958 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (MK_COMB (@lem515957) (@lem515956 m n)). Qed.
Lemma lem515959 (m : nat) (n : nat) : (term26 m n) = (term26 m n).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem515960 (m : nat) (n : nat) : ((term22 m n) = (term26 m n)) = ((term23 m n) = (term26 m n)).
Proof. exact (MK_COMB (@lem515958 m n) (@lem515959 m n)). Qed.
Lemma lem515961 (m : nat) (n : nat) : ((term23 m n) = (term26 m n)) = ((term22 m n) = (term26 m n)).
Proof. exact (SYM (@lem515960 m n)). Qed.
Lemma lem515963 (n : nat) : (BIT1 n) = (term17 n).
Proof. exact (EQ_MP (@lem515689 n) (@lem515688 n)). Qed.
Lemma lem515964 (m : nat) : (term11 m) = (term11 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem515965 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem515964 m) (@lem515963 n)). Qed.
Lemma lem515966 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515967 (m : nat) (n : nat) : (term29 m n) = (term30 m n).
Proof. exact (MK_COMB (@lem515966) (@lem515965 m n)). Qed.
Lemma lem515968 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem515969 (m : nat) (n : nat) : ((term27 m n) = (term31 m n)) = ((term28 m n) = (term31 m n)).
Proof. exact (MK_COMB (@lem515967 m n) (@lem515968 m n)). Qed.
Lemma lem515970 (m : nat) (n : nat) : ((term28 m n) = (term31 m n)) = ((term27 m n) = (term31 m n)).
Proof. exact (SYM (@lem515969 m n)). Qed.
Lemma lem515974 (m : nat) : (Nat.pow m 0) = (BIT1 0).
Proof. exact (EQ_MP (@lem515686 m) (@lem515685 m)). Qed.
Lemma lem515975 : (Nat.pow 0 0) = (BIT1 0).
Proof. exact (@lem515974 0). Qed.
Lemma lem515976 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515977 : term32 = term33.
Proof. exact (MK_COMB (@lem515976) (@lem515975)). Qed.
Lemma lem515978 : (BIT1 0) = (BIT1 0).
Proof. exact (eq_refl (BIT1 0)). Qed.
Lemma lem515979 : ((Nat.pow 0 0) = (BIT1 0)) = ((BIT1 0) = (BIT1 0)).
Proof. exact (MK_COMB (@lem515977) (@lem515978)). Qed.
Lemma lem515981 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem515982 (x : nat) : (x = x) = True.
Proof. exact (@lem515981 nat x). Qed.
Lemma lem515983 : ((BIT1 0) = (BIT1 0)) = True.
Proof. exact (@lem515982 (BIT1 0)). Qed.
Lemma lem515984 : ((Nat.pow 0 0) = (BIT1 0)) = True.
Proof. exact (TRANS (@lem515979) (@lem515983)). Qed.
Lemma lem515985 : True = ((Nat.pow 0 0) = (BIT1 0)).
Proof. exact (SYM (@lem515984)). Qed.
Lemma lem515986 : (Nat.pow 0 0) = (BIT1 0).
Proof. exact (EQ_MP (@lem515985) (@lem0)). Qed.
Lemma lem515990 (m : nat) : (Nat.pow m 0) = (BIT1 0).
Proof. exact (EQ_MP (@lem515686 m) (@lem515685 m)). Qed.
Lemma lem515991 (m : nat) : (term34 m) = (BIT1 0).
Proof. exact (@lem515990 (BIT0 m)). Qed.
Lemma lem515992 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515993 (m : nat) : (term35 m) = term33.
Proof. exact (MK_COMB (@lem515992) (@lem515991 m)). Qed.
Lemma lem515994 : (BIT1 0) = (BIT1 0).
Proof. exact (eq_refl (BIT1 0)). Qed.
Lemma lem515995 (m : nat) : ((term34 m) = (BIT1 0)) = ((BIT1 0) = (BIT1 0)).
Proof. exact (MK_COMB (@lem515993 m) (@lem515994)). Qed.
Lemma lem515997 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem515998 (x : nat) : (x = x) = True.
Proof. exact (@lem515997 nat x). Qed.
Lemma lem515999 : ((BIT1 0) = (BIT1 0)) = True.
Proof. exact (@lem515998 (BIT1 0)). Qed.
Lemma lem516000 (m : nat) : ((term34 m) = (BIT1 0)) = True.
Proof. exact (TRANS (@lem515995 m) (@lem515999)). Qed.
Lemma lem516001 (m : nat) : True = ((term34 m) = (BIT1 0)).
Proof. exact (SYM (@lem516000 m)). Qed.
Lemma lem516002 (m : nat) : (term34 m) = (BIT1 0).
Proof. exact (EQ_MP (@lem516001 m) (@lem0)). Qed.
Lemma lem516006 (m : nat) : (Nat.pow m 0) = (BIT1 0).
Proof. exact (EQ_MP (@lem515686 m) (@lem515685 m)). Qed.
Lemma lem516007 (m : nat) : (term36 m) = (BIT1 0).
Proof. exact (@lem516006 (BIT1 m)). Qed.
Lemma lem516008 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem516009 (m : nat) : (term37 m) = term33.
Proof. exact (MK_COMB (@lem516008) (@lem516007 m)). Qed.
Lemma lem516010 : (BIT1 0) = (BIT1 0).
Proof. exact (eq_refl (BIT1 0)). Qed.
Lemma lem516011 (m : nat) : ((term36 m) = (BIT1 0)) = ((BIT1 0) = (BIT1 0)).
Proof. exact (MK_COMB (@lem516009 m) (@lem516010)). Qed.
Lemma lem516013 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem516014 (x : nat) : (x = x) = True.
Proof. exact (@lem516013 nat x). Qed.
Lemma lem516015 : ((BIT1 0) = (BIT1 0)) = True.
Proof. exact (@lem516014 (BIT1 0)). Qed.
Lemma lem516016 (m : nat) : ((term36 m) = (BIT1 0)) = True.
Proof. exact (TRANS (@lem516011 m) (@lem516015)). Qed.
Lemma lem516017 (m : nat) : True = ((term36 m) = (BIT1 0)).
Proof. exact (SYM (@lem516016 m)). Qed.
Lemma lem516018 (m : nat) : (term36 m) = (BIT1 0).
Proof. exact (EQ_MP (@lem516017 m) (@lem0)). Qed.
Lemma lem516022 (n : nat) (m : nat) (p : nat) : (term38 m n p) = (term39 n m p).
Proof. exact (EQ_MP (@lem515641 n m p) (@lem515640 n m p)). Qed.
Lemma lem516023 (n : nat) : (term1 n) = (term4 n).
Proof. exact (@lem516022 n 0 n). Qed.
Lemma lem516024 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem516025 (n : nat) : (term3 n) = (term40 n).
Proof. exact (MK_COMB (@lem516024) (@lem516023 n)). Qed.
Lemma lem516026 (n : nat) : (term4 n) = (term4 n).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem516027 (n : nat) : ((term1 n) = (term4 n)) = ((term4 n) = (term4 n)).
Proof. exact (MK_COMB (@lem516025 n) (@lem516026 n)). Qed.
Lemma lem516029 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem516030 (x : nat) : (x = x) = True.
Proof. exact (@lem516029 nat x). Qed.
Lemma lem516031 (n : nat) : ((term4 n) = (term4 n)) = True.
Proof. exact (@lem516030 (term4 n)). Qed.
Lemma lem516032 (n : nat) : ((term1 n) = (term4 n)) = True.
Proof. exact (TRANS (@lem516027 n) (@lem516031 n)). Qed.
Lemma lem516033 (n : nat) : True = ((term1 n) = (term4 n)).
Proof. exact (SYM (@lem516032 n)). Qed.
Lemma lem516034 (n : nat) : (term1 n) = (term4 n).
Proof. exact (EQ_MP (@lem516033 n) (@lem0)). Qed.
Lemma lem516038 (n : nat) (m : nat) (p : nat) : (term38 m n p) = (term39 n m p).
Proof. exact (EQ_MP (@lem515641 n m p) (@lem515640 n m p)). Qed.
Lemma lem516039 (m : nat) (n : nat) : (term7 m n) = (term10 m n).
Proof. exact (@lem516038 n (BIT0 m) n). Qed.
Lemma lem516040 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem516041 (m : nat) (n : nat) : (term9 m n) = (term41 m n).
Proof. exact (MK_COMB (@lem516040) (@lem516039 m n)). Qed.
Lemma lem516042 (m : nat) (n : nat) : (term10 m n) = (term10 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem516043 (m : nat) (n : nat) : ((term7 m n) = (term10 m n)) = ((term10 m n) = (term10 m n)).
Proof. exact (MK_COMB (@lem516041 m n) (@lem516042 m n)). Qed.
Lemma lem516045 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem516046 (x : nat) : (x = x) = True.
Proof. exact (@lem516045 nat x). Qed.
Lemma lem516047 (m : nat) (n : nat) : ((term10 m n) = (term10 m n)) = True.
Proof. exact (@lem516046 (term10 m n)). Qed.
Lemma lem516048 (m : nat) (n : nat) : ((term7 m n) = (term10 m n)) = True.
Proof. exact (TRANS (@lem516043 m n) (@lem516047 m n)). Qed.
Lemma lem516049 (m : nat) (n : nat) : True = ((term7 m n) = (term10 m n)).
Proof. exact (SYM (@lem516048 m n)). Qed.
Lemma lem516050 (m : nat) (n : nat) : (term7 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem516049 m n) (@lem0)). Qed.
Lemma lem516054 (n : nat) (m : nat) (p : nat) : (term38 m n p) = (term39 n m p).
Proof. exact (EQ_MP (@lem515641 n m p) (@lem515640 n m p)). Qed.
Lemma lem516055 (m : nat) (n : nat) : (term13 m n) = (term16 m n).
Proof. exact (@lem516054 n (BIT1 m) n). Qed.
Lemma lem516056 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem516057 (m : nat) (n : nat) : (term15 m n) = (term42 m n).
Proof. exact (MK_COMB (@lem516056) (@lem516055 m n)). Qed.
Lemma lem516058 (m : nat) (n : nat) : (term16 m n) = (term16 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem516059 (m : nat) (n : nat) : ((term13 m n) = (term16 m n)) = ((term16 m n) = (term16 m n)).
Proof. exact (MK_COMB (@lem516057 m n) (@lem516058 m n)). Qed.
Lemma lem516061 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem516062 (x : nat) : (x = x) = True.
Proof. exact (@lem516061 nat x). Qed.
Lemma lem516063 (m : nat) (n : nat) : ((term16 m n) = (term16 m n)) = True.
Proof. exact (@lem516062 (term16 m n)). Qed.
Lemma lem516064 (m : nat) (n : nat) : ((term13 m n) = (term16 m n)) = True.
Proof. exact (TRANS (@lem516059 m n) (@lem516063 m n)). Qed.
Lemma lem516065 (m : nat) (n : nat) : True = ((term13 m n) = (term16 m n)).
Proof. exact (SYM (@lem516064 m n)). Qed.
Lemma lem516066 (m : nat) (n : nat) : (term13 m n) = (term16 m n).
Proof. exact (EQ_MP (@lem516065 m n) (@lem0)). Qed.
Lemma lem516070 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem515682 m n) (@lem515681 m n)). Qed.
Lemma lem516071 (n : nat) : (term19 n) = (term45 n).
Proof. exact (@lem516070 0 (Nat.add n n)). Qed.
Lemma lem516073 (n : nat) : (Nat.mul 0 n) = 0.
Proof. exact (EQ_MP (@lem515675 n) (@lem515674 n)). Qed.
Lemma lem516074 (n : nat) : (term45 n) = 0.
Proof. exact (@lem516073 (term1 n)). Qed.
Lemma lem516075 (n : nat) : (term19 n) = 0.
Proof. exact (TRANS (@lem516071 n) (@lem516074 n)). Qed.
Lemma lem516076 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem516077 (n : nat) : (term21 n) = (@eq nat 0).
Proof. exact (MK_COMB (@lem516076) (@lem516075 n)). Qed.
Lemma lem516078 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem516079 (n : nat) : ((term19 n) = 0) = (0 = 0).
Proof. exact (MK_COMB (@lem516077 n) (@lem516078)). Qed.
Lemma lem516081 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem516082 (x : nat) : (x = x) = True.
Proof. exact (@lem516081 nat x). Qed.
Lemma lem516083 : (0 = 0) = True.
Proof. exact (@lem516082 0). Qed.
Lemma lem516084 (n : nat) : ((term19 n) = 0) = True.
Proof. exact (TRANS (@lem516079 n) (@lem516083)). Qed.
Lemma lem516085 (n : nat) : True = ((term19 n) = 0).
Proof. exact (SYM (@lem516084 n)). Qed.
Lemma lem516086 (n : nat) : (term19 n) = 0.
Proof. exact (EQ_MP (@lem516085 n) (@lem0)). Qed.
Lemma lem516090 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem515682 m n) (@lem515681 m n)). Qed.
Lemma lem516091 (m : nat) (n : nat) : (term23 m n) = (term46 m n).
Proof. exact (@lem516090 (BIT0 m) (Nat.add n n)). Qed.
Lemma lem516093 (n : nat) (m : nat) (p : nat) : (term38 m n p) = (term39 n m p).
Proof. exact (EQ_MP (@lem515641 n m p) (@lem515640 n m p)). Qed.
Lemma lem516094 (m : nat) (n : nat) : (term7 m n) = (term10 m n).
Proof. exact (@lem516093 n (BIT0 m) n). Qed.
Lemma lem516095 (m : nat) : (term47 m) = (term47 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem516096 (m : nat) (n : nat) : (term46 m n) = (term26 m n).
Proof. exact (MK_COMB (@lem516095 m) (@lem516094 m n)). Qed.
Lemma lem516097 (m : nat) (n : nat) : (term23 m n) = (term26 m n).
Proof. exact (TRANS (@lem516091 m n) (@lem516096 m n)). Qed.
Lemma lem516098 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem516099 (m : nat) (n : nat) : (term25 m n) = (term48 m n).
Proof. exact (MK_COMB (@lem516098) (@lem516097 m n)). Qed.
Lemma lem516100 (m : nat) (n : nat) : (term26 m n) = (term26 m n).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem516101 (m : nat) (n : nat) : ((term23 m n) = (term26 m n)) = ((term26 m n) = (term26 m n)).
Proof. exact (MK_COMB (@lem516099 m n) (@lem516100 m n)). Qed.
Lemma lem516103 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem516104 (x : nat) : (x = x) = True.
Proof. exact (@lem516103 nat x). Qed.
Lemma lem516105 (m : nat) (n : nat) : ((term26 m n) = (term26 m n)) = True.
Proof. exact (@lem516104 (term26 m n)). Qed.
Lemma lem516106 (m : nat) (n : nat) : ((term23 m n) = (term26 m n)) = True.
Proof. exact (TRANS (@lem516101 m n) (@lem516105 m n)). Qed.
Lemma lem516107 (m : nat) (n : nat) : True = ((term23 m n) = (term26 m n)).
Proof. exact (SYM (@lem516106 m n)). Qed.
Lemma lem516108 (m : nat) (n : nat) : (term23 m n) = (term26 m n).
Proof. exact (EQ_MP (@lem516107 m n) (@lem0)). Qed.
Lemma lem516112 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem515682 m n) (@lem515681 m n)). Qed.
Lemma lem516113 (m : nat) (n : nat) : (term28 m n) = (term49 m n).
Proof. exact (@lem516112 (BIT1 m) (Nat.add n n)). Qed.
Lemma lem516115 (n : nat) (m : nat) (p : nat) : (term38 m n p) = (term39 n m p).
Proof. exact (EQ_MP (@lem515641 n m p) (@lem515640 n m p)). Qed.
Lemma lem516116 (m : nat) (n : nat) : (term13 m n) = (term16 m n).
Proof. exact (@lem516115 n (BIT1 m) n). Qed.
Lemma lem516117 (m : nat) : (term50 m) = (term50 m).
Proof. exact (eq_refl (term50 m)). Qed.
Lemma lem516118 (m : nat) (n : nat) : (term49 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem516117 m) (@lem516116 m n)). Qed.
Lemma lem516119 (m : nat) (n : nat) : (term28 m n) = (term31 m n).
Proof. exact (TRANS (@lem516113 m n) (@lem516118 m n)). Qed.
Lemma lem516120 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem516121 (m : nat) (n : nat) : (term30 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem516120) (@lem516119 m n)). Qed.
Lemma lem516122 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem516123 (m : nat) (n : nat) : ((term28 m n) = (term31 m n)) = ((term31 m n) = (term31 m n)).
Proof. exact (MK_COMB (@lem516121 m n) (@lem516122 m n)). Qed.
Lemma lem516125 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem516126 (x : nat) : (x = x) = True.
Proof. exact (@lem516125 nat x). Qed.
Lemma lem516127 (m : nat) (n : nat) : ((term31 m n) = (term31 m n)) = True.
Proof. exact (@lem516126 (term31 m n)). Qed.
Lemma lem516128 (m : nat) (n : nat) : ((term28 m n) = (term31 m n)) = True.
Proof. exact (TRANS (@lem516123 m n) (@lem516127 m n)). Qed.
Lemma lem516129 (m : nat) (n : nat) : True = ((term28 m n) = (term31 m n)).
Proof. exact (SYM (@lem516128 m n)). Qed.
Lemma lem516130 (m : nat) (n : nat) : (term28 m n) = (term31 m n).
Proof. exact (EQ_MP (@lem516129 m n) (@lem0)). Qed.
Lemma lem516131 (m : nat) (n : nat) : (term27 m n) = (term31 m n).
Proof. exact (EQ_MP (@lem515970 m n) (@lem516130 m n)). Qed.
Lemma lem516132 (m : nat) (n : nat) : (term22 m n) = (term26 m n).
Proof. exact (EQ_MP (@lem515961 m n) (@lem516108 m n)). Qed.
Lemma lem516133 (n : nat) : (term18 n) = 0.
Proof. exact (EQ_MP (@lem515952 n) (@lem516086 n)). Qed.
Lemma lem516134 (m : nat) (n : nat) : (term12 m n) = (term16 m n).
Proof. exact (EQ_MP (@lem515943 m n) (@lem516066 m n)). Qed.
Lemma lem516135 (m : nat) (n : nat) : (term6 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem515934 m n) (@lem516050 m n)). Qed.
Lemma lem516136 (n : nat) : (term0 n) = (term4 n).
Proof. exact (EQ_MP (@lem515925 n) (@lem516034 n)). Qed.
Lemma lem516141 (m : nat) : term52 m.
Proof. exact (fun n : nat => @lem516131 m n). Qed.
Lemma lem516146 : term53.
Proof. exact (fun m : nat => @lem516141 m). Qed.
Lemma lem516151 (m : nat) : term54 m.
Proof. exact (fun n : nat => @lem516132 m n). Qed.
Lemma lem516156 : term55.
Proof. exact (fun m : nat => @lem516151 m). Qed.
Lemma lem516157 : term56.
Proof. exact (conj (@lem516156) (@lem516146)). Qed.
Lemma lem516162 : term57.
Proof. exact (fun n : nat => @lem516133 n). Qed.
Lemma lem516163 : term58.
Proof. exact (conj (@lem516162) (@lem516157)). Qed.
Lemma lem516168 (m : nat) : term59 m.
Proof. exact (fun n : nat => @lem516134 m n). Qed.
Lemma lem516173 : term60.
Proof. exact (fun m : nat => @lem516168 m). Qed.
Lemma lem516174 : term61.
Proof. exact (conj (@lem516173) (@lem516163)). Qed.
Lemma lem516179 (m : nat) : term62 m.
Proof. exact (fun n : nat => @lem516135 m n). Qed.
Lemma lem516184 : term63.
Proof. exact (fun m : nat => @lem516179 m). Qed.
Lemma lem516185 : term64.
Proof. exact (conj (@lem516184) (@lem516174)). Qed.
Lemma lem516190 : term65.
Proof. exact (fun n : nat => @lem516136 n). Qed.
Lemma lem516191 : term66.
Proof. exact (conj (@lem516190) (@lem516185)). Qed.
Lemma lem516196 : term67.
Proof. exact (fun m : nat => @lem516018 m). Qed.
Lemma lem516197 : term68.
Proof. exact (conj (@lem516196) (@lem516191)). Qed.
Lemma lem516202 : term69.
Proof. exact (fun m : nat => @lem516002 m). Qed.
Lemma lem516203 : term70.
Proof. exact (conj (@lem516202) (@lem516197)). Qed.
Lemma lem516204 : term71.
Proof. exact (conj (@lem515986) (@lem516203)). Qed.
