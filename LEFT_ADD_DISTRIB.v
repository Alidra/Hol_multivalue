Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LEFT_ADD_DISTRIB_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm77238_spec.
Lemma lem81822 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem81823 (m : nat) : term1 m.
Proof. exact (@lem81822 (term2 m)). Qed.
Lemma lem81824 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem81825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem81826 (m : nat) : (term5 m) = (term6 m).
Proof. exact (MK_COMB (@lem81825) (@lem81824 m)). Qed.
Lemma lem81827 (n : nat) (m : nat) : (term7 m n) = (term8 n m).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem81828 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem81829 (n : nat) (m : nat) : (term9 m n) = (term10 n m).
Proof. exact (MK_COMB (@lem81828) (@lem81827 n m)). Qed.
Lemma lem81830 (n : nat) (m : nat) : (term11 m n) = (term12 n m).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem81831 (n : nat) (m : nat) : (term13 m n) = (term14 n m).
Proof. exact (MK_COMB (@lem81829 n m) (@lem81830 n m)). Qed.
Lemma lem81832 (m : nat) : (term15 m) = (term16 m).
Proof. exact (fun_ext (fun n : nat => @lem81831 n m)). Qed.
Lemma lem81833 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81834 (m : nat) : (term17 m) = (term18 m).
Proof. exact (MK_COMB (@lem81833) (@lem81832 m)). Qed.
Lemma lem81835 (m : nat) : (term19 m) = (term20 m).
Proof. exact (MK_COMB (@lem81826 m) (@lem81834 m)). Qed.
Lemma lem81836 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem81837 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem81836) (@lem81835 m)). Qed.
Lemma lem81838 (n : nat) (m : nat) : (term7 m n) = (term8 n m).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem81839 (m : nat) : (term23 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem81838 n m)). Qed.
Lemma lem81840 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81841 (m : nat) : (term24 m) = (term25 m).
Proof. exact (MK_COMB (@lem81840) (@lem81839 m)). Qed.
Lemma lem81842 (m : nat) : (term1 m) = (term26 m).
Proof. exact (MK_COMB (@lem81837 m) (@lem81841 m)). Qed.
Lemma lem81843 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem81842 m) (@lem81823 m)). Qed.
Lemma lem81844 (n : nat) (m : nat) (h1 : term8 n m) : term8 n m.
Proof. exact (h1). Qed.
Lemma lem81854 : term27.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem81880 : term28.
Proof. exact (proj1 (@lem81854)). Qed.
Lemma lem81881 (m : nat) : term29 m.
Proof. exact (@lem81880 m). Qed.
Lemma lem81882 (m : nat) : (term29 m) = ((term30 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem81895 : term31.
Proof. exact (proj1 (@lem77238)). Qed.
Lemma lem81896 (n : nat) : term32 n.
Proof. exact (@lem81895 n). Qed.
Lemma lem81897 (n : nat) : (term32 n) = ((term33 n) = n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem81906 (n : nat) : (term33 n) = n.
Proof. exact (EQ_MP (@lem81897 n) (@lem81896 n)). Qed.
Lemma lem81907 (p : nat) : (term33 p) = p.
Proof. exact (@lem81906 p). Qed.
Lemma lem81908 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem81909 (m : nat) (p : nat) : (term34 m p) = (Nat.mul m p).
Proof. exact (MK_COMB (@lem81908 m) (@lem81907 p)). Qed.
Lemma lem81910 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem81911 (m : nat) (p : nat) : (term35 m p) = (term36 m p).
Proof. exact (MK_COMB (@lem81910) (@lem81909 m p)). Qed.
Lemma lem81913 (m : nat) : (term30 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem81882 m) (@lem81881 m)). Qed.
Lemma lem81914 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem81915 (m : nat) : (term37 m) = term38.
Proof. exact (MK_COMB (@lem81914) (@lem81913 m)). Qed.
Lemma lem81916 (m : nat) (p : nat) : (Nat.mul m p) = (Nat.mul m p).
Proof. exact (eq_refl (Nat.mul m p)). Qed.
Lemma lem81917 (m : nat) (p : nat) : (term39 m p) = (term40 m p).
Proof. exact (MK_COMB (@lem81915 m) (@lem81916 m p)). Qed.
Lemma lem81919 (n : nat) : (term33 n) = n.
Proof. exact (EQ_MP (@lem81897 n) (@lem81896 n)). Qed.
Lemma lem81920 (m : nat) (p : nat) : (term40 m p) = (Nat.mul m p).
Proof. exact (@lem81919 (Nat.mul m p)). Qed.
Lemma lem81921 (m : nat) (p : nat) : (term39 m p) = (Nat.mul m p).
Proof. exact (TRANS (@lem81917 m p) (@lem81920 m p)). Qed.
Lemma lem81922 (m : nat) (p : nat) : ((term34 m p) = (term39 m p)) = ((Nat.mul m p) = (Nat.mul m p)).
Proof. exact (MK_COMB (@lem81911 m p) (@lem81921 m p)). Qed.
Lemma lem81924 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem81925 (x : nat) : (x = x) = True.
Proof. exact (@lem81924 nat x). Qed.
Lemma lem81926 (m : nat) (p : nat) : ((Nat.mul m p) = (Nat.mul m p)) = True.
Proof. exact (@lem81925 (Nat.mul m p)). Qed.
Lemma lem81927 (m : nat) (p : nat) : ((term34 m p) = (term39 m p)) = True.
Proof. exact (TRANS (@lem81922 m p) (@lem81926 m p)). Qed.
Lemma lem81928 (m : nat) : (term41 m) = term42.
Proof. exact (fun_ext (fun p : nat => @lem81927 m p)). Qed.
Lemma lem81929 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81930 (m : nat) : (term4 m) = term43.
Proof. exact (MK_COMB (@lem81929) (@lem81928 m)). Qed.
Lemma lem81932 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem81933 (t : Prop) : (term45 t) = t.
Proof. exact (@lem81932 nat t). Qed.
Lemma lem81934 : term43 = True.
Proof. exact (@lem81933 True). Qed.
Lemma lem81935 (m : nat) : (term4 m) = True.
Proof. exact (TRANS (@lem81930 m) (@lem81934)). Qed.
Lemma lem81936 (m : nat) : True = (term4 m).
Proof. exact (SYM (@lem81935 m)). Qed.
Lemma lem81937 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem81936 m) (@lem0)). Qed.
Lemma lem81938 (m : nat) : term46 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem81939 (m : nat) : (term46 m) = (term47 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem81940 (m : nat) : term47 m.
Proof. exact (EQ_MP (@lem81939 m) (@lem81938 m)). Qed.
Lemma lem81941 (m : nat) (n : nat) : term48 m n.
Proof. exact (@lem81940 m n). Qed.
Lemma lem81942 (m : nat) (n : nat) : (term48 m n) = (term49 m n).
Proof. exact (eq_refl (term48 m n)). Qed.
Lemma lem81943 (m : nat) (n : nat) : term49 m n.
Proof. exact (EQ_MP (@lem81942 m n) (@lem81941 m n)). Qed.
Lemma lem81944 (m : nat) (n : nat) (p : nat) : term50 m n p.
Proof. exact (@lem81943 m n p). Qed.
Lemma lem81945 (m : nat) (n : nat) (p : nat) : (term50 m n p) = ((term51 m n p) = (term52 m n p)).
Proof. exact (eq_refl (term50 m n p)). Qed.
Lemma lem81947 : term27.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem81948 : term53.
Proof. exact (proj2 (@lem81947)). Qed.
Lemma lem81949 : term54.
Proof. exact (proj2 (@lem81948)). Qed.
Lemma lem81950 : term55.
Proof. exact (proj2 (@lem81949)). Qed.
Lemma lem81951 : term56.
Proof. exact (proj2 (@lem81950)). Qed.
Lemma lem81952 (m : nat) : term57 m.
Proof. exact (@lem81951 m). Qed.
Lemma lem81953 (m : nat) : (term57 m) = (term58 m).
Proof. exact (eq_refl (term57 m)). Qed.
Lemma lem81954 (m : nat) : term58 m.
Proof. exact (EQ_MP (@lem81953 m) (@lem81952 m)). Qed.
Lemma lem81955 (m : nat) (n : nat) : term59 m n.
Proof. exact (@lem81954 m n). Qed.
Lemma lem81956 (m : nat) (n : nat) : (term59 m n) = ((term60 m n) = (term61 m n)).
Proof. exact (eq_refl (term59 m n)). Qed.
Lemma lem81981 : term62.
Proof. exact (proj2 (@lem77238)). Qed.
Lemma lem81982 (m : nat) : term63 m.
Proof. exact (@lem81981 m). Qed.
Lemma lem81983 (m : nat) : (term63 m) = (term64 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem81984 (m : nat) : term64 m.
Proof. exact (EQ_MP (@lem81983 m) (@lem81982 m)). Qed.
Lemma lem81985 (m : nat) (n : nat) : term65 m n.
Proof. exact (@lem81984 m n). Qed.
Lemma lem81986 (m : nat) (n : nat) : (term65 m n) = ((term66 m n) = (term67 m n)).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem81992 (p : nat) (n : nat) (m : nat) (h1 : term8 n m) : term68 n m p.
Proof. exact (@lem81844 n m h1 p). Qed.
Lemma lem81993 (n : nat) (m : nat) (p : nat) : (term68 n m p) = ((term69 m n p) = (term70 n m p)).
Proof. exact (eq_refl (term68 n m p)). Qed.
Lemma lem82002 (m : nat) (n : nat) : (term66 m n) = (term67 m n).
Proof. exact (EQ_MP (@lem81986 m n) (@lem81985 m n)). Qed.
Lemma lem82003 (n : nat) (p : nat) : (term66 n p) = (term67 n p).
Proof. exact (@lem82002 n p). Qed.
Lemma lem82004 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem82005 (m : nat) (n : nat) (p : nat) : (term71 m n p) = (term72 m n p).
Proof. exact (MK_COMB (@lem82004 m) (@lem82003 n p)). Qed.
Lemma lem82007 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (EQ_MP (@lem81956 m n) (@lem81955 m n)). Qed.
Lemma lem82008 (m : nat) (n : nat) (p : nat) : (term72 m n p) = (term73 m n p).
Proof. exact (@lem82007 m (Nat.add n p)). Qed.
Lemma lem82010 (p : nat) (n : nat) (m : nat) (h1 : term8 n m) : (term69 m n p) = (term70 n m p).
Proof. exact (EQ_MP (@lem81993 n m p) (@lem81992 p n m h1)). Qed.
Lemma lem82011 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem82012 (p : nat) (n : nat) (m : nat) (h1 : term8 n m) : (term73 m n p) = (term74 n m p).
Proof. exact (MK_COMB (@lem82011 m) (@lem82010 p n m h1)). Qed.
Lemma lem82014 (m : nat) (n : nat) (p : nat) : (term51 m n p) = (term52 m n p).
Proof. exact (EQ_MP (@lem81945 m n p) (@lem81944 m n p)). Qed.
Lemma lem82015 (n : nat) (m : nat) (p : nat) : (term74 n m p) = (term75 n m p).
Proof. exact (@lem82014 m (Nat.mul m n) (Nat.mul m p)). Qed.
Lemma lem82016 (p : nat) (n : nat) (m : nat) (h1 : term8 n m) : (term73 m n p) = (term75 n m p).
Proof. exact (TRANS (@lem82012 p n m h1) (@lem82015 n m p)). Qed.
Lemma lem82017 (p : nat) (n : nat) (m : nat) (h1 : term8 n m) : (term72 m n p) = (term75 n m p).
Proof. exact (TRANS (@lem82008 m n p) (@lem82016 p n m h1)). Qed.
Lemma lem82018 (p : nat) (n : nat) (m : nat) (h1 : term8 n m) : (term71 m n p) = (term75 n m p).
Proof. exact (TRANS (@lem82005 m n p) (@lem82017 p n m h1)). Qed.
Lemma lem82019 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem82020 (p : nat) (n : nat) (m : nat) (h1 : term8 n m) : (term76 m n p) = (term77 n m p).
Proof. exact (MK_COMB (@lem82019) (@lem82018 p n m h1)). Qed.
Lemma lem82022 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (EQ_MP (@lem81956 m n) (@lem81955 m n)). Qed.
Lemma lem82023 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem82024 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (MK_COMB (@lem82023) (@lem82022 m n)). Qed.
Lemma lem82025 (m : nat) (p : nat) : (Nat.mul m p) = (Nat.mul m p).
Proof. exact (eq_refl (Nat.mul m p)). Qed.
Lemma lem82026 (n : nat) (m : nat) (p : nat) : (term80 n m p) = (term75 n m p).
Proof. exact (MK_COMB (@lem82024 m n) (@lem82025 m p)). Qed.
Lemma lem82027 (p : nat) (n : nat) (m : nat) (h1 : term8 n m) : ((term71 m n p) = (term80 n m p)) = ((term75 n m p) = (term75 n m p)).
Proof. exact (MK_COMB (@lem82020 p n m h1) (@lem82026 n m p)). Qed.
Lemma lem82029 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem82030 (x : nat) : (x = x) = True.
Proof. exact (@lem82029 nat x). Qed.
Lemma lem82031 (n : nat) (m : nat) (p : nat) : ((term75 n m p) = (term75 n m p)) = True.
Proof. exact (@lem82030 (term75 n m p)). Qed.
Lemma lem82032 (p : nat) (n : nat) (m : nat) (h1 : term8 n m) : ((term71 m n p) = (term80 n m p)) = True.
Proof. exact (TRANS (@lem82027 p n m h1) (@lem82031 n m p)). Qed.
Lemma lem82033 (n : nat) (m : nat) (h1 : term8 n m) : (term81 n m) = term42.
Proof. exact (fun_ext (fun p : nat => @lem82032 p n m h1)). Qed.
Lemma lem82034 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82035 (n : nat) (m : nat) (h1 : term8 n m) : (term12 n m) = term43.
Proof. exact (MK_COMB (@lem82034) (@lem82033 n m h1)). Qed.
Lemma lem82037 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem82038 (t : Prop) : (term45 t) = t.
Proof. exact (@lem82037 nat t). Qed.
Lemma lem82039 : term43 = True.
Proof. exact (@lem82038 True). Qed.
Lemma lem82040 (n : nat) (m : nat) (h1 : term8 n m) : (term12 n m) = True.
Proof. exact (TRANS (@lem82035 n m h1) (@lem82039)). Qed.
Lemma lem82041 (n : nat) (m : nat) (h1 : term8 n m) : True = (term12 n m).
Proof. exact (SYM (@lem82040 n m h1)). Qed.
Lemma lem82042 (n : nat) (m : nat) (h1 : term8 n m) : term12 n m.
Proof. exact (EQ_MP (@lem82041 n m h1) (@lem0)). Qed.
Lemma lem82043 (n : nat) (m : nat) : term14 n m.
Proof. exact (fun h0 : term8 n m => @lem82042 n m h0). Qed.
Lemma lem82048 (m : nat) : term18 m.
Proof. exact (fun n : nat => @lem82043 n m). Qed.
Lemma lem82049 (m : nat) : term20 m.
Proof. exact (conj (@lem81937 m) (@lem82048 m)). Qed.
Lemma lem82050 (m : nat) : term25 m.
Proof. exact (@lem81843 m (@lem82049 m)). Qed.
Lemma lem82055 : term82.
Proof. exact (fun m : nat => @lem82050 m). Qed.
