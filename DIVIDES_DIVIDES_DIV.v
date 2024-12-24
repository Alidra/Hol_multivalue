Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVIDES_DIVIDES_DIV_term_abbrevs.
Require Import INT_DIVIDES_DIVIDES_DIV_spec.
Require Import INT_OF_NUM_DIV_spec.
Require Import INT_OF_NUM_MUL_spec.
Require Import num_divides_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem3112966 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term0 m n) = (term1 m n).
Proof. exact (h1). Qed.
Lemma lem3112967 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term1 m n) = (term0 m n).
Proof. exact (SYM (@lem3112966 m n h1)). Qed.
Lemma lem3112968 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term1 m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem3112969 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term0 m n) = (term1 m n).
Proof. exact (SYM (@lem3112968 m n h1)). Qed.
Lemma lem3112970 (m : nat) (n : nat) : ((term0 m n) = (term1 m n)) = ((term1 m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (term1 m n) => @lem3112967 m n h1) (fun h1 : (term1 m n) = (term0 m n) => @lem3112969 m n h1)). Qed.
Lemma lem3112971 (m : nat) : (term2 m) = (term3 m).
Proof. exact (fun_ext (fun n : nat => @lem3112970 m n)). Qed.
Lemma lem3112972 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112973 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem3112972) (@lem3112971 m)). Qed.
Lemma lem3112974 : term6 = term7.
Proof. exact (fun_ext (fun m : nat => @lem3112973 m)). Qed.
Lemma lem3112975 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112976 : term8 = term9.
Proof. exact (MK_COMB (@lem3112975) (@lem3112974)). Qed.
Lemma lem3112977 : term9.
Proof. exact (EQ_MP (@lem3112976) (@lem2307381)). Qed.
Lemma lem3112980 (m : nat) (n : nat) (h1 : (term10 m n) = (term11 m n)) : (term10 m n) = (term11 m n).
Proof. exact (h1). Qed.
Lemma lem3112981 (m : nat) (n : nat) (h1 : (term10 m n) = (term11 m n)) : (term11 m n) = (term10 m n).
Proof. exact (SYM (@lem3112980 m n h1)). Qed.
Lemma lem3112982 (m : nat) (n : nat) (h1 : (term11 m n) = (term10 m n)) : (term11 m n) = (term10 m n).
Proof. exact (h1). Qed.
Lemma lem3112983 (m : nat) (n : nat) (h1 : (term11 m n) = (term10 m n)) : (term10 m n) = (term11 m n).
Proof. exact (SYM (@lem3112982 m n h1)). Qed.
Lemma lem3112984 (m : nat) (n : nat) : ((term10 m n) = (term11 m n)) = ((term11 m n) = (term10 m n)).
Proof. exact (prop_ext (fun h1 : (term10 m n) = (term11 m n) => @lem3112981 m n h1) (fun h1 : (term11 m n) = (term10 m n) => @lem3112983 m n h1)). Qed.
Lemma lem3112985 (m : nat) : (term12 m) = (term13 m).
Proof. exact (fun_ext (fun n : nat => @lem3112984 m n)). Qed.
Lemma lem3112986 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112987 (m : nat) : (term14 m) = (term15 m).
Proof. exact (MK_COMB (@lem3112986) (@lem3112985 m)). Qed.
Lemma lem3112988 : term16 = term17.
Proof. exact (fun_ext (fun m : nat => @lem3112987 m)). Qed.
Lemma lem3112989 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112990 : term18 = term19.
Proof. exact (MK_COMB (@lem3112989) (@lem3112988)). Qed.
Lemma lem3112991 : term19.
Proof. exact (EQ_MP (@lem3112990) (@lem2538105)). Qed.
Lemma lem3113006 (n : int) : term20 n.
Proof. exact (@lem2740831 n). Qed.
Lemma lem3113007 (n : int) : (term20 n) = (term21 n).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem3113008 (n : int) : term21 n.
Proof. exact (EQ_MP (@lem3113007 n) (@lem3113006 n)). Qed.
Lemma lem3113009 (n : int) (d : int) : term22 n d.
Proof. exact (@lem3113008 n d). Qed.
Lemma lem3113010 (d : int) (n : int) : (term22 n d) = (term23 d n).
Proof. exact (eq_refl (term22 n d)). Qed.
Lemma lem3113011 (d : int) (n : int) : term23 d n.
Proof. exact (EQ_MP (@lem3113010 d n) (@lem3113009 n d)). Qed.
Lemma lem3113012 (d : int) (n : int) (e : int) : term24 d n e.
Proof. exact (@lem3113011 d n e). Qed.
Lemma lem3113013 (d : int) (e : int) (n : int) : (term24 d n e) = (term25 d e n).
Proof. exact (eq_refl (term24 d n e)). Qed.
Lemma lem3113014 (d : int) (e : int) (n : int) : term25 d e n.
Proof. exact (EQ_MP (@lem3113013 d e n) (@lem3113012 d n e)). Qed.
Lemma lem3113015 (d : int) (e : int) (n : int) : (term25 d e n) = ((term25 d e n) = True).
Proof. exact (@lem7 (term25 d e n)). Qed.
Lemma lem3113017 (m : nat) : term26 m.
Proof. exact (@lem3112977 m). Qed.
Lemma lem3113018 (m : nat) : (term26 m) = (term5 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem3113019 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem3113018 m) (@lem3113017 m)). Qed.
Lemma lem3113020 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem3113019 m n). Qed.
Lemma lem3113021 (m : nat) (n : nat) : (term27 m n) = ((term1 m n) = (term0 m n)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem3113023 (a : nat) : term28 a.
Proof. exact (@lem2836659 a). Qed.
Lemma lem3113024 (a : nat) : (term28 a) = (term29 a).
Proof. exact (eq_refl (term28 a)). Qed.
Lemma lem3113025 (a : nat) : term29 a.
Proof. exact (EQ_MP (@lem3113024 a) (@lem3113023 a)). Qed.
Lemma lem3113026 (a : nat) (b : nat) : term30 a b.
Proof. exact (@lem3113025 a b). Qed.
Lemma lem3113027 (a : nat) (b : nat) : (term30 a b) = ((num_divides a b) = (term31 a b)).
Proof. exact (eq_refl (term30 a b)). Qed.
Lemma lem3113029 (m : nat) : term32 m.
Proof. exact (@lem3112991 m). Qed.
Lemma lem3113030 (m : nat) : (term32 m) = (term15 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem3113031 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem3113030 m) (@lem3113029 m)). Qed.
Lemma lem3113032 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem3113031 m n). Qed.
Lemma lem3113033 (m : nat) (n : nat) : (term33 m n) = ((term11 m n) = (term10 m n)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem3113056 (a : nat) (b : nat) : (num_divides a b) = (term31 a b).
Proof. exact (EQ_MP (@lem3113027 a b) (@lem3113026 a b)). Qed.
Lemma lem3113057 (d : nat) (n : nat) : (num_divides d n) = (term31 d n).
Proof. exact (@lem3113056 d n). Qed.
Lemma lem3113058 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3113059 (d : nat) (n : nat) : (term34 d n) = (term35 d n).
Proof. exact (MK_COMB (@lem3113058) (@lem3113057 d n)). Qed.
Lemma lem3113065 (a : nat) (b : nat) : (num_divides a b) = (term31 a b).
Proof. exact (EQ_MP (@lem3113027 a b) (@lem3113026 a b)). Qed.
Lemma lem3113066 (e : nat) (n : nat) (d : nat) : (term36 e n d) = (term37 e n d).
Proof. exact (@lem3113065 e (Nat.div n d)). Qed.
Lemma lem3113068 (m : nat) (n : nat) : (term11 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem3113033 m n) (@lem3113032 m n)). Qed.
Lemma lem3113069 (n : nat) (d : nat) : (term11 n d) = (term10 n d).
Proof. exact (@lem3113068 n d). Qed.
Lemma lem3113070 (e : nat) : (term38 e) = (term38 e).
Proof. exact (eq_refl (term38 e)). Qed.
Lemma lem3113071 (e : nat) (n : nat) (d : nat) : (term37 e n d) = (term39 e n d).
Proof. exact (MK_COMB (@lem3113070 e) (@lem3113069 n d)). Qed.
Lemma lem3113072 (e : nat) (n : nat) (d : nat) : (term36 e n d) = (term39 e n d).
Proof. exact (TRANS (@lem3113066 e n d) (@lem3113071 e n d)). Qed.
Lemma lem3113073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3113074 (e : nat) (n : nat) (d : nat) : (term40 e n d) = (term41 e n d).
Proof. exact (MK_COMB (@lem3113073) (@lem3113072 e n d)). Qed.
Lemma lem3113076 (a : nat) (b : nat) : (num_divides a b) = (term31 a b).
Proof. exact (EQ_MP (@lem3113027 a b) (@lem3113026 a b)). Qed.
Lemma lem3113077 (d : nat) (e : nat) (n : nat) : (term42 d e n) = (term43 d e n).
Proof. exact (@lem3113076 (Nat.mul d e) n). Qed.
Lemma lem3113079 (m : nat) (n : nat) : (term1 m n) = (term0 m n).
Proof. exact (EQ_MP (@lem3113021 m n) (@lem3113020 m n)). Qed.
Lemma lem3113080 (d : nat) (e : nat) : (term1 d e) = (term0 d e).
Proof. exact (@lem3113079 d e). Qed.
Lemma lem3113081 : int_divides = int_divides.
Proof. exact (eq_refl int_divides). Qed.
Lemma lem3113082 (d : nat) (e : nat) : (term44 d e) = (term45 d e).
Proof. exact (MK_COMB (@lem3113081) (@lem3113080 d e)). Qed.
Lemma lem3113083 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem3113084 (d : nat) (e : nat) (n : nat) : (term43 d e n) = (term46 d e n).
Proof. exact (MK_COMB (@lem3113082 d e) (@lem3113083 n)). Qed.
Lemma lem3113085 (d : nat) (e : nat) (n : nat) : (term42 d e n) = (term46 d e n).
Proof. exact (TRANS (@lem3113077 d e n) (@lem3113084 d e n)). Qed.
Lemma lem3113086 (d : nat) (e : nat) (n : nat) : ((term36 e n d) = (term42 d e n)) = ((term39 e n d) = (term46 d e n)).
Proof. exact (MK_COMB (@lem3113074 e n d) (@lem3113085 d e n)). Qed.
Lemma lem3113091 (d : nat) (e : nat) (n : nat) : (term47 d e n) = (term48 d e n).
Proof. exact (MK_COMB (@lem3113059 d n) (@lem3113086 d e n)). Qed.
Lemma lem3113093 (d : int) (e : int) (n : int) : (term25 d e n) = True.
Proof. exact (EQ_MP (@lem3113015 d e n) (@lem3113014 d e n)). Qed.
Lemma lem3113094 (d : nat) (e : nat) (n : nat) : (term48 d e n) = True.
Proof. exact (@lem3113093 (int_of_num d) (int_of_num e) (int_of_num n)). Qed.
Lemma lem3113095 (d : nat) (e : nat) (n : nat) : (term47 d e n) = True.
Proof. exact (TRANS (@lem3113091 d e n) (@lem3113094 d e n)). Qed.
Lemma lem3113096 (d : nat) (n : nat) : (term49 d n) = term50.
Proof. exact (fun_ext (fun e : nat => @lem3113095 d e n)). Qed.
Lemma lem3113097 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3113098 (d : nat) (n : nat) : (term51 d n) = term52.
Proof. exact (MK_COMB (@lem3113097) (@lem3113096 d n)). Qed.
Lemma lem3113100 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3113101 (t : Prop) : (term54 t) = t.
Proof. exact (@lem3113100 nat t). Qed.
Lemma lem3113102 : term52 = True.
Proof. exact (@lem3113101 True). Qed.
Lemma lem3113103 (d : nat) (n : nat) : (term51 d n) = True.
Proof. exact (TRANS (@lem3113098 d n) (@lem3113102)). Qed.
Lemma lem3113104 (n : nat) : (term55 n) = term50.
Proof. exact (fun_ext (fun d : nat => @lem3113103 d n)). Qed.
Lemma lem3113105 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3113106 (n : nat) : (term56 n) = term52.
Proof. exact (MK_COMB (@lem3113105) (@lem3113104 n)). Qed.
Lemma lem3113108 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3113109 (t : Prop) : (term54 t) = t.
Proof. exact (@lem3113108 nat t). Qed.
Lemma lem3113110 : term52 = True.
Proof. exact (@lem3113109 True). Qed.
Lemma lem3113111 (n : nat) : (term56 n) = True.
Proof. exact (TRANS (@lem3113106 n) (@lem3113110)). Qed.
Lemma lem3113112 : term57 = term50.
Proof. exact (fun_ext (fun n : nat => @lem3113111 n)). Qed.
Lemma lem3113113 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3113114 : term58 = term52.
Proof. exact (MK_COMB (@lem3113113) (@lem3113112)). Qed.
Lemma lem3113116 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3113117 (t : Prop) : (term54 t) = t.
Proof. exact (@lem3113116 nat t). Qed.
Lemma lem3113118 : term52 = True.
Proof. exact (@lem3113117 True). Qed.
Lemma lem3113119 : term58 = True.
Proof. exact (TRANS (@lem3113114) (@lem3113118)). Qed.
Lemma lem3113120 : True = term58.
Proof. exact (SYM (@lem3113119)). Qed.
Lemma lem3113121 : term58.
Proof. exact (EQ_MP (@lem3113120) (@lem0)). Qed.
