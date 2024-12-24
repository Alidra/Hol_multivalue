Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_NUM_MIN_term_abbrevs.
Require Import COND_RAND_spec.
Require Import MIN_spec.
Require Import real_min_spec.
Require Import thm0_spec.
Require Import thm1340282_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1483915 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) (h1 : (term0 A B f b x y) = (term1 A B b x f y)) : (term0 A B f b x y) = (term1 A B b x f y).
Proof. exact (h1). Qed.
Lemma lem1483916 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) (h1 : (term0 A B f b x y) = (term1 A B b x f y)) : (term1 A B b x f y) = (term0 A B f b x y).
Proof. exact (SYM (@lem1483915 A B b x f y h1)). Qed.
Lemma lem1483917 {A B : Type'} (f : A -> B) (b : Prop) (x : A) (y : A) (h1 : (term1 A B b x f y) = (term0 A B f b x y)) : (term1 A B b x f y) = (term0 A B f b x y).
Proof. exact (h1). Qed.
Lemma lem1483918 {A B : Type'} (f : A -> B) (b : Prop) (x : A) (y : A) (h1 : (term1 A B b x f y) = (term0 A B f b x y)) : (term0 A B f b x y) = (term1 A B b x f y).
Proof. exact (SYM (@lem1483917 A B f b x y h1)). Qed.
Lemma lem1483919 {A B : Type'} (f : A -> B) (b : Prop) (x : A) (y : A) : ((term0 A B f b x y) = (term1 A B b x f y)) = ((term1 A B b x f y) = (term0 A B f b x y)).
Proof. exact (prop_ext (fun h1 : (term0 A B f b x y) = (term1 A B b x f y) => @lem1483916 A B b x f y h1) (fun h1 : (term1 A B b x f y) = (term0 A B f b x y) => @lem1483918 A B f b x y h1)). Qed.
Lemma lem1483920 {A B : Type'} (f : A -> B) (b : Prop) (x : A) : (term2 A B b x f) = (term3 A B f b x).
Proof. exact (fun_ext (fun y : A => @lem1483919 A B f b x y)). Qed.
Lemma lem1483921 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1483922 {A B : Type'} (f : A -> B) (b : Prop) (x : A) : (term4 A B b x f) = (term5 A B f b x).
Proof. exact (MK_COMB (@lem1483921 A) (@lem1483920 A B f b x)). Qed.
Lemma lem1483923 {A B : Type'} (f : A -> B) (b : Prop) : (term6 A B b f) = (term7 A B f b).
Proof. exact (fun_ext (fun x : A => @lem1483922 A B f b x)). Qed.
Lemma lem1483924 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1483925 {A B : Type'} (f : A -> B) (b : Prop) : (term8 A B b f) = (term9 A B f b).
Proof. exact (MK_COMB (@lem1483924 A) (@lem1483923 A B f b)). Qed.
Lemma lem1483926 {A B : Type'} (b : Prop) : (term10 A B b) = (term11 A B b).
Proof. exact (fun_ext (fun f : A -> B => @lem1483925 A B f b)). Qed.
Lemma lem1483927 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1483928 {A B : Type'} (b : Prop) : (term12 A B b) = (term13 A B b).
Proof. exact (MK_COMB (@lem1483927 A B) (@lem1483926 A B b)). Qed.
Lemma lem1483929 {A B : Type'} : (term14 A B) = (term15 A B).
Proof. exact (fun_ext (fun b : Prop => @lem1483928 A B b)). Qed.
Lemma lem1483930 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1483931 {A B : Type'} : (term16 A B) = (term17 A B).
Proof. exact (MK_COMB (@lem1483930) (@lem1483929 A B)). Qed.
Lemma lem1483932 {A B : Type'} : term17 A B.
Proof. exact (EQ_MP (@lem1483931 A B) (@lem12958 A B)). Qed.
Lemma lem1483933 {A B : Type'} (b : Prop) : term18 A B b.
Proof. exact (@lem1483932 A B b). Qed.
Lemma lem1483934 {A B : Type'} (b : Prop) : (term18 A B b) = (term13 A B b).
Proof. exact (eq_refl (term18 A B b)). Qed.
Lemma lem1483935 {A B : Type'} (b : Prop) : term13 A B b.
Proof. exact (EQ_MP (@lem1483934 A B b) (@lem1483933 A B b)). Qed.
Lemma lem1483936 {A B : Type'} (b : Prop) (f : A -> B) : term19 A B b f.
Proof. exact (@lem1483935 A B b f). Qed.
Lemma lem1483937 {A B : Type'} (f : A -> B) (b : Prop) : (term19 A B b f) = (term9 A B f b).
Proof. exact (eq_refl (term19 A B b f)). Qed.
Lemma lem1483938 {A B : Type'} (f : A -> B) (b : Prop) : term9 A B f b.
Proof. exact (EQ_MP (@lem1483937 A B f b) (@lem1483936 A B b f)). Qed.
Lemma lem1483939 {A B : Type'} (f : A -> B) (b : Prop) (x : A) : term20 A B f b x.
Proof. exact (@lem1483938 A B f b x). Qed.
Lemma lem1483940 {A B : Type'} (f : A -> B) (b : Prop) (x : A) : (term20 A B f b x) = (term5 A B f b x).
Proof. exact (eq_refl (term20 A B f b x)). Qed.
Lemma lem1483941 {A B : Type'} (f : A -> B) (b : Prop) (x : A) : term5 A B f b x.
Proof. exact (EQ_MP (@lem1483940 A B f b x) (@lem1483939 A B f b x)). Qed.
Lemma lem1483942 {A B : Type'} (f : A -> B) (b : Prop) (x : A) (y : A) : term21 A B f b x y.
Proof. exact (@lem1483941 A B f b x y). Qed.
Lemma lem1483943 {A B : Type'} (f : A -> B) (b : Prop) (x : A) (y : A) : (term21 A B f b x y) = ((term1 A B b x f y) = (term0 A B f b x y)).
Proof. exact (eq_refl (term21 A B f b x y)). Qed.
Lemma lem1483945 (m : real) : term22 m.
Proof. exact (@lem1346200 m). Qed.
Lemma lem1483946 (m : real) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem1483947 (m : real) : term23 m.
Proof. exact (EQ_MP (@lem1483946 m) (@lem1483945 m)). Qed.
Lemma lem1483948 (m : real) (n : real) : term24 m n.
Proof. exact (@lem1483947 m n). Qed.
Lemma lem1483949 (m : real) (n : real) : (term24 m n) = ((real_min m n) = (term25 m n)).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem1483951 (m : nat) : term26 m.
Proof. exact (@lem90961 m). Qed.
Lemma lem1483952 (m : nat) : (term26 m) = (term27 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem1483953 (m : nat) : term27 m.
Proof. exact (EQ_MP (@lem1483952 m) (@lem1483951 m)). Qed.
Lemma lem1483954 (m : nat) (n : nat) : term28 m n.
Proof. exact (@lem1483953 m n). Qed.
Lemma lem1483955 (m : nat) (n : nat) : (term28 m n) = ((Nat.min m n) = (term29 m n)).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem1483957 (m : nat) : term30 m.
Proof. exact (@lem1340282 m). Qed.
Lemma lem1483958 (m : nat) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem1483959 (m : nat) : term31 m.
Proof. exact (EQ_MP (@lem1483958 m) (@lem1483957 m)). Qed.
Lemma lem1483960 (m : nat) (n : nat) : term32 m n.
Proof. exact (@lem1483959 m n). Qed.
Lemma lem1483961 (m : nat) (n : nat) : (term32 m n) = ((term33 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1483974 (m : real) (n : real) : (real_min m n) = (term25 m n).
Proof. exact (EQ_MP (@lem1483949 m n) (@lem1483948 m n)). Qed.
Lemma lem1483975 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (@lem1483974 (real_of_num m) (real_of_num n)). Qed.
Lemma lem1483977 {A B : Type'} (f : A -> B) (b : Prop) (x : A) (y : A) : (term1 A B b x f y) = (term0 A B f b x y).
Proof. exact (EQ_MP (@lem1483943 A B f b x y) (@lem1483942 A B f b x y)). Qed.
Lemma lem1483978 (f : nat -> real) (b : Prop) (x : nat) (y : nat) : (term36 b x f y) = (term37 f b x y).
Proof. exact (@lem1483977 nat real f b x y). Qed.
Lemma lem1483979 (m : nat) (n : nat) : (term35 m n) = (term38 m n).
Proof. exact (@lem1483978 real_of_num (term33 m n) m n). Qed.
Lemma lem1483980 (m : nat) (n : nat) : (term34 m n) = (term38 m n).
Proof. exact (TRANS (@lem1483975 m n) (@lem1483979 m n)). Qed.
Lemma lem1483984 (m : nat) (n : nat) : (term33 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1483961 m n) (@lem1483960 m n)). Qed.
Lemma lem1483985 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem1483986 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem1483985) (@lem1483984 m n)). Qed.
Lemma lem1483987 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1483988 (n : nat) (m : nat) : (term41 n m) = (term42 n m).
Proof. exact (MK_COMB (@lem1483986 m n) (@lem1483987 m)). Qed.
Lemma lem1483989 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1483990 (m : nat) (n : nat) : (term43 m n) = (term29 m n).
Proof. exact (MK_COMB (@lem1483988 n m) (@lem1483989 n)). Qed.
Lemma lem1483993 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1483994 (m : nat) (n : nat) : (term38 m n) = (term44 m n).
Proof. exact (MK_COMB (@lem1483993) (@lem1483990 m n)). Qed.
Lemma lem1483995 (m : nat) (n : nat) : (term34 m n) = (term44 m n).
Proof. exact (TRANS (@lem1483980 m n) (@lem1483994 m n)). Qed.
Lemma lem1483996 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1483997 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (MK_COMB (@lem1483996) (@lem1483995 m n)). Qed.
Lemma lem1483999 (m : nat) (n : nat) : (Nat.min m n) = (term29 m n).
Proof. exact (EQ_MP (@lem1483955 m n) (@lem1483954 m n)). Qed.
Lemma lem1484002 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1484003 (m : nat) (n : nat) : (term47 m n) = (term44 m n).
Proof. exact (MK_COMB (@lem1484002) (@lem1483999 m n)). Qed.
Lemma lem1484004 (m : nat) (n : nat) : ((term34 m n) = (term47 m n)) = ((term44 m n) = (term44 m n)).
Proof. exact (MK_COMB (@lem1483997 m n) (@lem1484003 m n)). Qed.
Lemma lem1484006 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1484007 (x : real) : (x = x) = True.
Proof. exact (@lem1484006 real x). Qed.
Lemma lem1484008 (m : nat) (n : nat) : ((term44 m n) = (term44 m n)) = True.
Proof. exact (@lem1484007 (term44 m n)). Qed.
Lemma lem1484009 (m : nat) (n : nat) : ((term34 m n) = (term47 m n)) = True.
Proof. exact (TRANS (@lem1484004 m n) (@lem1484008 m n)). Qed.
Lemma lem1484010 (m : nat) : (term48 m) = term49.
Proof. exact (fun_ext (fun n : nat => @lem1484009 m n)). Qed.
Lemma lem1484011 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1484012 (m : nat) : (term50 m) = term51.
Proof. exact (MK_COMB (@lem1484011) (@lem1484010 m)). Qed.
Lemma lem1484014 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1484015 (t : Prop) : (term53 t) = t.
Proof. exact (@lem1484014 nat t). Qed.
Lemma lem1484016 : term51 = True.
Proof. exact (@lem1484015 True). Qed.
Lemma lem1484017 (m : nat) : (term50 m) = True.
Proof. exact (TRANS (@lem1484012 m) (@lem1484016)). Qed.
Lemma lem1484018 : term54 = term49.
Proof. exact (fun_ext (fun m : nat => @lem1484017 m)). Qed.
Lemma lem1484019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1484020 : term55 = term51.
Proof. exact (MK_COMB (@lem1484019) (@lem1484018)). Qed.
Lemma lem1484022 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1484023 (t : Prop) : (term53 t) = t.
Proof. exact (@lem1484022 nat t). Qed.
Lemma lem1484024 : term51 = True.
Proof. exact (@lem1484023 True). Qed.
Lemma lem1484025 : term55 = True.
Proof. exact (TRANS (@lem1484020) (@lem1484024)). Qed.
Lemma lem1484026 : True = term55.
Proof. exact (SYM (@lem1484025)). Qed.
Lemma lem1484027 : term55.
Proof. exact (EQ_MP (@lem1484026) (@lem0)). Qed.
