Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_EQ_0_NUMSEG_term_abbrevs.
Require Import IN_NUMSEG_spec.
Require Import SUM_EQ_0_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7213835 (m : nat) : term0 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7213836 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7213837 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7213836 m) (@lem7213835 m)). Qed.
Lemma lem7213838 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7213837 m n). Qed.
Lemma lem7213839 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7213840 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7213839 m n) (@lem7213838 m n)). Qed.
Lemma lem7213841 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem7213840 m n p). Qed.
Lemma lem7213842 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 p m n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem7213844 {A : Type'} (f : A -> real) : term7 A f.
Proof. exact (@lem7069292 A f). Qed.
Lemma lem7213845 {A : Type'} (f : A -> real) : (term7 A f) = (term8 A f).
Proof. exact (eq_refl (term7 A f)). Qed.
Lemma lem7213846 {A : Type'} (f : A -> real) : term8 A f.
Proof. exact (EQ_MP (@lem7213845 A f) (@lem7213844 A f)). Qed.
Lemma lem7213847 {A : Type'} (f : A -> real) (s : A -> Prop) : term9 A f s.
Proof. exact (@lem7213846 A f s). Qed.
Lemma lem7213848 {A : Type'} (s : A -> Prop) (f : A -> real) : (term9 A f s) = (term10 A s f).
Proof. exact (eq_refl (term9 A f s)). Qed.
Lemma lem7213849 {A : Type'} (s : A -> Prop) (f : A -> real) : term10 A s f.
Proof. exact (EQ_MP (@lem7213848 A s f) (@lem7213847 A f s)). Qed.
Lemma lem7213850 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term11 A s f) : term11 A s f.
Proof. exact (h1). Qed.
Lemma lem7213851 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term11 A s f) : (@sum A s f) = term12.
Proof. exact (@lem7213849 A s f (@lem7213850 A s f h1)). Qed.
Lemma lem7213872 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term13 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7213873 (p : Prop) (q : Prop) (p' : Prop) : term14 p q p'.
Proof. exact (fun q' : Prop => @lem7213872 p q p' q'). Qed.
Lemma lem7213874 (p : Prop) (q : Prop) : term15 p q.
Proof. exact (fun p' : Prop => @lem7213873 p q p'). Qed.
Lemma lem7213875 (m : nat) (n : nat) (f : nat -> real) : term16 m n f.
Proof. exact (@lem7213874 (term17 m n f) ((term18 m n f) = term12)). Qed.
Lemma lem7213876 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) : term19 m n f p'.
Proof. exact (@lem7213875 m n f p'). Qed.
Lemma lem7213877 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) : (term19 m n f p') = (term20 m n f p').
Proof. exact (eq_refl (term19 m n f p')). Qed.
Lemma lem7213878 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) : term20 m n f p'.
Proof. exact (EQ_MP (@lem7213877 m n f p') (@lem7213876 m n f p')). Qed.
Lemma lem7213879 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : term21 m n f p' q'.
Proof. exact (@lem7213878 m n f p' q'). Qed.
Lemma lem7213880 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : (term21 m n f p' q') = (term22 m n f p' q').
Proof. exact (eq_refl (term21 m n f p' q')). Qed.
Lemma lem7213881 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : term22 m n f p' q'.
Proof. exact (EQ_MP (@lem7213880 m n f p' q') (@lem7213879 m n f p' q')). Qed.
Lemma lem7213921 (m : nat) (n : nat) (f : nat -> real) : (term17 m n f) = (term17 m n f).
Proof. exact (eq_refl (term17 m n f)). Qed.
Lemma lem7213922 (m : nat) (n : nat) (f : nat -> real) (q' : Prop) : term23 m n f q'.
Proof. exact (@lem7213881 m n f (term17 m n f) q'). Qed.
Lemma lem7213923 (m : nat) (n : nat) (f : nat -> real) (q' : Prop) : term24 m n f q'.
Proof. exact (@lem7213922 m n f q' (@lem7213921 m n f)). Qed.
Lemma lem7213924 (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : term17 m n f.
Proof. exact (h1). Qed.
Lemma lem7213925 (i : nat) (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : term25 m n f i.
Proof. exact (@lem7213924 m n f h1 i). Qed.
Lemma lem7213926 (m : nat) (n : nat) (f : nat -> real) (i : nat) : (term25 m n f i) = (term26 m n f i).
Proof. exact (eq_refl (term25 m n f i)). Qed.
Lemma lem7213927 (i : nat) (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : term26 m n f i.
Proof. exact (EQ_MP (@lem7213926 m n f i) (@lem7213925 i m n f h1)). Qed.
Lemma lem7213928 (m : nat) (i : nat) (n : nat) (h1 : term6 m i n) : term6 m i n.
Proof. exact (h1). Qed.
Lemma lem7213929 (f : nat -> real) (m : nat) (i : nat) (n : nat) (h1 : term17 m n f) (h2 : term6 m i n) : (f i) = term12.
Proof. exact (@lem7213927 i m n f h1 (@lem7213928 m i n h2)). Qed.
Lemma lem7213938 {A : Type'} (s : A -> Prop) (f : A -> real) : term10 A s f.
Proof. exact (fun h0 : term11 A s f => @lem7213851 A s f h0). Qed.
Lemma lem7213939 (s : nat -> Prop) (f : nat -> real) : term27 s f.
Proof. exact (@lem7213938 nat s f). Qed.
Lemma lem7213940 (m : nat) (n : nat) (f : nat -> real) : term28 m n f.
Proof. exact (@lem7213939 (dotdot m n) f). Qed.
Lemma lem7213948 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term13 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7213949 (p : Prop) (q : Prop) (p' : Prop) : term14 p q p'.
Proof. exact (fun q' : Prop => @lem7213948 p q p' q'). Qed.
Lemma lem7213950 (p : Prop) (q : Prop) : term15 p q.
Proof. exact (fun p' : Prop => @lem7213949 p q p'). Qed.
Lemma lem7213951 (m : nat) (n : nat) (f : nat -> real) (x : nat) : term29 m n f x.
Proof. exact (@lem7213950 (term5 x m n) ((f x) = term12)). Qed.
Lemma lem7213952 (m : nat) (n : nat) (f : nat -> real) (x : nat) (p' : Prop) : term30 m n f x p'.
Proof. exact (@lem7213951 m n f x p'). Qed.
Lemma lem7213953 (m : nat) (n : nat) (f : nat -> real) (x : nat) (p' : Prop) : (term30 m n f x p') = (term31 m n f x p').
Proof. exact (eq_refl (term30 m n f x p')). Qed.
Lemma lem7213954 (m : nat) (n : nat) (f : nat -> real) (x : nat) (p' : Prop) : term31 m n f x p'.
Proof. exact (EQ_MP (@lem7213953 m n f x p') (@lem7213952 m n f x p')). Qed.
Lemma lem7213955 (m : nat) (n : nat) (f : nat -> real) (x : nat) (p' : Prop) (q' : Prop) : term32 m n f x p' q'.
Proof. exact (@lem7213954 m n f x p' q'). Qed.
Lemma lem7213956 (m : nat) (n : nat) (f : nat -> real) (x : nat) (p' : Prop) (q' : Prop) : (term32 m n f x p' q') = (term33 m n f x p' q').
Proof. exact (eq_refl (term32 m n f x p' q')). Qed.
Lemma lem7213957 (m : nat) (n : nat) (f : nat -> real) (x : nat) (p' : Prop) (q' : Prop) : term33 m n f x p' q'.
Proof. exact (EQ_MP (@lem7213956 m n f x p' q') (@lem7213955 m n f x p' q')). Qed.
Lemma lem7213959 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7213842 m p n) (@lem7213841 m n p)). Qed.
Lemma lem7213960 (m : nat) (x : nat) (n : nat) : (term5 x m n) = (term6 m x n).
Proof. exact (@lem7213959 m x n). Qed.
Lemma lem7213963 (f : nat -> real) (m : nat) (x : nat) (n : nat) (q' : Prop) : term34 f m x n q'.
Proof. exact (@lem7213957 m n f x (term6 m x n) q'). Qed.
Lemma lem7213964 (f : nat -> real) (m : nat) (x : nat) (n : nat) (q' : Prop) : term35 f m x n q'.
Proof. exact (@lem7213963 f m x n q' (@lem7213960 m x n)). Qed.
Lemma lem7213965 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : term6 m x n.
Proof. exact (h1). Qed.
Lemma lem7213966 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : Peano.le x n.
Proof. exact (proj2 (@lem7213965 m x n h1)). Qed.
Lemma lem7213967 (x : nat) (n : nat) : (Peano.le x n) = ((Peano.le x n) = True).
Proof. exact (@lem7 (Peano.le x n)). Qed.
Lemma lem7213969 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : Peano.le m x.
Proof. exact (proj1 (@lem7213965 m x n h1)). Qed.
Lemma lem7213970 (m : nat) (x : nat) : (Peano.le m x) = ((Peano.le m x) = True).
Proof. exact (@lem7 (Peano.le m x)). Qed.
Lemma lem7213975 (i : nat) (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : term26 m n f i.
Proof. exact (fun h0 : term6 m i n => @lem7213929 f m i n h1 h0). Qed.
Lemma lem7213976 (x : nat) (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : term26 m n f x.
Proof. exact (@lem7213975 x m n f h1). Qed.
Lemma lem7213980 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (Peano.le m x) = True.
Proof. exact (EQ_MP (@lem7213970 m x) (@lem7213969 m x n h1)). Qed.
Lemma lem7213981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7213982 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term36 m x) = (and True).
Proof. exact (MK_COMB (@lem7213981) (@lem7213980 m x n h1)). Qed.
Lemma lem7213984 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (Peano.le x n) = True.
Proof. exact (EQ_MP (@lem7213967 x n) (@lem7213966 m x n h1)). Qed.
Lemma lem7213985 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term6 m x n) = (True /\ True).
Proof. exact (MK_COMB (@lem7213982 m x n h1) (@lem7213984 m x n h1)). Qed.
Lemma lem7213987 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7213988 : (True /\ True) = True.
Proof. exact (@lem7213987 True). Qed.
Lemma lem7213989 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term6 m x n) = True.
Proof. exact (TRANS (@lem7213985 m x n h1) (@lem7213988)). Qed.
Lemma lem7213990 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : True = (term6 m x n).
Proof. exact (SYM (@lem7213989 m x n h1)). Qed.
Lemma lem7213991 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : term6 m x n.
Proof. exact (EQ_MP (@lem7213990 m x n h1) (@lem0)). Qed.
Lemma lem7213992 (f : nat -> real) (m : nat) (x : nat) (n : nat) (h1 : term17 m n f) (h2 : term6 m x n) : (f x) = term12.
Proof. exact (@lem7213976 x m n f h1 (@lem7213991 m x n h2)). Qed.
Lemma lem7213993 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7213994 (f : nat -> real) (m : nat) (x : nat) (n : nat) (h1 : term17 m n f) (h2 : term6 m x n) : (term37 f x) = term38.
Proof. exact (MK_COMB (@lem7213993) (@lem7213992 f m x n h1 h2)). Qed.
Lemma lem7213995 : term12 = term12.
Proof. exact (eq_refl term12). Qed.
Lemma lem7213996 (f : nat -> real) (m : nat) (x : nat) (n : nat) (h1 : term17 m n f) (h2 : term6 m x n) : ((f x) = term12) = (term12 = term12).
Proof. exact (MK_COMB (@lem7213994 f m x n h1 h2) (@lem7213995)). Qed.
Lemma lem7213998 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7213999 (x : real) : (x = x) = True.
Proof. exact (@lem7213998 real x). Qed.
Lemma lem7214000 : (term12 = term12) = True.
Proof. exact (@lem7213999 term12). Qed.
Lemma lem7214001 (f : nat -> real) (m : nat) (x : nat) (n : nat) (h1 : term17 m n f) (h2 : term6 m x n) : ((f x) = term12) = True.
Proof. exact (TRANS (@lem7213996 f m x n h1 h2) (@lem7214000)). Qed.
Lemma lem7214002 (x : nat) (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : term39 m n f x.
Proof. exact (fun h0 : term6 m x n => @lem7214001 f m x n h1 h0). Qed.
Lemma lem7214003 (f : nat -> real) (m : nat) (x : nat) (n : nat) : term40 f m x n.
Proof. exact (@lem7213964 f m x n True). Qed.
Lemma lem7214004 (x : nat) (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : (term41 m n f x) = (term42 m x n).
Proof. exact (@lem7214003 f m x n (@lem7214002 x m n f h1)). Qed.
Lemma lem7214006 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7214007 (m : nat) (x : nat) (n : nat) : (term42 m x n) = True.
Proof. exact (@lem7214006 (term6 m x n)). Qed.
Lemma lem7214008 (x : nat) (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : (term41 m n f x) = True.
Proof. exact (TRANS (@lem7214004 x m n f h1) (@lem7214007 m x n)). Qed.
Lemma lem7214009 (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : (term43 m n f) = term44.
Proof. exact (fun_ext (fun x : nat => @lem7214008 x m n f h1)). Qed.
Lemma lem7214010 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214011 (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : (term45 m n f) = term46.
Proof. exact (MK_COMB (@lem7214010) (@lem7214009 m n f h1)). Qed.
Lemma lem7214013 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7214014 (t : Prop) : (term48 t) = t.
Proof. exact (@lem7214013 nat t). Qed.
Lemma lem7214015 : term46 = True.
Proof. exact (@lem7214014 True). Qed.
Lemma lem7214016 (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : (term45 m n f) = True.
Proof. exact (TRANS (@lem7214011 m n f h1) (@lem7214015)). Qed.
Lemma lem7214017 (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : True = (term45 m n f).
Proof. exact (SYM (@lem7214016 m n f h1)). Qed.
Lemma lem7214018 (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : term45 m n f.
Proof. exact (EQ_MP (@lem7214017 m n f h1) (@lem0)). Qed.
Lemma lem7214019 (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : (term18 m n f) = term12.
Proof. exact (@lem7213940 m n f (@lem7214018 m n f h1)). Qed.
Lemma lem7214020 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7214021 (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : (term49 m n f) = term38.
Proof. exact (MK_COMB (@lem7214020) (@lem7214019 m n f h1)). Qed.
Lemma lem7214022 : term12 = term12.
Proof. exact (eq_refl term12). Qed.
Lemma lem7214023 (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : ((term18 m n f) = term12) = (term12 = term12).
Proof. exact (MK_COMB (@lem7214021 m n f h1) (@lem7214022)). Qed.
Lemma lem7214025 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7214026 (x : real) : (x = x) = True.
Proof. exact (@lem7214025 real x). Qed.
Lemma lem7214027 : (term12 = term12) = True.
Proof. exact (@lem7214026 term12). Qed.
Lemma lem7214028 (m : nat) (n : nat) (f : nat -> real) (h1 : term17 m n f) : ((term18 m n f) = term12) = True.
Proof. exact (TRANS (@lem7214023 m n f h1) (@lem7214027)). Qed.
Lemma lem7214029 (m : nat) (n : nat) (f : nat -> real) : term50 m n f.
Proof. exact (fun h0 : term17 m n f => @lem7214028 m n f h0). Qed.
Lemma lem7214030 (m : nat) (n : nat) (f : nat -> real) : term51 m n f.
Proof. exact (@lem7213923 m n f True). Qed.
Lemma lem7214031 (m : nat) (n : nat) (f : nat -> real) : (term52 m n f) = (term53 m n f).
Proof. exact (@lem7214030 m n f (@lem7214029 m n f)). Qed.
Lemma lem7214033 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7214034 (m : nat) (n : nat) (f : nat -> real) : (term53 m n f) = True.
Proof. exact (@lem7214033 (term17 m n f)). Qed.
Lemma lem7214035 (m : nat) (n : nat) (f : nat -> real) : (term52 m n f) = True.
Proof. exact (TRANS (@lem7214031 m n f) (@lem7214034 m n f)). Qed.
Lemma lem7214036 (m : nat) (f : nat -> real) : (term54 m f) = term44.
Proof. exact (fun_ext (fun n : nat => @lem7214035 m n f)). Qed.
Lemma lem7214037 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214038 (m : nat) (f : nat -> real) : (term55 m f) = term46.
Proof. exact (MK_COMB (@lem7214037) (@lem7214036 m f)). Qed.
Lemma lem7214040 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7214041 (t : Prop) : (term48 t) = t.
Proof. exact (@lem7214040 nat t). Qed.
Lemma lem7214042 : term46 = True.
Proof. exact (@lem7214041 True). Qed.
Lemma lem7214043 (m : nat) (f : nat -> real) : (term55 m f) = True.
Proof. exact (TRANS (@lem7214038 m f) (@lem7214042)). Qed.
Lemma lem7214044 (f : nat -> real) : (term56 f) = term44.
Proof. exact (fun_ext (fun m : nat => @lem7214043 m f)). Qed.
Lemma lem7214045 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214046 (f : nat -> real) : (term57 f) = term46.
Proof. exact (MK_COMB (@lem7214045) (@lem7214044 f)). Qed.
Lemma lem7214048 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7214049 (t : Prop) : (term48 t) = t.
Proof. exact (@lem7214048 nat t). Qed.
Lemma lem7214050 : term46 = True.
Proof. exact (@lem7214049 True). Qed.
Lemma lem7214051 (f : nat -> real) : (term57 f) = True.
Proof. exact (TRANS (@lem7214046 f) (@lem7214050)). Qed.
Lemma lem7214052 : term58 = term59.
Proof. exact (fun_ext (fun f : nat -> real => @lem7214051 f)). Qed.
Lemma lem7214053 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7214054 : term60 = term61.
Proof. exact (MK_COMB (@lem7214053) (@lem7214052)). Qed.
Lemma lem7214056 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7214057 (t : Prop) : (term62 t) = t.
Proof. exact (@lem7214056 (nat -> real) t). Qed.
Lemma lem7214058 : term61 = True.
Proof. exact (@lem7214057 True). Qed.
Lemma lem7214059 : term60 = True.
Proof. exact (TRANS (@lem7214054) (@lem7214058)). Qed.
Lemma lem7214060 : True = term60.
Proof. exact (SYM (@lem7214059)). Qed.
Lemma lem7214061 : term60.
Proof. exact (EQ_MP (@lem7214060) (@lem0)). Qed.
