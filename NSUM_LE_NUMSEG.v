Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_LE_NUMSEG_term_abbrevs.
Require Import FINITE_NUMSEG_spec.
Require Import IN_NUMSEG_spec.
Require Import NSUM_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7040858 (m : nat) : term0 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7040859 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7040860 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7040859 m) (@lem7040858 m)). Qed.
Lemma lem7040861 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7040860 m n). Qed.
Lemma lem7040862 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7040863 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7040862 m n) (@lem7040861 m n)). Qed.
Lemma lem7040864 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem7040863 m n p). Qed.
Lemma lem7040865 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 p m n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem7040867 (m : nat) : term7 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7040868 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem7040869 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem7040868 m) (@lem7040867 m)). Qed.
Lemma lem7040870 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem7040869 m n). Qed.
Lemma lem7040871 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem7040872 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem7040871 m n) (@lem7040870 m n)). Qed.
Lemma lem7040873 (m : nat) (n : nat) : (term10 m n) = ((term10 m n) = True).
Proof. exact (@lem7 (term10 m n)). Qed.
Lemma lem7040875 {_127006 : Type'} (f : _127006 -> nat) : term11 _127006 f.
Proof. exact (@lem6933015 _127006 f). Qed.
Lemma lem7040876 {_127006 : Type'} (f : _127006 -> nat) : (term11 _127006 f) = (term12 _127006 f).
Proof. exact (eq_refl (term11 _127006 f)). Qed.
Lemma lem7040877 {_127006 : Type'} (f : _127006 -> nat) : term12 _127006 f.
Proof. exact (EQ_MP (@lem7040876 _127006 f) (@lem7040875 _127006 f)). Qed.
Lemma lem7040878 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : term13 _127006 f g.
Proof. exact (@lem7040877 _127006 f g). Qed.
Lemma lem7040879 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term13 _127006 f g) = (term14 _127006 f g).
Proof. exact (eq_refl (term13 _127006 f g)). Qed.
Lemma lem7040880 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : term14 _127006 f g.
Proof. exact (EQ_MP (@lem7040879 _127006 f g) (@lem7040878 _127006 f g)). Qed.
Lemma lem7040881 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (s : _127006 -> Prop) : term15 _127006 f g s.
Proof. exact (@lem7040880 _127006 f g s). Qed.
Lemma lem7040882 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term15 _127006 f g s) = (term16 _127006 f s g).
Proof. exact (eq_refl (term15 _127006 f g s)). Qed.
Lemma lem7040883 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : term16 _127006 f s g.
Proof. exact (EQ_MP (@lem7040882 _127006 f s g) (@lem7040881 _127006 f g s)). Qed.
Lemma lem7040884 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term17 _127006 s f g) : term17 _127006 s f g.
Proof. exact (h1). Qed.
Lemma lem7040885 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term17 _127006 s f g) : term18 _127006 f s g.
Proof. exact (@lem7040883 _127006 f s g (@lem7040884 _127006 s f g h1)). Qed.
Lemma lem7040886 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term18 _127006 f s g) = ((term18 _127006 f s g) = True).
Proof. exact (@lem7 (term18 _127006 f s g)). Qed.
Lemma lem7040887 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term17 _127006 s f g) : (term18 _127006 f s g) = True.
Proof. exact (EQ_MP (@lem7040886 _127006 f s g) (@lem7040885 _127006 s f g h1)). Qed.
Lemma lem7040912 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term19 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7040913 (p : Prop) (q : Prop) (p' : Prop) : term20 p q p'.
Proof. exact (fun q' : Prop => @lem7040912 p q p' q'). Qed.
Lemma lem7040914 (p : Prop) (q : Prop) : term21 p q.
Proof. exact (fun p' : Prop => @lem7040913 p q p'). Qed.
Lemma lem7040915 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : term22 f m n g.
Proof. exact (@lem7040914 (term23 m n f g) (term24 f m n g)). Qed.
Lemma lem7040916 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (p' : Prop) : term25 f m n g p'.
Proof. exact (@lem7040915 f m n g p'). Qed.
Lemma lem7040917 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (p' : Prop) : (term25 f m n g p') = (term26 f m n g p').
Proof. exact (eq_refl (term25 f m n g p')). Qed.
Lemma lem7040918 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (p' : Prop) : term26 f m n g p'.
Proof. exact (EQ_MP (@lem7040917 f m n g p') (@lem7040916 f m n g p')). Qed.
Lemma lem7040919 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (p' : Prop) (q' : Prop) : term27 f m n g p' q'.
Proof. exact (@lem7040918 f m n g p' q'). Qed.
Lemma lem7040920 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (p' : Prop) (q' : Prop) : (term27 f m n g p' q') = (term28 f m n g p' q').
Proof. exact (eq_refl (term27 f m n g p' q')). Qed.
Lemma lem7040921 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (p' : Prop) (q' : Prop) : term28 f m n g p' q'.
Proof. exact (EQ_MP (@lem7040920 f m n g p' q') (@lem7040919 f m n g p' q')). Qed.
Lemma lem7040957 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : (term23 m n f g) = (term23 m n f g).
Proof. exact (eq_refl (term23 m n f g)). Qed.
Lemma lem7040958 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (q' : Prop) : term29 m n f g q'.
Proof. exact (@lem7040921 f m n g (term23 m n f g) q'). Qed.
Lemma lem7040959 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (q' : Prop) : term30 m n f g q'.
Proof. exact (@lem7040958 m n f g q' (@lem7040957 m n f g)). Qed.
Lemma lem7040960 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : term23 m n f g.
Proof. exact (h1). Qed.
Lemma lem7040961 (i : nat) (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : term31 m n f g i.
Proof. exact (@lem7040960 m n f g h1 i). Qed.
Lemma lem7040962 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (i : nat) : (term31 m n f g i) = (term32 m n f g i).
Proof. exact (eq_refl (term31 m n f g i)). Qed.
Lemma lem7040963 (i : nat) (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : term32 m n f g i.
Proof. exact (EQ_MP (@lem7040962 m n f g i) (@lem7040961 i m n f g h1)). Qed.
Lemma lem7040964 (m : nat) (i : nat) (n : nat) (h1 : term6 m i n) : term6 m i n.
Proof. exact (h1). Qed.
Lemma lem7040965 (f : nat -> nat) (g : nat -> nat) (m : nat) (i : nat) (n : nat) (h1 : term23 m n f g) (h2 : term6 m i n) : term33 f g i.
Proof. exact (@lem7040963 i m n f g h1 (@lem7040964 m i n h2)). Qed.
Lemma lem7040966 (f : nat -> nat) (g : nat -> nat) (i : nat) : (term33 f g i) = ((term33 f g i) = True).
Proof. exact (@lem7 (term33 f g i)). Qed.
Lemma lem7040967 (f : nat -> nat) (g : nat -> nat) (m : nat) (i : nat) (n : nat) (h1 : term23 m n f g) (h2 : term6 m i n) : (term33 f g i) = True.
Proof. exact (EQ_MP (@lem7040966 f g i) (@lem7040965 f g m i n h1 h2)). Qed.
Lemma lem7040974 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : term34 _127006 f s g.
Proof. exact (fun h0 : term17 _127006 s f g => @lem7040887 _127006 s f g h0). Qed.
Lemma lem7040975 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : term35 f s g.
Proof. exact (@lem7040974 nat f s g). Qed.
Lemma lem7040976 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : term36 f m n g.
Proof. exact (@lem7040975 f (dotdot m n) g). Qed.
Lemma lem7040980 (m : nat) (n : nat) : (term10 m n) = True.
Proof. exact (EQ_MP (@lem7040873 m n) (@lem7040872 m n)). Qed.
Lemma lem7040981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7040982 (m : nat) (n : nat) : (term37 m n) = (and True).
Proof. exact (MK_COMB (@lem7040981) (@lem7040980 m n)). Qed.
Lemma lem7040990 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term19 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7040991 (p : Prop) (q : Prop) (p' : Prop) : term20 p q p'.
Proof. exact (fun q' : Prop => @lem7040990 p q p' q'). Qed.
Lemma lem7040992 (p : Prop) (q : Prop) : term21 p q.
Proof. exact (fun p' : Prop => @lem7040991 p q p'). Qed.
Lemma lem7040993 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (x : nat) : term38 m n f g x.
Proof. exact (@lem7040992 (term5 x m n) (term33 f g x)). Qed.
Lemma lem7040994 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (x : nat) (p' : Prop) : term39 m n f g x p'.
Proof. exact (@lem7040993 m n f g x p'). Qed.
Lemma lem7040995 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (x : nat) (p' : Prop) : (term39 m n f g x p') = (term40 m n f g x p').
Proof. exact (eq_refl (term39 m n f g x p')). Qed.
Lemma lem7040996 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (x : nat) (p' : Prop) : term40 m n f g x p'.
Proof. exact (EQ_MP (@lem7040995 m n f g x p') (@lem7040994 m n f g x p')). Qed.
Lemma lem7040997 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (x : nat) (p' : Prop) (q' : Prop) : term41 m n f g x p' q'.
Proof. exact (@lem7040996 m n f g x p' q'). Qed.
Lemma lem7040998 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (x : nat) (p' : Prop) (q' : Prop) : (term41 m n f g x p' q') = (term42 m n f g x p' q').
Proof. exact (eq_refl (term41 m n f g x p' q')). Qed.
Lemma lem7040999 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (x : nat) (p' : Prop) (q' : Prop) : term42 m n f g x p' q'.
Proof. exact (EQ_MP (@lem7040998 m n f g x p' q') (@lem7040997 m n f g x p' q')). Qed.
Lemma lem7041001 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7040865 m p n) (@lem7040864 m n p)). Qed.
Lemma lem7041002 (m : nat) (x : nat) (n : nat) : (term5 x m n) = (term6 m x n).
Proof. exact (@lem7041001 m x n). Qed.
Lemma lem7041005 (f : nat -> nat) (g : nat -> nat) (m : nat) (x : nat) (n : nat) (q' : Prop) : term43 f g m x n q'.
Proof. exact (@lem7040999 m n f g x (term6 m x n) q'). Qed.
Lemma lem7041006 (f : nat -> nat) (g : nat -> nat) (m : nat) (x : nat) (n : nat) (q' : Prop) : term44 f g m x n q'.
Proof. exact (@lem7041005 f g m x n q' (@lem7041002 m x n)). Qed.
Lemma lem7041007 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : term6 m x n.
Proof. exact (h1). Qed.
Lemma lem7041008 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : Peano.le x n.
Proof. exact (proj2 (@lem7041007 m x n h1)). Qed.
Lemma lem7041009 (x : nat) (n : nat) : (Peano.le x n) = ((Peano.le x n) = True).
Proof. exact (@lem7 (Peano.le x n)). Qed.
Lemma lem7041011 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : Peano.le m x.
Proof. exact (proj1 (@lem7041007 m x n h1)). Qed.
Lemma lem7041012 (m : nat) (x : nat) : (Peano.le m x) = ((Peano.le m x) = True).
Proof. exact (@lem7 (Peano.le m x)). Qed.
Lemma lem7041015 (i : nat) (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : term45 m n f g i.
Proof. exact (fun h0 : term6 m i n => @lem7040967 f g m i n h1 h0). Qed.
Lemma lem7041016 (x : nat) (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : term45 m n f g x.
Proof. exact (@lem7041015 x m n f g h1). Qed.
Lemma lem7041020 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (Peano.le m x) = True.
Proof. exact (EQ_MP (@lem7041012 m x) (@lem7041011 m x n h1)). Qed.
Lemma lem7041021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7041022 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term46 m x) = (and True).
Proof. exact (MK_COMB (@lem7041021) (@lem7041020 m x n h1)). Qed.
Lemma lem7041024 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (Peano.le x n) = True.
Proof. exact (EQ_MP (@lem7041009 x n) (@lem7041008 m x n h1)). Qed.
Lemma lem7041025 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term6 m x n) = (True /\ True).
Proof. exact (MK_COMB (@lem7041022 m x n h1) (@lem7041024 m x n h1)). Qed.
Lemma lem7041027 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7041028 : (True /\ True) = True.
Proof. exact (@lem7041027 True). Qed.
Lemma lem7041029 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term6 m x n) = True.
Proof. exact (TRANS (@lem7041025 m x n h1) (@lem7041028)). Qed.
Lemma lem7041030 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : True = (term6 m x n).
Proof. exact (SYM (@lem7041029 m x n h1)). Qed.
Lemma lem7041031 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : term6 m x n.
Proof. exact (EQ_MP (@lem7041030 m x n h1) (@lem0)). Qed.
Lemma lem7041032 (f : nat -> nat) (g : nat -> nat) (m : nat) (x : nat) (n : nat) (h1 : term23 m n f g) (h2 : term6 m x n) : (term33 f g x) = True.
Proof. exact (@lem7041016 x m n f g h1 (@lem7041031 m x n h2)). Qed.
Lemma lem7041033 (x : nat) (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : term45 m n f g x.
Proof. exact (fun h0 : term6 m x n => @lem7041032 f g m x n h1 h0). Qed.
Lemma lem7041034 (f : nat -> nat) (g : nat -> nat) (m : nat) (x : nat) (n : nat) : term47 f g m x n.
Proof. exact (@lem7041006 f g m x n True). Qed.
Lemma lem7041035 (x : nat) (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : (term48 m n f g x) = (term49 m x n).
Proof. exact (@lem7041034 f g m x n (@lem7041033 x m n f g h1)). Qed.
Lemma lem7041037 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7041038 (m : nat) (x : nat) (n : nat) : (term49 m x n) = True.
Proof. exact (@lem7041037 (term6 m x n)). Qed.
Lemma lem7041039 (x : nat) (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : (term48 m n f g x) = True.
Proof. exact (TRANS (@lem7041035 x m n f g h1) (@lem7041038 m x n)). Qed.
Lemma lem7041040 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : (term50 m n f g) = term51.
Proof. exact (fun_ext (fun x : nat => @lem7041039 x m n f g h1)). Qed.
Lemma lem7041041 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041042 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : (term52 m n f g) = term53.
Proof. exact (MK_COMB (@lem7041041) (@lem7041040 m n f g h1)). Qed.
Lemma lem7041044 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7041045 (t : Prop) : (term55 t) = t.
Proof. exact (@lem7041044 nat t). Qed.
Lemma lem7041046 : term53 = True.
Proof. exact (@lem7041045 True). Qed.
Lemma lem7041047 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : (term52 m n f g) = True.
Proof. exact (TRANS (@lem7041042 m n f g h1) (@lem7041046)). Qed.
Lemma lem7041048 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : (term56 m n f g) = (True /\ True).
Proof. exact (MK_COMB (@lem7040982 m n) (@lem7041047 m n f g h1)). Qed.
Lemma lem7041050 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7041051 : (True /\ True) = True.
Proof. exact (@lem7041050 True). Qed.
Lemma lem7041052 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : (term56 m n f g) = True.
Proof. exact (TRANS (@lem7041048 m n f g h1) (@lem7041051)). Qed.
Lemma lem7041053 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : True = (term56 m n f g).
Proof. exact (SYM (@lem7041052 m n f g h1)). Qed.
Lemma lem7041054 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : term56 m n f g.
Proof. exact (EQ_MP (@lem7041053 m n f g h1) (@lem0)). Qed.
Lemma lem7041055 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term23 m n f g) : (term24 f m n g) = True.
Proof. exact (@lem7040976 f m n g (@lem7041054 m n f g h1)). Qed.
Lemma lem7041056 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : term57 f m n g.
Proof. exact (fun h0 : term23 m n f g => @lem7041055 m n f g h0). Qed.
Lemma lem7041057 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : term58 m n f g.
Proof. exact (@lem7040959 m n f g True). Qed.
Lemma lem7041058 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : (term59 f m n g) = (term60 m n f g).
Proof. exact (@lem7041057 m n f g (@lem7041056 f m n g)). Qed.
Lemma lem7041060 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7041061 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : (term60 m n f g) = True.
Proof. exact (@lem7041060 (term23 m n f g)). Qed.
Lemma lem7041062 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term59 f m n g) = True.
Proof. exact (TRANS (@lem7041058 m n f g) (@lem7041061 m n f g)). Qed.
Lemma lem7041063 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term61 f m g) = term51.
Proof. exact (fun_ext (fun n : nat => @lem7041062 f m n g)). Qed.
Lemma lem7041064 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041065 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term62 f m g) = term53.
Proof. exact (MK_COMB (@lem7041064) (@lem7041063 f m g)). Qed.
Lemma lem7041067 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7041068 (t : Prop) : (term55 t) = t.
Proof. exact (@lem7041067 nat t). Qed.
Lemma lem7041069 : term53 = True.
Proof. exact (@lem7041068 True). Qed.
Lemma lem7041070 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term62 f m g) = True.
Proof. exact (TRANS (@lem7041065 f m g) (@lem7041069)). Qed.
Lemma lem7041071 (f : nat -> nat) (g : nat -> nat) : (term63 f g) = term51.
Proof. exact (fun_ext (fun m : nat => @lem7041070 f m g)). Qed.
Lemma lem7041072 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041073 (f : nat -> nat) (g : nat -> nat) : (term64 f g) = term53.
Proof. exact (MK_COMB (@lem7041072) (@lem7041071 f g)). Qed.
Lemma lem7041075 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7041076 (t : Prop) : (term55 t) = t.
Proof. exact (@lem7041075 nat t). Qed.
Lemma lem7041077 : term53 = True.
Proof. exact (@lem7041076 True). Qed.
Lemma lem7041078 (f : nat -> nat) (g : nat -> nat) : (term64 f g) = True.
Proof. exact (TRANS (@lem7041073 f g) (@lem7041077)). Qed.
Lemma lem7041079 (f : nat -> nat) : (term65 f) = term66.
Proof. exact (fun_ext (fun g : nat -> nat => @lem7041078 f g)). Qed.
Lemma lem7041080 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7041081 (f : nat -> nat) : (term67 f) = term68.
Proof. exact (MK_COMB (@lem7041080) (@lem7041079 f)). Qed.
Lemma lem7041083 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7041084 (t : Prop) : (term69 t) = t.
Proof. exact (@lem7041083 (nat -> nat) t). Qed.
Lemma lem7041085 : term68 = True.
Proof. exact (@lem7041084 True). Qed.
Lemma lem7041086 (f : nat -> nat) : (term67 f) = True.
Proof. exact (TRANS (@lem7041081 f) (@lem7041085)). Qed.
Lemma lem7041087 : term70 = term66.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7041086 f)). Qed.
Lemma lem7041088 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7041089 : term71 = term68.
Proof. exact (MK_COMB (@lem7041088) (@lem7041087)). Qed.
Lemma lem7041091 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7041092 (t : Prop) : (term69 t) = t.
Proof. exact (@lem7041091 (nat -> nat) t). Qed.
Lemma lem7041093 : term68 = True.
Proof. exact (@lem7041092 True). Qed.
Lemma lem7041094 : term71 = True.
Proof. exact (TRANS (@lem7041089) (@lem7041093)). Qed.
Lemma lem7041095 : True = term71.
Proof. exact (SYM (@lem7041094)). Qed.
Lemma lem7041096 : term71.
Proof. exact (EQ_MP (@lem7041095) (@lem0)). Qed.
