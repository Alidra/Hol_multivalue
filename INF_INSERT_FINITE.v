Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INF_INSERT_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INSERT_spec.
Require Import FORALL_IN_INSERT_spec.
Require Import INF_FINITE_spec.
Require Import INF_UNIQUE_FINITE_spec.
Require Import IN_INSERT_spec.
Require Import IN_SING_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_INSERT_EMPTY_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import real_min_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339240_spec.
Require Import thm1339577_spec.
Require Import thm1339697_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem5252870 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5252871 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5252872 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5252871 t1) (@lem5252870 t1)). Qed.
Lemma lem5252873 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5252872 t1 t2). Qed.
Lemma lem5252874 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5252875 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5252874 t1 t2) (@lem5252873 t1 t2)). Qed.
Lemma lem5252876 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5252875 t1 t2 t3). Qed.
Lemma lem5252877 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5252878 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5252877 t1 t2 t3) (@lem5252876 t1 t2 t3)). Qed.
Lemma lem5252879 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5252878 t1 t2 t3)). Qed.
Lemma lem5252880 (m : real) : term7 m.
Proof. exact (@lem1346200 m). Qed.
Lemma lem5252881 (m : real) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem5252882 (m : real) : term8 m.
Proof. exact (EQ_MP (@lem5252881 m) (@lem5252880 m)). Qed.
Lemma lem5252883 (m : real) (n : real) : term9 m n.
Proof. exact (@lem5252882 m n). Qed.
Lemma lem5252884 (m : real) (n : real) : (term9 m n) = ((real_min m n) = (term10 m n)).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem5252886 (x : real) : term11 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem5252887 (x : real) : (term11 x) = (real_le x x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem5252888 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem5252887 x) (@lem5252886 x)). Qed.
Lemma lem5252889 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem5252891 {A : Type'} (x : A) : term12 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem5252892 {A : Type'} (x : A) : (term12 A x) = (term13 A x).
Proof. exact (eq_refl (term12 A x)). Qed.
Lemma lem5252893 {A : Type'} (x : A) : term13 A x.
Proof. exact (EQ_MP (@lem5252892 A x) (@lem5252891 A x)). Qed.
Lemma lem5252894 {A : Type'} (x : A) (y : A) : term14 A x y.
Proof. exact (@lem5252893 A x y). Qed.
Lemma lem5252895 {A : Type'} (x : A) (y : A) : (term14 A x y) = ((term15 A x y) = (x = y)).
Proof. exact (eq_refl (term14 A x y)). Qed.
Lemma lem5252897 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5252898 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term16 _476 _475 _474 _477) = (term17 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem5252899 (_474 : real) (_475 : Prop) (x : real) (s : real -> Prop) (_477 : real) : (term18 x s _475 _474 _477) = (term19 _474 _475 x s _477).
Proof. exact (@lem5252898 _474 _475 (term20 x s) _477). Qed.
Lemma lem5252900 (x : real) (s : real -> Prop) : (term21 x s) = (term22 x s).
Proof. exact (@lem5252899 x (s = (@EMPTY real)) x s (term23 x s)). Qed.
Lemma lem5252901 (x : real) (s : real -> Prop) : (term24 x s) = ((term25 x s) = (term23 x s)).
Proof. exact (eq_refl (term24 x s)). Qed.
Lemma lem5252902 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5252903 (x : real) (s : real -> Prop) : (term27 x s) = (term28 x s).
Proof. exact (MK_COMB (@lem5252902 s) (@lem5252901 x s)). Qed.
Lemma lem5252904 (s : real -> Prop) (x : real) : (term29 s x) = ((term25 x s) = x).
Proof. exact (eq_refl (term29 s x)). Qed.
Lemma lem5252905 (s : real -> Prop) : (term30 s) = (term30 s).
Proof. exact (eq_refl (term30 s)). Qed.
Lemma lem5252906 (s : real -> Prop) (x : real) : (term31 s x) = (term32 s x).
Proof. exact (MK_COMB (@lem5252905 s) (@lem5252904 s x)). Qed.
Lemma lem5252907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5252908 (s : real -> Prop) (x : real) : (term33 s x) = (term34 s x).
Proof. exact (MK_COMB (@lem5252907) (@lem5252906 s x)). Qed.
Lemma lem5252909 (x : real) (s : real -> Prop) : (term22 x s) = (term35 x s).
Proof. exact (MK_COMB (@lem5252908 s x) (@lem5252903 x s)). Qed.
Lemma lem5252910 (x : real) (s : real -> Prop) : (term21 x s) = ((term25 x s) = (term36 x s)).
Proof. exact (eq_refl (term21 x s)). Qed.
Lemma lem5252911 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5252912 (x : real) (s : real -> Prop) : (term37 x s) = (term38 x s).
Proof. exact (MK_COMB (@lem5252911) (@lem5252910 x s)). Qed.
Lemma lem5252913 (x : real) (s : real -> Prop) : ((term21 x s) = (term22 x s)) = (((term25 x s) = (term36 x s)) = (term35 x s)).
Proof. exact (MK_COMB (@lem5252912 x s) (@lem5252909 x s)). Qed.
Lemma lem5252914 (x : real) (s : real -> Prop) : ((term25 x s) = (term36 x s)) = (term35 x s).
Proof. exact (EQ_MP (@lem5252913 x s) (@lem5252900 x s)). Qed.
Lemma lem5252915 (x : real) (s : real -> Prop) : (term35 x s) = ((term25 x s) = (term36 x s)).
Proof. exact (SYM (@lem5252914 x s)). Qed.
Lemma lem5252916 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5252933 (s : real -> Prop) (h1 : term39 s) : term39 s.
Proof. exact (h1). Qed.
Lemma lem5252950 {A : Type'} (x : A) : term40 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5252951 {A : Type'} (x : A) : (term40 A x) = (term41 A x).
Proof. exact (eq_refl (term40 A x)). Qed.
Lemma lem5252952 {A : Type'} (x : A) : term41 A x.
Proof. exact (EQ_MP (@lem5252951 A x) (@lem5252950 A x)). Qed.
Lemma lem5252953 {A : Type'} (x : A) : term42 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5252955 {_83983 : Type'} (P : _83983 -> Prop) : term43 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem5252956 {_83983 : Type'} (P : _83983 -> Prop) : (term43 _83983 P) = (term44 _83983 P).
Proof. exact (eq_refl (term43 _83983 P)). Qed.
Lemma lem5252957 {_83983 : Type'} (P : _83983 -> Prop) : term44 _83983 P.
Proof. exact (EQ_MP (@lem5252956 _83983 P) (@lem5252955 _83983 P)). Qed.
Lemma lem5252958 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term45 _83983 P a.
Proof. exact (@lem5252957 _83983 P a). Qed.
Lemma lem5252959 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term45 _83983 P a) = (term46 _83983 a P).
Proof. exact (eq_refl (term45 _83983 P a)). Qed.
Lemma lem5252960 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term46 _83983 a P.
Proof. exact (EQ_MP (@lem5252959 _83983 a P) (@lem5252958 _83983 P a)). Qed.
Lemma lem5252961 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term47 _83983 a P s.
Proof. exact (@lem5252960 _83983 a P s). Qed.
Lemma lem5252962 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term47 _83983 a P s) = ((term48 _83983 a s P) = (term49 _83983 a s P)).
Proof. exact (eq_refl (term47 _83983 a P s)). Qed.
Lemma lem5252964 {A : Type'} (x : A) : term50 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem5252965 {A : Type'} (x : A) : (term50 A x) = (term51 A x).
Proof. exact (eq_refl (term50 A x)). Qed.
Lemma lem5252966 {A : Type'} (x : A) : term51 A x.
Proof. exact (EQ_MP (@lem5252965 A x) (@lem5252964 A x)). Qed.
Lemma lem5252967 {A : Type'} (x : A) (s : A -> Prop) : term52 A x s.
Proof. exact (@lem5252966 A x s). Qed.
Lemma lem5252968 {A : Type'} (x : A) (s : A -> Prop) : (term52 A x s) = (term53 A x s).
Proof. exact (eq_refl (term52 A x s)). Qed.
Lemma lem5252969 {A : Type'} (x : A) (s : A -> Prop) : term53 A x s.
Proof. exact (EQ_MP (@lem5252968 A x s) (@lem5252967 A x s)). Qed.
Lemma lem5252970 {A : Type'} (x : A) (s : A -> Prop) : term54 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem5252985 {A : Type'} (s : A -> Prop) : term55 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem5252986 {A : Type'} (s : A -> Prop) : (term55 A s) = (term56 A s).
Proof. exact (eq_refl (term55 A s)). Qed.
Lemma lem5252987 {A : Type'} (s : A -> Prop) : term56 A s.
Proof. exact (EQ_MP (@lem5252986 A s) (@lem5252985 A s)). Qed.
Lemma lem5252988 {A : Type'} (s : A -> Prop) (x : A) : term57 A s x.
Proof. exact (@lem5252987 A s x). Qed.
Lemma lem5252989 {A : Type'} (x : A) (s : A -> Prop) : (term57 A s x) = ((term58 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term57 A s x)). Qed.
Lemma lem5252991 (a : real) (s : real -> Prop) : term59 a s.
Proof. exact (@lem5252869 a s). Qed.
Lemma lem5252992 (s : real -> Prop) (a : real) : (term59 a s) = (term60 s a).
Proof. exact (eq_refl (term59 a s)). Qed.
Lemma lem5252993 (s : real -> Prop) (a : real) : term60 s a.
Proof. exact (EQ_MP (@lem5252992 s a) (@lem5252991 a s)). Qed.
Lemma lem5252994 (s : real -> Prop) (h1 : term61 s) : term61 s.
Proof. exact (h1). Qed.
Lemma lem5252995 (a : real) (s : real -> Prop) (h1 : term61 s) : ((inf s) = a) = (term62 s a).
Proof. exact (@lem5252993 s a (@lem5252994 s h1)). Qed.
Lemma lem5253001 (s : real -> Prop) : (@FINITE real s) = ((@FINITE real s) = True).
Proof. exact (@lem7 (@FINITE real s)). Qed.
Lemma lem5253004 (s : real -> Prop) (a : real) : term60 s a.
Proof. exact (fun h0 : term61 s => @lem5252995 a s h0). Qed.
Lemma lem5253005 (s : real -> Prop) (x : real) : term63 s x.
Proof. exact (@lem5253004 (@INSERT real x s) x). Qed.
Lemma lem5253009 {A : Type'} (x : A) (s : A -> Prop) : (term58 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem5252989 A x s) (@lem5252988 A s x)). Qed.
Lemma lem5253010 (x : real) (s : real -> Prop) : (term64 x s) = (@FINITE real s).
Proof. exact (@lem5253009 real x s). Qed.
Lemma lem5253012 (s : real -> Prop) (h1 : @FINITE real s) : (@FINITE real s) = True.
Proof. exact (EQ_MP (@lem5253001 s) (@lem5252897 s h1)). Qed.
Lemma lem5253013 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term64 x s) = True.
Proof. exact (TRANS (@lem5253010 x s) (@lem5253012 s h1)). Qed.
Lemma lem5253014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253015 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term65 x s) = (and True).
Proof. exact (MK_COMB (@lem5253014) (@lem5253013 x s h1)). Qed.
Lemma lem5253017 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5252970 A x s (@lem5252969 A x s)). Qed.
Lemma lem5253018 (x : real) (s : real -> Prop) : ((@INSERT real x s) = (@EMPTY real)) = False.
Proof. exact (@lem5253017 real x s). Qed.
Lemma lem5253019 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5253020 (x : real) (s : real -> Prop) : (term66 x s) = (~ False).
Proof. exact (MK_COMB (@lem5253019) (@lem5253018 x s)). Qed.
Lemma lem5253022 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5253023 (x : real) (s : real -> Prop) : (term66 x s) = True.
Proof. exact (TRANS (@lem5253020 x s) (@lem5253022)). Qed.
Lemma lem5253024 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term67 x s) = (True /\ True).
Proof. exact (MK_COMB (@lem5253015 x s h1) (@lem5253023 x s)). Qed.
Lemma lem5253026 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5253027 : (True /\ True) = True.
Proof. exact (@lem5253026 True). Qed.
Lemma lem5253028 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term67 x s) = True.
Proof. exact (TRANS (@lem5253024 x s h1) (@lem5253027)). Qed.
Lemma lem5253029 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : True = (term67 x s).
Proof. exact (SYM (@lem5253028 x s h1)). Qed.
Lemma lem5253030 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term67 x s.
Proof. exact (EQ_MP (@lem5253029 x s h1) (@lem0)). Qed.
Lemma lem5253031 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : ((term25 x s) = x) = (term68 s x).
Proof. exact (@lem5253005 s x (@lem5253030 x s h1)). Qed.
Lemma lem5253035 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5253036 (x : real) : (@INSERT real x) = (@INSERT real x).
Proof. exact (eq_refl (@INSERT real x)). Qed.
Lemma lem5253037 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (@INSERT real x s) = (@INSERT real x (@EMPTY real)).
Proof. exact (MK_COMB (@lem5253036 x) (@lem5253035 s h1)). Qed.
Lemma lem5253038 (x : real) : (@IN real x) = (@IN real x).
Proof. exact (eq_refl (@IN real x)). Qed.
Lemma lem5253039 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term69 x s) = (term70 x).
Proof. exact (MK_COMB (@lem5253038 x) (@lem5253037 x s h1)). Qed.
Lemma lem5253040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253041 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term71 x s) = (term72 x).
Proof. exact (MK_COMB (@lem5253040) (@lem5253039 x s h1)). Qed.
Lemma lem5253043 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term48 _83983 a s P) = (term49 _83983 a s P).
Proof. exact (EQ_MP (@lem5252962 _83983 a s P) (@lem5252961 _83983 a P s)). Qed.
Lemma lem5253044 (a : real) (s : real -> Prop) (P : real -> Prop) : (term73 a s P) = (term74 a s P).
Proof. exact (@lem5253043 real a s P). Qed.
Lemma lem5253045 (s : real -> Prop) (x : real) : (term75 s x) = (term76 s x).
Proof. exact (@lem5253044 x s (term77 x)). Qed.
Lemma lem5253046 (x : real) (y : real) : (term78 x y) = (real_le x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem5253047 (y : real) (x : real) (s : real -> Prop) : (term79 y x s) = (term79 y x s).
Proof. exact (eq_refl (term79 y x s)). Qed.
Lemma lem5253048 (s : real -> Prop) (x : real) (y : real) : (term80 s x y) = (term81 s x y).
Proof. exact (MK_COMB (@lem5253047 y x s) (@lem5253046 x y)). Qed.
Lemma lem5253049 (s : real -> Prop) (x : real) : (term82 s x) = (term83 s x).
Proof. exact (fun_ext (fun y : real => @lem5253048 s x y)). Qed.
Lemma lem5253050 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5253051 (s : real -> Prop) (x : real) : (term75 s x) = (term84 s x).
Proof. exact (MK_COMB (@lem5253050) (@lem5253049 s x)). Qed.
Lemma lem5253052 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5253053 (s : real -> Prop) (x : real) : (term85 s x) = (term86 s x).
Proof. exact (MK_COMB (@lem5253052) (@lem5253051 s x)). Qed.
Lemma lem5253054 (x : real) : (term87 x) = (real_le x x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem5253055 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253056 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem5253055) (@lem5253054 x)). Qed.
Lemma lem5253057 (x : real) (y : real) : (term78 x y) = (real_le x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem5253058 (y : real) (s : real -> Prop) : (term90 y s) = (term90 y s).
Proof. exact (eq_refl (term90 y s)). Qed.
Lemma lem5253059 (s : real -> Prop) (x : real) (y : real) : (term91 s x y) = (term92 s x y).
Proof. exact (MK_COMB (@lem5253058 y s) (@lem5253057 x y)). Qed.
Lemma lem5253060 (s : real -> Prop) (x : real) : (term93 s x) = (term94 s x).
Proof. exact (fun_ext (fun y : real => @lem5253059 s x y)). Qed.
Lemma lem5253061 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5253062 (s : real -> Prop) (x : real) : (term95 s x) = (term96 s x).
Proof. exact (MK_COMB (@lem5253061) (@lem5253060 s x)). Qed.
Lemma lem5253063 (s : real -> Prop) (x : real) : (term76 s x) = (term97 s x).
Proof. exact (MK_COMB (@lem5253056 x) (@lem5253062 s x)). Qed.
Lemma lem5253064 (s : real -> Prop) (x : real) : ((term75 s x) = (term76 s x)) = ((term84 s x) = (term97 s x)).
Proof. exact (MK_COMB (@lem5253053 s x) (@lem5253063 s x)). Qed.
Lemma lem5253065 (s : real -> Prop) (x : real) : (term84 s x) = (term97 s x).
Proof. exact (EQ_MP (@lem5253064 s x) (@lem5253045 s x)). Qed.
Lemma lem5253075 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term98 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5253076 (p : Prop) (q : Prop) (p' : Prop) : term99 p q p'.
Proof. exact (fun q' : Prop => @lem5253075 p q p' q'). Qed.
Lemma lem5253077 (p : Prop) (q : Prop) : term100 p q.
Proof. exact (fun p' : Prop => @lem5253076 p q p'). Qed.
Lemma lem5253078 (s : real -> Prop) (x : real) (y : real) : term101 s x y.
Proof. exact (@lem5253077 (@IN real y s) (real_le x y)). Qed.
Lemma lem5253079 (s : real -> Prop) (x : real) (y : real) (p' : Prop) : term102 s x y p'.
Proof. exact (@lem5253078 s x y p'). Qed.
Lemma lem5253080 (s : real -> Prop) (x : real) (y : real) (p' : Prop) : (term102 s x y p') = (term103 s x y p').
Proof. exact (eq_refl (term102 s x y p')). Qed.
Lemma lem5253081 (s : real -> Prop) (x : real) (y : real) (p' : Prop) : term103 s x y p'.
Proof. exact (EQ_MP (@lem5253080 s x y p') (@lem5253079 s x y p')). Qed.
Lemma lem5253082 (s : real -> Prop) (x : real) (y : real) (p' : Prop) (q' : Prop) : term104 s x y p' q'.
Proof. exact (@lem5253081 s x y p' q'). Qed.
Lemma lem5253083 (s : real -> Prop) (x : real) (y : real) (p' : Prop) (q' : Prop) : (term104 s x y p' q') = (term105 s x y p' q').
Proof. exact (eq_refl (term104 s x y p' q')). Qed.
Lemma lem5253084 (s : real -> Prop) (x : real) (y : real) (p' : Prop) (q' : Prop) : term105 s x y p' q'.
Proof. exact (EQ_MP (@lem5253083 s x y p' q') (@lem5253082 s x y p' q')). Qed.
Lemma lem5253086 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5253087 (y : real) : (@IN real y) = (@IN real y).
Proof. exact (eq_refl (@IN real y)). Qed.
Lemma lem5253088 (y : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (@IN real y s) = (@IN real y (@EMPTY real)).
Proof. exact (MK_COMB (@lem5253087 y) (@lem5253086 s h1)). Qed.
Lemma lem5253090 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5252953 A x (@lem5252952 A x)). Qed.
Lemma lem5253091 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5253090 real x). Qed.
Lemma lem5253092 (y : real) : (@IN real y (@EMPTY real)) = False.
Proof. exact (@lem5253091 y). Qed.
Lemma lem5253093 (y : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (@IN real y s) = False.
Proof. exact (TRANS (@lem5253088 y s h1) (@lem5253092 y)). Qed.
Lemma lem5253094 (s : real -> Prop) (x : real) (y : real) (q' : Prop) : term106 s x y q'.
Proof. exact (@lem5253084 s x y False q'). Qed.
Lemma lem5253095 (x : real) (y : real) (q' : Prop) (s : real -> Prop) (h1 : s = (@EMPTY real)) : term107 s x y q'.
Proof. exact (@lem5253094 s x y q' (@lem5253093 y s h1)). Qed.
Lemma lem5253099 (x : real) (y : real) : (real_le x y) = (real_le x y).
Proof. exact (eq_refl (real_le x y)). Qed.
Lemma lem5253100 (x : real) (y : real) : term108 x y.
Proof. exact (fun h0 : False => @lem5253099 x y). Qed.
Lemma lem5253101 (x : real) (y : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : term109 s x y.
Proof. exact (@lem5253095 x y (real_le x y) s h1). Qed.
Lemma lem5253102 (x : real) (y : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term92 s x y) = (term110 x y).
Proof. exact (@lem5253101 x y s h1 (@lem5253100 x y)). Qed.
Lemma lem5253104 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5253105 (x : real) (y : real) : (term110 x y) = True.
Proof. exact (@lem5253104 (real_le x y)). Qed.
Lemma lem5253106 (x : real) (y : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term92 s x y) = True.
Proof. exact (TRANS (@lem5253102 x y s h1) (@lem5253105 x y)). Qed.
Lemma lem5253107 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term94 s x) = term111.
Proof. exact (fun_ext (fun y : real => @lem5253106 x y s h1)). Qed.
Lemma lem5253108 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5253109 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term96 s x) = term112.
Proof. exact (MK_COMB (@lem5253108) (@lem5253107 x s h1)). Qed.
Lemma lem5253111 {A : Type'} (t : Prop) : (term113 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5253112 (t : Prop) : (term114 t) = t.
Proof. exact (@lem5253111 real t). Qed.
Lemma lem5253113 : term112 = True.
Proof. exact (@lem5253112 True). Qed.
Lemma lem5253114 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term96 s x) = True.
Proof. exact (TRANS (@lem5253109 x s h1) (@lem5253113)). Qed.
Lemma lem5253115 (x : real) : (term89 x) = (term89 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem5253116 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term97 s x) = (term115 x).
Proof. exact (MK_COMB (@lem5253115 x) (@lem5253114 x s h1)). Qed.
Lemma lem5253118 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem5253119 (x : real) : (term115 x) = (real_le x x).
Proof. exact (@lem5253118 (real_le x x)). Qed.
Lemma lem5253120 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term97 s x) = (real_le x x).
Proof. exact (TRANS (@lem5253116 x s h1) (@lem5253119 x)). Qed.
Lemma lem5253121 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term84 s x) = (real_le x x).
Proof. exact (TRANS (@lem5253065 s x) (@lem5253120 x s h1)). Qed.
Lemma lem5253122 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term68 s x) = (term116 x).
Proof. exact (MK_COMB (@lem5253041 x s h1) (@lem5253121 x s h1)). Qed.
Lemma lem5253125 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : s = (@EMPTY real)) : ((term25 x s) = x) = (term116 x).
Proof. exact (TRANS (@lem5253031 x s h1) (@lem5253122 x s h2)). Qed.
Lemma lem5253126 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : s = (@EMPTY real)) : (term116 x) = ((term25 x s) = x).
Proof. exact (SYM (@lem5253125 x s h1 h2)). Qed.
Lemma lem5253132 {_83983 : Type'} (P : _83983 -> Prop) : term43 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem5253133 {_83983 : Type'} (P : _83983 -> Prop) : (term43 _83983 P) = (term44 _83983 P).
Proof. exact (eq_refl (term43 _83983 P)). Qed.
Lemma lem5253134 {_83983 : Type'} (P : _83983 -> Prop) : term44 _83983 P.
Proof. exact (EQ_MP (@lem5253133 _83983 P) (@lem5253132 _83983 P)). Qed.
Lemma lem5253135 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term45 _83983 P a.
Proof. exact (@lem5253134 _83983 P a). Qed.
Lemma lem5253136 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term45 _83983 P a) = (term46 _83983 a P).
Proof. exact (eq_refl (term45 _83983 P a)). Qed.
Lemma lem5253137 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term46 _83983 a P.
Proof. exact (EQ_MP (@lem5253136 _83983 a P) (@lem5253135 _83983 P a)). Qed.
Lemma lem5253138 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term47 _83983 a P s.
Proof. exact (@lem5253137 _83983 a P s). Qed.
Lemma lem5253139 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term47 _83983 a P s) = ((term48 _83983 a s P) = (term49 _83983 a s P)).
Proof. exact (eq_refl (term47 _83983 a P s)). Qed.
Lemma lem5253141 {A : Type'} (x : A) : term50 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem5253142 {A : Type'} (x : A) : (term50 A x) = (term51 A x).
Proof. exact (eq_refl (term50 A x)). Qed.
Lemma lem5253143 {A : Type'} (x : A) : term51 A x.
Proof. exact (EQ_MP (@lem5253142 A x) (@lem5253141 A x)). Qed.
Lemma lem5253144 {A : Type'} (x : A) (s : A -> Prop) : term52 A x s.
Proof. exact (@lem5253143 A x s). Qed.
Lemma lem5253145 {A : Type'} (x : A) (s : A -> Prop) : (term52 A x s) = (term53 A x s).
Proof. exact (eq_refl (term52 A x s)). Qed.
Lemma lem5253146 {A : Type'} (x : A) (s : A -> Prop) : term53 A x s.
Proof. exact (EQ_MP (@lem5253145 A x s) (@lem5253144 A x s)). Qed.
Lemma lem5253147 {A : Type'} (x : A) (s : A -> Prop) : term54 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem5253162 {A : Type'} (s : A -> Prop) : term55 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem5253163 {A : Type'} (s : A -> Prop) : (term55 A s) = (term56 A s).
Proof. exact (eq_refl (term55 A s)). Qed.
Lemma lem5253164 {A : Type'} (s : A -> Prop) : term56 A s.
Proof. exact (EQ_MP (@lem5253163 A s) (@lem5253162 A s)). Qed.
Lemma lem5253165 {A : Type'} (s : A -> Prop) (x : A) : term57 A s x.
Proof. exact (@lem5253164 A s x). Qed.
Lemma lem5253166 {A : Type'} (x : A) (s : A -> Prop) : (term57 A s x) = ((term58 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term57 A s x)). Qed.
Lemma lem5253168 (a : real) (s : real -> Prop) : term59 a s.
Proof. exact (@lem5252869 a s). Qed.
Lemma lem5253169 (s : real -> Prop) (a : real) : (term59 a s) = (term60 s a).
Proof. exact (eq_refl (term59 a s)). Qed.
Lemma lem5253170 (s : real -> Prop) (a : real) : term60 s a.
Proof. exact (EQ_MP (@lem5253169 s a) (@lem5253168 a s)). Qed.
Lemma lem5253171 (s : real -> Prop) (h1 : term61 s) : term61 s.
Proof. exact (h1). Qed.
Lemma lem5253172 (a : real) (s : real -> Prop) (h1 : term61 s) : ((inf s) = a) = (term62 s a).
Proof. exact (@lem5253170 s a (@lem5253171 s h1)). Qed.
Lemma lem5253178 (s : real -> Prop) : (@FINITE real s) = ((@FINITE real s) = True).
Proof. exact (@lem7 (@FINITE real s)). Qed.
Lemma lem5253194 (s : real -> Prop) (a : real) : term60 s a.
Proof. exact (fun h0 : term61 s => @lem5253172 a s h0). Qed.
Lemma lem5253195 (x : real) (s : real -> Prop) : term117 x s.
Proof. exact (@lem5253194 (@INSERT real x s) (term23 x s)). Qed.
Lemma lem5253199 {A : Type'} (x : A) (s : A -> Prop) : (term58 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem5253166 A x s) (@lem5253165 A s x)). Qed.
Lemma lem5253200 (x : real) (s : real -> Prop) : (term64 x s) = (@FINITE real s).
Proof. exact (@lem5253199 real x s). Qed.
Lemma lem5253202 (s : real -> Prop) (h1 : @FINITE real s) : (@FINITE real s) = True.
Proof. exact (EQ_MP (@lem5253178 s) (@lem5252897 s h1)). Qed.
Lemma lem5253203 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term64 x s) = True.
Proof. exact (TRANS (@lem5253200 x s) (@lem5253202 s h1)). Qed.
Lemma lem5253204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253205 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term65 x s) = (and True).
Proof. exact (MK_COMB (@lem5253204) (@lem5253203 x s h1)). Qed.
Lemma lem5253207 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5253147 A x s (@lem5253146 A x s)). Qed.
Lemma lem5253208 (x : real) (s : real -> Prop) : ((@INSERT real x s) = (@EMPTY real)) = False.
Proof. exact (@lem5253207 real x s). Qed.
Lemma lem5253209 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5253210 (x : real) (s : real -> Prop) : (term66 x s) = (~ False).
Proof. exact (MK_COMB (@lem5253209) (@lem5253208 x s)). Qed.
Lemma lem5253212 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5253213 (x : real) (s : real -> Prop) : (term66 x s) = True.
Proof. exact (TRANS (@lem5253210 x s) (@lem5253212)). Qed.
Lemma lem5253214 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term67 x s) = (True /\ True).
Proof. exact (MK_COMB (@lem5253205 x s h1) (@lem5253213 x s)). Qed.
Lemma lem5253216 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5253217 : (True /\ True) = True.
Proof. exact (@lem5253216 True). Qed.
Lemma lem5253218 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term67 x s) = True.
Proof. exact (TRANS (@lem5253214 x s h1) (@lem5253217)). Qed.
Lemma lem5253219 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : True = (term67 x s).
Proof. exact (SYM (@lem5253218 x s h1)). Qed.
Lemma lem5253220 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term67 x s.
Proof. exact (EQ_MP (@lem5253219 x s h1) (@lem0)). Qed.
Lemma lem5253221 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : ((term25 x s) = (term23 x s)) = (term118 x s).
Proof. exact (@lem5253195 x s (@lem5253220 x s h1)). Qed.
Lemma lem5253225 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term48 _83983 a s P) = (term49 _83983 a s P).
Proof. exact (EQ_MP (@lem5253139 _83983 a s P) (@lem5253138 _83983 a P s)). Qed.
Lemma lem5253226 (a : real) (s : real -> Prop) (P : real -> Prop) : (term73 a s P) = (term74 a s P).
Proof. exact (@lem5253225 real a s P). Qed.
Lemma lem5253227 (x : real) (s : real -> Prop) : (term119 x s) = (term120 x s).
Proof. exact (@lem5253226 x s (term121 x s)). Qed.
Lemma lem5253228 (x : real) (s : real -> Prop) (y : real) : (term122 x s y) = (term123 x s y).
Proof. exact (eq_refl (term122 x s y)). Qed.
Lemma lem5253229 (y : real) (x : real) (s : real -> Prop) : (term79 y x s) = (term79 y x s).
Proof. exact (eq_refl (term79 y x s)). Qed.
Lemma lem5253230 (x : real) (s : real -> Prop) (y : real) : (term124 x s y) = (term125 x s y).
Proof. exact (MK_COMB (@lem5253229 y x s) (@lem5253228 x s y)). Qed.
Lemma lem5253231 (x : real) (s : real -> Prop) : (term126 x s) = (term127 x s).
Proof. exact (fun_ext (fun y : real => @lem5253230 x s y)). Qed.
Lemma lem5253232 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5253233 (x : real) (s : real -> Prop) : (term119 x s) = (term128 x s).
Proof. exact (MK_COMB (@lem5253232) (@lem5253231 x s)). Qed.
Lemma lem5253234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5253235 (x : real) (s : real -> Prop) : (term129 x s) = (term130 x s).
Proof. exact (MK_COMB (@lem5253234) (@lem5253233 x s)). Qed.
Lemma lem5253236 (s : real -> Prop) (x : real) : (term131 s x) = (term132 s x).
Proof. exact (eq_refl (term131 s x)). Qed.
Lemma lem5253237 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253238 (s : real -> Prop) (x : real) : (term133 s x) = (term134 s x).
Proof. exact (MK_COMB (@lem5253237) (@lem5253236 s x)). Qed.
Lemma lem5253239 (x : real) (s : real -> Prop) (y : real) : (term122 x s y) = (term123 x s y).
Proof. exact (eq_refl (term122 x s y)). Qed.
Lemma lem5253240 (y : real) (s : real -> Prop) : (term90 y s) = (term90 y s).
Proof. exact (eq_refl (term90 y s)). Qed.
Lemma lem5253241 (x : real) (s : real -> Prop) (y : real) : (term135 x s y) = (term136 x s y).
Proof. exact (MK_COMB (@lem5253240 y s) (@lem5253239 x s y)). Qed.
Lemma lem5253242 (x : real) (s : real -> Prop) : (term137 x s) = (term138 x s).
Proof. exact (fun_ext (fun y : real => @lem5253241 x s y)). Qed.
Lemma lem5253243 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5253244 (x : real) (s : real -> Prop) : (term139 x s) = (term140 x s).
Proof. exact (MK_COMB (@lem5253243) (@lem5253242 x s)). Qed.
Lemma lem5253245 (x : real) (s : real -> Prop) : (term120 x s) = (term141 x s).
Proof. exact (MK_COMB (@lem5253238 s x) (@lem5253244 x s)). Qed.
Lemma lem5253246 (x : real) (s : real -> Prop) : ((term119 x s) = (term120 x s)) = ((term128 x s) = (term141 x s)).
Proof. exact (MK_COMB (@lem5253235 x s) (@lem5253245 x s)). Qed.
Lemma lem5253247 (x : real) (s : real -> Prop) : (term128 x s) = (term141 x s).
Proof. exact (EQ_MP (@lem5253246 x s) (@lem5253227 x s)). Qed.
Lemma lem5253277 (x : real) (s : real -> Prop) : (term142 x s) = (term142 x s).
Proof. exact (eq_refl (term142 x s)). Qed.
Lemma lem5253278 (x : real) (s : real -> Prop) : (term118 x s) = (term143 x s).
Proof. exact (MK_COMB (@lem5253277 x s) (@lem5253247 x s)). Qed.
Lemma lem5253310 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : ((term25 x s) = (term23 x s)) = (term143 x s).
Proof. exact (TRANS (@lem5253221 x s h1) (@lem5253278 x s)). Qed.
Lemma lem5253311 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term143 x s) = ((term25 x s) = (term23 x s)).
Proof. exact (SYM (@lem5253310 x s h1)). Qed.
Lemma lem5253315 {A : Type'} (x : A) (y : A) : (term15 A x y) = (x = y).
Proof. exact (EQ_MP (@lem5252895 A x y) (@lem5252894 A x y)). Qed.
Lemma lem5253316 (x : real) (y : real) : (term144 x y) = (x = y).
Proof. exact (@lem5253315 real x y). Qed.
Lemma lem5253317 (x : real) : (term70 x) = (x = x).
Proof. exact (@lem5253316 x x). Qed.
Lemma lem5253319 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5253320 (x : real) : (x = x) = True.
Proof. exact (@lem5253319 real x). Qed.
Lemma lem5253321 (x : real) : (term70 x) = True.
Proof. exact (TRANS (@lem5253317 x) (@lem5253320 x)). Qed.
Lemma lem5253322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253323 (x : real) : (term72 x) = (and True).
Proof. exact (MK_COMB (@lem5253322) (@lem5253321 x)). Qed.
Lemma lem5253325 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem5252889 x) (@lem5252888 x)). Qed.
Lemma lem5253326 (x : real) : (term116 x) = (True /\ True).
Proof. exact (MK_COMB (@lem5253323 x) (@lem5253325 x)). Qed.
Lemma lem5253328 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5253329 : (True /\ True) = True.
Proof. exact (@lem5253328 True). Qed.
Lemma lem5253330 (x : real) : (term116 x) = True.
Proof. exact (TRANS (@lem5253326 x) (@lem5253329)). Qed.
Lemma lem5253331 (x : real) : True = (term116 x).
Proof. exact (SYM (@lem5253330 x)). Qed.
Lemma lem5253332 (x : real) : term116 x.
Proof. exact (EQ_MP (@lem5253331 x) (@lem0)). Qed.
Lemma lem5253352 (m : real) (n : real) : (real_min m n) = (term10 m n).
Proof. exact (EQ_MP (@lem5252884 m n) (@lem5252883 m n)). Qed.
Lemma lem5253353 (x : real) (s : real -> Prop) : (term23 x s) = (term145 x s).
Proof. exact (@lem5253352 x (inf s)). Qed.
Lemma lem5253354 : (@IN real) = (@IN real).
Proof. exact (eq_refl (@IN real)). Qed.
Lemma lem5253355 (x : real) (s : real -> Prop) : (term146 x s) = (term147 x s).
Proof. exact (MK_COMB (@lem5253354) (@lem5253353 x s)). Qed.
Lemma lem5253356 (x : real) (s : real -> Prop) : (@INSERT real x s) = (@INSERT real x s).
Proof. exact (eq_refl (@INSERT real x s)). Qed.
Lemma lem5253357 (x : real) (s : real -> Prop) : (term148 x s) = (term149 x s).
Proof. exact (MK_COMB (@lem5253355 x s) (@lem5253356 x s)). Qed.
Lemma lem5253358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253359 (x : real) (s : real -> Prop) : (term142 x s) = (term150 x s).
Proof. exact (MK_COMB (@lem5253358) (@lem5253357 x s)). Qed.
Lemma lem5253363 (m : real) (n : real) : (real_min m n) = (term10 m n).
Proof. exact (EQ_MP (@lem5252884 m n) (@lem5252883 m n)). Qed.
Lemma lem5253364 (x : real) (s : real -> Prop) : (term23 x s) = (term145 x s).
Proof. exact (@lem5253363 x (inf s)). Qed.
Lemma lem5253365 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5253366 (x : real) (s : real -> Prop) : (term151 x s) = (term152 x s).
Proof. exact (MK_COMB (@lem5253365) (@lem5253364 x s)). Qed.
Lemma lem5253367 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5253368 (s : real -> Prop) (x : real) : (term132 s x) = (term153 s x).
Proof. exact (MK_COMB (@lem5253366 x s) (@lem5253367 x)). Qed.
Lemma lem5253369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253370 (s : real -> Prop) (x : real) : (term134 s x) = (term154 s x).
Proof. exact (MK_COMB (@lem5253369) (@lem5253368 s x)). Qed.
Lemma lem5253378 (m : real) (n : real) : (real_min m n) = (term10 m n).
Proof. exact (EQ_MP (@lem5252884 m n) (@lem5252883 m n)). Qed.
Lemma lem5253379 (x : real) (s : real -> Prop) : (term23 x s) = (term145 x s).
Proof. exact (@lem5253378 x (inf s)). Qed.
Lemma lem5253380 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5253381 (x : real) (s : real -> Prop) : (term151 x s) = (term152 x s).
Proof. exact (MK_COMB (@lem5253380) (@lem5253379 x s)). Qed.
Lemma lem5253382 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5253383 (x : real) (s : real -> Prop) (y : real) : (term123 x s y) = (term155 x s y).
Proof. exact (MK_COMB (@lem5253381 x s) (@lem5253382 y)). Qed.
Lemma lem5253384 (y : real) (s : real -> Prop) : (term90 y s) = (term90 y s).
Proof. exact (eq_refl (term90 y s)). Qed.
Lemma lem5253385 (x : real) (s : real -> Prop) (y : real) : (term136 x s y) = (term156 x s y).
Proof. exact (MK_COMB (@lem5253384 y s) (@lem5253383 x s y)). Qed.
Lemma lem5253388 (x : real) (s : real -> Prop) : (term138 x s) = (term157 x s).
Proof. exact (fun_ext (fun y : real => @lem5253385 x s y)). Qed.
Lemma lem5253389 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5253390 (x : real) (s : real -> Prop) : (term140 x s) = (term158 x s).
Proof. exact (MK_COMB (@lem5253389) (@lem5253388 x s)). Qed.
Lemma lem5253395 (x : real) (s : real -> Prop) : (term141 x s) = (term159 x s).
Proof. exact (MK_COMB (@lem5253370 s x) (@lem5253390 x s)). Qed.
Lemma lem5253398 (x : real) (s : real -> Prop) : (term143 x s) = (term160 x s).
Proof. exact (MK_COMB (@lem5253359 x s) (@lem5253395 x s)). Qed.
Lemma lem5253401 (x : real) (s : real -> Prop) : (term160 x s) = (term143 x s).
Proof. exact (SYM (@lem5253398 x s)). Qed.
Lemma lem5253402 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term16 _476 _475 _474 _477) = (term17 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem5253403 (_474 : real) (_475 : Prop) (x : real) (s : real -> Prop) (_477 : real) : (term161 x s _475 _474 _477) = (term162 _474 _475 x s _477).
Proof. exact (@lem5253402 _474 _475 (term163 x s) _477). Qed.
Lemma lem5253404 (x : real) (s : real -> Prop) : (term164 x s) = (term165 x s).
Proof. exact (@lem5253403 x (term166 x s) x s (inf s)). Qed.
Lemma lem5253405 (x : real) (s : real -> Prop) : (term167 x s) = (term168 x s).
Proof. exact (eq_refl (term167 x s)). Qed.
Lemma lem5253406 (x : real) (s : real -> Prop) : (term169 x s) = (term169 x s).
Proof. exact (eq_refl (term169 x s)). Qed.
Lemma lem5253407 (x : real) (s : real -> Prop) : (term170 x s) = (term171 x s).
Proof. exact (MK_COMB (@lem5253406 x s) (@lem5253405 x s)). Qed.
Lemma lem5253408 (s : real -> Prop) (x : real) : (term172 s x) = (term173 s x).
Proof. exact (eq_refl (term172 s x)). Qed.
Lemma lem5253409 (x : real) (s : real -> Prop) : (term174 x s) = (term174 x s).
Proof. exact (eq_refl (term174 x s)). Qed.
Lemma lem5253410 (s : real -> Prop) (x : real) : (term175 s x) = (term176 s x).
Proof. exact (MK_COMB (@lem5253409 x s) (@lem5253408 s x)). Qed.
Lemma lem5253411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253412 (s : real -> Prop) (x : real) : (term177 s x) = (term178 s x).
Proof. exact (MK_COMB (@lem5253411) (@lem5253410 s x)). Qed.
Lemma lem5253413 (x : real) (s : real -> Prop) : (term165 x s) = (term179 x s).
Proof. exact (MK_COMB (@lem5253412 s x) (@lem5253407 x s)). Qed.
Lemma lem5253414 (x : real) (s : real -> Prop) : (term164 x s) = (term160 x s).
Proof. exact (eq_refl (term164 x s)). Qed.
Lemma lem5253415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5253416 (x : real) (s : real -> Prop) : (term180 x s) = (term181 x s).
Proof. exact (MK_COMB (@lem5253415) (@lem5253414 x s)). Qed.
Lemma lem5253417 (x : real) (s : real -> Prop) : ((term164 x s) = (term165 x s)) = ((term160 x s) = (term179 x s)).
Proof. exact (MK_COMB (@lem5253416 x s) (@lem5253413 x s)). Qed.
Lemma lem5253418 (x : real) (s : real -> Prop) : (term160 x s) = (term179 x s).
Proof. exact (EQ_MP (@lem5253417 x s) (@lem5253404 x s)). Qed.
Lemma lem5253419 (x : real) (s : real -> Prop) : (term179 x s) = (term160 x s).
Proof. exact (SYM (@lem5253418 x s)). Qed.
Lemma lem5253420 (x : real) (s : real -> Prop) (h1 : term166 x s) : term166 x s.
Proof. exact (h1). Qed.
Lemma lem5253437 (x : real) (s : real -> Prop) (h1 : term182 x s) : term182 x s.
Proof. exact (h1). Qed.
Lemma lem5253454 (x : real) : term11 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem5253455 (x : real) : (term11 x) = (real_le x x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem5253456 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem5253455 x) (@lem5253454 x)). Qed.
Lemma lem5253457 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem5253459 {A : Type'} (x : A) : term183 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5253460 {A : Type'} (x : A) : (term183 A x) = (term184 A x).
Proof. exact (eq_refl (term183 A x)). Qed.
Lemma lem5253461 {A : Type'} (x : A) : term184 A x.
Proof. exact (EQ_MP (@lem5253460 A x) (@lem5253459 A x)). Qed.
Lemma lem5253462 {A : Type'} (x : A) (y : A) : term185 A x y.
Proof. exact (@lem5253461 A x y). Qed.
Lemma lem5253463 {A : Type'} (y : A) (x : A) : (term185 A x y) = (term186 A y x).
Proof. exact (eq_refl (term185 A x y)). Qed.
Lemma lem5253464 {A : Type'} (y : A) (x : A) : term186 A y x.
Proof. exact (EQ_MP (@lem5253463 A y x) (@lem5253462 A x y)). Qed.
Lemma lem5253465 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term187 A y x s.
Proof. exact (@lem5253464 A y x s). Qed.
Lemma lem5253466 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term187 A y x s) = ((term188 A x y s) = (term189 A y x s)).
Proof. exact (eq_refl (term187 A y x s)). Qed.
Lemma lem5253519 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term188 A x y s) = (term189 A y x s).
Proof. exact (EQ_MP (@lem5253466 A y x s) (@lem5253465 A y x s)). Qed.
Lemma lem5253520 (y : real) (x : real) (s : real -> Prop) : (term190 x y s) = (term191 y x s).
Proof. exact (@lem5253519 real y x s). Qed.
Lemma lem5253521 (x : real) (s : real -> Prop) : (term69 x s) = (term192 x s).
Proof. exact (@lem5253520 x x s). Qed.
Lemma lem5253525 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5253526 (x : real) : (x = x) = True.
Proof. exact (@lem5253525 real x). Qed.
Lemma lem5253527 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5253528 (x : real) : (term193 x) = (or True).
Proof. exact (MK_COMB (@lem5253527) (@lem5253526 x)). Qed.
Lemma lem5253529 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5253530 (x : real) (s : real -> Prop) : (term192 x s) = (term194 x s).
Proof. exact (MK_COMB (@lem5253528 x) (@lem5253529 x s)). Qed.
Lemma lem5253532 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem5253533 (x : real) (s : real -> Prop) : (term194 x s) = True.
Proof. exact (@lem5253532 (@IN real x s)). Qed.
Lemma lem5253534 (x : real) (s : real -> Prop) : (term192 x s) = True.
Proof. exact (TRANS (@lem5253530 x s) (@lem5253533 x s)). Qed.
Lemma lem5253535 (x : real) (s : real -> Prop) : (term69 x s) = True.
Proof. exact (TRANS (@lem5253521 x s) (@lem5253534 x s)). Qed.
Lemma lem5253536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253537 (x : real) (s : real -> Prop) : (term71 x s) = (and True).
Proof. exact (MK_COMB (@lem5253536) (@lem5253535 x s)). Qed.
Lemma lem5253541 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem5253457 x) (@lem5253456 x)). Qed.
Lemma lem5253542 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253543 (x : real) : (term89 x) = (and True).
Proof. exact (MK_COMB (@lem5253542) (@lem5253541 x)). Qed.
Lemma lem5253575 (s : real -> Prop) (x : real) : (term96 s x) = (term96 s x).
Proof. exact (eq_refl (term96 s x)). Qed.
Lemma lem5253576 (s : real -> Prop) (x : real) : (term97 s x) = (term195 s x).
Proof. exact (MK_COMB (@lem5253543 x) (@lem5253575 s x)). Qed.
Lemma lem5253578 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5253579 (s : real -> Prop) (x : real) : (term195 s x) = (term96 s x).
Proof. exact (@lem5253578 (term96 s x)). Qed.
Lemma lem5253611 (s : real -> Prop) (x : real) : (term97 s x) = (term96 s x).
Proof. exact (TRANS (@lem5253576 s x) (@lem5253579 s x)). Qed.
Lemma lem5253612 (s : real -> Prop) (x : real) : (term173 s x) = (term195 s x).
Proof. exact (MK_COMB (@lem5253537 x s) (@lem5253611 s x)). Qed.
Lemma lem5253614 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5253615 (s : real -> Prop) (x : real) : (term195 s x) = (term96 s x).
Proof. exact (@lem5253614 (term96 s x)). Qed.
Lemma lem5253647 (s : real -> Prop) (x : real) : (term173 s x) = (term96 s x).
Proof. exact (TRANS (@lem5253612 s x) (@lem5253615 s x)). Qed.
Lemma lem5253648 (s : real -> Prop) (x : real) : (term96 s x) = (term173 s x).
Proof. exact (SYM (@lem5253647 s x)). Qed.
Lemma lem5253654 {A : Type'} (x : A) : term183 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5253655 {A : Type'} (x : A) : (term183 A x) = (term184 A x).
Proof. exact (eq_refl (term183 A x)). Qed.
Lemma lem5253656 {A : Type'} (x : A) : term184 A x.
Proof. exact (EQ_MP (@lem5253655 A x) (@lem5253654 A x)). Qed.
Lemma lem5253657 {A : Type'} (x : A) (y : A) : term185 A x y.
Proof. exact (@lem5253656 A x y). Qed.
Lemma lem5253658 {A : Type'} (y : A) (x : A) : (term185 A x y) = (term186 A y x).
Proof. exact (eq_refl (term185 A x y)). Qed.
Lemma lem5253659 {A : Type'} (y : A) (x : A) : term186 A y x.
Proof. exact (EQ_MP (@lem5253658 A y x) (@lem5253657 A x y)). Qed.
Lemma lem5253660 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term187 A y x s.
Proof. exact (@lem5253659 A y x s). Qed.
Lemma lem5253661 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term187 A y x s) = ((term188 A x y s) = (term189 A y x s)).
Proof. exact (eq_refl (term187 A y x s)). Qed.
Lemma lem5253663 (s : real -> Prop) : term196 s.
Proof. exact (@lem5222545 s). Qed.
Lemma lem5253664 (s : real -> Prop) : (term196 s) = (term197 s).
Proof. exact (eq_refl (term196 s)). Qed.
Lemma lem5253665 (s : real -> Prop) : term197 s.
Proof. exact (EQ_MP (@lem5253664 s) (@lem5253663 s)). Qed.
Lemma lem5253666 (s : real -> Prop) (h1 : term61 s) : term61 s.
Proof. exact (h1). Qed.
Lemma lem5253667 (s : real -> Prop) (h1 : term61 s) : term198 s.
Proof. exact (@lem5253665 s (@lem5253666 s h1)). Qed.
Lemma lem5253668 (s : real -> Prop) (h1 : term61 s) : term199 s.
Proof. exact (proj2 (@lem5253667 s h1)). Qed.
Lemma lem5253669 (x : real) (s : real -> Prop) (h1 : term61 s) : term200 s x.
Proof. exact (@lem5253668 s h1 x). Qed.
Lemma lem5253670 (s : real -> Prop) (x : real) : (term200 s x) = (term201 s x).
Proof. exact (eq_refl (term200 s x)). Qed.
Lemma lem5253671 (x : real) (s : real -> Prop) (h1 : term61 s) : term201 s x.
Proof. exact (EQ_MP (@lem5253670 s x) (@lem5253669 x s h1)). Qed.
Lemma lem5253672 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5253673 (x : real) (s : real -> Prop) (h1 : term61 s) (h2 : @IN real x s) : term202 s x.
Proof. exact (@lem5253671 x s h1 (@lem5253672 x s h2)). Qed.
Lemma lem5253674 (s : real -> Prop) (x : real) : (term202 s x) = ((term202 s x) = True).
Proof. exact (@lem7 (term202 s x)). Qed.
Lemma lem5253675 (x : real) (s : real -> Prop) (h1 : term61 s) (h2 : @IN real x s) : (term202 s x) = True.
Proof. exact (EQ_MP (@lem5253674 s x) (@lem5253673 x s h1 h2)). Qed.
Lemma lem5253676 (x : real) (s : real -> Prop) (h1 : term61 s) : term203 s x.
Proof. exact (fun h0 : @IN real x s => @lem5253675 x s h1 h0). Qed.
Lemma lem5253677 (s : real -> Prop) (x : real) : term204 s x.
Proof. exact (fun h0 : term61 s => @lem5253676 x s h0). Qed.
Lemma lem5253679 (p : Prop) (q : Prop) (r : Prop) : (term205 p q r) = (term206 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5253684 (s : real -> Prop) (x : real) : (term204 s x) = (term207 s x).
Proof. exact (@lem5253679 (term61 s) (@IN real x s) ((term202 s x) = True)). Qed.
Lemma lem5253686 (s : real -> Prop) (h1 : term61 s) : term208 s.
Proof. exact (proj1 (@lem5253667 s h1)). Qed.
Lemma lem5253687 (s : real -> Prop) : (term208 s) = ((term208 s) = True).
Proof. exact (@lem7 (term208 s)). Qed.
Lemma lem5253688 (s : real -> Prop) (h1 : term61 s) : (term208 s) = True.
Proof. exact (EQ_MP (@lem5253687 s) (@lem5253686 s h1)). Qed.
Lemma lem5253694 (s : real -> Prop) : (@FINITE real s) = ((@FINITE real s) = True).
Proof. exact (@lem7 (@FINITE real s)). Qed.
Lemma lem5253696 (s : real -> Prop) : term209 s.
Proof. exact (@lem82 (s = (@EMPTY real))). Qed.
Lemma lem5253716 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term188 A x y s) = (term189 A y x s).
Proof. exact (EQ_MP (@lem5253661 A y x s) (@lem5253660 A y x s)). Qed.
Lemma lem5253717 (y : real) (x : real) (s : real -> Prop) : (term190 x y s) = (term191 y x s).
Proof. exact (@lem5253716 real y x s). Qed.
Lemma lem5253718 (x : real) (s : real -> Prop) : (term210 x s) = (term211 x s).
Proof. exact (@lem5253717 x (inf s) s). Qed.
Lemma lem5253724 (s : real -> Prop) : term212 s.
Proof. exact (fun h0 : term61 s => @lem5253688 s h0). Qed.
Lemma lem5253728 (s : real -> Prop) (h1 : @FINITE real s) : (@FINITE real s) = True.
Proof. exact (EQ_MP (@lem5253694 s) (@lem5252897 s h1)). Qed.
Lemma lem5253729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253730 (s : real -> Prop) (h1 : @FINITE real s) : (term213 s) = (and True).
Proof. exact (MK_COMB (@lem5253729) (@lem5253728 s h1)). Qed.
Lemma lem5253732 (s : real -> Prop) (h1 : term39 s) : (s = (@EMPTY real)) = False.
Proof. exact (@lem5253696 s (@lem5252933 s h1)). Qed.
Lemma lem5253733 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5253734 (s : real -> Prop) (h1 : term39 s) : (term39 s) = (~ False).
Proof. exact (MK_COMB (@lem5253733) (@lem5253732 s h1)). Qed.
Lemma lem5253736 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5253737 (s : real -> Prop) (h1 : term39 s) : (term39 s) = True.
Proof. exact (TRANS (@lem5253734 s h1) (@lem5253736)). Qed.
Lemma lem5253738 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term61 s) = (True /\ True).
Proof. exact (MK_COMB (@lem5253730 s h1) (@lem5253737 s h2)). Qed.
Lemma lem5253740 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5253741 : (True /\ True) = True.
Proof. exact (@lem5253740 True). Qed.
Lemma lem5253742 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term61 s) = True.
Proof. exact (TRANS (@lem5253738 s h1 h2) (@lem5253741)). Qed.
Lemma lem5253743 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : True = (term61 s).
Proof. exact (SYM (@lem5253742 s h1 h2)). Qed.
Lemma lem5253744 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term61 s.
Proof. exact (EQ_MP (@lem5253743 s h1 h2) (@lem0)). Qed.
Lemma lem5253745 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term208 s) = True.
Proof. exact (@lem5253724 s (@lem5253744 s h1 h2)). Qed.
Lemma lem5253746 (s : real -> Prop) (x : real) : (term214 s x) = (term214 s x).
Proof. exact (eq_refl (term214 s x)). Qed.
Lemma lem5253747 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term211 x s) = (term215 s x).
Proof. exact (MK_COMB (@lem5253746 s x) (@lem5253745 s h1 h2)). Qed.
Lemma lem5253749 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem5253750 (s : real -> Prop) (x : real) : (term215 s x) = True.
Proof. exact (@lem5253749 ((inf s) = x)). Qed.
Lemma lem5253751 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term211 x s) = True.
Proof. exact (TRANS (@lem5253747 x s h1 h2) (@lem5253750 s x)). Qed.
Lemma lem5253752 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term210 x s) = True.
Proof. exact (TRANS (@lem5253718 x s) (@lem5253751 x s h1 h2)). Qed.
Lemma lem5253753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253754 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term216 x s) = (and True).
Proof. exact (MK_COMB (@lem5253753) (@lem5253752 x s h1 h2)). Qed.
Lemma lem5253797 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term98 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5253798 (p : Prop) (q : Prop) (p' : Prop) : term99 p q p'.
Proof. exact (fun q' : Prop => @lem5253797 p q p' q'). Qed.
Lemma lem5253799 (p : Prop) (q : Prop) : term100 p q.
Proof. exact (fun p' : Prop => @lem5253798 p q p'). Qed.
Lemma lem5253800 (s : real -> Prop) (y : real) : term217 s y.
Proof. exact (@lem5253799 (@IN real y s) (term202 s y)). Qed.
Lemma lem5253801 (s : real -> Prop) (y : real) (p' : Prop) : term218 s y p'.
Proof. exact (@lem5253800 s y p'). Qed.
Lemma lem5253802 (s : real -> Prop) (y : real) (p' : Prop) : (term218 s y p') = (term219 s y p').
Proof. exact (eq_refl (term218 s y p')). Qed.
Lemma lem5253803 (s : real -> Prop) (y : real) (p' : Prop) : term219 s y p'.
Proof. exact (EQ_MP (@lem5253802 s y p') (@lem5253801 s y p')). Qed.
Lemma lem5253804 (s : real -> Prop) (y : real) (p' : Prop) (q' : Prop) : term220 s y p' q'.
Proof. exact (@lem5253803 s y p' q'). Qed.
Lemma lem5253805 (s : real -> Prop) (y : real) (p' : Prop) (q' : Prop) : (term220 s y p' q') = (term221 s y p' q').
Proof. exact (eq_refl (term220 s y p' q')). Qed.
Lemma lem5253806 (s : real -> Prop) (y : real) (p' : Prop) (q' : Prop) : term221 s y p' q'.
Proof. exact (EQ_MP (@lem5253805 s y p' q') (@lem5253804 s y p' q')). Qed.
Lemma lem5253807 (y : real) (s : real -> Prop) : (@IN real y s) = (@IN real y s).
Proof. exact (eq_refl (@IN real y s)). Qed.
Lemma lem5253808 (y : real) (s : real -> Prop) (q' : Prop) : term222 y s q'.
Proof. exact (@lem5253806 s y (@IN real y s) q'). Qed.
Lemma lem5253809 (y : real) (s : real -> Prop) (q' : Prop) : term223 y s q'.
Proof. exact (@lem5253808 y s q' (@lem5253807 y s)). Qed.
Lemma lem5253810 (y : real) (s : real -> Prop) (h1 : @IN real y s) : @IN real y s.
Proof. exact (h1). Qed.
Lemma lem5253811 (y : real) (s : real -> Prop) : (@IN real y s) = ((@IN real y s) = True).
Proof. exact (@lem7 (@IN real y s)). Qed.
Lemma lem5253814 (s : real -> Prop) (x : real) : term207 s x.
Proof. exact (EQ_MP (@lem5253684 s x) (@lem5253677 s x)). Qed.
Lemma lem5253815 (s : real -> Prop) (y : real) : term207 s y.
Proof. exact (@lem5253814 s y). Qed.
Lemma lem5253821 (s : real -> Prop) (h1 : @FINITE real s) : (@FINITE real s) = True.
Proof. exact (EQ_MP (@lem5253694 s) (@lem5252897 s h1)). Qed.
Lemma lem5253822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253823 (s : real -> Prop) (h1 : @FINITE real s) : (term213 s) = (and True).
Proof. exact (MK_COMB (@lem5253822) (@lem5253821 s h1)). Qed.
Lemma lem5253825 (s : real -> Prop) (h1 : term39 s) : (s = (@EMPTY real)) = False.
Proof. exact (@lem5253696 s (@lem5252933 s h1)). Qed.
Lemma lem5253826 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5253827 (s : real -> Prop) (h1 : term39 s) : (term39 s) = (~ False).
Proof. exact (MK_COMB (@lem5253826) (@lem5253825 s h1)). Qed.
Lemma lem5253829 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5253830 (s : real -> Prop) (h1 : term39 s) : (term39 s) = True.
Proof. exact (TRANS (@lem5253827 s h1) (@lem5253829)). Qed.
Lemma lem5253831 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term61 s) = (True /\ True).
Proof. exact (MK_COMB (@lem5253823 s h1) (@lem5253830 s h2)). Qed.
Lemma lem5253833 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5253834 : (True /\ True) = True.
Proof. exact (@lem5253833 True). Qed.
Lemma lem5253835 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term61 s) = True.
Proof. exact (TRANS (@lem5253831 s h1 h2) (@lem5253834)). Qed.
Lemma lem5253836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5253837 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term224 s) = (and True).
Proof. exact (MK_COMB (@lem5253836) (@lem5253835 s h1 h2)). Qed.
Lemma lem5253839 (y : real) (s : real -> Prop) (h1 : @IN real y s) : (@IN real y s) = True.
Proof. exact (EQ_MP (@lem5253811 y s) (@lem5253810 y s h1)). Qed.
Lemma lem5253840 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : @IN real y s) : (term225 y s) = (True /\ True).
Proof. exact (MK_COMB (@lem5253837 s h1 h2) (@lem5253839 y s h3)). Qed.
Lemma lem5253842 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5253843 : (True /\ True) = True.
Proof. exact (@lem5253842 True). Qed.
Lemma lem5253844 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : @IN real y s) : (term225 y s) = True.
Proof. exact (TRANS (@lem5253840 y s h1 h2 h3) (@lem5253843)). Qed.
Lemma lem5253845 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : @IN real y s) : True = (term225 y s).
Proof. exact (SYM (@lem5253844 y s h1 h2 h3)). Qed.
Lemma lem5253846 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : @IN real y s) : term225 y s.
Proof. exact (EQ_MP (@lem5253845 y s h1 h2 h3) (@lem0)). Qed.
Lemma lem5253847 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : @IN real y s) : (term202 s y) = True.
Proof. exact (@lem5253815 s y (@lem5253846 y s h1 h2 h3)). Qed.
Lemma lem5253848 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term203 s y.
Proof. exact (fun h0 : @IN real y s => @lem5253847 y s h1 h2 h0). Qed.
Lemma lem5253849 (y : real) (s : real -> Prop) : term226 y s.
Proof. exact (@lem5253809 y s True). Qed.
Lemma lem5253850 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term201 s y) = (term227 y s).
Proof. exact (@lem5253849 y s (@lem5253848 y s h1 h2)). Qed.
Lemma lem5253852 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5253853 (y : real) (s : real -> Prop) : (term227 y s) = True.
Proof. exact (@lem5253852 (@IN real y s)). Qed.
Lemma lem5253854 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term201 s y) = True.
Proof. exact (TRANS (@lem5253850 y s h1 h2) (@lem5253853 y s)). Qed.
Lemma lem5253855 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term228 s) = term111.
Proof. exact (fun_ext (fun y : real => @lem5253854 y s h1 h2)). Qed.
Lemma lem5253856 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5253857 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term199 s) = term112.
Proof. exact (MK_COMB (@lem5253856) (@lem5253855 s h1 h2)). Qed.
Lemma lem5253859 {A : Type'} (t : Prop) : (term113 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5253860 (t : Prop) : (term114 t) = t.
Proof. exact (@lem5253859 real t). Qed.
Lemma lem5253861 : term112 = True.
Proof. exact (@lem5253860 True). Qed.
Lemma lem5253862 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term199 s) = True.
Proof. exact (TRANS (@lem5253857 s h1 h2) (@lem5253861)). Qed.
Lemma lem5253863 (s : real -> Prop) (x : real) : (term229 s x) = (term229 s x).
Proof. exact (eq_refl (term229 s x)). Qed.
Lemma lem5253864 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term230 x s) = (term231 s x).
Proof. exact (MK_COMB (@lem5253863 s x) (@lem5253862 s h1 h2)). Qed.
Lemma lem5253866 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem5253867 (s : real -> Prop) (x : real) : (term231 s x) = (term202 s x).
Proof. exact (@lem5253866 (term202 s x)). Qed.
Lemma lem5253901 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term230 x s) = (term202 s x).
Proof. exact (TRANS (@lem5253864 x s h1 h2) (@lem5253867 s x)). Qed.
Lemma lem5253902 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term168 x s) = (term232 s x).
Proof. exact (MK_COMB (@lem5253754 x s h1 h2) (@lem5253901 x s h1 h2)). Qed.
Lemma lem5253904 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5253905 (s : real -> Prop) (x : real) : (term232 s x) = (term202 s x).
Proof. exact (@lem5253904 (term202 s x)). Qed.
Lemma lem5253939 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term168 x s) = (term202 s x).
Proof. exact (TRANS (@lem5253902 x s h1 h2) (@lem5253905 s x)). Qed.
Lemma lem5253940 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term202 s x) = (term168 x s).
Proof. exact (SYM (@lem5253939 x s h1 h2)). Qed.
Lemma lem5253942 (p : Prop) : p = (term233 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5253943 (s : real -> Prop) (x : real) : (term96 s x) = (term234 s x).
Proof. exact (@lem5253942 (term96 s x)). Qed.
Lemma lem5253944 (s : real -> Prop) (x : real) : (term234 s x) = (term96 s x).
Proof. exact (SYM (@lem5253943 s x)). Qed.
Lemma lem5253945 (s : real -> Prop) (x : real) (h1 : term235 s x) : term235 s x.
Proof. exact (h1). Qed.
Lemma lem5253948 (s : real -> Prop) (x : real) (h1 : term236 s x) : term236 s x.
Proof. exact (h1). Qed.
Lemma lem5253949 (s : real -> Prop) (x : real) : term237 s x.
Proof. exact (fun h0 : term236 s x => @lem5253948 s x h0). Qed.
Lemma lem5253950 (s : real -> Prop) (x : real) (h1 : term237 s x) : term237 s x.
Proof. exact (h1). Qed.
Lemma lem5253951 (s : real -> Prop) (x : real) (h1 : term236 s x) : term236 s x.
Proof. exact (h1). Qed.
Lemma lem5253952 (s : real -> Prop) (x : real) (h1 : term236 s x) (h2 : term237 s x) : term236 s x.
Proof. exact (@lem5253950 s x h2 (@lem5253951 s x h1)). Qed.
Lemma lem5253953 (s : real -> Prop) (x : real) (h1 : term236 s x) : term238 s x.
Proof. exact (fun h0 : term237 s x => @lem5253952 s x h1 h0). Qed.
Lemma lem5253954 (s : real -> Prop) (x : real) (h1 : term237 s x) : term237 s x.
Proof. exact (h1). Qed.
Lemma lem5253955 (s : real -> Prop) (x : real) (h1 : term236 s x) (h2 : term237 s x) : term236 s x.
Proof. exact (@lem5253953 s x h1 (@lem5253954 s x h2)). Qed.
Lemma lem5253956 (s : real -> Prop) (x : real) (h1 : term237 s x) : term237 s x.
Proof. exact (fun h0 : term236 s x => @lem5253955 s x h0 h1). Qed.
Lemma lem5253957 (s : real -> Prop) (x : real) : term239 s x.
Proof. exact (fun h0 : term237 s x => @lem5253956 s x h0). Qed.
Lemma lem5253960 (s : real -> Prop) (x : real) : term237 s x.
Proof. exact (@lem5253957 s x (@lem5253949 s x)). Qed.
Lemma lem5254058 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5254059 : term240 = term241.
Proof. exact (@lem5254058 term242). Qed.
Lemma lem5254076 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem5254077 : term244 = term245.
Proof. exact (MK_COMB (@lem5254076) (@lem5254059)). Qed.
Lemma lem5254080 : term246 = term246.
Proof. exact (eq_refl term246). Qed.
Lemma lem5254081 : term247 = term248.
Proof. exact (MK_COMB (@lem5254080) (@lem5254077)). Qed.
Lemma lem5254084 (s : real -> Prop) (x : real) : (term249 s x) = (term249 s x).
Proof. exact (eq_refl (term249 s x)). Qed.
Lemma lem5254085 (s : real -> Prop) (x : real) : (term250 s x) = (term251 s x).
Proof. exact (MK_COMB (@lem5254084 s x) (@lem5254081)). Qed.
Lemma lem5254088 (x : real) (s : real -> Prop) : (term174 x s) = (term174 x s).
Proof. exact (eq_refl (term174 x s)). Qed.
Lemma lem5254089 (s : real -> Prop) (x : real) : (term252 s x) = (term253 s x).
Proof. exact (MK_COMB (@lem5254088 x s) (@lem5254085 s x)). Qed.
Lemma lem5254092 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5254093 (s : real -> Prop) (x : real) : (term254 s x) = (term255 s x).
Proof. exact (MK_COMB (@lem5254092 s) (@lem5254089 s x)). Qed.
Lemma lem5254096 (s : real -> Prop) : (term256 s) = (term256 s).
Proof. exact (eq_refl (term256 s)). Qed.
Lemma lem5254097 (s : real -> Prop) (x : real) : (term236 s x) = (term257 s x).
Proof. exact (MK_COMB (@lem5254096 s) (@lem5254093 s x)). Qed.
Lemma lem5254100 (x : real) : (term258 x) = (term259 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5254097 s x)). Qed.
Lemma lem5254101 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5254102 (x : real) : (term260 x) = (term261 x).
Proof. exact (MK_COMB (@lem5254101) (@lem5254100 x)). Qed.
Lemma lem5254107 : term262 = term263.
Proof. exact (fun_ext (fun x : real => @lem5254102 x)). Qed.
Lemma lem5254108 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254117 : term264 = term265.
Proof. exact (MK_COMB (@lem5254108) (@lem5254107)). Qed.
Lemma lem5254122 (s : real -> Prop) (x : real) : (term201 s x) = (term201 s x).
Proof. exact (eq_refl (term201 s x)). Qed.
Lemma lem5254123 (s : real -> Prop) : (term228 s) = (term228 s).
Proof. exact (fun_ext (fun x : real => @lem5254122 s x)). Qed.
Lemma lem5254124 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254125 (s : real -> Prop) : (term199 s) = (term199 s).
Proof. exact (MK_COMB (@lem5254124) (@lem5254123 s)). Qed.
Lemma lem5254128 (s : real -> Prop) : (term266 s) = (term266 s).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5254129 (s : real -> Prop) : (term198 s) = (term198 s).
Proof. exact (MK_COMB (@lem5254128 s) (@lem5254125 s)). Qed.
Lemma lem5254138 (s : real -> Prop) : (term267 s) = (term267 s).
Proof. exact (eq_refl (term267 s)). Qed.
Lemma lem5254139 (s : real -> Prop) : (term197 s) = (term197 s).
Proof. exact (MK_COMB (@lem5254138 s) (@lem5254129 s)). Qed.
Lemma lem5254140 : term268 = term268.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5254139 s)). Qed.
Lemma lem5254141 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5254142 : term242 = term242.
Proof. exact (MK_COMB (@lem5254141) (@lem5254140)). Qed.
Lemma lem5254143 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5254144 : term241 = term241.
Proof. exact (MK_COMB (@lem5254143) (@lem5254142)). Qed.
Lemma lem5254149 (y : real) (x : real) : (term269 y x) = (term269 y x).
Proof. exact (eq_refl (term269 y x)). Qed.
Lemma lem5254150 (x : real) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem5254149 y x)). Qed.
Lemma lem5254151 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254152 (x : real) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem5254151) (@lem5254150 x)). Qed.
Lemma lem5254153 : term272 = term272.
Proof. exact (fun_ext (fun x : real => @lem5254152 x)). Qed.
Lemma lem5254154 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254155 : term273 = term273.
Proof. exact (MK_COMB (@lem5254154) (@lem5254153)). Qed.
Lemma lem5254156 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5254157 : term243 = term243.
Proof. exact (MK_COMB (@lem5254156) (@lem5254155)). Qed.
Lemma lem5254158 : term245 = term245.
Proof. exact (MK_COMB (@lem5254157) (@lem5254144)). Qed.
Lemma lem5254167 (y : real) (x : real) (z : real) : (term274 y x z) = (term274 y x z).
Proof. exact (eq_refl (term274 y x z)). Qed.
Lemma lem5254168 (y : real) (x : real) : (term275 y x) = (term275 y x).
Proof. exact (fun_ext (fun z : real => @lem5254167 y x z)). Qed.
Lemma lem5254169 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254170 (y : real) (x : real) : (term276 y x) = (term276 y x).
Proof. exact (MK_COMB (@lem5254169) (@lem5254168 y x)). Qed.
Lemma lem5254171 (x : real) : (term277 x) = (term277 x).
Proof. exact (fun_ext (fun y : real => @lem5254170 y x)). Qed.
Lemma lem5254172 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254173 (x : real) : (term278 x) = (term278 x).
Proof. exact (MK_COMB (@lem5254172) (@lem5254171 x)). Qed.
Lemma lem5254174 : term279 = term279.
Proof. exact (fun_ext (fun x : real => @lem5254173 x)). Qed.
Lemma lem5254175 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254176 : term280 = term280.
Proof. exact (MK_COMB (@lem5254175) (@lem5254174)). Qed.
Lemma lem5254177 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5254178 : term246 = term246.
Proof. exact (MK_COMB (@lem5254177) (@lem5254176)). Qed.
Lemma lem5254179 : term248 = term248.
Proof. exact (MK_COMB (@lem5254178) (@lem5254158)). Qed.
Lemma lem5254184 (s : real -> Prop) (x : real) (y : real) : (term92 s x y) = (term92 s x y).
Proof. exact (eq_refl (term92 s x y)). Qed.
Lemma lem5254185 (s : real -> Prop) (x : real) : (term94 s x) = (term94 s x).
Proof. exact (fun_ext (fun y : real => @lem5254184 s x y)). Qed.
Lemma lem5254186 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254187 (s : real -> Prop) (x : real) : (term96 s x) = (term96 s x).
Proof. exact (MK_COMB (@lem5254186) (@lem5254185 s x)). Qed.
Lemma lem5254188 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5254189 (s : real -> Prop) (x : real) : (term235 s x) = (term235 s x).
Proof. exact (MK_COMB (@lem5254188) (@lem5254187 s x)). Qed.
Lemma lem5254190 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5254191 (s : real -> Prop) (x : real) : (term249 s x) = (term249 s x).
Proof. exact (MK_COMB (@lem5254190) (@lem5254189 s x)). Qed.
Lemma lem5254192 (s : real -> Prop) (x : real) : (term251 s x) = (term251 s x).
Proof. exact (MK_COMB (@lem5254191 s x) (@lem5254179)). Qed.
Lemma lem5254195 (x : real) (s : real -> Prop) : (term174 x s) = (term174 x s).
Proof. exact (eq_refl (term174 x s)). Qed.
Lemma lem5254196 (s : real -> Prop) (x : real) : (term253 s x) = (term253 s x).
Proof. exact (MK_COMB (@lem5254195 x s) (@lem5254192 s x)). Qed.
Lemma lem5254201 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5254202 (s : real -> Prop) (x : real) : (term255 s x) = (term255 s x).
Proof. exact (MK_COMB (@lem5254201 s) (@lem5254196 s x)). Qed.
Lemma lem5254205 (s : real -> Prop) : (term256 s) = (term256 s).
Proof. exact (eq_refl (term256 s)). Qed.
Lemma lem5254206 (s : real -> Prop) (x : real) : (term257 s x) = (term257 s x).
Proof. exact (MK_COMB (@lem5254205 s) (@lem5254202 s x)). Qed.
Lemma lem5254207 (x : real) : (term259 x) = (term259 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5254206 s x)). Qed.
Lemma lem5254208 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5254209 (x : real) : (term261 x) = (term261 x).
Proof. exact (MK_COMB (@lem5254208) (@lem5254207 x)). Qed.
Lemma lem5254210 : term263 = term263.
Proof. exact (fun_ext (fun x : real => @lem5254209 x)). Qed.
Lemma lem5254211 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254212 : term265 = term265.
Proof. exact (MK_COMB (@lem5254211) (@lem5254210)). Qed.
Lemma lem5254303 : term264 = term265.
Proof. exact (TRANS (@lem5254117) (@lem5254212)). Qed.
Lemma lem5254304 : term265 = term264.
Proof. exact (SYM (@lem5254303)). Qed.
Lemma lem5254308 (s : real -> Prop) (x : real) (h1 : term235 s x) : term235 s x.
Proof. exact (h1). Qed.
Lemma lem5254309 (h1 : term280) : term280.
Proof. exact (h1). Qed.
Lemma lem5254311 (h1 : term242) : term242.
Proof. exact (h1). Qed.
Lemma lem5254317 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5254323 (s : real -> Prop) (h1 : term39 s) : term39 s.
Proof. exact (h1). Qed.
Lemma lem5254329 (x : real) (s : real -> Prop) (h1 : term166 x s) : term166 x s.
Proof. exact (h1). Qed.
Lemma lem5254336 (s : real -> Prop) (x : real) (y : real) : (term281 s x y) = (term282 s x y).
Proof. exact (@lem17362 (@IN real y s) (real_le x y)). Qed.
Lemma lem5254337 (P : real -> Prop) : (term283 P) = (term284 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5254338 (s : real -> Prop) (x : real) : (term235 s x) = (term285 s x).
Proof. exact (@lem5254337 (term94 s x)). Qed.
Lemma lem5254339 (s : real -> Prop) (x : real) (y : real) : (term286 s x y) = (term92 s x y).
Proof. exact (eq_refl (term286 s x y)). Qed.
Lemma lem5254340 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5254341 (s : real -> Prop) (x : real) (y : real) : (term287 s x y) = (term281 s x y).
Proof. exact (MK_COMB (@lem5254340) (@lem5254339 s x y)). Qed.
Lemma lem5254342 (s : real -> Prop) (x : real) (y : real) : (term287 s x y) = (term282 s x y).
Proof. exact (TRANS (@lem5254341 s x y) (@lem5254336 s x y)). Qed.
Lemma lem5254343 (s : real -> Prop) (x : real) : (term288 s x) = (term289 s x).
Proof. exact (fun_ext (fun y : real => @lem5254342 s x y)). Qed.
Lemma lem5254344 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5254345 (s : real -> Prop) (x : real) : (term285 s x) = (term290 s x).
Proof. exact (MK_COMB (@lem5254344) (@lem5254343 s x)). Qed.
Lemma lem5254398 (s : real -> Prop) (x : real) : (term235 s x) = (term290 s x).
Proof. exact (TRANS (@lem5254338 s x) (@lem5254345 s x)). Qed.
Lemma lem5254399 (s : real -> Prop) (x : real) (h1 : term235 s x) : term290 s x.
Proof. exact (EQ_MP (@lem5254398 s x) (@lem5254308 s x h1)). Qed.
Lemma lem5254406 (x : real) (y : real) (z : real) : (term291 x y z) = (term292 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5254407 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5254408 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5254409 (x : real) (y : real) (z : real) : (term293 x y z) = (term294 x y z).
Proof. exact (MK_COMB (@lem5254408) (@lem5254406 x y z)). Qed.
Lemma lem5254410 (y : real) (x : real) (z : real) : (term295 y x z) = (term296 y x z).
Proof. exact (MK_COMB (@lem5254409 x y z) (@lem5254407 x z)). Qed.
Lemma lem5254411 (y : real) (x : real) (z : real) : (term274 y x z) = (term295 y x z).
Proof. exact (@lem17265 (term297 x y z) (real_le x z)). Qed.
Lemma lem5254412 (y : real) (x : real) (z : real) : (term274 y x z) = (term296 y x z).
Proof. exact (TRANS (@lem5254411 y x z) (@lem5254410 y x z)). Qed.
Lemma lem5254413 (y : real) (x : real) : (term275 y x) = (term298 y x).
Proof. exact (fun_ext (fun z : real => @lem5254412 y x z)). Qed.
Lemma lem5254414 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254415 (y : real) (x : real) : (term276 y x) = (term299 y x).
Proof. exact (MK_COMB (@lem5254414) (@lem5254413 y x)). Qed.
Lemma lem5254416 (x : real) : (term277 x) = (term300 x).
Proof. exact (fun_ext (fun y : real => @lem5254415 y x)). Qed.
Lemma lem5254417 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254418 (x : real) : (term278 x) = (term301 x).
Proof. exact (MK_COMB (@lem5254417) (@lem5254416 x)). Qed.
Lemma lem5254419 : term279 = term302.
Proof. exact (fun_ext (fun x : real => @lem5254418 x)). Qed.
Lemma lem5254420 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254481 : term280 = term303.
Proof. exact (MK_COMB (@lem5254420) (@lem5254419)). Qed.
Lemma lem5254482 (h1 : term280) : term303.
Proof. exact (EQ_MP (@lem5254481) (@lem5254309 h1)). Qed.
Lemma lem5254554 (s : real -> Prop) : (term304 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5254556 (s : real -> Prop) : (term305 s) = (term305 s).
Proof. exact (eq_refl (term305 s)). Qed.
Lemma lem5254557 (s : real -> Prop) : (term306 s) = (term307 s).
Proof. exact (MK_COMB (@lem5254556 s) (@lem5254554 s)). Qed.
Lemma lem5254558 (s : real -> Prop) : (term308 s) = (term306 s).
Proof. exact (@lem17045 (@FINITE real s) (term39 s)). Qed.
Lemma lem5254559 (s : real -> Prop) : (term308 s) = (term307 s).
Proof. exact (TRANS (@lem5254558 s) (@lem5254557 s)). Qed.
Lemma lem5254567 (s : real -> Prop) (x : real) : (term201 s x) = (term309 s x).
Proof. exact (@lem17265 (@IN real x s) (term202 s x)). Qed.
Lemma lem5254568 (s : real -> Prop) : (term228 s) = (term310 s).
Proof. exact (fun_ext (fun x : real => @lem5254567 s x)). Qed.
Lemma lem5254569 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254570 (s : real -> Prop) : (term199 s) = (term311 s).
Proof. exact (MK_COMB (@lem5254569) (@lem5254568 s)). Qed.
Lemma lem5254572 (s : real -> Prop) : (term266 s) = (term266 s).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5254573 (s : real -> Prop) : (term198 s) = (term312 s).
Proof. exact (MK_COMB (@lem5254572 s) (@lem5254570 s)). Qed.
Lemma lem5254574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5254575 (s : real -> Prop) : (term313 s) = (term314 s).
Proof. exact (MK_COMB (@lem5254574) (@lem5254559 s)). Qed.
Lemma lem5254576 (s : real -> Prop) : (term315 s) = (term316 s).
Proof. exact (MK_COMB (@lem5254575 s) (@lem5254573 s)). Qed.
Lemma lem5254577 (s : real -> Prop) : (term197 s) = (term315 s).
Proof. exact (@lem17265 (term61 s) (term198 s)). Qed.
Lemma lem5254578 (s : real -> Prop) : (term197 s) = (term316 s).
Proof. exact (TRANS (@lem5254577 s) (@lem5254576 s)). Qed.
Lemma lem5254579 : term268 = term317.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5254578 s)). Qed.
Lemma lem5254580 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5254681 : term242 = term318.
Proof. exact (MK_COMB (@lem5254580) (@lem5254579)). Qed.
Lemma lem5254682 (h1 : term242) : term318.
Proof. exact (EQ_MP (@lem5254681) (@lem5254311 h1)). Qed.
Lemma lem5254687 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5254695 (s : real -> Prop) (h1 : term39 s) : term39 s.
Proof. exact (h1). Qed.
Lemma lem5254703 (x : real) (s : real -> Prop) (h1 : term166 x s) : term166 x s.
Proof. exact (h1). Qed.
Lemma lem5254728 (y : real) (x : real) (z : real) : (term296 y x z) = (term296 y x z).
Proof. exact (eq_refl (term296 y x z)). Qed.
Lemma lem5254729 (y : real) (x : real) : (term298 y x) = (term298 y x).
Proof. exact (fun_ext (fun z : real => @lem5254728 y x z)). Qed.
Lemma lem5254730 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254731 (y : real) (x : real) : (term299 y x) = (term299 y x).
Proof. exact (MK_COMB (@lem5254730) (@lem5254729 y x)). Qed.
Lemma lem5254732 (x : real) : (term300 x) = (term300 x).
Proof. exact (fun_ext (fun y : real => @lem5254731 y x)). Qed.
Lemma lem5254733 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254734 (x : real) : (term301 x) = (term301 x).
Proof. exact (MK_COMB (@lem5254733) (@lem5254732 x)). Qed.
Lemma lem5254735 : term302 = term302.
Proof. exact (fun_ext (fun x : real => @lem5254734 x)). Qed.
Lemma lem5254736 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254737 : term303 = term303.
Proof. exact (MK_COMB (@lem5254736) (@lem5254735)). Qed.
Lemma lem5254738 (h1 : term280) : term303.
Proof. exact (EQ_MP (@lem5254737) (@lem5254482 h1)). Qed.
Lemma lem5254775 (s : real -> Prop) (x : real) : (term309 s x) = (term309 s x).
Proof. exact (eq_refl (term309 s x)). Qed.
Lemma lem5254776 (s : real -> Prop) : (term310 s) = (term310 s).
Proof. exact (fun_ext (fun x : real => @lem5254775 s x)). Qed.
Lemma lem5254777 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254778 (s : real -> Prop) : (term311 s) = (term311 s).
Proof. exact (MK_COMB (@lem5254777) (@lem5254776 s)). Qed.
Lemma lem5254787 (s : real -> Prop) : (term266 s) = (term266 s).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5254788 (s : real -> Prop) : (term312 s) = (term312 s).
Proof. exact (MK_COMB (@lem5254787 s) (@lem5254778 s)). Qed.
Lemma lem5254803 (s : real -> Prop) : (term314 s) = (term314 s).
Proof. exact (eq_refl (term314 s)). Qed.
Lemma lem5254804 (s : real -> Prop) : (term316 s) = (term316 s).
Proof. exact (MK_COMB (@lem5254803 s) (@lem5254788 s)). Qed.
Lemma lem5254805 : term317 = term317.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5254804 s)). Qed.
Lemma lem5254806 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5254807 : term318 = term318.
Proof. exact (MK_COMB (@lem5254806) (@lem5254805)). Qed.
Lemma lem5254808 (h1 : term242) : term318.
Proof. exact (EQ_MP (@lem5254807) (@lem5254682 h1)). Qed.
Lemma lem5254824 (s : real -> Prop) (x : real) (y : real) (h1 : term282 s x y) : term282 s x y.
Proof. exact (h1). Qed.
Lemma lem5254830 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5254834 (s : real -> Prop) (h1 : term39 s) : term39 s.
Proof. exact (h1). Qed.
Lemma lem5254838 (x : real) (s : real -> Prop) (h1 : term166 x s) : term166 x s.
Proof. exact (h1). Qed.
Lemma lem5254852 (y : real) (x : real) (z : real) : (term296 y x z) = (term296 y x z).
Proof. exact (eq_refl (term296 y x z)). Qed.
Lemma lem5254853 (y : real) (x : real) : (term298 y x) = (term298 y x).
Proof. exact (fun_ext (fun z : real => @lem5254852 y x z)). Qed.
Lemma lem5254854 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254855 (y : real) (x : real) : (term299 y x) = (term299 y x).
Proof. exact (MK_COMB (@lem5254854) (@lem5254853 y x)). Qed.
Lemma lem5254856 (x : real) : (term300 x) = (term300 x).
Proof. exact (fun_ext (fun y : real => @lem5254855 y x)). Qed.
Lemma lem5254857 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254858 (x : real) : (term301 x) = (term301 x).
Proof. exact (MK_COMB (@lem5254857) (@lem5254856 x)). Qed.
Lemma lem5254859 : term302 = term302.
Proof. exact (fun_ext (fun x : real => @lem5254858 x)). Qed.
Lemma lem5254860 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254862 : term303 = term303.
Proof. exact (MK_COMB (@lem5254860) (@lem5254859)). Qed.
Lemma lem5254863 (h1 : term280) : term303.
Proof. exact (EQ_MP (@lem5254862) (@lem5254738 h1)). Qed.
Lemma lem5254881 {A : Type'} (P : Prop) (Q : A -> Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5254882 (P : Prop) (Q : real -> Prop) : (term321 P Q) = (term322 P Q).
Proof. exact (@lem5254881 real P Q). Qed.
Lemma lem5254883 (s : real -> Prop) : (term323 s) = (term324 s).
Proof. exact (@lem5254882 (term208 s) (term310 s)). Qed.
Lemma lem5254884 (s : real -> Prop) (x : real) : (term325 s x) = (term309 s x).
Proof. exact (eq_refl (term325 s x)). Qed.
Lemma lem5254885 (s : real -> Prop) : (term326 s) = (term310 s).
Proof. exact (fun_ext (fun x : real => @lem5254884 s x)). Qed.
Lemma lem5254886 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254887 (s : real -> Prop) : (term327 s) = (term311 s).
Proof. exact (MK_COMB (@lem5254886) (@lem5254885 s)). Qed.
Lemma lem5254888 (s : real -> Prop) : (term266 s) = (term266 s).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5254889 (s : real -> Prop) : (term323 s) = (term312 s).
Proof. exact (MK_COMB (@lem5254888 s) (@lem5254887 s)). Qed.
Lemma lem5254890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5254891 (s : real -> Prop) : (term328 s) = (term329 s).
Proof. exact (MK_COMB (@lem5254890) (@lem5254889 s)). Qed.
Lemma lem5254892 (s : real -> Prop) (x : real) : (term325 s x) = (term309 s x).
Proof. exact (eq_refl (term325 s x)). Qed.
Lemma lem5254893 (s : real -> Prop) : (term266 s) = (term266 s).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5254894 (s : real -> Prop) (x : real) : (term330 s x) = (term331 s x).
Proof. exact (MK_COMB (@lem5254893 s) (@lem5254892 s x)). Qed.
Lemma lem5254895 (s : real -> Prop) : (term332 s) = (term333 s).
Proof. exact (fun_ext (fun x : real => @lem5254894 s x)). Qed.
Lemma lem5254896 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254897 (s : real -> Prop) : (term324 s) = (term334 s).
Proof. exact (MK_COMB (@lem5254896) (@lem5254895 s)). Qed.
Lemma lem5254898 (s : real -> Prop) : ((term323 s) = (term324 s)) = ((term312 s) = (term334 s)).
Proof. exact (MK_COMB (@lem5254891 s) (@lem5254897 s)). Qed.
Lemma lem5254899 (s : real -> Prop) : (term312 s) = (term334 s).
Proof. exact (EQ_MP (@lem5254898 s) (@lem5254883 s)). Qed.
Lemma lem5254900 (s : real -> Prop) : (term314 s) = (term314 s).
Proof. exact (eq_refl (term314 s)). Qed.
Lemma lem5254901 (s : real -> Prop) : (term316 s) = (term335 s).
Proof. exact (MK_COMB (@lem5254900 s) (@lem5254899 s)). Qed.
Lemma lem5254903 {A : Type'} (P : Prop) (Q : A -> Prop) : (term336 A P Q) = (term337 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5254904 (P : Prop) (Q : real -> Prop) : (term338 P Q) = (term339 P Q).
Proof. exact (@lem5254903 real P Q). Qed.
Lemma lem5254905 (s : real -> Prop) : (term340 s) = (term341 s).
Proof. exact (@lem5254904 (term307 s) (term333 s)). Qed.
Lemma lem5254906 (s : real -> Prop) (x : real) : (term342 s x) = (term331 s x).
Proof. exact (eq_refl (term342 s x)). Qed.
Lemma lem5254907 (s : real -> Prop) : (term343 s) = (term333 s).
Proof. exact (fun_ext (fun x : real => @lem5254906 s x)). Qed.
Lemma lem5254908 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254909 (s : real -> Prop) : (term344 s) = (term334 s).
Proof. exact (MK_COMB (@lem5254908) (@lem5254907 s)). Qed.
Lemma lem5254910 (s : real -> Prop) : (term314 s) = (term314 s).
Proof. exact (eq_refl (term314 s)). Qed.
Lemma lem5254911 (s : real -> Prop) : (term340 s) = (term335 s).
Proof. exact (MK_COMB (@lem5254910 s) (@lem5254909 s)). Qed.
Lemma lem5254912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5254913 (s : real -> Prop) : (term345 s) = (term346 s).
Proof. exact (MK_COMB (@lem5254912) (@lem5254911 s)). Qed.
Lemma lem5254914 (s : real -> Prop) (x : real) : (term342 s x) = (term331 s x).
Proof. exact (eq_refl (term342 s x)). Qed.
Lemma lem5254915 (s : real -> Prop) : (term314 s) = (term314 s).
Proof. exact (eq_refl (term314 s)). Qed.
Lemma lem5254916 (s : real -> Prop) (x : real) : (term347 s x) = (term348 s x).
Proof. exact (MK_COMB (@lem5254915 s) (@lem5254914 s x)). Qed.
Lemma lem5254917 (s : real -> Prop) : (term349 s) = (term350 s).
Proof. exact (fun_ext (fun x : real => @lem5254916 s x)). Qed.
Lemma lem5254918 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254919 (s : real -> Prop) : (term341 s) = (term351 s).
Proof. exact (MK_COMB (@lem5254918) (@lem5254917 s)). Qed.
Lemma lem5254920 (s : real -> Prop) : ((term340 s) = (term341 s)) = ((term335 s) = (term351 s)).
Proof. exact (MK_COMB (@lem5254913 s) (@lem5254919 s)). Qed.
Lemma lem5254921 (s : real -> Prop) : (term335 s) = (term351 s).
Proof. exact (EQ_MP (@lem5254920 s) (@lem5254905 s)). Qed.
Lemma lem5254922 (s : real -> Prop) : (term316 s) = (term351 s).
Proof. exact (TRANS (@lem5254901 s) (@lem5254921 s)). Qed.
Lemma lem5254923 : term317 = term352.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5254922 s)). Qed.
Lemma lem5254924 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5254925 : term318 = term353.
Proof. exact (MK_COMB (@lem5254924) (@lem5254923)). Qed.
Lemma lem5254954 (s : real -> Prop) (x : real) : (term348 s x) = (term354 s x).
Proof. exact (@lem19490 (term208 s) (term307 s) (term309 s x)). Qed.
Lemma lem5254955 (s : real -> Prop) : (term350 s) = (term355 s).
Proof. exact (fun_ext (fun x : real => @lem5254954 s x)). Qed.
Lemma lem5254956 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5254957 (s : real -> Prop) : (term351 s) = (term356 s).
Proof. exact (MK_COMB (@lem5254956) (@lem5254955 s)). Qed.
Lemma lem5254958 : term352 = term357.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5254957 s)). Qed.
Lemma lem5254959 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5254960 : term353 = term358.
Proof. exact (MK_COMB (@lem5254959) (@lem5254958)). Qed.
Lemma lem5254961 : term318 = term358.
Proof. exact (TRANS (@lem5254925) (@lem5254960)). Qed.
Lemma lem5254962 (h1 : term242) : term358.
Proof. exact (EQ_MP (@lem5254961) (@lem5254808 h1)). Qed.
Lemma lem5254971 (_68816 : real) (h1 : term280) : term359 _68816.
Proof. exact (@lem5254863 h1 _68816). Qed.
Lemma lem5254972 (_68816 : real) : (term359 _68816) = (term301 _68816).
Proof. exact (eq_refl (term359 _68816)). Qed.
Lemma lem5254973 (_68816 : real) (h1 : term280) : term301 _68816.
Proof. exact (EQ_MP (@lem5254972 _68816) (@lem5254971 _68816 h1)). Qed.
Lemma lem5254974 (_68816 : real) (_68817 : real) (h1 : term280) : term360 _68816 _68817.
Proof. exact (@lem5254973 _68816 h1 _68817). Qed.
Lemma lem5254975 (_68817 : real) (_68816 : real) : (term360 _68816 _68817) = (term299 _68817 _68816).
Proof. exact (eq_refl (term360 _68816 _68817)). Qed.
Lemma lem5254976 (_68817 : real) (_68816 : real) (h1 : term280) : term299 _68817 _68816.
Proof. exact (EQ_MP (@lem5254975 _68817 _68816) (@lem5254974 _68816 _68817 h1)). Qed.
Lemma lem5254977 (_68817 : real) (_68816 : real) (_68818 : real) (h1 : term280) : term361 _68817 _68816 _68818.
Proof. exact (@lem5254976 _68817 _68816 h1 _68818). Qed.
Lemma lem5254978 (_68817 : real) (_68816 : real) (_68818 : real) : (term361 _68817 _68816 _68818) = (term296 _68817 _68816 _68818).
Proof. exact (eq_refl (term361 _68817 _68816 _68818)). Qed.
Lemma lem5254979 (_68817 : real) (_68816 : real) (_68818 : real) (h1 : term280) : term296 _68817 _68816 _68818.
Proof. exact (EQ_MP (@lem5254978 _68817 _68816 _68818) (@lem5254977 _68817 _68816 _68818 h1)). Qed.
Lemma lem5254986 (_68821 : real -> Prop) (h1 : term242) : term362 _68821.
Proof. exact (@lem5254962 h1 _68821). Qed.
Lemma lem5254987 (_68821 : real -> Prop) : (term362 _68821) = (term356 _68821).
Proof. exact (eq_refl (term362 _68821)). Qed.
Lemma lem5254988 (_68821 : real -> Prop) (h1 : term242) : term356 _68821.
Proof. exact (EQ_MP (@lem5254987 _68821) (@lem5254986 _68821 h1)). Qed.
Lemma lem5254989 (_68821 : real -> Prop) (_68822 : real) (h1 : term242) : term363 _68821 _68822.
Proof. exact (@lem5254988 _68821 h1 _68822). Qed.
Lemma lem5254990 (_68821 : real -> Prop) (_68822 : real) : (term363 _68821 _68822) = (term354 _68821 _68822).
Proof. exact (eq_refl (term363 _68821 _68822)). Qed.
Lemma lem5254991 (_68821 : real -> Prop) (_68822 : real) (h1 : term242) : term354 _68821 _68822.
Proof. exact (EQ_MP (@lem5254990 _68821 _68822) (@lem5254989 _68821 _68822 h1)). Qed.
Lemma lem5254992 (_68821 : real -> Prop) (_68822 : real) (h1 : term242) : term364 _68821 _68822.
Proof. exact (proj2 (@lem5254991 _68821 _68822 h1)). Qed.
Lemma lem5254995 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5254997 (s : real -> Prop) (h1 : term39 s) : term39 s.
Proof. exact (h1). Qed.
Lemma lem5254999 (x : real) (s : real -> Prop) (h1 : term166 x s) : term166 x s.
Proof. exact (h1). Qed.
Lemma lem5255010 (_68817 : real) (_68816 : real) (_68818 : real) : (term296 _68817 _68816 _68818) = (term365 _68817 _68816 _68818).
Proof. exact (@lem5252879 (term366 _68816 _68817) (term366 _68817 _68818) (real_le _68816 _68818)). Qed.
Lemma lem5255011 (_68817 : real) (_68816 : real) (_68818 : real) (h1 : term280) : term365 _68817 _68816 _68818.
Proof. exact (EQ_MP (@lem5255010 _68817 _68816 _68818) (@lem5254979 _68817 _68816 _68818 h1)). Qed.
Lemma lem5255021 (s : real -> Prop) (x : real) (y : real) (h1 : term282 s x y) : term366 x y.
Proof. exact (proj2 (@lem5254824 s x y h1)). Qed.
Lemma lem5255048 (_68821 : real -> Prop) (_68822 : real) : (term364 _68821 _68822) = (term367 _68821 _68822).
Proof. exact (@lem5252879 (term368 _68821) (_68821 = (@EMPTY real)) (term309 _68821 _68822)). Qed.
Lemma lem5255049 (_68821 : real -> Prop) (_68822 : real) (h1 : term242) : term367 _68821 _68822.
Proof. exact (EQ_MP (@lem5255048 _68821 _68822) (@lem5254992 _68821 _68822 h1)). Qed.
Lemma lem5255113 (x : real) (s : real -> Prop) (h1 : term166 x s) : term166 x s.
Proof. exact (h1). Qed.
Lemma lem5255114 (x : real) (s : real -> Prop) (h1 : term166 x s) : term369 x s.
Proof. exact (fun h0 : term182 x s => @lem5255113 x s h1). Qed.
Lemma lem5255116 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5255117 (x : real) (s : real -> Prop) : (term369 x s) = (term166 x s).
Proof. exact (@lem5255116 (term166 x s)). Qed.
Lemma lem5255118 (x : real) (s : real -> Prop) (h1 : term166 x s) : term166 x s.
Proof. exact (EQ_MP (@lem5255117 x s) (@lem5255114 x s h1)). Qed.
Lemma lem5255120 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5255121 (s : real -> Prop) (h1 : @FINITE real s) : term371 s.
Proof. exact (fun h0 : term368 s => @lem5255120 s h1). Qed.
Lemma lem5255123 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5255124 (s : real -> Prop) : (term371 s) = (@FINITE real s).
Proof. exact (@lem5255123 (@FINITE real s)). Qed.
Lemma lem5255125 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (EQ_MP (@lem5255124 s) (@lem5255121 s h1)). Qed.
Lemma lem5255127 (s : real -> Prop) (h1 : term39 s) : term39 s.
Proof. exact (h1). Qed.
Lemma lem5255128 (s : real -> Prop) (h1 : term39 s) : term372 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5255127 s h1). Qed.
Lemma lem5255130 (p : Prop) : (term373 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5255131 (s : real -> Prop) : (term372 s) = (term39 s).
Proof. exact (@lem5255130 (s = (@EMPTY real))). Qed.
Lemma lem5255132 (s : real -> Prop) (h1 : term39 s) : term39 s.
Proof. exact (EQ_MP (@lem5255131 s) (@lem5255128 s h1)). Qed.
Lemma lem5255134 (s : real -> Prop) (x : real) (y : real) (h1 : term282 s x y) : @IN real y s.
Proof. exact (proj1 (@lem5254824 s x y h1)). Qed.
Lemma lem5255135 (s : real -> Prop) (x : real) (y : real) (h1 : term282 s x y) : term374 y s.
Proof. exact (fun h0 : term375 y s => @lem5255134 s x y h1). Qed.
Lemma lem5255137 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5255138 (y : real) (s : real -> Prop) : (term374 y s) = (@IN real y s).
Proof. exact (@lem5255137 (@IN real y s)). Qed.
Lemma lem5255139 (s : real -> Prop) (x : real) (y : real) (h1 : term282 s x y) : @IN real y s.
Proof. exact (EQ_MP (@lem5255138 y s) (@lem5255135 s x y h1)). Qed.
Lemma lem5255145 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5255146 (_68821 : real -> Prop) (_68822 : real) : (term367 _68821 _68822) = (term376 _68821 _68822).
Proof. exact (@lem5255145 (_68821 = (@EMPTY real)) (term368 _68821) (term309 _68821 _68822)). Qed.
Lemma lem5255172 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5255173 (_68822 : real) (_68821 : real -> Prop) : (term309 _68821 _68822) = (term377 _68822 _68821).
Proof. exact (@lem5255172 (term202 _68821 _68822) (term375 _68822 _68821)). Qed.
Lemma lem5255179 (_68821 : real -> Prop) : (term305 _68821) = (term305 _68821).
Proof. exact (eq_refl (term305 _68821)). Qed.
Lemma lem5255180 (_68822 : real) (_68821 : real -> Prop) : (term378 _68821 _68822) = (term379 _68822 _68821).
Proof. exact (MK_COMB (@lem5255179 _68821) (@lem5255173 _68822 _68821)). Qed.
Lemma lem5255184 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5255185 (_68822 : real) (_68821 : real -> Prop) : (term379 _68822 _68821) = (term380 _68822 _68821).
Proof. exact (@lem5255184 (term202 _68821 _68822) (term368 _68821) (term375 _68822 _68821)). Qed.
Lemma lem5255201 (_68822 : real) (_68821 : real -> Prop) : (term378 _68821 _68822) = (term380 _68822 _68821).
Proof. exact (TRANS (@lem5255180 _68822 _68821) (@lem5255185 _68822 _68821)). Qed.
Lemma lem5255202 (_68821 : real -> Prop) : (term381 _68821) = (term381 _68821).
Proof. exact (eq_refl (term381 _68821)). Qed.
Lemma lem5255203 (_68822 : real) (_68821 : real -> Prop) : (term376 _68821 _68822) = (term382 _68822 _68821).
Proof. exact (MK_COMB (@lem5255202 _68821) (@lem5255201 _68822 _68821)). Qed.
Lemma lem5255214 (_68822 : real) (_68821 : real -> Prop) : (term367 _68821 _68822) = (term382 _68822 _68821).
Proof. exact (TRANS (@lem5255146 _68821 _68822) (@lem5255203 _68822 _68821)). Qed.
Lemma lem5255215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5255216 (_68822 : real) (_68821 : real -> Prop) : (term383 _68821 _68822) = (term384 _68822 _68821).
Proof. exact (MK_COMB (@lem5255215) (@lem5255214 _68822 _68821)). Qed.
Lemma lem5255230 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5255231 (_68822 : real) (_68821 : real -> Prop) : (term385 _68822 _68821) = (term386 _68822 _68821).
Proof. exact (@lem5255230 (_68821 = (@EMPTY real)) (term368 _68821) (term375 _68822 _68821)). Qed.
Lemma lem5255249 (_68821 : real -> Prop) (_68822 : real) : (term387 _68821 _68822) = (term387 _68821 _68822).
Proof. exact (eq_refl (term387 _68821 _68822)). Qed.
Lemma lem5255250 (_68822 : real) (_68821 : real -> Prop) : (term388 _68822 _68821) = (term389 _68822 _68821).
Proof. exact (MK_COMB (@lem5255249 _68821 _68822) (@lem5255231 _68822 _68821)). Qed.
Lemma lem5255254 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5255255 (_68822 : real) (_68821 : real -> Prop) : (term389 _68822 _68821) = (term382 _68822 _68821).
Proof. exact (@lem5255254 (_68821 = (@EMPTY real)) (term202 _68821 _68822) (term390 _68822 _68821)). Qed.
Lemma lem5255283 (_68822 : real) (_68821 : real -> Prop) : (term388 _68822 _68821) = (term382 _68822 _68821).
Proof. exact (TRANS (@lem5255250 _68822 _68821) (@lem5255255 _68822 _68821)). Qed.
Lemma lem5255284 (_68822 : real) (_68821 : real -> Prop) : ((term367 _68821 _68822) = (term388 _68822 _68821)) = ((term382 _68822 _68821) = (term382 _68822 _68821)).
Proof. exact (MK_COMB (@lem5255216 _68822 _68821) (@lem5255283 _68822 _68821)). Qed.
Lemma lem5255286 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5255287 (x : Prop) : (x = x) = True.
Proof. exact (@lem5255286 Prop x). Qed.
Lemma lem5255288 (_68822 : real) (_68821 : real -> Prop) : ((term382 _68822 _68821) = (term382 _68822 _68821)) = True.
Proof. exact (@lem5255287 (term382 _68822 _68821)). Qed.
Lemma lem5255289 (_68822 : real) (_68821 : real -> Prop) : ((term367 _68821 _68822) = (term388 _68822 _68821)) = True.
Proof. exact (TRANS (@lem5255284 _68822 _68821) (@lem5255288 _68822 _68821)). Qed.
Lemma lem5255290 (_68822 : real) (_68821 : real -> Prop) : True = ((term367 _68821 _68822) = (term388 _68822 _68821)).
Proof. exact (SYM (@lem5255289 _68822 _68821)). Qed.
Lemma lem5255291 (_68822 : real) (_68821 : real -> Prop) : (term367 _68821 _68822) = (term388 _68822 _68821).
Proof. exact (EQ_MP (@lem5255290 _68822 _68821) (@lem0)). Qed.
Lemma lem5255292 (_68822 : real) (_68821 : real -> Prop) (h1 : term242) : term388 _68822 _68821.
Proof. exact (EQ_MP (@lem5255291 _68822 _68821) (@lem5255049 _68821 _68822 h1)). Qed.
Lemma lem5255294 (b : Prop) (a : Prop) : (a \/ b) = (term391 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5255295 (_68821 : real -> Prop) (_68822 : real) : (term388 _68822 _68821) = (term392 _68821 _68822).
Proof. exact (@lem5255294 (term385 _68822 _68821) (term202 _68821 _68822)). Qed.
Lemma lem5255297 (a : Prop) (b : Prop) : (term393 a b) = (term394 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5255298 (_68822 : real) (_68821 : real -> Prop) : (term395 _68822 _68821) = (term396 _68822 _68821).
Proof. exact (@lem5255297 (term368 _68821) (term397 _68822 _68821)). Qed.
Lemma lem5255300 (a : Prop) : (term398 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5255301 (_68821 : real -> Prop) : (term399 _68821) = (@FINITE real _68821).
Proof. exact (@lem5255300 (@FINITE real _68821)). Qed.
Lemma lem5255302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5255303 (_68821 : real -> Prop) : (term400 _68821) = (term213 _68821).
Proof. exact (MK_COMB (@lem5255302) (@lem5255301 _68821)). Qed.
Lemma lem5255305 (a : Prop) (b : Prop) : (term393 a b) = (term394 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5255306 (_68822 : real) (_68821 : real -> Prop) : (term401 _68822 _68821) = (term402 _68822 _68821).
Proof. exact (@lem5255305 (_68821 = (@EMPTY real)) (term375 _68822 _68821)). Qed.
Lemma lem5255308 (a : Prop) : (term398 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5255309 (_68822 : real) (_68821 : real -> Prop) : (term403 _68822 _68821) = (@IN real _68822 _68821).
Proof. exact (@lem5255308 (@IN real _68822 _68821)). Qed.
Lemma lem5255310 (_68821 : real -> Prop) : (term404 _68821) = (term404 _68821).
Proof. exact (eq_refl (term404 _68821)). Qed.
Lemma lem5255311 (_68822 : real) (_68821 : real -> Prop) : (term402 _68822 _68821) = (term405 _68822 _68821).
Proof. exact (MK_COMB (@lem5255310 _68821) (@lem5255309 _68822 _68821)). Qed.
Lemma lem5255312 (_68822 : real) (_68821 : real -> Prop) : (term401 _68822 _68821) = (term405 _68822 _68821).
Proof. exact (TRANS (@lem5255306 _68822 _68821) (@lem5255311 _68822 _68821)). Qed.
Lemma lem5255313 (_68822 : real) (_68821 : real -> Prop) : (term396 _68822 _68821) = (term406 _68822 _68821).
Proof. exact (MK_COMB (@lem5255303 _68821) (@lem5255312 _68822 _68821)). Qed.
Lemma lem5255314 (_68822 : real) (_68821 : real -> Prop) : (term395 _68822 _68821) = (term406 _68822 _68821).
Proof. exact (TRANS (@lem5255298 _68822 _68821) (@lem5255313 _68822 _68821)). Qed.
Lemma lem5255315 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5255316 (_68822 : real) (_68821 : real -> Prop) : (term407 _68822 _68821) = (term408 _68822 _68821).
Proof. exact (MK_COMB (@lem5255315) (@lem5255314 _68822 _68821)). Qed.
Lemma lem5255317 (_68821 : real -> Prop) (_68822 : real) : (term202 _68821 _68822) = (term202 _68821 _68822).
Proof. exact (eq_refl (term202 _68821 _68822)). Qed.
Lemma lem5255318 (_68821 : real -> Prop) (_68822 : real) : (term392 _68821 _68822) = (term409 _68821 _68822).
Proof. exact (MK_COMB (@lem5255316 _68822 _68821) (@lem5255317 _68821 _68822)). Qed.
Lemma lem5255319 (_68821 : real -> Prop) (_68822 : real) : (term388 _68822 _68821) = (term409 _68821 _68822).
Proof. exact (TRANS (@lem5255295 _68821 _68822) (@lem5255318 _68821 _68822)). Qed.
Lemma lem5255321 (s : real -> Prop) (x : real) (y : real) (h1 : term39 s) (h2 : term282 s x y) : term405 y s.
Proof. exact (conj (@lem5255132 s h1) (@lem5255139 s x y h2)). Qed.
Lemma lem5255322 (s : real -> Prop) (x : real) (y : real) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term282 s x y) : term406 y s.
Proof. exact (conj (@lem5255125 s h1) (@lem5255321 s x y h2 h3)). Qed.
Lemma lem5255324 (_68821 : real -> Prop) (_68822 : real) (h1 : term242) : term409 _68821 _68822.
Proof. exact (EQ_MP (@lem5255319 _68821 _68822) (@lem5255292 _68822 _68821 h1)). Qed.
Lemma lem5255325 (s : real -> Prop) (y : real) (h1 : term242) : term409 s y.
Proof. exact (@lem5255324 s y h1). Qed.
Lemma lem5255328 (s : real -> Prop) (x : real) (y : real) (h1 : term242) (h2 : @FINITE real s) (h3 : term39 s) (h4 : term282 s x y) : term202 s y.
Proof. exact (@lem5255325 s y h1 (@lem5255322 s x y h2 h3 h4)). Qed.
Lemma lem5255329 (s : real -> Prop) (x : real) (y : real) (h1 : term242) (h2 : @FINITE real s) (h3 : term39 s) (h4 : term282 s x y) : term410 s y.
Proof. exact (fun h0 : term411 s y => @lem5255328 s x y h1 h2 h3 h4). Qed.
Lemma lem5255331 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5255332 (s : real -> Prop) (y : real) : (term410 s y) = (term202 s y).
Proof. exact (@lem5255331 (term202 s y)). Qed.
Lemma lem5255333 (s : real -> Prop) (x : real) (y : real) (h1 : term242) (h2 : @FINITE real s) (h3 : term39 s) (h4 : term282 s x y) : term202 s y.
Proof. exact (EQ_MP (@lem5255332 s y) (@lem5255329 s x y h1 h2 h3 h4)). Qed.
Lemma lem5255349 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5255350 (_68816 : real) (_68817 : real) (_68818 : real) : (term412 _68817 _68816 _68818) = (term413 _68816 _68817 _68818).
Proof. exact (@lem5255349 (real_le _68816 _68818) (term366 _68817 _68818)). Qed.
Lemma lem5255356 (_68816 : real) (_68817 : real) : (term414 _68816 _68817) = (term414 _68816 _68817).
Proof. exact (eq_refl (term414 _68816 _68817)). Qed.
Lemma lem5255357 (_68816 : real) (_68817 : real) (_68818 : real) : (term365 _68817 _68816 _68818) = (term415 _68816 _68817 _68818).
Proof. exact (MK_COMB (@lem5255356 _68816 _68817) (@lem5255350 _68816 _68817 _68818)). Qed.
Lemma lem5255361 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5255362 (_68816 : real) (_68817 : real) (_68818 : real) : (term415 _68816 _68817 _68818) = (term416 _68816 _68817 _68818).
Proof. exact (@lem5255361 (real_le _68816 _68818) (term366 _68816 _68817) (term366 _68817 _68818)). Qed.
Lemma lem5255378 (_68816 : real) (_68817 : real) (_68818 : real) : (term365 _68817 _68816 _68818) = (term416 _68816 _68817 _68818).
Proof. exact (TRANS (@lem5255357 _68816 _68817 _68818) (@lem5255362 _68816 _68817 _68818)). Qed.
Lemma lem5255379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5255380 (_68816 : real) (_68817 : real) (_68818 : real) : (term417 _68817 _68816 _68818) = (term418 _68816 _68817 _68818).
Proof. exact (MK_COMB (@lem5255379) (@lem5255378 _68816 _68817 _68818)). Qed.
Lemma lem5255396 (_68816 : real) (_68817 : real) (_68818 : real) : (term416 _68816 _68817 _68818) = (term416 _68816 _68817 _68818).
Proof. exact (eq_refl (term416 _68816 _68817 _68818)). Qed.
Lemma lem5255397 (_68816 : real) (_68817 : real) (_68818 : real) : ((term365 _68817 _68816 _68818) = (term416 _68816 _68817 _68818)) = ((term416 _68816 _68817 _68818) = (term416 _68816 _68817 _68818)).
Proof. exact (MK_COMB (@lem5255380 _68816 _68817 _68818) (@lem5255396 _68816 _68817 _68818)). Qed.
Lemma lem5255399 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5255400 (x : Prop) : (x = x) = True.
Proof. exact (@lem5255399 Prop x). Qed.
Lemma lem5255401 (_68816 : real) (_68817 : real) (_68818 : real) : ((term416 _68816 _68817 _68818) = (term416 _68816 _68817 _68818)) = True.
Proof. exact (@lem5255400 (term416 _68816 _68817 _68818)). Qed.
Lemma lem5255402 (_68816 : real) (_68817 : real) (_68818 : real) : ((term365 _68817 _68816 _68818) = (term416 _68816 _68817 _68818)) = True.
Proof. exact (TRANS (@lem5255397 _68816 _68817 _68818) (@lem5255401 _68816 _68817 _68818)). Qed.
Lemma lem5255403 (_68816 : real) (_68817 : real) (_68818 : real) : True = ((term365 _68817 _68816 _68818) = (term416 _68816 _68817 _68818)).
Proof. exact (SYM (@lem5255402 _68816 _68817 _68818)). Qed.
Lemma lem5255404 (_68816 : real) (_68817 : real) (_68818 : real) : (term365 _68817 _68816 _68818) = (term416 _68816 _68817 _68818).
Proof. exact (EQ_MP (@lem5255403 _68816 _68817 _68818) (@lem0)). Qed.
Lemma lem5255405 (_68816 : real) (_68817 : real) (_68818 : real) (h1 : term280) : term416 _68816 _68817 _68818.
Proof. exact (EQ_MP (@lem5255404 _68816 _68817 _68818) (@lem5255011 _68817 _68816 _68818 h1)). Qed.
Lemma lem5255407 (b : Prop) (a : Prop) : (a \/ b) = (term391 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5255408 (_68817 : real) (_68816 : real) (_68818 : real) : (term416 _68816 _68817 _68818) = (term419 _68817 _68816 _68818).
Proof. exact (@lem5255407 (term292 _68816 _68817 _68818) (real_le _68816 _68818)). Qed.
Lemma lem5255410 (a : Prop) (b : Prop) : (term393 a b) = (term394 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5255411 (_68816 : real) (_68817 : real) (_68818 : real) : (term420 _68816 _68817 _68818) = (term421 _68816 _68817 _68818).
Proof. exact (@lem5255410 (term366 _68816 _68817) (term366 _68817 _68818)). Qed.
Lemma lem5255413 (a : Prop) : (term398 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5255414 (_68816 : real) (_68817 : real) : (term422 _68816 _68817) = (real_le _68816 _68817).
Proof. exact (@lem5255413 (real_le _68816 _68817)). Qed.
Lemma lem5255415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5255416 (_68816 : real) (_68817 : real) : (term423 _68816 _68817) = (term424 _68816 _68817).
Proof. exact (MK_COMB (@lem5255415) (@lem5255414 _68816 _68817)). Qed.
Lemma lem5255418 (a : Prop) : (term398 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5255419 (_68817 : real) (_68818 : real) : (term422 _68817 _68818) = (real_le _68817 _68818).
Proof. exact (@lem5255418 (real_le _68817 _68818)). Qed.
Lemma lem5255420 (_68816 : real) (_68817 : real) (_68818 : real) : (term421 _68816 _68817 _68818) = (term297 _68816 _68817 _68818).
Proof. exact (MK_COMB (@lem5255416 _68816 _68817) (@lem5255419 _68817 _68818)). Qed.
Lemma lem5255421 (_68816 : real) (_68817 : real) (_68818 : real) : (term420 _68816 _68817 _68818) = (term297 _68816 _68817 _68818).
Proof. exact (TRANS (@lem5255411 _68816 _68817 _68818) (@lem5255420 _68816 _68817 _68818)). Qed.
Lemma lem5255422 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5255423 (_68816 : real) (_68817 : real) (_68818 : real) : (term425 _68816 _68817 _68818) = (term426 _68816 _68817 _68818).
Proof. exact (MK_COMB (@lem5255422) (@lem5255421 _68816 _68817 _68818)). Qed.
Lemma lem5255424 (_68816 : real) (_68818 : real) : (real_le _68816 _68818) = (real_le _68816 _68818).
Proof. exact (eq_refl (real_le _68816 _68818)). Qed.
Lemma lem5255425 (_68817 : real) (_68816 : real) (_68818 : real) : (term419 _68817 _68816 _68818) = (term274 _68817 _68816 _68818).
Proof. exact (MK_COMB (@lem5255423 _68816 _68817 _68818) (@lem5255424 _68816 _68818)). Qed.
Lemma lem5255426 (_68817 : real) (_68816 : real) (_68818 : real) : (term416 _68816 _68817 _68818) = (term274 _68817 _68816 _68818).
Proof. exact (TRANS (@lem5255408 _68817 _68816 _68818) (@lem5255425 _68817 _68816 _68818)). Qed.
Lemma lem5255428 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : @FINITE real s) (h3 : term39 s) (h4 : term282 s x y) (h5 : term166 x s) : term427 x s y.
Proof. exact (conj (@lem5255118 x s h5) (@lem5255333 s x y h1 h2 h3 h4)). Qed.
Lemma lem5255430 (_68817 : real) (_68816 : real) (_68818 : real) (h1 : term280) : term274 _68817 _68816 _68818.
Proof. exact (EQ_MP (@lem5255426 _68817 _68816 _68818) (@lem5255405 _68816 _68817 _68818 h1)). Qed.
Lemma lem5255431 (s : real -> Prop) (x : real) (y : real) (h1 : term280) : term428 s x y.
Proof. exact (@lem5255430 (inf s) x y h1). Qed.
Lemma lem5255434 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : real_le x y.
Proof. exact (@lem5255431 s x y h2 (@lem5255428 y x s h1 h3 h4 h5 h6)). Qed.
Lemma lem5255435 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : term429 x y.
Proof. exact (fun h0 : term366 x y => @lem5255434 y x s h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5255437 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5255438 (x : real) (y : real) : (term429 x y) = (real_le x y).
Proof. exact (@lem5255437 (real_le x y)). Qed.
Lemma lem5255439 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : real_le x y.
Proof. exact (EQ_MP (@lem5255438 x y) (@lem5255435 y x s h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5255442 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5255444 (x : real) (y : real) : (term366 x y) = (term430 x y).
Proof. exact (@lem5255442 (real_le x y)). Qed.
Lemma lem5255447 (s : real -> Prop) (x : real) (y : real) (h1 : term282 s x y) : term430 x y.
Proof. exact (EQ_MP (@lem5255444 x y) (@lem5255021 s x y h1)). Qed.
Lemma lem5255450 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (@lem5255447 s x y h5 (@lem5255439 y x s h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5255451 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : term431.
Proof. exact (fun h0 : ~ False => @lem5255450 y x s h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5255453 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5255454 : term431 = False.
Proof. exact (@lem5255453 False). Qed.
Lemma lem5255455 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255454) (@lem5255451 y x s h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5255456 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : (term166 x s) = False.
Proof. exact (prop_ext (fun h7 : term166 x s => @lem5255455 y x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254999 x s h6)). Qed.
Lemma lem5255457 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255456 y x s h1 h2 h3 h4 h5 h6) (@lem5254999 x s h6)). Qed.
Lemma lem5255458 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : (term39 s) = False.
Proof. exact (prop_ext (fun h7 : term39 s => @lem5255457 y x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254997 s h4)). Qed.
Lemma lem5255459 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255458 y x s h1 h2 h3 h4 h5 h6) (@lem5254997 s h4)). Qed.
Lemma lem5255460 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : (@FINITE real s) = False.
Proof. exact (prop_ext (fun h7 : @FINITE real s => @lem5255459 y x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254995 s h3)). Qed.
Lemma lem5255461 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255460 y x s h1 h2 h3 h4 h5 h6) (@lem5254995 s h3)). Qed.
Lemma lem5255462 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : (term166 x s) = False.
Proof. exact (prop_ext (fun h7 : term166 x s => @lem5255461 y x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254838 x s h6)). Qed.
Lemma lem5255463 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255462 y x s h1 h2 h3 h4 h5 h6) (@lem5254838 x s h6)). Qed.
Lemma lem5255464 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : (term39 s) = False.
Proof. exact (prop_ext (fun h7 : term39 s => @lem5255463 y x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254834 s h4)). Qed.
Lemma lem5255465 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255464 y x s h1 h2 h3 h4 h5 h6) (@lem5254834 s h4)). Qed.
Lemma lem5255466 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : (@FINITE real s) = False.
Proof. exact (prop_ext (fun h7 : @FINITE real s => @lem5255465 y x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254830 s h3)). Qed.
Lemma lem5255467 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255466 y x s h1 h2 h3 h4 h5 h6) (@lem5254830 s h3)). Qed.
Lemma lem5255468 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : (term166 x s) = False.
Proof. exact (prop_ext (fun h7 : term166 x s => @lem5255467 y x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254838 x s h6)). Qed.
Lemma lem5255469 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255468 y x s h1 h2 h3 h4 h5 h6) (@lem5254838 x s h6)). Qed.
Lemma lem5255470 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : (term39 s) = False.
Proof. exact (prop_ext (fun h7 : term39 s => @lem5255469 y x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254834 s h4)). Qed.
Lemma lem5255471 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255470 y x s h1 h2 h3 h4 h5 h6) (@lem5254834 s h4)). Qed.
Lemma lem5255472 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : (@FINITE real s) = False.
Proof. exact (prop_ext (fun h7 : @FINITE real s => @lem5255471 y x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254830 s h3)). Qed.
Lemma lem5255473 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255472 y x s h1 h2 h3 h4 h5 h6) (@lem5254830 s h3)). Qed.
Lemma lem5255474 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : (term282 s x y) = False.
Proof. exact (prop_ext (fun h7 : term282 s x y => @lem5255473 y x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254824 s x y h5)). Qed.
Lemma lem5255475 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255474 y x s h1 h2 h3 h4 h5 h6) (@lem5254824 s x y h5)). Qed.
Lemma lem5255476 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : (term166 x s) = False.
Proof. exact (prop_ext (fun h7 : term166 x s => @lem5255475 y x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254703 x s h6)). Qed.
Lemma lem5255477 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255476 y x s h1 h2 h3 h4 h5 h6) (@lem5254703 x s h6)). Qed.
Lemma lem5255478 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : (term39 s) = False.
Proof. exact (prop_ext (fun h7 : term39 s => @lem5255477 y x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254695 s h4)). Qed.
Lemma lem5255479 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255478 y x s h1 h2 h3 h4 h5 h6) (@lem5254695 s h4)). Qed.
Lemma lem5255480 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : (@FINITE real s) = False.
Proof. exact (prop_ext (fun h7 : @FINITE real s => @lem5255479 y x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254687 s h3)). Qed.
Lemma lem5255481 (y : real) (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term282 s x y) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255480 y x s h1 h2 h3 h4 h5 h6) (@lem5254687 s h3)). Qed.
Lemma lem5255482 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term235 s x) (h5 : term39 s) (h6 : term166 x s) : False.
Proof. exact (ex_elim (@lem5254399 s x h4) (fun y : real => fun h0 : term289 s x y => @lem5255481 y x s h1 h2 h3 h5 h0 h6)). Qed.
Lemma lem5255483 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term235 s x) (h5 : term39 s) (h6 : term166 x s) : (term166 x s) = False.
Proof. exact (prop_ext (fun h7 : term166 x s => @lem5255482 x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254329 x s h6)). Qed.
Lemma lem5255484 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term235 s x) (h5 : term39 s) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255483 x s h1 h2 h3 h4 h5 h6) (@lem5254329 x s h6)). Qed.
Lemma lem5255485 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term235 s x) (h5 : term39 s) (h6 : term166 x s) : (term39 s) = False.
Proof. exact (prop_ext (fun h7 : term39 s => @lem5255484 x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254323 s h5)). Qed.
Lemma lem5255486 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term235 s x) (h5 : term39 s) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255485 x s h1 h2 h3 h4 h5 h6) (@lem5254323 s h5)). Qed.
Lemma lem5255487 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term235 s x) (h5 : term39 s) (h6 : term166 x s) : (@FINITE real s) = False.
Proof. exact (prop_ext (fun h7 : @FINITE real s => @lem5255486 x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5254317 s h3)). Qed.
Lemma lem5255488 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term235 s x) (h5 : term39 s) (h6 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255487 x s h1 h2 h3 h4 h5 h6) (@lem5254317 s h3)). Qed.
Lemma lem5255489 (x : real) (s : real -> Prop) (h1 : term280) (h2 : @FINITE real s) (h3 : term235 s x) (h4 : term39 s) (h5 : term166 x s) : term240.
Proof. exact (fun h0 : term242 => @lem5255488 x s h0 h1 h2 h3 h4 h5). Qed.
Lemma lem5255490 : term240 = term241.
Proof. exact (@lem69 term242). Qed.
Lemma lem5255491 (x : real) (s : real -> Prop) (h1 : term280) (h2 : @FINITE real s) (h3 : term235 s x) (h4 : term39 s) (h5 : term166 x s) : term241.
Proof. exact (EQ_MP (@lem5255490) (@lem5255489 x s h1 h2 h3 h4 h5)). Qed.
Lemma lem5255492 (x : real) (s : real -> Prop) (h1 : term280) (h2 : @FINITE real s) (h3 : term235 s x) (h4 : term39 s) (h5 : term166 x s) : term245.
Proof. exact (fun h0 : term273 => @lem5255491 x s h1 h2 h3 h4 h5). Qed.
Lemma lem5255493 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term235 s x) (h3 : term39 s) (h4 : term166 x s) : term248.
Proof. exact (fun h0 : term280 => @lem5255492 x s h0 h1 h2 h3 h4). Qed.
Lemma lem5255494 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term166 x s) : term251 s x.
Proof. exact (fun h0 : term235 s x => @lem5255493 x s h1 h0 h2 h3). Qed.
Lemma lem5255495 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term253 s x.
Proof. exact (fun h0 : term166 x s => @lem5255494 x s h1 h2 h0). Qed.
Lemma lem5255496 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term255 s x.
Proof. exact (fun h0 : term39 s => @lem5255495 x s h1 h0). Qed.
Lemma lem5255497 (s : real -> Prop) (x : real) : term257 s x.
Proof. exact (fun h0 : @FINITE real s => @lem5255496 x s h0). Qed.
Lemma lem5255502 (x : real) : term261 x.
Proof. exact (fun s : real -> Prop => @lem5255497 s x). Qed.
Lemma lem5255507 : term265.
Proof. exact (fun x : real => @lem5255502 x). Qed.
Lemma lem5255508 : term264.
Proof. exact (EQ_MP (@lem5254304) (@lem5255507)). Qed.
Lemma lem5255509 (x : real) : term432 x.
Proof. exact (@lem5255508 x). Qed.
Lemma lem5255510 (x : real) : (term432 x) = (term260 x).
Proof. exact (eq_refl (term432 x)). Qed.
Lemma lem5255511 (x : real) : term260 x.
Proof. exact (EQ_MP (@lem5255510 x) (@lem5255509 x)). Qed.
Lemma lem5255512 (x : real) (s : real -> Prop) : term433 x s.
Proof. exact (@lem5255511 x s). Qed.
Lemma lem5255513 (s : real -> Prop) (x : real) : (term433 x s) = (term236 s x).
Proof. exact (eq_refl (term433 x s)). Qed.
Lemma lem5255514 (s : real -> Prop) (x : real) : term236 s x.
Proof. exact (EQ_MP (@lem5255513 s x) (@lem5255512 x s)). Qed.
Lemma lem5255516 (s : real -> Prop) (x : real) : term236 s x.
Proof. exact (@lem5253960 s x (@lem5255514 s x)). Qed.
Lemma lem5255517 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term254 s x.
Proof. exact (@lem5255516 s x (@lem5252897 s h1)). Qed.
Lemma lem5255518 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term252 s x.
Proof. exact (@lem5255517 x s h1 (@lem5252933 s h2)). Qed.
Lemma lem5255519 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term166 x s) : term250 s x.
Proof. exact (@lem5255518 x s h1 h2 (@lem5253420 x s h3)). Qed.
Lemma lem5255520 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term235 s x) (h3 : term39 s) (h4 : term166 x s) : term247.
Proof. exact (@lem5255519 x s h1 h3 h4 (@lem5253945 s x h2)). Qed.
Lemma lem5255521 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term235 s x) (h3 : term39 s) (h4 : term166 x s) : term244.
Proof. exact (@lem5255520 x s h1 h2 h3 h4 (@lem1339577)). Qed.
Lemma lem5255522 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term235 s x) (h3 : term39 s) (h4 : term166 x s) : term240.
Proof. exact (@lem5255521 x s h1 h2 h3 h4 (@lem1339697)). Qed.
Lemma lem5255523 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term235 s x) (h3 : term39 s) (h4 : term166 x s) : False.
Proof. exact (@lem5255522 x s h1 h2 h3 h4 (@lem5222545)). Qed.
Lemma lem5255524 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term235 s x) (h3 : term39 s) (h4 : term166 x s) : (term235 s x) = False.
Proof. exact (prop_ext (fun h5 : term235 s x => @lem5255523 x s h1 h2 h3 h4) (fun h5 : False => @lem5253945 s x h2)). Qed.
Lemma lem5255525 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term235 s x) (h3 : term39 s) (h4 : term166 x s) : False.
Proof. exact (EQ_MP (@lem5255524 x s h1 h2 h3 h4) (@lem5253945 s x h2)). Qed.
Lemma lem5255526 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term166 x s) : term234 s x.
Proof. exact (fun h0 : term235 s x => @lem5255525 x s h1 h0 h2 h3). Qed.
Lemma lem5255527 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term166 x s) : term96 s x.
Proof. exact (EQ_MP (@lem5253944 s x) (@lem5255526 x s h1 h2 h3)). Qed.
Lemma lem5255529 (p : Prop) : p = (term233 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5255530 (s : real -> Prop) (x : real) : (term202 s x) = (term434 s x).
Proof. exact (@lem5255529 (term202 s x)). Qed.
Lemma lem5255531 (s : real -> Prop) (x : real) : (term434 s x) = (term202 s x).
Proof. exact (SYM (@lem5255530 s x)). Qed.
Lemma lem5255532 (s : real -> Prop) (x : real) (h1 : term411 s x) : term411 s x.
Proof. exact (h1). Qed.
Lemma lem5255535 (s : real -> Prop) (x : real) (h1 : term435 s x) : term435 s x.
Proof. exact (h1). Qed.
Lemma lem5255536 (s : real -> Prop) (x : real) : term436 s x.
Proof. exact (fun h0 : term435 s x => @lem5255535 s x h0). Qed.
Lemma lem5255537 (s : real -> Prop) (x : real) (h1 : term436 s x) : term436 s x.
Proof. exact (h1). Qed.
Lemma lem5255538 (s : real -> Prop) (x : real) (h1 : term435 s x) : term435 s x.
Proof. exact (h1). Qed.
Lemma lem5255539 (s : real -> Prop) (x : real) (h1 : term435 s x) (h2 : term436 s x) : term435 s x.
Proof. exact (@lem5255537 s x h2 (@lem5255538 s x h1)). Qed.
Lemma lem5255540 (s : real -> Prop) (x : real) (h1 : term435 s x) : term437 s x.
Proof. exact (fun h0 : term436 s x => @lem5255539 s x h1 h0). Qed.
Lemma lem5255541 (s : real -> Prop) (x : real) (h1 : term436 s x) : term436 s x.
Proof. exact (h1). Qed.
Lemma lem5255542 (s : real -> Prop) (x : real) (h1 : term435 s x) (h2 : term436 s x) : term435 s x.
Proof. exact (@lem5255540 s x h1 (@lem5255541 s x h2)). Qed.
Lemma lem5255543 (s : real -> Prop) (x : real) (h1 : term436 s x) : term436 s x.
Proof. exact (fun h0 : term435 s x => @lem5255542 s x h0 h1). Qed.
Lemma lem5255544 (s : real -> Prop) (x : real) : term438 s x.
Proof. exact (fun h0 : term436 s x => @lem5255543 s x h0). Qed.
Lemma lem5255547 (s : real -> Prop) (x : real) : term436 s x.
Proof. exact (@lem5255544 s x (@lem5255536 s x)). Qed.
Lemma lem5255639 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5255640 : term240 = term241.
Proof. exact (@lem5255639 term242). Qed.
Lemma lem5255657 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem5255658 : term244 = term245.
Proof. exact (MK_COMB (@lem5255657) (@lem5255640)). Qed.
Lemma lem5255661 : term246 = term246.
Proof. exact (eq_refl term246). Qed.
Lemma lem5255662 : term247 = term248.
Proof. exact (MK_COMB (@lem5255661) (@lem5255658)). Qed.
Lemma lem5255665 (s : real -> Prop) (x : real) : (term439 s x) = (term439 s x).
Proof. exact (eq_refl (term439 s x)). Qed.
Lemma lem5255666 (s : real -> Prop) (x : real) : (term440 s x) = (term441 s x).
Proof. exact (MK_COMB (@lem5255665 s x) (@lem5255662)). Qed.
Lemma lem5255669 (x : real) (s : real -> Prop) : (term169 x s) = (term169 x s).
Proof. exact (eq_refl (term169 x s)). Qed.
Lemma lem5255670 (s : real -> Prop) (x : real) : (term442 s x) = (term443 s x).
Proof. exact (MK_COMB (@lem5255669 x s) (@lem5255666 s x)). Qed.
Lemma lem5255673 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5255674 (s : real -> Prop) (x : real) : (term444 s x) = (term445 s x).
Proof. exact (MK_COMB (@lem5255673 s) (@lem5255670 s x)). Qed.
Lemma lem5255677 (s : real -> Prop) : (term256 s) = (term256 s).
Proof. exact (eq_refl (term256 s)). Qed.
Lemma lem5255678 (s : real -> Prop) (x : real) : (term435 s x) = (term446 s x).
Proof. exact (MK_COMB (@lem5255677 s) (@lem5255674 s x)). Qed.
Lemma lem5255681 (x : real) : (term447 x) = (term448 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5255678 s x)). Qed.
Lemma lem5255682 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5255683 (x : real) : (term449 x) = (term450 x).
Proof. exact (MK_COMB (@lem5255682) (@lem5255681 x)). Qed.
Lemma lem5255688 : term451 = term452.
Proof. exact (fun_ext (fun x : real => @lem5255683 x)). Qed.
Lemma lem5255689 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5255698 : term453 = term454.
Proof. exact (MK_COMB (@lem5255689) (@lem5255688)). Qed.
Lemma lem5255703 (s : real -> Prop) (x : real) : (term201 s x) = (term201 s x).
Proof. exact (eq_refl (term201 s x)). Qed.
Lemma lem5255704 (s : real -> Prop) : (term228 s) = (term228 s).
Proof. exact (fun_ext (fun x : real => @lem5255703 s x)). Qed.
Lemma lem5255705 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5255706 (s : real -> Prop) : (term199 s) = (term199 s).
Proof. exact (MK_COMB (@lem5255705) (@lem5255704 s)). Qed.
Lemma lem5255709 (s : real -> Prop) : (term266 s) = (term266 s).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5255710 (s : real -> Prop) : (term198 s) = (term198 s).
Proof. exact (MK_COMB (@lem5255709 s) (@lem5255706 s)). Qed.
Lemma lem5255719 (s : real -> Prop) : (term267 s) = (term267 s).
Proof. exact (eq_refl (term267 s)). Qed.
Lemma lem5255720 (s : real -> Prop) : (term197 s) = (term197 s).
Proof. exact (MK_COMB (@lem5255719 s) (@lem5255710 s)). Qed.
Lemma lem5255721 : term268 = term268.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5255720 s)). Qed.
Lemma lem5255722 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5255723 : term242 = term242.
Proof. exact (MK_COMB (@lem5255722) (@lem5255721)). Qed.
Lemma lem5255724 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5255725 : term241 = term241.
Proof. exact (MK_COMB (@lem5255724) (@lem5255723)). Qed.
Lemma lem5255730 (y : real) (x : real) : (term269 y x) = (term269 y x).
Proof. exact (eq_refl (term269 y x)). Qed.
Lemma lem5255731 (x : real) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem5255730 y x)). Qed.
Lemma lem5255732 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5255733 (x : real) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem5255732) (@lem5255731 x)). Qed.
Lemma lem5255734 : term272 = term272.
Proof. exact (fun_ext (fun x : real => @lem5255733 x)). Qed.
Lemma lem5255735 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5255736 : term273 = term273.
Proof. exact (MK_COMB (@lem5255735) (@lem5255734)). Qed.
Lemma lem5255737 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5255738 : term243 = term243.
Proof. exact (MK_COMB (@lem5255737) (@lem5255736)). Qed.
Lemma lem5255739 : term245 = term245.
Proof. exact (MK_COMB (@lem5255738) (@lem5255725)). Qed.
Lemma lem5255748 (y : real) (x : real) (z : real) : (term274 y x z) = (term274 y x z).
Proof. exact (eq_refl (term274 y x z)). Qed.
Lemma lem5255749 (y : real) (x : real) : (term275 y x) = (term275 y x).
Proof. exact (fun_ext (fun z : real => @lem5255748 y x z)). Qed.
Lemma lem5255750 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5255751 (y : real) (x : real) : (term276 y x) = (term276 y x).
Proof. exact (MK_COMB (@lem5255750) (@lem5255749 y x)). Qed.
Lemma lem5255752 (x : real) : (term277 x) = (term277 x).
Proof. exact (fun_ext (fun y : real => @lem5255751 y x)). Qed.
Lemma lem5255753 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5255754 (x : real) : (term278 x) = (term278 x).
Proof. exact (MK_COMB (@lem5255753) (@lem5255752 x)). Qed.
Lemma lem5255755 : term279 = term279.
Proof. exact (fun_ext (fun x : real => @lem5255754 x)). Qed.
Lemma lem5255756 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5255757 : term280 = term280.
Proof. exact (MK_COMB (@lem5255756) (@lem5255755)). Qed.
Lemma lem5255758 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5255759 : term246 = term246.
Proof. exact (MK_COMB (@lem5255758) (@lem5255757)). Qed.
Lemma lem5255760 : term248 = term248.
Proof. exact (MK_COMB (@lem5255759) (@lem5255739)). Qed.
Lemma lem5255765 (s : real -> Prop) (x : real) : (term439 s x) = (term439 s x).
Proof. exact (eq_refl (term439 s x)). Qed.
Lemma lem5255766 (s : real -> Prop) (x : real) : (term441 s x) = (term441 s x).
Proof. exact (MK_COMB (@lem5255765 s x) (@lem5255760)). Qed.
Lemma lem5255771 (x : real) (s : real -> Prop) : (term169 x s) = (term169 x s).
Proof. exact (eq_refl (term169 x s)). Qed.
Lemma lem5255772 (s : real -> Prop) (x : real) : (term443 s x) = (term443 s x).
Proof. exact (MK_COMB (@lem5255771 x s) (@lem5255766 s x)). Qed.
Lemma lem5255777 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5255778 (s : real -> Prop) (x : real) : (term445 s x) = (term445 s x).
Proof. exact (MK_COMB (@lem5255777 s) (@lem5255772 s x)). Qed.
Lemma lem5255781 (s : real -> Prop) : (term256 s) = (term256 s).
Proof. exact (eq_refl (term256 s)). Qed.
Lemma lem5255782 (s : real -> Prop) (x : real) : (term446 s x) = (term446 s x).
Proof. exact (MK_COMB (@lem5255781 s) (@lem5255778 s x)). Qed.
Lemma lem5255783 (x : real) : (term448 x) = (term448 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5255782 s x)). Qed.
Lemma lem5255784 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5255785 (x : real) : (term450 x) = (term450 x).
Proof. exact (MK_COMB (@lem5255784) (@lem5255783 x)). Qed.
Lemma lem5255786 : term452 = term452.
Proof. exact (fun_ext (fun x : real => @lem5255785 x)). Qed.
Lemma lem5255787 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5255788 : term454 = term454.
Proof. exact (MK_COMB (@lem5255787) (@lem5255786)). Qed.
Lemma lem5255871 : term453 = term454.
Proof. exact (TRANS (@lem5255698) (@lem5255788)). Qed.
Lemma lem5255872 : term454 = term453.
Proof. exact (SYM (@lem5255871)). Qed.
Lemma lem5255878 (h1 : term273) : term273.
Proof. exact (h1). Qed.
Lemma lem5255897 (x : real) (s : real -> Prop) (h1 : term182 x s) : term182 x s.
Proof. exact (h1). Qed.
Lemma lem5255903 (s : real -> Prop) (x : real) (h1 : term411 s x) : term411 s x.
Proof. exact (h1). Qed.
Lemma lem5255991 (y : real) (x : real) : (term269 y x) = (term269 y x).
Proof. exact (eq_refl (term269 y x)). Qed.
Lemma lem5255992 (x : real) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem5255991 y x)). Qed.
Lemma lem5255993 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5255994 (x : real) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem5255993) (@lem5255992 x)). Qed.
Lemma lem5255995 : term272 = term272.
Proof. exact (fun_ext (fun x : real => @lem5255994 x)). Qed.
Lemma lem5255996 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5256053 : term273 = term273.
Proof. exact (MK_COMB (@lem5255996) (@lem5255995)). Qed.
Lemma lem5256054 (h1 : term273) : term273.
Proof. exact (EQ_MP (@lem5256053) (@lem5255878 h1)). Qed.
Lemma lem5256208 (x : real) (s : real -> Prop) (h1 : term182 x s) : term182 x s.
Proof. exact (h1). Qed.
Lemma lem5256218 (s : real -> Prop) (x : real) (h1 : term411 s x) : term411 s x.
Proof. exact (h1). Qed.
Lemma lem5256266 (y : real) (x : real) : (term269 y x) = (term269 y x).
Proof. exact (eq_refl (term269 y x)). Qed.
Lemma lem5256267 (x : real) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem5256266 y x)). Qed.
Lemma lem5256268 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5256269 (x : real) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem5256268) (@lem5256267 x)). Qed.
Lemma lem5256270 : term272 = term272.
Proof. exact (fun_ext (fun x : real => @lem5256269 x)). Qed.
Lemma lem5256271 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5256272 : term273 = term273.
Proof. exact (MK_COMB (@lem5256271) (@lem5256270)). Qed.
Lemma lem5256273 (h1 : term273) : term273.
Proof. exact (EQ_MP (@lem5256272) (@lem5256054 h1)). Qed.
Lemma lem5256335 (x : real) (s : real -> Prop) (h1 : term182 x s) : term182 x s.
Proof. exact (h1). Qed.
Lemma lem5256339 (s : real -> Prop) (x : real) (h1 : term411 s x) : term411 s x.
Proof. exact (h1). Qed.
Lemma lem5256372 (y : real) (x : real) : (term269 y x) = (term269 y x).
Proof. exact (eq_refl (term269 y x)). Qed.
Lemma lem5256373 (x : real) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem5256372 y x)). Qed.
Lemma lem5256374 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5256375 (x : real) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem5256374) (@lem5256373 x)). Qed.
Lemma lem5256376 : term272 = term272.
Proof. exact (fun_ext (fun x : real => @lem5256375 x)). Qed.
Lemma lem5256377 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5256379 : term273 = term273.
Proof. exact (MK_COMB (@lem5256377) (@lem5256376)). Qed.
Lemma lem5256380 (h1 : term273) : term273.
Proof. exact (EQ_MP (@lem5256379) (@lem5256273 h1)). Qed.
Lemma lem5256473 (_68838 : real) (h1 : term273) : term455 _68838.
Proof. exact (@lem5256380 h1 _68838). Qed.
Lemma lem5256474 (_68838 : real) : (term455 _68838) = (term271 _68838).
Proof. exact (eq_refl (term455 _68838)). Qed.
Lemma lem5256475 (_68838 : real) (h1 : term273) : term271 _68838.
Proof. exact (EQ_MP (@lem5256474 _68838) (@lem5256473 _68838 h1)). Qed.
Lemma lem5256476 (_68838 : real) (_68839 : real) (h1 : term273) : term456 _68838 _68839.
Proof. exact (@lem5256475 _68838 h1 _68839). Qed.
Lemma lem5256477 (_68839 : real) (_68838 : real) : (term456 _68838 _68839) = (term269 _68839 _68838).
Proof. exact (eq_refl (term456 _68838 _68839)). Qed.
Lemma lem5256492 (x : real) (s : real -> Prop) (h1 : term182 x s) : term182 x s.
Proof. exact (h1). Qed.
Lemma lem5256494 (s : real -> Prop) (x : real) (h1 : term411 s x) : term411 s x.
Proof. exact (h1). Qed.
Lemma lem5256512 (_68839 : real) (_68838 : real) (h1 : term273) : term269 _68839 _68838.
Proof. exact (EQ_MP (@lem5256477 _68839 _68838) (@lem5256476 _68838 _68839 h1)). Qed.
Lemma lem5256604 (x : real) (s : real -> Prop) (h1 : term182 x s) : term182 x s.
Proof. exact (h1). Qed.
Lemma lem5256605 (x : real) (s : real -> Prop) (h1 : term182 x s) : term457 x s.
Proof. exact (fun h0 : term166 x s => @lem5256604 x s h1). Qed.
Lemma lem5256607 (p : Prop) : (term373 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5256608 (x : real) (s : real -> Prop) : (term457 x s) = (term182 x s).
Proof. exact (@lem5256607 (term166 x s)). Qed.
Lemma lem5256609 (x : real) (s : real -> Prop) (h1 : term182 x s) : term182 x s.
Proof. exact (EQ_MP (@lem5256608 x s) (@lem5256605 x s h1)). Qed.
Lemma lem5256620 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5256621 (_68839 : real) (_68838 : real) : (term269 _68838 _68839) = (term269 _68839 _68838).
Proof. exact (@lem5256620 (real_le _68838 _68839) (real_le _68839 _68838)). Qed.
Lemma lem5256627 (_68839 : real) (_68838 : real) : (term458 _68839 _68838) = (term458 _68839 _68838).
Proof. exact (eq_refl (term458 _68839 _68838)). Qed.
Lemma lem5256628 (_68839 : real) (_68838 : real) : ((term269 _68839 _68838) = (term269 _68838 _68839)) = ((term269 _68839 _68838) = (term269 _68839 _68838)).
Proof. exact (MK_COMB (@lem5256627 _68839 _68838) (@lem5256621 _68839 _68838)). Qed.
Lemma lem5256630 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5256631 (x : Prop) : (x = x) = True.
Proof. exact (@lem5256630 Prop x). Qed.
Lemma lem5256632 (_68839 : real) (_68838 : real) : ((term269 _68839 _68838) = (term269 _68839 _68838)) = True.
Proof. exact (@lem5256631 (term269 _68839 _68838)). Qed.
Lemma lem5256633 (_68838 : real) (_68839 : real) : ((term269 _68839 _68838) = (term269 _68838 _68839)) = True.
Proof. exact (TRANS (@lem5256628 _68839 _68838) (@lem5256632 _68839 _68838)). Qed.
Lemma lem5256634 (_68838 : real) (_68839 : real) : True = ((term269 _68839 _68838) = (term269 _68838 _68839)).
Proof. exact (SYM (@lem5256633 _68838 _68839)). Qed.
Lemma lem5256635 (_68838 : real) (_68839 : real) : (term269 _68839 _68838) = (term269 _68838 _68839).
Proof. exact (EQ_MP (@lem5256634 _68838 _68839) (@lem0)). Qed.
Lemma lem5256636 (_68838 : real) (_68839 : real) (h1 : term273) : term269 _68838 _68839.
Proof. exact (EQ_MP (@lem5256635 _68838 _68839) (@lem5256512 _68839 _68838 h1)). Qed.
Lemma lem5256638 (b : Prop) (a : Prop) : (a \/ b) = (term391 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5256641 (_68839 : real) (_68838 : real) : (term269 _68838 _68839) = (term459 _68839 _68838).
Proof. exact (@lem5256638 (real_le _68838 _68839) (real_le _68839 _68838)). Qed.
Lemma lem5256644 (_68839 : real) (_68838 : real) (h1 : term273) : term459 _68839 _68838.
Proof. exact (EQ_MP (@lem5256641 _68839 _68838) (@lem5256636 _68838 _68839 h1)). Qed.
Lemma lem5256645 (s : real -> Prop) (x : real) (h1 : term273) : term460 s x.
Proof. exact (@lem5256644 (inf s) x h1). Qed.
Lemma lem5256648 (x : real) (s : real -> Prop) (h1 : term273) (h2 : term182 x s) : term202 s x.
Proof. exact (@lem5256645 s x h1 (@lem5256609 x s h2)). Qed.
Lemma lem5256649 (x : real) (s : real -> Prop) (h1 : term273) (h2 : term182 x s) : term410 s x.
Proof. exact (fun h0 : term411 s x => @lem5256648 x s h1 h2). Qed.
Lemma lem5256651 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5256652 (s : real -> Prop) (x : real) : (term410 s x) = (term202 s x).
Proof. exact (@lem5256651 (term202 s x)). Qed.
Lemma lem5256653 (x : real) (s : real -> Prop) (h1 : term273) (h2 : term182 x s) : term202 s x.
Proof. exact (EQ_MP (@lem5256652 s x) (@lem5256649 x s h1 h2)). Qed.
Lemma lem5256656 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5256658 (s : real -> Prop) (x : real) : (term411 s x) = (term461 s x).
Proof. exact (@lem5256656 (term202 s x)). Qed.
Lemma lem5256661 (s : real -> Prop) (x : real) (h1 : term411 s x) : term461 s x.
Proof. exact (EQ_MP (@lem5256658 s x) (@lem5256494 s x h1)). Qed.
Lemma lem5256664 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (@lem5256661 s x h3 (@lem5256653 x s h1 h2)). Qed.
Lemma lem5256665 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : term431.
Proof. exact (fun h0 : ~ False => @lem5256664 s x h1 h2 h3). Qed.
Lemma lem5256667 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5256668 : term431 = False.
Proof. exact (@lem5256667 False). Qed.
Lemma lem5256669 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256668) (@lem5256665 s x h1 h2 h3)). Qed.
Lemma lem5256670 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : (term411 s x) = False.
Proof. exact (prop_ext (fun h4 : term411 s x => @lem5256669 s x h1 h2 h3) (fun h4 : False => @lem5256494 s x h3)). Qed.
Lemma lem5256671 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256670 s x h1 h2 h3) (@lem5256494 s x h3)). Qed.
Lemma lem5256672 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : (term182 x s) = False.
Proof. exact (prop_ext (fun h4 : term182 x s => @lem5256671 s x h1 h2 h3) (fun h4 : False => @lem5256492 x s h2)). Qed.
Lemma lem5256673 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256672 s x h1 h2 h3) (@lem5256492 x s h2)). Qed.
Lemma lem5256674 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : (term411 s x) = False.
Proof. exact (prop_ext (fun h4 : term411 s x => @lem5256673 s x h1 h2 h3) (fun h4 : False => @lem5256339 s x h3)). Qed.
Lemma lem5256675 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256674 s x h1 h2 h3) (@lem5256339 s x h3)). Qed.
Lemma lem5256676 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : (term182 x s) = False.
Proof. exact (prop_ext (fun h4 : term182 x s => @lem5256675 s x h1 h2 h3) (fun h4 : False => @lem5256335 x s h2)). Qed.
Lemma lem5256677 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256676 s x h1 h2 h3) (@lem5256335 x s h2)). Qed.
Lemma lem5256678 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : term273 = False.
Proof. exact (prop_ext (fun h4 : term273 => @lem5256677 s x h1 h2 h3) (fun h4 : False => @lem5256380 h1)). Qed.
Lemma lem5256679 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256678 s x h1 h2 h3) (@lem5256380 h1)). Qed.
Lemma lem5256680 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : (term411 s x) = False.
Proof. exact (prop_ext (fun h4 : term411 s x => @lem5256679 s x h1 h2 h3) (fun h4 : False => @lem5256339 s x h3)). Qed.
Lemma lem5256681 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256680 s x h1 h2 h3) (@lem5256339 s x h3)). Qed.
Lemma lem5256682 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : (term182 x s) = False.
Proof. exact (prop_ext (fun h4 : term182 x s => @lem5256681 s x h1 h2 h3) (fun h4 : False => @lem5256335 x s h2)). Qed.
Lemma lem5256683 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256682 s x h1 h2 h3) (@lem5256335 x s h2)). Qed.
Lemma lem5256684 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : term273 = False.
Proof. exact (prop_ext (fun h4 : term273 => @lem5256683 s x h1 h2 h3) (fun h4 : False => @lem5256273 h1)). Qed.
Lemma lem5256685 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256684 s x h1 h2 h3) (@lem5256273 h1)). Qed.
Lemma lem5256686 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : (term411 s x) = False.
Proof. exact (prop_ext (fun h4 : term411 s x => @lem5256685 s x h1 h2 h3) (fun h4 : False => @lem5256218 s x h3)). Qed.
Lemma lem5256687 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256686 s x h1 h2 h3) (@lem5256218 s x h3)). Qed.
Lemma lem5256688 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : (term182 x s) = False.
Proof. exact (prop_ext (fun h4 : term182 x s => @lem5256687 s x h1 h2 h3) (fun h4 : False => @lem5256208 x s h2)). Qed.
Lemma lem5256689 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256688 s x h1 h2 h3) (@lem5256208 x s h2)). Qed.
Lemma lem5256690 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : term273 = False.
Proof. exact (prop_ext (fun h4 : term273 => @lem5256689 s x h1 h2 h3) (fun h4 : False => @lem5256054 h1)). Qed.
Lemma lem5256691 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256690 s x h1 h2 h3) (@lem5256054 h1)). Qed.
Lemma lem5256692 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : (term411 s x) = False.
Proof. exact (prop_ext (fun h4 : term411 s x => @lem5256691 s x h1 h2 h3) (fun h4 : False => @lem5255903 s x h3)). Qed.
Lemma lem5256693 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256692 s x h1 h2 h3) (@lem5255903 s x h3)). Qed.
Lemma lem5256694 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : (term182 x s) = False.
Proof. exact (prop_ext (fun h4 : term182 x s => @lem5256693 s x h1 h2 h3) (fun h4 : False => @lem5255897 x s h2)). Qed.
Lemma lem5256695 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256694 s x h1 h2 h3) (@lem5255897 x s h2)). Qed.
Lemma lem5256696 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : term240.
Proof. exact (fun h0 : term242 => @lem5256695 s x h1 h2 h3). Qed.
Lemma lem5256697 : term240 = term241.
Proof. exact (@lem69 term242). Qed.
Lemma lem5256698 (s : real -> Prop) (x : real) (h1 : term273) (h2 : term182 x s) (h3 : term411 s x) : term241.
Proof. exact (EQ_MP (@lem5256697) (@lem5256696 s x h1 h2 h3)). Qed.
Lemma lem5256699 (s : real -> Prop) (x : real) (h1 : term182 x s) (h2 : term411 s x) : term245.
Proof. exact (fun h0 : term273 => @lem5256698 s x h0 h1 h2). Qed.
Lemma lem5256700 (s : real -> Prop) (x : real) (h1 : term182 x s) (h2 : term411 s x) : term248.
Proof. exact (fun h0 : term280 => @lem5256699 s x h1 h2). Qed.
Lemma lem5256701 (x : real) (s : real -> Prop) (h1 : term182 x s) : term441 s x.
Proof. exact (fun h0 : term411 s x => @lem5256700 s x h1 h0). Qed.
Lemma lem5256702 (s : real -> Prop) (x : real) : term443 s x.
Proof. exact (fun h0 : term182 x s => @lem5256701 x s h0). Qed.
Lemma lem5256703 (s : real -> Prop) (x : real) : term445 s x.
Proof. exact (fun h0 : term39 s => @lem5256702 s x). Qed.
Lemma lem5256704 (s : real -> Prop) (x : real) : term446 s x.
Proof. exact (fun h0 : @FINITE real s => @lem5256703 s x). Qed.
Lemma lem5256709 (x : real) : term450 x.
Proof. exact (fun s : real -> Prop => @lem5256704 s x). Qed.
Lemma lem5256714 : term454.
Proof. exact (fun x : real => @lem5256709 x). Qed.
Lemma lem5256715 : term453.
Proof. exact (EQ_MP (@lem5255872) (@lem5256714)). Qed.
Lemma lem5256716 (x : real) : term462 x.
Proof. exact (@lem5256715 x). Qed.
Lemma lem5256717 (x : real) : (term462 x) = (term449 x).
Proof. exact (eq_refl (term462 x)). Qed.
Lemma lem5256718 (x : real) : term449 x.
Proof. exact (EQ_MP (@lem5256717 x) (@lem5256716 x)). Qed.
Lemma lem5256719 (x : real) (s : real -> Prop) : term463 x s.
Proof. exact (@lem5256718 x s). Qed.
Lemma lem5256720 (s : real -> Prop) (x : real) : (term463 x s) = (term435 s x).
Proof. exact (eq_refl (term463 x s)). Qed.
Lemma lem5256721 (s : real -> Prop) (x : real) : term435 s x.
Proof. exact (EQ_MP (@lem5256720 s x) (@lem5256719 x s)). Qed.
Lemma lem5256723 (s : real -> Prop) (x : real) : term435 s x.
Proof. exact (@lem5255547 s x (@lem5256721 s x)). Qed.
Lemma lem5256724 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term444 s x.
Proof. exact (@lem5256723 s x (@lem5252897 s h1)). Qed.
Lemma lem5256725 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term442 s x.
Proof. exact (@lem5256724 x s h1 (@lem5252933 s h2)). Qed.
Lemma lem5256726 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term182 x s) : term440 s x.
Proof. exact (@lem5256725 x s h1 h2 (@lem5253437 x s h3)). Qed.
Lemma lem5256727 (s : real -> Prop) (x : real) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term182 x s) (h4 : term411 s x) : term247.
Proof. exact (@lem5256726 x s h1 h2 h3 (@lem5255532 s x h4)). Qed.
Lemma lem5256728 (s : real -> Prop) (x : real) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term182 x s) (h4 : term411 s x) : term244.
Proof. exact (@lem5256727 s x h1 h2 h3 h4 (@lem1339577)). Qed.
Lemma lem5256729 (s : real -> Prop) (x : real) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term182 x s) (h4 : term411 s x) : term240.
Proof. exact (@lem5256728 s x h1 h2 h3 h4 (@lem1339697)). Qed.
Lemma lem5256730 (s : real -> Prop) (x : real) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term182 x s) (h4 : term411 s x) : False.
Proof. exact (@lem5256729 s x h1 h2 h3 h4 (@lem5222545)). Qed.
Lemma lem5256731 (s : real -> Prop) (x : real) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term182 x s) (h4 : term411 s x) : (term411 s x) = False.
Proof. exact (prop_ext (fun h5 : term411 s x => @lem5256730 s x h1 h2 h3 h4) (fun h5 : False => @lem5255532 s x h4)). Qed.
Lemma lem5256732 (s : real -> Prop) (x : real) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term182 x s) (h4 : term411 s x) : False.
Proof. exact (EQ_MP (@lem5256731 s x h1 h2 h3 h4) (@lem5255532 s x h4)). Qed.
Lemma lem5256733 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term182 x s) : term434 s x.
Proof. exact (fun h0 : term411 s x => @lem5256732 s x h1 h2 h3 h0). Qed.
Lemma lem5256734 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term182 x s) : term202 s x.
Proof. exact (EQ_MP (@lem5255531 s x) (@lem5256733 x s h1 h2 h3)). Qed.
Lemma lem5256737 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term182 x s) : term168 x s.
Proof. exact (EQ_MP (@lem5253940 x s h1 h2) (@lem5256734 x s h1 h2 h3)). Qed.
Lemma lem5256738 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term182 x s) : (term182 x s) = (term168 x s).
Proof. exact (prop_ext (fun h4 : term182 x s => @lem5256737 x s h1 h2 h3) (fun h4 : term168 x s => @lem5253437 x s h3)). Qed.
Lemma lem5256739 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term182 x s) : term168 x s.
Proof. exact (EQ_MP (@lem5256738 x s h1 h2 h3) (@lem5253437 x s h3)). Qed.
Lemma lem5256740 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term171 x s.
Proof. exact (fun h0 : term182 x s => @lem5256739 x s h1 h2 h0). Qed.
Lemma lem5256741 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term166 x s) : term173 s x.
Proof. exact (EQ_MP (@lem5253648 s x) (@lem5255527 x s h1 h2 h3)). Qed.
Lemma lem5256742 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term166 x s) : (term166 x s) = (term173 s x).
Proof. exact (prop_ext (fun h4 : term166 x s => @lem5256741 x s h1 h2 h3) (fun h4 : term173 s x => @lem5253420 x s h3)). Qed.
Lemma lem5256743 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term166 x s) : term173 s x.
Proof. exact (EQ_MP (@lem5256742 x s h1 h2 h3) (@lem5253420 x s h3)). Qed.
Lemma lem5256744 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term176 s x.
Proof. exact (fun h0 : term166 x s => @lem5256743 x s h1 h2 h0). Qed.
Lemma lem5256745 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term179 x s.
Proof. exact (conj (@lem5256744 x s h1 h2) (@lem5256740 x s h1 h2)). Qed.
Lemma lem5256746 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term160 x s.
Proof. exact (EQ_MP (@lem5253419 x s) (@lem5256745 x s h1 h2)). Qed.
Lemma lem5256748 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term143 x s.
Proof. exact (EQ_MP (@lem5253401 x s) (@lem5256746 x s h1 h2)). Qed.
Lemma lem5256751 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term25 x s) = (term23 x s).
Proof. exact (EQ_MP (@lem5253311 x s h1) (@lem5256748 x s h1 h2)). Qed.
Lemma lem5256752 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term39 s) = ((term25 x s) = (term23 x s)).
Proof. exact (prop_ext (fun h3 : term39 s => @lem5256751 x s h1 h2) (fun h3 : (term25 x s) = (term23 x s) => @lem5252933 s h2)). Qed.
Lemma lem5256753 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term25 x s) = (term23 x s).
Proof. exact (EQ_MP (@lem5256752 x s h1 h2) (@lem5252933 s h2)). Qed.
Lemma lem5256754 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term28 x s.
Proof. exact (fun h0 : term39 s => @lem5256753 x s h1 h0). Qed.
Lemma lem5256755 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : s = (@EMPTY real)) : (term25 x s) = x.
Proof. exact (EQ_MP (@lem5253126 x s h1 h2) (@lem5253332 x)). Qed.
Lemma lem5256756 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : s = (@EMPTY real)) : (s = (@EMPTY real)) = ((term25 x s) = x).
Proof. exact (prop_ext (fun h3 : s = (@EMPTY real) => @lem5256755 x s h1 h2) (fun h3 : (term25 x s) = x => @lem5252916 s h2)). Qed.
Lemma lem5256757 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : s = (@EMPTY real)) : (term25 x s) = x.
Proof. exact (EQ_MP (@lem5256756 x s h1 h2) (@lem5252916 s h2)). Qed.
Lemma lem5256758 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term32 s x.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5256757 x s h1 h0). Qed.
Lemma lem5256759 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term35 x s.
Proof. exact (conj (@lem5256758 x s h1) (@lem5256754 x s h1)). Qed.
Lemma lem5256760 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term25 x s) = (term36 x s).
Proof. exact (EQ_MP (@lem5252915 x s) (@lem5256759 x s h1)). Qed.
Lemma lem5256761 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (@FINITE real s) = ((term25 x s) = (term36 x s)).
Proof. exact (prop_ext (fun h2 : @FINITE real s => @lem5256760 x s h1) (fun h2 : (term25 x s) = (term36 x s) => @lem5252897 s h1)). Qed.
Lemma lem5256762 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term25 x s) = (term36 x s).
Proof. exact (EQ_MP (@lem5256761 x s h1) (@lem5252897 s h1)). Qed.
Lemma lem5256763 (x : real) (s : real -> Prop) : term464 x s.
Proof. exact (fun h0 : @FINITE real s => @lem5256762 x s h0). Qed.
Lemma lem5256768 (x : real) : term465 x.
Proof. exact (fun s : real -> Prop => @lem5256763 x s). Qed.
Lemma lem5256773 : term466.
Proof. exact (fun x : real => @lem5256768 x). Qed.
