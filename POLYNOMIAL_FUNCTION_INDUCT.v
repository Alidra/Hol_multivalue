Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POLYNOMIAL_FUNCTION_INDUCT_term_abbrevs.
Require Import ADD1_spec.
Require Import EXISTS_REFL_spec.
Require Import FUN_EQ_THM_spec.
Require Import LEFT_FORALL_IMP_THM_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import LE_0_spec.
Require Import REAL_POW_1_spec.
Require Import REAL_POW_ADD_spec.
Require Import SUM_CLAUSES_LEFT_spec.
Require Import SUM_OFFSET_spec.
Require Import SUM_RMUL_spec.
Require Import SUM_SING_NUMSEG_spec.
Require Import polynomial_function_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338912_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem7581931 {A : Type'} (f : A -> real) : term0 A f.
Proof. exact (@lem7070368 A f). Qed.
Lemma lem7581932 {A : Type'} (f : A -> real) : (term0 A f) = (term1 A f).
Proof. exact (eq_refl (term0 A f)). Qed.
Lemma lem7581933 {A : Type'} (f : A -> real) : term1 A f.
Proof. exact (EQ_MP (@lem7581932 A f) (@lem7581931 A f)). Qed.
Lemma lem7581934 {A : Type'} (f : A -> real) (c : real) : term2 A f c.
Proof. exact (@lem7581933 A f c). Qed.
Lemma lem7581935 {A : Type'} (f : A -> real) (c : real) : (term2 A f c) = (term3 A f c).
Proof. exact (eq_refl (term2 A f c)). Qed.
Lemma lem7581936 {A : Type'} (f : A -> real) (c : real) : term3 A f c.
Proof. exact (EQ_MP (@lem7581935 A f c) (@lem7581934 A f c)). Qed.
Lemma lem7581937 {A : Type'} (f : A -> real) (c : real) (s : A -> Prop) : term4 A f c s.
Proof. exact (@lem7581936 A f c s). Qed.
Lemma lem7581938 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) : (term4 A f c s) = ((term5 A s f c) = (term6 A s f c)).
Proof. exact (eq_refl (term4 A f c s)). Qed.
Lemma lem7581940 (x : real) : term7 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem7581941 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem7581942 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem7581941 x) (@lem7581940 x)). Qed.
Lemma lem7581943 (x : real) (y : real) : term9 x y.
Proof. exact (@lem7581942 x y). Qed.
Lemma lem7581944 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem7581945 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem7581944 x y) (@lem7581943 x y)). Qed.
Lemma lem7581946 (x : real) (y : real) (z : real) : term11 x y z.
Proof. exact (@lem7581945 x y z). Qed.
Lemma lem7581947 (x : real) (y : real) (z : real) : (term11 x y z) = ((term12 x y z) = (term13 x y z)).
Proof. exact (eq_refl (term11 x y z)). Qed.
Lemma lem7581949 (x : real) : term14 x.
Proof. exact (@lem1631005 x). Qed.
Lemma lem7581950 (x : real) : (term14 x) = ((term15 x) = x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem7581952 (x : real) : term16 x.
Proof. exact (@lem1596102 x). Qed.
Lemma lem7581953 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem7581954 (x : real) : term17 x.
Proof. exact (EQ_MP (@lem7581953 x) (@lem7581952 x)). Qed.
Lemma lem7581955 (x : real) (m : nat) : term18 x m.
Proof. exact (@lem7581954 x m). Qed.
Lemma lem7581956 (m : nat) (x : real) : (term18 x m) = (term19 m x).
Proof. exact (eq_refl (term18 x m)). Qed.
Lemma lem7581957 (m : nat) (x : real) : term19 m x.
Proof. exact (EQ_MP (@lem7581956 m x) (@lem7581955 x m)). Qed.
Lemma lem7581958 (m : nat) (x : real) (n : nat) : term20 m x n.
Proof. exact (@lem7581957 m x n). Qed.
Lemma lem7581959 (m : nat) (x : real) (n : nat) : (term20 m x n) = ((term21 x m n) = (term22 m x n)).
Proof. exact (eq_refl (term20 m x n)). Qed.
Lemma lem7581961 : term23.
Proof. exact (@lem7223171 term24). Qed.
Lemma lem7581962 : term23 = term25.
Proof. exact (eq_refl term23). Qed.
Lemma lem7581963 : term25.
Proof. exact (EQ_MP (@lem7581962) (@lem7581961)). Qed.
Lemma lem7581964 (f : nat -> real) : term26 f.
Proof. exact (@lem7581963 f). Qed.
Lemma lem7581965 (f : nat -> real) : (term26 f) = (term27 f).
Proof. exact (eq_refl (term26 f)). Qed.
Lemma lem7581966 (f : nat -> real) : term27 f.
Proof. exact (EQ_MP (@lem7581965 f) (@lem7581964 f)). Qed.
Lemma lem7581967 (f : nat -> real) (m : nat) : term28 f m.
Proof. exact (@lem7581966 f m). Qed.
Lemma lem7581968 (m : nat) (f : nat -> real) : (term28 f m) = (term29 m f).
Proof. exact (eq_refl (term28 f m)). Qed.
Lemma lem7581969 (m : nat) (f : nat -> real) : term29 m f.
Proof. exact (EQ_MP (@lem7581968 m f) (@lem7581967 f m)). Qed.
Lemma lem7581970 (m : nat) (f : nat -> real) (n : nat) : term30 m f n.
Proof. exact (@lem7581969 m f n). Qed.
Lemma lem7581971 (m : nat) (n : nat) (f : nat -> real) : (term30 m f n) = ((term31 m n f) = (term32 m n f)).
Proof. exact (eq_refl (term30 m f n)). Qed.
Lemma lem7581973 (n : nat) : term33 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem7581974 (n : nat) : (term33 n) = (term34 n).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem7581975 (n : nat) : term34 n.
Proof. exact (EQ_MP (@lem7581974 n) (@lem7581973 n)). Qed.
Lemma lem7581976 (n : nat) : (term34 n) = ((term34 n) = True).
Proof. exact (@lem7 (term34 n)). Qed.
Lemma lem7581978 (m : nat) : term35 m.
Proof. exact (@lem80621 m). Qed.
Lemma lem7581979 (m : nat) : (term35 m) = ((S m) = (term36 m)).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem7581981 (f : nat -> real) : term37 f.
Proof. exact (@lem7226008 f). Qed.
Lemma lem7581982 (f : nat -> real) : (term37 f) = (term38 f).
Proof. exact (eq_refl (term37 f)). Qed.
Lemma lem7581983 (f : nat -> real) : term38 f.
Proof. exact (EQ_MP (@lem7581982 f) (@lem7581981 f)). Qed.
Lemma lem7581984 (f : nat -> real) (m : nat) : term39 f m.
Proof. exact (@lem7581983 f m). Qed.
Lemma lem7581985 (m : nat) (f : nat -> real) : (term39 f m) = (term40 m f).
Proof. exact (eq_refl (term39 f m)). Qed.
Lemma lem7581986 (m : nat) (f : nat -> real) : term40 m f.
Proof. exact (EQ_MP (@lem7581985 m f) (@lem7581984 f m)). Qed.
Lemma lem7581987 (m : nat) (f : nat -> real) (n : nat) : term41 m f n.
Proof. exact (@lem7581986 m f n). Qed.
Lemma lem7581988 (m : nat) (n : nat) (f : nat -> real) : (term41 m f n) = (term42 m n f).
Proof. exact (eq_refl (term41 m f n)). Qed.
Lemma lem7581989 (m : nat) (n : nat) (f : nat -> real) : term42 m n f.
Proof. exact (EQ_MP (@lem7581988 m n f) (@lem7581987 m f n)). Qed.
Lemma lem7581990 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem7581991 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term43 m n f) = (term44 m n f).
Proof. exact (@lem7581989 m n f (@lem7581990 m n h1)). Qed.
Lemma lem7581997 {A : Type'} (a : A) : term45 A a.
Proof. exact (@lem4363 A a). Qed.
Lemma lem7581998 {A : Type'} (a : A) : (term45 A a) = (term46 A a).
Proof. exact (eq_refl (term45 A a)). Qed.
Lemma lem7581999 {A : Type'} (a : A) : term46 A a.
Proof. exact (EQ_MP (@lem7581998 A a) (@lem7581997 A a)). Qed.
Lemma lem7582000 {A : Type'} (a : A) : (term46 A a) = ((term46 A a) = True).
Proof. exact (@lem7 (term46 A a)). Qed.
Lemma lem7582002 {A : Type'} (P : A -> Prop) : term47 A P.
Proof. exact (@lem6754 A P). Qed.
Lemma lem7582003 {A : Type'} (P : A -> Prop) : (term47 A P) = (term48 A P).
Proof. exact (eq_refl (term47 A P)). Qed.
Lemma lem7582004 {A : Type'} (P : A -> Prop) : term48 A P.
Proof. exact (EQ_MP (@lem7582003 A P) (@lem7582002 A P)). Qed.
Lemma lem7582005 {A : Type'} (P : A -> Prop) (Q : Prop) : term49 A P Q.
Proof. exact (@lem7582004 A P Q). Qed.
Lemma lem7582006 {A : Type'} (P : A -> Prop) (Q : Prop) : (term49 A P Q) = ((term50 A P Q) = (term51 A P Q)).
Proof. exact (eq_refl (term49 A P Q)). Qed.
Lemma lem7582010 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (f = g) = (term52 A B f g)) : (f = g) = (term52 A B f g).
Proof. exact (h1). Qed.
Lemma lem7582011 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (f = g) = (term52 A B f g)) : (term52 A B f g) = (f = g).
Proof. exact (SYM (@lem7582010 A B f g h1)). Qed.
Lemma lem7582012 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (term52 A B f g) = (f = g)) : (term52 A B f g) = (f = g).
Proof. exact (h1). Qed.
Lemma lem7582013 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (term52 A B f g) = (f = g)) : (f = g) = (term52 A B f g).
Proof. exact (SYM (@lem7582012 A B f g h1)). Qed.
Lemma lem7582014 {A B : Type'} (f : A -> B) (g : A -> B) : ((f = g) = (term52 A B f g)) = ((term52 A B f g) = (f = g)).
Proof. exact (prop_ext (fun h1 : (f = g) = (term52 A B f g) => @lem7582011 A B f g h1) (fun h1 : (term52 A B f g) = (f = g) => @lem7582013 A B f g h1)). Qed.
Lemma lem7582015 {A B : Type'} (f : A -> B) : (term53 A B f) = (term54 A B f).
Proof. exact (fun_ext (fun g : A -> B => @lem7582014 A B f g)). Qed.
Lemma lem7582016 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7582017 {A B : Type'} (f : A -> B) : (term55 A B f) = (term56 A B f).
Proof. exact (MK_COMB (@lem7582016 A B) (@lem7582015 A B f)). Qed.
Lemma lem7582018 {A B : Type'} : (term57 A B) = (term58 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem7582017 A B f)). Qed.
Lemma lem7582019 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7582020 {A B : Type'} : (term59 A B) = (term60 A B).
Proof. exact (MK_COMB (@lem7582019 A B) (@lem7582018 A B)). Qed.
Lemma lem7582021 {A B : Type'} : term60 A B.
Proof. exact (EQ_MP (@lem7582020 A B) (@lem9220 A B)). Qed.
Lemma lem7582022 {A B : Type'} (f : A -> B) : term61 A B f.
Proof. exact (@lem7582021 A B f). Qed.
Lemma lem7582023 {A B : Type'} (f : A -> B) : (term61 A B f) = (term56 A B f).
Proof. exact (eq_refl (term61 A B f)). Qed.
Lemma lem7582024 {A B : Type'} (f : A -> B) : term56 A B f.
Proof. exact (EQ_MP (@lem7582023 A B f) (@lem7582022 A B f)). Qed.
Lemma lem7582025 {A B : Type'} (f : A -> B) (g : A -> B) : term62 A B f g.
Proof. exact (@lem7582024 A B f g). Qed.
Lemma lem7582026 {A B : Type'} (f : A -> B) (g : A -> B) : (term62 A B f g) = ((term52 A B f g) = (f = g)).
Proof. exact (eq_refl (term62 A B f g)). Qed.
Lemma lem7582039 (p : Prop) : p = (term63 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7582040 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : ((term64 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P)) = (term66 _139258 _139259 _139260 P).
Proof. exact (@lem7582039 ((term64 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P))). Qed.
Lemma lem7582041 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term66 _139258 _139259 _139260 P) = ((term64 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P)).
Proof. exact (SYM (@lem7582040 _139258 _139259 _139260 P)). Qed.
Lemma lem7582042 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term67 _139258 _139259 _139260 P) : term67 _139258 _139259 _139260 P.
Proof. exact (h1). Qed.
Lemma lem7582045 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term66 _139258 _139259 _139260 P) : term66 _139258 _139259 _139260 P.
Proof. exact (h1). Qed.
Lemma lem7582046 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : term68 _139258 _139259 _139260 P.
Proof. exact (fun h0 : term66 _139258 _139259 _139260 P => @lem7582045 _139258 _139259 _139260 P h0). Qed.
Lemma lem7582047 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term68 _139258 _139259 _139260 P) : term68 _139258 _139259 _139260 P.
Proof. exact (h1). Qed.
Lemma lem7582048 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term66 _139258 _139259 _139260 P) : term66 _139258 _139259 _139260 P.
Proof. exact (h1). Qed.
Lemma lem7582049 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term66 _139258 _139259 _139260 P) (h2 : term68 _139258 _139259 _139260 P) : term66 _139258 _139259 _139260 P.
Proof. exact (@lem7582047 _139258 _139259 _139260 P h2 (@lem7582048 _139258 _139259 _139260 P h1)). Qed.
Lemma lem7582050 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term66 _139258 _139259 _139260 P) : term69 _139258 _139259 _139260 P.
Proof. exact (fun h0 : term68 _139258 _139259 _139260 P => @lem7582049 _139258 _139259 _139260 P h1 h0). Qed.
Lemma lem7582051 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term68 _139258 _139259 _139260 P) : term68 _139258 _139259 _139260 P.
Proof. exact (h1). Qed.
Lemma lem7582052 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term66 _139258 _139259 _139260 P) (h2 : term68 _139258 _139259 _139260 P) : term66 _139258 _139259 _139260 P.
Proof. exact (@lem7582050 _139258 _139259 _139260 P h1 (@lem7582051 _139258 _139259 _139260 P h2)). Qed.
Lemma lem7582053 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term68 _139258 _139259 _139260 P) : term68 _139258 _139259 _139260 P.
Proof. exact (fun h0 : term66 _139258 _139259 _139260 P => @lem7582052 _139258 _139259 _139260 P h0 h1). Qed.
Lemma lem7582054 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : term70 _139258 _139259 _139260 P.
Proof. exact (fun h0 : term68 _139258 _139259 _139260 P => @lem7582053 _139258 _139259 _139260 P h0). Qed.
Lemma lem7582057 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : term68 _139258 _139259 _139260 P.
Proof. exact (@lem7582054 _139258 _139259 _139260 P (@lem7582046 _139258 _139259 _139260 P)). Qed.
Lemma lem7582058 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : term68 _139258 _139259 _139260 P.
Proof. exact (@lem7582057 _139258 _139259 _139260 P). Qed.
Lemma lem7582064 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7582065 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term66 _139258 _139259 _139260 P) = (term71 _139258 _139259 _139260 P).
Proof. exact (@lem7582064 (term67 _139258 _139259 _139260 P)). Qed.
Lemma lem7582067 (t : Prop) : (term72 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7582068 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term71 _139258 _139259 _139260 P) = ((term64 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P)).
Proof. exact (@lem7582067 ((term64 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P))). Qed.
Lemma lem7582069 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term66 _139258 _139259 _139260 P) = ((term64 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P)).
Proof. exact (TRANS (@lem7582065 _139258 _139259 _139260 P) (@lem7582068 _139258 _139259 _139260 P)). Qed.
Lemma lem7582094 {_139258 _139259 _139260 : Type'} : (term73 _139258 _139259 _139260) = (term74 _139258 _139259 _139260).
Proof. exact (fun_ext (fun P : type1517 _139258 _139259 _139260 => @lem7582069 _139258 _139259 _139260 P)). Qed.
Lemma lem7582095 {_139258 _139259 _139260 : Type'} : (@all (_139260 -> _139259 -> _139258 -> Prop)) = (@all (_139260 -> _139259 -> _139258 -> Prop)).
Proof. exact (eq_refl (@all (_139260 -> _139259 -> _139258 -> Prop))). Qed.
Lemma lem7582104 {_139258 _139259 _139260 : Type'} : (term75 _139258 _139259 _139260) = (term76 _139258 _139259 _139260).
Proof. exact (MK_COMB (@lem7582095 _139258 _139259 _139260) (@lem7582094 _139258 _139259 _139260)). Qed.
Lemma lem7582105 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7582106 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term77 _139258 _139259 _139260 P m c) = (term77 _139258 _139259 _139260 P m c).
Proof. exact (fun_ext (fun q : _139260 => @lem7582105 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582107 {_139260 : Type'} : (@all _139260) = (@all _139260).
Proof. exact (eq_refl (@all _139260)). Qed.
Lemma lem7582108 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term78 _139258 _139259 _139260 P m c) = (term78 _139258 _139259 _139260 P m c).
Proof. exact (MK_COMB (@lem7582107 _139260) (@lem7582106 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582109 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term79 _139258 _139259 _139260 P m) = (term79 _139258 _139259 _139260 P m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582108 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582110 {_139258 : Type'} : (@all _139258) = (@all _139258).
Proof. exact (eq_refl (@all _139258)). Qed.
Lemma lem7582111 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term80 _139258 _139259 _139260 P m) = (term80 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582110 _139258) (@lem7582109 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582112 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term81 _139258 _139259 _139260 P) = (term81 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun m : _139259 => @lem7582111 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582113 {_139259 : Type'} : (@all _139259) = (@all _139259).
Proof. exact (eq_refl (@all _139259)). Qed.
Lemma lem7582114 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term65 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582113 _139259) (@lem7582112 _139258 _139259 _139260 P)). Qed.
Lemma lem7582115 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7582116 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term82 _139258 _139259 _139260 P q m) = (term82 _139258 _139259 _139260 P q m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582115 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582117 {_139258 : Type'} : (@all _139258) = (@all _139258).
Proof. exact (eq_refl (@all _139258)). Qed.
Lemma lem7582118 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term83 _139258 _139259 _139260 P q m) = (term83 _139258 _139259 _139260 P q m).
Proof. exact (MK_COMB (@lem7582117 _139258) (@lem7582116 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582119 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term84 _139258 _139259 _139260 P q) = (term84 _139258 _139259 _139260 P q).
Proof. exact (fun_ext (fun m : _139259 => @lem7582118 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582120 {_139259 : Type'} : (@all _139259) = (@all _139259).
Proof. exact (eq_refl (@all _139259)). Qed.
Lemma lem7582121 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term85 _139258 _139259 _139260 P q) = (term85 _139258 _139259 _139260 P q).
Proof. exact (MK_COMB (@lem7582120 _139259) (@lem7582119 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582122 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term86 _139258 _139259 _139260 P) = (term86 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun q : _139260 => @lem7582121 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582123 {_139260 : Type'} : (@all _139260) = (@all _139260).
Proof. exact (eq_refl (@all _139260)). Qed.
Lemma lem7582124 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term64 _139258 _139259 _139260 P) = (term64 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582123 _139260) (@lem7582122 _139258 _139259 _139260 P)). Qed.
Lemma lem7582125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582126 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term87 _139258 _139259 _139260 P) = (term87 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582125) (@lem7582124 _139258 _139259 _139260 P)). Qed.
Lemma lem7582127 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : ((term64 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P)) = ((term64 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P)).
Proof. exact (MK_COMB (@lem7582126 _139258 _139259 _139260 P) (@lem7582114 _139258 _139259 _139260 P)). Qed.
Lemma lem7582128 {_139258 _139259 _139260 : Type'} : (term74 _139258 _139259 _139260) = (term74 _139258 _139259 _139260).
Proof. exact (fun_ext (fun P : type1517 _139258 _139259 _139260 => @lem7582127 _139258 _139259 _139260 P)). Qed.
Lemma lem7582129 {_139258 _139259 _139260 : Type'} : (@all (_139260 -> _139259 -> _139258 -> Prop)) = (@all (_139260 -> _139259 -> _139258 -> Prop)).
Proof. exact (eq_refl (@all (_139260 -> _139259 -> _139258 -> Prop))). Qed.
Lemma lem7582130 {_139258 _139259 _139260 : Type'} : (term76 _139258 _139259 _139260) = (term76 _139258 _139259 _139260).
Proof. exact (MK_COMB (@lem7582129 _139258 _139259 _139260) (@lem7582128 _139258 _139259 _139260)). Qed.
Lemma lem7582175 {_139258 _139259 _139260 : Type'} : (term75 _139258 _139259 _139260) = (term76 _139258 _139259 _139260).
Proof. exact (TRANS (@lem7582104 _139258 _139259 _139260) (@lem7582130 _139258 _139259 _139260)). Qed.
Lemma lem7582176 {_139258 _139259 _139260 : Type'} : (term76 _139258 _139259 _139260) = (term75 _139258 _139259 _139260).
Proof. exact (SYM (@lem7582175 _139258 _139259 _139260)). Qed.
Lemma lem7582178 (p : Prop) : p = (term63 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7582179 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : ((term64 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P)) = (term66 _139258 _139259 _139260 P).
Proof. exact (@lem7582178 ((term64 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P))). Qed.
Lemma lem7582180 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term66 _139258 _139259 _139260 P) = ((term64 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P)).
Proof. exact (SYM (@lem7582179 _139258 _139259 _139260 P)). Qed.
Lemma lem7582181 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term67 _139258 _139259 _139260 P) : term67 _139258 _139259 _139260 P.
Proof. exact (h1). Qed.
Lemma lem7582183 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7582184 {_139258 : Type'} (P : _139258 -> Prop) : (term88 _139258 P) = (term89 _139258 P).
Proof. exact (@lem18392 _139258 P). Qed.
Lemma lem7582185 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term90 _139258 _139259 _139260 P q m) = (term91 _139258 _139259 _139260 P q m).
Proof. exact (@lem7582184 _139258 (term82 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582186 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term92 _139258 _139259 _139260 P q m c) = (P q m c).
Proof. exact (eq_refl (term92 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582187 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7582189 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term93 _139258 _139259 _139260 P q m c) = (term94 _139258 _139259 _139260 P q m c).
Proof. exact (MK_COMB (@lem7582187) (@lem7582186 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582190 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term95 _139258 _139259 _139260 P q m) = (term96 _139258 _139259 _139260 P q m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582189 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582191 {_139258 : Type'} : (@ex _139258) = (@ex _139258).
Proof. exact (eq_refl (@ex _139258)). Qed.
Lemma lem7582192 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term91 _139258 _139259 _139260 P q m) = (term97 _139258 _139259 _139260 P q m).
Proof. exact (MK_COMB (@lem7582191 _139258) (@lem7582190 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582193 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term90 _139258 _139259 _139260 P q m) = (term97 _139258 _139259 _139260 P q m).
Proof. exact (TRANS (@lem7582185 _139258 _139259 _139260 P q m) (@lem7582192 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582194 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term82 _139258 _139259 _139260 P q m) = (term82 _139258 _139259 _139260 P q m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582183 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582195 {_139258 : Type'} : (@all _139258) = (@all _139258).
Proof. exact (eq_refl (@all _139258)). Qed.
Lemma lem7582196 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term83 _139258 _139259 _139260 P q m) = (term83 _139258 _139259 _139260 P q m).
Proof. exact (MK_COMB (@lem7582195 _139258) (@lem7582194 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582197 {_139259 : Type'} (P : _139259 -> Prop) : (term88 _139259 P) = (term89 _139259 P).
Proof. exact (@lem18392 _139259 P). Qed.
Lemma lem7582198 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term98 _139258 _139259 _139260 P q) = (term99 _139258 _139259 _139260 P q).
Proof. exact (@lem7582197 _139259 (term84 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582199 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term100 _139258 _139259 _139260 P q m) = (term83 _139258 _139259 _139260 P q m).
Proof. exact (eq_refl (term100 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582200 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7582201 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term101 _139258 _139259 _139260 P q m) = (term90 _139258 _139259 _139260 P q m).
Proof. exact (MK_COMB (@lem7582200) (@lem7582199 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582202 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term101 _139258 _139259 _139260 P q m) = (term97 _139258 _139259 _139260 P q m).
Proof. exact (TRANS (@lem7582201 _139258 _139259 _139260 P q m) (@lem7582193 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582203 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term102 _139258 _139259 _139260 P q) = (term103 _139258 _139259 _139260 P q).
Proof. exact (fun_ext (fun m : _139259 => @lem7582202 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582204 {_139259 : Type'} : (@ex _139259) = (@ex _139259).
Proof. exact (eq_refl (@ex _139259)). Qed.
Lemma lem7582205 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term99 _139258 _139259 _139260 P q) = (term104 _139258 _139259 _139260 P q).
Proof. exact (MK_COMB (@lem7582204 _139259) (@lem7582203 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582206 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term98 _139258 _139259 _139260 P q) = (term104 _139258 _139259 _139260 P q).
Proof. exact (TRANS (@lem7582198 _139258 _139259 _139260 P q) (@lem7582205 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582207 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term84 _139258 _139259 _139260 P q) = (term84 _139258 _139259 _139260 P q).
Proof. exact (fun_ext (fun m : _139259 => @lem7582196 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582208 {_139259 : Type'} : (@all _139259) = (@all _139259).
Proof. exact (eq_refl (@all _139259)). Qed.
Lemma lem7582209 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term85 _139258 _139259 _139260 P q) = (term85 _139258 _139259 _139260 P q).
Proof. exact (MK_COMB (@lem7582208 _139259) (@lem7582207 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582210 {_139260 : Type'} (P : _139260 -> Prop) : (term88 _139260 P) = (term89 _139260 P).
Proof. exact (@lem18392 _139260 P). Qed.
Lemma lem7582211 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term105 _139258 _139259 _139260 P) = (term106 _139258 _139259 _139260 P).
Proof. exact (@lem7582210 _139260 (term86 _139258 _139259 _139260 P)). Qed.
Lemma lem7582212 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term107 _139258 _139259 _139260 P q) = (term85 _139258 _139259 _139260 P q).
Proof. exact (eq_refl (term107 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582213 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7582214 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term108 _139258 _139259 _139260 P q) = (term98 _139258 _139259 _139260 P q).
Proof. exact (MK_COMB (@lem7582213) (@lem7582212 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582215 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term108 _139258 _139259 _139260 P q) = (term104 _139258 _139259 _139260 P q).
Proof. exact (TRANS (@lem7582214 _139258 _139259 _139260 P q) (@lem7582206 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582216 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term109 _139258 _139259 _139260 P) = (term110 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun q : _139260 => @lem7582215 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582217 {_139260 : Type'} : (@ex _139260) = (@ex _139260).
Proof. exact (eq_refl (@ex _139260)). Qed.
Lemma lem7582218 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term106 _139258 _139259 _139260 P) = (term111 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582217 _139260) (@lem7582216 _139258 _139259 _139260 P)). Qed.
Lemma lem7582219 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term105 _139258 _139259 _139260 P) = (term111 _139258 _139259 _139260 P).
Proof. exact (TRANS (@lem7582211 _139258 _139259 _139260 P) (@lem7582218 _139258 _139259 _139260 P)). Qed.
Lemma lem7582220 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term86 _139258 _139259 _139260 P) = (term86 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun q : _139260 => @lem7582209 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582221 {_139260 : Type'} : (@all _139260) = (@all _139260).
Proof. exact (eq_refl (@all _139260)). Qed.
Lemma lem7582222 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term64 _139258 _139259 _139260 P) = (term64 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582221 _139260) (@lem7582220 _139258 _139259 _139260 P)). Qed.
Lemma lem7582224 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7582225 {_139260 : Type'} (P : _139260 -> Prop) : (term88 _139260 P) = (term89 _139260 P).
Proof. exact (@lem18392 _139260 P). Qed.
Lemma lem7582226 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term112 _139258 _139259 _139260 P m c) = (term113 _139258 _139259 _139260 P m c).
Proof. exact (@lem7582225 _139260 (term77 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582227 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term114 _139258 _139259 _139260 P m c q) = (P q m c).
Proof. exact (eq_refl (term114 _139258 _139259 _139260 P m c q)). Qed.
Lemma lem7582228 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7582230 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term115 _139258 _139259 _139260 P m c q) = (term94 _139258 _139259 _139260 P q m c).
Proof. exact (MK_COMB (@lem7582228) (@lem7582227 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582231 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term116 _139258 _139259 _139260 P m c) = (term117 _139258 _139259 _139260 P m c).
Proof. exact (fun_ext (fun q : _139260 => @lem7582230 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582232 {_139260 : Type'} : (@ex _139260) = (@ex _139260).
Proof. exact (eq_refl (@ex _139260)). Qed.
Lemma lem7582233 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term113 _139258 _139259 _139260 P m c) = (term118 _139258 _139259 _139260 P m c).
Proof. exact (MK_COMB (@lem7582232 _139260) (@lem7582231 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582234 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term112 _139258 _139259 _139260 P m c) = (term118 _139258 _139259 _139260 P m c).
Proof. exact (TRANS (@lem7582226 _139258 _139259 _139260 P m c) (@lem7582233 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582235 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term77 _139258 _139259 _139260 P m c) = (term77 _139258 _139259 _139260 P m c).
Proof. exact (fun_ext (fun q : _139260 => @lem7582224 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582236 {_139260 : Type'} : (@all _139260) = (@all _139260).
Proof. exact (eq_refl (@all _139260)). Qed.
Lemma lem7582237 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term78 _139258 _139259 _139260 P m c) = (term78 _139258 _139259 _139260 P m c).
Proof. exact (MK_COMB (@lem7582236 _139260) (@lem7582235 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582238 {_139258 : Type'} (P : _139258 -> Prop) : (term88 _139258 P) = (term89 _139258 P).
Proof. exact (@lem18392 _139258 P). Qed.
Lemma lem7582239 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term119 _139258 _139259 _139260 P m) = (term120 _139258 _139259 _139260 P m).
Proof. exact (@lem7582238 _139258 (term79 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582240 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term121 _139258 _139259 _139260 P m c) = (term78 _139258 _139259 _139260 P m c).
Proof. exact (eq_refl (term121 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582241 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7582242 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term122 _139258 _139259 _139260 P m c) = (term112 _139258 _139259 _139260 P m c).
Proof. exact (MK_COMB (@lem7582241) (@lem7582240 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582243 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term122 _139258 _139259 _139260 P m c) = (term118 _139258 _139259 _139260 P m c).
Proof. exact (TRANS (@lem7582242 _139258 _139259 _139260 P m c) (@lem7582234 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582244 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term123 _139258 _139259 _139260 P m) = (term124 _139258 _139259 _139260 P m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582243 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582245 {_139258 : Type'} : (@ex _139258) = (@ex _139258).
Proof. exact (eq_refl (@ex _139258)). Qed.
Lemma lem7582246 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term120 _139258 _139259 _139260 P m) = (term125 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582245 _139258) (@lem7582244 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582247 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term119 _139258 _139259 _139260 P m) = (term125 _139258 _139259 _139260 P m).
Proof. exact (TRANS (@lem7582239 _139258 _139259 _139260 P m) (@lem7582246 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582248 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term79 _139258 _139259 _139260 P m) = (term79 _139258 _139259 _139260 P m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582237 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582249 {_139258 : Type'} : (@all _139258) = (@all _139258).
Proof. exact (eq_refl (@all _139258)). Qed.
Lemma lem7582250 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term80 _139258 _139259 _139260 P m) = (term80 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582249 _139258) (@lem7582248 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582251 {_139259 : Type'} (P : _139259 -> Prop) : (term88 _139259 P) = (term89 _139259 P).
Proof. exact (@lem18392 _139259 P). Qed.
Lemma lem7582252 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term126 _139258 _139259 _139260 P) = (term127 _139258 _139259 _139260 P).
Proof. exact (@lem7582251 _139259 (term81 _139258 _139259 _139260 P)). Qed.
Lemma lem7582253 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term128 _139258 _139259 _139260 P m) = (term80 _139258 _139259 _139260 P m).
Proof. exact (eq_refl (term128 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582254 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7582255 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term129 _139258 _139259 _139260 P m) = (term119 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582254) (@lem7582253 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582256 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term129 _139258 _139259 _139260 P m) = (term125 _139258 _139259 _139260 P m).
Proof. exact (TRANS (@lem7582255 _139258 _139259 _139260 P m) (@lem7582247 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582257 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term130 _139258 _139259 _139260 P) = (term131 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun m : _139259 => @lem7582256 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582258 {_139259 : Type'} : (@ex _139259) = (@ex _139259).
Proof. exact (eq_refl (@ex _139259)). Qed.
Lemma lem7582259 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term127 _139258 _139259 _139260 P) = (term132 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582258 _139259) (@lem7582257 _139258 _139259 _139260 P)). Qed.
Lemma lem7582260 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term126 _139258 _139259 _139260 P) = (term132 _139258 _139259 _139260 P).
Proof. exact (TRANS (@lem7582252 _139258 _139259 _139260 P) (@lem7582259 _139258 _139259 _139260 P)). Qed.
Lemma lem7582261 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term81 _139258 _139259 _139260 P) = (term81 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun m : _139259 => @lem7582250 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582262 {_139259 : Type'} : (@all _139259) = (@all _139259).
Proof. exact (eq_refl (@all _139259)). Qed.
Lemma lem7582263 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term65 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582262 _139259) (@lem7582261 _139258 _139259 _139260 P)). Qed.
Lemma lem7582264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7582265 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term133 _139258 _139259 _139260 P) = (term134 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582264) (@lem7582219 _139258 _139259 _139260 P)). Qed.
Lemma lem7582266 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term135 _139258 _139259 _139260 P) = (term136 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582265 _139258 _139259 _139260 P) (@lem7582263 _139258 _139259 _139260 P)). Qed.
Lemma lem7582267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7582268 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term137 _139258 _139259 _139260 P) = (term137 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582267) (@lem7582222 _139258 _139259 _139260 P)). Qed.
Lemma lem7582269 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term138 _139258 _139259 _139260 P) = (term139 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582268 _139258 _139259 _139260 P) (@lem7582260 _139258 _139259 _139260 P)). Qed.
Lemma lem7582270 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7582271 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term140 _139258 _139259 _139260 P) = (term141 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582270) (@lem7582269 _139258 _139259 _139260 P)). Qed.
Lemma lem7582272 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term142 _139258 _139259 _139260 P) = (term143 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582271 _139258 _139259 _139260 P) (@lem7582266 _139258 _139259 _139260 P)). Qed.
Lemma lem7582273 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term67 _139258 _139259 _139260 P) = (term142 _139258 _139259 _139260 P).
Proof. exact (@lem17646 (term64 _139258 _139259 _139260 P) (term65 _139258 _139259 _139260 P)). Qed.
Lemma lem7582274 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term67 _139258 _139259 _139260 P) = (term143 _139258 _139259 _139260 P).
Proof. exact (TRANS (@lem7582273 _139258 _139259 _139260 P) (@lem7582272 _139258 _139259 _139260 P)). Qed.
Lemma lem7582325 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7582326 {_139259 : Type'} (P : Prop) (Q : _139259 -> Prop) : (term144 _139259 P Q) = (term145 _139259 P Q).
Proof. exact (@lem7582325 _139259 P Q). Qed.
Lemma lem7582327 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term146 _139258 _139259 _139260 P) = (term147 _139258 _139259 _139260 P).
Proof. exact (@lem7582326 _139259 (term64 _139258 _139259 _139260 P) (term131 _139258 _139259 _139260 P)). Qed.
Lemma lem7582328 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term148 _139258 _139259 _139260 P m) = (term125 _139258 _139259 _139260 P m).
Proof. exact (eq_refl (term148 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582329 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term149 _139258 _139259 _139260 P) = (term131 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun m : _139259 => @lem7582328 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582330 {_139259 : Type'} : (@ex _139259) = (@ex _139259).
Proof. exact (eq_refl (@ex _139259)). Qed.
Lemma lem7582331 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term150 _139258 _139259 _139260 P) = (term132 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582330 _139259) (@lem7582329 _139258 _139259 _139260 P)). Qed.
Lemma lem7582332 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term137 _139258 _139259 _139260 P) = (term137 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term137 _139258 _139259 _139260 P)). Qed.
Lemma lem7582333 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term146 _139258 _139259 _139260 P) = (term139 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582332 _139258 _139259 _139260 P) (@lem7582331 _139258 _139259 _139260 P)). Qed.
Lemma lem7582334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582335 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term151 _139258 _139259 _139260 P) = (term152 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582334) (@lem7582333 _139258 _139259 _139260 P)). Qed.
Lemma lem7582336 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term148 _139258 _139259 _139260 P m) = (term125 _139258 _139259 _139260 P m).
Proof. exact (eq_refl (term148 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582337 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term137 _139258 _139259 _139260 P) = (term137 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term137 _139258 _139259 _139260 P)). Qed.
Lemma lem7582338 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term153 _139258 _139259 _139260 P m) = (term154 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582337 _139258 _139259 _139260 P) (@lem7582336 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582339 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term155 _139258 _139259 _139260 P) = (term156 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun m : _139259 => @lem7582338 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582340 {_139259 : Type'} : (@ex _139259) = (@ex _139259).
Proof. exact (eq_refl (@ex _139259)). Qed.
Lemma lem7582341 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term147 _139258 _139259 _139260 P) = (term157 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582340 _139259) (@lem7582339 _139258 _139259 _139260 P)). Qed.
Lemma lem7582342 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : ((term146 _139258 _139259 _139260 P) = (term147 _139258 _139259 _139260 P)) = ((term139 _139258 _139259 _139260 P) = (term157 _139258 _139259 _139260 P)).
Proof. exact (MK_COMB (@lem7582335 _139258 _139259 _139260 P) (@lem7582341 _139258 _139259 _139260 P)). Qed.
Lemma lem7582343 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term139 _139258 _139259 _139260 P) = (term157 _139258 _139259 _139260 P).
Proof. exact (EQ_MP (@lem7582342 _139258 _139259 _139260 P) (@lem7582327 _139258 _139259 _139260 P)). Qed.
Lemma lem7582345 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7582346 {_139258 : Type'} (P : Prop) (Q : _139258 -> Prop) : (term144 _139258 P Q) = (term145 _139258 P Q).
Proof. exact (@lem7582345 _139258 P Q). Qed.
Lemma lem7582347 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term158 _139258 _139259 _139260 P m) = (term159 _139258 _139259 _139260 P m).
Proof. exact (@lem7582346 _139258 (term64 _139258 _139259 _139260 P) (term124 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582348 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term160 _139258 _139259 _139260 P m c) = (term118 _139258 _139259 _139260 P m c).
Proof. exact (eq_refl (term160 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582349 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term161 _139258 _139259 _139260 P m) = (term124 _139258 _139259 _139260 P m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582348 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582350 {_139258 : Type'} : (@ex _139258) = (@ex _139258).
Proof. exact (eq_refl (@ex _139258)). Qed.
Lemma lem7582351 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term162 _139258 _139259 _139260 P m) = (term125 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582350 _139258) (@lem7582349 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582352 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term137 _139258 _139259 _139260 P) = (term137 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term137 _139258 _139259 _139260 P)). Qed.
Lemma lem7582353 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term158 _139258 _139259 _139260 P m) = (term154 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582352 _139258 _139259 _139260 P) (@lem7582351 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582355 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term163 _139258 _139259 _139260 P m) = (term164 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582354) (@lem7582353 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582356 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term160 _139258 _139259 _139260 P m c) = (term118 _139258 _139259 _139260 P m c).
Proof. exact (eq_refl (term160 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582357 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term137 _139258 _139259 _139260 P) = (term137 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term137 _139258 _139259 _139260 P)). Qed.
Lemma lem7582358 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term165 _139258 _139259 _139260 P m c) = (term166 _139258 _139259 _139260 P m c).
Proof. exact (MK_COMB (@lem7582357 _139258 _139259 _139260 P) (@lem7582356 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582359 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term167 _139258 _139259 _139260 P m) = (term168 _139258 _139259 _139260 P m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582358 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582360 {_139258 : Type'} : (@ex _139258) = (@ex _139258).
Proof. exact (eq_refl (@ex _139258)). Qed.
Lemma lem7582361 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term159 _139258 _139259 _139260 P m) = (term169 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582360 _139258) (@lem7582359 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582362 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : ((term158 _139258 _139259 _139260 P m) = (term159 _139258 _139259 _139260 P m)) = ((term154 _139258 _139259 _139260 P m) = (term169 _139258 _139259 _139260 P m)).
Proof. exact (MK_COMB (@lem7582355 _139258 _139259 _139260 P m) (@lem7582361 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582363 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term154 _139258 _139259 _139260 P m) = (term169 _139258 _139259 _139260 P m).
Proof. exact (EQ_MP (@lem7582362 _139258 _139259 _139260 P m) (@lem7582347 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582365 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7582366 {_139260 : Type'} (P : Prop) (Q : _139260 -> Prop) : (term144 _139260 P Q) = (term145 _139260 P Q).
Proof. exact (@lem7582365 _139260 P Q). Qed.
Lemma lem7582367 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term170 _139258 _139259 _139260 P m c) = (term171 _139258 _139259 _139260 P m c).
Proof. exact (@lem7582366 _139260 (term64 _139258 _139259 _139260 P) (term117 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582368 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term172 _139258 _139259 _139260 P m c q) = (term94 _139258 _139259 _139260 P q m c).
Proof. exact (eq_refl (term172 _139258 _139259 _139260 P m c q)). Qed.
Lemma lem7582369 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term173 _139258 _139259 _139260 P m c) = (term117 _139258 _139259 _139260 P m c).
Proof. exact (fun_ext (fun q : _139260 => @lem7582368 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582370 {_139260 : Type'} : (@ex _139260) = (@ex _139260).
Proof. exact (eq_refl (@ex _139260)). Qed.
Lemma lem7582371 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term174 _139258 _139259 _139260 P m c) = (term118 _139258 _139259 _139260 P m c).
Proof. exact (MK_COMB (@lem7582370 _139260) (@lem7582369 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582372 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term137 _139258 _139259 _139260 P) = (term137 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term137 _139258 _139259 _139260 P)). Qed.
Lemma lem7582373 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term170 _139258 _139259 _139260 P m c) = (term166 _139258 _139259 _139260 P m c).
Proof. exact (MK_COMB (@lem7582372 _139258 _139259 _139260 P) (@lem7582371 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582375 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term175 _139258 _139259 _139260 P m c) = (term176 _139258 _139259 _139260 P m c).
Proof. exact (MK_COMB (@lem7582374) (@lem7582373 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582376 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term172 _139258 _139259 _139260 P m c q) = (term94 _139258 _139259 _139260 P q m c).
Proof. exact (eq_refl (term172 _139258 _139259 _139260 P m c q)). Qed.
Lemma lem7582377 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term137 _139258 _139259 _139260 P) = (term137 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term137 _139258 _139259 _139260 P)). Qed.
Lemma lem7582378 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term177 _139258 _139259 _139260 P m c q) = (term178 _139258 _139259 _139260 P q m c).
Proof. exact (MK_COMB (@lem7582377 _139258 _139259 _139260 P) (@lem7582376 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582379 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term179 _139258 _139259 _139260 P m c) = (term180 _139258 _139259 _139260 P m c).
Proof. exact (fun_ext (fun q : _139260 => @lem7582378 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582380 {_139260 : Type'} : (@ex _139260) = (@ex _139260).
Proof. exact (eq_refl (@ex _139260)). Qed.
Lemma lem7582381 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term171 _139258 _139259 _139260 P m c) = (term181 _139258 _139259 _139260 P m c).
Proof. exact (MK_COMB (@lem7582380 _139260) (@lem7582379 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582382 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : ((term170 _139258 _139259 _139260 P m c) = (term171 _139258 _139259 _139260 P m c)) = ((term166 _139258 _139259 _139260 P m c) = (term181 _139258 _139259 _139260 P m c)).
Proof. exact (MK_COMB (@lem7582375 _139258 _139259 _139260 P m c) (@lem7582381 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582383 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term166 _139258 _139259 _139260 P m c) = (term181 _139258 _139259 _139260 P m c).
Proof. exact (EQ_MP (@lem7582382 _139258 _139259 _139260 P m c) (@lem7582367 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582384 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term168 _139258 _139259 _139260 P m) = (term182 _139258 _139259 _139260 P m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582383 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582385 {_139258 : Type'} : (@ex _139258) = (@ex _139258).
Proof. exact (eq_refl (@ex _139258)). Qed.
Lemma lem7582386 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term169 _139258 _139259 _139260 P m) = (term183 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582385 _139258) (@lem7582384 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582387 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term154 _139258 _139259 _139260 P m) = (term183 _139258 _139259 _139260 P m).
Proof. exact (TRANS (@lem7582363 _139258 _139259 _139260 P m) (@lem7582386 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582388 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term156 _139258 _139259 _139260 P) = (term184 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun m : _139259 => @lem7582387 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582389 {_139259 : Type'} : (@ex _139259) = (@ex _139259).
Proof. exact (eq_refl (@ex _139259)). Qed.
Lemma lem7582390 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term157 _139258 _139259 _139260 P) = (term185 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582389 _139259) (@lem7582388 _139258 _139259 _139260 P)). Qed.
Lemma lem7582391 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term139 _139258 _139259 _139260 P) = (term185 _139258 _139259 _139260 P).
Proof. exact (TRANS (@lem7582343 _139258 _139259 _139260 P) (@lem7582390 _139258 _139259 _139260 P)). Qed.
Lemma lem7582392 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7582393 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term141 _139258 _139259 _139260 P) = (term186 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582392) (@lem7582391 _139258 _139259 _139260 P)). Qed.
Lemma lem7582395 {A : Type'} (P : A -> Prop) (Q : Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7582396 {_139260 : Type'} (P : _139260 -> Prop) (Q : Prop) : (term187 _139260 P Q) = (term188 _139260 P Q).
Proof. exact (@lem7582395 _139260 P Q). Qed.
Lemma lem7582397 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term189 _139258 _139259 _139260 P) = (term190 _139258 _139259 _139260 P).
Proof. exact (@lem7582396 _139260 (term110 _139258 _139259 _139260 P) (term65 _139258 _139259 _139260 P)). Qed.
Lemma lem7582398 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term191 _139258 _139259 _139260 P q) = (term104 _139258 _139259 _139260 P q).
Proof. exact (eq_refl (term191 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582399 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term192 _139258 _139259 _139260 P) = (term110 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun q : _139260 => @lem7582398 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582400 {_139260 : Type'} : (@ex _139260) = (@ex _139260).
Proof. exact (eq_refl (@ex _139260)). Qed.
Lemma lem7582401 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term193 _139258 _139259 _139260 P) = (term111 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582400 _139260) (@lem7582399 _139258 _139259 _139260 P)). Qed.
Lemma lem7582402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7582403 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term194 _139258 _139259 _139260 P) = (term134 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582402) (@lem7582401 _139258 _139259 _139260 P)). Qed.
Lemma lem7582404 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term65 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term65 _139258 _139259 _139260 P)). Qed.
Lemma lem7582405 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term189 _139258 _139259 _139260 P) = (term136 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582403 _139258 _139259 _139260 P) (@lem7582404 _139258 _139259 _139260 P)). Qed.
Lemma lem7582406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582407 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term195 _139258 _139259 _139260 P) = (term196 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582406) (@lem7582405 _139258 _139259 _139260 P)). Qed.
Lemma lem7582408 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term191 _139258 _139259 _139260 P q) = (term104 _139258 _139259 _139260 P q).
Proof. exact (eq_refl (term191 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582409 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7582410 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term197 _139258 _139259 _139260 P q) = (term198 _139258 _139259 _139260 P q).
Proof. exact (MK_COMB (@lem7582409) (@lem7582408 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582411 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term65 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term65 _139258 _139259 _139260 P)). Qed.
Lemma lem7582412 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : (term199 _139258 _139259 _139260 q P) = (term200 _139258 _139259 _139260 q P).
Proof. exact (MK_COMB (@lem7582410 _139258 _139259 _139260 P q) (@lem7582411 _139258 _139259 _139260 P)). Qed.
Lemma lem7582413 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term201 _139258 _139259 _139260 P) = (term202 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun q : _139260 => @lem7582412 _139258 _139259 _139260 q P)). Qed.
Lemma lem7582414 {_139260 : Type'} : (@ex _139260) = (@ex _139260).
Proof. exact (eq_refl (@ex _139260)). Qed.
Lemma lem7582415 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term190 _139258 _139259 _139260 P) = (term203 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582414 _139260) (@lem7582413 _139258 _139259 _139260 P)). Qed.
Lemma lem7582416 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : ((term189 _139258 _139259 _139260 P) = (term190 _139258 _139259 _139260 P)) = ((term136 _139258 _139259 _139260 P) = (term203 _139258 _139259 _139260 P)).
Proof. exact (MK_COMB (@lem7582407 _139258 _139259 _139260 P) (@lem7582415 _139258 _139259 _139260 P)). Qed.
Lemma lem7582417 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term136 _139258 _139259 _139260 P) = (term203 _139258 _139259 _139260 P).
Proof. exact (EQ_MP (@lem7582416 _139258 _139259 _139260 P) (@lem7582397 _139258 _139259 _139260 P)). Qed.
Lemma lem7582419 {A : Type'} (P : A -> Prop) (Q : Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7582420 {_139259 : Type'} (P : _139259 -> Prop) (Q : Prop) : (term187 _139259 P Q) = (term188 _139259 P Q).
Proof. exact (@lem7582419 _139259 P Q). Qed.
Lemma lem7582421 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : (term204 _139258 _139259 _139260 q P) = (term205 _139258 _139259 _139260 q P).
Proof. exact (@lem7582420 _139259 (term103 _139258 _139259 _139260 P q) (term65 _139258 _139259 _139260 P)). Qed.
Lemma lem7582422 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term206 _139258 _139259 _139260 P q m) = (term97 _139258 _139259 _139260 P q m).
Proof. exact (eq_refl (term206 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582423 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term207 _139258 _139259 _139260 P q) = (term103 _139258 _139259 _139260 P q).
Proof. exact (fun_ext (fun m : _139259 => @lem7582422 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582424 {_139259 : Type'} : (@ex _139259) = (@ex _139259).
Proof. exact (eq_refl (@ex _139259)). Qed.
Lemma lem7582425 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term208 _139258 _139259 _139260 P q) = (term104 _139258 _139259 _139260 P q).
Proof. exact (MK_COMB (@lem7582424 _139259) (@lem7582423 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7582427 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term209 _139258 _139259 _139260 P q) = (term198 _139258 _139259 _139260 P q).
Proof. exact (MK_COMB (@lem7582426) (@lem7582425 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582428 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term65 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term65 _139258 _139259 _139260 P)). Qed.
Lemma lem7582429 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : (term204 _139258 _139259 _139260 q P) = (term200 _139258 _139259 _139260 q P).
Proof. exact (MK_COMB (@lem7582427 _139258 _139259 _139260 P q) (@lem7582428 _139258 _139259 _139260 P)). Qed.
Lemma lem7582430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582431 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : (term210 _139258 _139259 _139260 q P) = (term211 _139258 _139259 _139260 q P).
Proof. exact (MK_COMB (@lem7582430) (@lem7582429 _139258 _139259 _139260 q P)). Qed.
Lemma lem7582432 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term206 _139258 _139259 _139260 P q m) = (term97 _139258 _139259 _139260 P q m).
Proof. exact (eq_refl (term206 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7582434 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term212 _139258 _139259 _139260 P q m) = (term213 _139258 _139259 _139260 P q m).
Proof. exact (MK_COMB (@lem7582433) (@lem7582432 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582435 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term65 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term65 _139258 _139259 _139260 P)). Qed.
Lemma lem7582436 {_139258 _139259 _139260 : Type'} (q : _139260) (m : _139259) (P : type1517 _139258 _139259 _139260) : (term214 _139258 _139259 _139260 q m P) = (term215 _139258 _139259 _139260 q m P).
Proof. exact (MK_COMB (@lem7582434 _139258 _139259 _139260 P q m) (@lem7582435 _139258 _139259 _139260 P)). Qed.
Lemma lem7582437 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : (term216 _139258 _139259 _139260 q P) = (term217 _139258 _139259 _139260 q P).
Proof. exact (fun_ext (fun m : _139259 => @lem7582436 _139258 _139259 _139260 q m P)). Qed.
Lemma lem7582438 {_139259 : Type'} : (@ex _139259) = (@ex _139259).
Proof. exact (eq_refl (@ex _139259)). Qed.
Lemma lem7582439 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : (term205 _139258 _139259 _139260 q P) = (term218 _139258 _139259 _139260 q P).
Proof. exact (MK_COMB (@lem7582438 _139259) (@lem7582437 _139258 _139259 _139260 q P)). Qed.
Lemma lem7582440 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : ((term204 _139258 _139259 _139260 q P) = (term205 _139258 _139259 _139260 q P)) = ((term200 _139258 _139259 _139260 q P) = (term218 _139258 _139259 _139260 q P)).
Proof. exact (MK_COMB (@lem7582431 _139258 _139259 _139260 q P) (@lem7582439 _139258 _139259 _139260 q P)). Qed.
Lemma lem7582441 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : (term200 _139258 _139259 _139260 q P) = (term218 _139258 _139259 _139260 q P).
Proof. exact (EQ_MP (@lem7582440 _139258 _139259 _139260 q P) (@lem7582421 _139258 _139259 _139260 q P)). Qed.
Lemma lem7582443 {A : Type'} (P : A -> Prop) (Q : Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7582444 {_139258 : Type'} (P : _139258 -> Prop) (Q : Prop) : (term187 _139258 P Q) = (term188 _139258 P Q).
Proof. exact (@lem7582443 _139258 P Q). Qed.
Lemma lem7582445 {_139258 _139259 _139260 : Type'} (q : _139260) (m : _139259) (P : type1517 _139258 _139259 _139260) : (term219 _139258 _139259 _139260 q m P) = (term220 _139258 _139259 _139260 q m P).
Proof. exact (@lem7582444 _139258 (term96 _139258 _139259 _139260 P q m) (term65 _139258 _139259 _139260 P)). Qed.
Lemma lem7582446 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term221 _139258 _139259 _139260 P q m c) = (term94 _139258 _139259 _139260 P q m c).
Proof. exact (eq_refl (term221 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582447 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term222 _139258 _139259 _139260 P q m) = (term96 _139258 _139259 _139260 P q m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582446 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582448 {_139258 : Type'} : (@ex _139258) = (@ex _139258).
Proof. exact (eq_refl (@ex _139258)). Qed.
Lemma lem7582449 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term223 _139258 _139259 _139260 P q m) = (term97 _139258 _139259 _139260 P q m).
Proof. exact (MK_COMB (@lem7582448 _139258) (@lem7582447 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7582451 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term224 _139258 _139259 _139260 P q m) = (term213 _139258 _139259 _139260 P q m).
Proof. exact (MK_COMB (@lem7582450) (@lem7582449 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582452 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term65 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term65 _139258 _139259 _139260 P)). Qed.
Lemma lem7582453 {_139258 _139259 _139260 : Type'} (q : _139260) (m : _139259) (P : type1517 _139258 _139259 _139260) : (term219 _139258 _139259 _139260 q m P) = (term215 _139258 _139259 _139260 q m P).
Proof. exact (MK_COMB (@lem7582451 _139258 _139259 _139260 P q m) (@lem7582452 _139258 _139259 _139260 P)). Qed.
Lemma lem7582454 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582455 {_139258 _139259 _139260 : Type'} (q : _139260) (m : _139259) (P : type1517 _139258 _139259 _139260) : (term225 _139258 _139259 _139260 q m P) = (term226 _139258 _139259 _139260 q m P).
Proof. exact (MK_COMB (@lem7582454) (@lem7582453 _139258 _139259 _139260 q m P)). Qed.
Lemma lem7582456 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term221 _139258 _139259 _139260 P q m c) = (term94 _139258 _139259 _139260 P q m c).
Proof. exact (eq_refl (term221 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7582458 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term227 _139258 _139259 _139260 P q m c) = (term228 _139258 _139259 _139260 P q m c).
Proof. exact (MK_COMB (@lem7582457) (@lem7582456 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582459 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term65 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term65 _139258 _139259 _139260 P)). Qed.
Lemma lem7582460 {_139258 _139259 _139260 : Type'} (q : _139260) (m : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) : (term229 _139258 _139259 _139260 q m c P) = (term230 _139258 _139259 _139260 q m c P).
Proof. exact (MK_COMB (@lem7582458 _139258 _139259 _139260 P q m c) (@lem7582459 _139258 _139259 _139260 P)). Qed.
Lemma lem7582461 {_139258 _139259 _139260 : Type'} (q : _139260) (m : _139259) (P : type1517 _139258 _139259 _139260) : (term231 _139258 _139259 _139260 q m P) = (term232 _139258 _139259 _139260 q m P).
Proof. exact (fun_ext (fun c : _139258 => @lem7582460 _139258 _139259 _139260 q m c P)). Qed.
Lemma lem7582462 {_139258 : Type'} : (@ex _139258) = (@ex _139258).
Proof. exact (eq_refl (@ex _139258)). Qed.
Lemma lem7582463 {_139258 _139259 _139260 : Type'} (q : _139260) (m : _139259) (P : type1517 _139258 _139259 _139260) : (term220 _139258 _139259 _139260 q m P) = (term233 _139258 _139259 _139260 q m P).
Proof. exact (MK_COMB (@lem7582462 _139258) (@lem7582461 _139258 _139259 _139260 q m P)). Qed.
Lemma lem7582464 {_139258 _139259 _139260 : Type'} (q : _139260) (m : _139259) (P : type1517 _139258 _139259 _139260) : ((term219 _139258 _139259 _139260 q m P) = (term220 _139258 _139259 _139260 q m P)) = ((term215 _139258 _139259 _139260 q m P) = (term233 _139258 _139259 _139260 q m P)).
Proof. exact (MK_COMB (@lem7582455 _139258 _139259 _139260 q m P) (@lem7582463 _139258 _139259 _139260 q m P)). Qed.
Lemma lem7582465 {_139258 _139259 _139260 : Type'} (q : _139260) (m : _139259) (P : type1517 _139258 _139259 _139260) : (term215 _139258 _139259 _139260 q m P) = (term233 _139258 _139259 _139260 q m P).
Proof. exact (EQ_MP (@lem7582464 _139258 _139259 _139260 q m P) (@lem7582445 _139258 _139259 _139260 q m P)). Qed.
Lemma lem7582466 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : (term217 _139258 _139259 _139260 q P) = (term234 _139258 _139259 _139260 q P).
Proof. exact (fun_ext (fun m : _139259 => @lem7582465 _139258 _139259 _139260 q m P)). Qed.
Lemma lem7582467 {_139259 : Type'} : (@ex _139259) = (@ex _139259).
Proof. exact (eq_refl (@ex _139259)). Qed.
Lemma lem7582468 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : (term218 _139258 _139259 _139260 q P) = (term235 _139258 _139259 _139260 q P).
Proof. exact (MK_COMB (@lem7582467 _139259) (@lem7582466 _139258 _139259 _139260 q P)). Qed.
Lemma lem7582469 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : (term200 _139258 _139259 _139260 q P) = (term235 _139258 _139259 _139260 q P).
Proof. exact (TRANS (@lem7582441 _139258 _139259 _139260 q P) (@lem7582468 _139258 _139259 _139260 q P)). Qed.
Lemma lem7582470 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term202 _139258 _139259 _139260 P) = (term236 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun q : _139260 => @lem7582469 _139258 _139259 _139260 q P)). Qed.
Lemma lem7582471 {_139260 : Type'} : (@ex _139260) = (@ex _139260).
Proof. exact (eq_refl (@ex _139260)). Qed.
Lemma lem7582472 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term203 _139258 _139259 _139260 P) = (term237 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582471 _139260) (@lem7582470 _139258 _139259 _139260 P)). Qed.
Lemma lem7582473 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term136 _139258 _139259 _139260 P) = (term237 _139258 _139259 _139260 P).
Proof. exact (TRANS (@lem7582417 _139258 _139259 _139260 P) (@lem7582472 _139258 _139259 _139260 P)). Qed.
Lemma lem7582474 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term143 _139258 _139259 _139260 P) = (term238 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582393 _139258 _139259 _139260 P) (@lem7582473 _139258 _139259 _139260 P)). Qed.
Lemma lem7582478 {A : Type'} (P : A -> Prop) (Q : Prop) : (term239 A P Q) = (term240 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7582479 {_139259 : Type'} (P : _139259 -> Prop) (Q : Prop) : (term239 _139259 P Q) = (term240 _139259 P Q).
Proof. exact (@lem7582478 _139259 P Q). Qed.
Lemma lem7582480 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term241 _139258 _139259 _139260 P) = (term242 _139258 _139259 _139260 P).
Proof. exact (@lem7582479 _139259 (term184 _139258 _139259 _139260 P) (term237 _139258 _139259 _139260 P)). Qed.
Lemma lem7582481 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term243 _139258 _139259 _139260 P m) = (term183 _139258 _139259 _139260 P m).
Proof. exact (eq_refl (term243 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582482 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term244 _139258 _139259 _139260 P) = (term184 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun m : _139259 => @lem7582481 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582483 {_139259 : Type'} : (@ex _139259) = (@ex _139259).
Proof. exact (eq_refl (@ex _139259)). Qed.
Lemma lem7582484 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term245 _139258 _139259 _139260 P) = (term185 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582483 _139259) (@lem7582482 _139258 _139259 _139260 P)). Qed.
Lemma lem7582485 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7582486 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term246 _139258 _139259 _139260 P) = (term186 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582485) (@lem7582484 _139258 _139259 _139260 P)). Qed.
Lemma lem7582487 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term237 _139258 _139259 _139260 P) = (term237 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term237 _139258 _139259 _139260 P)). Qed.
Lemma lem7582488 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term241 _139258 _139259 _139260 P) = (term238 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582486 _139258 _139259 _139260 P) (@lem7582487 _139258 _139259 _139260 P)). Qed.
Lemma lem7582489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582490 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term247 _139258 _139259 _139260 P) = (term248 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582489) (@lem7582488 _139258 _139259 _139260 P)). Qed.
Lemma lem7582491 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term243 _139258 _139259 _139260 P m) = (term183 _139258 _139259 _139260 P m).
Proof. exact (eq_refl (term243 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582492 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7582493 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term249 _139258 _139259 _139260 P m) = (term250 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582492) (@lem7582491 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582494 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term237 _139258 _139259 _139260 P) = (term237 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term237 _139258 _139259 _139260 P)). Qed.
Lemma lem7582495 {_139258 _139259 _139260 : Type'} (m : _139259) (P : type1517 _139258 _139259 _139260) : (term251 _139258 _139259 _139260 m P) = (term252 _139258 _139259 _139260 m P).
Proof. exact (MK_COMB (@lem7582493 _139258 _139259 _139260 P m) (@lem7582494 _139258 _139259 _139260 P)). Qed.
Lemma lem7582496 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term253 _139258 _139259 _139260 P) = (term254 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun m : _139259 => @lem7582495 _139258 _139259 _139260 m P)). Qed.
Lemma lem7582497 {_139259 : Type'} : (@ex _139259) = (@ex _139259).
Proof. exact (eq_refl (@ex _139259)). Qed.
Lemma lem7582498 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term242 _139258 _139259 _139260 P) = (term255 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582497 _139259) (@lem7582496 _139258 _139259 _139260 P)). Qed.
Lemma lem7582499 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : ((term241 _139258 _139259 _139260 P) = (term242 _139258 _139259 _139260 P)) = ((term238 _139258 _139259 _139260 P) = (term255 _139258 _139259 _139260 P)).
Proof. exact (MK_COMB (@lem7582490 _139258 _139259 _139260 P) (@lem7582498 _139258 _139259 _139260 P)). Qed.
Lemma lem7582500 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term238 _139258 _139259 _139260 P) = (term255 _139258 _139259 _139260 P).
Proof. exact (EQ_MP (@lem7582499 _139258 _139259 _139260 P) (@lem7582480 _139258 _139259 _139260 P)). Qed.
Lemma lem7582504 {A : Type'} (P : A -> Prop) (Q : Prop) : (term239 A P Q) = (term240 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7582505 {_139258 : Type'} (P : _139258 -> Prop) (Q : Prop) : (term239 _139258 P Q) = (term240 _139258 P Q).
Proof. exact (@lem7582504 _139258 P Q). Qed.
Lemma lem7582506 {_139258 _139259 _139260 : Type'} (m : _139259) (P : type1517 _139258 _139259 _139260) : (term256 _139258 _139259 _139260 m P) = (term257 _139258 _139259 _139260 m P).
Proof. exact (@lem7582505 _139258 (term182 _139258 _139259 _139260 P m) (term237 _139258 _139259 _139260 P)). Qed.
Lemma lem7582507 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term258 _139258 _139259 _139260 P m c) = (term181 _139258 _139259 _139260 P m c).
Proof. exact (eq_refl (term258 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582508 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term259 _139258 _139259 _139260 P m) = (term182 _139258 _139259 _139260 P m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582507 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582509 {_139258 : Type'} : (@ex _139258) = (@ex _139258).
Proof. exact (eq_refl (@ex _139258)). Qed.
Lemma lem7582510 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term260 _139258 _139259 _139260 P m) = (term183 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582509 _139258) (@lem7582508 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582511 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7582512 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term261 _139258 _139259 _139260 P m) = (term250 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582511) (@lem7582510 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582513 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term237 _139258 _139259 _139260 P) = (term237 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term237 _139258 _139259 _139260 P)). Qed.
Lemma lem7582514 {_139258 _139259 _139260 : Type'} (m : _139259) (P : type1517 _139258 _139259 _139260) : (term256 _139258 _139259 _139260 m P) = (term252 _139258 _139259 _139260 m P).
Proof. exact (MK_COMB (@lem7582512 _139258 _139259 _139260 P m) (@lem7582513 _139258 _139259 _139260 P)). Qed.
Lemma lem7582515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582516 {_139258 _139259 _139260 : Type'} (m : _139259) (P : type1517 _139258 _139259 _139260) : (term262 _139258 _139259 _139260 m P) = (term263 _139258 _139259 _139260 m P).
Proof. exact (MK_COMB (@lem7582515) (@lem7582514 _139258 _139259 _139260 m P)). Qed.
Lemma lem7582517 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term258 _139258 _139259 _139260 P m c) = (term181 _139258 _139259 _139260 P m c).
Proof. exact (eq_refl (term258 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7582519 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term264 _139258 _139259 _139260 P m c) = (term265 _139258 _139259 _139260 P m c).
Proof. exact (MK_COMB (@lem7582518) (@lem7582517 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582520 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term237 _139258 _139259 _139260 P) = (term237 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term237 _139258 _139259 _139260 P)). Qed.
Lemma lem7582521 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) : (term266 _139258 _139259 _139260 m c P) = (term267 _139258 _139259 _139260 m c P).
Proof. exact (MK_COMB (@lem7582519 _139258 _139259 _139260 P m c) (@lem7582520 _139258 _139259 _139260 P)). Qed.
Lemma lem7582522 {_139258 _139259 _139260 : Type'} (m : _139259) (P : type1517 _139258 _139259 _139260) : (term268 _139258 _139259 _139260 m P) = (term269 _139258 _139259 _139260 m P).
Proof. exact (fun_ext (fun c : _139258 => @lem7582521 _139258 _139259 _139260 m c P)). Qed.
Lemma lem7582523 {_139258 : Type'} : (@ex _139258) = (@ex _139258).
Proof. exact (eq_refl (@ex _139258)). Qed.
Lemma lem7582524 {_139258 _139259 _139260 : Type'} (m : _139259) (P : type1517 _139258 _139259 _139260) : (term257 _139258 _139259 _139260 m P) = (term270 _139258 _139259 _139260 m P).
Proof. exact (MK_COMB (@lem7582523 _139258) (@lem7582522 _139258 _139259 _139260 m P)). Qed.
Lemma lem7582525 {_139258 _139259 _139260 : Type'} (m : _139259) (P : type1517 _139258 _139259 _139260) : ((term256 _139258 _139259 _139260 m P) = (term257 _139258 _139259 _139260 m P)) = ((term252 _139258 _139259 _139260 m P) = (term270 _139258 _139259 _139260 m P)).
Proof. exact (MK_COMB (@lem7582516 _139258 _139259 _139260 m P) (@lem7582524 _139258 _139259 _139260 m P)). Qed.
Lemma lem7582526 {_139258 _139259 _139260 : Type'} (m : _139259) (P : type1517 _139258 _139259 _139260) : (term252 _139258 _139259 _139260 m P) = (term270 _139258 _139259 _139260 m P).
Proof. exact (EQ_MP (@lem7582525 _139258 _139259 _139260 m P) (@lem7582506 _139258 _139259 _139260 m P)). Qed.
Lemma lem7582528 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7582529 {_139260 : Type'} (P : _139260 -> Prop) (Q : _139260 -> Prop) : (term271 _139260 P Q) = (term272 _139260 P Q).
Proof. exact (@lem7582528 _139260 P Q). Qed.
Lemma lem7582530 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) : (term273 _139258 _139259 _139260 m c P) = (term274 _139258 _139259 _139260 m c P).
Proof. exact (@lem7582529 _139260 (term180 _139258 _139259 _139260 P m c) (term236 _139258 _139259 _139260 P)). Qed.
Lemma lem7582531 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term275 _139258 _139259 _139260 P m c q) = (term178 _139258 _139259 _139260 P q m c).
Proof. exact (eq_refl (term275 _139258 _139259 _139260 P m c q)). Qed.
Lemma lem7582532 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term276 _139258 _139259 _139260 P m c) = (term180 _139258 _139259 _139260 P m c).
Proof. exact (fun_ext (fun q : _139260 => @lem7582531 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582533 {_139260 : Type'} : (@ex _139260) = (@ex _139260).
Proof. exact (eq_refl (@ex _139260)). Qed.
Lemma lem7582534 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term277 _139258 _139259 _139260 P m c) = (term181 _139258 _139259 _139260 P m c).
Proof. exact (MK_COMB (@lem7582533 _139260) (@lem7582532 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7582536 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term278 _139258 _139259 _139260 P m c) = (term265 _139258 _139259 _139260 P m c).
Proof. exact (MK_COMB (@lem7582535) (@lem7582534 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582537 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : (term279 _139258 _139259 _139260 P q) = (term235 _139258 _139259 _139260 q P).
Proof. exact (eq_refl (term279 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582538 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term280 _139258 _139259 _139260 P) = (term236 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun q : _139260 => @lem7582537 _139258 _139259 _139260 q P)). Qed.
Lemma lem7582539 {_139260 : Type'} : (@ex _139260) = (@ex _139260).
Proof. exact (eq_refl (@ex _139260)). Qed.
Lemma lem7582540 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term281 _139258 _139259 _139260 P) = (term237 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582539 _139260) (@lem7582538 _139258 _139259 _139260 P)). Qed.
Lemma lem7582541 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) : (term273 _139258 _139259 _139260 m c P) = (term267 _139258 _139259 _139260 m c P).
Proof. exact (MK_COMB (@lem7582536 _139258 _139259 _139260 P m c) (@lem7582540 _139258 _139259 _139260 P)). Qed.
Lemma lem7582542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582543 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) : (term282 _139258 _139259 _139260 m c P) = (term283 _139258 _139259 _139260 m c P).
Proof. exact (MK_COMB (@lem7582542) (@lem7582541 _139258 _139259 _139260 m c P)). Qed.
Lemma lem7582544 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term275 _139258 _139259 _139260 P m c q) = (term178 _139258 _139259 _139260 P q m c).
Proof. exact (eq_refl (term275 _139258 _139259 _139260 P m c q)). Qed.
Lemma lem7582545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7582546 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term284 _139258 _139259 _139260 P m c q) = (term285 _139258 _139259 _139260 P q m c).
Proof. exact (MK_COMB (@lem7582545) (@lem7582544 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582547 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : (term279 _139258 _139259 _139260 P q) = (term235 _139258 _139259 _139260 q P).
Proof. exact (eq_refl (term279 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582548 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (P : type1517 _139258 _139259 _139260) : (term286 _139258 _139259 _139260 m c P q) = (term287 _139258 _139259 _139260 m c q P).
Proof. exact (MK_COMB (@lem7582546 _139258 _139259 _139260 P q m c) (@lem7582547 _139258 _139259 _139260 q P)). Qed.
Lemma lem7582549 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) : (term288 _139258 _139259 _139260 m c P) = (term289 _139258 _139259 _139260 m c P).
Proof. exact (fun_ext (fun q : _139260 => @lem7582548 _139258 _139259 _139260 m c q P)). Qed.
Lemma lem7582550 {_139260 : Type'} : (@ex _139260) = (@ex _139260).
Proof. exact (eq_refl (@ex _139260)). Qed.
Lemma lem7582551 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) : (term274 _139258 _139259 _139260 m c P) = (term290 _139258 _139259 _139260 m c P).
Proof. exact (MK_COMB (@lem7582550 _139260) (@lem7582549 _139258 _139259 _139260 m c P)). Qed.
Lemma lem7582552 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) : ((term273 _139258 _139259 _139260 m c P) = (term274 _139258 _139259 _139260 m c P)) = ((term267 _139258 _139259 _139260 m c P) = (term290 _139258 _139259 _139260 m c P)).
Proof. exact (MK_COMB (@lem7582543 _139258 _139259 _139260 m c P) (@lem7582551 _139258 _139259 _139260 m c P)). Qed.
Lemma lem7582553 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) : (term267 _139258 _139259 _139260 m c P) = (term290 _139258 _139259 _139260 m c P).
Proof. exact (EQ_MP (@lem7582552 _139258 _139259 _139260 m c P) (@lem7582530 _139258 _139259 _139260 m c P)). Qed.
Lemma lem7582555 {A : Type'} (P : Prop) (Q : A -> Prop) : (term291 A P Q) = (term292 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7582556 {_139259 : Type'} (P : Prop) (Q : _139259 -> Prop) : (term291 _139259 P Q) = (term292 _139259 P Q).
Proof. exact (@lem7582555 _139259 P Q). Qed.
Lemma lem7582557 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (P : type1517 _139258 _139259 _139260) : (term293 _139258 _139259 _139260 m c q P) = (term294 _139258 _139259 _139260 m c q P).
Proof. exact (@lem7582556 _139259 (term178 _139258 _139259 _139260 P q m c) (term234 _139258 _139259 _139260 q P)). Qed.
Lemma lem7582558 {_139258 _139259 _139260 : Type'} (q : _139260) (m : _139259) (P : type1517 _139258 _139259 _139260) : (term295 _139258 _139259 _139260 q P m) = (term233 _139258 _139259 _139260 q m P).
Proof. exact (eq_refl (term295 _139258 _139259 _139260 q P m)). Qed.
Lemma lem7582559 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : (term296 _139258 _139259 _139260 q P) = (term234 _139258 _139259 _139260 q P).
Proof. exact (fun_ext (fun m : _139259 => @lem7582558 _139258 _139259 _139260 q m P)). Qed.
Lemma lem7582560 {_139259 : Type'} : (@ex _139259) = (@ex _139259).
Proof. exact (eq_refl (@ex _139259)). Qed.
Lemma lem7582561 {_139258 _139259 _139260 : Type'} (q : _139260) (P : type1517 _139258 _139259 _139260) : (term297 _139258 _139259 _139260 q P) = (term235 _139258 _139259 _139260 q P).
Proof. exact (MK_COMB (@lem7582560 _139259) (@lem7582559 _139258 _139259 _139260 q P)). Qed.
Lemma lem7582562 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term285 _139258 _139259 _139260 P q m c) = (term285 _139258 _139259 _139260 P q m c).
Proof. exact (eq_refl (term285 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582563 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (P : type1517 _139258 _139259 _139260) : (term293 _139258 _139259 _139260 m c q P) = (term287 _139258 _139259 _139260 m c q P).
Proof. exact (MK_COMB (@lem7582562 _139258 _139259 _139260 P q m c) (@lem7582561 _139258 _139259 _139260 q P)). Qed.
Lemma lem7582564 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582565 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (P : type1517 _139258 _139259 _139260) : (term298 _139258 _139259 _139260 m c q P) = (term299 _139258 _139259 _139260 m c q P).
Proof. exact (MK_COMB (@lem7582564) (@lem7582563 _139258 _139259 _139260 m c q P)). Qed.
Lemma lem7582566 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (P : type1517 _139258 _139259 _139260) : (term295 _139258 _139259 _139260 q P m') = (term233 _139258 _139259 _139260 q m' P).
Proof. exact (eq_refl (term295 _139258 _139259 _139260 q P m')). Qed.
Lemma lem7582567 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term285 _139258 _139259 _139260 P q m c) = (term285 _139258 _139259 _139260 P q m c).
Proof. exact (eq_refl (term285 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582568 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (P : type1517 _139258 _139259 _139260) : (term300 _139258 _139259 _139260 m c q P m') = (term301 _139258 _139259 _139260 m c q m' P).
Proof. exact (MK_COMB (@lem7582567 _139258 _139259 _139260 P q m c) (@lem7582566 _139258 _139259 _139260 q m' P)). Qed.
Lemma lem7582569 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (P : type1517 _139258 _139259 _139260) : (term302 _139258 _139259 _139260 m c q P) = (term303 _139258 _139259 _139260 m c q P).
Proof. exact (fun_ext (fun m' : _139259 => @lem7582568 _139258 _139259 _139260 m c q m' P)). Qed.
Lemma lem7582570 {_139259 : Type'} : (@ex _139259) = (@ex _139259).
Proof. exact (eq_refl (@ex _139259)). Qed.
Lemma lem7582571 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (P : type1517 _139258 _139259 _139260) : (term294 _139258 _139259 _139260 m c q P) = (term304 _139258 _139259 _139260 m c q P).
Proof. exact (MK_COMB (@lem7582570 _139259) (@lem7582569 _139258 _139259 _139260 m c q P)). Qed.
Lemma lem7582572 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (P : type1517 _139258 _139259 _139260) : ((term293 _139258 _139259 _139260 m c q P) = (term294 _139258 _139259 _139260 m c q P)) = ((term287 _139258 _139259 _139260 m c q P) = (term304 _139258 _139259 _139260 m c q P)).
Proof. exact (MK_COMB (@lem7582565 _139258 _139259 _139260 m c q P) (@lem7582571 _139258 _139259 _139260 m c q P)). Qed.
Lemma lem7582573 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (P : type1517 _139258 _139259 _139260) : (term287 _139258 _139259 _139260 m c q P) = (term304 _139258 _139259 _139260 m c q P).
Proof. exact (EQ_MP (@lem7582572 _139258 _139259 _139260 m c q P) (@lem7582557 _139258 _139259 _139260 m c q P)). Qed.
Lemma lem7582575 {A : Type'} (P : Prop) (Q : A -> Prop) : (term291 A P Q) = (term292 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7582576 {_139258 : Type'} (P : Prop) (Q : _139258 -> Prop) : (term291 _139258 P Q) = (term292 _139258 P Q).
Proof. exact (@lem7582575 _139258 P Q). Qed.
Lemma lem7582577 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (P : type1517 _139258 _139259 _139260) : (term305 _139258 _139259 _139260 m c q m' P) = (term306 _139258 _139259 _139260 m c q m' P).
Proof. exact (@lem7582576 _139258 (term178 _139258 _139259 _139260 P q m c) (term232 _139258 _139259 _139260 q m' P)). Qed.
Lemma lem7582578 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) : (term307 _139258 _139259 _139260 q m' P c) = (term230 _139258 _139259 _139260 q m' c P).
Proof. exact (eq_refl (term307 _139258 _139259 _139260 q m' P c)). Qed.
Lemma lem7582579 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (P : type1517 _139258 _139259 _139260) : (term308 _139258 _139259 _139260 q m' P) = (term232 _139258 _139259 _139260 q m' P).
Proof. exact (fun_ext (fun c : _139258 => @lem7582578 _139258 _139259 _139260 q m' c P)). Qed.
Lemma lem7582580 {_139258 : Type'} : (@ex _139258) = (@ex _139258).
Proof. exact (eq_refl (@ex _139258)). Qed.
Lemma lem7582581 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (P : type1517 _139258 _139259 _139260) : (term309 _139258 _139259 _139260 q m' P) = (term233 _139258 _139259 _139260 q m' P).
Proof. exact (MK_COMB (@lem7582580 _139258) (@lem7582579 _139258 _139259 _139260 q m' P)). Qed.
Lemma lem7582582 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term285 _139258 _139259 _139260 P q m c) = (term285 _139258 _139259 _139260 P q m c).
Proof. exact (eq_refl (term285 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582583 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (P : type1517 _139258 _139259 _139260) : (term305 _139258 _139259 _139260 m c q m' P) = (term301 _139258 _139259 _139260 m c q m' P).
Proof. exact (MK_COMB (@lem7582582 _139258 _139259 _139260 P q m c) (@lem7582581 _139258 _139259 _139260 q m' P)). Qed.
Lemma lem7582584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582585 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (P : type1517 _139258 _139259 _139260) : (term310 _139258 _139259 _139260 m c q m' P) = (term311 _139258 _139259 _139260 m c q m' P).
Proof. exact (MK_COMB (@lem7582584) (@lem7582583 _139258 _139259 _139260 m c q m' P)). Qed.
Lemma lem7582586 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) : (term307 _139258 _139259 _139260 q m' P c') = (term230 _139258 _139259 _139260 q m' c' P).
Proof. exact (eq_refl (term307 _139258 _139259 _139260 q m' P c')). Qed.
Lemma lem7582587 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term285 _139258 _139259 _139260 P q m c) = (term285 _139258 _139259 _139260 P q m c).
Proof. exact (eq_refl (term285 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582588 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) : (term312 _139258 _139259 _139260 m c q m' P c') = (term313 _139258 _139259 _139260 m c q m' c' P).
Proof. exact (MK_COMB (@lem7582587 _139258 _139259 _139260 P q m c) (@lem7582586 _139258 _139259 _139260 q m' c' P)). Qed.
Lemma lem7582589 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (P : type1517 _139258 _139259 _139260) : (term314 _139258 _139259 _139260 m c q m' P) = (term315 _139258 _139259 _139260 m c q m' P).
Proof. exact (fun_ext (fun c' : _139258 => @lem7582588 _139258 _139259 _139260 m c q m' c' P)). Qed.
Lemma lem7582590 {_139258 : Type'} : (@ex _139258) = (@ex _139258).
Proof. exact (eq_refl (@ex _139258)). Qed.
Lemma lem7582591 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (P : type1517 _139258 _139259 _139260) : (term306 _139258 _139259 _139260 m c q m' P) = (term316 _139258 _139259 _139260 m c q m' P).
Proof. exact (MK_COMB (@lem7582590 _139258) (@lem7582589 _139258 _139259 _139260 m c q m' P)). Qed.
Lemma lem7582592 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (P : type1517 _139258 _139259 _139260) : ((term305 _139258 _139259 _139260 m c q m' P) = (term306 _139258 _139259 _139260 m c q m' P)) = ((term301 _139258 _139259 _139260 m c q m' P) = (term316 _139258 _139259 _139260 m c q m' P)).
Proof. exact (MK_COMB (@lem7582585 _139258 _139259 _139260 m c q m' P) (@lem7582591 _139258 _139259 _139260 m c q m' P)). Qed.
Lemma lem7582593 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (P : type1517 _139258 _139259 _139260) : (term301 _139258 _139259 _139260 m c q m' P) = (term316 _139258 _139259 _139260 m c q m' P).
Proof. exact (EQ_MP (@lem7582592 _139258 _139259 _139260 m c q m' P) (@lem7582577 _139258 _139259 _139260 m c q m' P)). Qed.
Lemma lem7582594 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (P : type1517 _139258 _139259 _139260) : (term303 _139258 _139259 _139260 m c q P) = (term317 _139258 _139259 _139260 m c q P).
Proof. exact (fun_ext (fun m' : _139259 => @lem7582593 _139258 _139259 _139260 m c q m' P)). Qed.
Lemma lem7582595 {_139259 : Type'} : (@ex _139259) = (@ex _139259).
Proof. exact (eq_refl (@ex _139259)). Qed.
Lemma lem7582596 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (P : type1517 _139258 _139259 _139260) : (term304 _139258 _139259 _139260 m c q P) = (term318 _139258 _139259 _139260 m c q P).
Proof. exact (MK_COMB (@lem7582595 _139259) (@lem7582594 _139258 _139259 _139260 m c q P)). Qed.
Lemma lem7582597 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (P : type1517 _139258 _139259 _139260) : (term287 _139258 _139259 _139260 m c q P) = (term318 _139258 _139259 _139260 m c q P).
Proof. exact (TRANS (@lem7582573 _139258 _139259 _139260 m c q P) (@lem7582596 _139258 _139259 _139260 m c q P)). Qed.
Lemma lem7582598 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) : (term289 _139258 _139259 _139260 m c P) = (term319 _139258 _139259 _139260 m c P).
Proof. exact (fun_ext (fun q : _139260 => @lem7582597 _139258 _139259 _139260 m c q P)). Qed.
Lemma lem7582599 {_139260 : Type'} : (@ex _139260) = (@ex _139260).
Proof. exact (eq_refl (@ex _139260)). Qed.
Lemma lem7582600 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) : (term290 _139258 _139259 _139260 m c P) = (term320 _139258 _139259 _139260 m c P).
Proof. exact (MK_COMB (@lem7582599 _139260) (@lem7582598 _139258 _139259 _139260 m c P)). Qed.
Lemma lem7582601 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) : (term267 _139258 _139259 _139260 m c P) = (term320 _139258 _139259 _139260 m c P).
Proof. exact (TRANS (@lem7582553 _139258 _139259 _139260 m c P) (@lem7582600 _139258 _139259 _139260 m c P)). Qed.
Lemma lem7582602 {_139258 _139259 _139260 : Type'} (m : _139259) (P : type1517 _139258 _139259 _139260) : (term269 _139258 _139259 _139260 m P) = (term321 _139258 _139259 _139260 m P).
Proof. exact (fun_ext (fun c : _139258 => @lem7582601 _139258 _139259 _139260 m c P)). Qed.
Lemma lem7582603 {_139258 : Type'} : (@ex _139258) = (@ex _139258).
Proof. exact (eq_refl (@ex _139258)). Qed.
Lemma lem7582604 {_139258 _139259 _139260 : Type'} (m : _139259) (P : type1517 _139258 _139259 _139260) : (term270 _139258 _139259 _139260 m P) = (term322 _139258 _139259 _139260 m P).
Proof. exact (MK_COMB (@lem7582603 _139258) (@lem7582602 _139258 _139259 _139260 m P)). Qed.
Lemma lem7582605 {_139258 _139259 _139260 : Type'} (m : _139259) (P : type1517 _139258 _139259 _139260) : (term252 _139258 _139259 _139260 m P) = (term322 _139258 _139259 _139260 m P).
Proof. exact (TRANS (@lem7582526 _139258 _139259 _139260 m P) (@lem7582604 _139258 _139259 _139260 m P)). Qed.
Lemma lem7582606 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term254 _139258 _139259 _139260 P) = (term323 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun m : _139259 => @lem7582605 _139258 _139259 _139260 m P)). Qed.
Lemma lem7582607 {_139259 : Type'} : (@ex _139259) = (@ex _139259).
Proof. exact (eq_refl (@ex _139259)). Qed.
Lemma lem7582608 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term255 _139258 _139259 _139260 P) = (term324 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582607 _139259) (@lem7582606 _139258 _139259 _139260 P)). Qed.
Lemma lem7582609 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term238 _139258 _139259 _139260 P) = (term324 _139258 _139259 _139260 P).
Proof. exact (TRANS (@lem7582500 _139258 _139259 _139260 P) (@lem7582608 _139258 _139259 _139260 P)). Qed.
Lemma lem7582611 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term143 _139258 _139259 _139260 P) = (term324 _139258 _139259 _139260 P).
Proof. exact (TRANS (@lem7582474 _139258 _139259 _139260 P) (@lem7582609 _139258 _139259 _139260 P)). Qed.
Lemma lem7582612 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term67 _139258 _139259 _139260 P) = (term324 _139258 _139259 _139260 P).
Proof. exact (TRANS (@lem7582274 _139258 _139259 _139260 P) (@lem7582611 _139258 _139259 _139260 P)). Qed.
Lemma lem7582613 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term67 _139258 _139259 _139260 P) : term324 _139258 _139259 _139260 P.
Proof. exact (EQ_MP (@lem7582612 _139258 _139259 _139260 P) (@lem7582181 _139258 _139259 _139260 P h1)). Qed.
Lemma lem7582614 {_139258 _139259 _139260 : Type'} (m : _139259) (P : type1517 _139258 _139259 _139260) (h1 : term322 _139258 _139259 _139260 m P) : term322 _139258 _139259 _139260 m P.
Proof. exact (h1). Qed.
Lemma lem7582615 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term320 _139258 _139259 _139260 m c P) : term320 _139258 _139259 _139260 m c P.
Proof. exact (h1). Qed.
Lemma lem7582616 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (P : type1517 _139258 _139259 _139260) (h1 : term318 _139258 _139259 _139260 m c q P) : term318 _139258 _139259 _139260 m c q P.
Proof. exact (h1). Qed.
Lemma lem7582617 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (P : type1517 _139258 _139259 _139260) (h1 : term316 _139258 _139259 _139260 m c q m' P) : term316 _139258 _139259 _139260 m c q m' P.
Proof. exact (h1). Qed.
Lemma lem7582618 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term313 _139258 _139259 _139260 m c q m' c' P) : term313 _139258 _139259 _139260 m c q m' c' P.
Proof. exact (h1). Qed.
Lemma lem7582625 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7582626 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term77 _139258 _139259 _139260 P m c) = (term77 _139258 _139259 _139260 P m c).
Proof. exact (fun_ext (fun q : _139260 => @lem7582625 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582627 {_139260 : Type'} : (@all _139260) = (@all _139260).
Proof. exact (eq_refl (@all _139260)). Qed.
Lemma lem7582628 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term78 _139258 _139259 _139260 P m c) = (term78 _139258 _139259 _139260 P m c).
Proof. exact (MK_COMB (@lem7582627 _139260) (@lem7582626 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582629 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term79 _139258 _139259 _139260 P m) = (term79 _139258 _139259 _139260 P m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582628 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582630 {_139258 : Type'} : (@all _139258) = (@all _139258).
Proof. exact (eq_refl (@all _139258)). Qed.
Lemma lem7582631 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term80 _139258 _139259 _139260 P m) = (term80 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582630 _139258) (@lem7582629 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582632 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term81 _139258 _139259 _139260 P) = (term81 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun m : _139259 => @lem7582631 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582633 {_139259 : Type'} : (@all _139259) = (@all _139259).
Proof. exact (eq_refl (@all _139259)). Qed.
Lemma lem7582634 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term65 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582633 _139259) (@lem7582632 _139258 _139259 _139260 P)). Qed.
Lemma lem7582645 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m' : _139259) (c' : _139258) : (term228 _139258 _139259 _139260 P q m' c') = (term228 _139258 _139259 _139260 P q m' c').
Proof. exact (eq_refl (term228 _139258 _139259 _139260 P q m' c')). Qed.
Lemma lem7582646 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) : (term230 _139258 _139259 _139260 q m' c' P) = (term230 _139258 _139259 _139260 q m' c' P).
Proof. exact (MK_COMB (@lem7582645 _139258 _139259 _139260 P q m' c') (@lem7582634 _139258 _139259 _139260 P)). Qed.
Lemma lem7582655 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term94 _139258 _139259 _139260 P q m c) = (term94 _139258 _139259 _139260 P q m c).
Proof. exact (eq_refl (term94 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582662 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7582663 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term82 _139258 _139259 _139260 P q m) = (term82 _139258 _139259 _139260 P q m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582662 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582664 {_139258 : Type'} : (@all _139258) = (@all _139258).
Proof. exact (eq_refl (@all _139258)). Qed.
Lemma lem7582665 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term83 _139258 _139259 _139260 P q m) = (term83 _139258 _139259 _139260 P q m).
Proof. exact (MK_COMB (@lem7582664 _139258) (@lem7582663 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582666 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term84 _139258 _139259 _139260 P q) = (term84 _139258 _139259 _139260 P q).
Proof. exact (fun_ext (fun m : _139259 => @lem7582665 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582667 {_139259 : Type'} : (@all _139259) = (@all _139259).
Proof. exact (eq_refl (@all _139259)). Qed.
Lemma lem7582668 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term85 _139258 _139259 _139260 P q) = (term85 _139258 _139259 _139260 P q).
Proof. exact (MK_COMB (@lem7582667 _139259) (@lem7582666 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582669 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term86 _139258 _139259 _139260 P) = (term86 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun q : _139260 => @lem7582668 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582670 {_139260 : Type'} : (@all _139260) = (@all _139260).
Proof. exact (eq_refl (@all _139260)). Qed.
Lemma lem7582671 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term64 _139258 _139259 _139260 P) = (term64 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582670 _139260) (@lem7582669 _139258 _139259 _139260 P)). Qed.
Lemma lem7582672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7582673 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term137 _139258 _139259 _139260 P) = (term137 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582672) (@lem7582671 _139258 _139259 _139260 P)). Qed.
Lemma lem7582674 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term178 _139258 _139259 _139260 P q m c) = (term178 _139258 _139259 _139260 P q m c).
Proof. exact (MK_COMB (@lem7582673 _139258 _139259 _139260 P) (@lem7582655 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582675 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7582676 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term285 _139258 _139259 _139260 P q m c) = (term285 _139258 _139259 _139260 P q m c).
Proof. exact (MK_COMB (@lem7582675) (@lem7582674 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582677 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) : (term313 _139258 _139259 _139260 m c q m' c' P) = (term313 _139258 _139259 _139260 m c q m' c' P).
Proof. exact (MK_COMB (@lem7582676 _139258 _139259 _139260 P q m c) (@lem7582646 _139258 _139259 _139260 q m' c' P)). Qed.
Lemma lem7582678 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term313 _139258 _139259 _139260 m c q m' c' P) : term313 _139258 _139259 _139260 m c q m' c' P.
Proof. exact (EQ_MP (@lem7582677 _139258 _139259 _139260 m c q m' c' P) (@lem7582618 _139258 _139259 _139260 m c q m' c' P h1)). Qed.
Lemma lem7582679 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : term178 _139258 _139259 _139260 P q m c.
Proof. exact (h1). Qed.
Lemma lem7582680 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : term230 _139258 _139259 _139260 q m' c' P.
Proof. exact (h1). Qed.
Lemma lem7582682 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : term64 _139258 _139259 _139260 P.
Proof. exact (proj1 (@lem7582679 _139258 _139259 _139260 P q m c h1)). Qed.
Lemma lem7582683 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : term65 _139258 _139259 _139260 P.
Proof. exact (proj2 (@lem7582680 _139258 _139259 _139260 q m' c' P h1)). Qed.
Lemma lem7582686 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7582687 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term82 _139258 _139259 _139260 P q m) = (term82 _139258 _139259 _139260 P q m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582686 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582688 {_139258 : Type'} : (@all _139258) = (@all _139258).
Proof. exact (eq_refl (@all _139258)). Qed.
Lemma lem7582689 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) : (term83 _139258 _139259 _139260 P q m) = (term83 _139258 _139259 _139260 P q m).
Proof. exact (MK_COMB (@lem7582688 _139258) (@lem7582687 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582690 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term84 _139258 _139259 _139260 P q) = (term84 _139258 _139259 _139260 P q).
Proof. exact (fun_ext (fun m : _139259 => @lem7582689 _139258 _139259 _139260 P q m)). Qed.
Lemma lem7582691 {_139259 : Type'} : (@all _139259) = (@all _139259).
Proof. exact (eq_refl (@all _139259)). Qed.
Lemma lem7582692 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) : (term85 _139258 _139259 _139260 P q) = (term85 _139258 _139259 _139260 P q).
Proof. exact (MK_COMB (@lem7582691 _139259) (@lem7582690 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582693 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term86 _139258 _139259 _139260 P) = (term86 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun q : _139260 => @lem7582692 _139258 _139259 _139260 P q)). Qed.
Lemma lem7582694 {_139260 : Type'} : (@all _139260) = (@all _139260).
Proof. exact (eq_refl (@all _139260)). Qed.
Lemma lem7582696 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term64 _139258 _139259 _139260 P) = (term64 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582694 _139260) (@lem7582693 _139258 _139259 _139260 P)). Qed.
Lemma lem7582697 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : term64 _139258 _139259 _139260 P.
Proof. exact (EQ_MP (@lem7582696 _139258 _139259 _139260 P) (@lem7582682 _139258 _139259 _139260 P q m c h1)). Qed.
Lemma lem7582707 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7582708 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term77 _139258 _139259 _139260 P m c) = (term77 _139258 _139259 _139260 P m c).
Proof. exact (fun_ext (fun q : _139260 => @lem7582707 _139258 _139259 _139260 P q m c)). Qed.
Lemma lem7582709 {_139260 : Type'} : (@all _139260) = (@all _139260).
Proof. exact (eq_refl (@all _139260)). Qed.
Lemma lem7582710 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) (c : _139258) : (term78 _139258 _139259 _139260 P m c) = (term78 _139258 _139259 _139260 P m c).
Proof. exact (MK_COMB (@lem7582709 _139260) (@lem7582708 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582711 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term79 _139258 _139259 _139260 P m) = (term79 _139258 _139259 _139260 P m).
Proof. exact (fun_ext (fun c : _139258 => @lem7582710 _139258 _139259 _139260 P m c)). Qed.
Lemma lem7582712 {_139258 : Type'} : (@all _139258) = (@all _139258).
Proof. exact (eq_refl (@all _139258)). Qed.
Lemma lem7582713 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (m : _139259) : (term80 _139258 _139259 _139260 P m) = (term80 _139258 _139259 _139260 P m).
Proof. exact (MK_COMB (@lem7582712 _139258) (@lem7582711 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582714 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term81 _139258 _139259 _139260 P) = (term81 _139258 _139259 _139260 P).
Proof. exact (fun_ext (fun m : _139259 => @lem7582713 _139258 _139259 _139260 P m)). Qed.
Lemma lem7582715 {_139259 : Type'} : (@all _139259) = (@all _139259).
Proof. exact (eq_refl (@all _139259)). Qed.
Lemma lem7582717 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term65 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P).
Proof. exact (MK_COMB (@lem7582715 _139259) (@lem7582714 _139258 _139259 _139260 P)). Qed.
Lemma lem7582718 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : term65 _139258 _139259 _139260 P.
Proof. exact (EQ_MP (@lem7582717 _139258 _139259 _139260 P) (@lem7582683 _139258 _139259 _139260 q m' c' P h1)). Qed.
Lemma lem7582719 {_139258 _139259 _139260 : Type'} (_97585 : _139260) (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : term107 _139258 _139259 _139260 P _97585.
Proof. exact (@lem7582697 _139258 _139259 _139260 P q m c h1 _97585). Qed.
Lemma lem7582720 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (_97585 : _139260) : (term107 _139258 _139259 _139260 P _97585) = (term85 _139258 _139259 _139260 P _97585).
Proof. exact (eq_refl (term107 _139258 _139259 _139260 P _97585)). Qed.
Lemma lem7582721 {_139258 _139259 _139260 : Type'} (_97585 : _139260) (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : term85 _139258 _139259 _139260 P _97585.
Proof. exact (EQ_MP (@lem7582720 _139258 _139259 _139260 P _97585) (@lem7582719 _139258 _139259 _139260 _97585 P q m c h1)). Qed.
Lemma lem7582722 {_139258 _139259 _139260 : Type'} (_97585 : _139260) (_97586 : _139259) (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : term100 _139258 _139259 _139260 P _97585 _97586.
Proof. exact (@lem7582721 _139258 _139259 _139260 _97585 P q m c h1 _97586). Qed.
Lemma lem7582723 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (_97585 : _139260) (_97586 : _139259) : (term100 _139258 _139259 _139260 P _97585 _97586) = (term83 _139258 _139259 _139260 P _97585 _97586).
Proof. exact (eq_refl (term100 _139258 _139259 _139260 P _97585 _97586)). Qed.
Lemma lem7582724 {_139258 _139259 _139260 : Type'} (_97585 : _139260) (_97586 : _139259) (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : term83 _139258 _139259 _139260 P _97585 _97586.
Proof. exact (EQ_MP (@lem7582723 _139258 _139259 _139260 P _97585 _97586) (@lem7582722 _139258 _139259 _139260 _97585 _97586 P q m c h1)). Qed.
Lemma lem7582725 {_139258 _139259 _139260 : Type'} (_97585 : _139260) (_97586 : _139259) (_97587 : _139258) (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : term92 _139258 _139259 _139260 P _97585 _97586 _97587.
Proof. exact (@lem7582724 _139258 _139259 _139260 _97585 _97586 P q m c h1 _97587). Qed.
Lemma lem7582726 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (_97585 : _139260) (_97586 : _139259) (_97587 : _139258) : (term92 _139258 _139259 _139260 P _97585 _97586 _97587) = (P _97585 _97586 _97587).
Proof. exact (eq_refl (term92 _139258 _139259 _139260 P _97585 _97586 _97587)). Qed.
Lemma lem7582728 {_139258 _139259 _139260 : Type'} (_97588 : _139259) (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : term128 _139258 _139259 _139260 P _97588.
Proof. exact (@lem7582718 _139258 _139259 _139260 q m' c' P h1 _97588). Qed.
Lemma lem7582729 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (_97588 : _139259) : (term128 _139258 _139259 _139260 P _97588) = (term80 _139258 _139259 _139260 P _97588).
Proof. exact (eq_refl (term128 _139258 _139259 _139260 P _97588)). Qed.
Lemma lem7582730 {_139258 _139259 _139260 : Type'} (_97588 : _139259) (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : term80 _139258 _139259 _139260 P _97588.
Proof. exact (EQ_MP (@lem7582729 _139258 _139259 _139260 P _97588) (@lem7582728 _139258 _139259 _139260 _97588 q m' c' P h1)). Qed.
Lemma lem7582731 {_139258 _139259 _139260 : Type'} (_97588 : _139259) (_97589 : _139258) (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : term121 _139258 _139259 _139260 P _97588 _97589.
Proof. exact (@lem7582730 _139258 _139259 _139260 _97588 q m' c' P h1 _97589). Qed.
Lemma lem7582732 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (_97588 : _139259) (_97589 : _139258) : (term121 _139258 _139259 _139260 P _97588 _97589) = (term78 _139258 _139259 _139260 P _97588 _97589).
Proof. exact (eq_refl (term121 _139258 _139259 _139260 P _97588 _97589)). Qed.
Lemma lem7582733 {_139258 _139259 _139260 : Type'} (_97588 : _139259) (_97589 : _139258) (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : term78 _139258 _139259 _139260 P _97588 _97589.
Proof. exact (EQ_MP (@lem7582732 _139258 _139259 _139260 P _97588 _97589) (@lem7582731 _139258 _139259 _139260 _97588 _97589 q m' c' P h1)). Qed.
Lemma lem7582734 {_139258 _139259 _139260 : Type'} (_97588 : _139259) (_97589 : _139258) (_97590 : _139260) (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : term114 _139258 _139259 _139260 P _97588 _97589 _97590.
Proof. exact (@lem7582733 _139258 _139259 _139260 _97588 _97589 q m' c' P h1 _97590). Qed.
Lemma lem7582735 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (_97590 : _139260) (_97588 : _139259) (_97589 : _139258) : (term114 _139258 _139259 _139260 P _97588 _97589 _97590) = (P _97590 _97588 _97589).
Proof. exact (eq_refl (term114 _139258 _139259 _139260 P _97588 _97589 _97590)). Qed.
Lemma lem7582740 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : term94 _139258 _139259 _139260 P q m c.
Proof. exact (proj2 (@lem7582679 _139258 _139259 _139260 P q m c h1)). Qed.
Lemma lem7582742 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : term94 _139258 _139259 _139260 P q m' c'.
Proof. exact (proj1 (@lem7582680 _139258 _139259 _139260 q m' c' P h1)). Qed.
Lemma lem7582746 {_139258 _139259 _139260 : Type'} (_97585 : _139260) (_97586 : _139259) (_97587 : _139258) (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : P _97585 _97586 _97587.
Proof. exact (EQ_MP (@lem7582726 _139258 _139259 _139260 P _97585 _97586 _97587) (@lem7582725 _139258 _139259 _139260 _97585 _97586 _97587 P q m c h1)). Qed.
Lemma lem7582747 {_139258 _139259 _139260 : Type'} (_97585 : _139260) (_97586 : _139259) (_97587 : _139258) (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : P _97585 _97586 _97587.
Proof. exact (@lem7582746 _139258 _139259 _139260 _97585 _97586 _97587 P q m c h1). Qed.
Lemma lem7582748 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : P q m c.
Proof. exact (@lem7582747 _139258 _139259 _139260 q m c P q m c h1). Qed.
Lemma lem7582749 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : term325 _139258 _139259 _139260 P q m c.
Proof. exact (fun h0 : term94 _139258 _139259 _139260 P q m c => @lem7582748 _139258 _139259 _139260 P q m c h1). Qed.
Lemma lem7582751 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7582752 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term325 _139258 _139259 _139260 P q m c) = (P q m c).
Proof. exact (@lem7582751 (P q m c)). Qed.
Lemma lem7582753 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : P q m c.
Proof. exact (EQ_MP (@lem7582752 _139258 _139259 _139260 P q m c) (@lem7582749 _139258 _139259 _139260 P q m c h1)). Qed.
Lemma lem7582756 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7582758 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) : (term94 _139258 _139259 _139260 P q m c) = (term327 _139258 _139259 _139260 P q m c).
Proof. exact (@lem7582756 (P q m c)). Qed.
Lemma lem7582761 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : term327 _139258 _139259 _139260 P q m c.
Proof. exact (EQ_MP (@lem7582758 _139258 _139259 _139260 P q m c) (@lem7582740 _139258 _139259 _139260 P q m c h1)). Qed.
Lemma lem7582764 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : False.
Proof. exact (@lem7582761 _139258 _139259 _139260 P q m c h1 (@lem7582753 _139258 _139259 _139260 P q m c h1)). Qed.
Lemma lem7582765 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : term328.
Proof. exact (fun h0 : ~ False => @lem7582764 _139258 _139259 _139260 P q m c h1). Qed.
Lemma lem7582767 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7582768 : term328 = False.
Proof. exact (@lem7582767 False). Qed.
Lemma lem7582769 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m : _139259) (c : _139258) (h1 : term178 _139258 _139259 _139260 P q m c) : False.
Proof. exact (EQ_MP (@lem7582768) (@lem7582765 _139258 _139259 _139260 P q m c h1)). Qed.
Lemma lem7582771 {_139258 _139259 _139260 : Type'} (_97590 : _139260) (_97588 : _139259) (_97589 : _139258) (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : P _97590 _97588 _97589.
Proof. exact (EQ_MP (@lem7582735 _139258 _139259 _139260 P _97590 _97588 _97589) (@lem7582734 _139258 _139259 _139260 _97588 _97589 _97590 q m' c' P h1)). Qed.
Lemma lem7582772 {_139258 _139259 _139260 : Type'} (_97590 : _139260) (_97588 : _139259) (_97589 : _139258) (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : P _97590 _97588 _97589.
Proof. exact (@lem7582771 _139258 _139259 _139260 _97590 _97588 _97589 q m' c' P h1). Qed.
Lemma lem7582773 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : P q m' c'.
Proof. exact (@lem7582772 _139258 _139259 _139260 q m' c' q m' c' P h1). Qed.
Lemma lem7582774 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : term325 _139258 _139259 _139260 P q m' c'.
Proof. exact (fun h0 : term94 _139258 _139259 _139260 P q m' c' => @lem7582773 _139258 _139259 _139260 q m' c' P h1). Qed.
Lemma lem7582776 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7582777 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m' : _139259) (c' : _139258) : (term325 _139258 _139259 _139260 P q m' c') = (P q m' c').
Proof. exact (@lem7582776 (P q m' c')). Qed.
Lemma lem7582778 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : P q m' c'.
Proof. exact (EQ_MP (@lem7582777 _139258 _139259 _139260 P q m' c') (@lem7582774 _139258 _139259 _139260 q m' c' P h1)). Qed.
Lemma lem7582781 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7582783 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (q : _139260) (m' : _139259) (c' : _139258) : (term94 _139258 _139259 _139260 P q m' c') = (term327 _139258 _139259 _139260 P q m' c').
Proof. exact (@lem7582781 (P q m' c')). Qed.
Lemma lem7582786 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : term327 _139258 _139259 _139260 P q m' c'.
Proof. exact (EQ_MP (@lem7582783 _139258 _139259 _139260 P q m' c') (@lem7582742 _139258 _139259 _139260 q m' c' P h1)). Qed.
Lemma lem7582789 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : False.
Proof. exact (@lem7582786 _139258 _139259 _139260 q m' c' P h1 (@lem7582778 _139258 _139259 _139260 q m' c' P h1)). Qed.
Lemma lem7582790 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : term328.
Proof. exact (fun h0 : ~ False => @lem7582789 _139258 _139259 _139260 q m' c' P h1). Qed.
Lemma lem7582792 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7582793 : term328 = False.
Proof. exact (@lem7582792 False). Qed.
Lemma lem7582794 {_139258 _139259 _139260 : Type'} (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term230 _139258 _139259 _139260 q m' c' P) : False.
Proof. exact (EQ_MP (@lem7582793) (@lem7582790 _139258 _139259 _139260 q m' c' P h1)). Qed.
Lemma lem7582795 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term313 _139258 _139259 _139260 m c q m' c' P) : False.
Proof. exact (or_elim (@lem7582678 _139258 _139259 _139260 m c q m' c' P h1) (fun h0 : term178 _139258 _139259 _139260 P q m c => @lem7582769 _139258 _139259 _139260 P q m c h0) (fun h0 : term230 _139258 _139259 _139260 q m' c' P => @lem7582794 _139258 _139259 _139260 q m' c' P h0)). Qed.
Lemma lem7582796 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term313 _139258 _139259 _139260 m c q m' c' P) : (term313 _139258 _139259 _139260 m c q m' c' P) = False.
Proof. exact (prop_ext (fun h2 : term313 _139258 _139259 _139260 m c q m' c' P => @lem7582795 _139258 _139259 _139260 m c q m' c' P h1) (fun h2 : False => @lem7582678 _139258 _139259 _139260 m c q m' c' P h1)). Qed.
Lemma lem7582797 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (c' : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term313 _139258 _139259 _139260 m c q m' c' P) : False.
Proof. exact (EQ_MP (@lem7582796 _139258 _139259 _139260 m c q m' c' P h1) (@lem7582678 _139258 _139259 _139260 m c q m' c' P h1)). Qed.
Lemma lem7582798 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (m' : _139259) (P : type1517 _139258 _139259 _139260) (h1 : term316 _139258 _139259 _139260 m c q m' P) : False.
Proof. exact (ex_elim (@lem7582617 _139258 _139259 _139260 m c q m' P h1) (fun c' : _139258 => fun h0 : term315 _139258 _139259 _139260 m c q m' P c' => @lem7582797 _139258 _139259 _139260 m c q m' c' P h0)). Qed.
Lemma lem7582799 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (q : _139260) (P : type1517 _139258 _139259 _139260) (h1 : term318 _139258 _139259 _139260 m c q P) : False.
Proof. exact (ex_elim (@lem7582616 _139258 _139259 _139260 m c q P h1) (fun m' : _139259 => fun h0 : term317 _139258 _139259 _139260 m c q P m' => @lem7582798 _139258 _139259 _139260 m c q m' P h0)). Qed.
Lemma lem7582800 {_139258 _139259 _139260 : Type'} (m : _139259) (c : _139258) (P : type1517 _139258 _139259 _139260) (h1 : term320 _139258 _139259 _139260 m c P) : False.
Proof. exact (ex_elim (@lem7582615 _139258 _139259 _139260 m c P h1) (fun q : _139260 => fun h0 : term319 _139258 _139259 _139260 m c P q => @lem7582799 _139258 _139259 _139260 m c q P h0)). Qed.
Lemma lem7582801 {_139258 _139259 _139260 : Type'} (m : _139259) (P : type1517 _139258 _139259 _139260) (h1 : term322 _139258 _139259 _139260 m P) : False.
Proof. exact (ex_elim (@lem7582614 _139258 _139259 _139260 m P h1) (fun c : _139258 => fun h0 : term321 _139258 _139259 _139260 m P c => @lem7582800 _139258 _139259 _139260 m c P h0)). Qed.
Lemma lem7582802 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term67 _139258 _139259 _139260 P) : False.
Proof. exact (ex_elim (@lem7582613 _139258 _139259 _139260 P h1) (fun m : _139259 => fun h0 : term323 _139258 _139259 _139260 P m => @lem7582801 _139258 _139259 _139260 m P h0)). Qed.
Lemma lem7582803 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term67 _139258 _139259 _139260 P) : (term67 _139258 _139259 _139260 P) = False.
Proof. exact (prop_ext (fun h2 : term67 _139258 _139259 _139260 P => @lem7582802 _139258 _139259 _139260 P h1) (fun h2 : False => @lem7582181 _139258 _139259 _139260 P h1)). Qed.
Lemma lem7582804 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term67 _139258 _139259 _139260 P) : False.
Proof. exact (EQ_MP (@lem7582803 _139258 _139259 _139260 P h1) (@lem7582181 _139258 _139259 _139260 P h1)). Qed.
Lemma lem7582805 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : term66 _139258 _139259 _139260 P.
Proof. exact (fun h0 : term67 _139258 _139259 _139260 P => @lem7582804 _139258 _139259 _139260 P h0). Qed.
Lemma lem7582806 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term64 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P).
Proof. exact (EQ_MP (@lem7582180 _139258 _139259 _139260 P) (@lem7582805 _139258 _139259 _139260 P)). Qed.
Lemma lem7582811 {_139258 _139259 _139260 : Type'} : term76 _139258 _139259 _139260.
Proof. exact (fun P : type1517 _139258 _139259 _139260 => @lem7582806 _139258 _139259 _139260 P). Qed.
Lemma lem7582812 {_139258 _139259 _139260 : Type'} : term75 _139258 _139259 _139260.
Proof. exact (EQ_MP (@lem7582176 _139258 _139259 _139260) (@lem7582811 _139258 _139259 _139260)). Qed.
Lemma lem7582813 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : term329 _139258 _139259 _139260 P.
Proof. exact (@lem7582812 _139258 _139259 _139260 P). Qed.
Lemma lem7582814 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term329 _139258 _139259 _139260 P) = (term66 _139258 _139259 _139260 P).
Proof. exact (eq_refl (term329 _139258 _139259 _139260 P)). Qed.
Lemma lem7582815 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : term66 _139258 _139259 _139260 P.
Proof. exact (EQ_MP (@lem7582814 _139258 _139259 _139260 P) (@lem7582813 _139258 _139259 _139260 P)). Qed.
Lemma lem7582817 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : term66 _139258 _139259 _139260 P.
Proof. exact (@lem7582058 _139258 _139259 _139260 P (@lem7582815 _139258 _139259 _139260 P)). Qed.
Lemma lem7582818 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term67 _139258 _139259 _139260 P) : False.
Proof. exact (@lem7582817 _139258 _139259 _139260 P (@lem7582042 _139258 _139259 _139260 P h1)). Qed.
Lemma lem7582819 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term67 _139258 _139259 _139260 P) : (term67 _139258 _139259 _139260 P) = False.
Proof. exact (prop_ext (fun h2 : term67 _139258 _139259 _139260 P => @lem7582818 _139258 _139259 _139260 P h1) (fun h2 : False => @lem7582042 _139258 _139259 _139260 P h1)). Qed.
Lemma lem7582820 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) (h1 : term67 _139258 _139259 _139260 P) : False.
Proof. exact (EQ_MP (@lem7582819 _139258 _139259 _139260 P h1) (@lem7582042 _139258 _139259 _139260 P h1)). Qed.
Lemma lem7582821 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : term66 _139258 _139259 _139260 P.
Proof. exact (fun h0 : term67 _139258 _139259 _139260 P => @lem7582820 _139258 _139259 _139260 P h0). Qed.
Lemma lem7582823 {A : Type'} (P : A -> Prop) : term330 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem7582824 {A : Type'} (P : A -> Prop) : (term330 A P) = (term331 A P).
Proof. exact (eq_refl (term330 A P)). Qed.
Lemma lem7582825 {A : Type'} (P : A -> Prop) : term331 A P.
Proof. exact (EQ_MP (@lem7582824 A P) (@lem7582823 A P)). Qed.
Lemma lem7582826 {A : Type'} (P : A -> Prop) (Q : Prop) : term332 A P Q.
Proof. exact (@lem7582825 A P Q). Qed.
Lemma lem7582827 {A : Type'} (P : A -> Prop) (Q : Prop) : (term332 A P Q) = ((term51 A P Q) = (term50 A P Q)).
Proof. exact (eq_refl (term332 A P Q)). Qed.
Lemma lem7582829 (p : real -> real) : term333 p.
Proof. exact (@lem7553488 p). Qed.
Lemma lem7582830 (p : real -> real) : (term333 p) = ((polynomial_function p) = (term334 p)).
Proof. exact (eq_refl (term333 p)). Qed.
Lemma lem7582832 (P : type1028) (h1 : term335 P) : term335 P.
Proof. exact (h1). Qed.
Lemma lem7582833 (P : type1028) (h1 : term336 P) : term336 P.
Proof. exact (h1). Qed.
Lemma lem7582834 (P : type1028) (h1 : term337 P) : term337 P.
Proof. exact (h1). Qed.
Lemma lem7582835 (P : type1028) (h1 : term338 P) : term338 P.
Proof. exact (h1). Qed.
Lemma lem7582836 (P : type1028) (h1 : term339 P) : term339 P.
Proof. exact (h1). Qed.
Lemma lem7582837 (P : type1028) (h1 : term340 P) : term340 P.
Proof. exact (h1). Qed.
Lemma lem7582838 (P : type1028) (h1 : term341 P) : term341 P.
Proof. exact (h1). Qed.
Lemma lem7582846 (p : real -> real) : (polynomial_function p) = (term334 p).
Proof. exact (EQ_MP (@lem7582830 p) (@lem7582829 p)). Qed.
Lemma lem7582861 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7582862 (p : real -> real) : (term342 p) = (term343 p).
Proof. exact (MK_COMB (@lem7582861) (@lem7582846 p)). Qed.
Lemma lem7582863 (P : type1028) (p : real -> real) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem7582864 (P : type1028) (p : real -> real) : (term344 P p) = (term345 P p).
Proof. exact (MK_COMB (@lem7582862 p) (@lem7582863 P p)). Qed.
Lemma lem7582866 {A : Type'} (P : A -> Prop) (Q : Prop) : (term51 A P Q) = (term50 A P Q).
Proof. exact (EQ_MP (@lem7582827 A P Q) (@lem7582826 A P Q)). Qed.
Lemma lem7582867 (P : nat -> Prop) (Q : Prop) : (term346 P Q) = (term347 P Q).
Proof. exact (@lem7582866 nat P Q). Qed.
Lemma lem7582868 (P : type1028) (p : real -> real) : (term348 P p) = (term349 P p).
Proof. exact (@lem7582867 (term350 p) (P p)). Qed.
Lemma lem7582869 (p : real -> real) (m : nat) : (term351 p m) = (term352 p m).
Proof. exact (eq_refl (term351 p m)). Qed.
Lemma lem7582870 (p : real -> real) : (term353 p) = (term350 p).
Proof. exact (fun_ext (fun m : nat => @lem7582869 p m)). Qed.
Lemma lem7582871 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7582872 (p : real -> real) : (term354 p) = (term334 p).
Proof. exact (MK_COMB (@lem7582871) (@lem7582870 p)). Qed.
Lemma lem7582873 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7582874 (p : real -> real) : (term355 p) = (term343 p).
Proof. exact (MK_COMB (@lem7582873) (@lem7582872 p)). Qed.
Lemma lem7582875 (P : type1028) (p : real -> real) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem7582876 (P : type1028) (p : real -> real) : (term348 P p) = (term345 P p).
Proof. exact (MK_COMB (@lem7582874 p) (@lem7582875 P p)). Qed.
Lemma lem7582877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582878 (P : type1028) (p : real -> real) : (term356 P p) = (term357 P p).
Proof. exact (MK_COMB (@lem7582877) (@lem7582876 P p)). Qed.
Lemma lem7582879 (p : real -> real) (m : nat) : (term351 p m) = (term352 p m).
Proof. exact (eq_refl (term351 p m)). Qed.
Lemma lem7582880 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7582881 (p : real -> real) (m : nat) : (term358 p m) = (term359 p m).
Proof. exact (MK_COMB (@lem7582880) (@lem7582879 p m)). Qed.
Lemma lem7582882 (P : type1028) (p : real -> real) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem7582883 (m : nat) (P : type1028) (p : real -> real) : (term360 m P p) = (term361 m P p).
Proof. exact (MK_COMB (@lem7582881 p m) (@lem7582882 P p)). Qed.
Lemma lem7582884 (P : type1028) (p : real -> real) : (term362 P p) = (term363 P p).
Proof. exact (fun_ext (fun m : nat => @lem7582883 m P p)). Qed.
Lemma lem7582885 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7582886 (P : type1028) (p : real -> real) : (term349 P p) = (term364 P p).
Proof. exact (MK_COMB (@lem7582885) (@lem7582884 P p)). Qed.
Lemma lem7582887 (P : type1028) (p : real -> real) : ((term348 P p) = (term349 P p)) = ((term345 P p) = (term364 P p)).
Proof. exact (MK_COMB (@lem7582878 P p) (@lem7582886 P p)). Qed.
Lemma lem7582888 (P : type1028) (p : real -> real) : (term345 P p) = (term364 P p).
Proof. exact (EQ_MP (@lem7582887 P p) (@lem7582868 P p)). Qed.
Lemma lem7582894 {A : Type'} (P : A -> Prop) (Q : Prop) : (term51 A P Q) = (term50 A P Q).
Proof. exact (EQ_MP (@lem7582827 A P Q) (@lem7582826 A P Q)). Qed.
Lemma lem7582895 (P : type1010) (Q : Prop) : (term365 P Q) = (term366 P Q).
Proof. exact (@lem7582894 (nat -> real) P Q). Qed.
Lemma lem7582896 (m : nat) (P : type1028) (p : real -> real) : (term367 m P p) = (term368 m P p).
Proof. exact (@lem7582895 (term369 p m) (P p)). Qed.
Lemma lem7582897 (p : real -> real) (m : nat) (c : nat -> real) : (term370 p m c) = (term371 p m c).
Proof. exact (eq_refl (term370 p m c)). Qed.
Lemma lem7582898 (p : real -> real) (m : nat) : (term372 p m) = (term369 p m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7582897 p m c)). Qed.
Lemma lem7582899 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7582900 (p : real -> real) (m : nat) : (term373 p m) = (term352 p m).
Proof. exact (MK_COMB (@lem7582899) (@lem7582898 p m)). Qed.
Lemma lem7582901 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7582902 (p : real -> real) (m : nat) : (term374 p m) = (term359 p m).
Proof. exact (MK_COMB (@lem7582901) (@lem7582900 p m)). Qed.
Lemma lem7582903 (P : type1028) (p : real -> real) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem7582904 (m : nat) (P : type1028) (p : real -> real) : (term367 m P p) = (term361 m P p).
Proof. exact (MK_COMB (@lem7582902 p m) (@lem7582903 P p)). Qed.
Lemma lem7582905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582906 (m : nat) (P : type1028) (p : real -> real) : (term375 m P p) = (term376 m P p).
Proof. exact (MK_COMB (@lem7582905) (@lem7582904 m P p)). Qed.
Lemma lem7582907 (p : real -> real) (m : nat) (c : nat -> real) : (term370 p m c) = (term371 p m c).
Proof. exact (eq_refl (term370 p m c)). Qed.
Lemma lem7582908 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7582909 (p : real -> real) (m : nat) (c : nat -> real) : (term377 p m c) = (term378 p m c).
Proof. exact (MK_COMB (@lem7582908) (@lem7582907 p m c)). Qed.
Lemma lem7582910 (P : type1028) (p : real -> real) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem7582911 (m : nat) (c : nat -> real) (P : type1028) (p : real -> real) : (term379 m c P p) = (term380 m c P p).
Proof. exact (MK_COMB (@lem7582909 p m c) (@lem7582910 P p)). Qed.
Lemma lem7582912 (m : nat) (P : type1028) (p : real -> real) : (term381 m P p) = (term382 m P p).
Proof. exact (fun_ext (fun c : nat -> real => @lem7582911 m c P p)). Qed.
Lemma lem7582913 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7582914 (m : nat) (P : type1028) (p : real -> real) : (term368 m P p) = (term383 m P p).
Proof. exact (MK_COMB (@lem7582913) (@lem7582912 m P p)). Qed.
Lemma lem7582915 (m : nat) (P : type1028) (p : real -> real) : ((term367 m P p) = (term368 m P p)) = ((term361 m P p) = (term383 m P p)).
Proof. exact (MK_COMB (@lem7582906 m P p) (@lem7582914 m P p)). Qed.
Lemma lem7582916 (m : nat) (P : type1028) (p : real -> real) : (term361 m P p) = (term383 m P p).
Proof. exact (EQ_MP (@lem7582915 m P p) (@lem7582896 m P p)). Qed.
Lemma lem7582929 (P : type1028) (p : real -> real) : (term363 P p) = (term384 P p).
Proof. exact (fun_ext (fun m : nat => @lem7582916 m P p)). Qed.
Lemma lem7582930 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7582931 (P : type1028) (p : real -> real) : (term364 P p) = (term385 P p).
Proof. exact (MK_COMB (@lem7582930) (@lem7582929 P p)). Qed.
Lemma lem7582936 (P : type1028) (p : real -> real) : (term345 P p) = (term385 P p).
Proof. exact (TRANS (@lem7582888 P p) (@lem7582931 P p)). Qed.
Lemma lem7582937 (P : type1028) (p : real -> real) : (term344 P p) = (term385 P p).
Proof. exact (TRANS (@lem7582864 P p) (@lem7582936 P p)). Qed.
Lemma lem7582938 (P : type1028) : (term386 P) = (term387 P).
Proof. exact (fun_ext (fun p : real -> real => @lem7582937 P p)). Qed.
Lemma lem7582939 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7582940 (P : type1028) : (term388 P) = (term389 P).
Proof. exact (MK_COMB (@lem7582939) (@lem7582938 P)). Qed.
Lemma lem7582945 (P : type1028) : (term389 P) = (term388 P).
Proof. exact (SYM (@lem7582940 P)). Qed.
Lemma lem7582947 {_139258 _139259 _139260 : Type'} (P : type1517 _139258 _139259 _139260) : (term64 _139258 _139259 _139260 P) = (term65 _139258 _139259 _139260 P).
Proof. exact (EQ_MP (@lem7582041 _139258 _139259 _139260 P) (@lem7582821 _139258 _139259 _139260 P)). Qed.
Lemma lem7582948 (P : type1026) : (term390 P) = (term391 P).
Proof. exact (@lem7582947 (nat -> real) nat (real -> real) P). Qed.
Lemma lem7582949 (P : type1028) : (term392 P) = (term393 P).
Proof. exact (@lem7582948 (term394 P)). Qed.
Lemma lem7582950 (P : type1028) (p : real -> real) : (term395 P p) = (term396 P p).
Proof. exact (eq_refl (term395 P p)). Qed.
Lemma lem7582951 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7582952 (P : type1028) (p : real -> real) (m : nat) : (term397 P p m) = (term398 P p m).
Proof. exact (MK_COMB (@lem7582950 P p) (@lem7582951 m)). Qed.
Lemma lem7582953 (m : nat) (P : type1028) (p : real -> real) : (term398 P p m) = (term382 m P p).
Proof. exact (eq_refl (term398 P p m)). Qed.
Lemma lem7582954 (m : nat) (P : type1028) (p : real -> real) : (term397 P p m) = (term382 m P p).
Proof. exact (TRANS (@lem7582952 P p m) (@lem7582953 m P p)). Qed.
Lemma lem7582955 (c : nat -> real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem7582956 (m : nat) (P : type1028) (p : real -> real) (c : nat -> real) : (term399 P p m c) = (term400 m P p c).
Proof. exact (MK_COMB (@lem7582954 m P p) (@lem7582955 c)). Qed.
Lemma lem7582957 (m : nat) (c : nat -> real) (P : type1028) (p : real -> real) : (term400 m P p c) = (term380 m c P p).
Proof. exact (eq_refl (term400 m P p c)). Qed.
Lemma lem7582958 (m : nat) (c : nat -> real) (P : type1028) (p : real -> real) : (term399 P p m c) = (term380 m c P p).
Proof. exact (TRANS (@lem7582956 m P p c) (@lem7582957 m c P p)). Qed.
Lemma lem7582959 (m : nat) (P : type1028) (p : real -> real) : (term401 P p m) = (term382 m P p).
Proof. exact (fun_ext (fun c : nat -> real => @lem7582958 m c P p)). Qed.
Lemma lem7582960 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7582961 (m : nat) (P : type1028) (p : real -> real) : (term402 P p m) = (term383 m P p).
Proof. exact (MK_COMB (@lem7582960) (@lem7582959 m P p)). Qed.
Lemma lem7582962 (P : type1028) (p : real -> real) : (term403 P p) = (term384 P p).
Proof. exact (fun_ext (fun m : nat => @lem7582961 m P p)). Qed.
Lemma lem7582963 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7582964 (P : type1028) (p : real -> real) : (term404 P p) = (term385 P p).
Proof. exact (MK_COMB (@lem7582963) (@lem7582962 P p)). Qed.
Lemma lem7582965 (P : type1028) : (term405 P) = (term387 P).
Proof. exact (fun_ext (fun p : real -> real => @lem7582964 P p)). Qed.
Lemma lem7582966 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7582967 (P : type1028) : (term392 P) = (term389 P).
Proof. exact (MK_COMB (@lem7582966) (@lem7582965 P)). Qed.
Lemma lem7582968 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7582969 (P : type1028) : (term406 P) = (term407 P).
Proof. exact (MK_COMB (@lem7582968) (@lem7582967 P)). Qed.
Lemma lem7582970 (P : type1028) (p : real -> real) : (term395 P p) = (term396 P p).
Proof. exact (eq_refl (term395 P p)). Qed.
Lemma lem7582971 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7582972 (P : type1028) (p : real -> real) (m : nat) : (term397 P p m) = (term398 P p m).
Proof. exact (MK_COMB (@lem7582970 P p) (@lem7582971 m)). Qed.
Lemma lem7582973 (m : nat) (P : type1028) (p : real -> real) : (term398 P p m) = (term382 m P p).
Proof. exact (eq_refl (term398 P p m)). Qed.
Lemma lem7582974 (m : nat) (P : type1028) (p : real -> real) : (term397 P p m) = (term382 m P p).
Proof. exact (TRANS (@lem7582972 P p m) (@lem7582973 m P p)). Qed.
Lemma lem7582975 (c : nat -> real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem7582976 (m : nat) (P : type1028) (p : real -> real) (c : nat -> real) : (term399 P p m c) = (term400 m P p c).
Proof. exact (MK_COMB (@lem7582974 m P p) (@lem7582975 c)). Qed.
Lemma lem7582977 (m : nat) (c : nat -> real) (P : type1028) (p : real -> real) : (term400 m P p c) = (term380 m c P p).
Proof. exact (eq_refl (term400 m P p c)). Qed.
Lemma lem7582978 (m : nat) (c : nat -> real) (P : type1028) (p : real -> real) : (term399 P p m c) = (term380 m c P p).
Proof. exact (TRANS (@lem7582976 m P p c) (@lem7582977 m c P p)). Qed.
Lemma lem7582979 (m : nat) (c : nat -> real) (P : type1028) : (term408 P m c) = (term409 m c P).
Proof. exact (fun_ext (fun p : real -> real => @lem7582978 m c P p)). Qed.
Lemma lem7582980 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7582981 (m : nat) (c : nat -> real) (P : type1028) : (term410 P m c) = (term411 m c P).
Proof. exact (MK_COMB (@lem7582980) (@lem7582979 m c P)). Qed.
Lemma lem7582982 (m : nat) (P : type1028) : (term412 P m) = (term413 m P).
Proof. exact (fun_ext (fun c : nat -> real => @lem7582981 m c P)). Qed.
Lemma lem7582983 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7582984 (m : nat) (P : type1028) : (term414 P m) = (term415 m P).
Proof. exact (MK_COMB (@lem7582983) (@lem7582982 m P)). Qed.
Lemma lem7582985 (P : type1028) : (term416 P) = (term417 P).
Proof. exact (fun_ext (fun m : nat => @lem7582984 m P)). Qed.
Lemma lem7582986 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7582987 (P : type1028) : (term393 P) = (term418 P).
Proof. exact (MK_COMB (@lem7582986) (@lem7582985 P)). Qed.
Lemma lem7582988 (P : type1028) : ((term392 P) = (term393 P)) = ((term389 P) = (term418 P)).
Proof. exact (MK_COMB (@lem7582969 P) (@lem7582987 P)). Qed.
Lemma lem7582989 (P : type1028) : (term389 P) = (term418 P).
Proof. exact (EQ_MP (@lem7582988 P) (@lem7582949 P)). Qed.
Lemma lem7582990 (P : type1028) : (term418 P) = (term389 P).
Proof. exact (SYM (@lem7582989 P)). Qed.
Lemma lem7583006 {A B : Type'} (f : A -> B) (g : A -> B) : (term52 A B f g) = (f = g).
Proof. exact (EQ_MP (@lem7582026 A B f g) (@lem7582025 A B f g)). Qed.
Lemma lem7583007 (f : real -> real) (g : real -> real) : (term419 f g) = (f = g).
Proof. exact (@lem7583006 real real f g). Qed.
Lemma lem7583008 (p : real -> real) (m : nat) (c : nat -> real) : (term420 p m c) = (p = (term421 m c)).
Proof. exact (@lem7583007 p (term421 m c)). Qed.
Lemma lem7583009 (m : nat) (c : nat -> real) (x : real) : (term422 m c x) = (term423 m c x).
Proof. exact (eq_refl (term422 m c x)). Qed.
Lemma lem7583010 (p : real -> real) (x : real) : (term424 p x) = (term424 p x).
Proof. exact (eq_refl (term424 p x)). Qed.
Lemma lem7583011 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : ((p x) = (term422 m c x)) = ((p x) = (term423 m c x)).
Proof. exact (MK_COMB (@lem7583010 p x) (@lem7583009 m c x)). Qed.
Lemma lem7583012 (p : real -> real) (m : nat) (c : nat -> real) : (term425 p m c) = (term426 p m c).
Proof. exact (fun_ext (fun x : real => @lem7583011 p m c x)). Qed.
Lemma lem7583013 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7583014 (p : real -> real) (m : nat) (c : nat -> real) : (term420 p m c) = (term371 p m c).
Proof. exact (MK_COMB (@lem7583013) (@lem7583012 p m c)). Qed.
Lemma lem7583015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7583016 (p : real -> real) (m : nat) (c : nat -> real) : (term427 p m c) = (term428 p m c).
Proof. exact (MK_COMB (@lem7583015) (@lem7583014 p m c)). Qed.
Lemma lem7583017 (p : real -> real) (m : nat) (c : nat -> real) : (p = (term421 m c)) = (p = (term421 m c)).
Proof. exact (eq_refl (p = (term421 m c))). Qed.
Lemma lem7583018 (p : real -> real) (m : nat) (c : nat -> real) : ((term420 p m c) = (p = (term421 m c))) = ((term371 p m c) = (p = (term421 m c))).
Proof. exact (MK_COMB (@lem7583016 p m c) (@lem7583017 p m c)). Qed.
Lemma lem7583019 (p : real -> real) (m : nat) (c : nat -> real) : (term371 p m c) = (p = (term421 m c)).
Proof. exact (EQ_MP (@lem7583018 p m c) (@lem7583008 p m c)). Qed.
Lemma lem7583020 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7583021 (p : real -> real) (m : nat) (c : nat -> real) : (term378 p m c) = (term429 p m c).
Proof. exact (MK_COMB (@lem7583020) (@lem7583019 p m c)). Qed.
Lemma lem7583022 (P : type1028) (p : real -> real) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem7583023 (m : nat) (c : nat -> real) (P : type1028) (p : real -> real) : (term380 m c P p) = (term430 m c P p).
Proof. exact (MK_COMB (@lem7583021 p m c) (@lem7583022 P p)). Qed.
Lemma lem7583024 (m : nat) (c : nat -> real) (P : type1028) : (term409 m c P) = (term431 m c P).
Proof. exact (fun_ext (fun p : real -> real => @lem7583023 m c P p)). Qed.
Lemma lem7583025 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7583026 (m : nat) (c : nat -> real) (P : type1028) : (term411 m c P) = (term432 m c P).
Proof. exact (MK_COMB (@lem7583025) (@lem7583024 m c P)). Qed.
Lemma lem7583027 (m : nat) (P : type1028) : (term413 m P) = (term433 m P).
Proof. exact (fun_ext (fun c : nat -> real => @lem7583026 m c P)). Qed.
Lemma lem7583028 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7583029 (m : nat) (P : type1028) : (term415 m P) = (term434 m P).
Proof. exact (MK_COMB (@lem7583028) (@lem7583027 m P)). Qed.
Lemma lem7583030 (P : type1028) : (term417 P) = (term435 P).
Proof. exact (fun_ext (fun m : nat => @lem7583029 m P)). Qed.
Lemma lem7583031 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7583032 (P : type1028) : (term418 P) = (term436 P).
Proof. exact (MK_COMB (@lem7583031) (@lem7583030 P)). Qed.
Lemma lem7583033 (P : type1028) : (term436 P) = (term418 P).
Proof. exact (SYM (@lem7583032 P)). Qed.
Lemma lem7583075 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term437 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7583076 (p : Prop) (q : Prop) (p' : Prop) : term438 p q p'.
Proof. exact (fun q' : Prop => @lem7583075 p q p' q'). Qed.
Lemma lem7583077 (p : Prop) (q : Prop) : term439 p q.
Proof. exact (fun p' : Prop => @lem7583076 p q p'). Qed.
Lemma lem7583078 (m : nat) (c : nat -> real) (P : type1028) (p : real -> real) : term440 m c P p.
Proof. exact (@lem7583077 (p = (term421 m c)) (P p)). Qed.
Lemma lem7583079 (m : nat) (c : nat -> real) (P : type1028) (p : real -> real) (p' : Prop) : term441 m c P p p'.
Proof. exact (@lem7583078 m c P p p'). Qed.
Lemma lem7583080 (m : nat) (c : nat -> real) (P : type1028) (p : real -> real) (p' : Prop) : (term441 m c P p p') = (term442 m c P p p').
Proof. exact (eq_refl (term441 m c P p p')). Qed.
Lemma lem7583081 (m : nat) (c : nat -> real) (P : type1028) (p : real -> real) (p' : Prop) : term442 m c P p p'.
Proof. exact (EQ_MP (@lem7583080 m c P p p') (@lem7583079 m c P p p')). Qed.
Lemma lem7583082 (m : nat) (c : nat -> real) (P : type1028) (p : real -> real) (p' : Prop) (q' : Prop) : term443 m c P p p' q'.
Proof. exact (@lem7583081 m c P p p' q'). Qed.
Lemma lem7583083 (m : nat) (c : nat -> real) (P : type1028) (p : real -> real) (p' : Prop) (q' : Prop) : (term443 m c P p p' q') = (term444 m c P p p' q').
Proof. exact (eq_refl (term443 m c P p p' q')). Qed.
Lemma lem7583084 (m : nat) (c : nat -> real) (P : type1028) (p : real -> real) (p' : Prop) (q' : Prop) : term444 m c P p p' q'.
Proof. exact (EQ_MP (@lem7583083 m c P p p' q') (@lem7583082 m c P p p' q')). Qed.
Lemma lem7583202 (p : real -> real) (m : nat) (c : nat -> real) : (p = (term421 m c)) = (p = (term421 m c)).
Proof. exact (eq_refl (p = (term421 m c))). Qed.
Lemma lem7583203 (P : type1028) (p : real -> real) (m : nat) (c : nat -> real) (q' : Prop) : term445 P p m c q'.
Proof. exact (@lem7583084 m c P p (p = (term421 m c)) q'). Qed.
Lemma lem7583204 (P : type1028) (p : real -> real) (m : nat) (c : nat -> real) (q' : Prop) : term446 P p m c q'.
Proof. exact (@lem7583203 P p m c q' (@lem7583202 p m c)). Qed.
Lemma lem7583207 (p : real -> real) (m : nat) (c : nat -> real) (h1 : p = (term421 m c)) : p = (term421 m c).
Proof. exact (h1). Qed.
Lemma lem7583323 (P : type1028) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7583324 (P : type1028) (p : real -> real) (m : nat) (c : nat -> real) (h1 : p = (term421 m c)) : (P p) = (term447 P m c).
Proof. exact (MK_COMB (@lem7583323 P) (@lem7583207 p m c h1)). Qed.
Lemma lem7583440 (p : real -> real) (P : type1028) (m : nat) (c : nat -> real) : term448 p P m c.
Proof. exact (fun h0 : p = (term421 m c) => @lem7583324 P p m c h0). Qed.
Lemma lem7583441 (p : real -> real) (P : type1028) (m : nat) (c : nat -> real) : term449 p P m c.
Proof. exact (@lem7583204 P p m c (term447 P m c)). Qed.
Lemma lem7583442 (p : real -> real) (P : type1028) (m : nat) (c : nat -> real) : (term430 m c P p) = (term450 p P m c).
Proof. exact (@lem7583441 p P m c (@lem7583440 p P m c)). Qed.
Lemma lem7583930 (P : type1028) (m : nat) (c : nat -> real) : (term431 m c P) = (term451 P m c).
Proof. exact (fun_ext (fun p : real -> real => @lem7583442 p P m c)). Qed.
Lemma lem7584418 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7584419 (P : type1028) (m : nat) (c : nat -> real) : (term432 m c P) = (term452 P m c).
Proof. exact (MK_COMB (@lem7584418) (@lem7583930 P m c)). Qed.
Lemma lem7584421 {A : Type'} (P : A -> Prop) (Q : Prop) : (term50 A P Q) = (term51 A P Q).
Proof. exact (EQ_MP (@lem7582006 A P Q) (@lem7582005 A P Q)). Qed.
Lemma lem7584422 (P : type1028) (Q : Prop) : (term453 P Q) = (term454 P Q).
Proof. exact (@lem7584421 (real -> real) P Q). Qed.
Lemma lem7584423 (P : type1028) (m : nat) (c : nat -> real) : (term455 P m c) = (term456 P m c).
Proof. exact (@lem7584422 (term457 m c) (term447 P m c)). Qed.
Lemma lem7584424 (p : real -> real) (m : nat) (c : nat -> real) : (term458 m c p) = (p = (term421 m c)).
Proof. exact (eq_refl (term458 m c p)). Qed.
Lemma lem7584425 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7584426 (p : real -> real) (m : nat) (c : nat -> real) : (term459 m c p) = (term429 p m c).
Proof. exact (MK_COMB (@lem7584425) (@lem7584424 p m c)). Qed.
Lemma lem7584427 (P : type1028) (m : nat) (c : nat -> real) : (term447 P m c) = (term447 P m c).
Proof. exact (eq_refl (term447 P m c)). Qed.
Lemma lem7584428 (p : real -> real) (P : type1028) (m : nat) (c : nat -> real) : (term460 p P m c) = (term450 p P m c).
Proof. exact (MK_COMB (@lem7584426 p m c) (@lem7584427 P m c)). Qed.
Lemma lem7584429 (P : type1028) (m : nat) (c : nat -> real) : (term461 P m c) = (term451 P m c).
Proof. exact (fun_ext (fun p : real -> real => @lem7584428 p P m c)). Qed.
Lemma lem7584430 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7584431 (P : type1028) (m : nat) (c : nat -> real) : (term455 P m c) = (term452 P m c).
Proof. exact (MK_COMB (@lem7584430) (@lem7584429 P m c)). Qed.
Lemma lem7584432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7584433 (P : type1028) (m : nat) (c : nat -> real) : (term462 P m c) = (term463 P m c).
Proof. exact (MK_COMB (@lem7584432) (@lem7584431 P m c)). Qed.
Lemma lem7584434 (p : real -> real) (m : nat) (c : nat -> real) : (term458 m c p) = (p = (term421 m c)).
Proof. exact (eq_refl (term458 m c p)). Qed.
Lemma lem7584435 (m : nat) (c : nat -> real) : (term464 m c) = (term457 m c).
Proof. exact (fun_ext (fun p : real -> real => @lem7584434 p m c)). Qed.
Lemma lem7584436 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem7584437 (m : nat) (c : nat -> real) : (term465 m c) = (term466 m c).
Proof. exact (MK_COMB (@lem7584436) (@lem7584435 m c)). Qed.
Lemma lem7584438 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7584439 (m : nat) (c : nat -> real) : (term467 m c) = (term468 m c).
Proof. exact (MK_COMB (@lem7584438) (@lem7584437 m c)). Qed.
Lemma lem7584440 (P : type1028) (m : nat) (c : nat -> real) : (term447 P m c) = (term447 P m c).
Proof. exact (eq_refl (term447 P m c)). Qed.
Lemma lem7584441 (P : type1028) (m : nat) (c : nat -> real) : (term456 P m c) = (term469 P m c).
Proof. exact (MK_COMB (@lem7584439 m c) (@lem7584440 P m c)). Qed.
Lemma lem7584442 (P : type1028) (m : nat) (c : nat -> real) : ((term455 P m c) = (term456 P m c)) = ((term452 P m c) = (term469 P m c)).
Proof. exact (MK_COMB (@lem7584433 P m c) (@lem7584441 P m c)). Qed.
Lemma lem7584443 (P : type1028) (m : nat) (c : nat -> real) : (term452 P m c) = (term469 P m c).
Proof. exact (EQ_MP (@lem7584442 P m c) (@lem7584423 P m c)). Qed.
Lemma lem7584447 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term437 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7584448 (p : Prop) (q : Prop) (p' : Prop) : term438 p q p'.
Proof. exact (fun q' : Prop => @lem7584447 p q p' q'). Qed.
Lemma lem7584449 (p : Prop) (q : Prop) : term439 p q.
Proof. exact (fun p' : Prop => @lem7584448 p q p'). Qed.
Lemma lem7584450 (P : type1028) (m : nat) (c : nat -> real) : term470 P m c.
Proof. exact (@lem7584449 (term466 m c) (term447 P m c)). Qed.
Lemma lem7584451 (P : type1028) (m : nat) (c : nat -> real) (p' : Prop) : term471 P m c p'.
Proof. exact (@lem7584450 P m c p'). Qed.
Lemma lem7584452 (P : type1028) (m : nat) (c : nat -> real) (p' : Prop) : (term471 P m c p') = (term472 P m c p').
Proof. exact (eq_refl (term471 P m c p')). Qed.
Lemma lem7584453 (P : type1028) (m : nat) (c : nat -> real) (p' : Prop) : term472 P m c p'.
Proof. exact (EQ_MP (@lem7584452 P m c p') (@lem7584451 P m c p')). Qed.
Lemma lem7584454 (P : type1028) (m : nat) (c : nat -> real) (p' : Prop) (q' : Prop) : term473 P m c p' q'.
Proof. exact (@lem7584453 P m c p' q'). Qed.
Lemma lem7584455 (P : type1028) (m : nat) (c : nat -> real) (p' : Prop) (q' : Prop) : (term473 P m c p' q') = (term474 P m c p' q').
Proof. exact (eq_refl (term473 P m c p' q')). Qed.
Lemma lem7584456 (P : type1028) (m : nat) (c : nat -> real) (p' : Prop) (q' : Prop) : term474 P m c p' q'.
Proof. exact (EQ_MP (@lem7584455 P m c p' q') (@lem7584454 P m c p' q')). Qed.
Lemma lem7584458 {A : Type'} (a : A) : (term46 A a) = True.
Proof. exact (EQ_MP (@lem7582000 A a) (@lem7581999 A a)). Qed.
Lemma lem7584459 (a : real -> real) : (term475 a) = True.
Proof. exact (@lem7584458 (real -> real) a). Qed.
Lemma lem7584460 (m : nat) (c : nat -> real) : (term466 m c) = True.
Proof. exact (@lem7584459 (term421 m c)). Qed.
Lemma lem7584461 (P : type1028) (m : nat) (c : nat -> real) (q' : Prop) : term476 P m c q'.
Proof. exact (@lem7584456 P m c True q'). Qed.
Lemma lem7584462 (P : type1028) (m : nat) (c : nat -> real) (q' : Prop) : term477 P m c q'.
Proof. exact (@lem7584461 P m c q' (@lem7584460 m c)). Qed.
Lemma lem7584583 (P : type1028) (m : nat) (c : nat -> real) : (term447 P m c) = (term447 P m c).
Proof. exact (eq_refl (term447 P m c)). Qed.
Lemma lem7584584 (P : type1028) (m : nat) (c : nat -> real) : term478 P m c.
Proof. exact (fun h0 : True => @lem7584583 P m c). Qed.
Lemma lem7584585 (P : type1028) (m : nat) (c : nat -> real) : term479 P m c.
Proof. exact (@lem7584462 P m c (term447 P m c)). Qed.
Lemma lem7584586 (P : type1028) (m : nat) (c : nat -> real) : (term469 P m c) = (term480 P m c).
Proof. exact (@lem7584585 P m c (@lem7584584 P m c)). Qed.
Lemma lem7584588 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7584589 (P : type1028) (m : nat) (c : nat -> real) : (term480 P m c) = (term447 P m c).
Proof. exact (@lem7584588 (term447 P m c)). Qed.
Lemma lem7584705 (P : type1028) (m : nat) (c : nat -> real) : (term469 P m c) = (term447 P m c).
Proof. exact (TRANS (@lem7584586 P m c) (@lem7584589 P m c)). Qed.
Lemma lem7584706 (P : type1028) (m : nat) (c : nat -> real) : (term452 P m c) = (term447 P m c).
Proof. exact (TRANS (@lem7584443 P m c) (@lem7584705 P m c)). Qed.
Lemma lem7584707 (P : type1028) (m : nat) (c : nat -> real) : (term432 m c P) = (term447 P m c).
Proof. exact (TRANS (@lem7584419 P m c) (@lem7584706 P m c)). Qed.
Lemma lem7584708 (P : type1028) (m : nat) : (term433 m P) = (term481 P m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7584707 P m c)). Qed.
Lemma lem7584824 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7584825 (P : type1028) (m : nat) : (term434 m P) = (term482 P m).
Proof. exact (MK_COMB (@lem7584824) (@lem7584708 P m)). Qed.
Lemma lem7584945 (P : type1028) : (term435 P) = (term483 P).
Proof. exact (fun_ext (fun m : nat => @lem7584825 P m)). Qed.
Lemma lem7585065 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7585066 (P : type1028) : (term436 P) = (term484 P).
Proof. exact (MK_COMB (@lem7585065) (@lem7584945 P)). Qed.
Lemma lem7585190 (P : type1028) : (term484 P) = (term436 P).
Proof. exact (SYM (@lem7585066 P)). Qed.
Lemma lem7585192 (P : nat -> Prop) : term485 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem7585193 (P : type1028) : term486 P.
Proof. exact (@lem7585192 (term483 P)). Qed.
Lemma lem7585194 (P : type1028) : (term487 P) = (term488 P).
Proof. exact (eq_refl (term487 P)). Qed.
Lemma lem7585195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7585196 (P : type1028) : (term489 P) = (term490 P).
Proof. exact (MK_COMB (@lem7585195) (@lem7585194 P)). Qed.
Lemma lem7585197 (P : type1028) (m : nat) : (term491 P m) = (term482 P m).
Proof. exact (eq_refl (term491 P m)). Qed.
Lemma lem7585198 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7585199 (P : type1028) (m : nat) : (term492 P m) = (term493 P m).
Proof. exact (MK_COMB (@lem7585198) (@lem7585197 P m)). Qed.
Lemma lem7585200 (P : type1028) (m : nat) : (term494 P m) = (term495 P m).
Proof. exact (eq_refl (term494 P m)). Qed.
Lemma lem7585201 (P : type1028) (m : nat) : (term496 P m) = (term497 P m).
Proof. exact (MK_COMB (@lem7585199 P m) (@lem7585200 P m)). Qed.
Lemma lem7585202 (P : type1028) : (term498 P) = (term499 P).
Proof. exact (fun_ext (fun m : nat => @lem7585201 P m)). Qed.
Lemma lem7585203 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7585204 (P : type1028) : (term500 P) = (term501 P).
Proof. exact (MK_COMB (@lem7585203) (@lem7585202 P)). Qed.
Lemma lem7585205 (P : type1028) : (term502 P) = (term503 P).
Proof. exact (MK_COMB (@lem7585196 P) (@lem7585204 P)). Qed.
Lemma lem7585206 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7585207 (P : type1028) : (term504 P) = (term505 P).
Proof. exact (MK_COMB (@lem7585206) (@lem7585205 P)). Qed.
Lemma lem7585208 (P : type1028) (m : nat) : (term491 P m) = (term482 P m).
Proof. exact (eq_refl (term491 P m)). Qed.
Lemma lem7585209 (P : type1028) : (term506 P) = (term483 P).
Proof. exact (fun_ext (fun m : nat => @lem7585208 P m)). Qed.
Lemma lem7585210 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7585211 (P : type1028) : (term507 P) = (term484 P).
Proof. exact (MK_COMB (@lem7585210) (@lem7585209 P)). Qed.
Lemma lem7585212 (P : type1028) : (term486 P) = (term508 P).
Proof. exact (MK_COMB (@lem7585207 P) (@lem7585211 P)). Qed.
Lemma lem7585213 (P : type1028) : term508 P.
Proof. exact (EQ_MP (@lem7585212 P) (@lem7585193 P)). Qed.
Lemma lem7585214 (P : type1028) (m : nat) (h1 : term482 P m) : term482 P m.
Proof. exact (h1). Qed.
Lemma lem7585220 (f : nat -> real) : term509 f.
Proof. exact (@lem7221565 f). Qed.
Lemma lem7585221 (f : nat -> real) : (term509 f) = (term510 f).
Proof. exact (eq_refl (term509 f)). Qed.
Lemma lem7585222 (f : nat -> real) : term510 f.
Proof. exact (EQ_MP (@lem7585221 f) (@lem7585220 f)). Qed.
Lemma lem7585223 (f : nat -> real) (n : nat) : term511 f n.
Proof. exact (@lem7585222 f n). Qed.
Lemma lem7585224 (f : nat -> real) (n : nat) : (term511 f n) = ((term512 n f) = (f n)).
Proof. exact (eq_refl (term511 f n)). Qed.
Lemma lem7585228 (c : real) (P : type1028) (h1 : term339 P) : term513 P c.
Proof. exact (@lem7582836 P h1 c). Qed.
Lemma lem7585229 (P : type1028) (c : real) : (term513 P c) = (term514 P c).
Proof. exact (eq_refl (term513 P c)). Qed.
Lemma lem7585230 (c : real) (P : type1028) (h1 : term339 P) : term514 P c.
Proof. exact (EQ_MP (@lem7585229 P c) (@lem7585228 c P h1)). Qed.
Lemma lem7585231 (P : type1028) (c : real) : (term514 P c) = ((term514 P c) = True).
Proof. exact (@lem7 (term514 P c)). Qed.
Lemma lem7585259 (f : nat -> real) (n : nat) : (term512 n f) = (f n).
Proof. exact (EQ_MP (@lem7585224 f n) (@lem7585223 f n)). Qed.
Lemma lem7585260 (c : nat -> real) (x : real) : (term515 c x) = (term516 c x).
Proof. exact (@lem7585259 (term517 c x) (NUMERAL 0)). Qed.
Lemma lem7585262 {A B : Type'} (f : A -> B) (y : A) : (term518 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7585263 (f : nat -> real) (y : nat) : (term519 f y) = (f y).
Proof. exact (@lem7585262 nat real f y). Qed.
Lemma lem7585264 (c : nat -> real) (x : real) : (term520 c x) = (term516 c x).
Proof. exact (@lem7585263 (term517 c x) (NUMERAL 0)). Qed.
Lemma lem7585265 (c : nat -> real) (x : real) (i : nat) : (term521 c x i) = (term522 c x i).
Proof. exact (eq_refl (term521 c x i)). Qed.
Lemma lem7585266 (c : nat -> real) (x : real) : (term523 c x) = (term517 c x).
Proof. exact (fun_ext (fun i : nat => @lem7585265 c x i)). Qed.
Lemma lem7585267 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7585268 (c : nat -> real) (x : real) : (term520 c x) = (term516 c x).
Proof. exact (MK_COMB (@lem7585266 c x) (@lem7585267)). Qed.
Lemma lem7585269 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7585270 (c : nat -> real) (x : real) : (term524 c x) = (term525 c x).
Proof. exact (MK_COMB (@lem7585269) (@lem7585268 c x)). Qed.
Lemma lem7585271 (c : nat -> real) (x : real) : (term516 c x) = (term526 c x).
Proof. exact (eq_refl (term516 c x)). Qed.
Lemma lem7585272 (c : nat -> real) (x : real) : ((term520 c x) = (term516 c x)) = ((term516 c x) = (term526 c x)).
Proof. exact (MK_COMB (@lem7585270 c x) (@lem7585271 c x)). Qed.
Lemma lem7585273 (c : nat -> real) (x : real) : (term516 c x) = (term526 c x).
Proof. exact (EQ_MP (@lem7585272 c x) (@lem7585264 c x)). Qed.
Lemma lem7585274 (c : nat -> real) (x : real) : (term515 c x) = (term526 c x).
Proof. exact (TRANS (@lem7585260 c x) (@lem7585273 c x)). Qed.
Lemma lem7585276 (x : real) : (term527 x) = term528.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem7585277 (c : nat -> real) : (term529 c) = (term529 c).
Proof. exact (eq_refl (term529 c)). Qed.
Lemma lem7585278 (x : real) (c : nat -> real) : (term526 c x) = (term530 c).
Proof. exact (MK_COMB (@lem7585277 c) (@lem7585276 x)). Qed.
Lemma lem7585279 (x : real) (c : nat -> real) : (term515 c x) = (term530 c).
Proof. exact (TRANS (@lem7585274 c x) (@lem7585278 x c)). Qed.
Lemma lem7585280 (c : nat -> real) : (term531 c) = (term532 c).
Proof. exact (fun_ext (fun x : real => @lem7585279 x c)). Qed.
Lemma lem7585281 (P : type1028) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7585282 (P : type1028) (c : nat -> real) : (term533 P c) = (term534 P c).
Proof. exact (MK_COMB (@lem7585281 P) (@lem7585280 c)). Qed.
Lemma lem7585286 (c : real) (P : type1028) (h1 : term339 P) : (term514 P c) = True.
Proof. exact (EQ_MP (@lem7585231 P c) (@lem7585230 c P h1)). Qed.
Lemma lem7585287 (c : nat -> real) (P : type1028) (h1 : term339 P) : (term534 P c) = True.
Proof. exact (@lem7585286 (term530 c) P h1). Qed.
Lemma lem7585288 (c : nat -> real) (P : type1028) (h1 : term339 P) : (term533 P c) = True.
Proof. exact (TRANS (@lem7585282 P c) (@lem7585287 c P h1)). Qed.
Lemma lem7585289 (P : type1028) (h1 : term339 P) : (term535 P) = term536.
Proof. exact (fun_ext (fun c : nat -> real => @lem7585288 c P h1)). Qed.
Lemma lem7585290 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7585291 (P : type1028) (h1 : term339 P) : (term488 P) = term537.
Proof. exact (MK_COMB (@lem7585290) (@lem7585289 P h1)). Qed.
Lemma lem7585293 {A : Type'} (t : Prop) : (term538 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7585294 (t : Prop) : (term539 t) = t.
Proof. exact (@lem7585293 (nat -> real) t). Qed.
Lemma lem7585295 : term537 = True.
Proof. exact (@lem7585294 True). Qed.
Lemma lem7585296 (P : type1028) (h1 : term339 P) : (term488 P) = True.
Proof. exact (TRANS (@lem7585291 P h1) (@lem7585295)). Qed.
Lemma lem7585297 (P : type1028) (h1 : term339 P) : True = (term488 P).
Proof. exact (SYM (@lem7585296 P h1)). Qed.
Lemma lem7585298 (P : type1028) (h1 : term339 P) : term488 P.
Proof. exact (EQ_MP (@lem7585297 P h1) (@lem0)). Qed.
Lemma lem7585352 (m : nat) (n : nat) (f : nat -> real) : term42 m n f.
Proof. exact (fun h0 : Peano.le m n => @lem7581991 f m n h0). Qed.
Lemma lem7585353 (m : nat) (c : nat -> real) (x : real) : term540 m c x.
Proof. exact (@lem7585352 (NUMERAL 0) (S m) (term517 c x)). Qed.
Lemma lem7585355 (n : nat) : (term34 n) = True.
Proof. exact (EQ_MP (@lem7581976 n) (@lem7581975 n)). Qed.
Lemma lem7585356 (m : nat) : (term541 m) = True.
Proof. exact (@lem7585355 (S m)). Qed.
Lemma lem7585357 (m : nat) : True = (term541 m).
Proof. exact (SYM (@lem7585356 m)). Qed.
Lemma lem7585358 (m : nat) : term541 m.
Proof. exact (EQ_MP (@lem7585357 m) (@lem0)). Qed.
Lemma lem7585359 (m : nat) (c : nat -> real) (x : real) : (term542 m c x) = (term543 m c x).
Proof. exact (@lem7585353 m c x (@lem7585358 m)). Qed.
Lemma lem7585361 {A B : Type'} (f : A -> B) (y : A) : (term518 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7585362 (f : nat -> real) (y : nat) : (term519 f y) = (f y).
Proof. exact (@lem7585361 nat real f y). Qed.
Lemma lem7585363 (c : nat -> real) (x : real) : (term520 c x) = (term516 c x).
Proof. exact (@lem7585362 (term517 c x) (NUMERAL 0)). Qed.
Lemma lem7585364 (c : nat -> real) (x : real) (i : nat) : (term521 c x i) = (term522 c x i).
Proof. exact (eq_refl (term521 c x i)). Qed.
Lemma lem7585365 (c : nat -> real) (x : real) : (term523 c x) = (term517 c x).
Proof. exact (fun_ext (fun i : nat => @lem7585364 c x i)). Qed.
Lemma lem7585366 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7585367 (c : nat -> real) (x : real) : (term520 c x) = (term516 c x).
Proof. exact (MK_COMB (@lem7585365 c x) (@lem7585366)). Qed.
Lemma lem7585368 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7585369 (c : nat -> real) (x : real) : (term524 c x) = (term525 c x).
Proof. exact (MK_COMB (@lem7585368) (@lem7585367 c x)). Qed.
Lemma lem7585370 (c : nat -> real) (x : real) : (term516 c x) = (term526 c x).
Proof. exact (eq_refl (term516 c x)). Qed.
Lemma lem7585371 (c : nat -> real) (x : real) : ((term520 c x) = (term516 c x)) = ((term516 c x) = (term526 c x)).
Proof. exact (MK_COMB (@lem7585369 c x) (@lem7585370 c x)). Qed.
Lemma lem7585372 (c : nat -> real) (x : real) : (term516 c x) = (term526 c x).
Proof. exact (EQ_MP (@lem7585371 c x) (@lem7585363 c x)). Qed.
Lemma lem7585373 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7585374 (c : nat -> real) (x : real) : (term544 c x) = (term545 c x).
Proof. exact (MK_COMB (@lem7585373) (@lem7585372 c x)). Qed.
Lemma lem7585499 (m : nat) : (S m) = (term36 m).
Proof. exact (EQ_MP (@lem7581979 m) (@lem7581978 m)). Qed.
Lemma lem7585500 : term546 = term546.
Proof. exact (eq_refl term546). Qed.
Lemma lem7585501 (m : nat) : (term547 m) = (term548 m).
Proof. exact (MK_COMB (@lem7585500) (@lem7585499 m)). Qed.
Lemma lem7585502 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7585503 (m : nat) : (term549 m) = (term550 m).
Proof. exact (MK_COMB (@lem7585502) (@lem7585501 m)). Qed.
Lemma lem7585504 (c : nat -> real) (x : real) : (term517 c x) = (term517 c x).
Proof. exact (eq_refl (term517 c x)). Qed.
Lemma lem7585505 (m : nat) (c : nat -> real) (x : real) : (term551 m c x) = (term552 m c x).
Proof. exact (MK_COMB (@lem7585503 m) (@lem7585504 c x)). Qed.
Lemma lem7585626 (m : nat) (c : nat -> real) (x : real) : (term543 m c x) = (term553 m c x).
Proof. exact (MK_COMB (@lem7585374 c x) (@lem7585505 m c x)). Qed.
Lemma lem7585747 (m : nat) (c : nat -> real) (x : real) : (term542 m c x) = (term553 m c x).
Proof. exact (TRANS (@lem7585359 m c x) (@lem7585626 m c x)). Qed.
Lemma lem7585748 (m : nat) (c : nat -> real) : (term554 m c) = (term555 m c).
Proof. exact (fun_ext (fun x : real => @lem7585747 m c x)). Qed.
Lemma lem7585869 (P : type1028) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7585870 (P : type1028) (m : nat) (c : nat -> real) : (term556 P m c) = (term557 P m c).
Proof. exact (MK_COMB (@lem7585869 P) (@lem7585748 m c)). Qed.
Lemma lem7585991 (P : type1028) (m : nat) (c : nat -> real) : (term557 P m c) = (term556 P m c).
Proof. exact (SYM (@lem7585870 P m c)). Qed.
Lemma lem7586017 (P : type1028) (h1 : term341 P) : term341 P.
Proof. exact (h1). Qed.
Lemma lem7586018 (p : real -> real) (P : type1028) (h1 : term341 P) : term558 P p.
Proof. exact (@lem7586017 P h1 p). Qed.
Lemma lem7586019 (P : type1028) (p : real -> real) : (term558 P p) = (term559 P p).
Proof. exact (eq_refl (term558 P p)). Qed.
Lemma lem7586020 (p : real -> real) (P : type1028) (h1 : term341 P) : term559 P p.
Proof. exact (EQ_MP (@lem7586019 P p) (@lem7586018 p P h1)). Qed.
Lemma lem7586021 (p : real -> real) (q : real -> real) (P : type1028) (h1 : term341 P) : term560 P p q.
Proof. exact (@lem7586020 p P h1 q). Qed.
Lemma lem7586022 (P : type1028) (p : real -> real) (q : real -> real) : (term560 P p q) = (term561 P p q).
Proof. exact (eq_refl (term560 P p q)). Qed.
Lemma lem7586023 (p : real -> real) (q : real -> real) (P : type1028) (h1 : term341 P) : term561 P p q.
Proof. exact (EQ_MP (@lem7586022 P p q) (@lem7586021 p q P h1)). Qed.
Lemma lem7586024 (p : real -> real) (P : type1028) (q : real -> real) (h1 : term562 p P q) : term562 p P q.
Proof. exact (h1). Qed.
Lemma lem7586025 (p : real -> real) (P : type1028) (q : real -> real) (h1 : term341 P) (h2 : term562 p P q) : term563 P p q.
Proof. exact (@lem7586023 p q P h1 (@lem7586024 p P q h2)). Qed.
Lemma lem7586026 (p : real -> real) (P : type1028) (q : real -> real) (h1 : term562 p P q) : term564 P p q.
Proof. exact (fun h0 : term341 P => @lem7586025 p P q h0 h1). Qed.
Lemma lem7586027 (P : type1028) (h1 : term341 P) : term341 P.
Proof. exact (h1). Qed.
Lemma lem7586028 (p : real -> real) (P : type1028) (q : real -> real) (h1 : term341 P) (h2 : term562 p P q) : term563 P p q.
Proof. exact (@lem7586026 p P q h2 (@lem7586027 P h1)). Qed.
Lemma lem7586029 (p : real -> real) (q : real -> real) (P : type1028) (h1 : term341 P) : term561 P p q.
Proof. exact (fun h0 : term562 p P q => @lem7586028 p P q h1 h0). Qed.
Lemma lem7586030 (p : real -> real) (P : type1028) (h1 : term341 P) : term559 P p.
Proof. exact (fun q : real -> real => @lem7586029 p q P h1). Qed.
Lemma lem7586031 (P : type1028) (h1 : term341 P) : term341 P.
Proof. exact (fun p : real -> real => @lem7586030 p P h1). Qed.
Lemma lem7586032 (P : type1028) : term565 P.
Proof. exact (fun h0 : term341 P => @lem7586031 P h0). Qed.
Lemma lem7586033 (P : type1028) (h1 : term341 P) : term341 P.
Proof. exact (@lem7586032 P (@lem7582838 P h1)). Qed.
Lemma lem7586034 (p : real -> real) (P : type1028) (h1 : term341 P) : term558 P p.
Proof. exact (@lem7586033 P h1 p). Qed.
Lemma lem7586035 (P : type1028) (p : real -> real) : (term558 P p) = (term559 P p).
Proof. exact (eq_refl (term558 P p)). Qed.
Lemma lem7586036 (p : real -> real) (P : type1028) (h1 : term341 P) : term559 P p.
Proof. exact (EQ_MP (@lem7586035 P p) (@lem7586034 p P h1)). Qed.
Lemma lem7586037 (p : real -> real) (q : real -> real) (P : type1028) (h1 : term341 P) : term560 P p q.
Proof. exact (@lem7586036 p P h1 q). Qed.
Lemma lem7586038 (P : type1028) (p : real -> real) (q : real -> real) : (term560 P p q) = (term561 P p q).
Proof. exact (eq_refl (term560 P p q)). Qed.
Lemma lem7586041 (p : real -> real) (q : real -> real) (P : type1028) (h1 : term341 P) : term561 P p q.
Proof. exact (EQ_MP (@lem7586038 P p q) (@lem7586037 p q P h1)). Qed.
Lemma lem7586042 (m : nat) (c : nat -> real) (P : type1028) (h1 : term341 P) : term566 P m c.
Proof. exact (@lem7586041 (term567 c) (term568 m c) P h1). Qed.
Lemma lem7586043 (c : nat -> real) (x : real) : (term569 c x) = (term526 c x).
Proof. exact (eq_refl (term569 c x)). Qed.
Lemma lem7586044 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7586045 (c : nat -> real) (x : real) : (term570 c x) = (term545 c x).
Proof. exact (MK_COMB (@lem7586044) (@lem7586043 c x)). Qed.
Lemma lem7586046 (m : nat) (c : nat -> real) (x : real) : (term571 m c x) = (term552 m c x).
Proof. exact (eq_refl (term571 m c x)). Qed.
Lemma lem7586047 (m : nat) (c : nat -> real) (x : real) : (term572 m c x) = (term553 m c x).
Proof. exact (MK_COMB (@lem7586045 c x) (@lem7586046 m c x)). Qed.
Lemma lem7586048 (m : nat) (c : nat -> real) : (term573 m c) = (term555 m c).
Proof. exact (fun_ext (fun x : real => @lem7586047 m c x)). Qed.
Lemma lem7586049 (P : type1028) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7586050 (P : type1028) (m : nat) (c : nat -> real) : (term574 P m c) = (term557 P m c).
Proof. exact (MK_COMB (@lem7586049 P) (@lem7586048 m c)). Qed.
Lemma lem7586051 (P : type1028) (m : nat) (c : nat -> real) : (term575 P m c) = (term575 P m c).
Proof. exact (eq_refl (term575 P m c)). Qed.
Lemma lem7586052 (P : type1028) (m : nat) (c : nat -> real) : (term566 P m c) = (term576 P m c).
Proof. exact (MK_COMB (@lem7586051 P m c) (@lem7586050 P m c)). Qed.
Lemma lem7586053 (m : nat) (c : nat -> real) (P : type1028) (h1 : term341 P) : term576 P m c.
Proof. exact (EQ_MP (@lem7586052 P m c) (@lem7586042 m c P h1)). Qed.
Lemma lem7586061 (c : real) (P : type1028) (h1 : term339 P) : term513 P c.
Proof. exact (@lem7582836 P h1 c). Qed.
Lemma lem7586062 (P : type1028) (c : real) : (term513 P c) = (term514 P c).
Proof. exact (eq_refl (term513 P c)). Qed.
Lemma lem7586063 (c : real) (P : type1028) (h1 : term339 P) : term514 P c.
Proof. exact (EQ_MP (@lem7586062 P c) (@lem7586061 c P h1)). Qed.
Lemma lem7586064 (P : type1028) (c : real) : (term514 P c) = ((term514 P c) = True).
Proof. exact (@lem7 (term514 P c)). Qed.
Lemma lem7586095 (x : real) : (term527 x) = term528.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem7586096 (c : nat -> real) : (term529 c) = (term529 c).
Proof. exact (eq_refl (term529 c)). Qed.
Lemma lem7586097 (x : real) (c : nat -> real) : (term526 c x) = (term530 c).
Proof. exact (MK_COMB (@lem7586096 c) (@lem7586095 x)). Qed.
Lemma lem7586098 (c : nat -> real) : (term567 c) = (term532 c).
Proof. exact (fun_ext (fun x : real => @lem7586097 x c)). Qed.
Lemma lem7586099 (P : type1028) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7586100 (P : type1028) (c : nat -> real) : (term577 P c) = (term534 P c).
Proof. exact (MK_COMB (@lem7586099 P) (@lem7586098 c)). Qed.
Lemma lem7586104 (c : real) (P : type1028) (h1 : term339 P) : (term514 P c) = True.
Proof. exact (EQ_MP (@lem7586064 P c) (@lem7586063 c P h1)). Qed.
Lemma lem7586105 (c : nat -> real) (P : type1028) (h1 : term339 P) : (term534 P c) = True.
Proof. exact (@lem7586104 (term530 c) P h1). Qed.
Lemma lem7586106 (c : nat -> real) (P : type1028) (h1 : term339 P) : (term577 P c) = True.
Proof. exact (TRANS (@lem7586100 P c) (@lem7586105 c P h1)). Qed.
Lemma lem7586107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7586108 (c : nat -> real) (P : type1028) (h1 : term339 P) : (term578 P c) = (and True).
Proof. exact (MK_COMB (@lem7586107) (@lem7586106 c P h1)). Qed.
Lemma lem7586114 (P : type1028) (m : nat) (c : nat -> real) : (term579 P m c) = (term579 P m c).
Proof. exact (eq_refl (term579 P m c)). Qed.
Lemma lem7586115 (m : nat) (c : nat -> real) (P : type1028) (h1 : term339 P) : (term580 P m c) = (term581 P m c).
Proof. exact (MK_COMB (@lem7586108 c P h1) (@lem7586114 P m c)). Qed.
Lemma lem7586117 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7586118 (P : type1028) (m : nat) (c : nat -> real) : (term581 P m c) = (term579 P m c).
Proof. exact (@lem7586117 (term579 P m c)). Qed.
Lemma lem7586124 (m : nat) (c : nat -> real) (P : type1028) (h1 : term339 P) : (term580 P m c) = (term579 P m c).
Proof. exact (TRANS (@lem7586115 m c P h1) (@lem7586118 P m c)). Qed.
Lemma lem7586125 (m : nat) (c : nat -> real) (P : type1028) (h1 : term339 P) : (term579 P m c) = (term580 P m c).
Proof. exact (SYM (@lem7586124 m c P h1)). Qed.
Lemma lem7586127 (m : nat) (n : nat) (f : nat -> real) : (term31 m n f) = (term32 m n f).
Proof. exact (EQ_MP (@lem7581971 m n f) (@lem7581970 m f n)). Qed.
Lemma lem7586128 (m : nat) (c : nat -> real) (x : real) : (term552 m c x) = (term582 m c x).
Proof. exact (@lem7586127 (NUMERAL 0) m (term517 c x)). Qed.
Lemma lem7586130 {A B : Type'} (f : A -> B) (y : A) : (term518 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7586131 (f : nat -> real) (y : nat) : (term519 f y) = (f y).
Proof. exact (@lem7586130 nat real f y). Qed.
Lemma lem7586132 (c : nat -> real) (x : real) (i : nat) : (term583 c x i) = (term584 c x i).
Proof. exact (@lem7586131 (term517 c x) (term36 i)). Qed.
Lemma lem7586133 (c : nat -> real) (x : real) (i : nat) : (term521 c x i) = (term522 c x i).
Proof. exact (eq_refl (term521 c x i)). Qed.
Lemma lem7586134 (c : nat -> real) (x : real) : (term523 c x) = (term517 c x).
Proof. exact (fun_ext (fun i : nat => @lem7586133 c x i)). Qed.
Lemma lem7586135 (i : nat) : (term36 i) = (term36 i).
Proof. exact (eq_refl (term36 i)). Qed.
Lemma lem7586136 (c : nat -> real) (x : real) (i : nat) : (term583 c x i) = (term584 c x i).
Proof. exact (MK_COMB (@lem7586134 c x) (@lem7586135 i)). Qed.
Lemma lem7586137 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7586138 (c : nat -> real) (x : real) (i : nat) : (term585 c x i) = (term586 c x i).
Proof. exact (MK_COMB (@lem7586137) (@lem7586136 c x i)). Qed.
Lemma lem7586139 (c : nat -> real) (x : real) (i : nat) : (term584 c x i) = (term587 c x i).
Proof. exact (eq_refl (term584 c x i)). Qed.
Lemma lem7586140 (c : nat -> real) (x : real) (i : nat) : ((term583 c x i) = (term584 c x i)) = ((term584 c x i) = (term587 c x i)).
Proof. exact (MK_COMB (@lem7586138 c x i) (@lem7586139 c x i)). Qed.
Lemma lem7586141 (c : nat -> real) (x : real) (i : nat) : (term584 c x i) = (term587 c x i).
Proof. exact (EQ_MP (@lem7586140 c x i) (@lem7586132 c x i)). Qed.
Lemma lem7586142 (c : nat -> real) (x : real) : (term588 c x) = (term589 c x).
Proof. exact (fun_ext (fun i : nat => @lem7586141 c x i)). Qed.
Lemma lem7586143 (m : nat) : (term590 m) = (term590 m).
Proof. exact (eq_refl (term590 m)). Qed.
Lemma lem7586144 (m : nat) (c : nat -> real) (x : real) : (term582 m c x) = (term591 m c x).
Proof. exact (MK_COMB (@lem7586143 m) (@lem7586142 c x)). Qed.
Lemma lem7586145 (m : nat) (c : nat -> real) (x : real) : (term552 m c x) = (term591 m c x).
Proof. exact (TRANS (@lem7586128 m c x) (@lem7586144 m c x)). Qed.
Lemma lem7586146 (m : nat) (c : nat -> real) : (term568 m c) = (term592 m c).
Proof. exact (fun_ext (fun x : real => @lem7586145 m c x)). Qed.
Lemma lem7586147 (P : type1028) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7586148 (P : type1028) (m : nat) (c : nat -> real) : (term579 P m c) = (term593 P m c).
Proof. exact (MK_COMB (@lem7586147 P) (@lem7586146 m c)). Qed.
Lemma lem7586149 (P : type1028) (m : nat) (c : nat -> real) : (term593 P m c) = (term579 P m c).
Proof. exact (SYM (@lem7586148 P m c)). Qed.
Lemma lem7586168 (m : nat) (x : real) (n : nat) : (term21 x m n) = (term22 m x n).
Proof. exact (EQ_MP (@lem7581959 m x n) (@lem7581958 m x n)). Qed.
Lemma lem7586169 (i : nat) (x : real) : (term594 x i) = (term595 i x).
Proof. exact (@lem7586168 i x term24). Qed.
Lemma lem7586171 (x : real) : (term15 x) = x.
Proof. exact (EQ_MP (@lem7581950 x) (@lem7581949 x)). Qed.
Lemma lem7586172 (x : real) (i : nat) : (term596 x i) = (term596 x i).
Proof. exact (eq_refl (term596 x i)). Qed.
Lemma lem7586173 (i : nat) (x : real) : (term595 i x) = (term597 i x).
Proof. exact (MK_COMB (@lem7586172 x i) (@lem7586171 x)). Qed.
Lemma lem7586174 (i : nat) (x : real) : (term594 x i) = (term597 i x).
Proof. exact (TRANS (@lem7586169 i x) (@lem7586173 i x)). Qed.
Lemma lem7586175 (c : nat -> real) (i : nat) : (term598 c i) = (term598 c i).
Proof. exact (eq_refl (term598 c i)). Qed.
Lemma lem7586176 (c : nat -> real) (i : nat) (x : real) : (term587 c x i) = (term599 c i x).
Proof. exact (MK_COMB (@lem7586175 c i) (@lem7586174 i x)). Qed.
Lemma lem7586178 (x : real) (y : real) (z : real) : (term12 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem7581947 x y z) (@lem7581946 x y z)). Qed.
Lemma lem7586179 (c : nat -> real) (i : nat) (x : real) : (term599 c i x) = (term600 c i x).
Proof. exact (@lem7586178 (term601 c i) (real_pow x i) x). Qed.
Lemma lem7586180 (c : nat -> real) (i : nat) (x : real) : (term587 c x i) = (term600 c i x).
Proof. exact (TRANS (@lem7586176 c i x) (@lem7586179 c i x)). Qed.
Lemma lem7586181 (c : nat -> real) (x : real) : (term589 c x) = (term602 c x).
Proof. exact (fun_ext (fun i : nat => @lem7586180 c i x)). Qed.
Lemma lem7586182 (m : nat) : (term590 m) = (term590 m).
Proof. exact (eq_refl (term590 m)). Qed.
Lemma lem7586183 (m : nat) (c : nat -> real) (x : real) : (term591 m c x) = (term603 m c x).
Proof. exact (MK_COMB (@lem7586182 m) (@lem7586181 c x)). Qed.
Lemma lem7586185 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) : (term5 A s f c) = (term6 A s f c).
Proof. exact (EQ_MP (@lem7581938 A s f c) (@lem7581937 A f c s)). Qed.
Lemma lem7586186 (s : nat -> Prop) (f : nat -> real) (c : real) : (term604 s f c) = (term605 s f c).
Proof. exact (@lem7586185 nat s f c). Qed.
Lemma lem7586187 (m : nat) (c : nat -> real) (x : real) : (term606 m c x) = (term607 m c x).
Proof. exact (@lem7586186 (term608 m) (term609 c x) x). Qed.
Lemma lem7586188 (c : nat -> real) (x : real) (i : nat) : (term610 c x i) = (term611 c x i).
Proof. exact (eq_refl (term610 c x i)). Qed.
Lemma lem7586189 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7586190 (c : nat -> real) (x : real) (i : nat) : (term612 c x i) = (term613 c x i).
Proof. exact (MK_COMB (@lem7586189) (@lem7586188 c x i)). Qed.
Lemma lem7586191 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7586192 (c : nat -> real) (i : nat) (x : real) : (term614 c i x) = (term600 c i x).
Proof. exact (MK_COMB (@lem7586190 c x i) (@lem7586191 x)). Qed.
Lemma lem7586193 (c : nat -> real) (x : real) : (term615 c x) = (term602 c x).
Proof. exact (fun_ext (fun i : nat => @lem7586192 c i x)). Qed.
Lemma lem7586194 (m : nat) : (term590 m) = (term590 m).
Proof. exact (eq_refl (term590 m)). Qed.
Lemma lem7586195 (m : nat) (c : nat -> real) (x : real) : (term606 m c x) = (term603 m c x).
Proof. exact (MK_COMB (@lem7586194 m) (@lem7586193 c x)). Qed.
Lemma lem7586196 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7586197 (m : nat) (c : nat -> real) (x : real) : (term616 m c x) = (term617 m c x).
Proof. exact (MK_COMB (@lem7586196) (@lem7586195 m c x)). Qed.
Lemma lem7586198 (m : nat) (c : nat -> real) (x : real) : (term607 m c x) = (term607 m c x).
Proof. exact (eq_refl (term607 m c x)). Qed.
Lemma lem7586199 (m : nat) (c : nat -> real) (x : real) : ((term606 m c x) = (term607 m c x)) = ((term603 m c x) = (term607 m c x)).
Proof. exact (MK_COMB (@lem7586197 m c x) (@lem7586198 m c x)). Qed.
Lemma lem7586200 (m : nat) (c : nat -> real) (x : real) : (term603 m c x) = (term607 m c x).
Proof. exact (EQ_MP (@lem7586199 m c x) (@lem7586187 m c x)). Qed.
Lemma lem7586218 (m : nat) (c : nat -> real) (x : real) : (term591 m c x) = (term607 m c x).
Proof. exact (TRANS (@lem7586183 m c x) (@lem7586200 m c x)). Qed.
Lemma lem7586219 (m : nat) (c : nat -> real) : (term592 m c) = (term618 m c).
Proof. exact (fun_ext (fun x : real => @lem7586218 m c x)). Qed.
Lemma lem7586220 (P : type1028) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7586221 (P : type1028) (m : nat) (c : nat -> real) : (term593 P m c) = (term619 P m c).
Proof. exact (MK_COMB (@lem7586220 P) (@lem7586219 m c)). Qed.
Lemma lem7586222 (P : type1028) (m : nat) (c : nat -> real) : (term619 P m c) = (term593 P m c).
Proof. exact (SYM (@lem7586221 P m c)). Qed.
Lemma lem7586223 (P : type1028) : (term337 P) = ((term337 P) = True).
Proof. exact (@lem7 (term337 P)). Qed.
Lemma lem7586245 (p : real -> real) (P : type1028) (h1 : term340 P) : term620 P p.
Proof. exact (@lem7582837 P h1 p). Qed.
Lemma lem7586246 (P : type1028) (p : real -> real) : (term620 P p) = (term621 P p).
Proof. exact (eq_refl (term620 P p)). Qed.
Lemma lem7586247 (p : real -> real) (P : type1028) (h1 : term340 P) : term621 P p.
Proof. exact (EQ_MP (@lem7586246 P p) (@lem7586245 p P h1)). Qed.
Lemma lem7586248 (p : real -> real) (q : real -> real) (P : type1028) (h1 : term340 P) : term622 P p q.
Proof. exact (@lem7586247 p P h1 q). Qed.
Lemma lem7586249 (P : type1028) (p : real -> real) (q : real -> real) : (term622 P p q) = (term623 P p q).
Proof. exact (eq_refl (term622 P p q)). Qed.
Lemma lem7586250 (p : real -> real) (q : real -> real) (P : type1028) (h1 : term340 P) : term623 P p q.
Proof. exact (EQ_MP (@lem7586249 P p q) (@lem7586248 p q P h1)). Qed.
Lemma lem7586251 (p : real -> real) (P : type1028) (q : real -> real) (h1 : term562 p P q) : term562 p P q.
Proof. exact (h1). Qed.
Lemma lem7586252 (p : real -> real) (P : type1028) (q : real -> real) (h1 : term340 P) (h2 : term562 p P q) : term624 P p q.
Proof. exact (@lem7586250 p q P h1 (@lem7586251 p P q h2)). Qed.
Lemma lem7586253 (P : type1028) (p : real -> real) (q : real -> real) : (term624 P p q) = ((term624 P p q) = True).
Proof. exact (@lem7 (term624 P p q)). Qed.
Lemma lem7586254 (p : real -> real) (P : type1028) (q : real -> real) (h1 : term340 P) (h2 : term562 p P q) : (term624 P p q) = True.
Proof. exact (EQ_MP (@lem7586253 P p q) (@lem7586252 p P q h1 h2)). Qed.
Lemma lem7586260 (c : nat -> real) (P : type1028) (m : nat) (h1 : term482 P m) : term625 P m c.
Proof. exact (@lem7585214 P m h1 c). Qed.
Lemma lem7586261 (P : type1028) (m : nat) (c : nat -> real) : (term625 P m c) = (term447 P m c).
Proof. exact (eq_refl (term625 P m c)). Qed.
Lemma lem7586262 (c : nat -> real) (P : type1028) (m : nat) (h1 : term482 P m) : term447 P m c.
Proof. exact (EQ_MP (@lem7586261 P m c) (@lem7586260 c P m h1)). Qed.
Lemma lem7586263 (P : type1028) (m : nat) (c : nat -> real) : (term447 P m c) = ((term447 P m c) = True).
Proof. exact (@lem7 (term447 P m c)). Qed.
Lemma lem7586266 (p : real -> real) (q : real -> real) (P : type1028) (h1 : term340 P) : term626 P p q.
Proof. exact (fun h0 : term562 p P q => @lem7586254 p P q h1 h0). Qed.
Lemma lem7586267 (m : nat) (c : nat -> real) (P : type1028) (h1 : term340 P) : term627 P m c.
Proof. exact (@lem7586266 (term628 m c) term629 P h1). Qed.
Lemma lem7586268 (m : nat) (c : nat -> real) (x : real) : (term630 m c x) = (term631 m c x).
Proof. exact (eq_refl (term630 m c x)). Qed.
Lemma lem7586269 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7586270 (m : nat) (c : nat -> real) (x : real) : (term632 m c x) = (term633 m c x).
Proof. exact (MK_COMB (@lem7586269) (@lem7586268 m c x)). Qed.
Lemma lem7586271 (x : real) : (term634 x) = x.
Proof. exact (eq_refl (term634 x)). Qed.
Lemma lem7586272 (m : nat) (c : nat -> real) (x : real) : (term635 m c x) = (term607 m c x).
Proof. exact (MK_COMB (@lem7586270 m c x) (@lem7586271 x)). Qed.
Lemma lem7586273 (m : nat) (c : nat -> real) : (term636 m c) = (term618 m c).
Proof. exact (fun_ext (fun x : real => @lem7586272 m c x)). Qed.
Lemma lem7586274 (P : type1028) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7586275 (P : type1028) (m : nat) (c : nat -> real) : (term637 P m c) = (term619 P m c).
Proof. exact (MK_COMB (@lem7586274 P) (@lem7586273 m c)). Qed.
Lemma lem7586276 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7586277 (P : type1028) (m : nat) (c : nat -> real) : (term638 P m c) = (term639 P m c).
Proof. exact (MK_COMB (@lem7586276) (@lem7586275 P m c)). Qed.
Lemma lem7586278 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem7586279 (P : type1028) (m : nat) (c : nat -> real) : ((term637 P m c) = True) = ((term619 P m c) = True).
Proof. exact (MK_COMB (@lem7586277 P m c) (@lem7586278)). Qed.
Lemma lem7586280 (m : nat) (c : nat -> real) (P : type1028) : (term640 m c P) = (term640 m c P).
Proof. exact (eq_refl (term640 m c P)). Qed.
Lemma lem7586281 (P : type1028) (m : nat) (c : nat -> real) : (term627 P m c) = (term641 P m c).
Proof. exact (MK_COMB (@lem7586280 m c P) (@lem7586279 P m c)). Qed.
Lemma lem7586282 (m : nat) (c : nat -> real) (P : type1028) (h1 : term340 P) : term641 P m c.
Proof. exact (EQ_MP (@lem7586281 P m c) (@lem7586267 m c P h1)). Qed.
Lemma lem7586286 (c : nat -> real) (P : type1028) (m : nat) (h1 : term482 P m) : (term447 P m c) = True.
Proof. exact (EQ_MP (@lem7586263 P m c) (@lem7586262 c P m h1)). Qed.
Lemma lem7586287 (c : nat -> real) (P : type1028) (m : nat) (h1 : term482 P m) : (term642 P m c) = True.
Proof. exact (@lem7586286 (term643 c) P m h1). Qed.
Lemma lem7586288 (c : nat -> real) (i : nat) : (term644 c i) = (term601 c i).
Proof. exact (eq_refl (term644 c i)). Qed.
Lemma lem7586289 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7586290 (c : nat -> real) (i : nat) : (term645 c i) = (term598 c i).
Proof. exact (MK_COMB (@lem7586289) (@lem7586288 c i)). Qed.
Lemma lem7586291 (x : real) (i : nat) : (real_pow x i) = (real_pow x i).
Proof. exact (eq_refl (real_pow x i)). Qed.
Lemma lem7586292 (c : nat -> real) (x : real) (i : nat) : (term646 c x i) = (term611 c x i).
Proof. exact (MK_COMB (@lem7586290 c i) (@lem7586291 x i)). Qed.
Lemma lem7586293 (c : nat -> real) (x : real) : (term647 c x) = (term609 c x).
Proof. exact (fun_ext (fun i : nat => @lem7586292 c x i)). Qed.
Lemma lem7586294 (m : nat) : (term590 m) = (term590 m).
Proof. exact (eq_refl (term590 m)). Qed.
Lemma lem7586295 (m : nat) (c : nat -> real) (x : real) : (term648 m c x) = (term631 m c x).
Proof. exact (MK_COMB (@lem7586294 m) (@lem7586293 c x)). Qed.
Lemma lem7586296 (m : nat) (c : nat -> real) : (term649 m c) = (term628 m c).
Proof. exact (fun_ext (fun x : real => @lem7586295 m c x)). Qed.
Lemma lem7586297 (P : type1028) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7586298 (P : type1028) (m : nat) (c : nat -> real) : (term642 P m c) = (term650 P m c).
Proof. exact (MK_COMB (@lem7586297 P) (@lem7586296 m c)). Qed.
Lemma lem7586299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7586300 (P : type1028) (m : nat) (c : nat -> real) : (term651 P m c) = (term652 P m c).
Proof. exact (MK_COMB (@lem7586299) (@lem7586298 P m c)). Qed.
Lemma lem7586301 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem7586302 (P : type1028) (m : nat) (c : nat -> real) : ((term642 P m c) = True) = ((term650 P m c) = True).
Proof. exact (MK_COMB (@lem7586300 P m c) (@lem7586301)). Qed.
Lemma lem7586303 (c : nat -> real) (P : type1028) (m : nat) (h1 : term482 P m) : (term650 P m c) = True.
Proof. exact (EQ_MP (@lem7586302 P m c) (@lem7586287 c P m h1)). Qed.
Lemma lem7586304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7586305 (c : nat -> real) (P : type1028) (m : nat) (h1 : term482 P m) : (term653 P m c) = (and True).
Proof. exact (MK_COMB (@lem7586304) (@lem7586303 c P m h1)). Qed.
Lemma lem7586307 (P : type1028) (h1 : term337 P) : (term337 P) = True.
Proof. exact (EQ_MP (@lem7586223 P) (@lem7582834 P h1)). Qed.
Lemma lem7586308 (c : nat -> real) (m : nat) (P : type1028) (h1 : term482 P m) (h2 : term337 P) : (term654 m c P) = (True /\ True).
Proof. exact (MK_COMB (@lem7586305 c P m h1) (@lem7586307 P h2)). Qed.
Lemma lem7586310 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7586311 : (True /\ True) = True.
Proof. exact (@lem7586310 True). Qed.
Lemma lem7586312 (c : nat -> real) (m : nat) (P : type1028) (h1 : term482 P m) (h2 : term337 P) : (term654 m c P) = True.
Proof. exact (TRANS (@lem7586308 c m P h1 h2) (@lem7586311)). Qed.
Lemma lem7586313 (c : nat -> real) (m : nat) (P : type1028) (h1 : term482 P m) (h2 : term337 P) : True = (term654 m c P).
Proof. exact (SYM (@lem7586312 c m P h1 h2)). Qed.
Lemma lem7586314 (c : nat -> real) (m : nat) (P : type1028) (h1 : term482 P m) (h2 : term337 P) : term654 m c P.
Proof. exact (EQ_MP (@lem7586313 c m P h1 h2) (@lem0)). Qed.
Lemma lem7586315 (c : nat -> real) (m : nat) (P : type1028) (h1 : term482 P m) (h2 : term340 P) (h3 : term337 P) : (term619 P m c) = True.
Proof. exact (@lem7586282 m c P h2 (@lem7586314 c m P h1 h3)). Qed.
Lemma lem7586316 (c : nat -> real) (m : nat) (P : type1028) (h1 : term482 P m) (h2 : term340 P) (h3 : term337 P) : True = (term619 P m c).
Proof. exact (SYM (@lem7586315 c m P h1 h2 h3)). Qed.
Lemma lem7586317 (c : nat -> real) (m : nat) (P : type1028) (h1 : term482 P m) (h2 : term340 P) (h3 : term337 P) : term619 P m c.
Proof. exact (EQ_MP (@lem7586316 c m P h1 h2 h3) (@lem0)). Qed.
Lemma lem7586318 (c : nat -> real) (m : nat) (P : type1028) (h1 : term482 P m) (h2 : term340 P) (h3 : term337 P) : term593 P m c.
Proof. exact (EQ_MP (@lem7586222 P m c) (@lem7586317 c m P h1 h2 h3)). Qed.
Lemma lem7586319 (c : nat -> real) (m : nat) (P : type1028) (h1 : term482 P m) (h2 : term340 P) (h3 : term337 P) : term579 P m c.
Proof. exact (EQ_MP (@lem7586149 P m c) (@lem7586318 c m P h1 h2 h3)). Qed.
Lemma lem7586320 (c : nat -> real) (m : nat) (P : type1028) (h1 : term482 P m) (h2 : term340 P) (h3 : term339 P) (h4 : term337 P) : term580 P m c.
Proof. exact (EQ_MP (@lem7586125 m c P h3) (@lem7586319 c m P h1 h2 h4)). Qed.
Lemma lem7586321 (c : nat -> real) (m : nat) (P : type1028) (h1 : term482 P m) (h2 : term341 P) (h3 : term340 P) (h4 : term339 P) (h5 : term337 P) : term557 P m c.
Proof. exact (@lem7586053 m c P h2 (@lem7586320 c m P h1 h3 h4 h5)). Qed.
Lemma lem7586322 (c : nat -> real) (m : nat) (P : type1028) (h1 : term482 P m) (h2 : term341 P) (h3 : term340 P) (h4 : term339 P) (h5 : term337 P) : term556 P m c.
Proof. exact (EQ_MP (@lem7585991 P m c) (@lem7586321 c m P h1 h2 h3 h4 h5)). Qed.
Lemma lem7586328 (m : nat) (P : type1028) (h1 : term482 P m) (h2 : term341 P) (h3 : term340 P) (h4 : term339 P) (h5 : term337 P) : term495 P m.
Proof. exact (fun c : nat -> real => @lem7586322 c m P h1 h2 h3 h4 h5). Qed.
Lemma lem7586329 (m : nat) (P : type1028) (h1 : term341 P) (h2 : term340 P) (h3 : term339 P) (h4 : term337 P) : term497 P m.
Proof. exact (fun h0 : term482 P m => @lem7586328 m P h0 h1 h2 h3 h4). Qed.
Lemma lem7586334 (P : type1028) (h1 : term341 P) (h2 : term340 P) (h3 : term339 P) (h4 : term337 P) : term501 P.
Proof. exact (fun m : nat => @lem7586329 m P h1 h2 h3 h4). Qed.
Lemma lem7586335 (P : type1028) (h1 : term341 P) (h2 : term340 P) (h3 : term339 P) (h4 : term337 P) : term503 P.
Proof. exact (conj (@lem7585298 P h3) (@lem7586334 P h1 h2 h3 h4)). Qed.
Lemma lem7586336 (P : type1028) (h1 : term341 P) (h2 : term340 P) (h3 : term339 P) (h4 : term337 P) : term484 P.
Proof. exact (@lem7585213 P (@lem7586335 P h1 h2 h3 h4)). Qed.
Lemma lem7586337 (P : type1028) (h1 : term341 P) (h2 : term340 P) (h3 : term339 P) (h4 : term337 P) : term436 P.
Proof. exact (EQ_MP (@lem7585190 P) (@lem7586336 P h1 h2 h3 h4)). Qed.
Lemma lem7586338 (P : type1028) (h1 : term341 P) (h2 : term340 P) (h3 : term339 P) (h4 : term337 P) : term418 P.
Proof. exact (EQ_MP (@lem7583033 P) (@lem7586337 P h1 h2 h3 h4)). Qed.
Lemma lem7586339 (P : type1028) (h1 : term341 P) (h2 : term340 P) (h3 : term339 P) (h4 : term337 P) : term389 P.
Proof. exact (EQ_MP (@lem7582990 P) (@lem7586338 P h1 h2 h3 h4)). Qed.
Lemma lem7586340 (P : type1028) (h1 : term341 P) (h2 : term340 P) (h3 : term339 P) (h4 : term337 P) : term388 P.
Proof. exact (EQ_MP (@lem7582945 P) (@lem7586339 P h1 h2 h3 h4)). Qed.
Lemma lem7586341 (P : type1028) (h1 : term335 P) : term336 P.
Proof. exact (proj2 (@lem7582832 P h1)). Qed.
Lemma lem7586342 (P : type1028) (h1 : term335 P) : term337 P.
Proof. exact (proj1 (@lem7582832 P h1)). Qed.
Lemma lem7586343 (P : type1028) (h1 : term336 P) : term338 P.
Proof. exact (proj2 (@lem7582833 P h1)). Qed.
Lemma lem7586344 (P : type1028) (h1 : term336 P) : term339 P.
Proof. exact (proj1 (@lem7582833 P h1)). Qed.
Lemma lem7586345 (P : type1028) (h1 : term338 P) : term340 P.
Proof. exact (proj2 (@lem7582835 P h1)). Qed.
Lemma lem7586346 (P : type1028) (h1 : term338 P) : term341 P.
Proof. exact (proj1 (@lem7582835 P h1)). Qed.
Lemma lem7586347 (P : type1028) (h1 : term341 P) (h2 : term340 P) (h3 : term339 P) (h4 : term337 P) : (term340 P) = (term388 P).
Proof. exact (prop_ext (fun h5 : term340 P => @lem7586340 P h1 h2 h3 h4) (fun h5 : term388 P => @lem7582837 P h2)). Qed.
Lemma lem7586348 (P : type1028) (h1 : term341 P) (h2 : term340 P) (h3 : term339 P) (h4 : term337 P) : term388 P.
Proof. exact (EQ_MP (@lem7586347 P h1 h2 h3 h4) (@lem7582837 P h2)). Qed.
Lemma lem7586349 (P : type1028) (h1 : term341 P) (h2 : term340 P) (h3 : term339 P) (h4 : term337 P) : (term341 P) = (term388 P).
Proof. exact (prop_ext (fun h5 : term341 P => @lem7586348 P h1 h2 h3 h4) (fun h5 : term388 P => @lem7582838 P h1)). Qed.
Lemma lem7586350 (P : type1028) (h1 : term341 P) (h2 : term340 P) (h3 : term339 P) (h4 : term337 P) : term388 P.
Proof. exact (EQ_MP (@lem7586349 P h1 h2 h3 h4) (@lem7582838 P h1)). Qed.
Lemma lem7586351 (P : type1028) (h1 : term341 P) (h2 : term339 P) (h3 : term337 P) (h4 : term338 P) : (term340 P) = (term388 P).
Proof. exact (prop_ext (fun h5 : term340 P => @lem7586350 P h1 h5 h2 h3) (fun h5 : term388 P => @lem7586345 P h4)). Qed.
Lemma lem7586352 (P : type1028) (h1 : term341 P) (h2 : term339 P) (h3 : term337 P) (h4 : term338 P) : term388 P.
Proof. exact (EQ_MP (@lem7586351 P h1 h2 h3 h4) (@lem7586345 P h4)). Qed.
Lemma lem7586353 (P : type1028) (h1 : term339 P) (h2 : term337 P) (h3 : term338 P) : (term341 P) = (term388 P).
Proof. exact (prop_ext (fun h4 : term341 P => @lem7586352 P h4 h1 h2 h3) (fun h4 : term388 P => @lem7586346 P h3)). Qed.
Lemma lem7586354 (P : type1028) (h1 : term339 P) (h2 : term337 P) (h3 : term338 P) : term388 P.
Proof. exact (EQ_MP (@lem7586353 P h1 h2 h3) (@lem7586346 P h3)). Qed.
Lemma lem7586355 (P : type1028) (h1 : term339 P) (h2 : term337 P) (h3 : term338 P) : (term339 P) = (term388 P).
Proof. exact (prop_ext (fun h4 : term339 P => @lem7586354 P h1 h2 h3) (fun h4 : term388 P => @lem7582836 P h1)). Qed.
Lemma lem7586356 (P : type1028) (h1 : term339 P) (h2 : term337 P) (h3 : term338 P) : term388 P.
Proof. exact (EQ_MP (@lem7586355 P h1 h2 h3) (@lem7582836 P h1)). Qed.
Lemma lem7586357 (P : type1028) (h1 : term339 P) (h2 : term337 P) (h3 : term336 P) : (term338 P) = (term388 P).
Proof. exact (prop_ext (fun h4 : term338 P => @lem7586356 P h1 h2 h4) (fun h4 : term388 P => @lem7586343 P h3)). Qed.
Lemma lem7586358 (P : type1028) (h1 : term339 P) (h2 : term337 P) (h3 : term336 P) : term388 P.
Proof. exact (EQ_MP (@lem7586357 P h1 h2 h3) (@lem7586343 P h3)). Qed.
Lemma lem7586359 (P : type1028) (h1 : term337 P) (h2 : term336 P) : (term339 P) = (term388 P).
Proof. exact (prop_ext (fun h3 : term339 P => @lem7586358 P h3 h1 h2) (fun h3 : term388 P => @lem7586344 P h2)). Qed.
Lemma lem7586360 (P : type1028) (h1 : term337 P) (h2 : term336 P) : term388 P.
Proof. exact (EQ_MP (@lem7586359 P h1 h2) (@lem7586344 P h2)). Qed.
Lemma lem7586361 (P : type1028) (h1 : term337 P) (h2 : term336 P) : (term337 P) = (term388 P).
Proof. exact (prop_ext (fun h3 : term337 P => @lem7586360 P h1 h2) (fun h3 : term388 P => @lem7582834 P h1)). Qed.
Lemma lem7586362 (P : type1028) (h1 : term337 P) (h2 : term336 P) : term388 P.
Proof. exact (EQ_MP (@lem7586361 P h1 h2) (@lem7582834 P h1)). Qed.
Lemma lem7586363 (P : type1028) (h1 : term337 P) (h2 : term335 P) : (term336 P) = (term388 P).
Proof. exact (prop_ext (fun h3 : term336 P => @lem7586362 P h1 h3) (fun h3 : term388 P => @lem7586341 P h2)). Qed.
Lemma lem7586364 (P : type1028) (h1 : term337 P) (h2 : term335 P) : term388 P.
Proof. exact (EQ_MP (@lem7586363 P h1 h2) (@lem7586341 P h2)). Qed.
Lemma lem7586365 (P : type1028) (h1 : term335 P) : (term337 P) = (term388 P).
Proof. exact (prop_ext (fun h2 : term337 P => @lem7586364 P h2 h1) (fun h2 : term388 P => @lem7586342 P h1)). Qed.
Lemma lem7586366 (P : type1028) (h1 : term335 P) : term388 P.
Proof. exact (EQ_MP (@lem7586365 P h1) (@lem7586342 P h1)). Qed.
Lemma lem7586367 (P : type1028) : term655 P.
Proof. exact (fun h0 : term335 P => @lem7586366 P h0). Qed.
Lemma lem7586372 : term656.
Proof. exact (fun P : type1028 => @lem7586367 P). Qed.
