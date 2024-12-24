Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POLYFUN_FINITE_ROOTS_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import CONTRAPOS_THM_spec.
Require Import INFINITE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_FORALL_THM_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_POLYFUN_ROOTBOUND_spec.
Require Import SUM_0_spec.
Require Import real_INFINITE_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm7261449_spec.
Require Import thm7261450_spec.
Require Import thm82_spec.
Lemma lem7537925 {A : Type'} (s : A -> Prop) (h1 : (@INFINITE A s) = (term0 A s)) : (@INFINITE A s) = (term0 A s).
Proof. exact (h1). Qed.
Lemma lem7537926 {A : Type'} (s : A -> Prop) (h1 : (@INFINITE A s) = (term0 A s)) : (term0 A s) = (@INFINITE A s).
Proof. exact (SYM (@lem7537925 A s h1)). Qed.
Lemma lem7537927 {A : Type'} (s : A -> Prop) (h1 : (term0 A s) = (@INFINITE A s)) : (term0 A s) = (@INFINITE A s).
Proof. exact (h1). Qed.
Lemma lem7537928 {A : Type'} (s : A -> Prop) (h1 : (term0 A s) = (@INFINITE A s)) : (@INFINITE A s) = (term0 A s).
Proof. exact (SYM (@lem7537927 A s h1)). Qed.
Lemma lem7537929 {A : Type'} (s : A -> Prop) : ((@INFINITE A s) = (term0 A s)) = ((term0 A s) = (@INFINITE A s)).
Proof. exact (prop_ext (fun h1 : (@INFINITE A s) = (term0 A s) => @lem7537926 A s h1) (fun h1 : (term0 A s) = (@INFINITE A s) => @lem7537928 A s h1)). Qed.
Lemma lem7537930 {A : Type'} : (term1 A) = (term2 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7537929 A s)). Qed.
Lemma lem7537931 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7537932 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (MK_COMB (@lem7537931 A) (@lem7537930 A)). Qed.
Lemma lem7537933 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem7537932 A) (@lem3198543 A)). Qed.
Lemma lem7537947 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term5 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7537948 (s : real -> Prop) (t : real -> Prop) : (s = t) = (term6 s t).
Proof. exact (@lem7537947 real s t). Qed.
Lemma lem7537949 : (term7 = (@UNIV real)) = term8.
Proof. exact (@lem7537948 term7 (@UNIV real)). Qed.
Lemma lem7537962 : term8 = (term7 = (@UNIV real)).
Proof. exact (SYM (@lem7537949)). Qed.
Lemma lem7537970 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term9 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem7537971 (p : real -> Prop) (x : real) : (term10 x p) = (p x).
Proof. exact (@lem7537970 real p x). Qed.
Lemma lem7537972 (x : real) : (term11 x) = (term12 x).
Proof. exact (@lem7537971 term13 x). Qed.
Lemma lem7537973 (x : real) : (term12 x) = True.
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem7537974 (GEN_PVAR_347 : real) : (@SETSPEC real GEN_PVAR_347) = (@SETSPEC real GEN_PVAR_347).
Proof. exact (eq_refl (@SETSPEC real GEN_PVAR_347)). Qed.
Lemma lem7537975 (x : real) (GEN_PVAR_347 : real) : (term14 GEN_PVAR_347 x) = (@SETSPEC real GEN_PVAR_347 True).
Proof. exact (MK_COMB (@lem7537974 GEN_PVAR_347) (@lem7537973 x)). Qed.
Lemma lem7537976 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7537977 (GEN_PVAR_347 : real) (x : real) : (term15 GEN_PVAR_347 x) = (@SETSPEC real GEN_PVAR_347 True x).
Proof. exact (MK_COMB (@lem7537975 x GEN_PVAR_347) (@lem7537976 x)). Qed.
Lemma lem7537978 (GEN_PVAR_347 : real) : (term16 GEN_PVAR_347) = (term17 GEN_PVAR_347).
Proof. exact (fun_ext (fun x : real => @lem7537977 GEN_PVAR_347 x)). Qed.
Lemma lem7537979 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7537980 (GEN_PVAR_347 : real) : (term18 GEN_PVAR_347) = (term19 GEN_PVAR_347).
Proof. exact (MK_COMB (@lem7537979) (@lem7537978 GEN_PVAR_347)). Qed.
Lemma lem7537981 : term20 = term21.
Proof. exact (fun_ext (fun GEN_PVAR_347 : real => @lem7537980 GEN_PVAR_347)). Qed.
Lemma lem7537982 : (@GSPEC real) = (@GSPEC real).
Proof. exact (eq_refl (@GSPEC real)). Qed.
Lemma lem7537983 : term22 = term7.
Proof. exact (MK_COMB (@lem7537982) (@lem7537981)). Qed.
Lemma lem7537984 (x : real) : (@IN real x) = (@IN real x).
Proof. exact (eq_refl (@IN real x)). Qed.
Lemma lem7537985 (x : real) : (term11 x) = (term23 x).
Proof. exact (MK_COMB (@lem7537984 x) (@lem7537983)). Qed.
Lemma lem7537986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7537987 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem7537986) (@lem7537985 x)). Qed.
Lemma lem7537988 (x : real) : (term12 x) = True.
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem7537989 (x : real) : ((term11 x) = (term12 x)) = ((term23 x) = True).
Proof. exact (MK_COMB (@lem7537987 x) (@lem7537988 x)). Qed.
Lemma lem7537990 (x : real) : (term23 x) = True.
Proof. exact (EQ_MP (@lem7537989 x) (@lem7537972 x)). Qed.
Lemma lem7537991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7537992 (x : real) : (term25 x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem7537991) (@lem7537990 x)). Qed.
Lemma lem7537994 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem7537995 (x : real) : (@IN real x (@UNIV real)) = True.
Proof. exact (@lem7537994 real x). Qed.
Lemma lem7537996 (x : real) : ((term23 x) = (@IN real x (@UNIV real))) = (True = True).
Proof. exact (MK_COMB (@lem7537992 x) (@lem7537995 x)). Qed.
Lemma lem7537998 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem7537999 : (True = True) = True.
Proof. exact (@lem7537998 True). Qed.
Lemma lem7538000 (x : real) : ((term23 x) = (@IN real x (@UNIV real))) = True.
Proof. exact (TRANS (@lem7537996 x) (@lem7537999)). Qed.
Lemma lem7538001 : term26 = term13.
Proof. exact (fun_ext (fun x : real => @lem7538000 x)). Qed.
Lemma lem7538002 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7538003 : term8 = term27.
Proof. exact (MK_COMB (@lem7538002) (@lem7538001)). Qed.
Lemma lem7538005 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7538006 (t : Prop) : (term29 t) = t.
Proof. exact (@lem7538005 real t). Qed.
Lemma lem7538007 : term27 = True.
Proof. exact (@lem7538006 True). Qed.
Lemma lem7538008 : term8 = True.
Proof. exact (TRANS (@lem7538003) (@lem7538007)). Qed.
Lemma lem7538009 : True = term8.
Proof. exact (SYM (@lem7538008)). Qed.
Lemma lem7538010 : term8.
Proof. exact (EQ_MP (@lem7538009) (@lem0)). Qed.
Lemma lem7538012 {A : Type'} (s : A -> Prop) : term30 A s.
Proof. exact (@lem7537933 A s). Qed.
Lemma lem7538013 {A : Type'} (s : A -> Prop) : (term30 A s) = ((term0 A s) = (@INFINITE A s)).
Proof. exact (eq_refl (term30 A s)). Qed.
Lemma lem7538015 : (@INFINITE real (@UNIV real)) = ((@INFINITE real (@UNIV real)) = True).
Proof. exact (@lem7 (@INFINITE real (@UNIV real))). Qed.
Lemma lem7538017 {A : Type'} (s : A -> Prop) : term31 A s.
Proof. exact (@lem7069399 A s). Qed.
Lemma lem7538018 {A : Type'} (s : A -> Prop) : (term31 A s) = ((term32 A s) = term33).
Proof. exact (eq_refl (term31 A s)). Qed.
Lemma lem7538020 (x : real) : term34 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem7538021 (x : real) : (term34 x) = ((term35 x) = term33).
Proof. exact (eq_refl (term34 x)). Qed.
Lemma lem7538025 (t2 : Prop) (t1 : Prop) (h1 : (term36 t1 t2) = (t2 -> t1)) : (term36 t1 t2) = (t2 -> t1).
Proof. exact (h1). Qed.
Lemma lem7538026 (t2 : Prop) (t1 : Prop) (h1 : (term36 t1 t2) = (t2 -> t1)) : (t2 -> t1) = (term36 t1 t2).
Proof. exact (SYM (@lem7538025 t2 t1 h1)). Qed.
Lemma lem7538027 (t1 : Prop) (t2 : Prop) (h1 : (t2 -> t1) = (term36 t1 t2)) : (t2 -> t1) = (term36 t1 t2).
Proof. exact (h1). Qed.
Lemma lem7538028 (t1 : Prop) (t2 : Prop) (h1 : (t2 -> t1) = (term36 t1 t2)) : (term36 t1 t2) = (t2 -> t1).
Proof. exact (SYM (@lem7538027 t1 t2 h1)). Qed.
Lemma lem7538029 (t1 : Prop) (t2 : Prop) : ((term36 t1 t2) = (t2 -> t1)) = ((t2 -> t1) = (term36 t1 t2)).
Proof. exact (prop_ext (fun h1 : (term36 t1 t2) = (t2 -> t1) => @lem7538026 t2 t1 h1) (fun h1 : (t2 -> t1) = (term36 t1 t2) => @lem7538028 t1 t2 h1)). Qed.
Lemma lem7538030 (t1 : Prop) : (term37 t1) = (term38 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem7538029 t1 t2)). Qed.
Lemma lem7538031 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem7538032 (t1 : Prop) : (term39 t1) = (term40 t1).
Proof. exact (MK_COMB (@lem7538031) (@lem7538030 t1)). Qed.
Lemma lem7538033 : term41 = term42.
Proof. exact (fun_ext (fun t1 : Prop => @lem7538032 t1)). Qed.
Lemma lem7538034 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem7538035 : term43 = term44.
Proof. exact (MK_COMB (@lem7538034) (@lem7538033)). Qed.
Lemma lem7538036 : term44.
Proof. exact (EQ_MP (@lem7538035) (@lem10414)). Qed.
Lemma lem7538037 (t1 : Prop) : term45 t1.
Proof. exact (@lem7538036 t1). Qed.
Lemma lem7538038 (t1 : Prop) : (term45 t1) = (term40 t1).
Proof. exact (eq_refl (term45 t1)). Qed.
Lemma lem7538039 (t1 : Prop) : term40 t1.
Proof. exact (EQ_MP (@lem7538038 t1) (@lem7538037 t1)). Qed.
Lemma lem7538040 (t1 : Prop) (t2 : Prop) : term46 t1 t2.
Proof. exact (@lem7538039 t1 t2). Qed.
Lemma lem7538041 (t1 : Prop) (t2 : Prop) : (term46 t1 t2) = ((t2 -> t1) = (term36 t1 t2)).
Proof. exact (eq_refl (term46 t1 t2)). Qed.
Lemma lem7538043 (n : nat) : term47 n.
Proof. exact (@lem7537923 n). Qed.
Lemma lem7538044 (n : nat) : (term47 n) = (term48 n).
Proof. exact (eq_refl (term47 n)). Qed.
Lemma lem7538045 (n : nat) : term48 n.
Proof. exact (EQ_MP (@lem7538044 n) (@lem7538043 n)). Qed.
Lemma lem7538046 (n : nat) (c : nat -> real) : term49 n c.
Proof. exact (@lem7538045 n c). Qed.
Lemma lem7538047 (c : nat -> real) (n : nat) : (term49 n c) = (term50 c n).
Proof. exact (eq_refl (term49 n c)). Qed.
Lemma lem7538048 (c : nat -> real) (n : nat) : term50 c n.
Proof. exact (EQ_MP (@lem7538047 c n) (@lem7538046 n c)). Qed.
Lemma lem7538049 (n : nat) (c : nat -> real) (h1 : term51 n c) : term51 n c.
Proof. exact (h1). Qed.
Lemma lem7538050 (n : nat) (c : nat -> real) (h1 : term51 n c) : term52 c n.
Proof. exact (@lem7538048 c n (@lem7538049 n c h1)). Qed.
Lemma lem7538059 (n : nat) (c : nat -> real) (h1 : term51 n c) : term53 n c.
Proof. exact (proj1 (@lem7538050 n c h1)). Qed.
Lemma lem7538060 (n : nat) (c : nat -> real) : (term53 n c) = ((term53 n c) = True).
Proof. exact (@lem7 (term53 n c)). Qed.
Lemma lem7538061 (n : nat) (c : nat -> real) (h1 : term51 n c) : (term53 n c) = True.
Proof. exact (EQ_MP (@lem7538060 n c) (@lem7538059 n c h1)). Qed.
Lemma lem7538068 {A : Type'} (P : A -> Prop) (h1 : (term54 A P) = (term55 A P)) : (term54 A P) = (term55 A P).
Proof. exact (h1). Qed.
Lemma lem7538069 {A : Type'} (P : A -> Prop) (h1 : (term54 A P) = (term55 A P)) : (term55 A P) = (term54 A P).
Proof. exact (SYM (@lem7538068 A P h1)). Qed.
Lemma lem7538070 {A : Type'} (P : A -> Prop) (h1 : (term55 A P) = (term54 A P)) : (term55 A P) = (term54 A P).
Proof. exact (h1). Qed.
Lemma lem7538071 {A : Type'} (P : A -> Prop) (h1 : (term55 A P) = (term54 A P)) : (term54 A P) = (term55 A P).
Proof. exact (SYM (@lem7538070 A P h1)). Qed.
Lemma lem7538072 {A : Type'} (P : A -> Prop) : ((term54 A P) = (term55 A P)) = ((term55 A P) = (term54 A P)).
Proof. exact (prop_ext (fun h1 : (term54 A P) = (term55 A P) => @lem7538069 A P h1) (fun h1 : (term55 A P) = (term54 A P) => @lem7538071 A P h1)). Qed.
Lemma lem7538073 {A : Type'} : (term56 A) = (term57 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem7538072 A P)). Qed.
Lemma lem7538074 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7538075 {A : Type'} : (term58 A) = (term59 A).
Proof. exact (MK_COMB (@lem7538074 A) (@lem7538073 A)). Qed.
Lemma lem7538076 {A : Type'} : term59 A.
Proof. exact (EQ_MP (@lem7538075 A) (@lem10884 A)). Qed.
Lemma lem7538077 {A : Type'} (P : A -> Prop) : term60 A P.
Proof. exact (@lem7538076 A P). Qed.
Lemma lem7538078 {A : Type'} (P : A -> Prop) : (term60 A P) = ((term55 A P) = (term54 A P)).
Proof. exact (eq_refl (term60 A P)). Qed.
Lemma lem7538088 (a : Prop) : term61 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem7538089 (a : Prop) : (term61 a) = (term62 a).
Proof. exact (eq_refl (term61 a)). Qed.
Lemma lem7538090 (a : Prop) : term62 a.
Proof. exact (EQ_MP (@lem7538089 a) (@lem7538088 a)). Qed.
Lemma lem7538091 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem7538092 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem7538101 (b : Prop) : (term63 b) = (term63 b).
Proof. exact (eq_refl (term63 b)). Qed.
Lemma lem7538102 (b : Prop) (a : Prop) (h1 : a = True) : (term64 b a) = (term65 b).
Proof. exact (MK_COMB (@lem7538101 b) (@lem7538091 a h1)). Qed.
Lemma lem7538103 (b : Prop) : (term65 b) = ((term66 b) = (term67 b)).
Proof. exact (eq_refl (term65 b)). Qed.
Lemma lem7538104 (b : Prop) (a : Prop) : (term68 b a) = (term68 b a).
Proof. exact (eq_refl (term68 b a)). Qed.
Lemma lem7538105 (a : Prop) (b : Prop) : ((term64 b a) = (term65 b)) = ((term64 b a) = ((term66 b) = (term67 b))).
Proof. exact (MK_COMB (@lem7538104 b a) (@lem7538103 b)). Qed.
Lemma lem7538106 (a : Prop) (b : Prop) : (term64 b a) = ((term69 a b) = (term70 a b)).
Proof. exact (eq_refl (term64 b a)). Qed.
Lemma lem7538107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7538108 (a : Prop) (b : Prop) : (term68 b a) = (term71 a b).
Proof. exact (MK_COMB (@lem7538107) (@lem7538106 a b)). Qed.
Lemma lem7538109 (b : Prop) : ((term66 b) = (term67 b)) = ((term66 b) = (term67 b)).
Proof. exact (eq_refl ((term66 b) = (term67 b))). Qed.
Lemma lem7538110 (a : Prop) (b : Prop) : ((term64 b a) = ((term66 b) = (term67 b))) = (((term69 a b) = (term70 a b)) = ((term66 b) = (term67 b))).
Proof. exact (MK_COMB (@lem7538108 a b) (@lem7538109 b)). Qed.
Lemma lem7538111 (a : Prop) (b : Prop) : ((term64 b a) = (term65 b)) = (((term69 a b) = (term70 a b)) = ((term66 b) = (term67 b))).
Proof. exact (TRANS (@lem7538105 a b) (@lem7538110 a b)). Qed.
Lemma lem7538112 (b : Prop) (a : Prop) (h1 : a = True) : ((term69 a b) = (term70 a b)) = ((term66 b) = (term67 b)).
Proof. exact (EQ_MP (@lem7538111 a b) (@lem7538102 b a h1)). Qed.
Lemma lem7538113 (b : Prop) (a : Prop) (h1 : a = True) : ((term66 b) = (term67 b)) = ((term69 a b) = (term70 a b)).
Proof. exact (SYM (@lem7538112 b a h1)). Qed.
Lemma lem7538114 (b : Prop) : (term63 b) = (term63 b).
Proof. exact (eq_refl (term63 b)). Qed.
Lemma lem7538115 (b : Prop) (a : Prop) (h1 : a = False) : (term64 b a) = (term72 b).
Proof. exact (MK_COMB (@lem7538114 b) (@lem7538092 a h1)). Qed.
Lemma lem7538116 (b : Prop) : (term72 b) = ((term73 b) = (term74 b)).
Proof. exact (eq_refl (term72 b)). Qed.
Lemma lem7538117 (b : Prop) (a : Prop) : (term68 b a) = (term68 b a).
Proof. exact (eq_refl (term68 b a)). Qed.
Lemma lem7538118 (a : Prop) (b : Prop) : ((term64 b a) = (term72 b)) = ((term64 b a) = ((term73 b) = (term74 b))).
Proof. exact (MK_COMB (@lem7538117 b a) (@lem7538116 b)). Qed.
Lemma lem7538119 (a : Prop) (b : Prop) : (term64 b a) = ((term69 a b) = (term70 a b)).
Proof. exact (eq_refl (term64 b a)). Qed.
Lemma lem7538120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7538121 (a : Prop) (b : Prop) : (term68 b a) = (term71 a b).
Proof. exact (MK_COMB (@lem7538120) (@lem7538119 a b)). Qed.
Lemma lem7538122 (b : Prop) : ((term73 b) = (term74 b)) = ((term73 b) = (term74 b)).
Proof. exact (eq_refl ((term73 b) = (term74 b))). Qed.
Lemma lem7538123 (a : Prop) (b : Prop) : ((term64 b a) = ((term73 b) = (term74 b))) = (((term69 a b) = (term70 a b)) = ((term73 b) = (term74 b))).
Proof. exact (MK_COMB (@lem7538121 a b) (@lem7538122 b)). Qed.
Lemma lem7538124 (a : Prop) (b : Prop) : ((term64 b a) = (term72 b)) = (((term69 a b) = (term70 a b)) = ((term73 b) = (term74 b))).
Proof. exact (TRANS (@lem7538118 a b) (@lem7538123 a b)). Qed.
Lemma lem7538125 (b : Prop) (a : Prop) (h1 : a = False) : ((term69 a b) = (term70 a b)) = ((term73 b) = (term74 b)).
Proof. exact (EQ_MP (@lem7538124 a b) (@lem7538115 b a h1)). Qed.
Lemma lem7538126 (b : Prop) (a : Prop) (h1 : a = False) : ((term73 b) = (term74 b)) = ((term69 a b) = (term70 a b)).
Proof. exact (SYM (@lem7538125 b a h1)). Qed.
Lemma lem7538130 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7538131 (b : Prop) : (term66 b) = (~ b).
Proof. exact (@lem7538130 (~ b)). Qed.
Lemma lem7538132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7538133 (b : Prop) : (term75 b) = (term76 b).
Proof. exact (MK_COMB (@lem7538132) (@lem7538131 b)). Qed.
Lemma lem7538135 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7538136 (b : Prop) : (True -> b) = b.
Proof. exact (@lem7538135 b). Qed.
Lemma lem7538137 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7538138 (b : Prop) : (term67 b) = (~ b).
Proof. exact (MK_COMB (@lem7538137) (@lem7538136 b)). Qed.
Lemma lem7538139 (b : Prop) : ((term66 b) = (term67 b)) = ((~ b) = (~ b)).
Proof. exact (MK_COMB (@lem7538133 b) (@lem7538138 b)). Qed.
Lemma lem7538141 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7538142 (x : Prop) : (x = x) = True.
Proof. exact (@lem7538141 Prop x). Qed.
Lemma lem7538143 (b : Prop) : ((~ b) = (~ b)) = True.
Proof. exact (@lem7538142 (~ b)). Qed.
Lemma lem7538144 (b : Prop) : ((term66 b) = (term67 b)) = True.
Proof. exact (TRANS (@lem7538139 b) (@lem7538143 b)). Qed.
Lemma lem7538145 (b : Prop) : True = ((term66 b) = (term67 b)).
Proof. exact (SYM (@lem7538144 b)). Qed.
Lemma lem7538146 (b : Prop) : (term66 b) = (term67 b).
Proof. exact (EQ_MP (@lem7538145 b) (@lem0)). Qed.
Lemma lem7538150 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem7538151 (b : Prop) : (term73 b) = False.
Proof. exact (@lem7538150 (~ b)). Qed.
Lemma lem7538152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7538153 (b : Prop) : (term77 b) = (@eq Prop False).
Proof. exact (MK_COMB (@lem7538152) (@lem7538151 b)). Qed.
Lemma lem7538155 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem7538156 (b : Prop) : (False -> b) = True.
Proof. exact (@lem7538155 b). Qed.
Lemma lem7538157 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7538158 (b : Prop) : (term74 b) = (~ True).
Proof. exact (MK_COMB (@lem7538157) (@lem7538156 b)). Qed.
Lemma lem7538160 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem7538161 (b : Prop) : (term74 b) = False.
Proof. exact (TRANS (@lem7538158 b) (@lem7538160)). Qed.
Lemma lem7538162 (b : Prop) : ((term73 b) = (term74 b)) = (False = False).
Proof. exact (MK_COMB (@lem7538153 b) (@lem7538161 b)). Qed.
Lemma lem7538164 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem7538165 : (False = False) = (~ False).
Proof. exact (@lem7538164 False). Qed.
Lemma lem7538167 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7538168 : (False = False) = True.
Proof. exact (TRANS (@lem7538165) (@lem7538167)). Qed.
Lemma lem7538169 (b : Prop) : ((term73 b) = (term74 b)) = True.
Proof. exact (TRANS (@lem7538162 b) (@lem7538168)). Qed.
Lemma lem7538170 (b : Prop) : True = ((term73 b) = (term74 b)).
Proof. exact (SYM (@lem7538169 b)). Qed.
Lemma lem7538171 (b : Prop) : (term73 b) = (term74 b).
Proof. exact (EQ_MP (@lem7538170 b) (@lem0)). Qed.
Lemma lem7538172 (b : Prop) (a : Prop) (h1 : a = False) : (term69 a b) = (term70 a b).
Proof. exact (EQ_MP (@lem7538126 b a h1) (@lem7538171 b)). Qed.
Lemma lem7538173 (b : Prop) (a : Prop) (h1 : a = True) : (term69 a b) = (term70 a b).
Proof. exact (EQ_MP (@lem7538113 b a h1) (@lem7538146 b)). Qed.
Lemma lem7538190 (a : Prop) (b : Prop) : (term69 a b) = (term70 a b).
Proof. exact (or_elim (@lem7538090 a) (fun h0 : a = True => @lem7538173 b a h0) (fun h0 : a = False => @lem7538172 b a h0)). Qed.
Lemma lem7538191 (n : nat) (c : nat -> real) (i : nat) : (term78 n c i) = (term79 n c i).
Proof. exact (@lem7538190 (term80 i n) ((c i) = term33)). Qed.
Lemma lem7538196 (n : nat) (c : nat -> real) : (term81 n c) = (term82 n c).
Proof. exact (fun_ext (fun i : nat => @lem7538191 n c i)). Qed.
Lemma lem7538197 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7538198 (n : nat) (c : nat -> real) : (term83 n c) = (term84 n c).
Proof. exact (MK_COMB (@lem7538197) (@lem7538196 n c)). Qed.
Lemma lem7538203 (n : nat) (c : nat -> real) : (term85 n c) = (term85 n c).
Proof. exact (eq_refl (term85 n c)). Qed.
Lemma lem7538204 (n : nat) (c : nat -> real) : ((term53 n c) = (term83 n c)) = ((term53 n c) = (term84 n c)).
Proof. exact (MK_COMB (@lem7538203 n c) (@lem7538198 n c)). Qed.
Lemma lem7538207 (n : nat) (c : nat -> real) : ((term53 n c) = (term84 n c)) = ((term53 n c) = (term83 n c)).
Proof. exact (SYM (@lem7538204 n c)). Qed.
Lemma lem7538217 {A : Type'} (P : A -> Prop) : (term55 A P) = (term54 A P).
Proof. exact (EQ_MP (@lem7538078 A P) (@lem7538077 A P)). Qed.
Lemma lem7538218 (P : nat -> Prop) : (term86 P) = (term87 P).
Proof. exact (@lem7538217 nat P). Qed.
Lemma lem7538219 (n : nat) (c : nat -> real) : (term88 n c) = (term89 n c).
Proof. exact (@lem7538218 (term90 n c)). Qed.
Lemma lem7538220 (n : nat) (c : nat -> real) (i : nat) : (term91 n c i) = (term92 n c i).
Proof. exact (eq_refl (term91 n c i)). Qed.
Lemma lem7538221 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7538222 (n : nat) (c : nat -> real) (i : nat) : (term93 n c i) = (term79 n c i).
Proof. exact (MK_COMB (@lem7538221) (@lem7538220 n c i)). Qed.
Lemma lem7538223 (n : nat) (c : nat -> real) : (term94 n c) = (term82 n c).
Proof. exact (fun_ext (fun i : nat => @lem7538222 n c i)). Qed.
Lemma lem7538224 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7538225 (n : nat) (c : nat -> real) : (term88 n c) = (term84 n c).
Proof. exact (MK_COMB (@lem7538224) (@lem7538223 n c)). Qed.
Lemma lem7538226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7538227 (n : nat) (c : nat -> real) : (term95 n c) = (term96 n c).
Proof. exact (MK_COMB (@lem7538226) (@lem7538225 n c)). Qed.
Lemma lem7538228 (n : nat) (c : nat -> real) (i : nat) : (term91 n c i) = (term92 n c i).
Proof. exact (eq_refl (term91 n c i)). Qed.
Lemma lem7538229 (n : nat) (c : nat -> real) : (term97 n c) = (term90 n c).
Proof. exact (fun_ext (fun i : nat => @lem7538228 n c i)). Qed.
Lemma lem7538230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7538231 (n : nat) (c : nat -> real) : (term98 n c) = (term99 n c).
Proof. exact (MK_COMB (@lem7538230) (@lem7538229 n c)). Qed.
Lemma lem7538232 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7538233 (n : nat) (c : nat -> real) : (term89 n c) = (term51 n c).
Proof. exact (MK_COMB (@lem7538232) (@lem7538231 n c)). Qed.
Lemma lem7538234 (n : nat) (c : nat -> real) : ((term88 n c) = (term89 n c)) = ((term84 n c) = (term51 n c)).
Proof. exact (MK_COMB (@lem7538227 n c) (@lem7538233 n c)). Qed.
Lemma lem7538235 (n : nat) (c : nat -> real) : (term84 n c) = (term51 n c).
Proof. exact (EQ_MP (@lem7538234 n c) (@lem7538219 n c)). Qed.
Lemma lem7538244 (n : nat) (c : nat -> real) : (term85 n c) = (term85 n c).
Proof. exact (eq_refl (term85 n c)). Qed.
Lemma lem7538245 (n : nat) (c : nat -> real) : ((term53 n c) = (term84 n c)) = ((term53 n c) = (term51 n c)).
Proof. exact (MK_COMB (@lem7538244 n c) (@lem7538235 n c)). Qed.
Lemma lem7538248 (n : nat) (c : nat -> real) : ((term53 n c) = (term51 n c)) = ((term53 n c) = (term84 n c)).
Proof. exact (SYM (@lem7538245 n c)). Qed.
Lemma lem7538651 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term100 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7538652 (p : Prop) (q : Prop) (p' : Prop) : term101 p q p'.
Proof. exact (fun q' : Prop => @lem7538651 p q p' q'). Qed.
Lemma lem7538653 (p : Prop) (q : Prop) : term102 p q.
Proof. exact (fun p' : Prop => @lem7538652 p q p'). Qed.
Lemma lem7538654 (n : nat) (c : nat -> real) : term103 n c.
Proof. exact (@lem7538653 (term51 n c) (term53 n c)). Qed.
Lemma lem7538655 (n : nat) (c : nat -> real) (p' : Prop) : term104 n c p'.
Proof. exact (@lem7538654 n c p'). Qed.
Lemma lem7538656 (n : nat) (c : nat -> real) (p' : Prop) : (term104 n c p') = (term105 n c p').
Proof. exact (eq_refl (term104 n c p')). Qed.
Lemma lem7538657 (n : nat) (c : nat -> real) (p' : Prop) : term105 n c p'.
Proof. exact (EQ_MP (@lem7538656 n c p') (@lem7538655 n c p')). Qed.
Lemma lem7538658 (n : nat) (c : nat -> real) (p' : Prop) (q' : Prop) : term106 n c p' q'.
Proof. exact (@lem7538657 n c p' q'). Qed.
Lemma lem7538659 (n : nat) (c : nat -> real) (p' : Prop) (q' : Prop) : (term106 n c p' q') = (term107 n c p' q').
Proof. exact (eq_refl (term106 n c p' q')). Qed.
Lemma lem7538660 (n : nat) (c : nat -> real) (p' : Prop) (q' : Prop) : term107 n c p' q'.
Proof. exact (EQ_MP (@lem7538659 n c p' q') (@lem7538658 n c p' q')). Qed.
Lemma lem7538692 (n : nat) (c : nat -> real) : (term51 n c) = (term51 n c).
Proof. exact (eq_refl (term51 n c)). Qed.
Lemma lem7538693 (n : nat) (c : nat -> real) (q' : Prop) : term108 n c q'.
Proof. exact (@lem7538660 n c (term51 n c) q'). Qed.
Lemma lem7538694 (n : nat) (c : nat -> real) (q' : Prop) : term109 n c q'.
Proof. exact (@lem7538693 n c q' (@lem7538692 n c)). Qed.
Lemma lem7538695 (n : nat) (c : nat -> real) (h1 : term51 n c) : term51 n c.
Proof. exact (h1). Qed.
Lemma lem7538696 (n : nat) (c : nat -> real) : term110 n c.
Proof. exact (@lem82 (term99 n c)). Qed.
Lemma lem7538699 (n : nat) (c : nat -> real) : term111 n c.
Proof. exact (fun h0 : term51 n c => @lem7538061 n c h0). Qed.
Lemma lem7538701 (n : nat) (c : nat -> real) (h1 : term51 n c) : (term99 n c) = False.
Proof. exact (@lem7538696 n c (@lem7538695 n c h1)). Qed.
Lemma lem7538702 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7538703 (n : nat) (c : nat -> real) (h1 : term51 n c) : (term51 n c) = (~ False).
Proof. exact (MK_COMB (@lem7538702) (@lem7538701 n c h1)). Qed.
Lemma lem7538705 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7538706 (n : nat) (c : nat -> real) (h1 : term51 n c) : (term51 n c) = True.
Proof. exact (TRANS (@lem7538703 n c h1) (@lem7538705)). Qed.
Lemma lem7538707 (n : nat) (c : nat -> real) (h1 : term51 n c) : True = (term51 n c).
Proof. exact (SYM (@lem7538706 n c h1)). Qed.
Lemma lem7538708 (n : nat) (c : nat -> real) (h1 : term51 n c) : term51 n c.
Proof. exact (EQ_MP (@lem7538707 n c h1) (@lem0)). Qed.
Lemma lem7538709 (n : nat) (c : nat -> real) (h1 : term51 n c) : (term53 n c) = True.
Proof. exact (@lem7538699 n c (@lem7538708 n c h1)). Qed.
Lemma lem7538710 (n : nat) (c : nat -> real) : term111 n c.
Proof. exact (fun h0 : term51 n c => @lem7538709 n c h0). Qed.
Lemma lem7538711 (n : nat) (c : nat -> real) : term112 n c.
Proof. exact (@lem7538694 n c True). Qed.
Lemma lem7538712 (n : nat) (c : nat -> real) : (term113 n c) = (term114 n c).
Proof. exact (@lem7538711 n c (@lem7538710 n c)). Qed.
Lemma lem7538714 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7538715 (n : nat) (c : nat -> real) : (term114 n c) = True.
Proof. exact (@lem7538714 (term51 n c)). Qed.
Lemma lem7538716 (n : nat) (c : nat -> real) : (term113 n c) = True.
Proof. exact (TRANS (@lem7538712 n c) (@lem7538715 n c)). Qed.
Lemma lem7538717 (n : nat) (c : nat -> real) : True = (term113 n c).
Proof. exact (SYM (@lem7538716 n c)). Qed.
Lemma lem7538718 (n : nat) (c : nat -> real) : term113 n c.
Proof. exact (EQ_MP (@lem7538717 n c) (@lem0)). Qed.
Lemma lem7538722 (t1 : Prop) (t2 : Prop) : (t2 -> t1) = (term36 t1 t2).
Proof. exact (EQ_MP (@lem7538041 t1 t2) (@lem7538040 t1 t2)). Qed.
Lemma lem7538723 (n : nat) (c : nat -> real) : (term115 n c) = (term116 n c).
Proof. exact (@lem7538722 (term51 n c) (term53 n c)). Qed.
Lemma lem7538724 (n : nat) (c : nat -> real) : (term116 n c) = (term115 n c).
Proof. exact (SYM (@lem7538723 n c)). Qed.
Lemma lem7538728 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term100 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7538729 (p : Prop) (q : Prop) (p' : Prop) : term101 p q p'.
Proof. exact (fun q' : Prop => @lem7538728 p q p' q'). Qed.
Lemma lem7538730 (p : Prop) (q : Prop) : term102 p q.
Proof. exact (fun p' : Prop => @lem7538729 p q p'). Qed.
Lemma lem7538731 (n : nat) (c : nat -> real) : term117 n c.
Proof. exact (@lem7538730 (term118 n c) (term119 n c)). Qed.
Lemma lem7538732 (n : nat) (c : nat -> real) (p' : Prop) : term120 n c p'.
Proof. exact (@lem7538731 n c p'). Qed.
Lemma lem7538733 (n : nat) (c : nat -> real) (p' : Prop) : (term120 n c p') = (term121 n c p').
Proof. exact (eq_refl (term120 n c p')). Qed.
Lemma lem7538734 (n : nat) (c : nat -> real) (p' : Prop) : term121 n c p'.
Proof. exact (EQ_MP (@lem7538733 n c p') (@lem7538732 n c p')). Qed.
Lemma lem7538735 (n : nat) (c : nat -> real) (p' : Prop) (q' : Prop) : term122 n c p' q'.
Proof. exact (@lem7538734 n c p' q'). Qed.
Lemma lem7538736 (n : nat) (c : nat -> real) (p' : Prop) (q' : Prop) : (term122 n c p' q') = (term123 n c p' q').
Proof. exact (eq_refl (term122 n c p' q')). Qed.
Lemma lem7538737 (n : nat) (c : nat -> real) (p' : Prop) (q' : Prop) : term123 n c p' q'.
Proof. exact (EQ_MP (@lem7538736 n c p' q') (@lem7538735 n c p' q')). Qed.
Lemma lem7538739 (t : Prop) : (term124 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem7538740 (n : nat) (c : nat -> real) : (term118 n c) = (term99 n c).
Proof. exact (@lem7538739 (term99 n c)). Qed.
Lemma lem7538772 (n : nat) (c : nat -> real) (q' : Prop) : term125 n c q'.
Proof. exact (@lem7538737 n c (term99 n c) q'). Qed.
Lemma lem7538773 (n : nat) (c : nat -> real) (q' : Prop) : term126 n c q'.
Proof. exact (@lem7538772 n c q' (@lem7538740 n c)). Qed.
Lemma lem7538774 (n : nat) (c : nat -> real) (h1 : term99 n c) : term99 n c.
Proof. exact (h1). Qed.
Lemma lem7538775 (i : nat) (n : nat) (c : nat -> real) (h1 : term99 n c) : term91 n c i.
Proof. exact (@lem7538774 n c h1 i). Qed.
Lemma lem7538776 (n : nat) (c : nat -> real) (i : nat) : (term91 n c i) = (term92 n c i).
Proof. exact (eq_refl (term91 n c i)). Qed.
Lemma lem7538777 (i : nat) (n : nat) (c : nat -> real) (h1 : term99 n c) : term92 n c i.
Proof. exact (EQ_MP (@lem7538776 n c i) (@lem7538775 i n c h1)). Qed.
Lemma lem7538778 (i : nat) (n : nat) (h1 : term80 i n) : term80 i n.
Proof. exact (h1). Qed.
Lemma lem7538779 (c : nat -> real) (i : nat) (n : nat) (h1 : term99 n c) (h2 : term80 i n) : (c i) = term33.
Proof. exact (@lem7538777 i n c h1 (@lem7538778 i n h2)). Qed.
Lemma lem7538855 {_137613 : Type'} (f : _137613 -> real) (s : _137613 -> Prop) (g : _137613 -> real) : term127 _137613 f s g.
Proof. exact (EQ_MP (@lem7261450 _137613 f s g) (@lem7261449 _137613 f g s)). Qed.
Lemma lem7538856 {_137613 : Type'} (f : _137613 -> real) (s : _137613 -> Prop) : term128 _137613 f s.
Proof. exact (fun g : _137613 -> real => @lem7538855 _137613 f s g). Qed.
Lemma lem7538857 (f : nat -> real) (s : nat -> Prop) : term129 f s.
Proof. exact (@lem7538856 nat f s). Qed.
Lemma lem7538858 (c : nat -> real) (x : real) (n : nat) : term130 c x n.
Proof. exact (@lem7538857 (term131 c x) (term132 n)). Qed.
Lemma lem7538859 (c : nat -> real) (x : real) (x' : nat) : (term133 c x x') = (term134 c x x').
Proof. exact (eq_refl (term133 c x x')). Qed.
Lemma lem7538860 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7538861 (c : nat -> real) (x : real) (x' : nat) : (term135 c x x') = (term136 c x x').
Proof. exact (MK_COMB (@lem7538860) (@lem7538859 c x x')). Qed.
Lemma lem7538862 (g : nat -> real) (x : nat) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem7538863 (c : nat -> real) (x : real) (g : nat -> real) (x' : nat) : ((term133 c x x') = (g x')) = ((term134 c x x') = (g x')).
Proof. exact (MK_COMB (@lem7538861 c x x') (@lem7538862 g x')). Qed.
Lemma lem7538864 (x : nat) (n : nat) : (term137 x n) = (term137 x n).
Proof. exact (eq_refl (term137 x n)). Qed.
Lemma lem7538865 (n : nat) (c : nat -> real) (x : real) (g : nat -> real) (x' : nat) : (term138 n c x g x') = (term139 n c x g x').
Proof. exact (MK_COMB (@lem7538864 x' n) (@lem7538863 c x g x')). Qed.
Lemma lem7538866 (n : nat) (c : nat -> real) (x : real) (g : nat -> real) : (term140 n c x g) = (term141 n c x g).
Proof. exact (fun_ext (fun x' : nat => @lem7538865 n c x g x')). Qed.
Lemma lem7538867 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7538868 (n : nat) (c : nat -> real) (x : real) (g : nat -> real) : (term142 n c x g) = (term143 n c x g).
Proof. exact (MK_COMB (@lem7538867) (@lem7538866 n c x g)). Qed.
Lemma lem7538869 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7538870 (n : nat) (c : nat -> real) (x : real) (g : nat -> real) : (term144 n c x g) = (term145 n c x g).
Proof. exact (MK_COMB (@lem7538869) (@lem7538868 n c x g)). Qed.
Lemma lem7538871 (c : nat -> real) (x : real) (i : nat) : (term133 c x i) = (term134 c x i).
Proof. exact (eq_refl (term133 c x i)). Qed.
Lemma lem7538872 (c : nat -> real) (x : real) : (term146 c x) = (term131 c x).
Proof. exact (fun_ext (fun i : nat => @lem7538871 c x i)). Qed.
Lemma lem7538873 (n : nat) : (term147 n) = (term147 n).
Proof. exact (eq_refl (term147 n)). Qed.
Lemma lem7538874 (n : nat) (c : nat -> real) (x : real) : (term148 n c x) = (term149 n c x).
Proof. exact (MK_COMB (@lem7538873 n) (@lem7538872 c x)). Qed.
Lemma lem7538875 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7538876 (n : nat) (c : nat -> real) (x : real) : (term150 n c x) = (term151 n c x).
Proof. exact (MK_COMB (@lem7538875) (@lem7538874 n c x)). Qed.
Lemma lem7538877 (n : nat) (g : nat -> real) : (term152 n g) = (term152 n g).
Proof. exact (eq_refl (term152 n g)). Qed.
Lemma lem7538878 (c : nat -> real) (x : real) (n : nat) (g : nat -> real) : ((term148 n c x) = (term152 n g)) = ((term149 n c x) = (term152 n g)).
Proof. exact (MK_COMB (@lem7538876 n c x) (@lem7538877 n g)). Qed.
Lemma lem7538879 (c : nat -> real) (x : real) (n : nat) (g : nat -> real) : (term153 c x n g) = (term154 c x n g).
Proof. exact (MK_COMB (@lem7538870 n c x g) (@lem7538878 c x n g)). Qed.
Lemma lem7538880 (c : nat -> real) (x : real) (n : nat) : (term155 c x n) = (term156 c x n).
Proof. exact (fun_ext (fun g : nat -> real => @lem7538879 c x n g)). Qed.
Lemma lem7538881 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7538882 (c : nat -> real) (x : real) (n : nat) : (term130 c x n) = (term157 c x n).
Proof. exact (MK_COMB (@lem7538881) (@lem7538880 c x n)). Qed.
Lemma lem7538883 (c : nat -> real) (x : real) (n : nat) : term157 c x n.
Proof. exact (EQ_MP (@lem7538882 c x n) (@lem7538858 c x n)). Qed.
Lemma lem7538884 (c : nat -> real) (x : real) (n : nat) (g : nat -> real) : term158 c x n g.
Proof. exact (@lem7538883 c x n g). Qed.
Lemma lem7538885 (c : nat -> real) (x : real) (n : nat) (g : nat -> real) : (term158 c x n g) = (term154 c x n g).
Proof. exact (eq_refl (term158 c x n g)). Qed.
Lemma lem7538887 (x : nat) (n : nat) (h1 : term80 x n) : term80 x n.
Proof. exact (h1). Qed.
Lemma lem7538888 (x : nat) (n : nat) : (term80 x n) = ((term80 x n) = True).
Proof. exact (@lem7 (term80 x n)). Qed.
Lemma lem7538891 (i : nat) (n : nat) (c : nat -> real) (h1 : term99 n c) : term92 n c i.
Proof. exact (fun h0 : term80 i n => @lem7538779 c i n h1 h0). Qed.
Lemma lem7538892 (x : nat) (n : nat) (c : nat -> real) (h1 : term99 n c) : term92 n c x.
Proof. exact (@lem7538891 x n c h1). Qed.
Lemma lem7538894 (x : nat) (n : nat) (h1 : term80 x n) : (term80 x n) = True.
Proof. exact (EQ_MP (@lem7538888 x n) (@lem7538887 x n h1)). Qed.
Lemma lem7538895 (x : nat) (n : nat) (h1 : term80 x n) : True = (term80 x n).
Proof. exact (SYM (@lem7538894 x n h1)). Qed.
Lemma lem7538896 (x : nat) (n : nat) (h1 : term80 x n) : term80 x n.
Proof. exact (EQ_MP (@lem7538895 x n h1) (@lem0)). Qed.
Lemma lem7538897 (c : nat -> real) (x : nat) (n : nat) (h1 : term99 n c) (h2 : term80 x n) : (c x) = term33.
Proof. exact (@lem7538892 x n c h1 (@lem7538896 x n h2)). Qed.
Lemma lem7538898 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7538899 (c : nat -> real) (x : nat) (n : nat) (h1 : term99 n c) (h2 : term80 x n) : (term159 c x) = term160.
Proof. exact (MK_COMB (@lem7538898) (@lem7538897 c x n h1 h2)). Qed.
Lemma lem7538900 (x : real) (x' : nat) : (real_pow x x') = (real_pow x x').
Proof. exact (eq_refl (real_pow x x')). Qed.
Lemma lem7538901 (x : real) (c : nat -> real) (x' : nat) (n : nat) (h1 : term99 n c) (h2 : term80 x' n) : (term134 c x x') = (term161 x x').
Proof. exact (MK_COMB (@lem7538899 c x' n h1 h2) (@lem7538900 x x')). Qed.
Lemma lem7538903 (x : real) : (term35 x) = term33.
Proof. exact (EQ_MP (@lem7538021 x) (@lem7538020 x)). Qed.
Lemma lem7538904 (x : real) (x' : nat) : (term161 x x') = term33.
Proof. exact (@lem7538903 (real_pow x x')). Qed.
Lemma lem7538905 (x : real) (c : nat -> real) (x' : nat) (n : nat) (h1 : term99 n c) (h2 : term80 x' n) : (term134 c x x') = term33.
Proof. exact (TRANS (@lem7538901 x c x' n h1 h2) (@lem7538904 x x')). Qed.
Lemma lem7538906 (x : real) (x' : nat) (n : nat) (c : nat -> real) (h1 : term99 n c) : term162 n c x x'.
Proof. exact (fun h0 : term80 x' n => @lem7538905 x c x' n h1 h0). Qed.
Lemma lem7538907 (x : real) (n : nat) (c : nat -> real) (h1 : term99 n c) : term163 n c x.
Proof. exact (fun x' : nat => @lem7538906 x x' n c h1). Qed.
Lemma lem7538909 (c : nat -> real) (x : real) (n : nat) (g : nat -> real) : term154 c x n g.
Proof. exact (EQ_MP (@lem7538885 c x n g) (@lem7538884 c x n g)). Qed.
Lemma lem7538910 (c : nat -> real) (x : real) (n : nat) : term164 c x n.
Proof. exact (@lem7538909 c x n term165). Qed.
Lemma lem7538911 (x : nat) : (term166 x) = term33.
Proof. exact (eq_refl (term166 x)). Qed.
Lemma lem7538912 (c : nat -> real) (x : real) (x' : nat) : (term136 c x x') = (term136 c x x').
Proof. exact (eq_refl (term136 c x x')). Qed.
Lemma lem7538913 (c : nat -> real) (x : real) (x' : nat) : ((term134 c x x') = (term166 x')) = ((term134 c x x') = term33).
Proof. exact (MK_COMB (@lem7538912 c x x') (@lem7538911 x')). Qed.
Lemma lem7538914 (x : nat) (n : nat) : (term137 x n) = (term137 x n).
Proof. exact (eq_refl (term137 x n)). Qed.
Lemma lem7538915 (n : nat) (c : nat -> real) (x : real) (x' : nat) : (term167 n c x x') = (term162 n c x x').
Proof. exact (MK_COMB (@lem7538914 x' n) (@lem7538913 c x x')). Qed.
Lemma lem7538916 (n : nat) (c : nat -> real) (x : real) : (term168 n c x) = (term169 n c x).
Proof. exact (fun_ext (fun x' : nat => @lem7538915 n c x x')). Qed.
Lemma lem7538917 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7538918 (n : nat) (c : nat -> real) (x : real) : (term170 n c x) = (term163 n c x).
Proof. exact (MK_COMB (@lem7538917) (@lem7538916 n c x)). Qed.
Lemma lem7538919 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7538920 (n : nat) (c : nat -> real) (x : real) : (term171 n c x) = (term172 n c x).
Proof. exact (MK_COMB (@lem7538919) (@lem7538918 n c x)). Qed.
Lemma lem7538921 (c : nat -> real) (x : real) (n : nat) : ((term149 n c x) = (term173 n)) = ((term149 n c x) = (term173 n)).
Proof. exact (eq_refl ((term149 n c x) = (term173 n))). Qed.
Lemma lem7538922 (c : nat -> real) (x : real) (n : nat) : (term164 c x n) = (term174 c x n).
Proof. exact (MK_COMB (@lem7538920 n c x) (@lem7538921 c x n)). Qed.
Lemma lem7538923 (c : nat -> real) (x : real) (n : nat) : term174 c x n.
Proof. exact (EQ_MP (@lem7538922 c x n) (@lem7538910 c x n)). Qed.
Lemma lem7538924 (x : real) (n : nat) (c : nat -> real) (h1 : term99 n c) : (term149 n c x) = (term173 n).
Proof. exact (@lem7538923 c x n (@lem7538907 x n c h1)). Qed.
Lemma lem7538926 {A : Type'} (s : A -> Prop) : (term32 A s) = term33.
Proof. exact (EQ_MP (@lem7538018 A s) (@lem7538017 A s)). Qed.
Lemma lem7538927 (s : nat -> Prop) : (term175 s) = term33.
Proof. exact (@lem7538926 nat s). Qed.
Lemma lem7538928 (n : nat) : (term173 n) = term33.
Proof. exact (@lem7538927 (term132 n)). Qed.
Lemma lem7538929 (x : real) (n : nat) (c : nat -> real) (h1 : term99 n c) : (term149 n c x) = term33.
Proof. exact (TRANS (@lem7538924 x n c h1) (@lem7538928 n)). Qed.
Lemma lem7538930 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7538931 (x : real) (n : nat) (c : nat -> real) (h1 : term99 n c) : (term151 n c x) = term176.
Proof. exact (MK_COMB (@lem7538930) (@lem7538929 x n c h1)). Qed.
Lemma lem7538932 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem7538933 (x : real) (n : nat) (c : nat -> real) (h1 : term99 n c) : ((term149 n c x) = term33) = (term33 = term33).
Proof. exact (MK_COMB (@lem7538931 x n c h1) (@lem7538932)). Qed.
Lemma lem7538935 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7538936 (x : real) : (x = x) = True.
Proof. exact (@lem7538935 real x). Qed.
Lemma lem7538937 : (term33 = term33) = True.
Proof. exact (@lem7538936 term33). Qed.
Lemma lem7538938 (x : real) (n : nat) (c : nat -> real) (h1 : term99 n c) : ((term149 n c x) = term33) = True.
Proof. exact (TRANS (@lem7538933 x n c h1) (@lem7538937)). Qed.
Lemma lem7538939 (GEN_PVAR_348 : real) : (@SETSPEC real GEN_PVAR_348) = (@SETSPEC real GEN_PVAR_348).
Proof. exact (eq_refl (@SETSPEC real GEN_PVAR_348)). Qed.
Lemma lem7538940 (x : real) (GEN_PVAR_348 : real) (n : nat) (c : nat -> real) (h1 : term99 n c) : (term177 GEN_PVAR_348 n c x) = (@SETSPEC real GEN_PVAR_348 True).
Proof. exact (MK_COMB (@lem7538939 GEN_PVAR_348) (@lem7538938 x n c h1)). Qed.
Lemma lem7538941 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7538942 (GEN_PVAR_348 : real) (x : real) (n : nat) (c : nat -> real) (h1 : term99 n c) : (term178 GEN_PVAR_348 n c x) = (@SETSPEC real GEN_PVAR_348 True x).
Proof. exact (MK_COMB (@lem7538940 x GEN_PVAR_348 n c h1) (@lem7538941 x)). Qed.
Lemma lem7538943 (GEN_PVAR_348 : real) (n : nat) (c : nat -> real) (h1 : term99 n c) : (term179 GEN_PVAR_348 n c) = (term17 GEN_PVAR_348).
Proof. exact (fun_ext (fun x : real => @lem7538942 GEN_PVAR_348 x n c h1)). Qed.
Lemma lem7538944 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7538945 (GEN_PVAR_348 : real) (n : nat) (c : nat -> real) (h1 : term99 n c) : (term180 GEN_PVAR_348 n c) = (term19 GEN_PVAR_348).
Proof. exact (MK_COMB (@lem7538944) (@lem7538943 GEN_PVAR_348 n c h1)). Qed.
Lemma lem7538950 (n : nat) (c : nat -> real) (h1 : term99 n c) : (term181 n c) = term21.
Proof. exact (fun_ext (fun GEN_PVAR_348 : real => @lem7538945 GEN_PVAR_348 n c h1)). Qed.
Lemma lem7538955 : (@GSPEC real) = (@GSPEC real).
Proof. exact (eq_refl (@GSPEC real)). Qed.
Lemma lem7538956 (n : nat) (c : nat -> real) (h1 : term99 n c) : (term182 n c) = term7.
Proof. exact (MK_COMB (@lem7538955) (@lem7538950 n c h1)). Qed.
Lemma lem7538961 : (@FINITE real) = (@FINITE real).
Proof. exact (eq_refl (@FINITE real)). Qed.
Lemma lem7538962 (n : nat) (c : nat -> real) (h1 : term99 n c) : (term53 n c) = term183.
Proof. exact (MK_COMB (@lem7538961) (@lem7538956 n c h1)). Qed.
Lemma lem7538967 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7538968 (n : nat) (c : nat -> real) (h1 : term99 n c) : (term119 n c) = term184.
Proof. exact (MK_COMB (@lem7538967) (@lem7538962 n c h1)). Qed.
Lemma lem7538973 (n : nat) (c : nat -> real) : term185 n c.
Proof. exact (fun h0 : term99 n c => @lem7538968 n c h0). Qed.
Lemma lem7538974 (n : nat) (c : nat -> real) : term186 n c.
Proof. exact (@lem7538773 n c term184). Qed.
Lemma lem7538975 (n : nat) (c : nat -> real) : (term116 n c) = (term187 n c).
Proof. exact (@lem7538974 n c (@lem7538973 n c)). Qed.
Lemma lem7539077 (n : nat) (c : nat -> real) : (term187 n c) = (term116 n c).
Proof. exact (SYM (@lem7538975 n c)). Qed.
Lemma lem7539089 {A : Type'} (s : A -> Prop) : (term0 A s) = (@INFINITE A s).
Proof. exact (EQ_MP (@lem7538013 A s) (@lem7538012 A s)). Qed.
Lemma lem7539090 (s : real -> Prop) : (term188 s) = (@INFINITE real s).
Proof. exact (@lem7539089 real s). Qed.
Lemma lem7539091 : term184 = term189.
Proof. exact (@lem7539090 term7). Qed.
Lemma lem7539093 : term7 = (@UNIV real).
Proof. exact (EQ_MP (@lem7537962) (@lem7538010)). Qed.
Lemma lem7539094 : (@INFINITE real) = (@INFINITE real).
Proof. exact (eq_refl (@INFINITE real)). Qed.
Lemma lem7539095 : term189 = (@INFINITE real (@UNIV real)).
Proof. exact (MK_COMB (@lem7539094) (@lem7539093)). Qed.
Lemma lem7539097 : (@INFINITE real (@UNIV real)) = True.
Proof. exact (EQ_MP (@lem7538015) (@lem4713723)). Qed.
Lemma lem7539098 : term189 = True.
Proof. exact (TRANS (@lem7539095) (@lem7539097)). Qed.
Lemma lem7539099 : term184 = True.
Proof. exact (TRANS (@lem7539091) (@lem7539098)). Qed.
Lemma lem7539100 (n : nat) (c : nat -> real) : (term190 n c) = (term190 n c).
Proof. exact (eq_refl (term190 n c)). Qed.
Lemma lem7539101 (n : nat) (c : nat -> real) : (term187 n c) = (term191 n c).
Proof. exact (MK_COMB (@lem7539100 n c) (@lem7539099)). Qed.
Lemma lem7539103 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7539104 (n : nat) (c : nat -> real) : (term191 n c) = True.
Proof. exact (@lem7539103 (term99 n c)). Qed.
Lemma lem7539105 (n : nat) (c : nat -> real) : (term187 n c) = True.
Proof. exact (TRANS (@lem7539101 n c) (@lem7539104 n c)). Qed.
Lemma lem7539106 (n : nat) (c : nat -> real) : True = (term187 n c).
Proof. exact (SYM (@lem7539105 n c)). Qed.
Lemma lem7539107 (n : nat) (c : nat -> real) : term187 n c.
Proof. exact (EQ_MP (@lem7539106 n c) (@lem0)). Qed.
Lemma lem7539108 (n : nat) (c : nat -> real) : term116 n c.
Proof. exact (EQ_MP (@lem7539077 n c) (@lem7539107 n c)). Qed.
Lemma lem7539110 (n : nat) (c : nat -> real) : term115 n c.
Proof. exact (EQ_MP (@lem7538724 n c) (@lem7539108 n c)). Qed.
Lemma lem7539111 (n : nat) (c : nat -> real) : term192 n c.
Proof. exact (conj (@lem7539110 n c) (@lem7538718 n c)). Qed.
Lemma lem7539112 (n : nat) (c : nat -> real) : (term192 n c) = ((term53 n c) = (term51 n c)).
Proof. exact (@lem32 (term53 n c) (term51 n c)). Qed.
Lemma lem7539113 (n : nat) (c : nat -> real) : (term53 n c) = (term51 n c).
Proof. exact (EQ_MP (@lem7539112 n c) (@lem7539111 n c)). Qed.
Lemma lem7539114 (n : nat) (c : nat -> real) : (term53 n c) = (term84 n c).
Proof. exact (EQ_MP (@lem7538248 n c) (@lem7539113 n c)). Qed.
Lemma lem7539115 (n : nat) (c : nat -> real) : (term53 n c) = (term83 n c).
Proof. exact (EQ_MP (@lem7538207 n c) (@lem7539114 n c)). Qed.
Lemma lem7539120 (n : nat) : term193 n.
Proof. exact (fun c : nat -> real => @lem7539115 n c). Qed.
Lemma lem7539125 : term194.
Proof. exact (fun n : nat => @lem7539120 n). Qed.
