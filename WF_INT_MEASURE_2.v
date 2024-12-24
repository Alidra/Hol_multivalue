Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_INT_MEASURE_2_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import FORALL_UNCURRY_spec.
Require Import WF_INT_MEASURE_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem2749912 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (h1 : (term0 _5106 _5107 P) = (term1 _5106 _5107 P)) : (term0 _5106 _5107 P) = (term1 _5106 _5107 P).
Proof. exact (h1). Qed.
Lemma lem2749913 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (h1 : (term0 _5106 _5107 P) = (term1 _5106 _5107 P)) : (term1 _5106 _5107 P) = (term0 _5106 _5107 P).
Proof. exact (SYM (@lem2749912 _5106 _5107 P h1)). Qed.
Lemma lem2749914 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (h1 : (term1 _5106 _5107 P) = (term0 _5106 _5107 P)) : (term1 _5106 _5107 P) = (term0 _5106 _5107 P).
Proof. exact (h1). Qed.
Lemma lem2749915 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (h1 : (term1 _5106 _5107 P) = (term0 _5106 _5107 P)) : (term0 _5106 _5107 P) = (term1 _5106 _5107 P).
Proof. exact (SYM (@lem2749914 _5106 _5107 P h1)). Qed.
Lemma lem2749916 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : ((term0 _5106 _5107 P) = (term1 _5106 _5107 P)) = ((term1 _5106 _5107 P) = (term0 _5106 _5107 P)).
Proof. exact (prop_ext (fun h1 : (term0 _5106 _5107 P) = (term1 _5106 _5107 P) => @lem2749913 _5106 _5107 P h1) (fun h1 : (term1 _5106 _5107 P) = (term0 _5106 _5107 P) => @lem2749915 _5106 _5107 P h1)). Qed.
Lemma lem2749917 {_5106 _5107 : Type'} : (term2 _5106 _5107) = (term3 _5106 _5107).
Proof. exact (fun_ext (fun P : type1223 _5106 _5107 => @lem2749916 _5106 _5107 P)). Qed.
Lemma lem2749918 {_5106 _5107 : Type'} : (@all ((prod _5107 _5106) -> Prop)) = (@all ((prod _5107 _5106) -> Prop)).
Proof. exact (eq_refl (@all ((prod _5107 _5106) -> Prop))). Qed.
Lemma lem2749919 {_5106 _5107 : Type'} : (term4 _5106 _5107) = (term5 _5106 _5107).
Proof. exact (MK_COMB (@lem2749918 _5106 _5107) (@lem2749917 _5106 _5107)). Qed.
Lemma lem2749920 {_5106 _5107 : Type'} : term5 _5106 _5107.
Proof. exact (EQ_MP (@lem2749919 _5106 _5107) (@lem49909 _5106 _5107)). Qed.
Lemma lem2749921 {A : Type'} (P : A -> Prop) : term6 A P.
Proof. exact (@lem2749910 A P). Qed.
Lemma lem2749922 {A : Type'} (P : A -> Prop) : (term6 A P) = (term7 A P).
Proof. exact (eq_refl (term6 A P)). Qed.
Lemma lem2749923 {A : Type'} (P : A -> Prop) : term7 A P.
Proof. exact (EQ_MP (@lem2749922 A P) (@lem2749921 A P)). Qed.
Lemma lem2749924 {A : Type'} (P : A -> Prop) (m : A -> int) : term8 A P m.
Proof. exact (@lem2749923 A P m). Qed.
Lemma lem2749925 {A : Type'} (m : A -> int) (P : A -> Prop) : (term8 A P m) = (term9 A m P).
Proof. exact (eq_refl (term8 A P m)). Qed.
Lemma lem2749926 {A : Type'} (m : A -> int) (P : A -> Prop) : term9 A m P.
Proof. exact (EQ_MP (@lem2749925 A m P) (@lem2749924 A P m)). Qed.
Lemma lem2749927 {A : Type'} (m : A -> int) (P : A -> Prop) : (term9 A m P) = ((term9 A m P) = True).
Proof. exact (@lem7 (term9 A m P)). Qed.
Lemma lem2749929 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term10 _5106 _5107 P.
Proof. exact (@lem2749920 _5106 _5107 P). Qed.
Lemma lem2749930 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term10 _5106 _5107 P) = ((term1 _5106 _5107 P) = (term0 _5106 _5107 P)).
Proof. exact (eq_refl (term10 _5106 _5107 P)). Qed.
Lemma lem2749932 {A B C : Type'} (P : type443 A B C) : term11 A B C P.
Proof. exact (@lem53018 A B C P). Qed.
Lemma lem2749933 {A B C : Type'} (P : type443 A B C) : (term11 A B C P) = ((term12 A B C P) = (term13 A B C P)).
Proof. exact (eq_refl (term11 A B C P)). Qed.
Lemma lem2749959 {A B C : Type'} (P : type443 A B C) : (term12 A B C P) = (term13 A B C P).
Proof. exact (EQ_MP (@lem2749933 A B C P) (@lem2749932 A B C P)). Qed.
Lemma lem2749960 {A B : Type'} (P : type475 A B) : (term14 A B P) = (term15 A B P).
Proof. exact (@lem2749959 A B Prop P). Qed.
Lemma lem2749961 {A B : Type'} : (term16 A B) = (term17 A B).
Proof. exact (@lem2749960 A B (term18 A B)). Qed.
Lemma lem2749962 {A B : Type'} (P : type1413 A B) : (term19 A B P) = (term20 A B P).
Proof. exact (eq_refl (term19 A B P)). Qed.
Lemma lem2749963 {A B : Type'} : (term21 A B) = (term18 A B).
Proof. exact (fun_ext (fun P : type1413 A B => @lem2749962 A B P)). Qed.
Lemma lem2749964 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem2749965 {A B : Type'} : (term16 A B) = (term22 A B).
Proof. exact (MK_COMB (@lem2749964 A B) (@lem2749963 A B)). Qed.
Lemma lem2749966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2749967 {A B : Type'} : (term23 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem2749966) (@lem2749965 A B)). Qed.
Lemma lem2749968 {A B : Type'} (P : type1210 A B) : (term25 A B P) = (term26 A B P).
Proof. exact (eq_refl (term25 A B P)). Qed.
Lemma lem2749969 {A B : Type'} : (term27 A B) = (term28 A B).
Proof. exact (fun_ext (fun P : type1210 A B => @lem2749968 A B P)). Qed.
Lemma lem2749970 {A B : Type'} : (@all ((prod A B) -> Prop)) = (@all ((prod A B) -> Prop)).
Proof. exact (eq_refl (@all ((prod A B) -> Prop))). Qed.
Lemma lem2749971 {A B : Type'} : (term17 A B) = (term29 A B).
Proof. exact (MK_COMB (@lem2749970 A B) (@lem2749969 A B)). Qed.
Lemma lem2749972 {A B : Type'} : ((term16 A B) = (term17 A B)) = ((term22 A B) = (term29 A B)).
Proof. exact (MK_COMB (@lem2749967 A B) (@lem2749971 A B)). Qed.
Lemma lem2749973 {A B : Type'} : (term22 A B) = (term29 A B).
Proof. exact (EQ_MP (@lem2749972 A B) (@lem2749961 A B)). Qed.
Lemma lem2750004 {A B C : Type'} (P : type443 A B C) : (term12 A B C P) = (term13 A B C P).
Proof. exact (EQ_MP (@lem2749933 A B C P) (@lem2749932 A B C P)). Qed.
Lemma lem2750005 {A B : Type'} (P : type476 A B) : (term30 A B P) = (term31 A B P).
Proof. exact (@lem2750004 A B int P). Qed.
Lemma lem2750006 {A B : Type'} (P : type1210 A B) : (term32 A B P) = (term33 A B P).
Proof. exact (@lem2750005 A B (term34 A B P)). Qed.
Lemma lem2750007 {A B : Type'} (m : type1414 A B) (P : type1210 A B) : (term35 A B P m) = (term36 A B m P).
Proof. exact (eq_refl (term35 A B P m)). Qed.
Lemma lem2750008 {A B : Type'} (P : type1210 A B) : (term37 A B P) = (term34 A B P).
Proof. exact (fun_ext (fun m : type1414 A B => @lem2750007 A B m P)). Qed.
Lemma lem2750009 {A B : Type'} : (@all (A -> B -> int)) = (@all (A -> B -> int)).
Proof. exact (eq_refl (@all (A -> B -> int))). Qed.
Lemma lem2750010 {A B : Type'} (P : type1210 A B) : (term32 A B P) = (term26 A B P).
Proof. exact (MK_COMB (@lem2750009 A B) (@lem2750008 A B P)). Qed.
Lemma lem2750011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2750012 {A B : Type'} (P : type1210 A B) : (term38 A B P) = (term39 A B P).
Proof. exact (MK_COMB (@lem2750011) (@lem2750010 A B P)). Qed.
Lemma lem2750013 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term40 A B P m) = (term41 A B m P).
Proof. exact (eq_refl (term40 A B P m)). Qed.
Lemma lem2750014 {A B : Type'} (P : type1210 A B) : (term42 A B P) = (term43 A B P).
Proof. exact (fun_ext (fun m : type1211 A B => @lem2750013 A B m P)). Qed.
Lemma lem2750015 {A B : Type'} : (@all ((prod A B) -> int)) = (@all ((prod A B) -> int)).
Proof. exact (eq_refl (@all ((prod A B) -> int))). Qed.
Lemma lem2750016 {A B : Type'} (P : type1210 A B) : (term33 A B P) = (term44 A B P).
Proof. exact (MK_COMB (@lem2750015 A B) (@lem2750014 A B P)). Qed.
Lemma lem2750017 {A B : Type'} (P : type1210 A B) : ((term32 A B P) = (term33 A B P)) = ((term26 A B P) = (term44 A B P)).
Proof. exact (MK_COMB (@lem2750012 A B P) (@lem2750016 A B P)). Qed.
Lemma lem2750018 {A B : Type'} (P : type1210 A B) : (term26 A B P) = (term44 A B P).
Proof. exact (EQ_MP (@lem2750017 A B P) (@lem2750006 A B P)). Qed.
Lemma lem2750061 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2750062 {A B : Type'} (f : type1414 A B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (@lem2750061 A (B -> int) f y). Qed.
Lemma lem2750063 {A B : Type'} (m : type1211 A B) (x : A) : (term47 A B m x) = (term48 A B m x).
Proof. exact (@lem2750062 A B (term49 A B m) x). Qed.
Lemma lem2750064 {A B : Type'} (m : type1211 A B) (a : A) : (term48 A B m a) = (term50 A B m a).
Proof. exact (eq_refl (term48 A B m a)). Qed.
Lemma lem2750065 {A B : Type'} (m : type1211 A B) : (term51 A B m) = (term49 A B m).
Proof. exact (fun_ext (fun a : A => @lem2750064 A B m a)). Qed.
Lemma lem2750066 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2750067 {A B : Type'} (m : type1211 A B) (x : A) : (term47 A B m x) = (term48 A B m x).
Proof. exact (MK_COMB (@lem2750065 A B m) (@lem2750066 A x)). Qed.
Lemma lem2750068 {B : Type'} : (@eq (B -> int)) = (@eq (B -> int)).
Proof. exact (eq_refl (@eq (B -> int))). Qed.
Lemma lem2750069 {A B : Type'} (m : type1211 A B) (x : A) : (term52 A B m x) = (term53 A B m x).
Proof. exact (MK_COMB (@lem2750068 B) (@lem2750067 A B m x)). Qed.
Lemma lem2750070 {A B : Type'} (m : type1211 A B) (x : A) : (term48 A B m x) = (term50 A B m x).
Proof. exact (eq_refl (term48 A B m x)). Qed.
Lemma lem2750071 {A B : Type'} (m : type1211 A B) (x : A) : ((term47 A B m x) = (term48 A B m x)) = ((term48 A B m x) = (term50 A B m x)).
Proof. exact (MK_COMB (@lem2750069 A B m x) (@lem2750070 A B m x)). Qed.
Lemma lem2750072 {A B : Type'} (m : type1211 A B) (x : A) : (term48 A B m x) = (term50 A B m x).
Proof. exact (EQ_MP (@lem2750071 A B m x) (@lem2750063 A B m x)). Qed.
Lemma lem2750073 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem2750074 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term54 A B m x y) = (term55 A B m x y).
Proof. exact (MK_COMB (@lem2750072 A B m x) (@lem2750073 B y)). Qed.
Lemma lem2750076 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2750077 {B : Type'} (f : B -> int) (y : B) : (term56 B f y) = (f y).
Proof. exact (@lem2750076 B int f y). Qed.
Lemma lem2750078 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term57 A B m x y) = (term55 A B m x y).
Proof. exact (@lem2750077 B (term50 A B m x) y). Qed.
Lemma lem2750079 {A B : Type'} (m : type1211 A B) (x : A) (b : B) : (term55 A B m x b) = (term58 A B m x b).
Proof. exact (eq_refl (term55 A B m x b)). Qed.
Lemma lem2750080 {A B : Type'} (m : type1211 A B) (x : A) : (term59 A B m x) = (term50 A B m x).
Proof. exact (fun_ext (fun b : B => @lem2750079 A B m x b)). Qed.
Lemma lem2750081 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem2750082 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term57 A B m x y) = (term55 A B m x y).
Proof. exact (MK_COMB (@lem2750080 A B m x) (@lem2750081 B y)). Qed.
Lemma lem2750083 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2750084 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term60 A B m x y) = (term61 A B m x y).
Proof. exact (MK_COMB (@lem2750083) (@lem2750082 A B m x y)). Qed.
Lemma lem2750085 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term55 A B m x y) = (term58 A B m x y).
Proof. exact (eq_refl (term55 A B m x y)). Qed.
Lemma lem2750086 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : ((term57 A B m x y) = (term55 A B m x y)) = ((term55 A B m x y) = (term58 A B m x y)).
Proof. exact (MK_COMB (@lem2750084 A B m x y) (@lem2750085 A B m x y)). Qed.
Lemma lem2750087 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term55 A B m x y) = (term58 A B m x y).
Proof. exact (EQ_MP (@lem2750086 A B m x y) (@lem2750078 A B m x y)). Qed.
Lemma lem2750088 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term54 A B m x y) = (term58 A B m x y).
Proof. exact (TRANS (@lem2750074 A B m x y) (@lem2750087 A B m x y)). Qed.
Lemma lem2750089 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem2750090 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term63 A B m x y) = (term64 A B m x y).
Proof. exact (MK_COMB (@lem2750089) (@lem2750088 A B m x y)). Qed.
Lemma lem2750091 {A B : Type'} (m : type1211 A B) (x : A) : (term65 A B m x) = (term66 A B m x).
Proof. exact (fun_ext (fun y : B => @lem2750090 A B m x y)). Qed.
Lemma lem2750092 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem2750093 {A B : Type'} (m : type1211 A B) (x : A) : (term67 A B m x) = (term68 A B m x).
Proof. exact (MK_COMB (@lem2750092 B) (@lem2750091 A B m x)). Qed.
Lemma lem2750100 {A B : Type'} (m : type1211 A B) : (term69 A B m) = (term70 A B m).
Proof. exact (fun_ext (fun x : A => @lem2750093 A B m x)). Qed.
Lemma lem2750101 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2750102 {A B : Type'} (m : type1211 A B) : (term71 A B m) = (term72 A B m).
Proof. exact (MK_COMB (@lem2750101 A) (@lem2750100 A B m)). Qed.
Lemma lem2750104 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term1 _5106 _5107 P) = (term0 _5106 _5107 P).
Proof. exact (EQ_MP (@lem2749930 _5106 _5107 P) (@lem2749929 _5106 _5107 P)). Qed.
Lemma lem2750105 {A B : Type'} (P : type1210 A B) : (term73 A B P) = (term74 A B P).
Proof. exact (@lem2750104 B A P). Qed.
Lemma lem2750106 {A B : Type'} (m : type1211 A B) : (term75 A B m) = (term76 A B m).
Proof. exact (@lem2750105 A B (term77 A B m)). Qed.
Lemma lem2750107 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term78 A B m x y) = (term64 A B m x y).
Proof. exact (eq_refl (term78 A B m x y)). Qed.
Lemma lem2750108 {A B : Type'} (m : type1211 A B) (x : A) : (term79 A B m x) = (term66 A B m x).
Proof. exact (fun_ext (fun y : B => @lem2750107 A B m x y)). Qed.
Lemma lem2750109 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem2750110 {A B : Type'} (m : type1211 A B) (x : A) : (term80 A B m x) = (term68 A B m x).
Proof. exact (MK_COMB (@lem2750109 B) (@lem2750108 A B m x)). Qed.
Lemma lem2750111 {A B : Type'} (m : type1211 A B) : (term81 A B m) = (term70 A B m).
Proof. exact (fun_ext (fun x : A => @lem2750110 A B m x)). Qed.
Lemma lem2750112 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2750113 {A B : Type'} (m : type1211 A B) : (term75 A B m) = (term72 A B m).
Proof. exact (MK_COMB (@lem2750112 A) (@lem2750111 A B m)). Qed.
Lemma lem2750114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2750115 {A B : Type'} (m : type1211 A B) : (term82 A B m) = (term83 A B m).
Proof. exact (MK_COMB (@lem2750114) (@lem2750113 A B m)). Qed.
Lemma lem2750116 {A B : Type'} (m : type1211 A B) (p : prod A B) : (term84 A B m p) = (term85 A B m p).
Proof. exact (eq_refl (term84 A B m p)). Qed.
Lemma lem2750117 {A B : Type'} (m : type1211 A B) : (term86 A B m) = (term77 A B m).
Proof. exact (fun_ext (fun p : prod A B => @lem2750116 A B m p)). Qed.
Lemma lem2750118 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem2750119 {A B : Type'} (m : type1211 A B) : (term76 A B m) = (term87 A B m).
Proof. exact (MK_COMB (@lem2750118 A B) (@lem2750117 A B m)). Qed.
Lemma lem2750120 {A B : Type'} (m : type1211 A B) : ((term75 A B m) = (term76 A B m)) = ((term72 A B m) = (term87 A B m)).
Proof. exact (MK_COMB (@lem2750115 A B m) (@lem2750119 A B m)). Qed.
Lemma lem2750121 {A B : Type'} (m : type1211 A B) : (term72 A B m) = (term87 A B m).
Proof. exact (EQ_MP (@lem2750120 A B m) (@lem2750106 A B m)). Qed.
Lemma lem2750128 {A B : Type'} (m : type1211 A B) : (term71 A B m) = (term87 A B m).
Proof. exact (TRANS (@lem2750102 A B m) (@lem2750121 A B m)). Qed.
Lemma lem2750129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2750130 {A B : Type'} (m : type1211 A B) : (term88 A B m) = (term89 A B m).
Proof. exact (MK_COMB (@lem2750129) (@lem2750128 A B m)). Qed.
Lemma lem2750198 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2750199 {A B : Type'} (f : type1414 A B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (@lem2750198 A (B -> int) f y). Qed.
Lemma lem2750200 {A B : Type'} (m : type1211 A B) (x' : A) : (term47 A B m x') = (term48 A B m x').
Proof. exact (@lem2750199 A B (term49 A B m) x'). Qed.
Lemma lem2750201 {A B : Type'} (m : type1211 A B) (a : A) : (term48 A B m a) = (term50 A B m a).
Proof. exact (eq_refl (term48 A B m a)). Qed.
Lemma lem2750202 {A B : Type'} (m : type1211 A B) : (term51 A B m) = (term49 A B m).
Proof. exact (fun_ext (fun a : A => @lem2750201 A B m a)). Qed.
Lemma lem2750203 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem2750204 {A B : Type'} (m : type1211 A B) (x' : A) : (term47 A B m x') = (term48 A B m x').
Proof. exact (MK_COMB (@lem2750202 A B m) (@lem2750203 A x')). Qed.
Lemma lem2750205 {B : Type'} : (@eq (B -> int)) = (@eq (B -> int)).
Proof. exact (eq_refl (@eq (B -> int))). Qed.
Lemma lem2750206 {A B : Type'} (m : type1211 A B) (x' : A) : (term52 A B m x') = (term53 A B m x').
Proof. exact (MK_COMB (@lem2750205 B) (@lem2750204 A B m x')). Qed.
Lemma lem2750207 {A B : Type'} (m : type1211 A B) (x' : A) : (term48 A B m x') = (term50 A B m x').
Proof. exact (eq_refl (term48 A B m x')). Qed.
Lemma lem2750208 {A B : Type'} (m : type1211 A B) (x' : A) : ((term47 A B m x') = (term48 A B m x')) = ((term48 A B m x') = (term50 A B m x')).
Proof. exact (MK_COMB (@lem2750206 A B m x') (@lem2750207 A B m x')). Qed.
Lemma lem2750209 {A B : Type'} (m : type1211 A B) (x' : A) : (term48 A B m x') = (term50 A B m x').
Proof. exact (EQ_MP (@lem2750208 A B m x') (@lem2750200 A B m x')). Qed.
Lemma lem2750210 {B : Type'} (y' : B) : y' = y'.
Proof. exact (eq_refl y'). Qed.
Lemma lem2750211 {A B : Type'} (m : type1211 A B) (x' : A) (y' : B) : (term54 A B m x' y') = (term55 A B m x' y').
Proof. exact (MK_COMB (@lem2750209 A B m x') (@lem2750210 B y')). Qed.
Lemma lem2750213 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2750214 {B : Type'} (f : B -> int) (y : B) : (term56 B f y) = (f y).
Proof. exact (@lem2750213 B int f y). Qed.
Lemma lem2750215 {A B : Type'} (m : type1211 A B) (x' : A) (y' : B) : (term57 A B m x' y') = (term55 A B m x' y').
Proof. exact (@lem2750214 B (term50 A B m x') y'). Qed.
Lemma lem2750216 {A B : Type'} (m : type1211 A B) (x' : A) (b : B) : (term55 A B m x' b) = (term58 A B m x' b).
Proof. exact (eq_refl (term55 A B m x' b)). Qed.
Lemma lem2750217 {A B : Type'} (m : type1211 A B) (x' : A) : (term59 A B m x') = (term50 A B m x').
Proof. exact (fun_ext (fun b : B => @lem2750216 A B m x' b)). Qed.
Lemma lem2750218 {B : Type'} (y' : B) : y' = y'.
Proof. exact (eq_refl y'). Qed.
Lemma lem2750219 {A B : Type'} (m : type1211 A B) (x' : A) (y' : B) : (term57 A B m x' y') = (term55 A B m x' y').
Proof. exact (MK_COMB (@lem2750217 A B m x') (@lem2750218 B y')). Qed.
Lemma lem2750220 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2750221 {A B : Type'} (m : type1211 A B) (x' : A) (y' : B) : (term60 A B m x' y') = (term61 A B m x' y').
Proof. exact (MK_COMB (@lem2750220) (@lem2750219 A B m x' y')). Qed.
Lemma lem2750222 {A B : Type'} (m : type1211 A B) (x' : A) (y' : B) : (term55 A B m x' y') = (term58 A B m x' y').
Proof. exact (eq_refl (term55 A B m x' y')). Qed.
Lemma lem2750223 {A B : Type'} (m : type1211 A B) (x' : A) (y' : B) : ((term57 A B m x' y') = (term55 A B m x' y')) = ((term55 A B m x' y') = (term58 A B m x' y')).
Proof. exact (MK_COMB (@lem2750221 A B m x' y') (@lem2750222 A B m x' y')). Qed.
Lemma lem2750224 {A B : Type'} (m : type1211 A B) (x' : A) (y' : B) : (term55 A B m x' y') = (term58 A B m x' y').
Proof. exact (EQ_MP (@lem2750223 A B m x' y') (@lem2750215 A B m x' y')). Qed.
Lemma lem2750225 {A B : Type'} (m : type1211 A B) (x' : A) (y' : B) : (term54 A B m x' y') = (term58 A B m x' y').
Proof. exact (TRANS (@lem2750211 A B m x' y') (@lem2750224 A B m x' y')). Qed.
Lemma lem2750226 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem2750227 {A B : Type'} (m : type1211 A B) (x' : A) (y' : B) : (term90 A B m x' y') = (term91 A B m x' y').
Proof. exact (MK_COMB (@lem2750226) (@lem2750225 A B m x' y')). Qed.
Lemma lem2750229 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2750230 {A B : Type'} (f : type1414 A B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (@lem2750229 A (B -> int) f y). Qed.
Lemma lem2750231 {A B : Type'} (m : type1211 A B) (x : A) : (term47 A B m x) = (term48 A B m x).
Proof. exact (@lem2750230 A B (term49 A B m) x). Qed.
Lemma lem2750232 {A B : Type'} (m : type1211 A B) (a : A) : (term48 A B m a) = (term50 A B m a).
Proof. exact (eq_refl (term48 A B m a)). Qed.
Lemma lem2750233 {A B : Type'} (m : type1211 A B) : (term51 A B m) = (term49 A B m).
Proof. exact (fun_ext (fun a : A => @lem2750232 A B m a)). Qed.
Lemma lem2750234 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2750235 {A B : Type'} (m : type1211 A B) (x : A) : (term47 A B m x) = (term48 A B m x).
Proof. exact (MK_COMB (@lem2750233 A B m) (@lem2750234 A x)). Qed.
Lemma lem2750236 {B : Type'} : (@eq (B -> int)) = (@eq (B -> int)).
Proof. exact (eq_refl (@eq (B -> int))). Qed.
Lemma lem2750237 {A B : Type'} (m : type1211 A B) (x : A) : (term52 A B m x) = (term53 A B m x).
Proof. exact (MK_COMB (@lem2750236 B) (@lem2750235 A B m x)). Qed.
Lemma lem2750238 {A B : Type'} (m : type1211 A B) (x : A) : (term48 A B m x) = (term50 A B m x).
Proof. exact (eq_refl (term48 A B m x)). Qed.
Lemma lem2750239 {A B : Type'} (m : type1211 A B) (x : A) : ((term47 A B m x) = (term48 A B m x)) = ((term48 A B m x) = (term50 A B m x)).
Proof. exact (MK_COMB (@lem2750237 A B m x) (@lem2750238 A B m x)). Qed.
Lemma lem2750240 {A B : Type'} (m : type1211 A B) (x : A) : (term48 A B m x) = (term50 A B m x).
Proof. exact (EQ_MP (@lem2750239 A B m x) (@lem2750231 A B m x)). Qed.
Lemma lem2750241 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem2750242 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term54 A B m x y) = (term55 A B m x y).
Proof. exact (MK_COMB (@lem2750240 A B m x) (@lem2750241 B y)). Qed.
Lemma lem2750244 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2750245 {B : Type'} (f : B -> int) (y : B) : (term56 B f y) = (f y).
Proof. exact (@lem2750244 B int f y). Qed.
Lemma lem2750246 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term57 A B m x y) = (term55 A B m x y).
Proof. exact (@lem2750245 B (term50 A B m x) y). Qed.
Lemma lem2750247 {A B : Type'} (m : type1211 A B) (x : A) (b : B) : (term55 A B m x b) = (term58 A B m x b).
Proof. exact (eq_refl (term55 A B m x b)). Qed.
Lemma lem2750248 {A B : Type'} (m : type1211 A B) (x : A) : (term59 A B m x) = (term50 A B m x).
Proof. exact (fun_ext (fun b : B => @lem2750247 A B m x b)). Qed.
Lemma lem2750249 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem2750250 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term57 A B m x y) = (term55 A B m x y).
Proof. exact (MK_COMB (@lem2750248 A B m x) (@lem2750249 B y)). Qed.
Lemma lem2750251 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2750252 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term60 A B m x y) = (term61 A B m x y).
Proof. exact (MK_COMB (@lem2750251) (@lem2750250 A B m x y)). Qed.
Lemma lem2750253 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term55 A B m x y) = (term58 A B m x y).
Proof. exact (eq_refl (term55 A B m x y)). Qed.
Lemma lem2750254 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : ((term57 A B m x y) = (term55 A B m x y)) = ((term55 A B m x y) = (term58 A B m x y)).
Proof. exact (MK_COMB (@lem2750252 A B m x y) (@lem2750253 A B m x y)). Qed.
Lemma lem2750255 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term55 A B m x y) = (term58 A B m x y).
Proof. exact (EQ_MP (@lem2750254 A B m x y) (@lem2750246 A B m x y)). Qed.
Lemma lem2750256 {A B : Type'} (m : type1211 A B) (x : A) (y : B) : (term54 A B m x y) = (term58 A B m x y).
Proof. exact (TRANS (@lem2750242 A B m x y) (@lem2750255 A B m x y)). Qed.
Lemma lem2750257 {A B : Type'} (x' : A) (y' : B) (m : type1211 A B) (x : A) (y : B) : (term92 A B x' y' m x y) = (term93 A B x' y' m x y).
Proof. exact (MK_COMB (@lem2750227 A B m x' y') (@lem2750256 A B m x y)). Qed.
Lemma lem2750258 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2750259 {A B : Type'} (x' : A) (y' : B) (m : type1211 A B) (x : A) (y : B) : (term94 A B x' y' m x y) = (term95 A B x' y' m x y).
Proof. exact (MK_COMB (@lem2750258) (@lem2750257 A B x' y' m x y)). Qed.
Lemma lem2750261 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2750262 {A B : Type'} (f : type1413 A B) (y : A) : (term96 A B f y) = (f y).
Proof. exact (@lem2750261 A (B -> Prop) f y). Qed.
Lemma lem2750263 {A B : Type'} (P : type1210 A B) (x' : A) : (term97 A B P x') = (term98 A B P x').
Proof. exact (@lem2750262 A B (term99 A B P) x'). Qed.
Lemma lem2750264 {A B : Type'} (P : type1210 A B) (a : A) : (term98 A B P a) = (term100 A B P a).
Proof. exact (eq_refl (term98 A B P a)). Qed.
Lemma lem2750265 {A B : Type'} (P : type1210 A B) : (term101 A B P) = (term99 A B P).
Proof. exact (fun_ext (fun a : A => @lem2750264 A B P a)). Qed.
Lemma lem2750266 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem2750267 {A B : Type'} (P : type1210 A B) (x' : A) : (term97 A B P x') = (term98 A B P x').
Proof. exact (MK_COMB (@lem2750265 A B P) (@lem2750266 A x')). Qed.
Lemma lem2750268 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem2750269 {A B : Type'} (P : type1210 A B) (x' : A) : (term102 A B P x') = (term103 A B P x').
Proof. exact (MK_COMB (@lem2750268 B) (@lem2750267 A B P x')). Qed.
Lemma lem2750270 {A B : Type'} (P : type1210 A B) (x' : A) : (term98 A B P x') = (term100 A B P x').
Proof. exact (eq_refl (term98 A B P x')). Qed.
Lemma lem2750271 {A B : Type'} (P : type1210 A B) (x' : A) : ((term97 A B P x') = (term98 A B P x')) = ((term98 A B P x') = (term100 A B P x')).
Proof. exact (MK_COMB (@lem2750269 A B P x') (@lem2750270 A B P x')). Qed.
Lemma lem2750272 {A B : Type'} (P : type1210 A B) (x' : A) : (term98 A B P x') = (term100 A B P x').
Proof. exact (EQ_MP (@lem2750271 A B P x') (@lem2750263 A B P x')). Qed.
Lemma lem2750273 {B : Type'} (y' : B) : y' = y'.
Proof. exact (eq_refl y'). Qed.
Lemma lem2750274 {A B : Type'} (P : type1210 A B) (x' : A) (y' : B) : (term104 A B P x' y') = (term105 A B P x' y').
Proof. exact (MK_COMB (@lem2750272 A B P x') (@lem2750273 B y')). Qed.
Lemma lem2750276 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2750277 {B : Type'} (f : B -> Prop) (y : B) : (term106 B f y) = (f y).
Proof. exact (@lem2750276 B Prop f y). Qed.
Lemma lem2750278 {A B : Type'} (P : type1210 A B) (x' : A) (y' : B) : (term107 A B P x' y') = (term105 A B P x' y').
Proof. exact (@lem2750277 B (term100 A B P x') y'). Qed.
Lemma lem2750279 {A B : Type'} (P : type1210 A B) (x' : A) (b : B) : (term105 A B P x' b) = (term108 A B P x' b).
Proof. exact (eq_refl (term105 A B P x' b)). Qed.
Lemma lem2750280 {A B : Type'} (P : type1210 A B) (x' : A) : (term109 A B P x') = (term100 A B P x').
Proof. exact (fun_ext (fun b : B => @lem2750279 A B P x' b)). Qed.
Lemma lem2750281 {B : Type'} (y' : B) : y' = y'.
Proof. exact (eq_refl y'). Qed.
Lemma lem2750282 {A B : Type'} (P : type1210 A B) (x' : A) (y' : B) : (term107 A B P x' y') = (term105 A B P x' y').
Proof. exact (MK_COMB (@lem2750280 A B P x') (@lem2750281 B y')). Qed.
Lemma lem2750283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2750284 {A B : Type'} (P : type1210 A B) (x' : A) (y' : B) : (term110 A B P x' y') = (term111 A B P x' y').
Proof. exact (MK_COMB (@lem2750283) (@lem2750282 A B P x' y')). Qed.
Lemma lem2750285 {A B : Type'} (P : type1210 A B) (x' : A) (y' : B) : (term105 A B P x' y') = (term108 A B P x' y').
Proof. exact (eq_refl (term105 A B P x' y')). Qed.
Lemma lem2750286 {A B : Type'} (P : type1210 A B) (x' : A) (y' : B) : ((term107 A B P x' y') = (term105 A B P x' y')) = ((term105 A B P x' y') = (term108 A B P x' y')).
Proof. exact (MK_COMB (@lem2750284 A B P x' y') (@lem2750285 A B P x' y')). Qed.
Lemma lem2750287 {A B : Type'} (P : type1210 A B) (x' : A) (y' : B) : (term105 A B P x' y') = (term108 A B P x' y').
Proof. exact (EQ_MP (@lem2750286 A B P x' y') (@lem2750278 A B P x' y')). Qed.
Lemma lem2750288 {A B : Type'} (P : type1210 A B) (x' : A) (y' : B) : (term104 A B P x' y') = (term108 A B P x' y').
Proof. exact (TRANS (@lem2750274 A B P x' y') (@lem2750287 A B P x' y')). Qed.
Lemma lem2750289 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) (x' : A) (y' : B) : (term112 A B m x y P x' y') = (term113 A B m x y P x' y').
Proof. exact (MK_COMB (@lem2750259 A B x' y' m x y) (@lem2750288 A B P x' y')). Qed.
Lemma lem2750292 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) (x' : A) : (term114 A B m x y P x') = (term115 A B m x y P x').
Proof. exact (fun_ext (fun y' : B => @lem2750289 A B m x y P x' y')). Qed.
Lemma lem2750293 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem2750294 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) (x' : A) : (term116 A B m x y P x') = (term117 A B m x y P x').
Proof. exact (MK_COMB (@lem2750293 B) (@lem2750292 A B m x y P x')). Qed.
Lemma lem2750301 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) : (term118 A B m x y P) = (term119 A B m x y P).
Proof. exact (fun_ext (fun x' : A => @lem2750294 A B m x y P x')). Qed.
Lemma lem2750302 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2750303 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) : (term120 A B m x y P) = (term121 A B m x y P).
Proof. exact (MK_COMB (@lem2750302 A) (@lem2750301 A B m x y P)). Qed.
Lemma lem2750305 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term1 _5106 _5107 P) = (term0 _5106 _5107 P).
Proof. exact (EQ_MP (@lem2749930 _5106 _5107 P) (@lem2749929 _5106 _5107 P)). Qed.
Lemma lem2750306 {A B : Type'} (P : type1210 A B) : (term73 A B P) = (term74 A B P).
Proof. exact (@lem2750305 B A P). Qed.
Lemma lem2750307 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) : (term122 A B m x y P) = (term123 A B m x y P).
Proof. exact (@lem2750306 A B (term124 A B m x y P)). Qed.
Lemma lem2750308 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) (x' : A) (y' : B) : (term125 A B m x y P x' y') = (term113 A B m x y P x' y').
Proof. exact (eq_refl (term125 A B m x y P x' y')). Qed.
Lemma lem2750309 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) (x' : A) : (term126 A B m x y P x') = (term115 A B m x y P x').
Proof. exact (fun_ext (fun y' : B => @lem2750308 A B m x y P x' y')). Qed.
Lemma lem2750310 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem2750311 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) (x' : A) : (term127 A B m x y P x') = (term117 A B m x y P x').
Proof. exact (MK_COMB (@lem2750310 B) (@lem2750309 A B m x y P x')). Qed.
Lemma lem2750312 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) : (term128 A B m x y P) = (term119 A B m x y P).
Proof. exact (fun_ext (fun x' : A => @lem2750311 A B m x y P x')). Qed.
Lemma lem2750313 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2750314 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) : (term122 A B m x y P) = (term121 A B m x y P).
Proof. exact (MK_COMB (@lem2750313 A) (@lem2750312 A B m x y P)). Qed.
Lemma lem2750315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2750316 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) : (term129 A B m x y P) = (term130 A B m x y P).
Proof. exact (MK_COMB (@lem2750315) (@lem2750314 A B m x y P)). Qed.
Lemma lem2750317 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) (p : prod A B) : (term131 A B m x y P p) = (term132 A B m x y P p).
Proof. exact (eq_refl (term131 A B m x y P p)). Qed.
Lemma lem2750318 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) : (term133 A B m x y P) = (term124 A B m x y P).
Proof. exact (fun_ext (fun p : prod A B => @lem2750317 A B m x y P p)). Qed.
Lemma lem2750319 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem2750320 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) : (term123 A B m x y P) = (term134 A B m x y P).
Proof. exact (MK_COMB (@lem2750319 A B) (@lem2750318 A B m x y P)). Qed.
Lemma lem2750321 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) : ((term122 A B m x y P) = (term123 A B m x y P)) = ((term121 A B m x y P) = (term134 A B m x y P)).
Proof. exact (MK_COMB (@lem2750316 A B m x y P) (@lem2750320 A B m x y P)). Qed.
Lemma lem2750322 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) : (term121 A B m x y P) = (term134 A B m x y P).
Proof. exact (EQ_MP (@lem2750321 A B m x y P) (@lem2750307 A B m x y P)). Qed.
Lemma lem2750331 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) : (term120 A B m x y P) = (term134 A B m x y P).
Proof. exact (TRANS (@lem2750303 A B m x y P) (@lem2750322 A B m x y P)). Qed.
Lemma lem2750332 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2750333 {A B : Type'} (m : type1211 A B) (x : A) (y : B) (P : type1210 A B) : (term135 A B m x y P) = (term136 A B m x y P).
Proof. exact (MK_COMB (@lem2750332) (@lem2750331 A B m x y P)). Qed.
Lemma lem2750335 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2750336 {A B : Type'} (f : type1413 A B) (y : A) : (term96 A B f y) = (f y).
Proof. exact (@lem2750335 A (B -> Prop) f y). Qed.
Lemma lem2750337 {A B : Type'} (P : type1210 A B) (x : A) : (term97 A B P x) = (term98 A B P x).
Proof. exact (@lem2750336 A B (term99 A B P) x). Qed.
Lemma lem2750338 {A B : Type'} (P : type1210 A B) (a : A) : (term98 A B P a) = (term100 A B P a).
Proof. exact (eq_refl (term98 A B P a)). Qed.
Lemma lem2750339 {A B : Type'} (P : type1210 A B) : (term101 A B P) = (term99 A B P).
Proof. exact (fun_ext (fun a : A => @lem2750338 A B P a)). Qed.
Lemma lem2750340 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2750341 {A B : Type'} (P : type1210 A B) (x : A) : (term97 A B P x) = (term98 A B P x).
Proof. exact (MK_COMB (@lem2750339 A B P) (@lem2750340 A x)). Qed.
Lemma lem2750342 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem2750343 {A B : Type'} (P : type1210 A B) (x : A) : (term102 A B P x) = (term103 A B P x).
Proof. exact (MK_COMB (@lem2750342 B) (@lem2750341 A B P x)). Qed.
Lemma lem2750344 {A B : Type'} (P : type1210 A B) (x : A) : (term98 A B P x) = (term100 A B P x).
Proof. exact (eq_refl (term98 A B P x)). Qed.
Lemma lem2750345 {A B : Type'} (P : type1210 A B) (x : A) : ((term97 A B P x) = (term98 A B P x)) = ((term98 A B P x) = (term100 A B P x)).
Proof. exact (MK_COMB (@lem2750343 A B P x) (@lem2750344 A B P x)). Qed.
Lemma lem2750346 {A B : Type'} (P : type1210 A B) (x : A) : (term98 A B P x) = (term100 A B P x).
Proof. exact (EQ_MP (@lem2750345 A B P x) (@lem2750337 A B P x)). Qed.
Lemma lem2750347 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem2750348 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : (term104 A B P x y) = (term105 A B P x y).
Proof. exact (MK_COMB (@lem2750346 A B P x) (@lem2750347 B y)). Qed.
Lemma lem2750350 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2750351 {B : Type'} (f : B -> Prop) (y : B) : (term106 B f y) = (f y).
Proof. exact (@lem2750350 B Prop f y). Qed.
Lemma lem2750352 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : (term107 A B P x y) = (term105 A B P x y).
Proof. exact (@lem2750351 B (term100 A B P x) y). Qed.
Lemma lem2750353 {A B : Type'} (P : type1210 A B) (x : A) (b : B) : (term105 A B P x b) = (term108 A B P x b).
Proof. exact (eq_refl (term105 A B P x b)). Qed.
Lemma lem2750354 {A B : Type'} (P : type1210 A B) (x : A) : (term109 A B P x) = (term100 A B P x).
Proof. exact (fun_ext (fun b : B => @lem2750353 A B P x b)). Qed.
Lemma lem2750355 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem2750356 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : (term107 A B P x y) = (term105 A B P x y).
Proof. exact (MK_COMB (@lem2750354 A B P x) (@lem2750355 B y)). Qed.
Lemma lem2750357 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2750358 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : (term110 A B P x y) = (term111 A B P x y).
Proof. exact (MK_COMB (@lem2750357) (@lem2750356 A B P x y)). Qed.
Lemma lem2750359 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : (term105 A B P x y) = (term108 A B P x y).
Proof. exact (eq_refl (term105 A B P x y)). Qed.
Lemma lem2750360 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : ((term107 A B P x y) = (term105 A B P x y)) = ((term105 A B P x y) = (term108 A B P x y)).
Proof. exact (MK_COMB (@lem2750358 A B P x y) (@lem2750359 A B P x y)). Qed.
Lemma lem2750361 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : (term105 A B P x y) = (term108 A B P x y).
Proof. exact (EQ_MP (@lem2750360 A B P x y) (@lem2750352 A B P x y)). Qed.
Lemma lem2750362 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : (term104 A B P x y) = (term108 A B P x y).
Proof. exact (TRANS (@lem2750348 A B P x y) (@lem2750361 A B P x y)). Qed.
Lemma lem2750363 {A B : Type'} (m : type1211 A B) (P : type1210 A B) (x : A) (y : B) : (term137 A B m P x y) = (term138 A B m P x y).
Proof. exact (MK_COMB (@lem2750333 A B m x y P) (@lem2750362 A B P x y)). Qed.
Lemma lem2750366 {A B : Type'} (m : type1211 A B) (P : type1210 A B) (x : A) : (term139 A B m P x) = (term140 A B m P x).
Proof. exact (fun_ext (fun y : B => @lem2750363 A B m P x y)). Qed.
Lemma lem2750367 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem2750368 {A B : Type'} (m : type1211 A B) (P : type1210 A B) (x : A) : (term141 A B m P x) = (term142 A B m P x).
Proof. exact (MK_COMB (@lem2750367 B) (@lem2750366 A B m P x)). Qed.
Lemma lem2750375 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term143 A B m P) = (term144 A B m P).
Proof. exact (fun_ext (fun x : A => @lem2750368 A B m P x)). Qed.
Lemma lem2750376 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2750377 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term145 A B m P) = (term146 A B m P).
Proof. exact (MK_COMB (@lem2750376 A) (@lem2750375 A B m P)). Qed.
Lemma lem2750379 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term1 _5106 _5107 P) = (term0 _5106 _5107 P).
Proof. exact (EQ_MP (@lem2749930 _5106 _5107 P) (@lem2749929 _5106 _5107 P)). Qed.
Lemma lem2750380 {A B : Type'} (P : type1210 A B) : (term73 A B P) = (term74 A B P).
Proof. exact (@lem2750379 B A P). Qed.
Lemma lem2750381 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term147 A B m P) = (term148 A B m P).
Proof. exact (@lem2750380 A B (term149 A B m P)). Qed.
Lemma lem2750382 {A B : Type'} (m : type1211 A B) (P : type1210 A B) (x : A) (y : B) : (term150 A B m P x y) = (term138 A B m P x y).
Proof. exact (eq_refl (term150 A B m P x y)). Qed.
Lemma lem2750383 {A B : Type'} (m : type1211 A B) (P : type1210 A B) (x : A) : (term151 A B m P x) = (term140 A B m P x).
Proof. exact (fun_ext (fun y : B => @lem2750382 A B m P x y)). Qed.
Lemma lem2750384 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem2750385 {A B : Type'} (m : type1211 A B) (P : type1210 A B) (x : A) : (term152 A B m P x) = (term142 A B m P x).
Proof. exact (MK_COMB (@lem2750384 B) (@lem2750383 A B m P x)). Qed.
Lemma lem2750386 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term153 A B m P) = (term144 A B m P).
Proof. exact (fun_ext (fun x : A => @lem2750385 A B m P x)). Qed.
Lemma lem2750387 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2750388 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term147 A B m P) = (term146 A B m P).
Proof. exact (MK_COMB (@lem2750387 A) (@lem2750386 A B m P)). Qed.
Lemma lem2750389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2750390 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term154 A B m P) = (term155 A B m P).
Proof. exact (MK_COMB (@lem2750389) (@lem2750388 A B m P)). Qed.
Lemma lem2750391 {A B : Type'} (m : type1211 A B) (P : type1210 A B) (p : prod A B) : (term156 A B m P p) = (term157 A B m P p).
Proof. exact (eq_refl (term156 A B m P p)). Qed.
Lemma lem2750392 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term158 A B m P) = (term149 A B m P).
Proof. exact (fun_ext (fun p : prod A B => @lem2750391 A B m P p)). Qed.
Lemma lem2750393 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem2750394 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term148 A B m P) = (term159 A B m P).
Proof. exact (MK_COMB (@lem2750393 A B) (@lem2750392 A B m P)). Qed.
Lemma lem2750395 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : ((term147 A B m P) = (term148 A B m P)) = ((term146 A B m P) = (term159 A B m P)).
Proof. exact (MK_COMB (@lem2750390 A B m P) (@lem2750394 A B m P)). Qed.
Lemma lem2750396 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term146 A B m P) = (term159 A B m P).
Proof. exact (EQ_MP (@lem2750395 A B m P) (@lem2750381 A B m P)). Qed.
Lemma lem2750413 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term145 A B m P) = (term159 A B m P).
Proof. exact (TRANS (@lem2750377 A B m P) (@lem2750396 A B m P)). Qed.
Lemma lem2750414 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term160 A B m P) = (term161 A B m P).
Proof. exact (MK_COMB (@lem2750130 A B m) (@lem2750413 A B m P)). Qed.
Lemma lem2750417 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2750418 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term162 A B m P) = (term163 A B m P).
Proof. exact (MK_COMB (@lem2750417) (@lem2750414 A B m P)). Qed.
Lemma lem2750451 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2750452 {A B : Type'} (f : type1413 A B) (y : A) : (term96 A B f y) = (f y).
Proof. exact (@lem2750451 A (B -> Prop) f y). Qed.
Lemma lem2750453 {A B : Type'} (P : type1210 A B) (x : A) : (term97 A B P x) = (term98 A B P x).
Proof. exact (@lem2750452 A B (term99 A B P) x). Qed.
Lemma lem2750454 {A B : Type'} (P : type1210 A B) (a : A) : (term98 A B P a) = (term100 A B P a).
Proof. exact (eq_refl (term98 A B P a)). Qed.
Lemma lem2750455 {A B : Type'} (P : type1210 A B) : (term101 A B P) = (term99 A B P).
Proof. exact (fun_ext (fun a : A => @lem2750454 A B P a)). Qed.
Lemma lem2750456 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2750457 {A B : Type'} (P : type1210 A B) (x : A) : (term97 A B P x) = (term98 A B P x).
Proof. exact (MK_COMB (@lem2750455 A B P) (@lem2750456 A x)). Qed.
Lemma lem2750458 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem2750459 {A B : Type'} (P : type1210 A B) (x : A) : (term102 A B P x) = (term103 A B P x).
Proof. exact (MK_COMB (@lem2750458 B) (@lem2750457 A B P x)). Qed.
Lemma lem2750460 {A B : Type'} (P : type1210 A B) (x : A) : (term98 A B P x) = (term100 A B P x).
Proof. exact (eq_refl (term98 A B P x)). Qed.
Lemma lem2750461 {A B : Type'} (P : type1210 A B) (x : A) : ((term97 A B P x) = (term98 A B P x)) = ((term98 A B P x) = (term100 A B P x)).
Proof. exact (MK_COMB (@lem2750459 A B P x) (@lem2750460 A B P x)). Qed.
Lemma lem2750462 {A B : Type'} (P : type1210 A B) (x : A) : (term98 A B P x) = (term100 A B P x).
Proof. exact (EQ_MP (@lem2750461 A B P x) (@lem2750453 A B P x)). Qed.
Lemma lem2750463 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem2750464 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : (term104 A B P x y) = (term105 A B P x y).
Proof. exact (MK_COMB (@lem2750462 A B P x) (@lem2750463 B y)). Qed.
Lemma lem2750466 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem2750467 {B : Type'} (f : B -> Prop) (y : B) : (term106 B f y) = (f y).
Proof. exact (@lem2750466 B Prop f y). Qed.
Lemma lem2750468 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : (term107 A B P x y) = (term105 A B P x y).
Proof. exact (@lem2750467 B (term100 A B P x) y). Qed.
Lemma lem2750469 {A B : Type'} (P : type1210 A B) (x : A) (b : B) : (term105 A B P x b) = (term108 A B P x b).
Proof. exact (eq_refl (term105 A B P x b)). Qed.
Lemma lem2750470 {A B : Type'} (P : type1210 A B) (x : A) : (term109 A B P x) = (term100 A B P x).
Proof. exact (fun_ext (fun b : B => @lem2750469 A B P x b)). Qed.
Lemma lem2750471 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem2750472 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : (term107 A B P x y) = (term105 A B P x y).
Proof. exact (MK_COMB (@lem2750470 A B P x) (@lem2750471 B y)). Qed.
Lemma lem2750473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2750474 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : (term110 A B P x y) = (term111 A B P x y).
Proof. exact (MK_COMB (@lem2750473) (@lem2750472 A B P x y)). Qed.
Lemma lem2750475 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : (term105 A B P x y) = (term108 A B P x y).
Proof. exact (eq_refl (term105 A B P x y)). Qed.
Lemma lem2750476 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : ((term107 A B P x y) = (term105 A B P x y)) = ((term105 A B P x y) = (term108 A B P x y)).
Proof. exact (MK_COMB (@lem2750474 A B P x y) (@lem2750475 A B P x y)). Qed.
Lemma lem2750477 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : (term105 A B P x y) = (term108 A B P x y).
Proof. exact (EQ_MP (@lem2750476 A B P x y) (@lem2750468 A B P x y)). Qed.
Lemma lem2750478 {A B : Type'} (P : type1210 A B) (x : A) (y : B) : (term104 A B P x y) = (term108 A B P x y).
Proof. exact (TRANS (@lem2750464 A B P x y) (@lem2750477 A B P x y)). Qed.
Lemma lem2750479 {A B : Type'} (P : type1210 A B) (x : A) : (term164 A B P x) = (term100 A B P x).
Proof. exact (fun_ext (fun y : B => @lem2750478 A B P x y)). Qed.
Lemma lem2750480 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem2750481 {A B : Type'} (P : type1210 A B) (x : A) : (term165 A B P x) = (term166 A B P x).
Proof. exact (MK_COMB (@lem2750480 B) (@lem2750479 A B P x)). Qed.
Lemma lem2750488 {A B : Type'} (P : type1210 A B) : (term167 A B P) = (term168 A B P).
Proof. exact (fun_ext (fun x : A => @lem2750481 A B P x)). Qed.
Lemma lem2750489 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2750490 {A B : Type'} (P : type1210 A B) : (term169 A B P) = (term73 A B P).
Proof. exact (MK_COMB (@lem2750489 A) (@lem2750488 A B P)). Qed.
Lemma lem2750492 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term1 _5106 _5107 P) = (term0 _5106 _5107 P).
Proof. exact (EQ_MP (@lem2749930 _5106 _5107 P) (@lem2749929 _5106 _5107 P)). Qed.
Lemma lem2750493 {A B : Type'} (P : type1210 A B) : (term73 A B P) = (term74 A B P).
Proof. exact (@lem2750492 B A P). Qed.
Lemma lem2750500 {A B : Type'} (P : type1210 A B) : (term169 A B P) = (term74 A B P).
Proof. exact (TRANS (@lem2750490 A B P) (@lem2750493 A B P)). Qed.
Lemma lem2750501 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term41 A B m P) = (term170 A B m P).
Proof. exact (MK_COMB (@lem2750418 A B m P) (@lem2750500 A B P)). Qed.
Lemma lem2750503 {A : Type'} (m : A -> int) (P : A -> Prop) : (term9 A m P) = True.
Proof. exact (EQ_MP (@lem2749927 A m P) (@lem2749926 A m P)). Qed.
Lemma lem2750504 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term170 A B m P) = True.
Proof. exact (@lem2750503 (prod A B) m P). Qed.
Lemma lem2750505 {A B : Type'} (m : type1211 A B) (P : type1210 A B) : (term41 A B m P) = True.
Proof. exact (TRANS (@lem2750501 A B m P) (@lem2750504 A B m P)). Qed.
Lemma lem2750506 {A B : Type'} (P : type1210 A B) : (term43 A B P) = (term171 A B).
Proof. exact (fun_ext (fun m : type1211 A B => @lem2750505 A B m P)). Qed.
Lemma lem2750507 {A B : Type'} : (@all ((prod A B) -> int)) = (@all ((prod A B) -> int)).
Proof. exact (eq_refl (@all ((prod A B) -> int))). Qed.
Lemma lem2750508 {A B : Type'} (P : type1210 A B) : (term44 A B P) = (term172 A B).
Proof. exact (MK_COMB (@lem2750507 A B) (@lem2750506 A B P)). Qed.
Lemma lem2750510 {A : Type'} (t : Prop) : (term173 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2750511 {A B : Type'} (t : Prop) : (term174 A B t) = t.
Proof. exact (@lem2750510 (type1211 A B) t). Qed.
Lemma lem2750512 {A B : Type'} : (term172 A B) = True.
Proof. exact (@lem2750511 A B True). Qed.
Lemma lem2750513 {A B : Type'} (P : type1210 A B) : (term44 A B P) = True.
Proof. exact (TRANS (@lem2750508 A B P) (@lem2750512 A B)). Qed.
Lemma lem2750514 {A B : Type'} (P : type1210 A B) : (term26 A B P) = True.
Proof. exact (TRANS (@lem2750018 A B P) (@lem2750513 A B P)). Qed.
Lemma lem2750515 {A B : Type'} : (term28 A B) = (term175 A B).
Proof. exact (fun_ext (fun P : type1210 A B => @lem2750514 A B P)). Qed.
Lemma lem2750516 {A B : Type'} : (@all ((prod A B) -> Prop)) = (@all ((prod A B) -> Prop)).
Proof. exact (eq_refl (@all ((prod A B) -> Prop))). Qed.
Lemma lem2750517 {A B : Type'} : (term29 A B) = (term176 A B).
Proof. exact (MK_COMB (@lem2750516 A B) (@lem2750515 A B)). Qed.
Lemma lem2750519 {A : Type'} (t : Prop) : (term173 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2750520 {A B : Type'} (t : Prop) : (term177 A B t) = t.
Proof. exact (@lem2750519 (type1210 A B) t). Qed.
Lemma lem2750521 {A B : Type'} : (term176 A B) = True.
Proof. exact (@lem2750520 A B True). Qed.
Lemma lem2750522 {A B : Type'} : (term29 A B) = True.
Proof. exact (TRANS (@lem2750517 A B) (@lem2750521 A B)). Qed.
Lemma lem2750523 {A B : Type'} : (term22 A B) = True.
Proof. exact (TRANS (@lem2749973 A B) (@lem2750522 A B)). Qed.
Lemma lem2750524 {A B : Type'} : True = (term22 A B).
Proof. exact (SYM (@lem2750523 A B)). Qed.
Lemma lem2750525 {A B : Type'} : term22 A B.
Proof. exact (EQ_MP (@lem2750524 A B) (@lem0)). Qed.
