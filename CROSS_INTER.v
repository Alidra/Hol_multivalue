Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CROSS_INTER_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import IN_INTER_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4360023 {_103718 _103721 : Type'} (x : _103718) : term0 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4360024 {_103718 _103721 : Type'} (x : _103718) : (term0 _103718 _103721 x) = (term1 _103718 _103721 x).
Proof. exact (eq_refl (term0 _103718 _103721 x)). Qed.
Lemma lem4360025 {_103718 _103721 : Type'} (x : _103718) : term1 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4360024 _103718 _103721 x) (@lem4360023 _103718 _103721 x)). Qed.
Lemma lem4360026 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term2 _103718 _103721 x y.
Proof. exact (@lem4360025 _103718 _103721 x y). Qed.
Lemma lem4360027 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term2 _103718 _103721 x y) = (term3 _103718 _103721 x y).
Proof. exact (eq_refl (term2 _103718 _103721 x y)). Qed.
Lemma lem4360028 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term3 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4360027 _103718 _103721 x y) (@lem4360026 _103718 _103721 x y)). Qed.
Lemma lem4360029 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term4 _103718 _103721 x y s.
Proof. exact (@lem4360028 _103718 _103721 x y s). Qed.
Lemma lem4360030 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term4 _103718 _103721 x y s) = (term5 _103718 _103721 x s y).
Proof. exact (eq_refl (term4 _103718 _103721 x y s)). Qed.
Lemma lem4360031 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term5 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4360030 _103718 _103721 x s y) (@lem4360029 _103718 _103721 x y s)). Qed.
Lemma lem4360032 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term6 _103718 _103721 x s y t.
Proof. exact (@lem4360031 _103718 _103721 x s y t). Qed.
Lemma lem4360033 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term6 _103718 _103721 x s y t) = ((term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term6 _103718 _103721 x s y t)). Qed.
Lemma lem4360035 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem4360036 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem4360037 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem4360036 A s) (@lem4360035 A s)). Qed.
Lemma lem4360038 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term11 A s t.
Proof. exact (@lem4360037 A s t). Qed.
Lemma lem4360039 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = (term12 A s t).
Proof. exact (eq_refl (term11 A s t)). Qed.
Lemma lem4360040 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (EQ_MP (@lem4360039 A s t) (@lem4360038 A s t)). Qed.
Lemma lem4360041 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term13 A s t x.
Proof. exact (@lem4360040 A s t x). Qed.
Lemma lem4360042 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A s t x) = ((term14 A x s t) = (term15 A s x t)).
Proof. exact (eq_refl (term13 A s t x)). Qed.
Lemma lem4360044 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term16 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4360045 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term16 _5106 _5107 P) = ((term17 _5106 _5107 P) = (term18 _5106 _5107 P)).
Proof. exact (eq_refl (term16 _5106 _5107 P)). Qed.
Lemma lem4360047 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4360048 {A : Type'} (s : A -> Prop) : (term19 A s) = (term20 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem4360049 {A : Type'} (s : A -> Prop) : term20 A s.
Proof. exact (EQ_MP (@lem4360048 A s) (@lem4360047 A s)). Qed.
Lemma lem4360050 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term21 A s t.
Proof. exact (@lem4360049 A s t). Qed.
Lemma lem4360051 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term21 A s t) = ((s = t) = (term22 A s t)).
Proof. exact (eq_refl (term21 A s t)). Qed.
Lemma lem4360076 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term22 A s t).
Proof. exact (EQ_MP (@lem4360051 A s t) (@lem4360050 A s t)). Qed.
Lemma lem4360077 {_104453 _104454 : Type'} (s : type1210 _104453 _104454) (t : type1210 _104453 _104454) : (s = t) = (term23 _104453 _104454 s t).
Proof. exact (@lem4360076 (prod _104453 _104454) s t). Qed.
Lemma lem4360078 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : ((term24 _104453 _104454 s t u) = (term25 _104453 _104454 t s u)) = (term26 _104453 _104454 t s u).
Proof. exact (@lem4360077 _104453 _104454 (term24 _104453 _104454 s t u) (term25 _104453 _104454 t s u)). Qed.
Lemma lem4360084 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term17 _5106 _5107 P) = (term18 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4360045 _5106 _5107 P) (@lem4360044 _5106 _5107 P)). Qed.
Lemma lem4360085 {_104453 _104454 : Type'} (P : type1210 _104453 _104454) : (term27 _104453 _104454 P) = (term28 _104453 _104454 P).
Proof. exact (@lem4360084 _104454 _104453 P). Qed.
Lemma lem4360086 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term29 _104453 _104454 t s u) = (term30 _104453 _104454 t s u).
Proof. exact (@lem4360085 _104453 _104454 (term31 _104453 _104454 t s u)). Qed.
Lemma lem4360087 {_104453 _104454 : Type'} (x : prod _104453 _104454) (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term32 _104453 _104454 t s u x) = ((term33 _104453 _104454 x s t u) = (term34 _104453 _104454 x t s u)).
Proof. exact (eq_refl (term32 _104453 _104454 t s u x)). Qed.
Lemma lem4360088 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term35 _104453 _104454 t s u) = (term31 _104453 _104454 t s u).
Proof. exact (fun_ext (fun x : prod _104453 _104454 => @lem4360087 _104453 _104454 x t s u)). Qed.
Lemma lem4360089 {_104453 _104454 : Type'} : (@all (prod _104453 _104454)) = (@all (prod _104453 _104454)).
Proof. exact (eq_refl (@all (prod _104453 _104454))). Qed.
Lemma lem4360090 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term29 _104453 _104454 t s u) = (term26 _104453 _104454 t s u).
Proof. exact (MK_COMB (@lem4360089 _104453 _104454) (@lem4360088 _104453 _104454 t s u)). Qed.
Lemma lem4360091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360092 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term36 _104453 _104454 t s u) = (term37 _104453 _104454 t s u).
Proof. exact (MK_COMB (@lem4360091) (@lem4360090 _104453 _104454 t s u)). Qed.
Lemma lem4360093 {_104453 _104454 : Type'} (p1 : _104453) (p2 : _104454) (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term38 _104453 _104454 t s u p1 p2) = ((term39 _104453 _104454 p1 p2 s t u) = (term40 _104453 _104454 p1 p2 t s u)).
Proof. exact (eq_refl (term38 _104453 _104454 t s u p1 p2)). Qed.
Lemma lem4360094 {_104453 _104454 : Type'} (p1 : _104453) (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term41 _104453 _104454 t s u p1) = (term42 _104453 _104454 p1 t s u).
Proof. exact (fun_ext (fun p2 : _104454 => @lem4360093 _104453 _104454 p1 p2 t s u)). Qed.
Lemma lem4360095 {_104454 : Type'} : (@all _104454) = (@all _104454).
Proof. exact (eq_refl (@all _104454)). Qed.
Lemma lem4360096 {_104453 _104454 : Type'} (p1 : _104453) (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term43 _104453 _104454 t s u p1) = (term44 _104453 _104454 p1 t s u).
Proof. exact (MK_COMB (@lem4360095 _104454) (@lem4360094 _104453 _104454 p1 t s u)). Qed.
Lemma lem4360097 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term45 _104453 _104454 t s u) = (term46 _104453 _104454 t s u).
Proof. exact (fun_ext (fun p1 : _104453 => @lem4360096 _104453 _104454 p1 t s u)). Qed.
Lemma lem4360098 {_104453 : Type'} : (@all _104453) = (@all _104453).
Proof. exact (eq_refl (@all _104453)). Qed.
Lemma lem4360099 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term30 _104453 _104454 t s u) = (term47 _104453 _104454 t s u).
Proof. exact (MK_COMB (@lem4360098 _104453) (@lem4360097 _104453 _104454 t s u)). Qed.
Lemma lem4360100 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : ((term29 _104453 _104454 t s u) = (term30 _104453 _104454 t s u)) = ((term26 _104453 _104454 t s u) = (term47 _104453 _104454 t s u)).
Proof. exact (MK_COMB (@lem4360092 _104453 _104454 t s u) (@lem4360099 _104453 _104454 t s u)). Qed.
Lemma lem4360101 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term26 _104453 _104454 t s u) = (term47 _104453 _104454 t s u).
Proof. exact (EQ_MP (@lem4360100 _104453 _104454 t s u) (@lem4360086 _104453 _104454 t s u)). Qed.
Lemma lem4360108 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : ((term24 _104453 _104454 s t u) = (term25 _104453 _104454 t s u)) = (term47 _104453 _104454 t s u).
Proof. exact (TRANS (@lem4360078 _104453 _104454 t s u) (@lem4360101 _104453 _104454 t s u)). Qed.
Lemma lem4360120 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4360033 _103718 _103721 x s y t) (@lem4360032 _103718 _103721 x s y t)). Qed.
Lemma lem4360121 {_104453 _104454 : Type'} (x : _104453) (s : _104453 -> Prop) (y : _104454) (t : _104454 -> Prop) : (term7 _104453 _104454 x y s t) = (term8 _104453 _104454 x s y t).
Proof. exact (@lem4360120 _104453 _104454 x s y t). Qed.
Lemma lem4360122 {_104453 _104454 : Type'} (p1 : _104453) (s : _104453 -> Prop) (p2 : _104454) (t : _104454 -> Prop) (u : _104454 -> Prop) : (term39 _104453 _104454 p1 p2 s t u) = (term48 _104453 _104454 p1 s p2 t u).
Proof. exact (@lem4360121 _104453 _104454 p1 s p2 (@INTER _104454 t u)). Qed.
Lemma lem4360126 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem4360042 A s x t) (@lem4360041 A s t x)). Qed.
Lemma lem4360127 {_104454 : Type'} (s : _104454 -> Prop) (x : _104454) (t : _104454 -> Prop) : (term14 _104454 x s t) = (term15 _104454 s x t).
Proof. exact (@lem4360126 _104454 s x t). Qed.
Lemma lem4360128 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term14 _104454 p2 t u) = (term15 _104454 t p2 u).
Proof. exact (@lem4360127 _104454 t p2 u). Qed.
Lemma lem4360131 {_104453 : Type'} (p1 : _104453) (s : _104453 -> Prop) : (term49 _104453 p1 s) = (term49 _104453 p1 s).
Proof. exact (eq_refl (term49 _104453 p1 s)). Qed.
Lemma lem4360132 {_104453 _104454 : Type'} (p1 : _104453) (s : _104453 -> Prop) (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term48 _104453 _104454 p1 s p2 t u) = (term50 _104453 _104454 p1 s t p2 u).
Proof. exact (MK_COMB (@lem4360131 _104453 p1 s) (@lem4360128 _104454 t p2 u)). Qed.
Lemma lem4360135 {_104453 _104454 : Type'} (p1 : _104453) (s : _104453 -> Prop) (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term39 _104453 _104454 p1 p2 s t u) = (term50 _104453 _104454 p1 s t p2 u).
Proof. exact (TRANS (@lem4360122 _104453 _104454 p1 s p2 t u) (@lem4360132 _104453 _104454 p1 s t p2 u)). Qed.
Lemma lem4360136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360137 {_104453 _104454 : Type'} (p1 : _104453) (s : _104453 -> Prop) (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term51 _104453 _104454 p1 p2 s t u) = (term52 _104453 _104454 p1 s t p2 u).
Proof. exact (MK_COMB (@lem4360136) (@lem4360135 _104453 _104454 p1 s t p2 u)). Qed.
Lemma lem4360139 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem4360042 A s x t) (@lem4360041 A s t x)). Qed.
Lemma lem4360140 {_104453 _104454 : Type'} (s : type1210 _104453 _104454) (x : prod _104453 _104454) (t : type1210 _104453 _104454) : (term53 _104453 _104454 x s t) = (term54 _104453 _104454 s x t).
Proof. exact (@lem4360139 (prod _104453 _104454) s x t). Qed.
Lemma lem4360141 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p1 : _104453) (p2 : _104454) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term40 _104453 _104454 p1 p2 t s u) = (term55 _104453 _104454 t p1 p2 s u).
Proof. exact (@lem4360140 _104453 _104454 (@CROSS _104454 _104453 s t) (@pair _104453 _104454 p1 p2) (@CROSS _104454 _104453 s u)). Qed.
Lemma lem4360145 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4360033 _103718 _103721 x s y t) (@lem4360032 _103718 _103721 x s y t)). Qed.
Lemma lem4360146 {_104453 _104454 : Type'} (x : _104453) (s : _104453 -> Prop) (y : _104454) (t : _104454 -> Prop) : (term7 _104453 _104454 x y s t) = (term8 _104453 _104454 x s y t).
Proof. exact (@lem4360145 _104453 _104454 x s y t). Qed.
Lemma lem4360147 {_104453 _104454 : Type'} (p1 : _104453) (s : _104453 -> Prop) (p2 : _104454) (t : _104454 -> Prop) : (term7 _104453 _104454 p1 p2 s t) = (term8 _104453 _104454 p1 s p2 t).
Proof. exact (@lem4360146 _104453 _104454 p1 s p2 t). Qed.
Lemma lem4360150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4360151 {_104453 _104454 : Type'} (p1 : _104453) (s : _104453 -> Prop) (p2 : _104454) (t : _104454 -> Prop) : (term56 _104453 _104454 p1 p2 s t) = (term57 _104453 _104454 p1 s p2 t).
Proof. exact (MK_COMB (@lem4360150) (@lem4360147 _104453 _104454 p1 s p2 t)). Qed.
Lemma lem4360153 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4360033 _103718 _103721 x s y t) (@lem4360032 _103718 _103721 x s y t)). Qed.
Lemma lem4360154 {_104453 _104454 : Type'} (x : _104453) (s : _104453 -> Prop) (y : _104454) (t : _104454 -> Prop) : (term7 _104453 _104454 x y s t) = (term8 _104453 _104454 x s y t).
Proof. exact (@lem4360153 _104453 _104454 x s y t). Qed.
Lemma lem4360155 {_104453 _104454 : Type'} (p1 : _104453) (s : _104453 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term7 _104453 _104454 p1 p2 s u) = (term8 _104453 _104454 p1 s p2 u).
Proof. exact (@lem4360154 _104453 _104454 p1 s p2 u). Qed.
Lemma lem4360158 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term55 _104453 _104454 t p1 p2 s u) = (term58 _104453 _104454 t p1 s p2 u).
Proof. exact (MK_COMB (@lem4360151 _104453 _104454 p1 s p2 t) (@lem4360155 _104453 _104454 p1 s p2 u)). Qed.
Lemma lem4360161 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term40 _104453 _104454 p1 p2 t s u) = (term58 _104453 _104454 t p1 s p2 u).
Proof. exact (TRANS (@lem4360141 _104453 _104454 t p1 p2 s u) (@lem4360158 _104453 _104454 t p1 s p2 u)). Qed.
Lemma lem4360162 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : ((term39 _104453 _104454 p1 p2 s t u) = (term40 _104453 _104454 p1 p2 t s u)) = ((term50 _104453 _104454 p1 s t p2 u) = (term58 _104453 _104454 t p1 s p2 u)).
Proof. exact (MK_COMB (@lem4360137 _104453 _104454 p1 s t p2 u) (@lem4360161 _104453 _104454 t p1 s p2 u)). Qed.
Lemma lem4360167 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term42 _104453 _104454 p1 t s u) = (term59 _104453 _104454 t p1 s u).
Proof. exact (fun_ext (fun p2 : _104454 => @lem4360162 _104453 _104454 t p1 s p2 u)). Qed.
Lemma lem4360168 {_104454 : Type'} : (@all _104454) = (@all _104454).
Proof. exact (eq_refl (@all _104454)). Qed.
Lemma lem4360169 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term44 _104453 _104454 p1 t s u) = (term60 _104453 _104454 t p1 s u).
Proof. exact (MK_COMB (@lem4360168 _104454) (@lem4360167 _104453 _104454 t p1 s u)). Qed.
Lemma lem4360176 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term46 _104453 _104454 t s u) = (term61 _104453 _104454 t s u).
Proof. exact (fun_ext (fun p1 : _104453 => @lem4360169 _104453 _104454 t p1 s u)). Qed.
Lemma lem4360177 {_104453 : Type'} : (@all _104453) = (@all _104453).
Proof. exact (eq_refl (@all _104453)). Qed.
Lemma lem4360178 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : (term47 _104453 _104454 t s u) = (term62 _104453 _104454 t s u).
Proof. exact (MK_COMB (@lem4360177 _104453) (@lem4360176 _104453 _104454 t s u)). Qed.
Lemma lem4360185 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : ((term24 _104453 _104454 s t u) = (term25 _104453 _104454 t s u)) = (term62 _104453 _104454 t s u).
Proof. exact (TRANS (@lem4360108 _104453 _104454 t s u) (@lem4360178 _104453 _104454 t s u)). Qed.
Lemma lem4360186 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) : (term63 _104453 _104454 t s) = (term64 _104453 _104454 t s).
Proof. exact (fun_ext (fun u : _104454 -> Prop => @lem4360185 _104453 _104454 t s u)). Qed.
Lemma lem4360187 {_104454 : Type'} : (@all (_104454 -> Prop)) = (@all (_104454 -> Prop)).
Proof. exact (eq_refl (@all (_104454 -> Prop))). Qed.
Lemma lem4360188 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) : (term65 _104453 _104454 t s) = (term66 _104453 _104454 t s).
Proof. exact (MK_COMB (@lem4360187 _104454) (@lem4360186 _104453 _104454 t s)). Qed.
Lemma lem4360195 {_104453 _104454 : Type'} (s : _104453 -> Prop) : (term67 _104453 _104454 s) = (term68 _104453 _104454 s).
Proof. exact (fun_ext (fun t : _104454 -> Prop => @lem4360188 _104453 _104454 t s)). Qed.
Lemma lem4360196 {_104454 : Type'} : (@all (_104454 -> Prop)) = (@all (_104454 -> Prop)).
Proof. exact (eq_refl (@all (_104454 -> Prop))). Qed.
Lemma lem4360197 {_104453 _104454 : Type'} (s : _104453 -> Prop) : (term69 _104453 _104454 s) = (term70 _104453 _104454 s).
Proof. exact (MK_COMB (@lem4360196 _104454) (@lem4360195 _104453 _104454 s)). Qed.
Lemma lem4360204 {_104453 _104454 : Type'} : (term71 _104453 _104454) = (term72 _104453 _104454).
Proof. exact (fun_ext (fun s : _104453 -> Prop => @lem4360197 _104453 _104454 s)). Qed.
Lemma lem4360205 {_104453 : Type'} : (@all (_104453 -> Prop)) = (@all (_104453 -> Prop)).
Proof. exact (eq_refl (@all (_104453 -> Prop))). Qed.
Lemma lem4360206 {_104453 _104454 : Type'} : (term73 _104453 _104454) = (term74 _104453 _104454).
Proof. exact (MK_COMB (@lem4360205 _104453) (@lem4360204 _104453 _104454)). Qed.
Lemma lem4360213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4360214 {_104453 _104454 : Type'} : (term75 _104453 _104454) = (term76 _104453 _104454).
Proof. exact (MK_COMB (@lem4360213) (@lem4360206 _104453 _104454)). Qed.
Lemma lem4360236 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term22 A s t).
Proof. exact (EQ_MP (@lem4360051 A s t) (@lem4360050 A s t)). Qed.
Lemma lem4360237 {_104486 _104487 : Type'} (s : type1210 _104486 _104487) (t : type1210 _104486 _104487) : (s = t) = (term23 _104486 _104487 s t).
Proof. exact (@lem4360236 (prod _104486 _104487) s t). Qed.
Lemma lem4360238 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : ((term77 _104486 _104487 s t u) = (term78 _104486 _104487 s t u)) = (term79 _104486 _104487 s t u).
Proof. exact (@lem4360237 _104486 _104487 (term77 _104486 _104487 s t u) (term78 _104486 _104487 s t u)). Qed.
Lemma lem4360244 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term17 _5106 _5107 P) = (term18 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4360045 _5106 _5107 P) (@lem4360044 _5106 _5107 P)). Qed.
Lemma lem4360245 {_104486 _104487 : Type'} (P : type1210 _104486 _104487) : (term27 _104486 _104487 P) = (term28 _104486 _104487 P).
Proof. exact (@lem4360244 _104487 _104486 P). Qed.
Lemma lem4360246 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term80 _104486 _104487 s t u) = (term81 _104486 _104487 s t u).
Proof. exact (@lem4360245 _104486 _104487 (term82 _104486 _104487 s t u)). Qed.
Lemma lem4360247 {_104486 _104487 : Type'} (x : prod _104486 _104487) (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term83 _104486 _104487 s t u x) = ((term84 _104486 _104487 x s t u) = (term85 _104486 _104487 x s t u)).
Proof. exact (eq_refl (term83 _104486 _104487 s t u x)). Qed.
Lemma lem4360248 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term86 _104486 _104487 s t u) = (term82 _104486 _104487 s t u).
Proof. exact (fun_ext (fun x : prod _104486 _104487 => @lem4360247 _104486 _104487 x s t u)). Qed.
Lemma lem4360249 {_104486 _104487 : Type'} : (@all (prod _104486 _104487)) = (@all (prod _104486 _104487)).
Proof. exact (eq_refl (@all (prod _104486 _104487))). Qed.
Lemma lem4360250 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term80 _104486 _104487 s t u) = (term79 _104486 _104487 s t u).
Proof. exact (MK_COMB (@lem4360249 _104486 _104487) (@lem4360248 _104486 _104487 s t u)). Qed.
Lemma lem4360251 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360252 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term87 _104486 _104487 s t u) = (term88 _104486 _104487 s t u).
Proof. exact (MK_COMB (@lem4360251) (@lem4360250 _104486 _104487 s t u)). Qed.
Lemma lem4360253 {_104486 _104487 : Type'} (p1 : _104486) (p2 : _104487) (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term89 _104486 _104487 s t u p1 p2) = ((term90 _104486 _104487 p1 p2 s t u) = (term91 _104486 _104487 p1 p2 s t u)).
Proof. exact (eq_refl (term89 _104486 _104487 s t u p1 p2)). Qed.
Lemma lem4360254 {_104486 _104487 : Type'} (p1 : _104486) (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term92 _104486 _104487 s t u p1) = (term93 _104486 _104487 p1 s t u).
Proof. exact (fun_ext (fun p2 : _104487 => @lem4360253 _104486 _104487 p1 p2 s t u)). Qed.
Lemma lem4360255 {_104487 : Type'} : (@all _104487) = (@all _104487).
Proof. exact (eq_refl (@all _104487)). Qed.
Lemma lem4360256 {_104486 _104487 : Type'} (p1 : _104486) (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term94 _104486 _104487 s t u p1) = (term95 _104486 _104487 p1 s t u).
Proof. exact (MK_COMB (@lem4360255 _104487) (@lem4360254 _104486 _104487 p1 s t u)). Qed.
Lemma lem4360257 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term96 _104486 _104487 s t u) = (term97 _104486 _104487 s t u).
Proof. exact (fun_ext (fun p1 : _104486 => @lem4360256 _104486 _104487 p1 s t u)). Qed.
Lemma lem4360258 {_104486 : Type'} : (@all _104486) = (@all _104486).
Proof. exact (eq_refl (@all _104486)). Qed.
Lemma lem4360259 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term81 _104486 _104487 s t u) = (term98 _104486 _104487 s t u).
Proof. exact (MK_COMB (@lem4360258 _104486) (@lem4360257 _104486 _104487 s t u)). Qed.
Lemma lem4360260 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : ((term80 _104486 _104487 s t u) = (term81 _104486 _104487 s t u)) = ((term79 _104486 _104487 s t u) = (term98 _104486 _104487 s t u)).
Proof. exact (MK_COMB (@lem4360252 _104486 _104487 s t u) (@lem4360259 _104486 _104487 s t u)). Qed.
Lemma lem4360261 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term79 _104486 _104487 s t u) = (term98 _104486 _104487 s t u).
Proof. exact (EQ_MP (@lem4360260 _104486 _104487 s t u) (@lem4360246 _104486 _104487 s t u)). Qed.
Lemma lem4360268 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : ((term77 _104486 _104487 s t u) = (term78 _104486 _104487 s t u)) = (term98 _104486 _104487 s t u).
Proof. exact (TRANS (@lem4360238 _104486 _104487 s t u) (@lem4360261 _104486 _104487 s t u)). Qed.
Lemma lem4360280 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4360033 _103718 _103721 x s y t) (@lem4360032 _103718 _103721 x s y t)). Qed.
Lemma lem4360281 {_104486 _104487 : Type'} (x : _104486) (s : _104486 -> Prop) (y : _104487) (t : _104487 -> Prop) : (term7 _104486 _104487 x y s t) = (term8 _104486 _104487 x s y t).
Proof. exact (@lem4360280 _104486 _104487 x s y t). Qed.
Lemma lem4360282 {_104486 _104487 : Type'} (p1 : _104486) (s : _104486 -> Prop) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term90 _104486 _104487 p1 p2 s t u) = (term99 _104486 _104487 p1 s t p2 u).
Proof. exact (@lem4360281 _104486 _104487 p1 (@INTER _104486 s t) p2 u). Qed.
Lemma lem4360286 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem4360042 A s x t) (@lem4360041 A s t x)). Qed.
Lemma lem4360287 {_104486 : Type'} (s : _104486 -> Prop) (x : _104486) (t : _104486 -> Prop) : (term14 _104486 x s t) = (term15 _104486 s x t).
Proof. exact (@lem4360286 _104486 s x t). Qed.
Lemma lem4360288 {_104486 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) : (term14 _104486 p1 s t) = (term15 _104486 s p1 t).
Proof. exact (@lem4360287 _104486 s p1 t). Qed.
Lemma lem4360291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4360292 {_104486 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) : (term100 _104486 p1 s t) = (term101 _104486 s p1 t).
Proof. exact (MK_COMB (@lem4360291) (@lem4360288 _104486 s p1 t)). Qed.
Lemma lem4360293 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (@IN _104487 p2 u) = (@IN _104487 p2 u).
Proof. exact (eq_refl (@IN _104487 p2 u)). Qed.
Lemma lem4360294 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term99 _104486 _104487 p1 s t p2 u) = (term102 _104486 _104487 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4360292 _104486 s p1 t) (@lem4360293 _104487 p2 u)). Qed.
Lemma lem4360297 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term90 _104486 _104487 p1 p2 s t u) = (term102 _104486 _104487 s p1 t p2 u).
Proof. exact (TRANS (@lem4360282 _104486 _104487 p1 s t p2 u) (@lem4360294 _104486 _104487 s p1 t p2 u)). Qed.
Lemma lem4360298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360299 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term103 _104486 _104487 p1 p2 s t u) = (term104 _104486 _104487 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4360298) (@lem4360297 _104486 _104487 s p1 t p2 u)). Qed.
Lemma lem4360301 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem4360042 A s x t) (@lem4360041 A s t x)). Qed.
Lemma lem4360302 {_104486 _104487 : Type'} (s : type1210 _104486 _104487) (x : prod _104486 _104487) (t : type1210 _104486 _104487) : (term53 _104486 _104487 x s t) = (term54 _104486 _104487 s x t).
Proof. exact (@lem4360301 (prod _104486 _104487) s x t). Qed.
Lemma lem4360303 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (p2 : _104487) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term91 _104486 _104487 p1 p2 s t u) = (term105 _104486 _104487 s p1 p2 t u).
Proof. exact (@lem4360302 _104486 _104487 (@CROSS _104487 _104486 s u) (@pair _104486 _104487 p1 p2) (@CROSS _104487 _104486 t u)). Qed.
Lemma lem4360307 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4360033 _103718 _103721 x s y t) (@lem4360032 _103718 _103721 x s y t)). Qed.
Lemma lem4360308 {_104486 _104487 : Type'} (x : _104486) (s : _104486 -> Prop) (y : _104487) (t : _104487 -> Prop) : (term7 _104486 _104487 x y s t) = (term8 _104486 _104487 x s y t).
Proof. exact (@lem4360307 _104486 _104487 x s y t). Qed.
Lemma lem4360309 {_104486 _104487 : Type'} (p1 : _104486) (s : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term7 _104486 _104487 p1 p2 s u) = (term8 _104486 _104487 p1 s p2 u).
Proof. exact (@lem4360308 _104486 _104487 p1 s p2 u). Qed.
Lemma lem4360312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4360313 {_104486 _104487 : Type'} (p1 : _104486) (s : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term56 _104486 _104487 p1 p2 s u) = (term57 _104486 _104487 p1 s p2 u).
Proof. exact (MK_COMB (@lem4360312) (@lem4360309 _104486 _104487 p1 s p2 u)). Qed.
Lemma lem4360315 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4360033 _103718 _103721 x s y t) (@lem4360032 _103718 _103721 x s y t)). Qed.
Lemma lem4360316 {_104486 _104487 : Type'} (x : _104486) (s : _104486 -> Prop) (y : _104487) (t : _104487 -> Prop) : (term7 _104486 _104487 x y s t) = (term8 _104486 _104487 x s y t).
Proof. exact (@lem4360315 _104486 _104487 x s y t). Qed.
Lemma lem4360317 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term7 _104486 _104487 p1 p2 t u) = (term8 _104486 _104487 p1 t p2 u).
Proof. exact (@lem4360316 _104486 _104487 p1 t p2 u). Qed.
Lemma lem4360320 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term105 _104486 _104487 s p1 p2 t u) = (term106 _104486 _104487 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4360313 _104486 _104487 p1 s p2 u) (@lem4360317 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360323 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term91 _104486 _104487 p1 p2 s t u) = (term106 _104486 _104487 s p1 t p2 u).
Proof. exact (TRANS (@lem4360303 _104486 _104487 s p1 p2 t u) (@lem4360320 _104486 _104487 s p1 t p2 u)). Qed.
Lemma lem4360324 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term90 _104486 _104487 p1 p2 s t u) = (term91 _104486 _104487 p1 p2 s t u)) = ((term102 _104486 _104487 s p1 t p2 u) = (term106 _104486 _104487 s p1 t p2 u)).
Proof. exact (MK_COMB (@lem4360299 _104486 _104487 s p1 t p2 u) (@lem4360323 _104486 _104487 s p1 t p2 u)). Qed.
Lemma lem4360329 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term93 _104486 _104487 p1 s t u) = (term107 _104486 _104487 s p1 t u).
Proof. exact (fun_ext (fun p2 : _104487 => @lem4360324 _104486 _104487 s p1 t p2 u)). Qed.
Lemma lem4360330 {_104487 : Type'} : (@all _104487) = (@all _104487).
Proof. exact (eq_refl (@all _104487)). Qed.
Lemma lem4360331 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term95 _104486 _104487 p1 s t u) = (term108 _104486 _104487 s p1 t u).
Proof. exact (MK_COMB (@lem4360330 _104487) (@lem4360329 _104486 _104487 s p1 t u)). Qed.
Lemma lem4360338 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term97 _104486 _104487 s t u) = (term109 _104486 _104487 s t u).
Proof. exact (fun_ext (fun p1 : _104486 => @lem4360331 _104486 _104487 s p1 t u)). Qed.
Lemma lem4360339 {_104486 : Type'} : (@all _104486) = (@all _104486).
Proof. exact (eq_refl (@all _104486)). Qed.
Lemma lem4360340 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : (term98 _104486 _104487 s t u) = (term110 _104486 _104487 s t u).
Proof. exact (MK_COMB (@lem4360339 _104486) (@lem4360338 _104486 _104487 s t u)). Qed.
Lemma lem4360347 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : ((term77 _104486 _104487 s t u) = (term78 _104486 _104487 s t u)) = (term110 _104486 _104487 s t u).
Proof. exact (TRANS (@lem4360268 _104486 _104487 s t u) (@lem4360340 _104486 _104487 s t u)). Qed.
Lemma lem4360348 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) : (term111 _104486 _104487 s t) = (term112 _104486 _104487 s t).
Proof. exact (fun_ext (fun u : _104487 -> Prop => @lem4360347 _104486 _104487 s t u)). Qed.
Lemma lem4360349 {_104487 : Type'} : (@all (_104487 -> Prop)) = (@all (_104487 -> Prop)).
Proof. exact (eq_refl (@all (_104487 -> Prop))). Qed.
Lemma lem4360350 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) : (term113 _104486 _104487 s t) = (term114 _104486 _104487 s t).
Proof. exact (MK_COMB (@lem4360349 _104487) (@lem4360348 _104486 _104487 s t)). Qed.
Lemma lem4360357 {_104486 _104487 : Type'} (s : _104486 -> Prop) : (term115 _104486 _104487 s) = (term116 _104486 _104487 s).
Proof. exact (fun_ext (fun t : _104486 -> Prop => @lem4360350 _104486 _104487 s t)). Qed.
Lemma lem4360358 {_104486 : Type'} : (@all (_104486 -> Prop)) = (@all (_104486 -> Prop)).
Proof. exact (eq_refl (@all (_104486 -> Prop))). Qed.
Lemma lem4360359 {_104486 _104487 : Type'} (s : _104486 -> Prop) : (term117 _104486 _104487 s) = (term118 _104486 _104487 s).
Proof. exact (MK_COMB (@lem4360358 _104486) (@lem4360357 _104486 _104487 s)). Qed.
Lemma lem4360366 {_104486 _104487 : Type'} : (term119 _104486 _104487) = (term120 _104486 _104487).
Proof. exact (fun_ext (fun s : _104486 -> Prop => @lem4360359 _104486 _104487 s)). Qed.
Lemma lem4360367 {_104486 : Type'} : (@all (_104486 -> Prop)) = (@all (_104486 -> Prop)).
Proof. exact (eq_refl (@all (_104486 -> Prop))). Qed.
Lemma lem4360368 {_104486 _104487 : Type'} : (term121 _104486 _104487) = (term122 _104486 _104487).
Proof. exact (MK_COMB (@lem4360367 _104486) (@lem4360366 _104486 _104487)). Qed.
Lemma lem4360375 {_104453 _104454 _104486 _104487 : Type'} : (term123 _104453 _104454 _104486 _104487) = (term124 _104453 _104454 _104486 _104487).
Proof. exact (MK_COMB (@lem4360214 _104453 _104454) (@lem4360368 _104486 _104487)). Qed.
Lemma lem4360378 {_104453 _104454 _104486 _104487 : Type'} : (term124 _104453 _104454 _104486 _104487) = (term123 _104453 _104454 _104486 _104487).
Proof. exact (SYM (@lem4360375 _104453 _104454 _104486 _104487)). Qed.
Lemma lem4360393 {_104453 : Type'} (p1 : _104453) (s : _104453 -> Prop) : term125 _104453 p1 s.
Proof. exact (@lem9851 (@IN _104453 p1 s)). Qed.
Lemma lem4360394 {_104453 : Type'} (p1 : _104453) (s : _104453 -> Prop) : (term125 _104453 p1 s) = (term126 _104453 p1 s).
Proof. exact (eq_refl (term125 _104453 p1 s)). Qed.
Lemma lem4360395 {_104453 : Type'} (p1 : _104453) (s : _104453 -> Prop) : term126 _104453 p1 s.
Proof. exact (EQ_MP (@lem4360394 _104453 p1 s) (@lem4360393 _104453 p1 s)). Qed.
Lemma lem4360396 {_104453 : Type'} (p1 : _104453) (s : _104453 -> Prop) (h1 : (@IN _104453 p1 s) = True) : (@IN _104453 p1 s) = True.
Proof. exact (h1). Qed.
Lemma lem4360397 {_104453 : Type'} (p1 : _104453) (s : _104453 -> Prop) (h1 : (@IN _104453 p1 s) = False) : (@IN _104453 p1 s) = False.
Proof. exact (h1). Qed.
Lemma lem4360412 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term127 _104454 t p2 u) = (term127 _104454 t p2 u).
Proof. exact (eq_refl (term127 _104454 t p2 u)). Qed.
Lemma lem4360413 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (h1 : (@IN _104453 p1 s) = True) : (term128 _104453 _104454 t p2 u p1 s) = (term129 _104454 t p2 u).
Proof. exact (MK_COMB (@lem4360412 _104454 t p2 u) (@lem4360396 _104453 p1 s h1)). Qed.
Lemma lem4360414 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term129 _104454 t p2 u) = ((term130 _104454 t p2 u) = (term131 _104454 t p2 u)).
Proof. exact (eq_refl (term129 _104454 t p2 u)). Qed.
Lemma lem4360415 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) : (term132 _104453 _104454 t p2 u p1 s) = (term132 _104453 _104454 t p2 u p1 s).
Proof. exact (eq_refl (term132 _104453 _104454 t p2 u p1 s)). Qed.
Lemma lem4360416 {_104453 _104454 : Type'} (p1 : _104453) (s : _104453 -> Prop) (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : ((term128 _104453 _104454 t p2 u p1 s) = (term129 _104454 t p2 u)) = ((term128 _104453 _104454 t p2 u p1 s) = ((term130 _104454 t p2 u) = (term131 _104454 t p2 u))).
Proof. exact (MK_COMB (@lem4360415 _104453 _104454 t p2 u p1 s) (@lem4360414 _104454 t p2 u)). Qed.
Lemma lem4360417 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term128 _104453 _104454 t p2 u p1 s) = ((term50 _104453 _104454 p1 s t p2 u) = (term58 _104453 _104454 t p1 s p2 u)).
Proof. exact (eq_refl (term128 _104453 _104454 t p2 u p1 s)). Qed.
Lemma lem4360418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360419 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term132 _104453 _104454 t p2 u p1 s) = (term133 _104453 _104454 t p1 s p2 u).
Proof. exact (MK_COMB (@lem4360418) (@lem4360417 _104453 _104454 t p1 s p2 u)). Qed.
Lemma lem4360420 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : ((term130 _104454 t p2 u) = (term131 _104454 t p2 u)) = ((term130 _104454 t p2 u) = (term131 _104454 t p2 u)).
Proof. exact (eq_refl ((term130 _104454 t p2 u) = (term131 _104454 t p2 u))). Qed.
Lemma lem4360421 {_104453 _104454 : Type'} (p1 : _104453) (s : _104453 -> Prop) (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : ((term128 _104453 _104454 t p2 u p1 s) = ((term130 _104454 t p2 u) = (term131 _104454 t p2 u))) = (((term50 _104453 _104454 p1 s t p2 u) = (term58 _104453 _104454 t p1 s p2 u)) = ((term130 _104454 t p2 u) = (term131 _104454 t p2 u))).
Proof. exact (MK_COMB (@lem4360419 _104453 _104454 t p1 s p2 u) (@lem4360420 _104454 t p2 u)). Qed.
Lemma lem4360422 {_104453 _104454 : Type'} (p1 : _104453) (s : _104453 -> Prop) (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : ((term128 _104453 _104454 t p2 u p1 s) = (term129 _104454 t p2 u)) = (((term50 _104453 _104454 p1 s t p2 u) = (term58 _104453 _104454 t p1 s p2 u)) = ((term130 _104454 t p2 u) = (term131 _104454 t p2 u))).
Proof. exact (TRANS (@lem4360416 _104453 _104454 p1 s t p2 u) (@lem4360421 _104453 _104454 p1 s t p2 u)). Qed.
Lemma lem4360423 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (h1 : (@IN _104453 p1 s) = True) : ((term50 _104453 _104454 p1 s t p2 u) = (term58 _104453 _104454 t p1 s p2 u)) = ((term130 _104454 t p2 u) = (term131 _104454 t p2 u)).
Proof. exact (EQ_MP (@lem4360422 _104453 _104454 p1 s t p2 u) (@lem4360413 _104453 _104454 t p2 u p1 s h1)). Qed.
Lemma lem4360424 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (h1 : (@IN _104453 p1 s) = True) : ((term130 _104454 t p2 u) = (term131 _104454 t p2 u)) = ((term50 _104453 _104454 p1 s t p2 u) = (term58 _104453 _104454 t p1 s p2 u)).
Proof. exact (SYM (@lem4360423 _104453 _104454 t p2 u p1 s h1)). Qed.
Lemma lem4360425 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term127 _104454 t p2 u) = (term127 _104454 t p2 u).
Proof. exact (eq_refl (term127 _104454 t p2 u)). Qed.
Lemma lem4360426 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (h1 : (@IN _104453 p1 s) = False) : (term128 _104453 _104454 t p2 u p1 s) = (term134 _104454 t p2 u).
Proof. exact (MK_COMB (@lem4360425 _104454 t p2 u) (@lem4360397 _104453 p1 s h1)). Qed.
Lemma lem4360427 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term134 _104454 t p2 u) = ((term135 _104454 t p2 u) = (term136 _104454 t p2 u)).
Proof. exact (eq_refl (term134 _104454 t p2 u)). Qed.
Lemma lem4360428 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) : (term132 _104453 _104454 t p2 u p1 s) = (term132 _104453 _104454 t p2 u p1 s).
Proof. exact (eq_refl (term132 _104453 _104454 t p2 u p1 s)). Qed.
Lemma lem4360429 {_104453 _104454 : Type'} (p1 : _104453) (s : _104453 -> Prop) (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : ((term128 _104453 _104454 t p2 u p1 s) = (term134 _104454 t p2 u)) = ((term128 _104453 _104454 t p2 u p1 s) = ((term135 _104454 t p2 u) = (term136 _104454 t p2 u))).
Proof. exact (MK_COMB (@lem4360428 _104453 _104454 t p2 u p1 s) (@lem4360427 _104454 t p2 u)). Qed.
Lemma lem4360430 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term128 _104453 _104454 t p2 u p1 s) = ((term50 _104453 _104454 p1 s t p2 u) = (term58 _104453 _104454 t p1 s p2 u)).
Proof. exact (eq_refl (term128 _104453 _104454 t p2 u p1 s)). Qed.
Lemma lem4360431 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360432 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term132 _104453 _104454 t p2 u p1 s) = (term133 _104453 _104454 t p1 s p2 u).
Proof. exact (MK_COMB (@lem4360431) (@lem4360430 _104453 _104454 t p1 s p2 u)). Qed.
Lemma lem4360433 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : ((term135 _104454 t p2 u) = (term136 _104454 t p2 u)) = ((term135 _104454 t p2 u) = (term136 _104454 t p2 u)).
Proof. exact (eq_refl ((term135 _104454 t p2 u) = (term136 _104454 t p2 u))). Qed.
Lemma lem4360434 {_104453 _104454 : Type'} (p1 : _104453) (s : _104453 -> Prop) (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : ((term128 _104453 _104454 t p2 u p1 s) = ((term135 _104454 t p2 u) = (term136 _104454 t p2 u))) = (((term50 _104453 _104454 p1 s t p2 u) = (term58 _104453 _104454 t p1 s p2 u)) = ((term135 _104454 t p2 u) = (term136 _104454 t p2 u))).
Proof. exact (MK_COMB (@lem4360432 _104453 _104454 t p1 s p2 u) (@lem4360433 _104454 t p2 u)). Qed.
Lemma lem4360435 {_104453 _104454 : Type'} (p1 : _104453) (s : _104453 -> Prop) (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : ((term128 _104453 _104454 t p2 u p1 s) = (term134 _104454 t p2 u)) = (((term50 _104453 _104454 p1 s t p2 u) = (term58 _104453 _104454 t p1 s p2 u)) = ((term135 _104454 t p2 u) = (term136 _104454 t p2 u))).
Proof. exact (TRANS (@lem4360429 _104453 _104454 p1 s t p2 u) (@lem4360434 _104453 _104454 p1 s t p2 u)). Qed.
Lemma lem4360436 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (h1 : (@IN _104453 p1 s) = False) : ((term50 _104453 _104454 p1 s t p2 u) = (term58 _104453 _104454 t p1 s p2 u)) = ((term135 _104454 t p2 u) = (term136 _104454 t p2 u)).
Proof. exact (EQ_MP (@lem4360435 _104453 _104454 p1 s t p2 u) (@lem4360426 _104453 _104454 t p2 u p1 s h1)). Qed.
Lemma lem4360437 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (h1 : (@IN _104453 p1 s) = False) : ((term135 _104454 t p2 u) = (term136 _104454 t p2 u)) = ((term50 _104453 _104454 p1 s t p2 u) = (term58 _104453 _104454 t p1 s p2 u)).
Proof. exact (SYM (@lem4360436 _104453 _104454 t p2 u p1 s h1)). Qed.
Lemma lem4360441 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4360442 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term130 _104454 t p2 u) = (term15 _104454 t p2 u).
Proof. exact (@lem4360441 (term15 _104454 t p2 u)). Qed.
Lemma lem4360445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360446 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term137 _104454 t p2 u) = (term138 _104454 t p2 u).
Proof. exact (MK_COMB (@lem4360445) (@lem4360442 _104454 t p2 u)). Qed.
Lemma lem4360450 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4360451 {_104454 : Type'} (p2 : _104454) (t : _104454 -> Prop) : (term139 _104454 p2 t) = (@IN _104454 p2 t).
Proof. exact (@lem4360450 (@IN _104454 p2 t)). Qed.
Lemma lem4360452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4360453 {_104454 : Type'} (p2 : _104454) (t : _104454 -> Prop) : (term140 _104454 p2 t) = (term49 _104454 p2 t).
Proof. exact (MK_COMB (@lem4360452) (@lem4360451 _104454 p2 t)). Qed.
Lemma lem4360455 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4360456 {_104454 : Type'} (p2 : _104454) (u : _104454 -> Prop) : (term139 _104454 p2 u) = (@IN _104454 p2 u).
Proof. exact (@lem4360455 (@IN _104454 p2 u)). Qed.
Lemma lem4360457 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term131 _104454 t p2 u) = (term15 _104454 t p2 u).
Proof. exact (MK_COMB (@lem4360453 _104454 p2 t) (@lem4360456 _104454 p2 u)). Qed.
Lemma lem4360460 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : ((term130 _104454 t p2 u) = (term131 _104454 t p2 u)) = ((term15 _104454 t p2 u) = (term15 _104454 t p2 u)).
Proof. exact (MK_COMB (@lem4360446 _104454 t p2 u) (@lem4360457 _104454 t p2 u)). Qed.
Lemma lem4360462 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4360463 (x : Prop) : (x = x) = True.
Proof. exact (@lem4360462 Prop x). Qed.
Lemma lem4360464 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : ((term15 _104454 t p2 u) = (term15 _104454 t p2 u)) = True.
Proof. exact (@lem4360463 (term15 _104454 t p2 u)). Qed.
Lemma lem4360465 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : ((term130 _104454 t p2 u) = (term131 _104454 t p2 u)) = True.
Proof. exact (TRANS (@lem4360460 _104454 t p2 u) (@lem4360464 _104454 t p2 u)). Qed.
Lemma lem4360466 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : True = ((term130 _104454 t p2 u) = (term131 _104454 t p2 u)).
Proof. exact (SYM (@lem4360465 _104454 t p2 u)). Qed.
Lemma lem4360467 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term130 _104454 t p2 u) = (term131 _104454 t p2 u).
Proof. exact (EQ_MP (@lem4360466 _104454 t p2 u) (@lem0)). Qed.
Lemma lem4360471 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4360472 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term135 _104454 t p2 u) = False.
Proof. exact (@lem4360471 (term15 _104454 t p2 u)). Qed.
Lemma lem4360473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360474 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term141 _104454 t p2 u) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4360473) (@lem4360472 _104454 t p2 u)). Qed.
Lemma lem4360478 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4360479 {_104454 : Type'} (p2 : _104454) (t : _104454 -> Prop) : (term142 _104454 p2 t) = False.
Proof. exact (@lem4360478 (@IN _104454 p2 t)). Qed.
Lemma lem4360480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4360481 {_104454 : Type'} (p2 : _104454) (t : _104454 -> Prop) : (term143 _104454 p2 t) = (and False).
Proof. exact (MK_COMB (@lem4360480) (@lem4360479 _104454 p2 t)). Qed.
Lemma lem4360483 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4360484 {_104454 : Type'} (p2 : _104454) (u : _104454 -> Prop) : (term142 _104454 p2 u) = False.
Proof. exact (@lem4360483 (@IN _104454 p2 u)). Qed.
Lemma lem4360485 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term136 _104454 t p2 u) = (False /\ False).
Proof. exact (MK_COMB (@lem4360481 _104454 p2 t) (@lem4360484 _104454 p2 u)). Qed.
Lemma lem4360487 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4360488 : (False /\ False) = False.
Proof. exact (@lem4360487 False). Qed.
Lemma lem4360489 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term136 _104454 t p2 u) = False.
Proof. exact (TRANS (@lem4360485 _104454 t p2 u) (@lem4360488)). Qed.
Lemma lem4360490 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : ((term135 _104454 t p2 u) = (term136 _104454 t p2 u)) = (False = False).
Proof. exact (MK_COMB (@lem4360474 _104454 t p2 u) (@lem4360489 _104454 t p2 u)). Qed.
Lemma lem4360492 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4360493 : (False = False) = (~ False).
Proof. exact (@lem4360492 False). Qed.
Lemma lem4360495 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4360496 : (False = False) = True.
Proof. exact (TRANS (@lem4360493) (@lem4360495)). Qed.
Lemma lem4360497 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : ((term135 _104454 t p2 u) = (term136 _104454 t p2 u)) = True.
Proof. exact (TRANS (@lem4360490 _104454 t p2 u) (@lem4360496)). Qed.
Lemma lem4360498 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : True = ((term135 _104454 t p2 u) = (term136 _104454 t p2 u)).
Proof. exact (SYM (@lem4360497 _104454 t p2 u)). Qed.
Lemma lem4360499 {_104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term135 _104454 t p2 u) = (term136 _104454 t p2 u).
Proof. exact (EQ_MP (@lem4360498 _104454 t p2 u) (@lem0)). Qed.
Lemma lem4360500 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (h1 : (@IN _104453 p1 s) = False) : (term50 _104453 _104454 p1 s t p2 u) = (term58 _104453 _104454 t p1 s p2 u).
Proof. exact (EQ_MP (@lem4360437 _104453 _104454 t p2 u p1 s h1) (@lem4360499 _104454 t p2 u)). Qed.
Lemma lem4360501 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p2 : _104454) (u : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (h1 : (@IN _104453 p1 s) = True) : (term50 _104453 _104454 p1 s t p2 u) = (term58 _104453 _104454 t p1 s p2 u).
Proof. exact (EQ_MP (@lem4360424 _104453 _104454 t p2 u p1 s h1) (@lem4360467 _104454 t p2 u)). Qed.
Lemma lem4360504 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (p2 : _104454) (u : _104454 -> Prop) : (term50 _104453 _104454 p1 s t p2 u) = (term58 _104453 _104454 t p1 s p2 u).
Proof. exact (or_elim (@lem4360395 _104453 p1 s) (fun h0 : (@IN _104453 p1 s) = True => @lem4360501 _104453 _104454 t p2 u p1 s h0) (fun h0 : (@IN _104453 p1 s) = False => @lem4360500 _104453 _104454 t p2 u p1 s h0)). Qed.
Lemma lem4360519 {_104486 : Type'} (p1 : _104486) (s : _104486 -> Prop) : term125 _104486 p1 s.
Proof. exact (@lem9851 (@IN _104486 p1 s)). Qed.
Lemma lem4360520 {_104486 : Type'} (p1 : _104486) (s : _104486 -> Prop) : (term125 _104486 p1 s) = (term126 _104486 p1 s).
Proof. exact (eq_refl (term125 _104486 p1 s)). Qed.
Lemma lem4360521 {_104486 : Type'} (p1 : _104486) (s : _104486 -> Prop) : term126 _104486 p1 s.
Proof. exact (EQ_MP (@lem4360520 _104486 p1 s) (@lem4360519 _104486 p1 s)). Qed.
Lemma lem4360522 {_104486 : Type'} (p1 : _104486) (s : _104486 -> Prop) (h1 : (@IN _104486 p1 s) = True) : (@IN _104486 p1 s) = True.
Proof. exact (h1). Qed.
Lemma lem4360523 {_104486 : Type'} (p1 : _104486) (s : _104486 -> Prop) (h1 : (@IN _104486 p1 s) = False) : (@IN _104486 p1 s) = False.
Proof. exact (h1). Qed.
Lemma lem4360538 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term144 _104486 _104487 p1 t p2 u) = (term144 _104486 _104487 p1 t p2 u).
Proof. exact (eq_refl (term144 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360539 {_104486 _104487 : Type'} (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (s : _104486 -> Prop) (h1 : (@IN _104486 p1 s) = True) : (term145 _104486 _104487 t p2 u p1 s) = (term146 _104486 _104487 p1 t p2 u).
Proof. exact (MK_COMB (@lem4360538 _104486 _104487 p1 t p2 u) (@lem4360522 _104486 p1 s h1)). Qed.
Lemma lem4360540 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term146 _104486 _104487 p1 t p2 u) = ((term147 _104486 _104487 p1 t p2 u) = (term148 _104486 _104487 p1 t p2 u)).
Proof. exact (eq_refl (term146 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360541 {_104486 _104487 : Type'} (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (s : _104486 -> Prop) : (term149 _104486 _104487 t p2 u p1 s) = (term149 _104486 _104487 t p2 u p1 s).
Proof. exact (eq_refl (term149 _104486 _104487 t p2 u p1 s)). Qed.
Lemma lem4360542 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term145 _104486 _104487 t p2 u p1 s) = (term146 _104486 _104487 p1 t p2 u)) = ((term145 _104486 _104487 t p2 u p1 s) = ((term147 _104486 _104487 p1 t p2 u) = (term148 _104486 _104487 p1 t p2 u))).
Proof. exact (MK_COMB (@lem4360541 _104486 _104487 t p2 u p1 s) (@lem4360540 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360543 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term145 _104486 _104487 t p2 u p1 s) = ((term102 _104486 _104487 s p1 t p2 u) = (term106 _104486 _104487 s p1 t p2 u)).
Proof. exact (eq_refl (term145 _104486 _104487 t p2 u p1 s)). Qed.
Lemma lem4360544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360545 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term149 _104486 _104487 t p2 u p1 s) = (term150 _104486 _104487 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4360544) (@lem4360543 _104486 _104487 s p1 t p2 u)). Qed.
Lemma lem4360546 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term147 _104486 _104487 p1 t p2 u) = (term148 _104486 _104487 p1 t p2 u)) = ((term147 _104486 _104487 p1 t p2 u) = (term148 _104486 _104487 p1 t p2 u)).
Proof. exact (eq_refl ((term147 _104486 _104487 p1 t p2 u) = (term148 _104486 _104487 p1 t p2 u))). Qed.
Lemma lem4360547 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term145 _104486 _104487 t p2 u p1 s) = ((term147 _104486 _104487 p1 t p2 u) = (term148 _104486 _104487 p1 t p2 u))) = (((term102 _104486 _104487 s p1 t p2 u) = (term106 _104486 _104487 s p1 t p2 u)) = ((term147 _104486 _104487 p1 t p2 u) = (term148 _104486 _104487 p1 t p2 u))).
Proof. exact (MK_COMB (@lem4360545 _104486 _104487 s p1 t p2 u) (@lem4360546 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360548 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term145 _104486 _104487 t p2 u p1 s) = (term146 _104486 _104487 p1 t p2 u)) = (((term102 _104486 _104487 s p1 t p2 u) = (term106 _104486 _104487 s p1 t p2 u)) = ((term147 _104486 _104487 p1 t p2 u) = (term148 _104486 _104487 p1 t p2 u))).
Proof. exact (TRANS (@lem4360542 _104486 _104487 s p1 t p2 u) (@lem4360547 _104486 _104487 s p1 t p2 u)). Qed.
Lemma lem4360549 {_104486 _104487 : Type'} (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (s : _104486 -> Prop) (h1 : (@IN _104486 p1 s) = True) : ((term102 _104486 _104487 s p1 t p2 u) = (term106 _104486 _104487 s p1 t p2 u)) = ((term147 _104486 _104487 p1 t p2 u) = (term148 _104486 _104487 p1 t p2 u)).
Proof. exact (EQ_MP (@lem4360548 _104486 _104487 s p1 t p2 u) (@lem4360539 _104486 _104487 t p2 u p1 s h1)). Qed.
Lemma lem4360550 {_104486 _104487 : Type'} (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (s : _104486 -> Prop) (h1 : (@IN _104486 p1 s) = True) : ((term147 _104486 _104487 p1 t p2 u) = (term148 _104486 _104487 p1 t p2 u)) = ((term102 _104486 _104487 s p1 t p2 u) = (term106 _104486 _104487 s p1 t p2 u)).
Proof. exact (SYM (@lem4360549 _104486 _104487 t p2 u p1 s h1)). Qed.
Lemma lem4360551 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term144 _104486 _104487 p1 t p2 u) = (term144 _104486 _104487 p1 t p2 u).
Proof. exact (eq_refl (term144 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360552 {_104486 _104487 : Type'} (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (s : _104486 -> Prop) (h1 : (@IN _104486 p1 s) = False) : (term145 _104486 _104487 t p2 u p1 s) = (term151 _104486 _104487 p1 t p2 u).
Proof. exact (MK_COMB (@lem4360551 _104486 _104487 p1 t p2 u) (@lem4360523 _104486 p1 s h1)). Qed.
Lemma lem4360553 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term151 _104486 _104487 p1 t p2 u) = ((term152 _104486 _104487 p1 t p2 u) = (term153 _104486 _104487 p1 t p2 u)).
Proof. exact (eq_refl (term151 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360554 {_104486 _104487 : Type'} (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (s : _104486 -> Prop) : (term149 _104486 _104487 t p2 u p1 s) = (term149 _104486 _104487 t p2 u p1 s).
Proof. exact (eq_refl (term149 _104486 _104487 t p2 u p1 s)). Qed.
Lemma lem4360555 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term145 _104486 _104487 t p2 u p1 s) = (term151 _104486 _104487 p1 t p2 u)) = ((term145 _104486 _104487 t p2 u p1 s) = ((term152 _104486 _104487 p1 t p2 u) = (term153 _104486 _104487 p1 t p2 u))).
Proof. exact (MK_COMB (@lem4360554 _104486 _104487 t p2 u p1 s) (@lem4360553 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360556 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term145 _104486 _104487 t p2 u p1 s) = ((term102 _104486 _104487 s p1 t p2 u) = (term106 _104486 _104487 s p1 t p2 u)).
Proof. exact (eq_refl (term145 _104486 _104487 t p2 u p1 s)). Qed.
Lemma lem4360557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360558 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term149 _104486 _104487 t p2 u p1 s) = (term150 _104486 _104487 s p1 t p2 u).
Proof. exact (MK_COMB (@lem4360557) (@lem4360556 _104486 _104487 s p1 t p2 u)). Qed.
Lemma lem4360559 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term152 _104486 _104487 p1 t p2 u) = (term153 _104486 _104487 p1 t p2 u)) = ((term152 _104486 _104487 p1 t p2 u) = (term153 _104486 _104487 p1 t p2 u)).
Proof. exact (eq_refl ((term152 _104486 _104487 p1 t p2 u) = (term153 _104486 _104487 p1 t p2 u))). Qed.
Lemma lem4360560 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term145 _104486 _104487 t p2 u p1 s) = ((term152 _104486 _104487 p1 t p2 u) = (term153 _104486 _104487 p1 t p2 u))) = (((term102 _104486 _104487 s p1 t p2 u) = (term106 _104486 _104487 s p1 t p2 u)) = ((term152 _104486 _104487 p1 t p2 u) = (term153 _104486 _104487 p1 t p2 u))).
Proof. exact (MK_COMB (@lem4360558 _104486 _104487 s p1 t p2 u) (@lem4360559 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360561 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term145 _104486 _104487 t p2 u p1 s) = (term151 _104486 _104487 p1 t p2 u)) = (((term102 _104486 _104487 s p1 t p2 u) = (term106 _104486 _104487 s p1 t p2 u)) = ((term152 _104486 _104487 p1 t p2 u) = (term153 _104486 _104487 p1 t p2 u))).
Proof. exact (TRANS (@lem4360555 _104486 _104487 s p1 t p2 u) (@lem4360560 _104486 _104487 s p1 t p2 u)). Qed.
Lemma lem4360562 {_104486 _104487 : Type'} (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (s : _104486 -> Prop) (h1 : (@IN _104486 p1 s) = False) : ((term102 _104486 _104487 s p1 t p2 u) = (term106 _104486 _104487 s p1 t p2 u)) = ((term152 _104486 _104487 p1 t p2 u) = (term153 _104486 _104487 p1 t p2 u)).
Proof. exact (EQ_MP (@lem4360561 _104486 _104487 s p1 t p2 u) (@lem4360552 _104486 _104487 t p2 u p1 s h1)). Qed.
Lemma lem4360563 {_104486 _104487 : Type'} (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (s : _104486 -> Prop) (h1 : (@IN _104486 p1 s) = False) : ((term152 _104486 _104487 p1 t p2 u) = (term153 _104486 _104487 p1 t p2 u)) = ((term102 _104486 _104487 s p1 t p2 u) = (term106 _104486 _104487 s p1 t p2 u)).
Proof. exact (SYM (@lem4360562 _104486 _104487 t p2 u p1 s h1)). Qed.
Lemma lem4360569 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4360570 {_104486 : Type'} (p1 : _104486) (t : _104486 -> Prop) : (term139 _104486 p1 t) = (@IN _104486 p1 t).
Proof. exact (@lem4360569 (@IN _104486 p1 t)). Qed.
Lemma lem4360571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4360572 {_104486 : Type'} (p1 : _104486) (t : _104486 -> Prop) : (term140 _104486 p1 t) = (term49 _104486 p1 t).
Proof. exact (MK_COMB (@lem4360571) (@lem4360570 _104486 p1 t)). Qed.
Lemma lem4360573 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (@IN _104487 p2 u) = (@IN _104487 p2 u).
Proof. exact (eq_refl (@IN _104487 p2 u)). Qed.
Lemma lem4360574 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term147 _104486 _104487 p1 t p2 u) = (term8 _104486 _104487 p1 t p2 u).
Proof. exact (MK_COMB (@lem4360572 _104486 p1 t) (@lem4360573 _104487 p2 u)). Qed.
Lemma lem4360577 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360578 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term154 _104486 _104487 p1 t p2 u) = (term155 _104486 _104487 p1 t p2 u).
Proof. exact (MK_COMB (@lem4360577) (@lem4360574 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360582 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4360583 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term139 _104487 p2 u) = (@IN _104487 p2 u).
Proof. exact (@lem4360582 (@IN _104487 p2 u)). Qed.
Lemma lem4360584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4360585 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term140 _104487 p2 u) = (term49 _104487 p2 u).
Proof. exact (MK_COMB (@lem4360584) (@lem4360583 _104487 p2 u)). Qed.
Lemma lem4360588 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term8 _104486 _104487 p1 t p2 u) = (term8 _104486 _104487 p1 t p2 u).
Proof. exact (eq_refl (term8 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360589 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term148 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u).
Proof. exact (MK_COMB (@lem4360585 _104487 p2 u) (@lem4360588 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360592 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term147 _104486 _104487 p1 t p2 u) = (term148 _104486 _104487 p1 t p2 u)) = ((term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u)).
Proof. exact (MK_COMB (@lem4360578 _104486 _104487 p1 t p2 u) (@lem4360589 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360595 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u)) = ((term147 _104486 _104487 p1 t p2 u) = (term148 _104486 _104487 p1 t p2 u)).
Proof. exact (SYM (@lem4360592 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360596 {_104486 : Type'} (p1 : _104486) (t : _104486 -> Prop) : term125 _104486 p1 t.
Proof. exact (@lem9851 (@IN _104486 p1 t)). Qed.
Lemma lem4360597 {_104486 : Type'} (p1 : _104486) (t : _104486 -> Prop) : (term125 _104486 p1 t) = (term126 _104486 p1 t).
Proof. exact (eq_refl (term125 _104486 p1 t)). Qed.
Lemma lem4360598 {_104486 : Type'} (p1 : _104486) (t : _104486 -> Prop) : term126 _104486 p1 t.
Proof. exact (EQ_MP (@lem4360597 _104486 p1 t) (@lem4360596 _104486 p1 t)). Qed.
Lemma lem4360599 {_104486 : Type'} (p1 : _104486) (t : _104486 -> Prop) (h1 : (@IN _104486 p1 t) = True) : (@IN _104486 p1 t) = True.
Proof. exact (h1). Qed.
Lemma lem4360600 {_104486 : Type'} (p1 : _104486) (t : _104486 -> Prop) (h1 : (@IN _104486 p1 t) = False) : (@IN _104486 p1 t) = False.
Proof. exact (h1). Qed.
Lemma lem4360611 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term157 _104487 p2 u) = (term157 _104487 p2 u).
Proof. exact (eq_refl (term157 _104487 p2 u)). Qed.
Lemma lem4360612 {_104486 _104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (h1 : (@IN _104486 p1 t) = True) : (term158 _104486 _104487 p2 u p1 t) = (term159 _104487 p2 u).
Proof. exact (MK_COMB (@lem4360611 _104487 p2 u) (@lem4360599 _104486 p1 t h1)). Qed.
Lemma lem4360613 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term159 _104487 p2 u) = ((term139 _104487 p2 u) = (term160 _104487 p2 u)).
Proof. exact (eq_refl (term159 _104487 p2 u)). Qed.
Lemma lem4360614 {_104486 _104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (t : _104486 -> Prop) : (term161 _104486 _104487 p2 u p1 t) = (term161 _104486 _104487 p2 u p1 t).
Proof. exact (eq_refl (term161 _104486 _104487 p2 u p1 t)). Qed.
Lemma lem4360615 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term158 _104486 _104487 p2 u p1 t) = (term159 _104487 p2 u)) = ((term158 _104486 _104487 p2 u p1 t) = ((term139 _104487 p2 u) = (term160 _104487 p2 u))).
Proof. exact (MK_COMB (@lem4360614 _104486 _104487 p2 u p1 t) (@lem4360613 _104487 p2 u)). Qed.
Lemma lem4360616 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term158 _104486 _104487 p2 u p1 t) = ((term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u)).
Proof. exact (eq_refl (term158 _104486 _104487 p2 u p1 t)). Qed.
Lemma lem4360617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360618 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term161 _104486 _104487 p2 u p1 t) = (term162 _104486 _104487 p1 t p2 u).
Proof. exact (MK_COMB (@lem4360617) (@lem4360616 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360619 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : ((term139 _104487 p2 u) = (term160 _104487 p2 u)) = ((term139 _104487 p2 u) = (term160 _104487 p2 u)).
Proof. exact (eq_refl ((term139 _104487 p2 u) = (term160 _104487 p2 u))). Qed.
Lemma lem4360620 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term158 _104486 _104487 p2 u p1 t) = ((term139 _104487 p2 u) = (term160 _104487 p2 u))) = (((term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u)) = ((term139 _104487 p2 u) = (term160 _104487 p2 u))).
Proof. exact (MK_COMB (@lem4360618 _104486 _104487 p1 t p2 u) (@lem4360619 _104487 p2 u)). Qed.
Lemma lem4360621 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term158 _104486 _104487 p2 u p1 t) = (term159 _104487 p2 u)) = (((term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u)) = ((term139 _104487 p2 u) = (term160 _104487 p2 u))).
Proof. exact (TRANS (@lem4360615 _104486 _104487 p1 t p2 u) (@lem4360620 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360622 {_104486 _104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (h1 : (@IN _104486 p1 t) = True) : ((term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u)) = ((term139 _104487 p2 u) = (term160 _104487 p2 u)).
Proof. exact (EQ_MP (@lem4360621 _104486 _104487 p1 t p2 u) (@lem4360612 _104486 _104487 p2 u p1 t h1)). Qed.
Lemma lem4360623 {_104486 _104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (h1 : (@IN _104486 p1 t) = True) : ((term139 _104487 p2 u) = (term160 _104487 p2 u)) = ((term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u)).
Proof. exact (SYM (@lem4360622 _104486 _104487 p2 u p1 t h1)). Qed.
Lemma lem4360624 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term157 _104487 p2 u) = (term157 _104487 p2 u).
Proof. exact (eq_refl (term157 _104487 p2 u)). Qed.
Lemma lem4360625 {_104486 _104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (h1 : (@IN _104486 p1 t) = False) : (term158 _104486 _104487 p2 u p1 t) = (term163 _104487 p2 u).
Proof. exact (MK_COMB (@lem4360624 _104487 p2 u) (@lem4360600 _104486 p1 t h1)). Qed.
Lemma lem4360626 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term163 _104487 p2 u) = ((term142 _104487 p2 u) = (term164 _104487 p2 u)).
Proof. exact (eq_refl (term163 _104487 p2 u)). Qed.
Lemma lem4360627 {_104486 _104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (t : _104486 -> Prop) : (term161 _104486 _104487 p2 u p1 t) = (term161 _104486 _104487 p2 u p1 t).
Proof. exact (eq_refl (term161 _104486 _104487 p2 u p1 t)). Qed.
Lemma lem4360628 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term158 _104486 _104487 p2 u p1 t) = (term163 _104487 p2 u)) = ((term158 _104486 _104487 p2 u p1 t) = ((term142 _104487 p2 u) = (term164 _104487 p2 u))).
Proof. exact (MK_COMB (@lem4360627 _104486 _104487 p2 u p1 t) (@lem4360626 _104487 p2 u)). Qed.
Lemma lem4360629 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term158 _104486 _104487 p2 u p1 t) = ((term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u)).
Proof. exact (eq_refl (term158 _104486 _104487 p2 u p1 t)). Qed.
Lemma lem4360630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360631 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term161 _104486 _104487 p2 u p1 t) = (term162 _104486 _104487 p1 t p2 u).
Proof. exact (MK_COMB (@lem4360630) (@lem4360629 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360632 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : ((term142 _104487 p2 u) = (term164 _104487 p2 u)) = ((term142 _104487 p2 u) = (term164 _104487 p2 u)).
Proof. exact (eq_refl ((term142 _104487 p2 u) = (term164 _104487 p2 u))). Qed.
Lemma lem4360633 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term158 _104486 _104487 p2 u p1 t) = ((term142 _104487 p2 u) = (term164 _104487 p2 u))) = (((term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u)) = ((term142 _104487 p2 u) = (term164 _104487 p2 u))).
Proof. exact (MK_COMB (@lem4360631 _104486 _104487 p1 t p2 u) (@lem4360632 _104487 p2 u)). Qed.
Lemma lem4360634 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term158 _104486 _104487 p2 u p1 t) = (term163 _104487 p2 u)) = (((term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u)) = ((term142 _104487 p2 u) = (term164 _104487 p2 u))).
Proof. exact (TRANS (@lem4360628 _104486 _104487 p1 t p2 u) (@lem4360633 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360635 {_104486 _104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (h1 : (@IN _104486 p1 t) = False) : ((term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u)) = ((term142 _104487 p2 u) = (term164 _104487 p2 u)).
Proof. exact (EQ_MP (@lem4360634 _104486 _104487 p1 t p2 u) (@lem4360625 _104486 _104487 p2 u p1 t h1)). Qed.
Lemma lem4360636 {_104486 _104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (h1 : (@IN _104486 p1 t) = False) : ((term142 _104487 p2 u) = (term164 _104487 p2 u)) = ((term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u)).
Proof. exact (SYM (@lem4360635 _104486 _104487 p2 u p1 t h1)). Qed.
Lemma lem4360640 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4360641 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term139 _104487 p2 u) = (@IN _104487 p2 u).
Proof. exact (@lem4360640 (@IN _104487 p2 u)). Qed.
Lemma lem4360642 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360643 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term165 _104487 p2 u) = (term166 _104487 p2 u).
Proof. exact (MK_COMB (@lem4360642) (@lem4360641 _104487 p2 u)). Qed.
Lemma lem4360647 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4360648 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term139 _104487 p2 u) = (@IN _104487 p2 u).
Proof. exact (@lem4360647 (@IN _104487 p2 u)). Qed.
Lemma lem4360649 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term49 _104487 p2 u) = (term49 _104487 p2 u).
Proof. exact (eq_refl (term49 _104487 p2 u)). Qed.
Lemma lem4360650 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term160 _104487 p2 u) = (term167 _104487 p2 u).
Proof. exact (MK_COMB (@lem4360649 _104487 p2 u) (@lem4360648 _104487 p2 u)). Qed.
Lemma lem4360652 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem4360653 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term167 _104487 p2 u) = (@IN _104487 p2 u).
Proof. exact (@lem4360652 (@IN _104487 p2 u)). Qed.
Lemma lem4360654 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term160 _104487 p2 u) = (@IN _104487 p2 u).
Proof. exact (TRANS (@lem4360650 _104487 p2 u) (@lem4360653 _104487 p2 u)). Qed.
Lemma lem4360655 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : ((term139 _104487 p2 u) = (term160 _104487 p2 u)) = ((@IN _104487 p2 u) = (@IN _104487 p2 u)).
Proof. exact (MK_COMB (@lem4360643 _104487 p2 u) (@lem4360654 _104487 p2 u)). Qed.
Lemma lem4360657 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4360658 (x : Prop) : (x = x) = True.
Proof. exact (@lem4360657 Prop x). Qed.
Lemma lem4360659 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : ((@IN _104487 p2 u) = (@IN _104487 p2 u)) = True.
Proof. exact (@lem4360658 (@IN _104487 p2 u)). Qed.
Lemma lem4360660 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : ((term139 _104487 p2 u) = (term160 _104487 p2 u)) = True.
Proof. exact (TRANS (@lem4360655 _104487 p2 u) (@lem4360659 _104487 p2 u)). Qed.
Lemma lem4360661 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : True = ((term139 _104487 p2 u) = (term160 _104487 p2 u)).
Proof. exact (SYM (@lem4360660 _104487 p2 u)). Qed.
Lemma lem4360662 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term139 _104487 p2 u) = (term160 _104487 p2 u).
Proof. exact (EQ_MP (@lem4360661 _104487 p2 u) (@lem0)). Qed.
Lemma lem4360666 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4360667 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term142 _104487 p2 u) = False.
Proof. exact (@lem4360666 (@IN _104487 p2 u)). Qed.
Lemma lem4360668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360669 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term168 _104487 p2 u) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4360668) (@lem4360667 _104487 p2 u)). Qed.
Lemma lem4360673 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4360674 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term142 _104487 p2 u) = False.
Proof. exact (@lem4360673 (@IN _104487 p2 u)). Qed.
Lemma lem4360675 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term49 _104487 p2 u) = (term49 _104487 p2 u).
Proof. exact (eq_refl (term49 _104487 p2 u)). Qed.
Lemma lem4360676 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term164 _104487 p2 u) = (term169 _104487 p2 u).
Proof. exact (MK_COMB (@lem4360675 _104487 p2 u) (@lem4360674 _104487 p2 u)). Qed.
Lemma lem4360678 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem4360679 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term169 _104487 p2 u) = False.
Proof. exact (@lem4360678 (@IN _104487 p2 u)). Qed.
Lemma lem4360680 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term164 _104487 p2 u) = False.
Proof. exact (TRANS (@lem4360676 _104487 p2 u) (@lem4360679 _104487 p2 u)). Qed.
Lemma lem4360681 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : ((term142 _104487 p2 u) = (term164 _104487 p2 u)) = (False = False).
Proof. exact (MK_COMB (@lem4360669 _104487 p2 u) (@lem4360680 _104487 p2 u)). Qed.
Lemma lem4360683 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4360684 : (False = False) = (~ False).
Proof. exact (@lem4360683 False). Qed.
Lemma lem4360686 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4360687 : (False = False) = True.
Proof. exact (TRANS (@lem4360684) (@lem4360686)). Qed.
Lemma lem4360688 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : ((term142 _104487 p2 u) = (term164 _104487 p2 u)) = True.
Proof. exact (TRANS (@lem4360681 _104487 p2 u) (@lem4360687)). Qed.
Lemma lem4360689 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : True = ((term142 _104487 p2 u) = (term164 _104487 p2 u)).
Proof. exact (SYM (@lem4360688 _104487 p2 u)). Qed.
Lemma lem4360690 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term142 _104487 p2 u) = (term164 _104487 p2 u).
Proof. exact (EQ_MP (@lem4360689 _104487 p2 u) (@lem0)). Qed.
Lemma lem4360691 {_104486 _104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (h1 : (@IN _104486 p1 t) = False) : (term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u).
Proof. exact (EQ_MP (@lem4360636 _104486 _104487 p2 u p1 t h1) (@lem4360690 _104487 p2 u)). Qed.
Lemma lem4360692 {_104486 _104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (h1 : (@IN _104486 p1 t) = True) : (term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u).
Proof. exact (EQ_MP (@lem4360623 _104486 _104487 p2 u p1 t h1) (@lem4360662 _104487 p2 u)). Qed.
Lemma lem4360694 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term8 _104486 _104487 p1 t p2 u) = (term156 _104486 _104487 p1 t p2 u).
Proof. exact (or_elim (@lem4360598 _104486 p1 t) (fun h0 : (@IN _104486 p1 t) = True => @lem4360692 _104486 _104487 p2 u p1 t h0) (fun h0 : (@IN _104486 p1 t) = False => @lem4360691 _104486 _104487 p2 u p1 t h0)). Qed.
Lemma lem4360695 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term147 _104486 _104487 p1 t p2 u) = (term148 _104486 _104487 p1 t p2 u).
Proof. exact (EQ_MP (@lem4360595 _104486 _104487 p1 t p2 u) (@lem4360694 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360701 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4360702 {_104486 : Type'} (p1 : _104486) (t : _104486 -> Prop) : (term142 _104486 p1 t) = False.
Proof. exact (@lem4360701 (@IN _104486 p1 t)). Qed.
Lemma lem4360703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4360704 {_104486 : Type'} (p1 : _104486) (t : _104486 -> Prop) : (term143 _104486 p1 t) = (and False).
Proof. exact (MK_COMB (@lem4360703) (@lem4360702 _104486 p1 t)). Qed.
Lemma lem4360705 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (@IN _104487 p2 u) = (@IN _104487 p2 u).
Proof. exact (eq_refl (@IN _104487 p2 u)). Qed.
Lemma lem4360706 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term152 _104486 _104487 p1 t p2 u) = (term142 _104487 p2 u).
Proof. exact (MK_COMB (@lem4360704 _104486 p1 t) (@lem4360705 _104487 p2 u)). Qed.
Lemma lem4360708 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4360709 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term142 _104487 p2 u) = False.
Proof. exact (@lem4360708 (@IN _104487 p2 u)). Qed.
Lemma lem4360710 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term152 _104486 _104487 p1 t p2 u) = False.
Proof. exact (TRANS (@lem4360706 _104486 _104487 p1 t p2 u) (@lem4360709 _104487 p2 u)). Qed.
Lemma lem4360711 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4360712 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term170 _104486 _104487 p1 t p2 u) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4360711) (@lem4360710 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360716 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4360717 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term142 _104487 p2 u) = False.
Proof. exact (@lem4360716 (@IN _104487 p2 u)). Qed.
Lemma lem4360718 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4360719 {_104487 : Type'} (p2 : _104487) (u : _104487 -> Prop) : (term143 _104487 p2 u) = (and False).
Proof. exact (MK_COMB (@lem4360718) (@lem4360717 _104487 p2 u)). Qed.
Lemma lem4360722 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term8 _104486 _104487 p1 t p2 u) = (term8 _104486 _104487 p1 t p2 u).
Proof. exact (eq_refl (term8 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360723 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term153 _104486 _104487 p1 t p2 u) = (term171 _104486 _104487 p1 t p2 u).
Proof. exact (MK_COMB (@lem4360719 _104487 p2 u) (@lem4360722 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360725 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4360726 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term171 _104486 _104487 p1 t p2 u) = False.
Proof. exact (@lem4360725 (term8 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360727 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term153 _104486 _104487 p1 t p2 u) = False.
Proof. exact (TRANS (@lem4360723 _104486 _104487 p1 t p2 u) (@lem4360726 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360728 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term152 _104486 _104487 p1 t p2 u) = (term153 _104486 _104487 p1 t p2 u)) = (False = False).
Proof. exact (MK_COMB (@lem4360712 _104486 _104487 p1 t p2 u) (@lem4360727 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360730 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4360731 : (False = False) = (~ False).
Proof. exact (@lem4360730 False). Qed.
Lemma lem4360733 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4360734 : (False = False) = True.
Proof. exact (TRANS (@lem4360731) (@lem4360733)). Qed.
Lemma lem4360735 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : ((term152 _104486 _104487 p1 t p2 u) = (term153 _104486 _104487 p1 t p2 u)) = True.
Proof. exact (TRANS (@lem4360728 _104486 _104487 p1 t p2 u) (@lem4360734)). Qed.
Lemma lem4360736 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : True = ((term152 _104486 _104487 p1 t p2 u) = (term153 _104486 _104487 p1 t p2 u)).
Proof. exact (SYM (@lem4360735 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360737 {_104486 _104487 : Type'} (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term152 _104486 _104487 p1 t p2 u) = (term153 _104486 _104487 p1 t p2 u).
Proof. exact (EQ_MP (@lem4360736 _104486 _104487 p1 t p2 u) (@lem0)). Qed.
Lemma lem4360738 {_104486 _104487 : Type'} (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (s : _104486 -> Prop) (h1 : (@IN _104486 p1 s) = False) : (term102 _104486 _104487 s p1 t p2 u) = (term106 _104486 _104487 s p1 t p2 u).
Proof. exact (EQ_MP (@lem4360563 _104486 _104487 t p2 u p1 s h1) (@lem4360737 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360739 {_104486 _104487 : Type'} (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) (p1 : _104486) (s : _104486 -> Prop) (h1 : (@IN _104486 p1 s) = True) : (term102 _104486 _104487 s p1 t p2 u) = (term106 _104486 _104487 s p1 t p2 u).
Proof. exact (EQ_MP (@lem4360550 _104486 _104487 t p2 u p1 s h1) (@lem4360695 _104486 _104487 p1 t p2 u)). Qed.
Lemma lem4360742 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (p2 : _104487) (u : _104487 -> Prop) : (term102 _104486 _104487 s p1 t p2 u) = (term106 _104486 _104487 s p1 t p2 u).
Proof. exact (or_elim (@lem4360521 _104486 p1 s) (fun h0 : (@IN _104486 p1 s) = True => @lem4360739 _104486 _104487 t p2 u p1 s h0) (fun h0 : (@IN _104486 p1 s) = False => @lem4360738 _104486 _104487 t p2 u p1 s h0)). Qed.
Lemma lem4360747 {_104486 _104487 : Type'} (s : _104486 -> Prop) (p1 : _104486) (t : _104486 -> Prop) (u : _104487 -> Prop) : term108 _104486 _104487 s p1 t u.
Proof. exact (fun p2 : _104487 => @lem4360742 _104486 _104487 s p1 t p2 u). Qed.
Lemma lem4360752 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) (u : _104487 -> Prop) : term110 _104486 _104487 s t u.
Proof. exact (fun p1 : _104486 => @lem4360747 _104486 _104487 s p1 t u). Qed.
Lemma lem4360757 {_104486 _104487 : Type'} (s : _104486 -> Prop) (t : _104486 -> Prop) : term114 _104486 _104487 s t.
Proof. exact (fun u : _104487 -> Prop => @lem4360752 _104486 _104487 s t u). Qed.
Lemma lem4360762 {_104486 _104487 : Type'} (s : _104486 -> Prop) : term118 _104486 _104487 s.
Proof. exact (fun t : _104486 -> Prop => @lem4360757 _104486 _104487 s t). Qed.
Lemma lem4360767 {_104486 _104487 : Type'} : term122 _104486 _104487.
Proof. exact (fun s : _104486 -> Prop => @lem4360762 _104486 _104487 s). Qed.
Lemma lem4360772 {_104453 _104454 : Type'} (t : _104454 -> Prop) (p1 : _104453) (s : _104453 -> Prop) (u : _104454 -> Prop) : term60 _104453 _104454 t p1 s u.
Proof. exact (fun p2 : _104454 => @lem4360504 _104453 _104454 t p1 s p2 u). Qed.
Lemma lem4360777 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) (u : _104454 -> Prop) : term62 _104453 _104454 t s u.
Proof. exact (fun p1 : _104453 => @lem4360772 _104453 _104454 t p1 s u). Qed.
Lemma lem4360782 {_104453 _104454 : Type'} (t : _104454 -> Prop) (s : _104453 -> Prop) : term66 _104453 _104454 t s.
Proof. exact (fun u : _104454 -> Prop => @lem4360777 _104453 _104454 t s u). Qed.
Lemma lem4360787 {_104453 _104454 : Type'} (s : _104453 -> Prop) : term70 _104453 _104454 s.
Proof. exact (fun t : _104454 -> Prop => @lem4360782 _104453 _104454 t s). Qed.
Lemma lem4360792 {_104453 _104454 : Type'} : term74 _104453 _104454.
Proof. exact (fun s : _104453 -> Prop => @lem4360787 _104453 _104454 s). Qed.
Lemma lem4360793 {_104453 _104454 _104486 _104487 : Type'} : term124 _104453 _104454 _104486 _104487.
Proof. exact (conj (@lem4360792 _104453 _104454) (@lem4360767 _104486 _104487)). Qed.
Lemma lem4360794 {_104453 _104454 _104486 _104487 : Type'} : term123 _104453 _104454 _104486 _104487.
Proof. exact (EQ_MP (@lem4360378 _104453 _104454 _104486 _104487) (@lem4360793 _104453 _104454 _104486 _104487)). Qed.
