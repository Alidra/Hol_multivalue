Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POLYNOMIAL_FUNCTION_FINITE_ROOTS_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import CONTRAPOS_THM_spec.
Require Import INFINITE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import POLYNOMIAL_FUNCTION_CONST_spec.
Require Import POLYNOMIAL_FUNCTION_SUB_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_POLYFUN_FINITE_ROOTS_spec.
Require Import REAL_SUB_0_spec.
Require Import SUM_0_spec.
Require Import polynomial_function_spec.
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
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm3399787_spec.
Require Import thm3399835_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm7261449_spec.
Require Import thm7261450_spec.
Lemma lem7587040 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem7069399 A s). Qed.
Lemma lem7587041 {A : Type'} (s : A -> Prop) : (term0 A s) = ((term1 A s) = term2).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem7587043 (x : real) : term3 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem7587044 (x : real) : (term3 x) = ((term4 x) = term2).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem7587054 (p : Prop) : term5 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem7587055 (p : Prop) : (term5 p) = (term6 p).
Proof. exact (eq_refl (term5 p)). Qed.
Lemma lem7587056 (p : Prop) : term6 p.
Proof. exact (EQ_MP (@lem7587055 p) (@lem7587054 p)). Qed.
Lemma lem7587057 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem7587058 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem7587067 (q : Prop) : (term7 q) = (term7 q).
Proof. exact (eq_refl (term7 q)). Qed.
Lemma lem7587068 (q : Prop) (p : Prop) (h1 : p = True) : (term8 q p) = (term9 q).
Proof. exact (MK_COMB (@lem7587067 q) (@lem7587057 p h1)). Qed.
Lemma lem7587069 (q : Prop) : (term9 q) = ((term10 q) = (True -> q)).
Proof. exact (eq_refl (term9 q)). Qed.
Lemma lem7587070 (q : Prop) (p : Prop) : (term11 q p) = (term11 q p).
Proof. exact (eq_refl (term11 q p)). Qed.
Lemma lem7587071 (p : Prop) (q : Prop) : ((term8 q p) = (term9 q)) = ((term8 q p) = ((term10 q) = (True -> q))).
Proof. exact (MK_COMB (@lem7587070 q p) (@lem7587069 q)). Qed.
Lemma lem7587072 (p : Prop) (q : Prop) : (term8 q p) = ((term12 p q) = (p -> q)).
Proof. exact (eq_refl (term8 q p)). Qed.
Lemma lem7587073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7587074 (p : Prop) (q : Prop) : (term11 q p) = (term13 p q).
Proof. exact (MK_COMB (@lem7587073) (@lem7587072 p q)). Qed.
Lemma lem7587075 (q : Prop) : ((term10 q) = (True -> q)) = ((term10 q) = (True -> q)).
Proof. exact (eq_refl ((term10 q) = (True -> q))). Qed.
Lemma lem7587076 (p : Prop) (q : Prop) : ((term8 q p) = ((term10 q) = (True -> q))) = (((term12 p q) = (p -> q)) = ((term10 q) = (True -> q))).
Proof. exact (MK_COMB (@lem7587074 p q) (@lem7587075 q)). Qed.
Lemma lem7587077 (p : Prop) (q : Prop) : ((term8 q p) = (term9 q)) = (((term12 p q) = (p -> q)) = ((term10 q) = (True -> q))).
Proof. exact (TRANS (@lem7587071 p q) (@lem7587076 p q)). Qed.
Lemma lem7587078 (q : Prop) (p : Prop) (h1 : p = True) : ((term12 p q) = (p -> q)) = ((term10 q) = (True -> q)).
Proof. exact (EQ_MP (@lem7587077 p q) (@lem7587068 q p h1)). Qed.
Lemma lem7587079 (q : Prop) (p : Prop) (h1 : p = True) : ((term10 q) = (True -> q)) = ((term12 p q) = (p -> q)).
Proof. exact (SYM (@lem7587078 q p h1)). Qed.
Lemma lem7587080 (q : Prop) : (term7 q) = (term7 q).
Proof. exact (eq_refl (term7 q)). Qed.
Lemma lem7587081 (q : Prop) (p : Prop) (h1 : p = False) : (term8 q p) = (term14 q).
Proof. exact (MK_COMB (@lem7587080 q) (@lem7587058 p h1)). Qed.
Lemma lem7587082 (q : Prop) : (term14 q) = ((term15 q) = (False -> q)).
Proof. exact (eq_refl (term14 q)). Qed.
Lemma lem7587083 (q : Prop) (p : Prop) : (term11 q p) = (term11 q p).
Proof. exact (eq_refl (term11 q p)). Qed.
Lemma lem7587084 (p : Prop) (q : Prop) : ((term8 q p) = (term14 q)) = ((term8 q p) = ((term15 q) = (False -> q))).
Proof. exact (MK_COMB (@lem7587083 q p) (@lem7587082 q)). Qed.
Lemma lem7587085 (p : Prop) (q : Prop) : (term8 q p) = ((term12 p q) = (p -> q)).
Proof. exact (eq_refl (term8 q p)). Qed.
Lemma lem7587086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7587087 (p : Prop) (q : Prop) : (term11 q p) = (term13 p q).
Proof. exact (MK_COMB (@lem7587086) (@lem7587085 p q)). Qed.
Lemma lem7587088 (q : Prop) : ((term15 q) = (False -> q)) = ((term15 q) = (False -> q)).
Proof. exact (eq_refl ((term15 q) = (False -> q))). Qed.
Lemma lem7587089 (p : Prop) (q : Prop) : ((term8 q p) = ((term15 q) = (False -> q))) = (((term12 p q) = (p -> q)) = ((term15 q) = (False -> q))).
Proof. exact (MK_COMB (@lem7587087 p q) (@lem7587088 q)). Qed.
Lemma lem7587090 (p : Prop) (q : Prop) : ((term8 q p) = (term14 q)) = (((term12 p q) = (p -> q)) = ((term15 q) = (False -> q))).
Proof. exact (TRANS (@lem7587084 p q) (@lem7587089 p q)). Qed.
Lemma lem7587091 (q : Prop) (p : Prop) (h1 : p = False) : ((term12 p q) = (p -> q)) = ((term15 q) = (False -> q)).
Proof. exact (EQ_MP (@lem7587090 p q) (@lem7587081 q p h1)). Qed.
Lemma lem7587092 (q : Prop) (p : Prop) (h1 : p = False) : ((term15 q) = (False -> q)) = ((term12 p q) = (p -> q)).
Proof. exact (SYM (@lem7587091 q p h1)). Qed.
Lemma lem7587096 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7587097 (q : Prop) : (term16 q) = (~ q).
Proof. exact (@lem7587096 (~ q)). Qed.
Lemma lem7587098 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7587099 (q : Prop) : (term10 q) = (term17 q).
Proof. exact (MK_COMB (@lem7587098) (@lem7587097 q)). Qed.
Lemma lem7587101 (t : Prop) : (term17 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem7587102 (q : Prop) : (term17 q) = q.
Proof. exact (@lem7587101 q). Qed.
Lemma lem7587103 (q : Prop) : (term10 q) = q.
Proof. exact (TRANS (@lem7587099 q) (@lem7587102 q)). Qed.
Lemma lem7587104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7587105 (q : Prop) : (term18 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem7587104) (@lem7587103 q)). Qed.
Lemma lem7587107 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7587108 (q : Prop) : (True -> q) = q.
Proof. exact (@lem7587107 q). Qed.
Lemma lem7587109 (q : Prop) : ((term10 q) = (True -> q)) = (q = q).
Proof. exact (MK_COMB (@lem7587105 q) (@lem7587108 q)). Qed.
Lemma lem7587111 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7587112 (x : Prop) : (x = x) = True.
Proof. exact (@lem7587111 Prop x). Qed.
Lemma lem7587113 (q : Prop) : (q = q) = True.
Proof. exact (@lem7587112 q). Qed.
Lemma lem7587114 (q : Prop) : ((term10 q) = (True -> q)) = True.
Proof. exact (TRANS (@lem7587109 q) (@lem7587113 q)). Qed.
Lemma lem7587115 (q : Prop) : True = ((term10 q) = (True -> q)).
Proof. exact (SYM (@lem7587114 q)). Qed.
Lemma lem7587116 (q : Prop) : (term10 q) = (True -> q).
Proof. exact (EQ_MP (@lem7587115 q) (@lem0)). Qed.
Lemma lem7587120 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem7587121 (q : Prop) : (term19 q) = False.
Proof. exact (@lem7587120 (~ q)). Qed.
Lemma lem7587122 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7587123 (q : Prop) : (term15 q) = (~ False).
Proof. exact (MK_COMB (@lem7587122) (@lem7587121 q)). Qed.
Lemma lem7587125 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7587126 (q : Prop) : (term15 q) = True.
Proof. exact (TRANS (@lem7587123 q) (@lem7587125)). Qed.
Lemma lem7587127 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7587128 (q : Prop) : (term20 q) = (@eq Prop True).
Proof. exact (MK_COMB (@lem7587127) (@lem7587126 q)). Qed.
Lemma lem7587130 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem7587131 (q : Prop) : (False -> q) = True.
Proof. exact (@lem7587130 q). Qed.
Lemma lem7587132 (q : Prop) : ((term15 q) = (False -> q)) = (True = True).
Proof. exact (MK_COMB (@lem7587128 q) (@lem7587131 q)). Qed.
Lemma lem7587134 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem7587135 : (True = True) = True.
Proof. exact (@lem7587134 True). Qed.
Lemma lem7587136 (q : Prop) : ((term15 q) = (False -> q)) = True.
Proof. exact (TRANS (@lem7587132 q) (@lem7587135)). Qed.
Lemma lem7587137 (q : Prop) : True = ((term15 q) = (False -> q)).
Proof. exact (SYM (@lem7587136 q)). Qed.
Lemma lem7587138 (q : Prop) : (term15 q) = (False -> q).
Proof. exact (EQ_MP (@lem7587137 q) (@lem0)). Qed.
Lemma lem7587139 (q : Prop) (p : Prop) (h1 : p = False) : (term12 p q) = (p -> q).
Proof. exact (EQ_MP (@lem7587092 q p h1) (@lem7587138 q)). Qed.
Lemma lem7587140 (q : Prop) (p : Prop) (h1 : p = True) : (term12 p q) = (p -> q).
Proof. exact (EQ_MP (@lem7587079 q p h1) (@lem7587116 q)). Qed.
Lemma lem7587144 {A : Type'} (P : A -> Prop) : term21 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem7587145 {A : Type'} (P : A -> Prop) : (term21 A P) = ((term22 A P) = (term23 A P)).
Proof. exact (eq_refl (term21 A P)). Qed.
Lemma lem7587148 {A : Type'} (s : A -> Prop) (h1 : (@INFINITE A s) = (term24 A s)) : (@INFINITE A s) = (term24 A s).
Proof. exact (h1). Qed.
Lemma lem7587149 {A : Type'} (s : A -> Prop) (h1 : (@INFINITE A s) = (term24 A s)) : (term24 A s) = (@INFINITE A s).
Proof. exact (SYM (@lem7587148 A s h1)). Qed.
Lemma lem7587150 {A : Type'} (s : A -> Prop) (h1 : (term24 A s) = (@INFINITE A s)) : (term24 A s) = (@INFINITE A s).
Proof. exact (h1). Qed.
Lemma lem7587151 {A : Type'} (s : A -> Prop) (h1 : (term24 A s) = (@INFINITE A s)) : (@INFINITE A s) = (term24 A s).
Proof. exact (SYM (@lem7587150 A s h1)). Qed.
Lemma lem7587152 {A : Type'} (s : A -> Prop) : ((@INFINITE A s) = (term24 A s)) = ((term24 A s) = (@INFINITE A s)).
Proof. exact (prop_ext (fun h1 : (@INFINITE A s) = (term24 A s) => @lem7587149 A s h1) (fun h1 : (term24 A s) = (@INFINITE A s) => @lem7587151 A s h1)). Qed.
Lemma lem7587153 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7587152 A s)). Qed.
Lemma lem7587154 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7587155 {A : Type'} : (term27 A) = (term28 A).
Proof. exact (MK_COMB (@lem7587154 A) (@lem7587153 A)). Qed.
Lemma lem7587156 {A : Type'} : term28 A.
Proof. exact (EQ_MP (@lem7587155 A) (@lem3198543 A)). Qed.
Lemma lem7587157 : (@INFINITE real (@UNIV real)) = ((@INFINITE real (@UNIV real)) = True).
Proof. exact (@lem7 (@INFINITE real (@UNIV real))). Qed.
Lemma lem7587159 {A : Type'} (s : A -> Prop) : term29 A s.
Proof. exact (@lem7587156 A s). Qed.
Lemma lem7587160 {A : Type'} (s : A -> Prop) : (term29 A s) = ((term24 A s) = (@INFINITE A s)).
Proof. exact (eq_refl (term29 A s)). Qed.
Lemma lem7587164 (t2 : Prop) (t1 : Prop) (h1 : (term30 t1 t2) = (t2 -> t1)) : (term30 t1 t2) = (t2 -> t1).
Proof. exact (h1). Qed.
Lemma lem7587165 (t2 : Prop) (t1 : Prop) (h1 : (term30 t1 t2) = (t2 -> t1)) : (t2 -> t1) = (term30 t1 t2).
Proof. exact (SYM (@lem7587164 t2 t1 h1)). Qed.
Lemma lem7587166 (t1 : Prop) (t2 : Prop) (h1 : (t2 -> t1) = (term30 t1 t2)) : (t2 -> t1) = (term30 t1 t2).
Proof. exact (h1). Qed.
Lemma lem7587167 (t1 : Prop) (t2 : Prop) (h1 : (t2 -> t1) = (term30 t1 t2)) : (term30 t1 t2) = (t2 -> t1).
Proof. exact (SYM (@lem7587166 t1 t2 h1)). Qed.
Lemma lem7587168 (t1 : Prop) (t2 : Prop) : ((term30 t1 t2) = (t2 -> t1)) = ((t2 -> t1) = (term30 t1 t2)).
Proof. exact (prop_ext (fun h1 : (term30 t1 t2) = (t2 -> t1) => @lem7587165 t2 t1 h1) (fun h1 : (t2 -> t1) = (term30 t1 t2) => @lem7587167 t1 t2 h1)). Qed.
Lemma lem7587169 (t1 : Prop) : (term31 t1) = (term32 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem7587168 t1 t2)). Qed.
Lemma lem7587170 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem7587171 (t1 : Prop) : (term33 t1) = (term34 t1).
Proof. exact (MK_COMB (@lem7587170) (@lem7587169 t1)). Qed.
Lemma lem7587172 : term35 = term36.
Proof. exact (fun_ext (fun t1 : Prop => @lem7587171 t1)). Qed.
Lemma lem7587173 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem7587174 : term37 = term38.
Proof. exact (MK_COMB (@lem7587173) (@lem7587172)). Qed.
Lemma lem7587175 : term38.
Proof. exact (EQ_MP (@lem7587174) (@lem10414)). Qed.
Lemma lem7587176 (t1 : Prop) : term39 t1.
Proof. exact (@lem7587175 t1). Qed.
Lemma lem7587177 (t1 : Prop) : (term39 t1) = (term34 t1).
Proof. exact (eq_refl (term39 t1)). Qed.
Lemma lem7587178 (t1 : Prop) : term34 t1.
Proof. exact (EQ_MP (@lem7587177 t1) (@lem7587176 t1)). Qed.
Lemma lem7587179 (t1 : Prop) (t2 : Prop) : term40 t1 t2.
Proof. exact (@lem7587178 t1 t2). Qed.
Lemma lem7587180 (t1 : Prop) (t2 : Prop) : (term40 t1 t2) = ((t2 -> t1) = (term30 t1 t2)).
Proof. exact (eq_refl (term40 t1 t2)). Qed.
Lemma lem7587182 (p : real -> real) : term41 p.
Proof. exact (@lem7553488 p). Qed.
Lemma lem7587183 (p : real -> real) : (term41 p) = ((polynomial_function p) = (term42 p)).
Proof. exact (eq_refl (term41 p)). Qed.
Lemma lem7587187 (x : real) (y : real) (h1 : ((real_sub x y) = term2) = (x = y)) : ((real_sub x y) = term2) = (x = y).
Proof. exact (h1). Qed.
Lemma lem7587188 (x : real) (y : real) (h1 : ((real_sub x y) = term2) = (x = y)) : (x = y) = ((real_sub x y) = term2).
Proof. exact (SYM (@lem7587187 x y h1)). Qed.
Lemma lem7587189 (x : real) (y : real) (h1 : (x = y) = ((real_sub x y) = term2)) : (x = y) = ((real_sub x y) = term2).
Proof. exact (h1). Qed.
Lemma lem7587190 (x : real) (y : real) (h1 : (x = y) = ((real_sub x y) = term2)) : ((real_sub x y) = term2) = (x = y).
Proof. exact (SYM (@lem7587189 x y h1)). Qed.
Lemma lem7587191 (x : real) (y : real) : (((real_sub x y) = term2) = (x = y)) = ((x = y) = ((real_sub x y) = term2)).
Proof. exact (prop_ext (fun h1 : ((real_sub x y) = term2) = (x = y) => @lem7587188 x y h1) (fun h1 : (x = y) = ((real_sub x y) = term2) => @lem7587190 x y h1)). Qed.
Lemma lem7587192 (x : real) : (term43 x) = (term44 x).
Proof. exact (fun_ext (fun y : real => @lem7587191 x y)). Qed.
Lemma lem7587193 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7587194 (x : real) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem7587193) (@lem7587192 x)). Qed.
Lemma lem7587195 : term47 = term48.
Proof. exact (fun_ext (fun x : real => @lem7587194 x)). Qed.
Lemma lem7587196 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7587197 : term49 = term50.
Proof. exact (MK_COMB (@lem7587196) (@lem7587195)). Qed.
Lemma lem7587198 : term50.
Proof. exact (EQ_MP (@lem7587197) (@lem1376695)). Qed.
Lemma lem7587199 (x : real) : term51 x.
Proof. exact (@lem7587198 x). Qed.
Lemma lem7587200 (x : real) : (term51 x) = (term46 x).
Proof. exact (eq_refl (term51 x)). Qed.
Lemma lem7587201 (x : real) : term46 x.
Proof. exact (EQ_MP (@lem7587200 x) (@lem7587199 x)). Qed.
Lemma lem7587202 (x : real) (y : real) : term52 x y.
Proof. exact (@lem7587201 x y). Qed.
Lemma lem7587203 (x : real) (y : real) : (term52 x y) = ((x = y) = ((real_sub x y) = term2)).
Proof. exact (eq_refl (term52 x y)). Qed.
Lemma lem7587226 (x : real) (y : real) : (x = y) = ((real_sub x y) = term2).
Proof. exact (EQ_MP (@lem7587203 x y) (@lem7587202 x y)). Qed.
Lemma lem7587227 (p : real -> real) (x : real) (a : real) : ((p x) = a) = ((term53 p x a) = term2).
Proof. exact (@lem7587226 (p x) a). Qed.
Lemma lem7587228 (GEN_PVAR_351 : real) : (@SETSPEC real GEN_PVAR_351) = (@SETSPEC real GEN_PVAR_351).
Proof. exact (eq_refl (@SETSPEC real GEN_PVAR_351)). Qed.
Lemma lem7587229 (GEN_PVAR_351 : real) (p : real -> real) (x : real) (a : real) : (term54 GEN_PVAR_351 p x a) = (term55 GEN_PVAR_351 p x a).
Proof. exact (MK_COMB (@lem7587228 GEN_PVAR_351) (@lem7587227 p x a)). Qed.
Lemma lem7587230 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7587231 (GEN_PVAR_351 : real) (p : real -> real) (a : real) (x : real) : (term56 GEN_PVAR_351 p a x) = (term57 GEN_PVAR_351 p a x).
Proof. exact (MK_COMB (@lem7587229 GEN_PVAR_351 p x a) (@lem7587230 x)). Qed.
Lemma lem7587232 (GEN_PVAR_351 : real) (p : real -> real) (a : real) : (term58 GEN_PVAR_351 p a) = (term59 GEN_PVAR_351 p a).
Proof. exact (fun_ext (fun x : real => @lem7587231 GEN_PVAR_351 p a x)). Qed.
Lemma lem7587233 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7587234 (GEN_PVAR_351 : real) (p : real -> real) (a : real) : (term60 GEN_PVAR_351 p a) = (term61 GEN_PVAR_351 p a).
Proof. exact (MK_COMB (@lem7587233) (@lem7587232 GEN_PVAR_351 p a)). Qed.
Lemma lem7587235 (p : real -> real) (a : real) : (term62 p a) = (term63 p a).
Proof. exact (fun_ext (fun GEN_PVAR_351 : real => @lem7587234 GEN_PVAR_351 p a)). Qed.
Lemma lem7587236 : (@GSPEC real) = (@GSPEC real).
Proof. exact (eq_refl (@GSPEC real)). Qed.
Lemma lem7587237 (p : real -> real) (a : real) : (term64 p a) = (term65 p a).
Proof. exact (MK_COMB (@lem7587236) (@lem7587235 p a)). Qed.
Lemma lem7587238 : (@FINITE real) = (@FINITE real).
Proof. exact (eq_refl (@FINITE real)). Qed.
Lemma lem7587239 (p : real -> real) (a : real) : (term66 p a) = (term67 p a).
Proof. exact (MK_COMB (@lem7587238) (@lem7587237 p a)). Qed.
Lemma lem7587240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7587241 (p : real -> real) (a : real) : (term68 p a) = (term69 p a).
Proof. exact (MK_COMB (@lem7587240) (@lem7587239 p a)). Qed.
Lemma lem7587249 (x : real) (y : real) : (x = y) = ((real_sub x y) = term2).
Proof. exact (EQ_MP (@lem7587203 x y) (@lem7587202 x y)). Qed.
Lemma lem7587250 (p : real -> real) (x : real) (a : real) : ((p x) = a) = ((term53 p x a) = term2).
Proof. exact (@lem7587249 (p x) a). Qed.
Lemma lem7587251 (p : real -> real) (a : real) : (term70 p a) = (term71 p a).
Proof. exact (fun_ext (fun x : real => @lem7587250 p x a)). Qed.
Lemma lem7587252 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7587253 (p : real -> real) (a : real) : (term72 p a) = (term73 p a).
Proof. exact (MK_COMB (@lem7587252) (@lem7587251 p a)). Qed.
Lemma lem7587254 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7587255 (p : real -> real) (a : real) : (term74 p a) = (term75 p a).
Proof. exact (MK_COMB (@lem7587254) (@lem7587253 p a)). Qed.
Lemma lem7587256 (p : real -> real) (a : real) : ((term66 p a) = (term74 p a)) = ((term67 p a) = (term75 p a)).
Proof. exact (MK_COMB (@lem7587241 p a) (@lem7587255 p a)). Qed.
Lemma lem7587257 (p : real -> real) : (term76 p) = (term76 p).
Proof. exact (eq_refl (term76 p)). Qed.
Lemma lem7587258 (p : real -> real) (a : real) : (term77 p a) = (term78 p a).
Proof. exact (MK_COMB (@lem7587257 p) (@lem7587256 p a)). Qed.
Lemma lem7587259 (p : real -> real) : (term79 p) = (term80 p).
Proof. exact (fun_ext (fun a : real => @lem7587258 p a)). Qed.
Lemma lem7587260 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7587261 (p : real -> real) : (term81 p) = (term82 p).
Proof. exact (MK_COMB (@lem7587260) (@lem7587259 p)). Qed.
Lemma lem7587262 : term83 = term84.
Proof. exact (fun_ext (fun p : real -> real => @lem7587261 p)). Qed.
Lemma lem7587263 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7587264 : term85 = term86.
Proof. exact (MK_COMB (@lem7587263) (@lem7587262)). Qed.
Lemma lem7587265 : term86 = term85.
Proof. exact (SYM (@lem7587264)). Qed.
Lemma lem7587266 (h1 : term87) : term87.
Proof. exact (h1). Qed.
Lemma lem7587267 (c : real) : term88 c.
Proof. exact (@lem7553635 c). Qed.
Lemma lem7587268 (c : real) : (term88 c) = (term89 c).
Proof. exact (eq_refl (term88 c)). Qed.
Lemma lem7587269 (c : real) : term89 c.
Proof. exact (EQ_MP (@lem7587268 c) (@lem7587267 c)). Qed.
Lemma lem7587270 (c : real) : (term89 c) = ((term89 c) = True).
Proof. exact (@lem7 (term89 c)). Qed.
Lemma lem7587272 (p : real -> real) : term90 p.
Proof. exact (@lem7567846 p). Qed.
Lemma lem7587273 (p : real -> real) : (term90 p) = (term91 p).
Proof. exact (eq_refl (term90 p)). Qed.
Lemma lem7587274 (p : real -> real) : term91 p.
Proof. exact (EQ_MP (@lem7587273 p) (@lem7587272 p)). Qed.
Lemma lem7587275 (p : real -> real) (q : real -> real) : term92 p q.
Proof. exact (@lem7587274 p q). Qed.
Lemma lem7587276 (p : real -> real) (q : real -> real) : (term92 p q) = (term93 p q).
Proof. exact (eq_refl (term92 p q)). Qed.
Lemma lem7587277 (p : real -> real) (q : real -> real) : term93 p q.
Proof. exact (EQ_MP (@lem7587276 p q) (@lem7587275 p q)). Qed.
Lemma lem7587278 (p : real -> real) (q : real -> real) (h1 : term94 p q) : term94 p q.
Proof. exact (h1). Qed.
Lemma lem7587279 (p : real -> real) (q : real -> real) (h1 : term94 p q) : term95 p q.
Proof. exact (@lem7587277 p q (@lem7587278 p q h1)). Qed.
Lemma lem7587280 (p : real -> real) (q : real -> real) : (term95 p q) = ((term95 p q) = True).
Proof. exact (@lem7 (term95 p q)). Qed.
Lemma lem7587281 (p : real -> real) (q : real -> real) (h1 : term94 p q) : (term95 p q) = True.
Proof. exact (EQ_MP (@lem7587280 p q) (@lem7587279 p q h1)). Qed.
Lemma lem7587287 (p : real -> real) (h1 : term87) : term96 p.
Proof. exact (@lem7587266 h1 p). Qed.
Lemma lem7587288 (p : real -> real) : (term96 p) = (term97 p).
Proof. exact (eq_refl (term96 p)). Qed.
Lemma lem7587289 (p : real -> real) (h1 : term87) : term97 p.
Proof. exact (EQ_MP (@lem7587288 p) (@lem7587287 p h1)). Qed.
Lemma lem7587290 (p : real -> real) (h1 : polynomial_function p) : polynomial_function p.
Proof. exact (h1). Qed.
Lemma lem7587291 (p : real -> real) (h1 : term87) (h2 : polynomial_function p) : (term98 p) = (term99 p).
Proof. exact (@lem7587289 p h1 (@lem7587290 p h2)). Qed.
Lemma lem7587308 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term100 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7587309 (p : Prop) (q : Prop) (p' : Prop) : term101 p q p'.
Proof. exact (fun q' : Prop => @lem7587308 p q p' q'). Qed.
Lemma lem7587310 (p : Prop) (q : Prop) : term102 p q.
Proof. exact (fun p' : Prop => @lem7587309 p q p'). Qed.
Lemma lem7587311 (p : real -> real) (a : real) : term103 p a.
Proof. exact (@lem7587310 (polynomial_function p) ((term67 p a) = (term75 p a))). Qed.
Lemma lem7587312 (p : real -> real) (a : real) (p' : Prop) : term104 p a p'.
Proof. exact (@lem7587311 p a p'). Qed.
Lemma lem7587313 (p : real -> real) (a : real) (p' : Prop) : (term104 p a p') = (term105 p a p').
Proof. exact (eq_refl (term104 p a p')). Qed.
Lemma lem7587314 (p : real -> real) (a : real) (p' : Prop) : term105 p a p'.
Proof. exact (EQ_MP (@lem7587313 p a p') (@lem7587312 p a p')). Qed.
Lemma lem7587315 (p : real -> real) (a : real) (p' : Prop) (q' : Prop) : term106 p a p' q'.
Proof. exact (@lem7587314 p a p' q'). Qed.
Lemma lem7587316 (p : real -> real) (a : real) (p' : Prop) (q' : Prop) : (term106 p a p' q') = (term107 p a p' q').
Proof. exact (eq_refl (term106 p a p' q')). Qed.
Lemma lem7587317 (p : real -> real) (a : real) (p' : Prop) (q' : Prop) : term107 p a p' q'.
Proof. exact (EQ_MP (@lem7587316 p a p' q') (@lem7587315 p a p' q')). Qed.
Lemma lem7587318 (p : real -> real) : (polynomial_function p) = (polynomial_function p).
Proof. exact (eq_refl (polynomial_function p)). Qed.
Lemma lem7587319 (a : real) (p : real -> real) (q' : Prop) : term108 a p q'.
Proof. exact (@lem7587317 p a (polynomial_function p) q'). Qed.
Lemma lem7587320 (a : real) (p : real -> real) (q' : Prop) : term109 a p q'.
Proof. exact (@lem7587319 a p q' (@lem7587318 p)). Qed.
Lemma lem7587321 (p : real -> real) (h1 : polynomial_function p) : polynomial_function p.
Proof. exact (h1). Qed.
Lemma lem7587322 (p : real -> real) : (polynomial_function p) = ((polynomial_function p) = True).
Proof. exact (@lem7 (polynomial_function p)). Qed.
Lemma lem7587327 (p : real -> real) (h1 : term87) : term97 p.
Proof. exact (fun h0 : polynomial_function p => @lem7587291 p h1 h0). Qed.
Lemma lem7587328 (p : real -> real) (a : real) (h1 : term87) : term110 p a.
Proof. exact (@lem7587327 (term111 p a) h1). Qed.
Lemma lem7587329 (p : real -> real) (x : real) (a : real) : (term112 p a x) = (term53 p x a).
Proof. exact (eq_refl (term112 p a x)). Qed.
Lemma lem7587330 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7587331 (p : real -> real) (x : real) (a : real) : (term113 p a x) = (term114 p x a).
Proof. exact (MK_COMB (@lem7587330) (@lem7587329 p x a)). Qed.
Lemma lem7587332 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7587333 (p : real -> real) (x : real) (a : real) : ((term112 p a x) = term2) = ((term53 p x a) = term2).
Proof. exact (MK_COMB (@lem7587331 p x a) (@lem7587332)). Qed.
Lemma lem7587334 (GEN_PVAR_351 : real) : (@SETSPEC real GEN_PVAR_351) = (@SETSPEC real GEN_PVAR_351).
Proof. exact (eq_refl (@SETSPEC real GEN_PVAR_351)). Qed.
Lemma lem7587335 (GEN_PVAR_351 : real) (p : real -> real) (x : real) (a : real) : (term115 GEN_PVAR_351 p a x) = (term55 GEN_PVAR_351 p x a).
Proof. exact (MK_COMB (@lem7587334 GEN_PVAR_351) (@lem7587333 p x a)). Qed.
Lemma lem7587336 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7587337 (GEN_PVAR_351 : real) (p : real -> real) (a : real) (x : real) : (term116 GEN_PVAR_351 p a x) = (term57 GEN_PVAR_351 p a x).
Proof. exact (MK_COMB (@lem7587335 GEN_PVAR_351 p x a) (@lem7587336 x)). Qed.
Lemma lem7587338 (GEN_PVAR_351 : real) (p : real -> real) (a : real) : (term117 GEN_PVAR_351 p a) = (term59 GEN_PVAR_351 p a).
Proof. exact (fun_ext (fun x : real => @lem7587337 GEN_PVAR_351 p a x)). Qed.
Lemma lem7587339 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7587340 (GEN_PVAR_351 : real) (p : real -> real) (a : real) : (term118 GEN_PVAR_351 p a) = (term61 GEN_PVAR_351 p a).
Proof. exact (MK_COMB (@lem7587339) (@lem7587338 GEN_PVAR_351 p a)). Qed.
Lemma lem7587341 (p : real -> real) (a : real) : (term119 p a) = (term63 p a).
Proof. exact (fun_ext (fun GEN_PVAR_351 : real => @lem7587340 GEN_PVAR_351 p a)). Qed.
Lemma lem7587342 : (@GSPEC real) = (@GSPEC real).
Proof. exact (eq_refl (@GSPEC real)). Qed.
Lemma lem7587343 (p : real -> real) (a : real) : (term120 p a) = (term65 p a).
Proof. exact (MK_COMB (@lem7587342) (@lem7587341 p a)). Qed.
Lemma lem7587344 : (@FINITE real) = (@FINITE real).
Proof. exact (eq_refl (@FINITE real)). Qed.
Lemma lem7587345 (p : real -> real) (a : real) : (term121 p a) = (term67 p a).
Proof. exact (MK_COMB (@lem7587344) (@lem7587343 p a)). Qed.
Lemma lem7587346 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7587347 (p : real -> real) (a : real) : (term122 p a) = (term69 p a).
Proof. exact (MK_COMB (@lem7587346) (@lem7587345 p a)). Qed.
Lemma lem7587348 (p : real -> real) (x : real) (a : real) : (term112 p a x) = (term53 p x a).
Proof. exact (eq_refl (term112 p a x)). Qed.
Lemma lem7587349 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7587350 (p : real -> real) (x : real) (a : real) : (term113 p a x) = (term114 p x a).
Proof. exact (MK_COMB (@lem7587349) (@lem7587348 p x a)). Qed.
Lemma lem7587351 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7587352 (p : real -> real) (x : real) (a : real) : ((term112 p a x) = term2) = ((term53 p x a) = term2).
Proof. exact (MK_COMB (@lem7587350 p x a) (@lem7587351)). Qed.
Lemma lem7587353 (p : real -> real) (a : real) : (term123 p a) = (term71 p a).
Proof. exact (fun_ext (fun x : real => @lem7587352 p x a)). Qed.
Lemma lem7587354 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7587355 (p : real -> real) (a : real) : (term124 p a) = (term73 p a).
Proof. exact (MK_COMB (@lem7587354) (@lem7587353 p a)). Qed.
Lemma lem7587356 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7587357 (p : real -> real) (a : real) : (term125 p a) = (term75 p a).
Proof. exact (MK_COMB (@lem7587356) (@lem7587355 p a)). Qed.
Lemma lem7587358 (p : real -> real) (a : real) : ((term121 p a) = (term125 p a)) = ((term67 p a) = (term75 p a)).
Proof. exact (MK_COMB (@lem7587347 p a) (@lem7587357 p a)). Qed.
Lemma lem7587359 (p : real -> real) (a : real) : (term126 p a) = (term126 p a).
Proof. exact (eq_refl (term126 p a)). Qed.
Lemma lem7587360 (p : real -> real) (a : real) : (term110 p a) = (term127 p a).
Proof. exact (MK_COMB (@lem7587359 p a) (@lem7587358 p a)). Qed.
Lemma lem7587361 (p : real -> real) (a : real) (h1 : term87) : term127 p a.
Proof. exact (EQ_MP (@lem7587360 p a) (@lem7587328 p a h1)). Qed.
Lemma lem7587363 (p : real -> real) (q : real -> real) : term128 p q.
Proof. exact (fun h0 : term94 p q => @lem7587281 p q h0). Qed.
Lemma lem7587364 (p : real -> real) (a : real) : term129 p a.
Proof. exact (@lem7587363 p (term130 a)). Qed.
Lemma lem7587365 (x : real) (a : real) : (term131 a x) = a.
Proof. exact (eq_refl (term131 a x)). Qed.
Lemma lem7587366 (p : real -> real) (x : real) : (term132 p x) = (term132 p x).
Proof. exact (eq_refl (term132 p x)). Qed.
Lemma lem7587367 (p : real -> real) (x : real) (a : real) : (term133 p a x) = (term53 p x a).
Proof. exact (MK_COMB (@lem7587366 p x) (@lem7587365 x a)). Qed.
Lemma lem7587368 (p : real -> real) (a : real) : (term134 p a) = (term111 p a).
Proof. exact (fun_ext (fun x : real => @lem7587367 p x a)). Qed.
Lemma lem7587369 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7587370 (p : real -> real) (a : real) : (term135 p a) = (term136 p a).
Proof. exact (MK_COMB (@lem7587369) (@lem7587368 p a)). Qed.
Lemma lem7587371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7587372 (p : real -> real) (a : real) : (term137 p a) = (term138 p a).
Proof. exact (MK_COMB (@lem7587371) (@lem7587370 p a)). Qed.
Lemma lem7587373 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem7587374 (p : real -> real) (a : real) : ((term135 p a) = True) = ((term136 p a) = True).
Proof. exact (MK_COMB (@lem7587372 p a) (@lem7587373)). Qed.
Lemma lem7587375 (p : real -> real) (a : real) : (term139 p a) = (term139 p a).
Proof. exact (eq_refl (term139 p a)). Qed.
Lemma lem7587376 (p : real -> real) (a : real) : (term129 p a) = (term140 p a).
Proof. exact (MK_COMB (@lem7587375 p a) (@lem7587374 p a)). Qed.
Lemma lem7587377 (p : real -> real) (a : real) : term140 p a.
Proof. exact (EQ_MP (@lem7587376 p a) (@lem7587364 p a)). Qed.
Lemma lem7587381 (p : real -> real) (h1 : polynomial_function p) : (polynomial_function p) = True.
Proof. exact (EQ_MP (@lem7587322 p) (@lem7587321 p h1)). Qed.
Lemma lem7587382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7587383 (p : real -> real) (h1 : polynomial_function p) : (term141 p) = (and True).
Proof. exact (MK_COMB (@lem7587382) (@lem7587381 p h1)). Qed.
Lemma lem7587385 (c : real) : (term89 c) = True.
Proof. exact (EQ_MP (@lem7587270 c) (@lem7587269 c)). Qed.
Lemma lem7587386 (a : real) : (term89 a) = True.
Proof. exact (@lem7587385 a). Qed.
Lemma lem7587387 (a : real) (p : real -> real) (h1 : polynomial_function p) : (term142 p a) = (True /\ True).
Proof. exact (MK_COMB (@lem7587383 p h1) (@lem7587386 a)). Qed.
Lemma lem7587389 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7587390 : (True /\ True) = True.
Proof. exact (@lem7587389 True). Qed.
Lemma lem7587391 (a : real) (p : real -> real) (h1 : polynomial_function p) : (term142 p a) = True.
Proof. exact (TRANS (@lem7587387 a p h1) (@lem7587390)). Qed.
Lemma lem7587392 (a : real) (p : real -> real) (h1 : polynomial_function p) : True = (term142 p a).
Proof. exact (SYM (@lem7587391 a p h1)). Qed.
Lemma lem7587393 (a : real) (p : real -> real) (h1 : polynomial_function p) : term142 p a.
Proof. exact (EQ_MP (@lem7587392 a p h1) (@lem0)). Qed.
Lemma lem7587394 (a : real) (p : real -> real) (h1 : polynomial_function p) : (term136 p a) = True.
Proof. exact (@lem7587377 p a (@lem7587393 a p h1)). Qed.
Lemma lem7587395 (a : real) (p : real -> real) (h1 : polynomial_function p) : True = (term136 p a).
Proof. exact (SYM (@lem7587394 a p h1)). Qed.
Lemma lem7587396 (a : real) (p : real -> real) (h1 : polynomial_function p) : term136 p a.
Proof. exact (EQ_MP (@lem7587395 a p h1) (@lem0)). Qed.
Lemma lem7587397 (a : real) (p : real -> real) (h1 : term87) (h2 : polynomial_function p) : (term67 p a) = (term75 p a).
Proof. exact (@lem7587361 p a h1 (@lem7587396 a p h2)). Qed.
Lemma lem7587404 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7587405 (a : real) (p : real -> real) (h1 : term87) (h2 : polynomial_function p) : (term69 p a) = (term143 p a).
Proof. exact (MK_COMB (@lem7587404) (@lem7587397 a p h1 h2)). Qed.
Lemma lem7587418 (p : real -> real) (a : real) : (term75 p a) = (term75 p a).
Proof. exact (eq_refl (term75 p a)). Qed.
Lemma lem7587419 (a : real) (p : real -> real) (h1 : term87) (h2 : polynomial_function p) : ((term67 p a) = (term75 p a)) = ((term75 p a) = (term75 p a)).
Proof. exact (MK_COMB (@lem7587405 a p h1 h2) (@lem7587418 p a)). Qed.
Lemma lem7587421 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7587422 (x : Prop) : (x = x) = True.
Proof. exact (@lem7587421 Prop x). Qed.
Lemma lem7587423 (p : real -> real) (a : real) : ((term75 p a) = (term75 p a)) = True.
Proof. exact (@lem7587422 (term75 p a)). Qed.
Lemma lem7587424 (a : real) (p : real -> real) (h1 : term87) (h2 : polynomial_function p) : ((term67 p a) = (term75 p a)) = True.
Proof. exact (TRANS (@lem7587419 a p h1 h2) (@lem7587423 p a)). Qed.
Lemma lem7587425 (p : real -> real) (a : real) (h1 : term87) : term144 p a.
Proof. exact (fun h0 : polynomial_function p => @lem7587424 a p h1 h0). Qed.
Lemma lem7587426 (a : real) (p : real -> real) : term145 a p.
Proof. exact (@lem7587320 a p True). Qed.
Lemma lem7587427 (a : real) (p : real -> real) (h1 : term87) : (term78 p a) = (term146 p).
Proof. exact (@lem7587426 a p (@lem7587425 p a h1)). Qed.
Lemma lem7587429 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7587430 (p : real -> real) : (term146 p) = True.
Proof. exact (@lem7587429 (polynomial_function p)). Qed.
Lemma lem7587431 (p : real -> real) (a : real) (h1 : term87) : (term78 p a) = True.
Proof. exact (TRANS (@lem7587427 a p h1) (@lem7587430 p)). Qed.
Lemma lem7587432 (p : real -> real) (h1 : term87) : (term80 p) = term147.
Proof. exact (fun_ext (fun a : real => @lem7587431 p a h1)). Qed.
Lemma lem7587433 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7587434 (p : real -> real) (h1 : term87) : (term82 p) = term148.
Proof. exact (MK_COMB (@lem7587433) (@lem7587432 p h1)). Qed.
Lemma lem7587436 {A : Type'} (t : Prop) : (term149 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7587437 (t : Prop) : (term150 t) = t.
Proof. exact (@lem7587436 real t). Qed.
Lemma lem7587438 : term148 = True.
Proof. exact (@lem7587437 True). Qed.
Lemma lem7587439 (p : real -> real) (h1 : term87) : (term82 p) = True.
Proof. exact (TRANS (@lem7587434 p h1) (@lem7587438)). Qed.
Lemma lem7587440 (h1 : term87) : term84 = term151.
Proof. exact (fun_ext (fun p : real -> real => @lem7587439 p h1)). Qed.
Lemma lem7587441 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7587442 (h1 : term87) : term86 = term152.
Proof. exact (MK_COMB (@lem7587441) (@lem7587440 h1)). Qed.
Lemma lem7587444 {A : Type'} (t : Prop) : (term149 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7587445 (t : Prop) : (term153 t) = t.
Proof. exact (@lem7587444 (real -> real) t). Qed.
Lemma lem7587446 : term152 = True.
Proof. exact (@lem7587445 True). Qed.
Lemma lem7587447 (h1 : term87) : term86 = True.
Proof. exact (TRANS (@lem7587442 h1) (@lem7587446)). Qed.
Lemma lem7587448 (h1 : term87) : True = term86.
Proof. exact (SYM (@lem7587447 h1)). Qed.
Lemma lem7587449 (h1 : term87) : term86.
Proof. exact (EQ_MP (@lem7587448 h1) (@lem0)). Qed.
Lemma lem7587453 (p : real -> real) : (polynomial_function p) = (term42 p).
Proof. exact (EQ_MP (@lem7587183 p) (@lem7587182 p)). Qed.
Lemma lem7587468 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7587469 (p : real -> real) : (term76 p) = (term154 p).
Proof. exact (MK_COMB (@lem7587468) (@lem7587453 p)). Qed.
Lemma lem7587484 (p : real -> real) : ((term98 p) = (term99 p)) = ((term98 p) = (term99 p)).
Proof. exact (eq_refl ((term98 p) = (term99 p))). Qed.
Lemma lem7587485 (p : real -> real) : (term97 p) = (term155 p).
Proof. exact (MK_COMB (@lem7587469 p) (@lem7587484 p)). Qed.
Lemma lem7587488 (p : real -> real) : (term155 p) = (term97 p).
Proof. exact (SYM (@lem7587485 p)). Qed.
Lemma lem7587489 (p : real -> real) (h1 : term42 p) : term42 p.
Proof. exact (h1). Qed.
Lemma lem7587490 (p : real -> real) (m : nat) (h1 : term156 p m) : term156 p m.
Proof. exact (h1). Qed.
Lemma lem7587491 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : term157 p m c.
Proof. exact (h1). Qed.
Lemma lem7587495 (t1 : Prop) (t2 : Prop) : (t2 -> t1) = (term30 t1 t2).
Proof. exact (EQ_MP (@lem7587180 t1 t2) (@lem7587179 t1 t2)). Qed.
Lemma lem7587496 (p : real -> real) : (term158 p) = (term159 p).
Proof. exact (@lem7587495 (term99 p) (term98 p)). Qed.
Lemma lem7587497 (p : real -> real) : (term159 p) = (term158 p).
Proof. exact (SYM (@lem7587496 p)). Qed.
Lemma lem7587501 (t1 : Prop) (t2 : Prop) : (t2 -> t1) = (term30 t1 t2).
Proof. exact (EQ_MP (@lem7587180 t1 t2) (@lem7587179 t1 t2)). Qed.
Lemma lem7587502 (p : real -> real) : (term160 p) = (term161 p).
Proof. exact (@lem7587501 (term98 p) (term99 p)). Qed.
Lemma lem7587503 (p : real -> real) : (term161 p) = (term160 p).
Proof. exact (SYM (@lem7587502 p)). Qed.
Lemma lem7587507 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term100 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7587508 (p : Prop) (q : Prop) (p' : Prop) : term101 p q p'.
Proof. exact (fun q' : Prop => @lem7587507 p q p' q'). Qed.
Lemma lem7587509 (p : Prop) (q : Prop) : term102 p q.
Proof. exact (fun p' : Prop => @lem7587508 p q p'). Qed.
Lemma lem7587510 (p : real -> real) : term162 p.
Proof. exact (@lem7587509 (term163 p) (term164 p)). Qed.
Lemma lem7587511 (p : real -> real) (p' : Prop) : term165 p p'.
Proof. exact (@lem7587510 p p'). Qed.
Lemma lem7587512 (p : real -> real) (p' : Prop) : (term165 p p') = (term166 p p').
Proof. exact (eq_refl (term165 p p')). Qed.
Lemma lem7587513 (p : real -> real) (p' : Prop) : term166 p p'.
Proof. exact (EQ_MP (@lem7587512 p p') (@lem7587511 p p')). Qed.
Lemma lem7587514 (p : real -> real) (p' : Prop) (q' : Prop) : term167 p p' q'.
Proof. exact (@lem7587513 p p' q'). Qed.
Lemma lem7587515 (p : real -> real) (p' : Prop) (q' : Prop) : (term167 p p' q') = (term168 p p' q').
Proof. exact (eq_refl (term167 p p' q')). Qed.
Lemma lem7587516 (p : real -> real) (p' : Prop) (q' : Prop) : term168 p p' q'.
Proof. exact (EQ_MP (@lem7587515 p p' q') (@lem7587514 p p' q')). Qed.
Lemma lem7587518 (t : Prop) : (term17 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem7587519 (p : real -> real) : (term163 p) = (term169 p).
Proof. exact (@lem7587518 (term169 p)). Qed.
Lemma lem7587526 (p : real -> real) (q' : Prop) : term170 p q'.
Proof. exact (@lem7587516 p (term169 p) q'). Qed.
Lemma lem7587527 (p : real -> real) (q' : Prop) : term171 p q'.
Proof. exact (@lem7587526 p q' (@lem7587519 p)). Qed.
Lemma lem7587528 (p : real -> real) (h1 : term169 p) : term169 p.
Proof. exact (h1). Qed.
Lemma lem7587529 (x : real) (p : real -> real) (h1 : term169 p) : term172 p x.
Proof. exact (@lem7587528 p h1 x). Qed.
Lemma lem7587530 (p : real -> real) (x : real) : (term172 p x) = ((p x) = term2).
Proof. exact (eq_refl (term172 p x)). Qed.
Lemma lem7587533 {A : Type'} (s : A -> Prop) : (term24 A s) = (@INFINITE A s).
Proof. exact (EQ_MP (@lem7587160 A s) (@lem7587159 A s)). Qed.
Lemma lem7587534 (s : real -> Prop) : (term173 s) = (@INFINITE real s).
Proof. exact (@lem7587533 real s). Qed.
Lemma lem7587535 (p : real -> real) : (term164 p) = (term174 p).
Proof. exact (@lem7587534 (term175 p)). Qed.
Lemma lem7587543 (x : real) (p : real -> real) (h1 : term169 p) : (p x) = term2.
Proof. exact (EQ_MP (@lem7587530 p x) (@lem7587529 x p h1)). Qed.
Lemma lem7587544 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7587545 (x : real) (p : real -> real) (h1 : term169 p) : (term176 p x) = term177.
Proof. exact (MK_COMB (@lem7587544) (@lem7587543 x p h1)). Qed.
Lemma lem7587546 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7587547 (x : real) (p : real -> real) (h1 : term169 p) : ((p x) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem7587545 x p h1) (@lem7587546)). Qed.
Lemma lem7587549 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7587550 (x : real) : (x = x) = True.
Proof. exact (@lem7587549 real x). Qed.
Lemma lem7587551 : (term2 = term2) = True.
Proof. exact (@lem7587550 term2). Qed.
Lemma lem7587552 (x : real) (p : real -> real) (h1 : term169 p) : ((p x) = term2) = True.
Proof. exact (TRANS (@lem7587547 x p h1) (@lem7587551)). Qed.
Lemma lem7587553 (GEN_PVAR_350 : real) : (@SETSPEC real GEN_PVAR_350) = (@SETSPEC real GEN_PVAR_350).
Proof. exact (eq_refl (@SETSPEC real GEN_PVAR_350)). Qed.
Lemma lem7587554 (x : real) (GEN_PVAR_350 : real) (p : real -> real) (h1 : term169 p) : (term178 GEN_PVAR_350 p x) = (@SETSPEC real GEN_PVAR_350 True).
Proof. exact (MK_COMB (@lem7587553 GEN_PVAR_350) (@lem7587552 x p h1)). Qed.
Lemma lem7587555 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7587556 (GEN_PVAR_350 : real) (x : real) (p : real -> real) (h1 : term169 p) : (term179 GEN_PVAR_350 p x) = (@SETSPEC real GEN_PVAR_350 True x).
Proof. exact (MK_COMB (@lem7587554 x GEN_PVAR_350 p h1) (@lem7587555 x)). Qed.
Lemma lem7587557 (GEN_PVAR_350 : real) (p : real -> real) (h1 : term169 p) : (term180 GEN_PVAR_350 p) = (term181 GEN_PVAR_350).
Proof. exact (fun_ext (fun x : real => @lem7587556 GEN_PVAR_350 x p h1)). Qed.
Lemma lem7587558 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7587559 (GEN_PVAR_350 : real) (p : real -> real) (h1 : term169 p) : (term182 GEN_PVAR_350 p) = (term183 GEN_PVAR_350).
Proof. exact (MK_COMB (@lem7587558) (@lem7587557 GEN_PVAR_350 p h1)). Qed.
Lemma lem7587564 (p : real -> real) (h1 : term169 p) : (term184 p) = term185.
Proof. exact (fun_ext (fun GEN_PVAR_350 : real => @lem7587559 GEN_PVAR_350 p h1)). Qed.
Lemma lem7587569 : (@GSPEC real) = (@GSPEC real).
Proof. exact (eq_refl (@GSPEC real)). Qed.
Lemma lem7587570 (p : real -> real) (h1 : term169 p) : (term175 p) = term186.
Proof. exact (MK_COMB (@lem7587569) (@lem7587564 p h1)). Qed.
Lemma lem7587572 {_88312 : Type'} : (term187 _88312) = (@UNIV _88312).
Proof. exact (EQ_MP (@lem3399787 _88312) (@lem3399835 _88312)). Qed.
Lemma lem7587573 : term186 = (@UNIV real).
Proof. exact (@lem7587572 real). Qed.
Lemma lem7587574 (p : real -> real) (h1 : term169 p) : (term175 p) = (@UNIV real).
Proof. exact (TRANS (@lem7587570 p h1) (@lem7587573)). Qed.
Lemma lem7587575 : (@INFINITE real) = (@INFINITE real).
Proof. exact (eq_refl (@INFINITE real)). Qed.
Lemma lem7587576 (p : real -> real) (h1 : term169 p) : (term174 p) = (@INFINITE real (@UNIV real)).
Proof. exact (MK_COMB (@lem7587575) (@lem7587574 p h1)). Qed.
Lemma lem7587578 : (@INFINITE real (@UNIV real)) = True.
Proof. exact (EQ_MP (@lem7587157) (@lem4713723)). Qed.
Lemma lem7587579 (p : real -> real) (h1 : term169 p) : (term174 p) = True.
Proof. exact (TRANS (@lem7587576 p h1) (@lem7587578)). Qed.
Lemma lem7587580 (p : real -> real) (h1 : term169 p) : (term164 p) = True.
Proof. exact (TRANS (@lem7587535 p) (@lem7587579 p h1)). Qed.
Lemma lem7587581 (p : real -> real) : term188 p.
Proof. exact (fun h0 : term169 p => @lem7587580 p h0). Qed.
Lemma lem7587582 (p : real -> real) : term189 p.
Proof. exact (@lem7587527 p True). Qed.
Lemma lem7587583 (p : real -> real) : (term159 p) = (term190 p).
Proof. exact (@lem7587582 p (@lem7587581 p)). Qed.
Lemma lem7587585 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7587586 (p : real -> real) : (term190 p) = True.
Proof. exact (@lem7587585 (term169 p)). Qed.
Lemma lem7587587 (p : real -> real) : (term159 p) = True.
Proof. exact (TRANS (@lem7587583 p) (@lem7587586 p)). Qed.
Lemma lem7587588 (p : real -> real) : True = (term159 p).
Proof. exact (SYM (@lem7587587 p)). Qed.
Lemma lem7587589 (p : real -> real) : term159 p.
Proof. exact (EQ_MP (@lem7587588 p) (@lem0)). Qed.
Lemma lem7587590 (n : nat) : term191 n.
Proof. exact (@lem7539125 n). Qed.
Lemma lem7587591 (n : nat) : (term191 n) = (term192 n).
Proof. exact (eq_refl (term191 n)). Qed.
Lemma lem7587592 (n : nat) : term192 n.
Proof. exact (EQ_MP (@lem7587591 n) (@lem7587590 n)). Qed.
Lemma lem7587593 (n : nat) (c : nat -> real) : term193 n c.
Proof. exact (@lem7587592 n c). Qed.
Lemma lem7587594 (n : nat) (c : nat -> real) : (term193 n c) = ((term194 n c) = (term195 n c)).
Proof. exact (eq_refl (term193 n c)). Qed.
Lemma lem7587596 (x : real) (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : term196 p m c x.
Proof. exact (@lem7587491 p m c h1 x). Qed.
Lemma lem7587597 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term196 p m c x) = ((p x) = (term197 m c x)).
Proof. exact (eq_refl (term196 p m c x)). Qed.
Lemma lem7587608 (x : real) (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (p x) = (term197 m c x).
Proof. exact (EQ_MP (@lem7587597 p m c x) (@lem7587596 x p m c h1)). Qed.
Lemma lem7587609 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7587610 (x : real) (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term176 p x) = (term198 m c x).
Proof. exact (MK_COMB (@lem7587609) (@lem7587608 x p m c h1)). Qed.
Lemma lem7587611 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7587612 (x : real) (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : ((p x) = term2) = ((term197 m c x) = term2).
Proof. exact (MK_COMB (@lem7587610 x p m c h1) (@lem7587611)). Qed.
Lemma lem7587615 (GEN_PVAR_350 : real) : (@SETSPEC real GEN_PVAR_350) = (@SETSPEC real GEN_PVAR_350).
Proof. exact (eq_refl (@SETSPEC real GEN_PVAR_350)). Qed.
Lemma lem7587616 (GEN_PVAR_350 : real) (x : real) (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term178 GEN_PVAR_350 p x) = (term199 GEN_PVAR_350 m c x).
Proof. exact (MK_COMB (@lem7587615 GEN_PVAR_350) (@lem7587612 x p m c h1)). Qed.
Lemma lem7587617 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7587618 (GEN_PVAR_350 : real) (x : real) (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term179 GEN_PVAR_350 p x) = (term200 GEN_PVAR_350 m c x).
Proof. exact (MK_COMB (@lem7587616 GEN_PVAR_350 x p m c h1) (@lem7587617 x)). Qed.
Lemma lem7587619 (GEN_PVAR_350 : real) (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term180 GEN_PVAR_350 p) = (term201 GEN_PVAR_350 m c).
Proof. exact (fun_ext (fun x : real => @lem7587618 GEN_PVAR_350 x p m c h1)). Qed.
Lemma lem7587620 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7587621 (GEN_PVAR_350 : real) (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term182 GEN_PVAR_350 p) = (term202 GEN_PVAR_350 m c).
Proof. exact (MK_COMB (@lem7587620) (@lem7587619 GEN_PVAR_350 p m c h1)). Qed.
Lemma lem7587626 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term184 p) = (term203 m c).
Proof. exact (fun_ext (fun GEN_PVAR_350 : real => @lem7587621 GEN_PVAR_350 p m c h1)). Qed.
Lemma lem7587627 : (@GSPEC real) = (@GSPEC real).
Proof. exact (eq_refl (@GSPEC real)). Qed.
Lemma lem7587628 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term175 p) = (term204 m c).
Proof. exact (MK_COMB (@lem7587627) (@lem7587626 p m c h1)). Qed.
Lemma lem7587629 : (@FINITE real) = (@FINITE real).
Proof. exact (eq_refl (@FINITE real)). Qed.
Lemma lem7587630 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term98 p) = (term194 m c).
Proof. exact (MK_COMB (@lem7587629) (@lem7587628 p m c h1)). Qed.
Lemma lem7587632 (n : nat) (c : nat -> real) : (term194 n c) = (term195 n c).
Proof. exact (EQ_MP (@lem7587594 n c) (@lem7587593 n c)). Qed.
Lemma lem7587633 (m : nat) (c : nat -> real) : (term194 m c) = (term195 m c).
Proof. exact (@lem7587632 m c). Qed.
Lemma lem7587642 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term98 p) = (term195 m c).
Proof. exact (TRANS (@lem7587630 p m c h1) (@lem7587633 m c)). Qed.
Lemma lem7587643 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7587644 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term164 p) = (term205 m c).
Proof. exact (MK_COMB (@lem7587643) (@lem7587642 p m c h1)). Qed.
Lemma lem7587645 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7587646 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term206 p) = (term207 m c).
Proof. exact (MK_COMB (@lem7587645) (@lem7587644 p m c h1)). Qed.
Lemma lem7587648 (t : Prop) : (term17 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem7587649 (p : real -> real) : (term163 p) = (term169 p).
Proof. exact (@lem7587648 (term169 p)). Qed.
Lemma lem7587657 (x : real) (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (p x) = (term197 m c x).
Proof. exact (EQ_MP (@lem7587597 p m c x) (@lem7587596 x p m c h1)). Qed.
Lemma lem7587658 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7587659 (x : real) (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term176 p x) = (term198 m c x).
Proof. exact (MK_COMB (@lem7587658) (@lem7587657 x p m c h1)). Qed.
Lemma lem7587660 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7587661 (x : real) (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : ((p x) = term2) = ((term197 m c x) = term2).
Proof. exact (MK_COMB (@lem7587659 x p m c h1) (@lem7587660)). Qed.
Lemma lem7587664 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term208 p) = (term209 m c).
Proof. exact (fun_ext (fun x : real => @lem7587661 x p m c h1)). Qed.
Lemma lem7587665 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7587666 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term169 p) = (term210 m c).
Proof. exact (MK_COMB (@lem7587665) (@lem7587664 p m c h1)). Qed.
Lemma lem7587671 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term163 p) = (term210 m c).
Proof. exact (TRANS (@lem7587649 p) (@lem7587666 p m c h1)). Qed.
Lemma lem7587672 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term161 p) = (term211 m c).
Proof. exact (MK_COMB (@lem7587646 p m c h1) (@lem7587671 p m c h1)). Qed.
Lemma lem7587675 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term211 m c) = (term161 p).
Proof. exact (SYM (@lem7587672 p m c h1)). Qed.
Lemma lem7587679 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term100 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7587680 (p : Prop) (q : Prop) (p' : Prop) : term101 p q p'.
Proof. exact (fun q' : Prop => @lem7587679 p q p' q'). Qed.
Lemma lem7587681 (p : Prop) (q : Prop) : term102 p q.
Proof. exact (fun p' : Prop => @lem7587680 p q p'). Qed.
Lemma lem7587682 (m : nat) (c : nat -> real) : term212 m c.
Proof. exact (@lem7587681 (term205 m c) (term210 m c)). Qed.
Lemma lem7587683 (m : nat) (c : nat -> real) (p' : Prop) : term213 m c p'.
Proof. exact (@lem7587682 m c p'). Qed.
Lemma lem7587684 (m : nat) (c : nat -> real) (p' : Prop) : (term213 m c p') = (term214 m c p').
Proof. exact (eq_refl (term213 m c p')). Qed.
Lemma lem7587685 (m : nat) (c : nat -> real) (p' : Prop) : term214 m c p'.
Proof. exact (EQ_MP (@lem7587684 m c p') (@lem7587683 m c p')). Qed.
Lemma lem7587686 (m : nat) (c : nat -> real) (p' : Prop) (q' : Prop) : term215 m c p' q'.
Proof. exact (@lem7587685 m c p' q'). Qed.
Lemma lem7587687 (m : nat) (c : nat -> real) (p' : Prop) (q' : Prop) : (term215 m c p' q') = (term216 m c p' q').
Proof. exact (eq_refl (term215 m c p' q')). Qed.
Lemma lem7587688 (m : nat) (c : nat -> real) (p' : Prop) (q' : Prop) : term216 m c p' q'.
Proof. exact (EQ_MP (@lem7587687 m c p' q') (@lem7587686 m c p' q')). Qed.
Lemma lem7587690 {A : Type'} (P : A -> Prop) : (term22 A P) = (term23 A P).
Proof. exact (EQ_MP (@lem7587145 A P) (@lem7587144 A P)). Qed.
Lemma lem7587691 (P : nat -> Prop) : (term217 P) = (term218 P).
Proof. exact (@lem7587690 nat P). Qed.
Lemma lem7587692 (m : nat) (c : nat -> real) : (term219 m c) = (term220 m c).
Proof. exact (@lem7587691 (term221 m c)). Qed.
Lemma lem7587693 (m : nat) (c : nat -> real) (i : nat) : (term222 m c i) = (term223 m c i).
Proof. exact (eq_refl (term222 m c i)). Qed.
Lemma lem7587694 (m : nat) (c : nat -> real) : (term224 m c) = (term221 m c).
Proof. exact (fun_ext (fun i : nat => @lem7587693 m c i)). Qed.
Lemma lem7587695 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7587696 (m : nat) (c : nat -> real) : (term225 m c) = (term195 m c).
Proof. exact (MK_COMB (@lem7587695) (@lem7587694 m c)). Qed.
Lemma lem7587697 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7587698 (m : nat) (c : nat -> real) : (term219 m c) = (term205 m c).
Proof. exact (MK_COMB (@lem7587697) (@lem7587696 m c)). Qed.
Lemma lem7587699 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7587700 (m : nat) (c : nat -> real) : (term226 m c) = (term227 m c).
Proof. exact (MK_COMB (@lem7587699) (@lem7587698 m c)). Qed.
Lemma lem7587701 (m : nat) (c : nat -> real) (i : nat) : (term222 m c i) = (term223 m c i).
Proof. exact (eq_refl (term222 m c i)). Qed.
Lemma lem7587702 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7587703 (m : nat) (c : nat -> real) (i : nat) : (term228 m c i) = (term229 m c i).
Proof. exact (MK_COMB (@lem7587702) (@lem7587701 m c i)). Qed.
Lemma lem7587704 (m : nat) (c : nat -> real) : (term230 m c) = (term231 m c).
Proof. exact (fun_ext (fun i : nat => @lem7587703 m c i)). Qed.
Lemma lem7587705 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7587706 (m : nat) (c : nat -> real) : (term220 m c) = (term232 m c).
Proof. exact (MK_COMB (@lem7587705) (@lem7587704 m c)). Qed.
Lemma lem7587707 (m : nat) (c : nat -> real) : ((term219 m c) = (term220 m c)) = ((term205 m c) = (term232 m c)).
Proof. exact (MK_COMB (@lem7587700 m c) (@lem7587706 m c)). Qed.
Lemma lem7587708 (m : nat) (c : nat -> real) : (term205 m c) = (term232 m c).
Proof. exact (EQ_MP (@lem7587707 m c) (@lem7587692 m c)). Qed.
Lemma lem7587714 (p : Prop) (q : Prop) : (term12 p q) = (p -> q).
Proof. exact (or_elim (@lem7587056 p) (fun h0 : p = True => @lem7587140 q p h0) (fun h0 : p = False => @lem7587139 q p h0)). Qed.
Lemma lem7587715 (m : nat) (c : nat -> real) (i : nat) : (term229 m c i) = (term233 m c i).
Proof. exact (@lem7587714 (term234 i m) ((c i) = term2)). Qed.
Lemma lem7587743 (m : nat) (c : nat -> real) : (term231 m c) = (term235 m c).
Proof. exact (fun_ext (fun i : nat => @lem7587715 m c i)). Qed.
Lemma lem7587771 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7587772 (m : nat) (c : nat -> real) : (term232 m c) = (term236 m c).
Proof. exact (MK_COMB (@lem7587771) (@lem7587743 m c)). Qed.
Lemma lem7587804 (m : nat) (c : nat -> real) : (term205 m c) = (term236 m c).
Proof. exact (TRANS (@lem7587708 m c) (@lem7587772 m c)). Qed.
Lemma lem7587805 (m : nat) (c : nat -> real) (q' : Prop) : term237 m c q'.
Proof. exact (@lem7587688 m c (term236 m c) q'). Qed.
Lemma lem7587806 (m : nat) (c : nat -> real) (q' : Prop) : term238 m c q'.
Proof. exact (@lem7587805 m c q' (@lem7587804 m c)). Qed.
Lemma lem7587807 (m : nat) (c : nat -> real) (h1 : term236 m c) : term236 m c.
Proof. exact (h1). Qed.
Lemma lem7587808 (i : nat) (m : nat) (c : nat -> real) (h1 : term236 m c) : term239 m c i.
Proof. exact (@lem7587807 m c h1 i). Qed.
Lemma lem7587809 (m : nat) (c : nat -> real) (i : nat) : (term239 m c i) = (term233 m c i).
Proof. exact (eq_refl (term239 m c i)). Qed.
Lemma lem7587810 (i : nat) (m : nat) (c : nat -> real) (h1 : term236 m c) : term233 m c i.
Proof. exact (EQ_MP (@lem7587809 m c i) (@lem7587808 i m c h1)). Qed.
Lemma lem7587811 (i : nat) (m : nat) (h1 : term234 i m) : term234 i m.
Proof. exact (h1). Qed.
Lemma lem7587812 (c : nat -> real) (i : nat) (m : nat) (h1 : term236 m c) (h2 : term234 i m) : (c i) = term2.
Proof. exact (@lem7587810 i m c h1 (@lem7587811 i m h2)). Qed.
Lemma lem7587888 {_137613 : Type'} (f : _137613 -> real) (s : _137613 -> Prop) (g : _137613 -> real) : term240 _137613 f s g.
Proof. exact (EQ_MP (@lem7261450 _137613 f s g) (@lem7261449 _137613 f g s)). Qed.
Lemma lem7587889 {_137613 : Type'} (f : _137613 -> real) (s : _137613 -> Prop) : term241 _137613 f s.
Proof. exact (fun g : _137613 -> real => @lem7587888 _137613 f s g). Qed.
Lemma lem7587890 (f : nat -> real) (s : nat -> Prop) : term242 f s.
Proof. exact (@lem7587889 nat f s). Qed.
Lemma lem7587891 (c : nat -> real) (x : real) (m : nat) : term243 c x m.
Proof. exact (@lem7587890 (term244 c x) (term245 m)). Qed.
Lemma lem7587892 (c : nat -> real) (x : real) (x' : nat) : (term246 c x x') = (term247 c x x').
Proof. exact (eq_refl (term246 c x x')). Qed.
Lemma lem7587893 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7587894 (c : nat -> real) (x : real) (x' : nat) : (term248 c x x') = (term249 c x x').
Proof. exact (MK_COMB (@lem7587893) (@lem7587892 c x x')). Qed.
Lemma lem7587895 (g : nat -> real) (x : nat) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem7587896 (c : nat -> real) (x : real) (g : nat -> real) (x' : nat) : ((term246 c x x') = (g x')) = ((term247 c x x') = (g x')).
Proof. exact (MK_COMB (@lem7587894 c x x') (@lem7587895 g x')). Qed.
Lemma lem7587897 (x : nat) (m : nat) : (term250 x m) = (term250 x m).
Proof. exact (eq_refl (term250 x m)). Qed.
Lemma lem7587898 (m : nat) (c : nat -> real) (x : real) (g : nat -> real) (x' : nat) : (term251 m c x g x') = (term252 m c x g x').
Proof. exact (MK_COMB (@lem7587897 x' m) (@lem7587896 c x g x')). Qed.
Lemma lem7587899 (m : nat) (c : nat -> real) (x : real) (g : nat -> real) : (term253 m c x g) = (term254 m c x g).
Proof. exact (fun_ext (fun x' : nat => @lem7587898 m c x g x')). Qed.
Lemma lem7587900 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7587901 (m : nat) (c : nat -> real) (x : real) (g : nat -> real) : (term255 m c x g) = (term256 m c x g).
Proof. exact (MK_COMB (@lem7587900) (@lem7587899 m c x g)). Qed.
Lemma lem7587902 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7587903 (m : nat) (c : nat -> real) (x : real) (g : nat -> real) : (term257 m c x g) = (term258 m c x g).
Proof. exact (MK_COMB (@lem7587902) (@lem7587901 m c x g)). Qed.
Lemma lem7587904 (c : nat -> real) (x : real) (i : nat) : (term246 c x i) = (term247 c x i).
Proof. exact (eq_refl (term246 c x i)). Qed.
Lemma lem7587905 (c : nat -> real) (x : real) : (term259 c x) = (term244 c x).
Proof. exact (fun_ext (fun i : nat => @lem7587904 c x i)). Qed.
Lemma lem7587906 (m : nat) : (term260 m) = (term260 m).
Proof. exact (eq_refl (term260 m)). Qed.
Lemma lem7587907 (m : nat) (c : nat -> real) (x : real) : (term261 m c x) = (term197 m c x).
Proof. exact (MK_COMB (@lem7587906 m) (@lem7587905 c x)). Qed.
Lemma lem7587908 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7587909 (m : nat) (c : nat -> real) (x : real) : (term262 m c x) = (term198 m c x).
Proof. exact (MK_COMB (@lem7587908) (@lem7587907 m c x)). Qed.
Lemma lem7587910 (m : nat) (g : nat -> real) : (term263 m g) = (term263 m g).
Proof. exact (eq_refl (term263 m g)). Qed.
Lemma lem7587911 (c : nat -> real) (x : real) (m : nat) (g : nat -> real) : ((term261 m c x) = (term263 m g)) = ((term197 m c x) = (term263 m g)).
Proof. exact (MK_COMB (@lem7587909 m c x) (@lem7587910 m g)). Qed.
Lemma lem7587912 (c : nat -> real) (x : real) (m : nat) (g : nat -> real) : (term264 c x m g) = (term265 c x m g).
Proof. exact (MK_COMB (@lem7587903 m c x g) (@lem7587911 c x m g)). Qed.
Lemma lem7587913 (c : nat -> real) (x : real) (m : nat) : (term266 c x m) = (term267 c x m).
Proof. exact (fun_ext (fun g : nat -> real => @lem7587912 c x m g)). Qed.
Lemma lem7587914 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7587915 (c : nat -> real) (x : real) (m : nat) : (term243 c x m) = (term268 c x m).
Proof. exact (MK_COMB (@lem7587914) (@lem7587913 c x m)). Qed.
Lemma lem7587916 (c : nat -> real) (x : real) (m : nat) : term268 c x m.
Proof. exact (EQ_MP (@lem7587915 c x m) (@lem7587891 c x m)). Qed.
Lemma lem7587917 (c : nat -> real) (x : real) (m : nat) (g : nat -> real) : term269 c x m g.
Proof. exact (@lem7587916 c x m g). Qed.
Lemma lem7587918 (c : nat -> real) (x : real) (m : nat) (g : nat -> real) : (term269 c x m g) = (term265 c x m g).
Proof. exact (eq_refl (term269 c x m g)). Qed.
Lemma lem7587920 (x : nat) (m : nat) (h1 : term234 x m) : term234 x m.
Proof. exact (h1). Qed.
Lemma lem7587921 (x : nat) (m : nat) : (term234 x m) = ((term234 x m) = True).
Proof. exact (@lem7 (term234 x m)). Qed.
Lemma lem7587924 (i : nat) (m : nat) (c : nat -> real) (h1 : term236 m c) : term233 m c i.
Proof. exact (fun h0 : term234 i m => @lem7587812 c i m h1 h0). Qed.
Lemma lem7587925 (x : nat) (m : nat) (c : nat -> real) (h1 : term236 m c) : term233 m c x.
Proof. exact (@lem7587924 x m c h1). Qed.
Lemma lem7587927 (x : nat) (m : nat) (h1 : term234 x m) : (term234 x m) = True.
Proof. exact (EQ_MP (@lem7587921 x m) (@lem7587920 x m h1)). Qed.
Lemma lem7587928 (x : nat) (m : nat) (h1 : term234 x m) : True = (term234 x m).
Proof. exact (SYM (@lem7587927 x m h1)). Qed.
Lemma lem7587929 (x : nat) (m : nat) (h1 : term234 x m) : term234 x m.
Proof. exact (EQ_MP (@lem7587928 x m h1) (@lem0)). Qed.
Lemma lem7587930 (c : nat -> real) (x : nat) (m : nat) (h1 : term236 m c) (h2 : term234 x m) : (c x) = term2.
Proof. exact (@lem7587925 x m c h1 (@lem7587929 x m h2)). Qed.
Lemma lem7587931 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7587932 (c : nat -> real) (x : nat) (m : nat) (h1 : term236 m c) (h2 : term234 x m) : (term270 c x) = term271.
Proof. exact (MK_COMB (@lem7587931) (@lem7587930 c x m h1 h2)). Qed.
Lemma lem7587933 (x : real) (x' : nat) : (real_pow x x') = (real_pow x x').
Proof. exact (eq_refl (real_pow x x')). Qed.
Lemma lem7587934 (x : real) (c : nat -> real) (x' : nat) (m : nat) (h1 : term236 m c) (h2 : term234 x' m) : (term247 c x x') = (term272 x x').
Proof. exact (MK_COMB (@lem7587932 c x' m h1 h2) (@lem7587933 x x')). Qed.
Lemma lem7587935 (x : real) (x' : nat) (m : nat) (c : nat -> real) (h1 : term236 m c) : term273 m c x x'.
Proof. exact (fun h0 : term234 x' m => @lem7587934 x c x' m h1 h0). Qed.
Lemma lem7587936 (x : real) (m : nat) (c : nat -> real) (h1 : term236 m c) : term274 m c x.
Proof. exact (fun x' : nat => @lem7587935 x x' m c h1). Qed.
Lemma lem7587938 (c : nat -> real) (x : real) (m : nat) (g : nat -> real) : term265 c x m g.
Proof. exact (EQ_MP (@lem7587918 c x m g) (@lem7587917 c x m g)). Qed.
Lemma lem7587939 (c : nat -> real) (m : nat) (x : real) : term275 c m x.
Proof. exact (@lem7587938 c x m (term276 x)). Qed.
Lemma lem7587940 (x : real) (x' : nat) : (term277 x x') = (term272 x x').
Proof. exact (eq_refl (term277 x x')). Qed.
Lemma lem7587941 (c : nat -> real) (x : real) (x' : nat) : (term249 c x x') = (term249 c x x').
Proof. exact (eq_refl (term249 c x x')). Qed.
Lemma lem7587942 (c : nat -> real) (x : real) (x' : nat) : ((term247 c x x') = (term277 x x')) = ((term247 c x x') = (term272 x x')).
Proof. exact (MK_COMB (@lem7587941 c x x') (@lem7587940 x x')). Qed.
Lemma lem7587943 (x : nat) (m : nat) : (term250 x m) = (term250 x m).
Proof. exact (eq_refl (term250 x m)). Qed.
Lemma lem7587944 (m : nat) (c : nat -> real) (x : real) (x' : nat) : (term278 m c x x') = (term273 m c x x').
Proof. exact (MK_COMB (@lem7587943 x' m) (@lem7587942 c x x')). Qed.
Lemma lem7587945 (m : nat) (c : nat -> real) (x : real) : (term279 m c x) = (term280 m c x).
Proof. exact (fun_ext (fun x' : nat => @lem7587944 m c x x')). Qed.
Lemma lem7587946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7587947 (m : nat) (c : nat -> real) (x : real) : (term281 m c x) = (term274 m c x).
Proof. exact (MK_COMB (@lem7587946) (@lem7587945 m c x)). Qed.
Lemma lem7587948 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7587949 (m : nat) (c : nat -> real) (x : real) : (term282 m c x) = (term283 m c x).
Proof. exact (MK_COMB (@lem7587948) (@lem7587947 m c x)). Qed.
Lemma lem7587950 (c : nat -> real) (m : nat) (x : real) : ((term197 m c x) = (term284 m x)) = ((term197 m c x) = (term284 m x)).
Proof. exact (eq_refl ((term197 m c x) = (term284 m x))). Qed.
Lemma lem7587951 (c : nat -> real) (m : nat) (x : real) : (term275 c m x) = (term285 c m x).
Proof. exact (MK_COMB (@lem7587949 m c x) (@lem7587950 c m x)). Qed.
Lemma lem7587952 (c : nat -> real) (m : nat) (x : real) : term285 c m x.
Proof. exact (EQ_MP (@lem7587951 c m x) (@lem7587939 c m x)). Qed.
Lemma lem7587953 (x : real) (m : nat) (c : nat -> real) (h1 : term236 m c) : (term197 m c x) = (term284 m x).
Proof. exact (@lem7587952 c m x (@lem7587936 x m c h1)). Qed.
Lemma lem7588069 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7588070 (x : real) (m : nat) (c : nat -> real) (h1 : term236 m c) : (term198 m c x) = (term286 m x).
Proof. exact (MK_COMB (@lem7588069) (@lem7587953 x m c h1)). Qed.
Lemma lem7588186 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7588187 (x : real) (m : nat) (c : nat -> real) (h1 : term236 m c) : ((term197 m c x) = term2) = ((term284 m x) = term2).
Proof. exact (MK_COMB (@lem7588070 x m c h1) (@lem7588186)). Qed.
Lemma lem7588305 (m : nat) (c : nat -> real) (h1 : term236 m c) : (term209 m c) = (term287 m).
Proof. exact (fun_ext (fun x : real => @lem7588187 x m c h1)). Qed.
Lemma lem7588423 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7588424 (m : nat) (c : nat -> real) (h1 : term236 m c) : (term210 m c) = (term288 m).
Proof. exact (MK_COMB (@lem7588423) (@lem7588305 m c h1)). Qed.
Lemma lem7588546 (c : nat -> real) (m : nat) : term289 c m.
Proof. exact (fun h0 : term236 m c => @lem7588424 m c h0). Qed.
Lemma lem7588547 (c : nat -> real) (m : nat) : term290 c m.
Proof. exact (@lem7587806 m c (term288 m)). Qed.
Lemma lem7588548 (c : nat -> real) (m : nat) : (term211 m c) = (term291 c m).
Proof. exact (@lem7588547 c m (@lem7588546 c m)). Qed.
Lemma lem7588884 (m : nat) (c : nat -> real) : (term291 c m) = (term211 m c).
Proof. exact (SYM (@lem7588548 c m)). Qed.
Lemma lem7588902 (x : real) : (term4 x) = term2.
Proof. exact (EQ_MP (@lem7587044 x) (@lem7587043 x)). Qed.
Lemma lem7588903 (x : real) (x' : nat) : (term272 x x') = term2.
Proof. exact (@lem7588902 (real_pow x x')). Qed.
Lemma lem7588904 (x : real) : (term276 x) = term292.
Proof. exact (fun_ext (fun x' : nat => @lem7588903 x x')). Qed.
Lemma lem7588905 (m : nat) : (term260 m) = (term260 m).
Proof. exact (eq_refl (term260 m)). Qed.
Lemma lem7588906 (x : real) (m : nat) : (term284 m x) = (term293 m).
Proof. exact (MK_COMB (@lem7588905 m) (@lem7588904 x)). Qed.
Lemma lem7588908 {A : Type'} (s : A -> Prop) : (term1 A s) = term2.
Proof. exact (EQ_MP (@lem7587041 A s) (@lem7587040 A s)). Qed.
Lemma lem7588909 (s : nat -> Prop) : (term294 s) = term2.
Proof. exact (@lem7588908 nat s). Qed.
Lemma lem7588910 (m : nat) : (term293 m) = term2.
Proof. exact (@lem7588909 (term245 m)). Qed.
Lemma lem7588911 (m : nat) (x : real) : (term284 m x) = term2.
Proof. exact (TRANS (@lem7588906 x m) (@lem7588910 m)). Qed.
Lemma lem7588912 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7588913 (m : nat) (x : real) : (term286 m x) = term177.
Proof. exact (MK_COMB (@lem7588912) (@lem7588911 m x)). Qed.
Lemma lem7588914 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem7588915 (m : nat) (x : real) : ((term284 m x) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem7588913 m x) (@lem7588914)). Qed.
Lemma lem7588917 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7588918 (x : real) : (x = x) = True.
Proof. exact (@lem7588917 real x). Qed.
Lemma lem7588919 : (term2 = term2) = True.
Proof. exact (@lem7588918 term2). Qed.
Lemma lem7588920 (m : nat) (x : real) : ((term284 m x) = term2) = True.
Proof. exact (TRANS (@lem7588915 m x) (@lem7588919)). Qed.
Lemma lem7588921 (m : nat) : (term287 m) = term147.
Proof. exact (fun_ext (fun x : real => @lem7588920 m x)). Qed.
Lemma lem7588922 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7588923 (m : nat) : (term288 m) = term148.
Proof. exact (MK_COMB (@lem7588922) (@lem7588921 m)). Qed.
Lemma lem7588925 {A : Type'} (t : Prop) : (term149 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7588926 (t : Prop) : (term150 t) = t.
Proof. exact (@lem7588925 real t). Qed.
Lemma lem7588927 : term148 = True.
Proof. exact (@lem7588926 True). Qed.
Lemma lem7588928 (m : nat) : (term288 m) = True.
Proof. exact (TRANS (@lem7588923 m) (@lem7588927)). Qed.
Lemma lem7588929 (m : nat) (c : nat -> real) : (term295 m c) = (term295 m c).
Proof. exact (eq_refl (term295 m c)). Qed.
Lemma lem7588930 (m : nat) (c : nat -> real) : (term291 c m) = (term296 m c).
Proof. exact (MK_COMB (@lem7588929 m c) (@lem7588928 m)). Qed.
Lemma lem7588932 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7588933 (m : nat) (c : nat -> real) : (term296 m c) = True.
Proof. exact (@lem7588932 (term236 m c)). Qed.
Lemma lem7588934 (c : nat -> real) (m : nat) : (term291 c m) = True.
Proof. exact (TRANS (@lem7588930 m c) (@lem7588933 m c)). Qed.
Lemma lem7588935 (c : nat -> real) (m : nat) : True = (term291 c m).
Proof. exact (SYM (@lem7588934 c m)). Qed.
Lemma lem7588936 (c : nat -> real) (m : nat) : term291 c m.
Proof. exact (EQ_MP (@lem7588935 c m) (@lem0)). Qed.
Lemma lem7588937 (m : nat) (c : nat -> real) : term211 m c.
Proof. exact (EQ_MP (@lem7588884 m c) (@lem7588936 c m)). Qed.
Lemma lem7588938 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : term161 p.
Proof. exact (EQ_MP (@lem7587675 p m c h1) (@lem7588937 m c)). Qed.
Lemma lem7588939 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : term160 p.
Proof. exact (EQ_MP (@lem7587503 p) (@lem7588938 p m c h1)). Qed.
Lemma lem7588940 (p : real -> real) : term158 p.
Proof. exact (EQ_MP (@lem7587497 p) (@lem7587589 p)). Qed.
Lemma lem7588941 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : term297 p.
Proof. exact (conj (@lem7588940 p) (@lem7588939 p m c h1)). Qed.
Lemma lem7588942 (p : real -> real) : (term297 p) = ((term98 p) = (term99 p)).
Proof. exact (@lem32 (term98 p) (term99 p)). Qed.
Lemma lem7588943 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term98 p) = (term99 p).
Proof. exact (EQ_MP (@lem7588942 p) (@lem7588941 p m c h1)). Qed.
Lemma lem7588944 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term157 p m c) = ((term98 p) = (term99 p)).
Proof. exact (prop_ext (fun h2 : term157 p m c => @lem7588943 p m c h1) (fun h2 : (term98 p) = (term99 p) => @lem7587491 p m c h1)). Qed.
Lemma lem7588945 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term157 p m c) : (term98 p) = (term99 p).
Proof. exact (EQ_MP (@lem7588944 p m c h1) (@lem7587491 p m c h1)). Qed.
Lemma lem7588946 (p : real -> real) (m : nat) (h1 : term156 p m) : (term98 p) = (term99 p).
Proof. exact (ex_elim (@lem7587490 p m h1) (fun c : nat -> real => fun h0 : term298 p m c => @lem7588945 p m c h0)). Qed.
Lemma lem7588947 (p : real -> real) (h1 : term42 p) : (term98 p) = (term99 p).
Proof. exact (ex_elim (@lem7587489 p h1) (fun m : nat => fun h0 : term299 p m => @lem7588946 p m h0)). Qed.
Lemma lem7588948 (p : real -> real) : term155 p.
Proof. exact (fun h0 : term42 p => @lem7588947 p h0). Qed.
Lemma lem7588949 (p : real -> real) : term97 p.
Proof. exact (EQ_MP (@lem7587488 p) (@lem7588948 p)). Qed.
Lemma lem7588954 : term87.
Proof. exact (fun p : real -> real => @lem7588949 p). Qed.
Lemma lem7588955 : term87 = term86.
Proof. exact (prop_ext (fun h1 : term87 => @lem7587449 h1) (fun h1 : term86 => @lem7588954)). Qed.
Lemma lem7588956 : term86.
Proof. exact (EQ_MP (@lem7588955) (@lem7588954)). Qed.
Lemma lem7588957 : term85.
Proof. exact (EQ_MP (@lem7587265) (@lem7588956)). Qed.
