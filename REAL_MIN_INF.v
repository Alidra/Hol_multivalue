Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MIN_INF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_RULES_spec.
Require Import IN_INSERT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_INSERT_EMPTY_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import REAL_INF_LE_FINITE_spec.
Require Import REAL_LE_INF_FINITE_spec.
Require Import REAL_LE_MIN_spec.
Require Import REAL_MIN_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339379_spec.
Require Import thm1339697_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem5285062 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5285063 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem5285064 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem5285063 A x) (@lem5285062 A x)). Qed.
Lemma lem5285065 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5285067 {A : Type'} (x : A) : term3 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5285068 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem5285069 {A : Type'} (x : A) : term4 A x.
Proof. exact (EQ_MP (@lem5285068 A x) (@lem5285067 A x)). Qed.
Lemma lem5285070 {A : Type'} (x : A) (y : A) : term5 A x y.
Proof. exact (@lem5285069 A x y). Qed.
Lemma lem5285071 {A : Type'} (y : A) (x : A) : (term5 A x y) = (term6 A y x).
Proof. exact (eq_refl (term5 A x y)). Qed.
Lemma lem5285072 {A : Type'} (y : A) (x : A) : term6 A y x.
Proof. exact (EQ_MP (@lem5285071 A y x) (@lem5285070 A x y)). Qed.
Lemma lem5285073 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term7 A y x s.
Proof. exact (@lem5285072 A y x s). Qed.
Lemma lem5285074 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term7 A y x s) = ((term8 A x y s) = (term9 A y x s)).
Proof. exact (eq_refl (term7 A y x s)). Qed.
Lemma lem5285078 (x : real) (y : real) (h1 : (term10 y x) = (x = y)) : (term10 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem5285079 (x : real) (y : real) (h1 : (term10 y x) = (x = y)) : (x = y) = (term10 y x).
Proof. exact (SYM (@lem5285078 x y h1)). Qed.
Lemma lem5285080 (y : real) (x : real) (h1 : (x = y) = (term10 y x)) : (x = y) = (term10 y x).
Proof. exact (h1). Qed.
Lemma lem5285081 (y : real) (x : real) (h1 : (x = y) = (term10 y x)) : (term10 y x) = (x = y).
Proof. exact (SYM (@lem5285080 y x h1)). Qed.
Lemma lem5285082 (y : real) (x : real) : ((term10 y x) = (x = y)) = ((x = y) = (term10 y x)).
Proof. exact (prop_ext (fun h1 : (term10 y x) = (x = y) => @lem5285079 x y h1) (fun h1 : (x = y) = (term10 y x) => @lem5285081 y x h1)). Qed.
Lemma lem5285083 (x : real) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem5285082 y x)). Qed.
Lemma lem5285084 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5285085 (x : real) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem5285084) (@lem5285083 x)). Qed.
Lemma lem5285086 : term15 = term16.
Proof. exact (fun_ext (fun x : real => @lem5285085 x)). Qed.
Lemma lem5285087 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5285088 : term17 = term18.
Proof. exact (MK_COMB (@lem5285087) (@lem5285086)). Qed.
Lemma lem5285089 : term18.
Proof. exact (EQ_MP (@lem5285088) (@lem1339379)). Qed.
Lemma lem5285090 (x : real) : term19 x.
Proof. exact (@lem1562409 x). Qed.
Lemma lem5285091 (x : real) : (term19 x) = (term20 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem5285092 (x : real) : term20 x.
Proof. exact (EQ_MP (@lem5285091 x) (@lem5285090 x)). Qed.
Lemma lem5285093 (x : real) (y : real) : term21 x y.
Proof. exact (@lem5285092 x y). Qed.
Lemma lem5285094 (x : real) (y : real) : (term21 x y) = (term22 x y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem5285095 (x : real) (y : real) : term22 x y.
Proof. exact (EQ_MP (@lem5285094 x y) (@lem5285093 x y)). Qed.
Lemma lem5285096 (x : real) (y : real) (z : real) : term23 x y z.
Proof. exact (@lem5285095 x y z). Qed.
Lemma lem5285097 (x : real) (z : real) (y : real) : (term23 x y z) = ((term24 z x y) = (term25 x z y)).
Proof. exact (eq_refl (term23 x y z)). Qed.
Lemma lem5285099 (x : real) : term26 x.
Proof. exact (@lem1568445 x). Qed.
Lemma lem5285100 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem5285101 (x : real) : term27 x.
Proof. exact (EQ_MP (@lem5285100 x) (@lem5285099 x)). Qed.
Lemma lem5285102 (x : real) (y : real) : term28 x y.
Proof. exact (@lem5285101 x y). Qed.
Lemma lem5285103 (x : real) (y : real) : (term28 x y) = (term29 x y).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem5285104 (x : real) (y : real) : term29 x y.
Proof. exact (EQ_MP (@lem5285103 x y) (@lem5285102 x y)). Qed.
Lemma lem5285105 (x : real) (y : real) (z : real) : term30 x y z.
Proof. exact (@lem5285104 x y z). Qed.
Lemma lem5285106 (x : real) (y : real) (z : real) : (term30 x y z) = ((term31 x y z) = (term32 x y z)).
Proof. exact (eq_refl (term30 x y z)). Qed.
Lemma lem5285108 {A : Type'} (x : A) : term33 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem5285109 {A : Type'} (x : A) : (term33 A x) = (term34 A x).
Proof. exact (eq_refl (term33 A x)). Qed.
Lemma lem5285110 {A : Type'} (x : A) : term34 A x.
Proof. exact (EQ_MP (@lem5285109 A x) (@lem5285108 A x)). Qed.
Lemma lem5285111 {A : Type'} (x : A) (s : A -> Prop) : term35 A x s.
Proof. exact (@lem5285110 A x s). Qed.
Lemma lem5285112 {A : Type'} (x : A) (s : A -> Prop) : (term35 A x s) = (term36 A x s).
Proof. exact (eq_refl (term35 A x s)). Qed.
Lemma lem5285113 {A : Type'} (x : A) (s : A -> Prop) : term36 A x s.
Proof. exact (EQ_MP (@lem5285112 A x s) (@lem5285111 A x s)). Qed.
Lemma lem5285114 {A : Type'} (x : A) (s : A -> Prop) : term37 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem5285127 {A : Type'} : term38 A.
Proof. exact (proj2 (@lem3197565 A)). Qed.
Lemma lem5285128 {A : Type'} (x : A) : term39 A x.
Proof. exact (@lem5285127 A x). Qed.
Lemma lem5285129 {A : Type'} (x : A) : (term39 A x) = (term40 A x).
Proof. exact (eq_refl (term39 A x)). Qed.
Lemma lem5285130 {A : Type'} (x : A) : term40 A x.
Proof. exact (EQ_MP (@lem5285129 A x) (@lem5285128 A x)). Qed.
Lemma lem5285131 {A : Type'} (x : A) (s : A -> Prop) : term41 A x s.
Proof. exact (@lem5285130 A x s). Qed.
Lemma lem5285132 {A : Type'} (x : A) (s : A -> Prop) : (term41 A x s) = (term42 A x s).
Proof. exact (eq_refl (term41 A x s)). Qed.
Lemma lem5285133 {A : Type'} (x : A) (s : A -> Prop) : term42 A x s.
Proof. exact (EQ_MP (@lem5285132 A x s) (@lem5285131 A x s)). Qed.
Lemma lem5285134 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5285135 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term43 A x s.
Proof. exact (@lem5285133 A x s (@lem5285134 A s h1)). Qed.
Lemma lem5285136 {A : Type'} (x : A) (s : A -> Prop) : (term43 A x s) = ((term43 A x s) = True).
Proof. exact (@lem7 (term43 A x s)). Qed.
Lemma lem5285137 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term43 A x s) = True.
Proof. exact (EQ_MP (@lem5285136 A x s) (@lem5285135 A x s h1)). Qed.
Lemma lem5285143 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem5285144 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem5285146 (s : real -> Prop) : term44 s.
Proof. exact (@lem5224798 s). Qed.
Lemma lem5285147 (s : real -> Prop) : (term44 s) = (term45 s).
Proof. exact (eq_refl (term44 s)). Qed.
Lemma lem5285148 (s : real -> Prop) : term45 s.
Proof. exact (EQ_MP (@lem5285147 s) (@lem5285146 s)). Qed.
Lemma lem5285149 (s : real -> Prop) (a : real) : term46 s a.
Proof. exact (@lem5285148 s a). Qed.
Lemma lem5285150 (s : real -> Prop) (a : real) : (term46 s a) = (term47 s a).
Proof. exact (eq_refl (term46 s a)). Qed.
Lemma lem5285151 (s : real -> Prop) (a : real) : term47 s a.
Proof. exact (EQ_MP (@lem5285150 s a) (@lem5285149 s a)). Qed.
Lemma lem5285152 (s : real -> Prop) (h1 : term48 s) : term48 s.
Proof. exact (h1). Qed.
Lemma lem5285153 (a : real) (s : real -> Prop) (h1 : term48 s) : (term49 a s) = (term50 s a).
Proof. exact (@lem5285151 s a (@lem5285152 s h1)). Qed.
Lemma lem5285159 (s : real -> Prop) : term51 s.
Proof. exact (@lem5227045 s). Qed.
Lemma lem5285160 (s : real -> Prop) : (term51 s) = (term52 s).
Proof. exact (eq_refl (term51 s)). Qed.
Lemma lem5285161 (s : real -> Prop) : term52 s.
Proof. exact (EQ_MP (@lem5285160 s) (@lem5285159 s)). Qed.
Lemma lem5285162 (s : real -> Prop) (a : real) : term53 s a.
Proof. exact (@lem5285161 s a). Qed.
Lemma lem5285163 (s : real -> Prop) (a : real) : (term53 s a) = (term54 s a).
Proof. exact (eq_refl (term53 s a)). Qed.
Lemma lem5285164 (s : real -> Prop) (a : real) : term54 s a.
Proof. exact (EQ_MP (@lem5285163 s a) (@lem5285162 s a)). Qed.
Lemma lem5285165 (s : real -> Prop) (h1 : term48 s) : term48 s.
Proof. exact (h1). Qed.
Lemma lem5285166 (a : real) (s : real -> Prop) (h1 : term48 s) : (term55 s a) = (term56 s a).
Proof. exact (@lem5285164 s a (@lem5285165 s h1)). Qed.
Lemma lem5285172 (x : real) : term57 x.
Proof. exact (@lem5285089 x). Qed.
Lemma lem5285173 (x : real) : (term57 x) = (term14 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem5285174 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem5285173 x) (@lem5285172 x)). Qed.
Lemma lem5285175 (x : real) (y : real) : term58 x y.
Proof. exact (@lem5285174 x y). Qed.
Lemma lem5285176 (y : real) (x : real) : (term58 x y) = ((x = y) = (term10 y x)).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem5285189 (y : real) (x : real) : (x = y) = (term10 y x).
Proof. exact (EQ_MP (@lem5285176 y x) (@lem5285175 x y)). Qed.
Lemma lem5285190 (x : real) (y : real) : ((real_min x y) = (term59 x y)) = (term60 x y).
Proof. exact (@lem5285189 (term59 x y) (real_min x y)). Qed.
Lemma lem5285194 (x : real) (y : real) (z : real) : (term31 x y z) = (term32 x y z).
Proof. exact (EQ_MP (@lem5285106 x y z) (@lem5285105 x y z)). Qed.
Lemma lem5285195 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (@lem5285194 x y (term59 x y)). Qed.
Lemma lem5285199 (s : real -> Prop) (a : real) : term47 s a.
Proof. exact (fun h0 : term48 s => @lem5285153 a s h0). Qed.
Lemma lem5285200 (y : real) (x : real) : term63 y x.
Proof. exact (@lem5285199 (term64 x y) x). Qed.
Lemma lem5285204 {A : Type'} (x : A) (s : A -> Prop) : term65 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5285137 A x s h0). Qed.
Lemma lem5285205 (x : real) (s : real -> Prop) : term66 x s.
Proof. exact (@lem5285204 real x s). Qed.
Lemma lem5285206 (x : real) (y : real) : term67 x y.
Proof. exact (@lem5285205 x (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5285208 {A : Type'} (x : A) (s : A -> Prop) : term65 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5285137 A x s h0). Qed.
Lemma lem5285209 (x : real) (s : real -> Prop) : term66 x s.
Proof. exact (@lem5285208 real x s). Qed.
Lemma lem5285210 (y : real) : term68 y.
Proof. exact (@lem5285209 y (@EMPTY real)). Qed.
Lemma lem5285212 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem5285144 A) (@lem5285143 A)). Qed.
Lemma lem5285213 : (@FINITE real (@EMPTY real)) = True.
Proof. exact (@lem5285212 real). Qed.
Lemma lem5285214 : True = (@FINITE real (@EMPTY real)).
Proof. exact (SYM (@lem5285213)). Qed.
Lemma lem5285215 : @FINITE real (@EMPTY real).
Proof. exact (EQ_MP (@lem5285214) (@lem0)). Qed.
Lemma lem5285216 (y : real) : (term69 y) = True.
Proof. exact (@lem5285210 y (@lem5285215)). Qed.
Lemma lem5285217 (y : real) : True = (term69 y).
Proof. exact (SYM (@lem5285216 y)). Qed.
Lemma lem5285218 (y : real) : term69 y.
Proof. exact (EQ_MP (@lem5285217 y) (@lem0)). Qed.
Lemma lem5285219 (x : real) (y : real) : (term70 x y) = True.
Proof. exact (@lem5285206 x y (@lem5285218 y)). Qed.
Lemma lem5285220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5285221 (x : real) (y : real) : (term71 x y) = (and True).
Proof. exact (MK_COMB (@lem5285220) (@lem5285219 x y)). Qed.
Lemma lem5285223 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5285114 A x s (@lem5285113 A x s)). Qed.
Lemma lem5285224 (x : real) (s : real -> Prop) : ((@INSERT real x s) = (@EMPTY real)) = False.
Proof. exact (@lem5285223 real x s). Qed.
Lemma lem5285225 (x : real) (y : real) : ((term64 x y) = (@EMPTY real)) = False.
Proof. exact (@lem5285224 x (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5285226 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5285227 (x : real) (y : real) : (term72 x y) = (~ False).
Proof. exact (MK_COMB (@lem5285226) (@lem5285225 x y)). Qed.
Lemma lem5285229 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5285230 (x : real) (y : real) : (term72 x y) = True.
Proof. exact (TRANS (@lem5285227 x y) (@lem5285229)). Qed.
Lemma lem5285231 (x : real) (y : real) : (term73 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem5285221 x y) (@lem5285230 x y)). Qed.
Lemma lem5285233 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5285234 : (True /\ True) = True.
Proof. exact (@lem5285233 True). Qed.
Lemma lem5285235 (x : real) (y : real) : (term73 x y) = True.
Proof. exact (TRANS (@lem5285231 x y) (@lem5285234)). Qed.
Lemma lem5285236 (x : real) (y : real) : True = (term73 x y).
Proof. exact (SYM (@lem5285235 x y)). Qed.
Lemma lem5285237 (x : real) (y : real) : term73 x y.
Proof. exact (EQ_MP (@lem5285236 x y) (@lem0)). Qed.
Lemma lem5285238 (y : real) (x : real) : (term74 x y) = (term75 y x).
Proof. exact (@lem5285200 y x (@lem5285237 x y)). Qed.
Lemma lem5285266 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5285267 (y : real) (x : real) : (term76 x y) = (term77 y x).
Proof. exact (MK_COMB (@lem5285266) (@lem5285238 y x)). Qed.
Lemma lem5285296 (s : real -> Prop) (a : real) : term47 s a.
Proof. exact (fun h0 : term48 s => @lem5285153 a s h0). Qed.
Lemma lem5285297 (x : real) (y : real) : term78 x y.
Proof. exact (@lem5285296 (term64 x y) y). Qed.
Lemma lem5285301 {A : Type'} (x : A) (s : A -> Prop) : term65 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5285137 A x s h0). Qed.
Lemma lem5285302 (x : real) (s : real -> Prop) : term66 x s.
Proof. exact (@lem5285301 real x s). Qed.
Lemma lem5285303 (x : real) (y : real) : term67 x y.
Proof. exact (@lem5285302 x (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5285305 {A : Type'} (x : A) (s : A -> Prop) : term65 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5285137 A x s h0). Qed.
Lemma lem5285306 (x : real) (s : real -> Prop) : term66 x s.
Proof. exact (@lem5285305 real x s). Qed.
Lemma lem5285307 (y : real) : term68 y.
Proof. exact (@lem5285306 y (@EMPTY real)). Qed.
Lemma lem5285309 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem5285144 A) (@lem5285143 A)). Qed.
Lemma lem5285310 : (@FINITE real (@EMPTY real)) = True.
Proof. exact (@lem5285309 real). Qed.
Lemma lem5285311 : True = (@FINITE real (@EMPTY real)).
Proof. exact (SYM (@lem5285310)). Qed.
Lemma lem5285312 : @FINITE real (@EMPTY real).
Proof. exact (EQ_MP (@lem5285311) (@lem0)). Qed.
Lemma lem5285313 (y : real) : (term69 y) = True.
Proof. exact (@lem5285307 y (@lem5285312)). Qed.
Lemma lem5285314 (y : real) : True = (term69 y).
Proof. exact (SYM (@lem5285313 y)). Qed.
Lemma lem5285315 (y : real) : term69 y.
Proof. exact (EQ_MP (@lem5285314 y) (@lem0)). Qed.
Lemma lem5285316 (x : real) (y : real) : (term70 x y) = True.
Proof. exact (@lem5285303 x y (@lem5285315 y)). Qed.
Lemma lem5285317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5285318 (x : real) (y : real) : (term71 x y) = (and True).
Proof. exact (MK_COMB (@lem5285317) (@lem5285316 x y)). Qed.
Lemma lem5285320 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5285114 A x s (@lem5285113 A x s)). Qed.
Lemma lem5285321 (x : real) (s : real -> Prop) : ((@INSERT real x s) = (@EMPTY real)) = False.
Proof. exact (@lem5285320 real x s). Qed.
Lemma lem5285322 (x : real) (y : real) : ((term64 x y) = (@EMPTY real)) = False.
Proof. exact (@lem5285321 x (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5285323 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5285324 (x : real) (y : real) : (term72 x y) = (~ False).
Proof. exact (MK_COMB (@lem5285323) (@lem5285322 x y)). Qed.
Lemma lem5285326 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5285327 (x : real) (y : real) : (term72 x y) = True.
Proof. exact (TRANS (@lem5285324 x y) (@lem5285326)). Qed.
Lemma lem5285328 (x : real) (y : real) : (term73 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem5285318 x y) (@lem5285327 x y)). Qed.
Lemma lem5285330 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5285331 : (True /\ True) = True.
Proof. exact (@lem5285330 True). Qed.
Lemma lem5285332 (x : real) (y : real) : (term73 x y) = True.
Proof. exact (TRANS (@lem5285328 x y) (@lem5285331)). Qed.
Lemma lem5285333 (x : real) (y : real) : True = (term73 x y).
Proof. exact (SYM (@lem5285332 x y)). Qed.
Lemma lem5285334 (x : real) (y : real) : term73 x y.
Proof. exact (EQ_MP (@lem5285333 x y) (@lem0)). Qed.
Lemma lem5285335 (x : real) (y : real) : (term79 x y) = (term80 x y).
Proof. exact (@lem5285297 x y (@lem5285334 x y)). Qed.
Lemma lem5285363 (x : real) (y : real) : (term62 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem5285267 y x) (@lem5285335 x y)). Qed.
Lemma lem5285420 (x : real) (y : real) : (term61 x y) = (term81 x y).
Proof. exact (TRANS (@lem5285195 x y) (@lem5285363 x y)). Qed.
Lemma lem5285421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5285422 (x : real) (y : real) : (term82 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem5285421) (@lem5285420 x y)). Qed.
Lemma lem5285480 (s : real -> Prop) (a : real) : term54 s a.
Proof. exact (fun h0 : term48 s => @lem5285166 a s h0). Qed.
Lemma lem5285481 (x : real) (y : real) : term84 x y.
Proof. exact (@lem5285480 (term64 x y) (real_min x y)). Qed.
Lemma lem5285485 {A : Type'} (x : A) (s : A -> Prop) : term65 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5285137 A x s h0). Qed.
Lemma lem5285486 (x : real) (s : real -> Prop) : term66 x s.
Proof. exact (@lem5285485 real x s). Qed.
Lemma lem5285487 (x : real) (y : real) : term67 x y.
Proof. exact (@lem5285486 x (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5285489 {A : Type'} (x : A) (s : A -> Prop) : term65 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5285137 A x s h0). Qed.
Lemma lem5285490 (x : real) (s : real -> Prop) : term66 x s.
Proof. exact (@lem5285489 real x s). Qed.
Lemma lem5285491 (y : real) : term68 y.
Proof. exact (@lem5285490 y (@EMPTY real)). Qed.
Lemma lem5285493 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem5285144 A) (@lem5285143 A)). Qed.
Lemma lem5285494 : (@FINITE real (@EMPTY real)) = True.
Proof. exact (@lem5285493 real). Qed.
Lemma lem5285495 : True = (@FINITE real (@EMPTY real)).
Proof. exact (SYM (@lem5285494)). Qed.
Lemma lem5285496 : @FINITE real (@EMPTY real).
Proof. exact (EQ_MP (@lem5285495) (@lem0)). Qed.
Lemma lem5285497 (y : real) : (term69 y) = True.
Proof. exact (@lem5285491 y (@lem5285496)). Qed.
Lemma lem5285498 (y : real) : True = (term69 y).
Proof. exact (SYM (@lem5285497 y)). Qed.
Lemma lem5285499 (y : real) : term69 y.
Proof. exact (EQ_MP (@lem5285498 y) (@lem0)). Qed.
Lemma lem5285500 (x : real) (y : real) : (term70 x y) = True.
Proof. exact (@lem5285487 x y (@lem5285499 y)). Qed.
Lemma lem5285501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5285502 (x : real) (y : real) : (term71 x y) = (and True).
Proof. exact (MK_COMB (@lem5285501) (@lem5285500 x y)). Qed.
Lemma lem5285504 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5285114 A x s (@lem5285113 A x s)). Qed.
Lemma lem5285505 (x : real) (s : real -> Prop) : ((@INSERT real x s) = (@EMPTY real)) = False.
Proof. exact (@lem5285504 real x s). Qed.
Lemma lem5285506 (x : real) (y : real) : ((term64 x y) = (@EMPTY real)) = False.
Proof. exact (@lem5285505 x (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5285507 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5285508 (x : real) (y : real) : (term72 x y) = (~ False).
Proof. exact (MK_COMB (@lem5285507) (@lem5285506 x y)). Qed.
Lemma lem5285510 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5285511 (x : real) (y : real) : (term72 x y) = True.
Proof. exact (TRANS (@lem5285508 x y) (@lem5285510)). Qed.
Lemma lem5285512 (x : real) (y : real) : (term73 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem5285502 x y) (@lem5285511 x y)). Qed.
Lemma lem5285514 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5285515 : (True /\ True) = True.
Proof. exact (@lem5285514 True). Qed.
Lemma lem5285516 (x : real) (y : real) : (term73 x y) = True.
Proof. exact (TRANS (@lem5285512 x y) (@lem5285515)). Qed.
Lemma lem5285517 (x : real) (y : real) : True = (term73 x y).
Proof. exact (SYM (@lem5285516 x y)). Qed.
Lemma lem5285518 (x : real) (y : real) : term73 x y.
Proof. exact (EQ_MP (@lem5285517 x y) (@lem0)). Qed.
Lemma lem5285519 (x : real) (y : real) : (term85 x y) = (term86 x y).
Proof. exact (@lem5285481 x y (@lem5285518 x y)). Qed.
Lemma lem5285527 (x : real) (z : real) (y : real) : (term24 z x y) = (term25 x z y).
Proof. exact (EQ_MP (@lem5285097 x z y) (@lem5285096 x y z)). Qed.
Lemma lem5285528 (x : real) (x' : real) (y : real) : (term24 x' x y) = (term25 x x' y).
Proof. exact (@lem5285527 x x' y). Qed.
Lemma lem5285531 (x' : real) (x : real) (y : real) : (term87 x' x y) = (term87 x' x y).
Proof. exact (eq_refl (term87 x' x y)). Qed.
Lemma lem5285532 (x : real) (x' : real) (y : real) : (term88 x' x y) = (term89 x x' y).
Proof. exact (MK_COMB (@lem5285531 x' x y) (@lem5285528 x x' y)). Qed.
Lemma lem5285537 (x : real) (y : real) : (term90 x y) = (term91 x y).
Proof. exact (fun_ext (fun x' : real => @lem5285532 x x' y)). Qed.
Lemma lem5285542 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5285543 (x : real) (y : real) : (term86 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem5285542) (@lem5285537 x y)). Qed.
Lemma lem5285552 (x : real) (y : real) : (term85 x y) = (term92 x y).
Proof. exact (TRANS (@lem5285519 x y) (@lem5285543 x y)). Qed.
Lemma lem5285553 (x : real) (y : real) : (term60 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem5285422 x y) (@lem5285552 x y)). Qed.
Lemma lem5285620 (x : real) (y : real) : ((real_min x y) = (term59 x y)) = (term93 x y).
Proof. exact (TRANS (@lem5285190 x y) (@lem5285553 x y)). Qed.
Lemma lem5285621 (x : real) : (term94 x) = (term95 x).
Proof. exact (fun_ext (fun y : real => @lem5285620 x y)). Qed.
Lemma lem5285688 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5285689 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem5285688) (@lem5285621 x)). Qed.
Lemma lem5285760 : term98 = term99.
Proof. exact (fun_ext (fun x : real => @lem5285689 x)). Qed.
Lemma lem5285831 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5285832 : term100 = term101.
Proof. exact (MK_COMB (@lem5285831) (@lem5285760)). Qed.
Lemma lem5285907 : term101 = term100.
Proof. exact (SYM (@lem5285832)). Qed.
Lemma lem5285927 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem5285074 A y x s) (@lem5285073 A y x s)). Qed.
Lemma lem5285928 (y : real) (x : real) (s : real -> Prop) : (term102 x y s) = (term103 y x s).
Proof. exact (@lem5285927 real y x s). Qed.
Lemma lem5285929 (x : real) (x' : real) (y : real) : (term104 x' x y) = (term105 x x' y).
Proof. exact (@lem5285928 x x' (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5285935 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem5285074 A y x s) (@lem5285073 A y x s)). Qed.
Lemma lem5285936 (y : real) (x : real) (s : real -> Prop) : (term102 x y s) = (term103 y x s).
Proof. exact (@lem5285935 real y x s). Qed.
Lemma lem5285937 (y : real) (x' : real) : (term106 x' y) = (term107 y x').
Proof. exact (@lem5285936 y x' (@EMPTY real)). Qed.
Lemma lem5285943 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5285065 A x (@lem5285064 A x)). Qed.
Lemma lem5285944 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5285943 real x). Qed.
Lemma lem5285945 (x' : real) : (@IN real x' (@EMPTY real)) = False.
Proof. exact (@lem5285944 x'). Qed.
Lemma lem5285946 (x' : real) (y : real) : (term108 x' y) = (term108 x' y).
Proof. exact (eq_refl (term108 x' y)). Qed.
Lemma lem5285947 (x' : real) (y : real) : (term107 y x') = (term109 x' y).
Proof. exact (MK_COMB (@lem5285946 x' y) (@lem5285945 x')). Qed.
Lemma lem5285949 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5285950 (x' : real) (y : real) : (term109 x' y) = (x' = y).
Proof. exact (@lem5285949 (x' = y)). Qed.
Lemma lem5285953 (x' : real) (y : real) : (term107 y x') = (x' = y).
Proof. exact (TRANS (@lem5285947 x' y) (@lem5285950 x' y)). Qed.
Lemma lem5285954 (x' : real) (y : real) : (term106 x' y) = (x' = y).
Proof. exact (TRANS (@lem5285937 y x') (@lem5285953 x' y)). Qed.
Lemma lem5285955 (x' : real) (x : real) : (term108 x' x) = (term108 x' x).
Proof. exact (eq_refl (term108 x' x)). Qed.
Lemma lem5285956 (x : real) (x' : real) (y : real) : (term105 x x' y) = (term110 x x' y).
Proof. exact (MK_COMB (@lem5285955 x' x) (@lem5285954 x' y)). Qed.
Lemma lem5285959 (x : real) (x' : real) (y : real) : (term104 x' x y) = (term110 x x' y).
Proof. exact (TRANS (@lem5285929 x x' y) (@lem5285956 x x' y)). Qed.
Lemma lem5285960 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5285961 (x : real) (x' : real) (y : real) : (term111 x' x y) = (term112 x x' y).
Proof. exact (MK_COMB (@lem5285960) (@lem5285959 x x' y)). Qed.
Lemma lem5285962 (x : real) (x' : real) : (real_le x x') = (real_le x x').
Proof. exact (eq_refl (real_le x x')). Qed.
Lemma lem5285963 (y : real) (x : real) (x' : real) : (term113 y x x') = (term114 y x x').
Proof. exact (MK_COMB (@lem5285961 x x' y) (@lem5285962 x x')). Qed.
Lemma lem5285966 (y : real) (x : real) : (term115 y x) = (term116 y x).
Proof. exact (fun_ext (fun x' : real => @lem5285963 y x x')). Qed.
Lemma lem5285967 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5285968 (y : real) (x : real) : (term75 y x) = (term117 y x).
Proof. exact (MK_COMB (@lem5285967) (@lem5285966 y x)). Qed.
Lemma lem5285973 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5285974 (y : real) (x : real) : (term77 y x) = (term118 y x).
Proof. exact (MK_COMB (@lem5285973) (@lem5285968 y x)). Qed.
Lemma lem5285982 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem5285074 A y x s) (@lem5285073 A y x s)). Qed.
Lemma lem5285983 (y : real) (x : real) (s : real -> Prop) : (term102 x y s) = (term103 y x s).
Proof. exact (@lem5285982 real y x s). Qed.
Lemma lem5285984 (x : real) (x' : real) (y : real) : (term104 x' x y) = (term105 x x' y).
Proof. exact (@lem5285983 x x' (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5285990 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem5285074 A y x s) (@lem5285073 A y x s)). Qed.
Lemma lem5285991 (y : real) (x : real) (s : real -> Prop) : (term102 x y s) = (term103 y x s).
Proof. exact (@lem5285990 real y x s). Qed.
Lemma lem5285992 (y : real) (x' : real) : (term106 x' y) = (term107 y x').
Proof. exact (@lem5285991 y x' (@EMPTY real)). Qed.
Lemma lem5285998 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5285065 A x (@lem5285064 A x)). Qed.
Lemma lem5285999 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5285998 real x). Qed.
Lemma lem5286000 (x' : real) : (@IN real x' (@EMPTY real)) = False.
Proof. exact (@lem5285999 x'). Qed.
Lemma lem5286001 (x' : real) (y : real) : (term108 x' y) = (term108 x' y).
Proof. exact (eq_refl (term108 x' y)). Qed.
Lemma lem5286002 (x' : real) (y : real) : (term107 y x') = (term109 x' y).
Proof. exact (MK_COMB (@lem5286001 x' y) (@lem5286000 x')). Qed.
Lemma lem5286004 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5286005 (x' : real) (y : real) : (term109 x' y) = (x' = y).
Proof. exact (@lem5286004 (x' = y)). Qed.
Lemma lem5286008 (x' : real) (y : real) : (term107 y x') = (x' = y).
Proof. exact (TRANS (@lem5286002 x' y) (@lem5286005 x' y)). Qed.
Lemma lem5286009 (x' : real) (y : real) : (term106 x' y) = (x' = y).
Proof. exact (TRANS (@lem5285992 y x') (@lem5286008 x' y)). Qed.
Lemma lem5286010 (x' : real) (x : real) : (term108 x' x) = (term108 x' x).
Proof. exact (eq_refl (term108 x' x)). Qed.
Lemma lem5286011 (x : real) (x' : real) (y : real) : (term105 x x' y) = (term110 x x' y).
Proof. exact (MK_COMB (@lem5286010 x' x) (@lem5286009 x' y)). Qed.
Lemma lem5286014 (x : real) (x' : real) (y : real) : (term104 x' x y) = (term110 x x' y).
Proof. exact (TRANS (@lem5285984 x x' y) (@lem5286011 x x' y)). Qed.
Lemma lem5286015 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5286016 (x : real) (x' : real) (y : real) : (term111 x' x y) = (term112 x x' y).
Proof. exact (MK_COMB (@lem5286015) (@lem5286014 x x' y)). Qed.
Lemma lem5286017 (y : real) (x' : real) : (real_le y x') = (real_le y x').
Proof. exact (eq_refl (real_le y x')). Qed.
Lemma lem5286018 (x : real) (y : real) (x' : real) : (term119 x y x') = (term120 x y x').
Proof. exact (MK_COMB (@lem5286016 x x' y) (@lem5286017 y x')). Qed.
Lemma lem5286021 (x : real) (y : real) : (term121 x y) = (term122 x y).
Proof. exact (fun_ext (fun x' : real => @lem5286018 x y x')). Qed.
Lemma lem5286022 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286023 (x : real) (y : real) : (term80 x y) = (term123 x y).
Proof. exact (MK_COMB (@lem5286022) (@lem5286021 x y)). Qed.
Lemma lem5286028 (x : real) (y : real) : (term81 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem5285974 y x) (@lem5286023 x y)). Qed.
Lemma lem5286031 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5286032 (x : real) (y : real) : (term83 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem5286031) (@lem5286028 x y)). Qed.
Lemma lem5286040 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem5285074 A y x s) (@lem5285073 A y x s)). Qed.
Lemma lem5286041 (y : real) (x : real) (s : real -> Prop) : (term102 x y s) = (term103 y x s).
Proof. exact (@lem5286040 real y x s). Qed.
Lemma lem5286042 (x : real) (x' : real) (y : real) : (term104 x' x y) = (term105 x x' y).
Proof. exact (@lem5286041 x x' (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5286048 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem5285074 A y x s) (@lem5285073 A y x s)). Qed.
Lemma lem5286049 (y : real) (x : real) (s : real -> Prop) : (term102 x y s) = (term103 y x s).
Proof. exact (@lem5286048 real y x s). Qed.
Lemma lem5286050 (y : real) (x' : real) : (term106 x' y) = (term107 y x').
Proof. exact (@lem5286049 y x' (@EMPTY real)). Qed.
Lemma lem5286056 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5285065 A x (@lem5285064 A x)). Qed.
Lemma lem5286057 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5286056 real x). Qed.
Lemma lem5286058 (x' : real) : (@IN real x' (@EMPTY real)) = False.
Proof. exact (@lem5286057 x'). Qed.
Lemma lem5286059 (x' : real) (y : real) : (term108 x' y) = (term108 x' y).
Proof. exact (eq_refl (term108 x' y)). Qed.
Lemma lem5286060 (x' : real) (y : real) : (term107 y x') = (term109 x' y).
Proof. exact (MK_COMB (@lem5286059 x' y) (@lem5286058 x')). Qed.
Lemma lem5286062 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5286063 (x' : real) (y : real) : (term109 x' y) = (x' = y).
Proof. exact (@lem5286062 (x' = y)). Qed.
Lemma lem5286066 (x' : real) (y : real) : (term107 y x') = (x' = y).
Proof. exact (TRANS (@lem5286060 x' y) (@lem5286063 x' y)). Qed.
Lemma lem5286067 (x' : real) (y : real) : (term106 x' y) = (x' = y).
Proof. exact (TRANS (@lem5286050 y x') (@lem5286066 x' y)). Qed.
Lemma lem5286068 (x' : real) (x : real) : (term108 x' x) = (term108 x' x).
Proof. exact (eq_refl (term108 x' x)). Qed.
Lemma lem5286069 (x : real) (x' : real) (y : real) : (term105 x x' y) = (term110 x x' y).
Proof. exact (MK_COMB (@lem5286068 x' x) (@lem5286067 x' y)). Qed.
Lemma lem5286072 (x : real) (x' : real) (y : real) : (term104 x' x y) = (term110 x x' y).
Proof. exact (TRANS (@lem5286042 x x' y) (@lem5286069 x x' y)). Qed.
Lemma lem5286073 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5286074 (x : real) (x' : real) (y : real) : (term87 x' x y) = (term126 x x' y).
Proof. exact (MK_COMB (@lem5286073) (@lem5286072 x x' y)). Qed.
Lemma lem5286077 (x : real) (x' : real) (y : real) : (term25 x x' y) = (term25 x x' y).
Proof. exact (eq_refl (term25 x x' y)). Qed.
Lemma lem5286078 (x : real) (x' : real) (y : real) : (term89 x x' y) = (term127 x x' y).
Proof. exact (MK_COMB (@lem5286074 x x' y) (@lem5286077 x x' y)). Qed.
Lemma lem5286081 (x : real) (y : real) : (term91 x y) = (term128 x y).
Proof. exact (fun_ext (fun x' : real => @lem5286078 x x' y)). Qed.
Lemma lem5286082 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5286083 (x : real) (y : real) : (term92 x y) = (term129 x y).
Proof. exact (MK_COMB (@lem5286082) (@lem5286081 x y)). Qed.
Lemma lem5286088 (x : real) (y : real) : (term93 x y) = (term130 x y).
Proof. exact (MK_COMB (@lem5286032 x y) (@lem5286083 x y)). Qed.
Lemma lem5286091 (x : real) : (term95 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem5286088 x y)). Qed.
Lemma lem5286092 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286093 (x : real) : (term97 x) = (term132 x).
Proof. exact (MK_COMB (@lem5286092) (@lem5286091 x)). Qed.
Lemma lem5286098 : term99 = term133.
Proof. exact (fun_ext (fun x : real => @lem5286093 x)). Qed.
Lemma lem5286099 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286100 : term101 = term134.
Proof. exact (MK_COMB (@lem5286099) (@lem5286098)). Qed.
Lemma lem5286105 : term134 = term101.
Proof. exact (SYM (@lem5286100)). Qed.
Lemma lem5286107 (p : Prop) : p = (term135 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5286108 : term134 = term136.
Proof. exact (@lem5286107 term134). Qed.
Lemma lem5286109 : term136 = term134.
Proof. exact (SYM (@lem5286108)). Qed.
Lemma lem5286110 (h1 : term137) : term137.
Proof. exact (h1). Qed.
Lemma lem5286113 (h1 : term138) : term138.
Proof. exact (h1). Qed.
Lemma lem5286114 : term139.
Proof. exact (fun h0 : term138 => @lem5286113 h0). Qed.
Lemma lem5286115 (h1 : term139) : term139.
Proof. exact (h1). Qed.
Lemma lem5286116 (h1 : term138) : term138.
Proof. exact (h1). Qed.
Lemma lem5286117 (h1 : term138) (h2 : term139) : term138.
Proof. exact (@lem5286115 h2 (@lem5286116 h1)). Qed.
Lemma lem5286118 (h1 : term138) : term140.
Proof. exact (fun h0 : term139 => @lem5286117 h1 h0). Qed.
Lemma lem5286119 (h1 : term139) : term139.
Proof. exact (h1). Qed.
Lemma lem5286120 (h1 : term138) (h2 : term139) : term138.
Proof. exact (@lem5286118 h1 (@lem5286119 h2)). Qed.
Lemma lem5286121 (h1 : term139) : term139.
Proof. exact (fun h0 : term138 => @lem5286120 h0 h1). Qed.
Lemma lem5286122 : term141.
Proof. exact (fun h0 : term139 => @lem5286121 h0). Qed.
Lemma lem5286125 : term139.
Proof. exact (@lem5286122 (@lem5286114)). Qed.
Lemma lem5286133 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem5286134 (P : real -> Prop) (Q : real -> Prop) : (term144 P Q) = (term145 P Q).
Proof. exact (@lem5286133 real P Q). Qed.
Lemma lem5286135 (x : real) : (term146 x) = (term147 x).
Proof. exact (@lem5286134 (term148 x) (term149 x)). Qed.
Lemma lem5286136 (x : real) (y : real) : (term150 x y) = (term124 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem5286137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5286138 (x : real) (y : real) : (term151 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem5286137) (@lem5286136 x y)). Qed.
Lemma lem5286139 (x : real) (y : real) : (term152 x y) = (term129 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem5286140 (x : real) (y : real) : (term153 x y) = (term130 x y).
Proof. exact (MK_COMB (@lem5286138 x y) (@lem5286139 x y)). Qed.
Lemma lem5286141 (x : real) : (term154 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem5286140 x y)). Qed.
Lemma lem5286142 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286143 (x : real) : (term146 x) = (term132 x).
Proof. exact (MK_COMB (@lem5286142) (@lem5286141 x)). Qed.
Lemma lem5286144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5286145 (x : real) : (term155 x) = (term156 x).
Proof. exact (MK_COMB (@lem5286144) (@lem5286143 x)). Qed.
Lemma lem5286146 (x : real) (y : real) : (term150 x y) = (term124 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem5286147 (x : real) : (term157 x) = (term148 x).
Proof. exact (fun_ext (fun y : real => @lem5286146 x y)). Qed.
Lemma lem5286148 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286149 (x : real) : (term158 x) = (term159 x).
Proof. exact (MK_COMB (@lem5286148) (@lem5286147 x)). Qed.
Lemma lem5286150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5286151 (x : real) : (term160 x) = (term161 x).
Proof. exact (MK_COMB (@lem5286150) (@lem5286149 x)). Qed.
Lemma lem5286152 (x : real) (y : real) : (term152 x y) = (term129 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem5286153 (x : real) : (term162 x) = (term149 x).
Proof. exact (fun_ext (fun y : real => @lem5286152 x y)). Qed.
Lemma lem5286154 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286155 (x : real) : (term163 x) = (term164 x).
Proof. exact (MK_COMB (@lem5286154) (@lem5286153 x)). Qed.
Lemma lem5286156 (x : real) : (term147 x) = (term165 x).
Proof. exact (MK_COMB (@lem5286151 x) (@lem5286155 x)). Qed.
Lemma lem5286157 (x : real) : ((term146 x) = (term147 x)) = ((term132 x) = (term165 x)).
Proof. exact (MK_COMB (@lem5286145 x) (@lem5286156 x)). Qed.
Lemma lem5286158 (x : real) : (term132 x) = (term165 x).
Proof. exact (EQ_MP (@lem5286157 x) (@lem5286135 x)). Qed.
Lemma lem5286285 : term133 = term166.
Proof. exact (fun_ext (fun x : real => @lem5286158 x)). Qed.
Lemma lem5286286 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286287 : term134 = term167.
Proof. exact (MK_COMB (@lem5286286) (@lem5286285)). Qed.
Lemma lem5286289 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem5286290 (P : real -> Prop) (Q : real -> Prop) : (term144 P Q) = (term145 P Q).
Proof. exact (@lem5286289 real P Q). Qed.
Lemma lem5286291 : term168 = term169.
Proof. exact (@lem5286290 term170 term171). Qed.
Lemma lem5286292 (x : real) : (term172 x) = (term159 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem5286293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5286294 (x : real) : (term173 x) = (term161 x).
Proof. exact (MK_COMB (@lem5286293) (@lem5286292 x)). Qed.
Lemma lem5286295 (x : real) : (term174 x) = (term164 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem5286296 (x : real) : (term175 x) = (term165 x).
Proof. exact (MK_COMB (@lem5286294 x) (@lem5286295 x)). Qed.
Lemma lem5286297 : term176 = term166.
Proof. exact (fun_ext (fun x : real => @lem5286296 x)). Qed.
Lemma lem5286298 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286299 : term168 = term167.
Proof. exact (MK_COMB (@lem5286298) (@lem5286297)). Qed.
Lemma lem5286300 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5286301 : term177 = term178.
Proof. exact (MK_COMB (@lem5286300) (@lem5286299)). Qed.
Lemma lem5286302 (x : real) : (term172 x) = (term159 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem5286303 : term179 = term170.
Proof. exact (fun_ext (fun x : real => @lem5286302 x)). Qed.
Lemma lem5286304 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286305 : term180 = term181.
Proof. exact (MK_COMB (@lem5286304) (@lem5286303)). Qed.
Lemma lem5286306 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5286307 : term182 = term183.
Proof. exact (MK_COMB (@lem5286306) (@lem5286305)). Qed.
Lemma lem5286308 (x : real) : (term174 x) = (term164 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem5286309 : term184 = term171.
Proof. exact (fun_ext (fun x : real => @lem5286308 x)). Qed.
Lemma lem5286310 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286311 : term185 = term186.
Proof. exact (MK_COMB (@lem5286310) (@lem5286309)). Qed.
Lemma lem5286312 : term169 = term187.
Proof. exact (MK_COMB (@lem5286307) (@lem5286311)). Qed.
Lemma lem5286313 : (term168 = term169) = (term167 = term187).
Proof. exact (MK_COMB (@lem5286301) (@lem5286312)). Qed.
Lemma lem5286314 : term167 = term187.
Proof. exact (EQ_MP (@lem5286313) (@lem5286291)). Qed.
Lemma lem5286449 : term134 = term187.
Proof. exact (TRANS (@lem5286287) (@lem5286314)). Qed.
Lemma lem5286450 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5286451 : term137 = term188.
Proof. exact (MK_COMB (@lem5286450) (@lem5286449)). Qed.
Lemma lem5286452 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5286453 : term189 = term190.
Proof. exact (MK_COMB (@lem5286452) (@lem5286451)). Qed.
Lemma lem5286455 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5286456 : term191 = term192.
Proof. exact (@lem5286455 term193). Qed.
Lemma lem5286517 : term138 = term194.
Proof. exact (MK_COMB (@lem5286453) (@lem5286456)). Qed.
Lemma lem5286522 (y : real) (x : real) : (term195 y x) = (term195 y x).
Proof. exact (eq_refl (term195 y x)). Qed.
Lemma lem5286523 (x : real) : (term196 x) = (term196 x).
Proof. exact (fun_ext (fun y : real => @lem5286522 y x)). Qed.
Lemma lem5286524 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286525 (x : real) : (term197 x) = (term197 x).
Proof. exact (MK_COMB (@lem5286524) (@lem5286523 x)). Qed.
Lemma lem5286526 : term198 = term198.
Proof. exact (fun_ext (fun x : real => @lem5286525 x)). Qed.
Lemma lem5286527 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286528 : term193 = term193.
Proof. exact (MK_COMB (@lem5286527) (@lem5286526)). Qed.
Lemma lem5286529 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5286530 : term192 = term192.
Proof. exact (MK_COMB (@lem5286529) (@lem5286528)). Qed.
Lemma lem5286543 (x : real) (x' : real) (y : real) : (term127 x x' y) = (term127 x x' y).
Proof. exact (eq_refl (term127 x x' y)). Qed.
Lemma lem5286544 (x : real) (y : real) : (term128 x y) = (term128 x y).
Proof. exact (fun_ext (fun x' : real => @lem5286543 x x' y)). Qed.
Lemma lem5286545 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5286546 (x : real) (y : real) : (term129 x y) = (term129 x y).
Proof. exact (MK_COMB (@lem5286545) (@lem5286544 x y)). Qed.
Lemma lem5286547 (x : real) : (term149 x) = (term149 x).
Proof. exact (fun_ext (fun y : real => @lem5286546 x y)). Qed.
Lemma lem5286548 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286549 (x : real) : (term164 x) = (term164 x).
Proof. exact (MK_COMB (@lem5286548) (@lem5286547 x)). Qed.
Lemma lem5286550 : term171 = term171.
Proof. exact (fun_ext (fun x : real => @lem5286549 x)). Qed.
Lemma lem5286551 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286552 : term186 = term186.
Proof. exact (MK_COMB (@lem5286551) (@lem5286550)). Qed.
Lemma lem5286561 (x : real) (y : real) (x' : real) : (term120 x y x') = (term120 x y x').
Proof. exact (eq_refl (term120 x y x')). Qed.
Lemma lem5286562 (x : real) (y : real) : (term122 x y) = (term122 x y).
Proof. exact (fun_ext (fun x' : real => @lem5286561 x y x')). Qed.
Lemma lem5286563 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286564 (x : real) (y : real) : (term123 x y) = (term123 x y).
Proof. exact (MK_COMB (@lem5286563) (@lem5286562 x y)). Qed.
Lemma lem5286573 (y : real) (x : real) (x' : real) : (term114 y x x') = (term114 y x x').
Proof. exact (eq_refl (term114 y x x')). Qed.
Lemma lem5286574 (y : real) (x : real) : (term116 y x) = (term116 y x).
Proof. exact (fun_ext (fun x' : real => @lem5286573 y x x')). Qed.
Lemma lem5286575 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286576 (y : real) (x : real) : (term117 y x) = (term117 y x).
Proof. exact (MK_COMB (@lem5286575) (@lem5286574 y x)). Qed.
Lemma lem5286577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5286578 (y : real) (x : real) : (term118 y x) = (term118 y x).
Proof. exact (MK_COMB (@lem5286577) (@lem5286576 y x)). Qed.
Lemma lem5286579 (x : real) (y : real) : (term124 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem5286578 y x) (@lem5286564 x y)). Qed.
Lemma lem5286580 (x : real) : (term148 x) = (term148 x).
Proof. exact (fun_ext (fun y : real => @lem5286579 x y)). Qed.
Lemma lem5286581 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286582 (x : real) : (term159 x) = (term159 x).
Proof. exact (MK_COMB (@lem5286581) (@lem5286580 x)). Qed.
Lemma lem5286583 : term170 = term170.
Proof. exact (fun_ext (fun x : real => @lem5286582 x)). Qed.
Lemma lem5286584 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286585 : term181 = term181.
Proof. exact (MK_COMB (@lem5286584) (@lem5286583)). Qed.
Lemma lem5286586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5286587 : term183 = term183.
Proof. exact (MK_COMB (@lem5286586) (@lem5286585)). Qed.
Lemma lem5286588 : term187 = term187.
Proof. exact (MK_COMB (@lem5286587) (@lem5286552)). Qed.
Lemma lem5286589 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5286590 : term188 = term188.
Proof. exact (MK_COMB (@lem5286589) (@lem5286588)). Qed.
Lemma lem5286591 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5286592 : term190 = term190.
Proof. exact (MK_COMB (@lem5286591) (@lem5286590)). Qed.
Lemma lem5286593 : term194 = term194.
Proof. exact (MK_COMB (@lem5286592) (@lem5286530)). Qed.
Lemma lem5286672 : term138 = term194.
Proof. exact (TRANS (@lem5286517) (@lem5286593)). Qed.
Lemma lem5286673 : term194 = term138.
Proof. exact (SYM (@lem5286672)). Qed.
Lemma lem5286674 (h1 : term188) : term188.
Proof. exact (h1). Qed.
Lemma lem5286675 (h1 : term193) : term193.
Proof. exact (h1). Qed.
Lemma lem5286686 (y : real) (x : real) (x' : real) : (term199 y x x') = (term200 y x x').
Proof. exact (@lem17362 (term110 x x' y) (real_le x x')). Qed.
Lemma lem5286687 (P : real -> Prop) : (term201 P) = (term202 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5286688 (y : real) (x : real) : (term203 y x) = (term204 y x).
Proof. exact (@lem5286687 (term116 y x)). Qed.
Lemma lem5286689 (y : real) (x : real) (x' : real) : (term205 y x x') = (term114 y x x').
Proof. exact (eq_refl (term205 y x x')). Qed.
Lemma lem5286690 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5286691 (y : real) (x : real) (x' : real) : (term206 y x x') = (term199 y x x').
Proof. exact (MK_COMB (@lem5286690) (@lem5286689 y x x')). Qed.
Lemma lem5286692 (y : real) (x : real) (x' : real) : (term206 y x x') = (term200 y x x').
Proof. exact (TRANS (@lem5286691 y x x') (@lem5286686 y x x')). Qed.
Lemma lem5286693 (y : real) (x : real) : (term207 y x) = (term208 y x).
Proof. exact (fun_ext (fun x' : real => @lem5286692 y x x')). Qed.
Lemma lem5286694 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5286695 (y : real) (x : real) : (term204 y x) = (term209 y x).
Proof. exact (MK_COMB (@lem5286694) (@lem5286693 y x)). Qed.
Lemma lem5286696 (y : real) (x : real) : (term203 y x) = (term209 y x).
Proof. exact (TRANS (@lem5286688 y x) (@lem5286695 y x)). Qed.
Lemma lem5286707 (x : real) (y : real) (x' : real) : (term210 x y x') = (term211 x y x').
Proof. exact (@lem17362 (term110 x x' y) (real_le y x')). Qed.
Lemma lem5286708 (P : real -> Prop) : (term201 P) = (term202 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5286709 (x : real) (y : real) : (term212 x y) = (term213 x y).
Proof. exact (@lem5286708 (term122 x y)). Qed.
Lemma lem5286710 (x : real) (y : real) (x' : real) : (term214 x y x') = (term120 x y x').
Proof. exact (eq_refl (term214 x y x')). Qed.
Lemma lem5286711 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5286712 (x : real) (y : real) (x' : real) : (term215 x y x') = (term210 x y x').
Proof. exact (MK_COMB (@lem5286711) (@lem5286710 x y x')). Qed.
Lemma lem5286713 (x : real) (y : real) (x' : real) : (term215 x y x') = (term211 x y x').
Proof. exact (TRANS (@lem5286712 x y x') (@lem5286707 x y x')). Qed.
Lemma lem5286714 (x : real) (y : real) : (term216 x y) = (term217 x y).
Proof. exact (fun_ext (fun x' : real => @lem5286713 x y x')). Qed.
Lemma lem5286715 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5286716 (x : real) (y : real) : (term213 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem5286715) (@lem5286714 x y)). Qed.
Lemma lem5286717 (x : real) (y : real) : (term212 x y) = (term218 x y).
Proof. exact (TRANS (@lem5286709 x y) (@lem5286716 x y)). Qed.
Lemma lem5286718 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5286719 (y : real) (x : real) : (term219 y x) = (term220 y x).
Proof. exact (MK_COMB (@lem5286718) (@lem5286696 y x)). Qed.
Lemma lem5286720 (x : real) (y : real) : (term221 x y) = (term222 x y).
Proof. exact (MK_COMB (@lem5286719 y x) (@lem5286717 x y)). Qed.
Lemma lem5286721 (x : real) (y : real) : (term223 x y) = (term221 x y).
Proof. exact (@lem17160 (term117 y x) (term123 x y)). Qed.
Lemma lem5286722 (x : real) (y : real) : (term223 x y) = (term222 x y).
Proof. exact (TRANS (@lem5286721 x y) (@lem5286720 x y)). Qed.
Lemma lem5286723 (P : real -> Prop) : (term201 P) = (term202 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5286724 (x : real) : (term224 x) = (term225 x).
Proof. exact (@lem5286723 (term148 x)). Qed.
Lemma lem5286725 (x : real) (y : real) : (term150 x y) = (term124 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem5286726 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5286727 (x : real) (y : real) : (term226 x y) = (term223 x y).
Proof. exact (MK_COMB (@lem5286726) (@lem5286725 x y)). Qed.
Lemma lem5286728 (x : real) (y : real) : (term226 x y) = (term222 x y).
Proof. exact (TRANS (@lem5286727 x y) (@lem5286722 x y)). Qed.
Lemma lem5286729 (x : real) : (term227 x) = (term228 x).
Proof. exact (fun_ext (fun y : real => @lem5286728 x y)). Qed.
Lemma lem5286730 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5286731 (x : real) : (term225 x) = (term229 x).
Proof. exact (MK_COMB (@lem5286730) (@lem5286729 x)). Qed.
Lemma lem5286732 (x : real) : (term224 x) = (term229 x).
Proof. exact (TRANS (@lem5286724 x) (@lem5286731 x)). Qed.
Lemma lem5286733 (P : real -> Prop) : (term201 P) = (term202 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5286734 : term230 = term231.
Proof. exact (@lem5286733 term170). Qed.
Lemma lem5286735 (x : real) : (term172 x) = (term159 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem5286736 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5286737 (x : real) : (term232 x) = (term224 x).
Proof. exact (MK_COMB (@lem5286736) (@lem5286735 x)). Qed.
Lemma lem5286738 (x : real) : (term232 x) = (term229 x).
Proof. exact (TRANS (@lem5286737 x) (@lem5286732 x)). Qed.
Lemma lem5286739 : term233 = term234.
Proof. exact (fun_ext (fun x : real => @lem5286738 x)). Qed.
Lemma lem5286740 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5286741 : term231 = term235.
Proof. exact (MK_COMB (@lem5286740) (@lem5286739)). Qed.
Lemma lem5286742 : term230 = term235.
Proof. exact (TRANS (@lem5286734) (@lem5286741)). Qed.
Lemma lem5286749 (x : real) (x' : real) (y : real) : (term236 x x' y) = (term237 x x' y).
Proof. exact (@lem17160 (x' = x) (x' = y)). Qed.
Lemma lem5286756 (x : real) (x' : real) (y : real) : (term238 x x' y) = (term239 x x' y).
Proof. exact (@lem17045 (real_le x' x) (real_le x' y)). Qed.
Lemma lem5286757 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5286758 (x : real) (x' : real) (y : real) : (term240 x x' y) = (term241 x x' y).
Proof. exact (MK_COMB (@lem5286757) (@lem5286749 x x' y)). Qed.
Lemma lem5286759 (x : real) (x' : real) (y : real) : (term242 x x' y) = (term243 x x' y).
Proof. exact (MK_COMB (@lem5286758 x x' y) (@lem5286756 x x' y)). Qed.
Lemma lem5286760 (x : real) (x' : real) (y : real) : (term244 x x' y) = (term242 x x' y).
Proof. exact (@lem17045 (term110 x x' y) (term25 x x' y)). Qed.
Lemma lem5286761 (x : real) (x' : real) (y : real) : (term244 x x' y) = (term243 x x' y).
Proof. exact (TRANS (@lem5286760 x x' y) (@lem5286759 x x' y)). Qed.
Lemma lem5286762 (P : real -> Prop) : (term245 P) = (term246 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5286763 (x : real) (y : real) : (term247 x y) = (term248 x y).
Proof. exact (@lem5286762 (term128 x y)). Qed.
Lemma lem5286764 (x : real) (x' : real) (y : real) : (term249 x y x') = (term127 x x' y).
Proof. exact (eq_refl (term249 x y x')). Qed.
Lemma lem5286765 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5286766 (x : real) (x' : real) (y : real) : (term250 x y x') = (term244 x x' y).
Proof. exact (MK_COMB (@lem5286765) (@lem5286764 x x' y)). Qed.
Lemma lem5286767 (x : real) (x' : real) (y : real) : (term250 x y x') = (term243 x x' y).
Proof. exact (TRANS (@lem5286766 x x' y) (@lem5286761 x x' y)). Qed.
Lemma lem5286768 (x : real) (y : real) : (term251 x y) = (term252 x y).
Proof. exact (fun_ext (fun x' : real => @lem5286767 x x' y)). Qed.
Lemma lem5286769 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5286770 (x : real) (y : real) : (term248 x y) = (term253 x y).
Proof. exact (MK_COMB (@lem5286769) (@lem5286768 x y)). Qed.
Lemma lem5286771 (x : real) (y : real) : (term247 x y) = (term253 x y).
Proof. exact (TRANS (@lem5286763 x y) (@lem5286770 x y)). Qed.
Lemma lem5286772 (P : real -> Prop) : (term201 P) = (term202 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5286773 (x : real) : (term254 x) = (term255 x).
Proof. exact (@lem5286772 (term149 x)). Qed.
Lemma lem5286774 (x : real) (y : real) : (term152 x y) = (term129 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem5286775 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5286776 (x : real) (y : real) : (term256 x y) = (term247 x y).
Proof. exact (MK_COMB (@lem5286775) (@lem5286774 x y)). Qed.
Lemma lem5286777 (x : real) (y : real) : (term256 x y) = (term253 x y).
Proof. exact (TRANS (@lem5286776 x y) (@lem5286771 x y)). Qed.
Lemma lem5286778 (x : real) : (term257 x) = (term258 x).
Proof. exact (fun_ext (fun y : real => @lem5286777 x y)). Qed.
Lemma lem5286779 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5286780 (x : real) : (term255 x) = (term259 x).
Proof. exact (MK_COMB (@lem5286779) (@lem5286778 x)). Qed.
Lemma lem5286781 (x : real) : (term254 x) = (term259 x).
Proof. exact (TRANS (@lem5286773 x) (@lem5286780 x)). Qed.
Lemma lem5286782 (P : real -> Prop) : (term201 P) = (term202 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5286783 : term260 = term261.
Proof. exact (@lem5286782 term171). Qed.
Lemma lem5286784 (x : real) : (term174 x) = (term164 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem5286785 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5286786 (x : real) : (term262 x) = (term254 x).
Proof. exact (MK_COMB (@lem5286785) (@lem5286784 x)). Qed.
Lemma lem5286787 (x : real) : (term262 x) = (term259 x).
Proof. exact (TRANS (@lem5286786 x) (@lem5286781 x)). Qed.
Lemma lem5286788 : term263 = term264.
Proof. exact (fun_ext (fun x : real => @lem5286787 x)). Qed.
Lemma lem5286789 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5286790 : term261 = term265.
Proof. exact (MK_COMB (@lem5286789) (@lem5286788)). Qed.
Lemma lem5286791 : term260 = term265.
Proof. exact (TRANS (@lem5286783) (@lem5286790)). Qed.
Lemma lem5286792 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5286793 : term266 = term267.
Proof. exact (MK_COMB (@lem5286792) (@lem5286742)). Qed.
Lemma lem5286794 : term268 = term269.
Proof. exact (MK_COMB (@lem5286793) (@lem5286791)). Qed.
Lemma lem5286795 : term188 = term268.
Proof. exact (@lem17045 term181 term186). Qed.
Lemma lem5286796 : term188 = term269.
Proof. exact (TRANS (@lem5286795) (@lem5286794)). Qed.
Lemma lem5287003 {A : Type'} (P : A -> Prop) (Q : Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5287004 (P : real -> Prop) (Q : Prop) : (term272 P Q) = (term273 P Q).
Proof. exact (@lem5287003 real P Q). Qed.
Lemma lem5287005 (x : real) (y : real) : (term274 x y) = (term275 x y).
Proof. exact (@lem5287004 (term208 y x) (term218 x y)). Qed.
Lemma lem5287006 (y : real) (x : real) (x' : real) : (term276 y x x') = (term200 y x x').
Proof. exact (eq_refl (term276 y x x')). Qed.
Lemma lem5287007 (y : real) (x : real) : (term277 y x) = (term208 y x).
Proof. exact (fun_ext (fun x' : real => @lem5287006 y x x')). Qed.
Lemma lem5287008 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287009 (y : real) (x : real) : (term278 y x) = (term209 y x).
Proof. exact (MK_COMB (@lem5287008) (@lem5287007 y x)). Qed.
Lemma lem5287010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5287011 (y : real) (x : real) : (term279 y x) = (term220 y x).
Proof. exact (MK_COMB (@lem5287010) (@lem5287009 y x)). Qed.
Lemma lem5287012 (x : real) (y : real) : (term218 x y) = (term218 x y).
Proof. exact (eq_refl (term218 x y)). Qed.
Lemma lem5287013 (x : real) (y : real) : (term274 x y) = (term222 x y).
Proof. exact (MK_COMB (@lem5287011 y x) (@lem5287012 x y)). Qed.
Lemma lem5287014 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5287015 (x : real) (y : real) : (term280 x y) = (term281 x y).
Proof. exact (MK_COMB (@lem5287014) (@lem5287013 x y)). Qed.
Lemma lem5287016 (y : real) (x : real) (x' : real) : (term276 y x x') = (term200 y x x').
Proof. exact (eq_refl (term276 y x x')). Qed.
Lemma lem5287017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5287018 (y : real) (x : real) (x' : real) : (term282 y x x') = (term283 y x x').
Proof. exact (MK_COMB (@lem5287017) (@lem5287016 y x x')). Qed.
Lemma lem5287019 (x : real) (y : real) : (term218 x y) = (term218 x y).
Proof. exact (eq_refl (term218 x y)). Qed.
Lemma lem5287020 (x' : real) (x : real) (y : real) : (term284 x' x y) = (term285 x' x y).
Proof. exact (MK_COMB (@lem5287018 y x x') (@lem5287019 x y)). Qed.
Lemma lem5287021 (x : real) (y : real) : (term286 x y) = (term287 x y).
Proof. exact (fun_ext (fun x' : real => @lem5287020 x' x y)). Qed.
Lemma lem5287022 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287023 (x : real) (y : real) : (term275 x y) = (term288 x y).
Proof. exact (MK_COMB (@lem5287022) (@lem5287021 x y)). Qed.
Lemma lem5287024 (x : real) (y : real) : ((term274 x y) = (term275 x y)) = ((term222 x y) = (term288 x y)).
Proof. exact (MK_COMB (@lem5287015 x y) (@lem5287023 x y)). Qed.
Lemma lem5287025 (x : real) (y : real) : (term222 x y) = (term288 x y).
Proof. exact (EQ_MP (@lem5287024 x y) (@lem5287005 x y)). Qed.
Lemma lem5287027 {A : Type'} (P : Prop) (Q : A -> Prop) : (term289 A P Q) = (term290 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5287028 (P : Prop) (Q : real -> Prop) : (term291 P Q) = (term292 P Q).
Proof. exact (@lem5287027 real P Q). Qed.
Lemma lem5287029 (x' : real) (x : real) (y : real) : (term293 x' x y) = (term294 x' x y).
Proof. exact (@lem5287028 (term200 y x x') (term217 x y)). Qed.
Lemma lem5287030 (x : real) (y : real) (x' : real) : (term295 x y x') = (term211 x y x').
Proof. exact (eq_refl (term295 x y x')). Qed.
Lemma lem5287031 (x : real) (y : real) : (term296 x y) = (term217 x y).
Proof. exact (fun_ext (fun x' : real => @lem5287030 x y x')). Qed.
Lemma lem5287032 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287033 (x : real) (y : real) : (term297 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem5287032) (@lem5287031 x y)). Qed.
Lemma lem5287034 (y : real) (x : real) (x' : real) : (term283 y x x') = (term283 y x x').
Proof. exact (eq_refl (term283 y x x')). Qed.
Lemma lem5287035 (x' : real) (x : real) (y : real) : (term293 x' x y) = (term285 x' x y).
Proof. exact (MK_COMB (@lem5287034 y x x') (@lem5287033 x y)). Qed.
Lemma lem5287036 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5287037 (x' : real) (x : real) (y : real) : (term298 x' x y) = (term299 x' x y).
Proof. exact (MK_COMB (@lem5287036) (@lem5287035 x' x y)). Qed.
Lemma lem5287038 (x : real) (y : real) (x'' : real) : (term295 x y x'') = (term211 x y x'').
Proof. exact (eq_refl (term295 x y x'')). Qed.
Lemma lem5287039 (y : real) (x : real) (x' : real) : (term283 y x x') = (term283 y x x').
Proof. exact (eq_refl (term283 y x x')). Qed.
Lemma lem5287040 (x' : real) (x : real) (y : real) (x'' : real) : (term300 x' x y x'') = (term301 x' x y x'').
Proof. exact (MK_COMB (@lem5287039 y x x') (@lem5287038 x y x'')). Qed.
Lemma lem5287041 (x' : real) (x : real) (y : real) : (term302 x' x y) = (term303 x' x y).
Proof. exact (fun_ext (fun x'' : real => @lem5287040 x' x y x'')). Qed.
Lemma lem5287042 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287043 (x' : real) (x : real) (y : real) : (term294 x' x y) = (term304 x' x y).
Proof. exact (MK_COMB (@lem5287042) (@lem5287041 x' x y)). Qed.
Lemma lem5287044 (x' : real) (x : real) (y : real) : ((term293 x' x y) = (term294 x' x y)) = ((term285 x' x y) = (term304 x' x y)).
Proof. exact (MK_COMB (@lem5287037 x' x y) (@lem5287043 x' x y)). Qed.
Lemma lem5287045 (x' : real) (x : real) (y : real) : (term285 x' x y) = (term304 x' x y).
Proof. exact (EQ_MP (@lem5287044 x' x y) (@lem5287029 x' x y)). Qed.
Lemma lem5287046 (x : real) (y : real) : (term287 x y) = (term305 x y).
Proof. exact (fun_ext (fun x' : real => @lem5287045 x' x y)). Qed.
Lemma lem5287047 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287048 (x : real) (y : real) : (term288 x y) = (term306 x y).
Proof. exact (MK_COMB (@lem5287047) (@lem5287046 x y)). Qed.
Lemma lem5287049 (x : real) (y : real) : (term222 x y) = (term306 x y).
Proof. exact (TRANS (@lem5287025 x y) (@lem5287048 x y)). Qed.
Lemma lem5287050 (x : real) : (term228 x) = (term307 x).
Proof. exact (fun_ext (fun y : real => @lem5287049 x y)). Qed.
Lemma lem5287051 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287052 (x : real) : (term229 x) = (term308 x).
Proof. exact (MK_COMB (@lem5287051) (@lem5287050 x)). Qed.
Lemma lem5287053 : term234 = term309.
Proof. exact (fun_ext (fun x : real => @lem5287052 x)). Qed.
Lemma lem5287054 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287055 : term235 = term310.
Proof. exact (MK_COMB (@lem5287054) (@lem5287053)). Qed.
Lemma lem5287056 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5287057 : term267 = term311.
Proof. exact (MK_COMB (@lem5287056) (@lem5287055)). Qed.
Lemma lem5287058 : term265 = term265.
Proof. exact (eq_refl term265). Qed.
Lemma lem5287059 : term269 = term312.
Proof. exact (MK_COMB (@lem5287057) (@lem5287058)). Qed.
Lemma lem5287061 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5287062 (P : real -> Prop) (Q : real -> Prop) : (term315 P Q) = (term316 P Q).
Proof. exact (@lem5287061 real P Q). Qed.
Lemma lem5287063 : term317 = term318.
Proof. exact (@lem5287062 term309 term264). Qed.
Lemma lem5287064 (x : real) : (term319 x) = (term308 x).
Proof. exact (eq_refl (term319 x)). Qed.
Lemma lem5287065 : term320 = term309.
Proof. exact (fun_ext (fun x : real => @lem5287064 x)). Qed.
Lemma lem5287066 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287067 : term321 = term310.
Proof. exact (MK_COMB (@lem5287066) (@lem5287065)). Qed.
Lemma lem5287068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5287069 : term322 = term311.
Proof. exact (MK_COMB (@lem5287068) (@lem5287067)). Qed.
Lemma lem5287070 (x : real) : (term323 x) = (term259 x).
Proof. exact (eq_refl (term323 x)). Qed.
Lemma lem5287071 : term324 = term264.
Proof. exact (fun_ext (fun x : real => @lem5287070 x)). Qed.
Lemma lem5287072 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287073 : term325 = term265.
Proof. exact (MK_COMB (@lem5287072) (@lem5287071)). Qed.
Lemma lem5287074 : term317 = term312.
Proof. exact (MK_COMB (@lem5287069) (@lem5287073)). Qed.
Lemma lem5287075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5287076 : term326 = term327.
Proof. exact (MK_COMB (@lem5287075) (@lem5287074)). Qed.
Lemma lem5287077 (x : real) : (term319 x) = (term308 x).
Proof. exact (eq_refl (term319 x)). Qed.
Lemma lem5287078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5287079 (x : real) : (term328 x) = (term329 x).
Proof. exact (MK_COMB (@lem5287078) (@lem5287077 x)). Qed.
Lemma lem5287080 (x : real) : (term323 x) = (term259 x).
Proof. exact (eq_refl (term323 x)). Qed.
Lemma lem5287081 (x : real) : (term330 x) = (term331 x).
Proof. exact (MK_COMB (@lem5287079 x) (@lem5287080 x)). Qed.
Lemma lem5287082 : term332 = term333.
Proof. exact (fun_ext (fun x : real => @lem5287081 x)). Qed.
Lemma lem5287083 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287084 : term318 = term334.
Proof. exact (MK_COMB (@lem5287083) (@lem5287082)). Qed.
Lemma lem5287085 : (term317 = term318) = (term312 = term334).
Proof. exact (MK_COMB (@lem5287076) (@lem5287084)). Qed.
Lemma lem5287086 : term312 = term334.
Proof. exact (EQ_MP (@lem5287085) (@lem5287063)). Qed.
Lemma lem5287088 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5287089 (P : real -> Prop) (Q : real -> Prop) : (term315 P Q) = (term316 P Q).
Proof. exact (@lem5287088 real P Q). Qed.
Lemma lem5287090 (x : real) : (term335 x) = (term336 x).
Proof. exact (@lem5287089 (term307 x) (term258 x)). Qed.
Lemma lem5287091 (x : real) (y : real) : (term337 x y) = (term306 x y).
Proof. exact (eq_refl (term337 x y)). Qed.
Lemma lem5287092 (x : real) : (term338 x) = (term307 x).
Proof. exact (fun_ext (fun y : real => @lem5287091 x y)). Qed.
Lemma lem5287093 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287094 (x : real) : (term339 x) = (term308 x).
Proof. exact (MK_COMB (@lem5287093) (@lem5287092 x)). Qed.
Lemma lem5287095 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5287096 (x : real) : (term340 x) = (term329 x).
Proof. exact (MK_COMB (@lem5287095) (@lem5287094 x)). Qed.
Lemma lem5287097 (x : real) (y : real) : (term341 x y) = (term253 x y).
Proof. exact (eq_refl (term341 x y)). Qed.
Lemma lem5287098 (x : real) : (term342 x) = (term258 x).
Proof. exact (fun_ext (fun y : real => @lem5287097 x y)). Qed.
Lemma lem5287099 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287100 (x : real) : (term343 x) = (term259 x).
Proof. exact (MK_COMB (@lem5287099) (@lem5287098 x)). Qed.
Lemma lem5287101 (x : real) : (term335 x) = (term331 x).
Proof. exact (MK_COMB (@lem5287096 x) (@lem5287100 x)). Qed.
Lemma lem5287102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5287103 (x : real) : (term344 x) = (term345 x).
Proof. exact (MK_COMB (@lem5287102) (@lem5287101 x)). Qed.
Lemma lem5287104 (x : real) (y : real) : (term337 x y) = (term306 x y).
Proof. exact (eq_refl (term337 x y)). Qed.
Lemma lem5287105 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5287106 (x : real) (y : real) : (term346 x y) = (term347 x y).
Proof. exact (MK_COMB (@lem5287105) (@lem5287104 x y)). Qed.
Lemma lem5287107 (x : real) (y : real) : (term341 x y) = (term253 x y).
Proof. exact (eq_refl (term341 x y)). Qed.
Lemma lem5287108 (x : real) (y : real) : (term348 x y) = (term349 x y).
Proof. exact (MK_COMB (@lem5287106 x y) (@lem5287107 x y)). Qed.
Lemma lem5287109 (x : real) : (term350 x) = (term351 x).
Proof. exact (fun_ext (fun y : real => @lem5287108 x y)). Qed.
Lemma lem5287110 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287111 (x : real) : (term336 x) = (term352 x).
Proof. exact (MK_COMB (@lem5287110) (@lem5287109 x)). Qed.
Lemma lem5287112 (x : real) : ((term335 x) = (term336 x)) = ((term331 x) = (term352 x)).
Proof. exact (MK_COMB (@lem5287103 x) (@lem5287111 x)). Qed.
Lemma lem5287113 (x : real) : (term331 x) = (term352 x).
Proof. exact (EQ_MP (@lem5287112 x) (@lem5287090 x)). Qed.
Lemma lem5287115 {A : Type'} (P : A -> Prop) (Q : Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5287116 (P : real -> Prop) (Q : Prop) : (term355 P Q) = (term356 P Q).
Proof. exact (@lem5287115 real P Q). Qed.
Lemma lem5287117 (x : real) (y : real) : (term357 x y) = (term358 x y).
Proof. exact (@lem5287116 (term305 x y) (term253 x y)). Qed.
Lemma lem5287118 (x' : real) (x : real) (y : real) : (term359 x y x') = (term304 x' x y).
Proof. exact (eq_refl (term359 x y x')). Qed.
Lemma lem5287119 (x : real) (y : real) : (term360 x y) = (term305 x y).
Proof. exact (fun_ext (fun x' : real => @lem5287118 x' x y)). Qed.
Lemma lem5287120 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287121 (x : real) (y : real) : (term361 x y) = (term306 x y).
Proof. exact (MK_COMB (@lem5287120) (@lem5287119 x y)). Qed.
Lemma lem5287122 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5287123 (x : real) (y : real) : (term362 x y) = (term347 x y).
Proof. exact (MK_COMB (@lem5287122) (@lem5287121 x y)). Qed.
Lemma lem5287124 (x : real) (y : real) : (term253 x y) = (term253 x y).
Proof. exact (eq_refl (term253 x y)). Qed.
Lemma lem5287125 (x : real) (y : real) : (term357 x y) = (term349 x y).
Proof. exact (MK_COMB (@lem5287123 x y) (@lem5287124 x y)). Qed.
Lemma lem5287126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5287127 (x : real) (y : real) : (term363 x y) = (term364 x y).
Proof. exact (MK_COMB (@lem5287126) (@lem5287125 x y)). Qed.
Lemma lem5287128 (x' : real) (x : real) (y : real) : (term359 x y x') = (term304 x' x y).
Proof. exact (eq_refl (term359 x y x')). Qed.
Lemma lem5287129 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5287130 (x' : real) (x : real) (y : real) : (term365 x y x') = (term366 x' x y).
Proof. exact (MK_COMB (@lem5287129) (@lem5287128 x' x y)). Qed.
Lemma lem5287131 (x : real) (y : real) : (term253 x y) = (term253 x y).
Proof. exact (eq_refl (term253 x y)). Qed.
Lemma lem5287132 (x' : real) (x : real) (y : real) : (term367 x' x y) = (term368 x' x y).
Proof. exact (MK_COMB (@lem5287130 x' x y) (@lem5287131 x y)). Qed.
Lemma lem5287133 (x : real) (y : real) : (term369 x y) = (term370 x y).
Proof. exact (fun_ext (fun x' : real => @lem5287132 x' x y)). Qed.
Lemma lem5287134 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287135 (x : real) (y : real) : (term358 x y) = (term371 x y).
Proof. exact (MK_COMB (@lem5287134) (@lem5287133 x y)). Qed.
Lemma lem5287136 (x : real) (y : real) : ((term357 x y) = (term358 x y)) = ((term349 x y) = (term371 x y)).
Proof. exact (MK_COMB (@lem5287127 x y) (@lem5287135 x y)). Qed.
Lemma lem5287137 (x : real) (y : real) : (term349 x y) = (term371 x y).
Proof. exact (EQ_MP (@lem5287136 x y) (@lem5287117 x y)). Qed.
Lemma lem5287139 {A : Type'} (P : A -> Prop) (Q : Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5287140 (P : real -> Prop) (Q : Prop) : (term355 P Q) = (term356 P Q).
Proof. exact (@lem5287139 real P Q). Qed.
Lemma lem5287141 (x' : real) (x : real) (y : real) : (term372 x' x y) = (term373 x' x y).
Proof. exact (@lem5287140 (term303 x' x y) (term253 x y)). Qed.
Lemma lem5287142 (x' : real) (x : real) (y : real) (x'' : real) : (term374 x' x y x'') = (term301 x' x y x'').
Proof. exact (eq_refl (term374 x' x y x'')). Qed.
Lemma lem5287143 (x' : real) (x : real) (y : real) : (term375 x' x y) = (term303 x' x y).
Proof. exact (fun_ext (fun x'' : real => @lem5287142 x' x y x'')). Qed.
Lemma lem5287144 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287145 (x' : real) (x : real) (y : real) : (term376 x' x y) = (term304 x' x y).
Proof. exact (MK_COMB (@lem5287144) (@lem5287143 x' x y)). Qed.
Lemma lem5287146 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5287147 (x' : real) (x : real) (y : real) : (term377 x' x y) = (term366 x' x y).
Proof. exact (MK_COMB (@lem5287146) (@lem5287145 x' x y)). Qed.
Lemma lem5287148 (x : real) (y : real) : (term253 x y) = (term253 x y).
Proof. exact (eq_refl (term253 x y)). Qed.
Lemma lem5287149 (x' : real) (x : real) (y : real) : (term372 x' x y) = (term368 x' x y).
Proof. exact (MK_COMB (@lem5287147 x' x y) (@lem5287148 x y)). Qed.
Lemma lem5287150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5287151 (x' : real) (x : real) (y : real) : (term378 x' x y) = (term379 x' x y).
Proof. exact (MK_COMB (@lem5287150) (@lem5287149 x' x y)). Qed.
Lemma lem5287152 (x' : real) (x : real) (y : real) (x'' : real) : (term374 x' x y x'') = (term301 x' x y x'').
Proof. exact (eq_refl (term374 x' x y x'')). Qed.
Lemma lem5287153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5287154 (x' : real) (x : real) (y : real) (x'' : real) : (term380 x' x y x'') = (term381 x' x y x'').
Proof. exact (MK_COMB (@lem5287153) (@lem5287152 x' x y x'')). Qed.
Lemma lem5287155 (x : real) (y : real) : (term253 x y) = (term253 x y).
Proof. exact (eq_refl (term253 x y)). Qed.
Lemma lem5287156 (x' : real) (x'' : real) (x : real) (y : real) : (term382 x' x'' x y) = (term383 x' x'' x y).
Proof. exact (MK_COMB (@lem5287154 x' x y x'') (@lem5287155 x y)). Qed.
Lemma lem5287157 (x' : real) (x : real) (y : real) : (term384 x' x y) = (term385 x' x y).
Proof. exact (fun_ext (fun x'' : real => @lem5287156 x' x'' x y)). Qed.
Lemma lem5287158 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287159 (x' : real) (x : real) (y : real) : (term373 x' x y) = (term386 x' x y).
Proof. exact (MK_COMB (@lem5287158) (@lem5287157 x' x y)). Qed.
Lemma lem5287160 (x' : real) (x : real) (y : real) : ((term372 x' x y) = (term373 x' x y)) = ((term368 x' x y) = (term386 x' x y)).
Proof. exact (MK_COMB (@lem5287151 x' x y) (@lem5287159 x' x y)). Qed.
Lemma lem5287161 (x' : real) (x : real) (y : real) : (term368 x' x y) = (term386 x' x y).
Proof. exact (EQ_MP (@lem5287160 x' x y) (@lem5287141 x' x y)). Qed.
Lemma lem5287162 (x : real) (y : real) : (term370 x y) = (term387 x y).
Proof. exact (fun_ext (fun x' : real => @lem5287161 x' x y)). Qed.
Lemma lem5287163 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287164 (x : real) (y : real) : (term371 x y) = (term388 x y).
Proof. exact (MK_COMB (@lem5287163) (@lem5287162 x y)). Qed.
Lemma lem5287165 (x : real) (y : real) : (term349 x y) = (term388 x y).
Proof. exact (TRANS (@lem5287137 x y) (@lem5287164 x y)). Qed.
Lemma lem5287166 (x : real) : (term351 x) = (term389 x).
Proof. exact (fun_ext (fun y : real => @lem5287165 x y)). Qed.
Lemma lem5287167 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287168 (x : real) : (term352 x) = (term390 x).
Proof. exact (MK_COMB (@lem5287167) (@lem5287166 x)). Qed.
Lemma lem5287169 (x : real) : (term331 x) = (term390 x).
Proof. exact (TRANS (@lem5287113 x) (@lem5287168 x)). Qed.
Lemma lem5287170 : term333 = term391.
Proof. exact (fun_ext (fun x : real => @lem5287169 x)). Qed.
Lemma lem5287171 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5287172 : term334 = term392.
Proof. exact (MK_COMB (@lem5287171) (@lem5287170)). Qed.
Lemma lem5287173 : term312 = term392.
Proof. exact (TRANS (@lem5287086) (@lem5287172)). Qed.
Lemma lem5287175 : term269 = term392.
Proof. exact (TRANS (@lem5287059) (@lem5287173)). Qed.
Lemma lem5287176 : term188 = term392.
Proof. exact (TRANS (@lem5286796) (@lem5287175)). Qed.
Lemma lem5287177 (h1 : term188) : term392.
Proof. exact (EQ_MP (@lem5287176) (@lem5286674 h1)). Qed.
Lemma lem5287182 (y : real) (x : real) : (term195 y x) = (term195 y x).
Proof. exact (eq_refl (term195 y x)). Qed.
Lemma lem5287183 (x : real) : (term196 x) = (term196 x).
Proof. exact (fun_ext (fun y : real => @lem5287182 y x)). Qed.
Lemma lem5287184 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287185 (x : real) : (term197 x) = (term197 x).
Proof. exact (MK_COMB (@lem5287184) (@lem5287183 x)). Qed.
Lemma lem5287186 : term198 = term198.
Proof. exact (fun_ext (fun x : real => @lem5287185 x)). Qed.
Lemma lem5287187 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287244 : term193 = term193.
Proof. exact (MK_COMB (@lem5287187) (@lem5287186)). Qed.
Lemma lem5287245 (h1 : term193) : term193.
Proof. exact (EQ_MP (@lem5287244) (@lem5286675 h1)). Qed.
Lemma lem5287246 (x : real) (h1 : term390 x) : term390 x.
Proof. exact (h1). Qed.
Lemma lem5287247 (x : real) (y : real) (h1 : term388 x y) : term388 x y.
Proof. exact (h1). Qed.
Lemma lem5287248 (x' : real) (x : real) (y : real) (h1 : term386 x' x y) : term386 x' x y.
Proof. exact (h1). Qed.
Lemma lem5287249 (x' : real) (x'' : real) (x : real) (y : real) (h1 : term383 x' x'' x y) : term383 x' x'' x y.
Proof. exact (h1). Qed.
Lemma lem5287262 (y : real) (x : real) : (term195 y x) = (term195 y x).
Proof. exact (eq_refl (term195 y x)). Qed.
Lemma lem5287263 (x : real) : (term196 x) = (term196 x).
Proof. exact (fun_ext (fun y : real => @lem5287262 y x)). Qed.
Lemma lem5287264 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287265 (x : real) : (term197 x) = (term197 x).
Proof. exact (MK_COMB (@lem5287264) (@lem5287263 x)). Qed.
Lemma lem5287266 : term198 = term198.
Proof. exact (fun_ext (fun x : real => @lem5287265 x)). Qed.
Lemma lem5287267 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287268 : term193 = term193.
Proof. exact (MK_COMB (@lem5287267) (@lem5287266)). Qed.
Lemma lem5287269 (h1 : term193) : term193.
Proof. exact (EQ_MP (@lem5287268) (@lem5287245 h1)). Qed.
Lemma lem5287306 (x : real) (x' : real) (y : real) : (term243 x x' y) = (term243 x x' y).
Proof. exact (eq_refl (term243 x x' y)). Qed.
Lemma lem5287307 (x : real) (y : real) : (term252 x y) = (term252 x y).
Proof. exact (fun_ext (fun x' : real => @lem5287306 x x' y)). Qed.
Lemma lem5287308 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287309 (x : real) (y : real) : (term253 x y) = (term253 x y).
Proof. exact (MK_COMB (@lem5287308) (@lem5287307 x y)). Qed.
Lemma lem5287360 (x' : real) (x : real) (y : real) (x'' : real) : (term381 x' x y x'') = (term381 x' x y x'').
Proof. exact (eq_refl (term381 x' x y x'')). Qed.
Lemma lem5287361 (x' : real) (x'' : real) (x : real) (y : real) : (term383 x' x'' x y) = (term383 x' x'' x y).
Proof. exact (MK_COMB (@lem5287360 x' x y x'') (@lem5287309 x y)). Qed.
Lemma lem5287362 (x' : real) (x'' : real) (x : real) (y : real) (h1 : term383 x' x'' x y) : term383 x' x'' x y.
Proof. exact (EQ_MP (@lem5287361 x' x'' x y) (@lem5287249 x' x'' x y h1)). Qed.
Lemma lem5287363 (x' : real) (x : real) (y : real) (x'' : real) (h1 : term301 x' x y x'') : term301 x' x y x''.
Proof. exact (h1). Qed.
Lemma lem5287364 (x : real) (y : real) (h1 : term253 x y) : term253 x y.
Proof. exact (h1). Qed.
Lemma lem5287365 (x' : real) (x : real) (y : real) (x'' : real) (h1 : term301 x' x y x'') : term211 x y x''.
Proof. exact (proj2 (@lem5287363 x' x y x'' h1)). Qed.
Lemma lem5287366 (x' : real) (x : real) (y : real) (x'' : real) (h1 : term301 x' x y x'') : term200 y x x'.
Proof. exact (proj1 (@lem5287363 x' x y x'' h1)). Qed.
Lemma lem5287368 (x' : real) (x : real) (y : real) (x'' : real) (h1 : term301 x' x y x'') : term110 x x'' y.
Proof. exact (proj1 (@lem5287365 x' x y x'' h1)). Qed.
Lemma lem5287370 (x' : real) (x : real) (y : real) (x'' : real) (h1 : term301 x' x y x'') : term110 x x' y.
Proof. exact (proj1 (@lem5287366 x' x y x'' h1)). Qed.
Lemma lem5287384 (y : real) (x : real) : (term195 y x) = (term195 y x).
Proof. exact (eq_refl (term195 y x)). Qed.
Lemma lem5287385 (x : real) : (term196 x) = (term196 x).
Proof. exact (fun_ext (fun y : real => @lem5287384 y x)). Qed.
Lemma lem5287386 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287387 (x : real) : (term197 x) = (term197 x).
Proof. exact (MK_COMB (@lem5287386) (@lem5287385 x)). Qed.
Lemma lem5287388 : term198 = term198.
Proof. exact (fun_ext (fun x : real => @lem5287387 x)). Qed.
Lemma lem5287389 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287391 : term193 = term193.
Proof. exact (MK_COMB (@lem5287389) (@lem5287388)). Qed.
Lemma lem5287392 (h1 : term193) : term193.
Proof. exact (EQ_MP (@lem5287391) (@lem5287269 h1)). Qed.
Lemma lem5287404 (x' : real) (x : real) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5287416 (y : real) (x : real) : (term195 y x) = (term195 y x).
Proof. exact (eq_refl (term195 y x)). Qed.
Lemma lem5287417 (x : real) : (term196 x) = (term196 x).
Proof. exact (fun_ext (fun y : real => @lem5287416 y x)). Qed.
Lemma lem5287418 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287419 (x : real) : (term197 x) = (term197 x).
Proof. exact (MK_COMB (@lem5287418) (@lem5287417 x)). Qed.
Lemma lem5287420 : term198 = term198.
Proof. exact (fun_ext (fun x : real => @lem5287419 x)). Qed.
Lemma lem5287421 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287423 : term193 = term193.
Proof. exact (MK_COMB (@lem5287421) (@lem5287420)). Qed.
Lemma lem5287424 (h1 : term193) : term193.
Proof. exact (EQ_MP (@lem5287423) (@lem5287269 h1)). Qed.
Lemma lem5287436 (x' : real) (x : real) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5287448 (y : real) (x : real) : (term195 y x) = (term195 y x).
Proof. exact (eq_refl (term195 y x)). Qed.
Lemma lem5287449 (x : real) : (term196 x) = (term196 x).
Proof. exact (fun_ext (fun y : real => @lem5287448 y x)). Qed.
Lemma lem5287450 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287451 (x : real) : (term197 x) = (term197 x).
Proof. exact (MK_COMB (@lem5287450) (@lem5287449 x)). Qed.
Lemma lem5287452 : term198 = term198.
Proof. exact (fun_ext (fun x : real => @lem5287451 x)). Qed.
Lemma lem5287453 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287455 : term193 = term193.
Proof. exact (MK_COMB (@lem5287453) (@lem5287452)). Qed.
Lemma lem5287456 (h1 : term193) : term193.
Proof. exact (EQ_MP (@lem5287455) (@lem5287269 h1)). Qed.
Lemma lem5287468 (x' : real) (y : real) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem5287472 (x'' : real) (x : real) (h1 : x'' = x) : x'' = x.
Proof. exact (h1). Qed.
Lemma lem5287480 (y : real) (x : real) : (term195 y x) = (term195 y x).
Proof. exact (eq_refl (term195 y x)). Qed.
Lemma lem5287481 (x : real) : (term196 x) = (term196 x).
Proof. exact (fun_ext (fun y : real => @lem5287480 y x)). Qed.
Lemma lem5287482 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287483 (x : real) : (term197 x) = (term197 x).
Proof. exact (MK_COMB (@lem5287482) (@lem5287481 x)). Qed.
Lemma lem5287484 : term198 = term198.
Proof. exact (fun_ext (fun x : real => @lem5287483 x)). Qed.
Lemma lem5287485 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287487 : term193 = term193.
Proof. exact (MK_COMB (@lem5287485) (@lem5287484)). Qed.
Lemma lem5287488 (h1 : term193) : term193.
Proof. exact (EQ_MP (@lem5287487) (@lem5287269 h1)). Qed.
Lemma lem5287504 (x'' : real) (y : real) (h1 : x'' = y) : x'' = y.
Proof. exact (h1). Qed.
Lemma lem5287512 (y : real) (x : real) : (term195 y x) = (term195 y x).
Proof. exact (eq_refl (term195 y x)). Qed.
Lemma lem5287513 (x : real) : (term196 x) = (term196 x).
Proof. exact (fun_ext (fun y : real => @lem5287512 y x)). Qed.
Lemma lem5287514 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287515 (x : real) : (term197 x) = (term197 x).
Proof. exact (MK_COMB (@lem5287514) (@lem5287513 x)). Qed.
Lemma lem5287516 : term198 = term198.
Proof. exact (fun_ext (fun x : real => @lem5287515 x)). Qed.
Lemma lem5287517 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287519 : term193 = term193.
Proof. exact (MK_COMB (@lem5287517) (@lem5287516)). Qed.
Lemma lem5287520 (h1 : term193) : term193.
Proof. exact (EQ_MP (@lem5287519) (@lem5287269 h1)). Qed.
Lemma lem5287544 (x : real) (x' : real) (y : real) : (term243 x x' y) = (term393 x x' y).
Proof. exact (@lem19699 (term394 x' x) (term394 x' y) (term239 x x' y)). Qed.
Lemma lem5287545 (x : real) (y : real) : (term252 x y) = (term395 x y).
Proof. exact (fun_ext (fun x' : real => @lem5287544 x x' y)). Qed.
Lemma lem5287546 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5287548 (x : real) (y : real) : (term253 x y) = (term396 x y).
Proof. exact (MK_COMB (@lem5287546) (@lem5287545 x y)). Qed.
Lemma lem5287549 (x : real) (y : real) (h1 : term253 x y) : term396 x y.
Proof. exact (EQ_MP (@lem5287548 x y) (@lem5287364 x y h1)). Qed.
Lemma lem5287550 (_69167 : real) (h1 : term193) : term397 _69167.
Proof. exact (@lem5287392 h1 _69167). Qed.
Lemma lem5287551 (_69167 : real) : (term397 _69167) = (term197 _69167).
Proof. exact (eq_refl (term397 _69167)). Qed.
Lemma lem5287552 (_69167 : real) (h1 : term193) : term197 _69167.
Proof. exact (EQ_MP (@lem5287551 _69167) (@lem5287550 _69167 h1)). Qed.
Lemma lem5287553 (_69167 : real) (_69168 : real) (h1 : term193) : term398 _69167 _69168.
Proof. exact (@lem5287552 _69167 h1 _69168). Qed.
Lemma lem5287554 (_69168 : real) (_69167 : real) : (term398 _69167 _69168) = (term195 _69168 _69167).
Proof. exact (eq_refl (term398 _69167 _69168)). Qed.
Lemma lem5287556 (_69169 : real) (h1 : term193) : term397 _69169.
Proof. exact (@lem5287424 h1 _69169). Qed.
Lemma lem5287557 (_69169 : real) : (term397 _69169) = (term197 _69169).
Proof. exact (eq_refl (term397 _69169)). Qed.
Lemma lem5287558 (_69169 : real) (h1 : term193) : term197 _69169.
Proof. exact (EQ_MP (@lem5287557 _69169) (@lem5287556 _69169 h1)). Qed.
Lemma lem5287559 (_69169 : real) (_69170 : real) (h1 : term193) : term398 _69169 _69170.
Proof. exact (@lem5287558 _69169 h1 _69170). Qed.
Lemma lem5287560 (_69170 : real) (_69169 : real) : (term398 _69169 _69170) = (term195 _69170 _69169).
Proof. exact (eq_refl (term398 _69169 _69170)). Qed.
Lemma lem5287562 (_69171 : real) (h1 : term193) : term397 _69171.
Proof. exact (@lem5287456 h1 _69171). Qed.
Lemma lem5287563 (_69171 : real) : (term397 _69171) = (term197 _69171).
Proof. exact (eq_refl (term397 _69171)). Qed.
Lemma lem5287564 (_69171 : real) (h1 : term193) : term197 _69171.
Proof. exact (EQ_MP (@lem5287563 _69171) (@lem5287562 _69171 h1)). Qed.
Lemma lem5287565 (_69171 : real) (_69172 : real) (h1 : term193) : term398 _69171 _69172.
Proof. exact (@lem5287564 _69171 h1 _69172). Qed.
Lemma lem5287566 (_69172 : real) (_69171 : real) : (term398 _69171 _69172) = (term195 _69172 _69171).
Proof. exact (eq_refl (term398 _69171 _69172)). Qed.
Lemma lem5287568 (_69173 : real) (h1 : term193) : term397 _69173.
Proof. exact (@lem5287488 h1 _69173). Qed.
Lemma lem5287569 (_69173 : real) : (term397 _69173) = (term197 _69173).
Proof. exact (eq_refl (term397 _69173)). Qed.
Lemma lem5287570 (_69173 : real) (h1 : term193) : term197 _69173.
Proof. exact (EQ_MP (@lem5287569 _69173) (@lem5287568 _69173 h1)). Qed.
Lemma lem5287571 (_69173 : real) (_69174 : real) (h1 : term193) : term398 _69173 _69174.
Proof. exact (@lem5287570 _69173 h1 _69174). Qed.
Lemma lem5287572 (_69174 : real) (_69173 : real) : (term398 _69173 _69174) = (term195 _69174 _69173).
Proof. exact (eq_refl (term398 _69173 _69174)). Qed.
Lemma lem5287574 (_69175 : real) (h1 : term193) : term397 _69175.
Proof. exact (@lem5287520 h1 _69175). Qed.
Lemma lem5287575 (_69175 : real) : (term397 _69175) = (term197 _69175).
Proof. exact (eq_refl (term397 _69175)). Qed.
Lemma lem5287576 (_69175 : real) (h1 : term193) : term197 _69175.
Proof. exact (EQ_MP (@lem5287575 _69175) (@lem5287574 _69175 h1)). Qed.
Lemma lem5287577 (_69175 : real) (_69176 : real) (h1 : term193) : term398 _69175 _69176.
Proof. exact (@lem5287576 _69175 h1 _69176). Qed.
Lemma lem5287578 (_69176 : real) (_69175 : real) : (term398 _69175 _69176) = (term195 _69176 _69175).
Proof. exact (eq_refl (term398 _69175 _69176)). Qed.
Lemma lem5287580 (_69177 : real) (x : real) (y : real) (h1 : term253 x y) : term399 x y _69177.
Proof. exact (@lem5287549 x y h1 _69177). Qed.
Lemma lem5287581 (x : real) (_69177 : real) (y : real) : (term399 x y _69177) = (term393 x _69177 y).
Proof. exact (eq_refl (term399 x y _69177)). Qed.
Lemma lem5287582 (_69177 : real) (x : real) (y : real) (h1 : term253 x y) : term393 x _69177 y.
Proof. exact (EQ_MP (@lem5287581 x _69177 y) (@lem5287580 _69177 x y h1)). Qed.
Lemma lem5287596 (x' : real) (x : real) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5287610 (x' : real) (x : real) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5287620 (x' : real) (x : real) (y : real) (x'' : real) (h1 : term301 x' x y x'') : term400 y x''.
Proof. exact (proj2 (@lem5287365 x' x y x'' h1)). Qed.
Lemma lem5287624 (x' : real) (y : real) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem5287626 (x'' : real) (x : real) (h1 : x'' = x) : x'' = x.
Proof. exact (h1). Qed.
Lemma lem5287634 (x' : real) (x : real) (y : real) (x'' : real) (h1 : term301 x' x y x'') : term400 y x''.
Proof. exact (proj2 (@lem5287365 x' x y x'' h1)). Qed.
Lemma lem5287640 (x'' : real) (y : real) (h1 : x'' = y) : x'' = y.
Proof. exact (h1). Qed.
Lemma lem5287646 (_69176 : real) (_69175 : real) (h1 : term193) : term195 _69176 _69175.
Proof. exact (EQ_MP (@lem5287578 _69176 _69175) (@lem5287577 _69175 _69176 h1)). Qed.
Lemma lem5287656 (_69177 : real) (x : real) (y : real) (h1 : term253 x y) : term401 x _69177 y.
Proof. exact (proj1 (@lem5287582 _69177 x y h1)). Qed.
Lemma lem5287666 (_69177 : real) (x : real) (y : real) (h1 : term253 x y) : term402 x _69177 y.
Proof. exact (proj2 (@lem5287582 _69177 x y h1)). Qed.
Lemma lem5287721 (x' : real) (x : real) (y : real) (x'' : real) (h1 : term301 x' x y x'') : term400 x x'.
Proof. exact (proj2 (@lem5287366 x' x y x'' h1)). Qed.
Lemma lem5287735 (x' : real) (x : real) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5287763 (_69168 : real) (_69167 : real) (h1 : term193) : term195 _69168 _69167.
Proof. exact (EQ_MP (@lem5287554 _69168 _69167) (@lem5287553 _69167 _69168 h1)). Qed.
Lemma lem5287778 (x : real) : (term403 x) = (term403 x).
Proof. exact (eq_refl (term403 x)). Qed.
Lemma lem5287779 (x' : real) (x : real) (h1 : x' = x) : (term404 x x') = (term405 x).
Proof. exact (MK_COMB (@lem5287778 x) (@lem5287735 x' x h1)). Qed.
Lemma lem5287780 (x : real) : (term405 x) = (term406 x).
Proof. exact (eq_refl (term405 x)). Qed.
Lemma lem5287781 (x : real) (x' : real) : (term407 x x') = (term407 x x').
Proof. exact (eq_refl (term407 x x')). Qed.
Lemma lem5287782 (x' : real) (x : real) : ((term404 x x') = (term405 x)) = ((term404 x x') = (term406 x)).
Proof. exact (MK_COMB (@lem5287781 x x') (@lem5287780 x)). Qed.
Lemma lem5287783 (x : real) (x' : real) : (term404 x x') = (term400 x x').
Proof. exact (eq_refl (term404 x x')). Qed.
Lemma lem5287784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5287785 (x : real) (x' : real) : (term407 x x') = (term408 x x').
Proof. exact (MK_COMB (@lem5287784) (@lem5287783 x x')). Qed.
Lemma lem5287786 (x : real) : (term406 x) = (term406 x).
Proof. exact (eq_refl (term406 x)). Qed.
Lemma lem5287787 (x' : real) (x : real) : ((term404 x x') = (term406 x)) = ((term400 x x') = (term406 x)).
Proof. exact (MK_COMB (@lem5287785 x x') (@lem5287786 x)). Qed.
Lemma lem5287788 (x' : real) (x : real) : ((term404 x x') = (term405 x)) = ((term400 x x') = (term406 x)).
Proof. exact (TRANS (@lem5287782 x' x) (@lem5287787 x' x)). Qed.
Lemma lem5287789 (x' : real) (x : real) (h1 : x' = x) : (term400 x x') = (term406 x).
Proof. exact (EQ_MP (@lem5287788 x' x) (@lem5287779 x' x h1)). Qed.
Lemma lem5287790 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term301 x' x y x'') (h2 : x' = x) : term406 x.
Proof. exact (EQ_MP (@lem5287789 x' x h2) (@lem5287721 x' x y x'' h1)). Qed.
Lemma lem5287845 (x' : real) (x : real) (y : real) (x'' : real) (h1 : term301 x' x y x'') : term400 x x'.
Proof. exact (proj2 (@lem5287366 x' x y x'' h1)). Qed.
Lemma lem5287859 (x' : real) (x : real) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5287887 (_69170 : real) (_69169 : real) (h1 : term193) : term195 _69170 _69169.
Proof. exact (EQ_MP (@lem5287560 _69170 _69169) (@lem5287559 _69169 _69170 h1)). Qed.
Lemma lem5287902 (x : real) : (term403 x) = (term403 x).
Proof. exact (eq_refl (term403 x)). Qed.
Lemma lem5287903 (x' : real) (x : real) (h1 : x' = x) : (term404 x x') = (term405 x).
Proof. exact (MK_COMB (@lem5287902 x) (@lem5287859 x' x h1)). Qed.
Lemma lem5287904 (x : real) : (term405 x) = (term406 x).
Proof. exact (eq_refl (term405 x)). Qed.
Lemma lem5287905 (x : real) (x' : real) : (term407 x x') = (term407 x x').
Proof. exact (eq_refl (term407 x x')). Qed.
Lemma lem5287906 (x' : real) (x : real) : ((term404 x x') = (term405 x)) = ((term404 x x') = (term406 x)).
Proof. exact (MK_COMB (@lem5287905 x x') (@lem5287904 x)). Qed.
Lemma lem5287907 (x : real) (x' : real) : (term404 x x') = (term400 x x').
Proof. exact (eq_refl (term404 x x')). Qed.
Lemma lem5287908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5287909 (x : real) (x' : real) : (term407 x x') = (term408 x x').
Proof. exact (MK_COMB (@lem5287908) (@lem5287907 x x')). Qed.
Lemma lem5287910 (x : real) : (term406 x) = (term406 x).
Proof. exact (eq_refl (term406 x)). Qed.
Lemma lem5287911 (x' : real) (x : real) : ((term404 x x') = (term406 x)) = ((term400 x x') = (term406 x)).
Proof. exact (MK_COMB (@lem5287909 x x') (@lem5287910 x)). Qed.
Lemma lem5287912 (x' : real) (x : real) : ((term404 x x') = (term405 x)) = ((term400 x x') = (term406 x)).
Proof. exact (TRANS (@lem5287906 x' x) (@lem5287911 x' x)). Qed.
Lemma lem5287913 (x' : real) (x : real) (h1 : x' = x) : (term400 x x') = (term406 x).
Proof. exact (EQ_MP (@lem5287912 x' x) (@lem5287903 x' x h1)). Qed.
Lemma lem5287914 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term301 x' x y x'') (h2 : x' = x) : term406 x.
Proof. exact (EQ_MP (@lem5287913 x' x h2) (@lem5287845 x' x y x'' h1)). Qed.
Lemma lem5287943 (y : real) : (term403 y) = (term403 y).
Proof. exact (eq_refl (term403 y)). Qed.
Lemma lem5287944 (y : real) (x'' : real) (x : real) (h1 : x'' = x) : (term404 y x'') = (term404 y x).
Proof. exact (MK_COMB (@lem5287943 y) (@lem5287626 x'' x h1)). Qed.
Lemma lem5287945 (y : real) (x : real) : (term404 y x) = (term400 y x).
Proof. exact (eq_refl (term404 y x)). Qed.
Lemma lem5287946 (y : real) (x'' : real) : (term407 y x'') = (term407 y x'').
Proof. exact (eq_refl (term407 y x'')). Qed.
Lemma lem5287947 (x'' : real) (y : real) (x : real) : ((term404 y x'') = (term404 y x)) = ((term404 y x'') = (term400 y x)).
Proof. exact (MK_COMB (@lem5287946 y x'') (@lem5287945 y x)). Qed.
Lemma lem5287948 (y : real) (x'' : real) : (term404 y x'') = (term400 y x'').
Proof. exact (eq_refl (term404 y x'')). Qed.
Lemma lem5287949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5287950 (y : real) (x'' : real) : (term407 y x'') = (term408 y x'').
Proof. exact (MK_COMB (@lem5287949) (@lem5287948 y x'')). Qed.
Lemma lem5287951 (y : real) (x : real) : (term400 y x) = (term400 y x).
Proof. exact (eq_refl (term400 y x)). Qed.
Lemma lem5287952 (x'' : real) (y : real) (x : real) : ((term404 y x'') = (term400 y x)) = ((term400 y x'') = (term400 y x)).
Proof. exact (MK_COMB (@lem5287950 y x'') (@lem5287951 y x)). Qed.
Lemma lem5287953 (x'' : real) (y : real) (x : real) : ((term404 y x'') = (term404 y x)) = ((term400 y x'') = (term400 y x)).
Proof. exact (TRANS (@lem5287947 x'' y x) (@lem5287952 x'' y x)). Qed.
Lemma lem5287954 (y : real) (x'' : real) (x : real) (h1 : x'' = x) : (term400 y x'') = (term400 y x).
Proof. exact (EQ_MP (@lem5287953 x'' y x) (@lem5287944 y x'' x h1)). Qed.
Lemma lem5287969 (x' : real) (x : real) (y : real) (x'' : real) (h1 : term301 x' x y x'') : term400 x x'.
Proof. exact (proj2 (@lem5287366 x' x y x'' h1)). Qed.
Lemma lem5287983 (x' : real) (y : real) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem5288011 (_69172 : real) (_69171 : real) (h1 : term193) : term195 _69172 _69171.
Proof. exact (EQ_MP (@lem5287566 _69172 _69171) (@lem5287565 _69171 _69172 h1)). Qed.
Lemma lem5288026 (x : real) : (term403 x) = (term403 x).
Proof. exact (eq_refl (term403 x)). Qed.
Lemma lem5288027 (x : real) (x' : real) (y : real) (h1 : x' = y) : (term404 x x') = (term404 x y).
Proof. exact (MK_COMB (@lem5288026 x) (@lem5287983 x' y h1)). Qed.
Lemma lem5288028 (x : real) (y : real) : (term404 x y) = (term400 x y).
Proof. exact (eq_refl (term404 x y)). Qed.
Lemma lem5288029 (x : real) (x' : real) : (term407 x x') = (term407 x x').
Proof. exact (eq_refl (term407 x x')). Qed.
Lemma lem5288030 (x' : real) (x : real) (y : real) : ((term404 x x') = (term404 x y)) = ((term404 x x') = (term400 x y)).
Proof. exact (MK_COMB (@lem5288029 x x') (@lem5288028 x y)). Qed.
Lemma lem5288031 (x : real) (x' : real) : (term404 x x') = (term400 x x').
Proof. exact (eq_refl (term404 x x')). Qed.
Lemma lem5288032 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5288033 (x : real) (x' : real) : (term407 x x') = (term408 x x').
Proof. exact (MK_COMB (@lem5288032) (@lem5288031 x x')). Qed.
Lemma lem5288034 (x : real) (y : real) : (term400 x y) = (term400 x y).
Proof. exact (eq_refl (term400 x y)). Qed.
Lemma lem5288035 (x' : real) (x : real) (y : real) : ((term404 x x') = (term400 x y)) = ((term400 x x') = (term400 x y)).
Proof. exact (MK_COMB (@lem5288033 x x') (@lem5288034 x y)). Qed.
Lemma lem5288036 (x' : real) (x : real) (y : real) : ((term404 x x') = (term404 x y)) = ((term400 x x') = (term400 x y)).
Proof. exact (TRANS (@lem5288030 x' x y) (@lem5288035 x' x y)). Qed.
Lemma lem5288037 (x : real) (x' : real) (y : real) (h1 : x' = y) : (term400 x x') = (term400 x y).
Proof. exact (EQ_MP (@lem5288036 x' x y) (@lem5288027 x x' y h1)). Qed.
Lemma lem5288038 (x : real) (x'' : real) (x' : real) (y : real) (h1 : term301 x' x y x'') (h2 : x' = y) : term400 x y.
Proof. exact (EQ_MP (@lem5288037 x x' y h2) (@lem5287969 x' x y x'' h1)). Qed.
Lemma lem5288067 (y : real) : (term403 y) = (term403 y).
Proof. exact (eq_refl (term403 y)). Qed.
Lemma lem5288068 (x'' : real) (y : real) (h1 : x'' = y) : (term404 y x'') = (term405 y).
Proof. exact (MK_COMB (@lem5288067 y) (@lem5287640 x'' y h1)). Qed.
Lemma lem5288069 (y : real) : (term405 y) = (term406 y).
Proof. exact (eq_refl (term405 y)). Qed.
Lemma lem5288070 (y : real) (x'' : real) : (term407 y x'') = (term407 y x'').
Proof. exact (eq_refl (term407 y x'')). Qed.
Lemma lem5288071 (x'' : real) (y : real) : ((term404 y x'') = (term405 y)) = ((term404 y x'') = (term406 y)).
Proof. exact (MK_COMB (@lem5288070 y x'') (@lem5288069 y)). Qed.
Lemma lem5288072 (y : real) (x'' : real) : (term404 y x'') = (term400 y x'').
Proof. exact (eq_refl (term404 y x'')). Qed.
Lemma lem5288073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5288074 (y : real) (x'' : real) : (term407 y x'') = (term408 y x'').
Proof. exact (MK_COMB (@lem5288073) (@lem5288072 y x'')). Qed.
Lemma lem5288075 (y : real) : (term406 y) = (term406 y).
Proof. exact (eq_refl (term406 y)). Qed.
Lemma lem5288076 (x'' : real) (y : real) : ((term404 y x'') = (term406 y)) = ((term400 y x'') = (term406 y)).
Proof. exact (MK_COMB (@lem5288074 y x'') (@lem5288075 y)). Qed.
Lemma lem5288077 (x'' : real) (y : real) : ((term404 y x'') = (term405 y)) = ((term400 y x'') = (term406 y)).
Proof. exact (TRANS (@lem5288071 x'' y) (@lem5288076 x'' y)). Qed.
Lemma lem5288078 (x'' : real) (y : real) (h1 : x'' = y) : (term400 y x'') = (term406 y).
Proof. exact (EQ_MP (@lem5288077 x'' y) (@lem5288068 x'' y h1)). Qed.
Lemma lem5288135 (_69174 : real) (_69173 : real) (h1 : term193) : term195 _69174 _69173.
Proof. exact (EQ_MP (@lem5287572 _69174 _69173) (@lem5287571 _69173 _69174 h1)). Qed.
Lemma lem5288149 (x' : real) (x : real) (x'' : real) (y : real) (h1 : term301 x' x y x'') (h2 : x'' = y) : term406 y.
Proof. exact (EQ_MP (@lem5288078 x'' y h2) (@lem5287634 x' x y x'' h1)). Qed.
Lemma lem5288165 (x : real) (h1 : term406 x) : term406 x.
Proof. exact (h1). Qed.
Lemma lem5288166 (x : real) (h1 : term406 x) : term409 x.
Proof. exact (fun h0 : real_le x x => @lem5288165 x h1). Qed.
Lemma lem5288168 (p : Prop) : (term410 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5288169 (x : real) : (term409 x) = (term406 x).
Proof. exact (@lem5288168 (real_le x x)). Qed.
Lemma lem5288170 (x : real) (h1 : term406 x) : term406 x.
Proof. exact (EQ_MP (@lem5288169 x) (@lem5288166 x h1)). Qed.
Lemma lem5288181 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5288182 (_69168 : real) (_69167 : real) : (term195 _69167 _69168) = (term195 _69168 _69167).
Proof. exact (@lem5288181 (real_le _69167 _69168) (real_le _69168 _69167)). Qed.
Lemma lem5288188 (_69168 : real) (_69167 : real) : (term411 _69168 _69167) = (term411 _69168 _69167).
Proof. exact (eq_refl (term411 _69168 _69167)). Qed.
Lemma lem5288189 (_69168 : real) (_69167 : real) : ((term195 _69168 _69167) = (term195 _69167 _69168)) = ((term195 _69168 _69167) = (term195 _69168 _69167)).
Proof. exact (MK_COMB (@lem5288188 _69168 _69167) (@lem5288182 _69168 _69167)). Qed.
Lemma lem5288191 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5288192 (x : Prop) : (x = x) = True.
Proof. exact (@lem5288191 Prop x). Qed.
Lemma lem5288193 (_69168 : real) (_69167 : real) : ((term195 _69168 _69167) = (term195 _69168 _69167)) = True.
Proof. exact (@lem5288192 (term195 _69168 _69167)). Qed.
Lemma lem5288194 (_69167 : real) (_69168 : real) : ((term195 _69168 _69167) = (term195 _69167 _69168)) = True.
Proof. exact (TRANS (@lem5288189 _69168 _69167) (@lem5288193 _69168 _69167)). Qed.
Lemma lem5288195 (_69167 : real) (_69168 : real) : True = ((term195 _69168 _69167) = (term195 _69167 _69168)).
Proof. exact (SYM (@lem5288194 _69167 _69168)). Qed.
Lemma lem5288196 (_69167 : real) (_69168 : real) : (term195 _69168 _69167) = (term195 _69167 _69168).
Proof. exact (EQ_MP (@lem5288195 _69167 _69168) (@lem0)). Qed.
Lemma lem5288197 (_69167 : real) (_69168 : real) (h1 : term193) : term195 _69167 _69168.
Proof. exact (EQ_MP (@lem5288196 _69167 _69168) (@lem5287763 _69168 _69167 h1)). Qed.
Lemma lem5288199 (b : Prop) (a : Prop) : (a \/ b) = (term412 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5288202 (_69168 : real) (_69167 : real) : (term195 _69167 _69168) = (term413 _69168 _69167).
Proof. exact (@lem5288199 (real_le _69167 _69168) (real_le _69168 _69167)). Qed.
Lemma lem5288205 (_69168 : real) (_69167 : real) (h1 : term193) : term413 _69168 _69167.
Proof. exact (EQ_MP (@lem5288202 _69168 _69167) (@lem5288197 _69167 _69168 h1)). Qed.
Lemma lem5288206 (x : real) (h1 : term193) : term414 x.
Proof. exact (@lem5288205 x x h1). Qed.
Lemma lem5288209 (x : real) (h1 : term193) (h2 : term406 x) : real_le x x.
Proof. exact (@lem5288206 x h1 (@lem5288170 x h2)). Qed.
Lemma lem5288210 (x : real) (h1 : term193) : term414 x.
Proof. exact (fun h0 : term406 x => @lem5288209 x h1 h0). Qed.
Lemma lem5288212 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5288213 (x : real) : (term414 x) = (real_le x x).
Proof. exact (@lem5288212 (real_le x x)). Qed.
Lemma lem5288214 (x : real) (h1 : term193) : real_le x x.
Proof. exact (EQ_MP (@lem5288213 x) (@lem5288210 x h1)). Qed.
Lemma lem5288217 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5288219 (x : real) : (term406 x) = (term416 x).
Proof. exact (@lem5288217 (real_le x x)). Qed.
Lemma lem5288222 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term301 x' x y x'') (h2 : x' = x) : term416 x.
Proof. exact (EQ_MP (@lem5288219 x) (@lem5287790 y x'' x' x h1 h2)). Qed.
Lemma lem5288225 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (@lem5288222 y x'' x' x h2 h3 (@lem5288214 x h1)). Qed.
Lemma lem5288226 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : term417.
Proof. exact (fun h0 : ~ False => @lem5288225 y x'' x' x h1 h2 h3). Qed.
Lemma lem5288228 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5288229 : term417 = False.
Proof. exact (@lem5288228 False). Qed.
Lemma lem5288233 (x : real) (h1 : term406 x) : term406 x.
Proof. exact (h1). Qed.
Lemma lem5288234 (x : real) (h1 : term406 x) : term409 x.
Proof. exact (fun h0 : real_le x x => @lem5288233 x h1). Qed.
Lemma lem5288236 (p : Prop) : (term410 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5288237 (x : real) : (term409 x) = (term406 x).
Proof. exact (@lem5288236 (real_le x x)). Qed.
Lemma lem5288238 (x : real) (h1 : term406 x) : term406 x.
Proof. exact (EQ_MP (@lem5288237 x) (@lem5288234 x h1)). Qed.
Lemma lem5288249 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5288250 (_69170 : real) (_69169 : real) : (term195 _69169 _69170) = (term195 _69170 _69169).
Proof. exact (@lem5288249 (real_le _69169 _69170) (real_le _69170 _69169)). Qed.
Lemma lem5288256 (_69170 : real) (_69169 : real) : (term411 _69170 _69169) = (term411 _69170 _69169).
Proof. exact (eq_refl (term411 _69170 _69169)). Qed.
Lemma lem5288257 (_69170 : real) (_69169 : real) : ((term195 _69170 _69169) = (term195 _69169 _69170)) = ((term195 _69170 _69169) = (term195 _69170 _69169)).
Proof. exact (MK_COMB (@lem5288256 _69170 _69169) (@lem5288250 _69170 _69169)). Qed.
Lemma lem5288259 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5288260 (x : Prop) : (x = x) = True.
Proof. exact (@lem5288259 Prop x). Qed.
Lemma lem5288261 (_69170 : real) (_69169 : real) : ((term195 _69170 _69169) = (term195 _69170 _69169)) = True.
Proof. exact (@lem5288260 (term195 _69170 _69169)). Qed.
Lemma lem5288262 (_69169 : real) (_69170 : real) : ((term195 _69170 _69169) = (term195 _69169 _69170)) = True.
Proof. exact (TRANS (@lem5288257 _69170 _69169) (@lem5288261 _69170 _69169)). Qed.
Lemma lem5288263 (_69169 : real) (_69170 : real) : True = ((term195 _69170 _69169) = (term195 _69169 _69170)).
Proof. exact (SYM (@lem5288262 _69169 _69170)). Qed.
Lemma lem5288264 (_69169 : real) (_69170 : real) : (term195 _69170 _69169) = (term195 _69169 _69170).
Proof. exact (EQ_MP (@lem5288263 _69169 _69170) (@lem0)). Qed.
Lemma lem5288265 (_69169 : real) (_69170 : real) (h1 : term193) : term195 _69169 _69170.
Proof. exact (EQ_MP (@lem5288264 _69169 _69170) (@lem5287887 _69170 _69169 h1)). Qed.
Lemma lem5288267 (b : Prop) (a : Prop) : (a \/ b) = (term412 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5288270 (_69170 : real) (_69169 : real) : (term195 _69169 _69170) = (term413 _69170 _69169).
Proof. exact (@lem5288267 (real_le _69169 _69170) (real_le _69170 _69169)). Qed.
Lemma lem5288273 (_69170 : real) (_69169 : real) (h1 : term193) : term413 _69170 _69169.
Proof. exact (EQ_MP (@lem5288270 _69170 _69169) (@lem5288265 _69169 _69170 h1)). Qed.
Lemma lem5288274 (x : real) (h1 : term193) : term414 x.
Proof. exact (@lem5288273 x x h1). Qed.
Lemma lem5288277 (x : real) (h1 : term193) (h2 : term406 x) : real_le x x.
Proof. exact (@lem5288274 x h1 (@lem5288238 x h2)). Qed.
Lemma lem5288278 (x : real) (h1 : term193) : term414 x.
Proof. exact (fun h0 : term406 x => @lem5288277 x h1 h0). Qed.
Lemma lem5288280 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5288281 (x : real) : (term414 x) = (real_le x x).
Proof. exact (@lem5288280 (real_le x x)). Qed.
Lemma lem5288282 (x : real) (h1 : term193) : real_le x x.
Proof. exact (EQ_MP (@lem5288281 x) (@lem5288278 x h1)). Qed.
Lemma lem5288285 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5288287 (x : real) : (term406 x) = (term416 x).
Proof. exact (@lem5288285 (real_le x x)). Qed.
Lemma lem5288290 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term301 x' x y x'') (h2 : x' = x) : term416 x.
Proof. exact (EQ_MP (@lem5288287 x) (@lem5287914 y x'' x' x h1 h2)). Qed.
Lemma lem5288293 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (@lem5288290 y x'' x' x h2 h3 (@lem5288282 x h1)). Qed.
Lemma lem5288294 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : term417.
Proof. exact (fun h0 : ~ False => @lem5288293 y x'' x' x h1 h2 h3). Qed.
Lemma lem5288296 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5288297 : term417 = False.
Proof. exact (@lem5288296 False). Qed.
Lemma lem5288300 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term301 x' x y x'') (h2 : x'' = x) : term400 y x.
Proof. exact (EQ_MP (@lem5287954 y x'' x h2) (@lem5287620 x' x y x'' h1)). Qed.
Lemma lem5288301 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term301 x' x y x'') (h2 : x'' = x) : term418 y x.
Proof. exact (fun h0 : real_le y x => @lem5288300 x' y x'' x h1 h2). Qed.
Lemma lem5288303 (p : Prop) : (term410 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5288304 (y : real) (x : real) : (term418 y x) = (term400 y x).
Proof. exact (@lem5288303 (real_le y x)). Qed.
Lemma lem5288305 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term301 x' x y x'') (h2 : x'' = x) : term400 y x.
Proof. exact (EQ_MP (@lem5288304 y x) (@lem5288301 x' y x'' x h1 h2)). Qed.
Lemma lem5288316 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5288317 (_69172 : real) (_69171 : real) : (term195 _69171 _69172) = (term195 _69172 _69171).
Proof. exact (@lem5288316 (real_le _69171 _69172) (real_le _69172 _69171)). Qed.
Lemma lem5288323 (_69172 : real) (_69171 : real) : (term411 _69172 _69171) = (term411 _69172 _69171).
Proof. exact (eq_refl (term411 _69172 _69171)). Qed.
Lemma lem5288324 (_69172 : real) (_69171 : real) : ((term195 _69172 _69171) = (term195 _69171 _69172)) = ((term195 _69172 _69171) = (term195 _69172 _69171)).
Proof. exact (MK_COMB (@lem5288323 _69172 _69171) (@lem5288317 _69172 _69171)). Qed.
Lemma lem5288326 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5288327 (x : Prop) : (x = x) = True.
Proof. exact (@lem5288326 Prop x). Qed.
Lemma lem5288328 (_69172 : real) (_69171 : real) : ((term195 _69172 _69171) = (term195 _69172 _69171)) = True.
Proof. exact (@lem5288327 (term195 _69172 _69171)). Qed.
Lemma lem5288329 (_69171 : real) (_69172 : real) : ((term195 _69172 _69171) = (term195 _69171 _69172)) = True.
Proof. exact (TRANS (@lem5288324 _69172 _69171) (@lem5288328 _69172 _69171)). Qed.
Lemma lem5288330 (_69171 : real) (_69172 : real) : True = ((term195 _69172 _69171) = (term195 _69171 _69172)).
Proof. exact (SYM (@lem5288329 _69171 _69172)). Qed.
Lemma lem5288331 (_69171 : real) (_69172 : real) : (term195 _69172 _69171) = (term195 _69171 _69172).
Proof. exact (EQ_MP (@lem5288330 _69171 _69172) (@lem0)). Qed.
Lemma lem5288332 (_69171 : real) (_69172 : real) (h1 : term193) : term195 _69171 _69172.
Proof. exact (EQ_MP (@lem5288331 _69171 _69172) (@lem5288011 _69172 _69171 h1)). Qed.
Lemma lem5288334 (b : Prop) (a : Prop) : (a \/ b) = (term412 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5288337 (_69172 : real) (_69171 : real) : (term195 _69171 _69172) = (term413 _69172 _69171).
Proof. exact (@lem5288334 (real_le _69171 _69172) (real_le _69172 _69171)). Qed.
Lemma lem5288340 (_69172 : real) (_69171 : real) (h1 : term193) : term413 _69172 _69171.
Proof. exact (EQ_MP (@lem5288337 _69172 _69171) (@lem5288332 _69171 _69172 h1)). Qed.
Lemma lem5288341 (x : real) (y : real) (h1 : term193) : term413 x y.
Proof. exact (@lem5288340 x y h1). Qed.
Lemma lem5288344 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x'' = x) : real_le x y.
Proof. exact (@lem5288341 x y h1 (@lem5288305 x' y x'' x h2 h3)). Qed.
Lemma lem5288345 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x'' = x) : term419 x y.
Proof. exact (fun h0 : term400 x y => @lem5288344 x' y x'' x h1 h2 h3). Qed.
Lemma lem5288347 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5288348 (x : real) (y : real) : (term419 x y) = (real_le x y).
Proof. exact (@lem5288347 (real_le x y)). Qed.
Lemma lem5288349 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x'' = x) : real_le x y.
Proof. exact (EQ_MP (@lem5288348 x y) (@lem5288345 x' y x'' x h1 h2 h3)). Qed.
Lemma lem5288352 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5288354 (x : real) (y : real) : (term400 x y) = (term420 x y).
Proof. exact (@lem5288352 (real_le x y)). Qed.
Lemma lem5288357 (x : real) (x'' : real) (x' : real) (y : real) (h1 : term301 x' x y x'') (h2 : x' = y) : term420 x y.
Proof. exact (EQ_MP (@lem5288354 x y) (@lem5288038 x x'' x' y h1 h2)). Qed.
Lemma lem5288360 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : False.
Proof. exact (@lem5288357 x x'' x' y h2 h3 (@lem5288349 x' y x'' x h1 h2 h4)). Qed.
Lemma lem5288361 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : term417.
Proof. exact (fun h0 : ~ False => @lem5288360 x' y x'' x h1 h2 h3 h4). Qed.
Lemma lem5288363 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5288364 : term417 = False.
Proof. exact (@lem5288363 False). Qed.
Lemma lem5288368 (y : real) (h1 : term406 y) : term406 y.
Proof. exact (h1). Qed.
Lemma lem5288369 (y : real) (h1 : term406 y) : term409 y.
Proof. exact (fun h0 : real_le y y => @lem5288368 y h1). Qed.
Lemma lem5288371 (p : Prop) : (term410 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5288372 (y : real) : (term409 y) = (term406 y).
Proof. exact (@lem5288371 (real_le y y)). Qed.
Lemma lem5288373 (y : real) (h1 : term406 y) : term406 y.
Proof. exact (EQ_MP (@lem5288372 y) (@lem5288369 y h1)). Qed.
Lemma lem5288384 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5288385 (_69174 : real) (_69173 : real) : (term195 _69173 _69174) = (term195 _69174 _69173).
Proof. exact (@lem5288384 (real_le _69173 _69174) (real_le _69174 _69173)). Qed.
Lemma lem5288391 (_69174 : real) (_69173 : real) : (term411 _69174 _69173) = (term411 _69174 _69173).
Proof. exact (eq_refl (term411 _69174 _69173)). Qed.
Lemma lem5288392 (_69174 : real) (_69173 : real) : ((term195 _69174 _69173) = (term195 _69173 _69174)) = ((term195 _69174 _69173) = (term195 _69174 _69173)).
Proof. exact (MK_COMB (@lem5288391 _69174 _69173) (@lem5288385 _69174 _69173)). Qed.
Lemma lem5288394 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5288395 (x : Prop) : (x = x) = True.
Proof. exact (@lem5288394 Prop x). Qed.
Lemma lem5288396 (_69174 : real) (_69173 : real) : ((term195 _69174 _69173) = (term195 _69174 _69173)) = True.
Proof. exact (@lem5288395 (term195 _69174 _69173)). Qed.
Lemma lem5288397 (_69173 : real) (_69174 : real) : ((term195 _69174 _69173) = (term195 _69173 _69174)) = True.
Proof. exact (TRANS (@lem5288392 _69174 _69173) (@lem5288396 _69174 _69173)). Qed.
Lemma lem5288398 (_69173 : real) (_69174 : real) : True = ((term195 _69174 _69173) = (term195 _69173 _69174)).
Proof. exact (SYM (@lem5288397 _69173 _69174)). Qed.
Lemma lem5288399 (_69173 : real) (_69174 : real) : (term195 _69174 _69173) = (term195 _69173 _69174).
Proof. exact (EQ_MP (@lem5288398 _69173 _69174) (@lem0)). Qed.
Lemma lem5288400 (_69173 : real) (_69174 : real) (h1 : term193) : term195 _69173 _69174.
Proof. exact (EQ_MP (@lem5288399 _69173 _69174) (@lem5288135 _69174 _69173 h1)). Qed.
Lemma lem5288402 (b : Prop) (a : Prop) : (a \/ b) = (term412 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5288405 (_69174 : real) (_69173 : real) : (term195 _69173 _69174) = (term413 _69174 _69173).
Proof. exact (@lem5288402 (real_le _69173 _69174) (real_le _69174 _69173)). Qed.
Lemma lem5288408 (_69174 : real) (_69173 : real) (h1 : term193) : term413 _69174 _69173.
Proof. exact (EQ_MP (@lem5288405 _69174 _69173) (@lem5288400 _69173 _69174 h1)). Qed.
Lemma lem5288409 (y : real) (h1 : term193) : term414 y.
Proof. exact (@lem5288408 y y h1). Qed.
Lemma lem5288412 (y : real) (h1 : term193) (h2 : term406 y) : real_le y y.
Proof. exact (@lem5288409 y h1 (@lem5288373 y h2)). Qed.
Lemma lem5288413 (y : real) (h1 : term193) : term414 y.
Proof. exact (fun h0 : term406 y => @lem5288412 y h1 h0). Qed.
Lemma lem5288415 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5288416 (y : real) : (term414 y) = (real_le y y).
Proof. exact (@lem5288415 (real_le y y)). Qed.
Lemma lem5288417 (y : real) (h1 : term193) : real_le y y.
Proof. exact (EQ_MP (@lem5288416 y) (@lem5288413 y h1)). Qed.
Lemma lem5288420 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5288422 (y : real) : (term406 y) = (term416 y).
Proof. exact (@lem5288420 (real_le y y)). Qed.
Lemma lem5288425 (x' : real) (x : real) (x'' : real) (y : real) (h1 : term301 x' x y x'') (h2 : x'' = y) : term416 y.
Proof. exact (EQ_MP (@lem5288422 y) (@lem5288149 x' x x'' y h1 h2)). Qed.
Lemma lem5288428 (x' : real) (x : real) (x'' : real) (y : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x'' = y) : False.
Proof. exact (@lem5288425 x' x x'' y h2 h3 (@lem5288417 y h1)). Qed.
Lemma lem5288429 (x' : real) (x : real) (x'' : real) (y : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x'' = y) : term417.
Proof. exact (fun h0 : ~ False => @lem5288428 x' x x'' y h1 h2 h3). Qed.
Lemma lem5288431 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5288432 : term417 = False.
Proof. exact (@lem5288431 False). Qed.
Lemma lem5288456 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5288457 (y : real) : y = y.
Proof. exact (@lem5288456 y). Qed.
Lemma lem5288458 (y : real) : term421 y.
Proof. exact (fun h0 : term422 y => @lem5288457 y). Qed.
Lemma lem5288460 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5288461 (y : real) : (term421 y) = (y = y).
Proof. exact (@lem5288460 (y = y)). Qed.
Lemma lem5288462 (y : real) : y = y.
Proof. exact (EQ_MP (@lem5288461 y) (@lem5288458 y)). Qed.
Lemma lem5288464 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5288465 (x : real) : term421 x.
Proof. exact (fun h0 : term422 x => @lem5288464 x). Qed.
Lemma lem5288467 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5288468 (x : real) : (term421 x) = (x = x).
Proof. exact (@lem5288467 (x = x)). Qed.
Lemma lem5288469 (x : real) : x = x.
Proof. exact (EQ_MP (@lem5288468 x) (@lem5288465 x)). Qed.
Lemma lem5288472 (x : real) (h1 : term406 x) : term406 x.
Proof. exact (h1). Qed.
Lemma lem5288473 (x : real) (h1 : term406 x) : term409 x.
Proof. exact (fun h0 : real_le x x => @lem5288472 x h1). Qed.
Lemma lem5288475 (p : Prop) : (term410 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5288476 (x : real) : (term409 x) = (term406 x).
Proof. exact (@lem5288475 (real_le x x)). Qed.
Lemma lem5288477 (x : real) (h1 : term406 x) : term406 x.
Proof. exact (EQ_MP (@lem5288476 x) (@lem5288473 x h1)). Qed.
Lemma lem5288488 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5288489 (_69176 : real) (_69175 : real) : (term195 _69175 _69176) = (term195 _69176 _69175).
Proof. exact (@lem5288488 (real_le _69175 _69176) (real_le _69176 _69175)). Qed.
Lemma lem5288495 (_69176 : real) (_69175 : real) : (term411 _69176 _69175) = (term411 _69176 _69175).
Proof. exact (eq_refl (term411 _69176 _69175)). Qed.
Lemma lem5288496 (_69176 : real) (_69175 : real) : ((term195 _69176 _69175) = (term195 _69175 _69176)) = ((term195 _69176 _69175) = (term195 _69176 _69175)).
Proof. exact (MK_COMB (@lem5288495 _69176 _69175) (@lem5288489 _69176 _69175)). Qed.
Lemma lem5288498 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5288499 (x : Prop) : (x = x) = True.
Proof. exact (@lem5288498 Prop x). Qed.
Lemma lem5288500 (_69176 : real) (_69175 : real) : ((term195 _69176 _69175) = (term195 _69176 _69175)) = True.
Proof. exact (@lem5288499 (term195 _69176 _69175)). Qed.
Lemma lem5288501 (_69175 : real) (_69176 : real) : ((term195 _69176 _69175) = (term195 _69175 _69176)) = True.
Proof. exact (TRANS (@lem5288496 _69176 _69175) (@lem5288500 _69176 _69175)). Qed.
Lemma lem5288502 (_69175 : real) (_69176 : real) : True = ((term195 _69176 _69175) = (term195 _69175 _69176)).
Proof. exact (SYM (@lem5288501 _69175 _69176)). Qed.
Lemma lem5288503 (_69175 : real) (_69176 : real) : (term195 _69176 _69175) = (term195 _69175 _69176).
Proof. exact (EQ_MP (@lem5288502 _69175 _69176) (@lem0)). Qed.
Lemma lem5288504 (_69175 : real) (_69176 : real) (h1 : term193) : term195 _69175 _69176.
Proof. exact (EQ_MP (@lem5288503 _69175 _69176) (@lem5287646 _69176 _69175 h1)). Qed.
Lemma lem5288506 (b : Prop) (a : Prop) : (a \/ b) = (term412 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5288509 (_69176 : real) (_69175 : real) : (term195 _69175 _69176) = (term413 _69176 _69175).
Proof. exact (@lem5288506 (real_le _69175 _69176) (real_le _69176 _69175)). Qed.
Lemma lem5288512 (_69176 : real) (_69175 : real) (h1 : term193) : term413 _69176 _69175.
Proof. exact (EQ_MP (@lem5288509 _69176 _69175) (@lem5288504 _69175 _69176 h1)). Qed.
Lemma lem5288513 (x : real) (h1 : term193) : term414 x.
Proof. exact (@lem5288512 x x h1). Qed.
Lemma lem5288516 (x : real) (h1 : term193) (h2 : term406 x) : real_le x x.
Proof. exact (@lem5288513 x h1 (@lem5288477 x h2)). Qed.
Lemma lem5288517 (x : real) (h1 : term193) : term414 x.
Proof. exact (fun h0 : term406 x => @lem5288516 x h1 h0). Qed.
Lemma lem5288519 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5288520 (x : real) : (term414 x) = (real_le x x).
Proof. exact (@lem5288519 (real_le x x)). Qed.
Lemma lem5288521 (x : real) (h1 : term193) : real_le x x.
Proof. exact (EQ_MP (@lem5288520 x) (@lem5288517 x h1)). Qed.
Lemma lem5288544 (q : Prop) (p : Prop) (r : Prop) : (term423 p q r) = (term423 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5288545 (y : real) (_69177 : real) (x : real) : (term424 y _69177 x) = (term402 y _69177 x).
Proof. exact (@lem5288544 (term394 _69177 x) (term400 _69177 y) (term400 _69177 x)). Qed.
Lemma lem5288561 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5288562 (x : real) (_69177 : real) (y : real) : (term239 y _69177 x) = (term239 x _69177 y).
Proof. exact (@lem5288561 (term400 _69177 x) (term400 _69177 y)). Qed.
Lemma lem5288568 (_69177 : real) (x : real) : (term425 _69177 x) = (term425 _69177 x).
Proof. exact (eq_refl (term425 _69177 x)). Qed.
Lemma lem5288569 (x : real) (_69177 : real) (y : real) : (term402 y _69177 x) = (term401 x _69177 y).
Proof. exact (MK_COMB (@lem5288568 _69177 x) (@lem5288562 x _69177 y)). Qed.
Lemma lem5288580 (x : real) (_69177 : real) (y : real) : (term424 y _69177 x) = (term401 x _69177 y).
Proof. exact (TRANS (@lem5288545 y _69177 x) (@lem5288569 x _69177 y)). Qed.
Lemma lem5288581 (x : real) (_69177 : real) (y : real) : (term426 x _69177 y) = (term426 x _69177 y).
Proof. exact (eq_refl (term426 x _69177 y)). Qed.
Lemma lem5288582 (x : real) (_69177 : real) (y : real) : ((term401 x _69177 y) = (term424 y _69177 x)) = ((term401 x _69177 y) = (term401 x _69177 y)).
Proof. exact (MK_COMB (@lem5288581 x _69177 y) (@lem5288580 x _69177 y)). Qed.
Lemma lem5288584 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5288585 (x : Prop) : (x = x) = True.
Proof. exact (@lem5288584 Prop x). Qed.
Lemma lem5288586 (x : real) (_69177 : real) (y : real) : ((term401 x _69177 y) = (term401 x _69177 y)) = True.
Proof. exact (@lem5288585 (term401 x _69177 y)). Qed.
Lemma lem5288587 (y : real) (_69177 : real) (x : real) : ((term401 x _69177 y) = (term424 y _69177 x)) = True.
Proof. exact (TRANS (@lem5288582 x _69177 y) (@lem5288586 x _69177 y)). Qed.
Lemma lem5288588 (y : real) (_69177 : real) (x : real) : True = ((term401 x _69177 y) = (term424 y _69177 x)).
Proof. exact (SYM (@lem5288587 y _69177 x)). Qed.
Lemma lem5288589 (y : real) (_69177 : real) (x : real) : (term401 x _69177 y) = (term424 y _69177 x).
Proof. exact (EQ_MP (@lem5288588 y _69177 x) (@lem0)). Qed.
Lemma lem5288590 (_69177 : real) (x : real) (y : real) (h1 : term253 x y) : term424 y _69177 x.
Proof. exact (EQ_MP (@lem5288589 y _69177 x) (@lem5287656 _69177 x y h1)). Qed.
Lemma lem5288592 (b : Prop) (a : Prop) : (a \/ b) = (term412 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5288593 (x : real) (_69177 : real) (y : real) : (term424 y _69177 x) = (term427 x _69177 y).
Proof. exact (@lem5288592 (term428 _69177 x) (term400 _69177 y)). Qed.
Lemma lem5288595 (a : Prop) (b : Prop) : (term429 a b) = (term430 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5288596 (_69177 : real) (x : real) : (term431 _69177 x) = (term432 _69177 x).
Proof. exact (@lem5288595 (term394 _69177 x) (term400 _69177 x)). Qed.
Lemma lem5288598 (a : Prop) : (term433 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5288599 (_69177 : real) (x : real) : (term434 _69177 x) = (_69177 = x).
Proof. exact (@lem5288598 (_69177 = x)). Qed.
Lemma lem5288600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5288601 (_69177 : real) (x : real) : (term435 _69177 x) = (term436 _69177 x).
Proof. exact (MK_COMB (@lem5288600) (@lem5288599 _69177 x)). Qed.
Lemma lem5288603 (a : Prop) : (term433 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5288604 (_69177 : real) (x : real) : (term437 _69177 x) = (real_le _69177 x).
Proof. exact (@lem5288603 (real_le _69177 x)). Qed.
Lemma lem5288605 (_69177 : real) (x : real) : (term432 _69177 x) = (term438 _69177 x).
Proof. exact (MK_COMB (@lem5288601 _69177 x) (@lem5288604 _69177 x)). Qed.
Lemma lem5288606 (_69177 : real) (x : real) : (term431 _69177 x) = (term438 _69177 x).
Proof. exact (TRANS (@lem5288596 _69177 x) (@lem5288605 _69177 x)). Qed.
Lemma lem5288607 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5288608 (_69177 : real) (x : real) : (term439 _69177 x) = (term440 _69177 x).
Proof. exact (MK_COMB (@lem5288607) (@lem5288606 _69177 x)). Qed.
Lemma lem5288609 (_69177 : real) (y : real) : (term400 _69177 y) = (term400 _69177 y).
Proof. exact (eq_refl (term400 _69177 y)). Qed.
Lemma lem5288610 (x : real) (_69177 : real) (y : real) : (term427 x _69177 y) = (term441 x _69177 y).
Proof. exact (MK_COMB (@lem5288608 _69177 x) (@lem5288609 _69177 y)). Qed.
Lemma lem5288611 (x : real) (_69177 : real) (y : real) : (term424 y _69177 x) = (term441 x _69177 y).
Proof. exact (TRANS (@lem5288593 x _69177 y) (@lem5288610 x _69177 y)). Qed.
Lemma lem5288613 (x : real) (h1 : term193) : term442 x.
Proof. exact (conj (@lem5288469 x) (@lem5288521 x h1)). Qed.
Lemma lem5288615 (_69177 : real) (x : real) (y : real) (h1 : term253 x y) : term441 x _69177 y.
Proof. exact (EQ_MP (@lem5288611 x _69177 y) (@lem5288590 _69177 x y h1)). Qed.
Lemma lem5288616 (x : real) (y : real) (h1 : term253 x y) : term443 x y.
Proof. exact (@lem5288615 x x y h1). Qed.
Lemma lem5288619 (x : real) (y : real) (h1 : term193) (h2 : term253 x y) : term400 x y.
Proof. exact (@lem5288616 x y h2 (@lem5288613 x h1)). Qed.
Lemma lem5288620 (x : real) (y : real) (h1 : term193) (h2 : term253 x y) : term418 x y.
Proof. exact (fun h0 : real_le x y => @lem5288619 x y h1 h2). Qed.
Lemma lem5288622 (p : Prop) : (term410 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5288623 (x : real) (y : real) : (term418 x y) = (term400 x y).
Proof. exact (@lem5288622 (real_le x y)). Qed.
Lemma lem5288624 (x : real) (y : real) (h1 : term193) (h2 : term253 x y) : term400 x y.
Proof. exact (EQ_MP (@lem5288623 x y) (@lem5288620 x y h1 h2)). Qed.
Lemma lem5288626 (_69176 : real) (_69175 : real) (h1 : term193) : term413 _69176 _69175.
Proof. exact (EQ_MP (@lem5288509 _69176 _69175) (@lem5288504 _69175 _69176 h1)). Qed.
Lemma lem5288627 (y : real) (x : real) (h1 : term193) : term413 y x.
Proof. exact (@lem5288626 y x h1). Qed.
Lemma lem5288630 (x : real) (y : real) (h1 : term193) (h2 : term253 x y) : real_le y x.
Proof. exact (@lem5288627 y x h1 (@lem5288624 x y h1 h2)). Qed.
Lemma lem5288631 (x : real) (y : real) (h1 : term193) (h2 : term253 x y) : term419 y x.
Proof. exact (fun h0 : term400 y x => @lem5288630 x y h1 h2). Qed.
Lemma lem5288633 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5288634 (y : real) (x : real) : (term419 y x) = (real_le y x).
Proof. exact (@lem5288633 (real_le y x)). Qed.
Lemma lem5288635 (x : real) (y : real) (h1 : term193) (h2 : term253 x y) : real_le y x.
Proof. exact (EQ_MP (@lem5288634 y x) (@lem5288631 x y h1 h2)). Qed.
Lemma lem5288638 (y : real) (h1 : term406 y) : term406 y.
Proof. exact (h1). Qed.
Lemma lem5288639 (y : real) (h1 : term406 y) : term409 y.
Proof. exact (fun h0 : real_le y y => @lem5288638 y h1). Qed.
Lemma lem5288641 (p : Prop) : (term410 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5288642 (y : real) : (term409 y) = (term406 y).
Proof. exact (@lem5288641 (real_le y y)). Qed.
Lemma lem5288643 (y : real) (h1 : term406 y) : term406 y.
Proof. exact (EQ_MP (@lem5288642 y) (@lem5288639 y h1)). Qed.
Lemma lem5288645 (_69176 : real) (_69175 : real) (h1 : term193) : term413 _69176 _69175.
Proof. exact (EQ_MP (@lem5288509 _69176 _69175) (@lem5288504 _69175 _69176 h1)). Qed.
Lemma lem5288646 (y : real) (h1 : term193) : term414 y.
Proof. exact (@lem5288645 y y h1). Qed.
Lemma lem5288649 (y : real) (h1 : term193) (h2 : term406 y) : real_le y y.
Proof. exact (@lem5288646 y h1 (@lem5288643 y h2)). Qed.
Lemma lem5288650 (y : real) (h1 : term193) : term414 y.
Proof. exact (fun h0 : term406 y => @lem5288649 y h1 h0). Qed.
Lemma lem5288652 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5288653 (y : real) : (term414 y) = (real_le y y).
Proof. exact (@lem5288652 (real_le y y)). Qed.
Lemma lem5288654 (y : real) (h1 : term193) : real_le y y.
Proof. exact (EQ_MP (@lem5288653 y) (@lem5288650 y h1)). Qed.
Lemma lem5288656 (a : Prop) (b : Prop) : (term444 a b) = (term445 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5288657 (x : real) (_69177 : real) (y : real) : (term239 x _69177 y) = (term238 x _69177 y).
Proof. exact (@lem5288656 (real_le _69177 x) (real_le _69177 y)). Qed.
Lemma lem5288658 (_69177 : real) (y : real) : (term425 _69177 y) = (term425 _69177 y).
Proof. exact (eq_refl (term425 _69177 y)). Qed.
Lemma lem5288659 (x : real) (_69177 : real) (y : real) : (term402 x _69177 y) = (term446 x _69177 y).
Proof. exact (MK_COMB (@lem5288658 _69177 y) (@lem5288657 x _69177 y)). Qed.
Lemma lem5288661 (a : Prop) (b : Prop) : (term444 a b) = (term445 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5288662 (x : real) (_69177 : real) (y : real) : (term446 x _69177 y) = (term447 x _69177 y).
Proof. exact (@lem5288661 (_69177 = y) (term25 x _69177 y)). Qed.
Lemma lem5288663 (x : real) (_69177 : real) (y : real) : (term402 x _69177 y) = (term447 x _69177 y).
Proof. exact (TRANS (@lem5288659 x _69177 y) (@lem5288662 x _69177 y)). Qed.
Lemma lem5288665 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5288666 (x : real) (_69177 : real) (y : real) : (term447 x _69177 y) = (term448 x _69177 y).
Proof. exact (@lem5288665 (term449 x _69177 y)). Qed.
Lemma lem5288667 (x : real) (_69177 : real) (y : real) : (term402 x _69177 y) = (term448 x _69177 y).
Proof. exact (TRANS (@lem5288663 x _69177 y) (@lem5288666 x _69177 y)). Qed.
Lemma lem5288669 (x : real) (y : real) (h1 : term193) (h2 : term253 x y) : term450 x y.
Proof. exact (conj (@lem5288635 x y h1 h2) (@lem5288654 y h1)). Qed.
Lemma lem5288670 (x : real) (y : real) (h1 : term193) (h2 : term253 x y) : term451 x y.
Proof. exact (conj (@lem5288462 y) (@lem5288669 x y h1 h2)). Qed.
Lemma lem5288672 (_69177 : real) (x : real) (y : real) (h1 : term253 x y) : term448 x _69177 y.
Proof. exact (EQ_MP (@lem5288667 x _69177 y) (@lem5287666 _69177 x y h1)). Qed.
Lemma lem5288673 (x : real) (y : real) (h1 : term253 x y) : term452 x y.
Proof. exact (@lem5288672 y x y h1). Qed.
Lemma lem5288676 (x : real) (y : real) (h1 : term193) (h2 : term253 x y) : False.
Proof. exact (@lem5288673 x y h2 (@lem5288670 x y h1 h2)). Qed.
Lemma lem5288677 (x : real) (y : real) (h1 : term193) (h2 : term253 x y) : term417.
Proof. exact (fun h0 : ~ False => @lem5288676 x y h1 h2). Qed.
Lemma lem5288679 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5288680 : term417 = False.
Proof. exact (@lem5288679 False). Qed.
Lemma lem5288681 (x : real) (y : real) (h1 : term193) (h2 : term253 x y) : False.
Proof. exact (EQ_MP (@lem5288680) (@lem5288677 x y h1 h2)). Qed.
Lemma lem5288683 (x' : real) (x : real) (x'' : real) (y : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x'' = y) : False.
Proof. exact (EQ_MP (@lem5288432) (@lem5288429 x' x x'' y h1 h2 h3)). Qed.
Lemma lem5288684 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : False.
Proof. exact (EQ_MP (@lem5288364) (@lem5288361 x' y x'' x h1 h2 h3 h4)). Qed.
Lemma lem5288685 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : (x' = y) = False.
Proof. exact (prop_ext (fun h5 : x' = y => @lem5288684 x' y x'' x h1 h2 h3 h4) (fun h5 : False => @lem5287983 x' y h3)). Qed.
Lemma lem5288687 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : False.
Proof. exact (EQ_MP (@lem5288685 x' y x'' x h1 h2 h3 h4) (@lem5287983 x' y h3)). Qed.
Lemma lem5288688 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5288297) (@lem5288294 y x'' x' x h1 h2 h3)). Qed.
Lemma lem5288689 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5288688 y x'' x' x h1 h2 h3) (fun h4 : False => @lem5287859 x' x h3)). Qed.
Lemma lem5288691 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5288689 y x'' x' x h1 h2 h3) (@lem5287859 x' x h3)). Qed.
Lemma lem5288692 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5288229) (@lem5288226 y x'' x' x h1 h2 h3)). Qed.
Lemma lem5288693 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5288692 y x'' x' x h1 h2 h3) (fun h4 : False => @lem5287735 x' x h3)). Qed.
Lemma lem5288695 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5288693 y x'' x' x h1 h2 h3) (@lem5287735 x' x h3)). Qed.
Lemma lem5288696 (x' : real) (x : real) (x'' : real) (y : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x'' = y) : (x'' = y) = False.
Proof. exact (prop_ext (fun h4 : x'' = y => @lem5288683 x' x x'' y h1 h2 h3) (fun h4 : False => @lem5287640 x'' y h3)). Qed.
Lemma lem5288697 (x' : real) (x : real) (x'' : real) (y : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x'' = y) : False.
Proof. exact (EQ_MP (@lem5288696 x' x x'' y h1 h2 h3) (@lem5287640 x'' y h3)). Qed.
Lemma lem5288698 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : (x'' = x) = False.
Proof. exact (prop_ext (fun h5 : x'' = x => @lem5288687 x' y x'' x h1 h2 h3 h4) (fun h5 : False => @lem5287626 x'' x h4)). Qed.
Lemma lem5288699 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : False.
Proof. exact (EQ_MP (@lem5288698 x' y x'' x h1 h2 h3 h4) (@lem5287626 x'' x h4)). Qed.
Lemma lem5288700 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : (x' = y) = False.
Proof. exact (prop_ext (fun h5 : x' = y => @lem5288699 x' y x'' x h1 h2 h3 h4) (fun h5 : False => @lem5287624 x' y h3)). Qed.
Lemma lem5288701 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : False.
Proof. exact (EQ_MP (@lem5288700 x' y x'' x h1 h2 h3 h4) (@lem5287624 x' y h3)). Qed.
Lemma lem5288702 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5288691 y x'' x' x h1 h2 h3) (fun h4 : False => @lem5287610 x' x h3)). Qed.
Lemma lem5288703 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5288702 y x'' x' x h1 h2 h3) (@lem5287610 x' x h3)). Qed.
Lemma lem5288704 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5288695 y x'' x' x h1 h2 h3) (fun h4 : False => @lem5287596 x' x h3)). Qed.
Lemma lem5288705 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5288704 y x'' x' x h1 h2 h3) (@lem5287596 x' x h3)). Qed.
Lemma lem5288706 (x' : real) (x : real) (x'' : real) (y : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x'' = y) : (x'' = y) = False.
Proof. exact (prop_ext (fun h4 : x'' = y => @lem5288697 x' x x'' y h1 h2 h3) (fun h4 : False => @lem5287504 x'' y h3)). Qed.
Lemma lem5288707 (x' : real) (x : real) (x'' : real) (y : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x'' = y) : False.
Proof. exact (EQ_MP (@lem5288706 x' x x'' y h1 h2 h3) (@lem5287504 x'' y h3)). Qed.
Lemma lem5288708 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : (x'' = x) = False.
Proof. exact (prop_ext (fun h5 : x'' = x => @lem5288701 x' y x'' x h1 h2 h3 h4) (fun h5 : False => @lem5287472 x'' x h4)). Qed.
Lemma lem5288709 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : False.
Proof. exact (EQ_MP (@lem5288708 x' y x'' x h1 h2 h3 h4) (@lem5287472 x'' x h4)). Qed.
Lemma lem5288710 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : (x' = y) = False.
Proof. exact (prop_ext (fun h5 : x' = y => @lem5288709 x' y x'' x h1 h2 h3 h4) (fun h5 : False => @lem5287468 x' y h3)). Qed.
Lemma lem5288711 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : False.
Proof. exact (EQ_MP (@lem5288710 x' y x'' x h1 h2 h3 h4) (@lem5287468 x' y h3)). Qed.
Lemma lem5288712 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5288703 y x'' x' x h1 h2 h3) (fun h4 : False => @lem5287436 x' x h3)). Qed.
Lemma lem5288713 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5288712 y x'' x' x h1 h2 h3) (@lem5287436 x' x h3)). Qed.
Lemma lem5288714 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5288705 y x'' x' x h1 h2 h3) (fun h4 : False => @lem5287404 x' x h3)). Qed.
Lemma lem5288715 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5288714 y x'' x' x h1 h2 h3) (@lem5287404 x' x h3)). Qed.
Lemma lem5288716 (x : real) (y : real) (h1 : term193) (h2 : term253 x y) : term193 = False.
Proof. exact (prop_ext (fun h3 : term193 => @lem5288681 x y h1 h2) (fun h3 : False => @lem5287520 h1)). Qed.
Lemma lem5288717 (x : real) (y : real) (h1 : term193) (h2 : term253 x y) : False.
Proof. exact (EQ_MP (@lem5288716 x y h1 h2) (@lem5287520 h1)). Qed.
Lemma lem5288718 (x' : real) (x : real) (x'' : real) (y : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x'' = y) : (x'' = y) = False.
Proof. exact (prop_ext (fun h4 : x'' = y => @lem5288707 x' x x'' y h1 h2 h3) (fun h4 : False => @lem5287504 x'' y h3)). Qed.
Lemma lem5288719 (x' : real) (x : real) (x'' : real) (y : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x'' = y) : False.
Proof. exact (EQ_MP (@lem5288718 x' x x'' y h1 h2 h3) (@lem5287504 x'' y h3)). Qed.
Lemma lem5288720 (x' : real) (x : real) (x'' : real) (y : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x'' = y) : term193 = False.
Proof. exact (prop_ext (fun h4 : term193 => @lem5288719 x' x x'' y h1 h2 h3) (fun h4 : False => @lem5287488 h1)). Qed.
Lemma lem5288721 (x' : real) (x : real) (x'' : real) (y : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x'' = y) : False.
Proof. exact (EQ_MP (@lem5288720 x' x x'' y h1 h2 h3) (@lem5287488 h1)). Qed.
Lemma lem5288722 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : (x'' = x) = False.
Proof. exact (prop_ext (fun h5 : x'' = x => @lem5288711 x' y x'' x h1 h2 h3 h4) (fun h5 : False => @lem5287472 x'' x h4)). Qed.
Lemma lem5288723 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : False.
Proof. exact (EQ_MP (@lem5288722 x' y x'' x h1 h2 h3 h4) (@lem5287472 x'' x h4)). Qed.
Lemma lem5288724 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : (x' = y) = False.
Proof. exact (prop_ext (fun h5 : x' = y => @lem5288723 x' y x'' x h1 h2 h3 h4) (fun h5 : False => @lem5287468 x' y h3)). Qed.
Lemma lem5288725 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : False.
Proof. exact (EQ_MP (@lem5288724 x' y x'' x h1 h2 h3 h4) (@lem5287468 x' y h3)). Qed.
Lemma lem5288726 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : term193 = False.
Proof. exact (prop_ext (fun h5 : term193 => @lem5288725 x' y x'' x h1 h2 h3 h4) (fun h5 : False => @lem5287456 h1)). Qed.
Lemma lem5288727 (x' : real) (y : real) (x'' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) (h4 : x'' = x) : False.
Proof. exact (EQ_MP (@lem5288726 x' y x'' x h1 h2 h3 h4) (@lem5287456 h1)). Qed.
Lemma lem5288728 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5288713 y x'' x' x h1 h2 h3) (fun h4 : False => @lem5287436 x' x h3)). Qed.
Lemma lem5288729 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5288728 y x'' x' x h1 h2 h3) (@lem5287436 x' x h3)). Qed.
Lemma lem5288730 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : term193 = False.
Proof. exact (prop_ext (fun h4 : term193 => @lem5288729 y x'' x' x h1 h2 h3) (fun h4 : False => @lem5287424 h1)). Qed.
Lemma lem5288731 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5288730 y x'' x' x h1 h2 h3) (@lem5287424 h1)). Qed.
Lemma lem5288732 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5288715 y x'' x' x h1 h2 h3) (fun h4 : False => @lem5287404 x' x h3)). Qed.
Lemma lem5288733 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5288732 y x'' x' x h1 h2 h3) (@lem5287404 x' x h3)). Qed.
Lemma lem5288734 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : term193 = False.
Proof. exact (prop_ext (fun h4 : term193 => @lem5288733 y x'' x' x h1 h2 h3) (fun h4 : False => @lem5287392 h1)). Qed.
Lemma lem5288735 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5288734 y x'' x' x h1 h2 h3) (@lem5287392 h1)). Qed.
Lemma lem5288736 (x : real) (x'' : real) (x' : real) (y : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = y) : False.
Proof. exact (or_elim (@lem5287368 x' x y x'' h2) (fun h0 : x'' = x => @lem5288727 x' y x'' x h1 h2 h3 h0) (fun h0 : x'' = y => @lem5288721 x' x x'' y h1 h2 h0)). Qed.
Lemma lem5288737 (y : real) (x'' : real) (x' : real) (x : real) (h1 : term193) (h2 : term301 x' x y x'') (h3 : x' = x) : False.
Proof. exact (or_elim (@lem5287368 x' x y x'' h2) (fun h0 : x'' = x => @lem5288735 y x'' x' x h1 h2 h3) (fun h0 : x'' = y => @lem5288731 y x'' x' x h1 h2 h3)). Qed.
Lemma lem5288738 (x' : real) (x : real) (y : real) (x'' : real) (h1 : term193) (h2 : term301 x' x y x'') : False.
Proof. exact (or_elim (@lem5287370 x' x y x'' h2) (fun h0 : x' = x => @lem5288737 y x'' x' x h1 h2 h0) (fun h0 : x' = y => @lem5288736 x x'' x' y h1 h2 h0)). Qed.
Lemma lem5288739 (x' : real) (x'' : real) (x : real) (y : real) (h1 : term193) (h2 : term383 x' x'' x y) : False.
Proof. exact (or_elim (@lem5287362 x' x'' x y h2) (fun h0 : term301 x' x y x'' => @lem5288738 x' x y x'' h1 h0) (fun h0 : term253 x y => @lem5288717 x y h1 h0)). Qed.
Lemma lem5288740 (x' : real) (x'' : real) (x : real) (y : real) (h1 : term193) (h2 : term383 x' x'' x y) : (term383 x' x'' x y) = False.
Proof. exact (prop_ext (fun h3 : term383 x' x'' x y => @lem5288739 x' x'' x y h1 h2) (fun h3 : False => @lem5287362 x' x'' x y h2)). Qed.
Lemma lem5288741 (x' : real) (x'' : real) (x : real) (y : real) (h1 : term193) (h2 : term383 x' x'' x y) : False.
Proof. exact (EQ_MP (@lem5288740 x' x'' x y h1 h2) (@lem5287362 x' x'' x y h2)). Qed.
Lemma lem5288742 (x' : real) (x'' : real) (x : real) (y : real) (h1 : term193) (h2 : term383 x' x'' x y) : term193 = False.
Proof. exact (prop_ext (fun h3 : term193 => @lem5288741 x' x'' x y h1 h2) (fun h3 : False => @lem5287269 h1)). Qed.
Lemma lem5288743 (x' : real) (x'' : real) (x : real) (y : real) (h1 : term193) (h2 : term383 x' x'' x y) : False.
Proof. exact (EQ_MP (@lem5288742 x' x'' x y h1 h2) (@lem5287269 h1)). Qed.
Lemma lem5288744 (x' : real) (x : real) (y : real) (h1 : term193) (h2 : term386 x' x y) : False.
Proof. exact (ex_elim (@lem5287248 x' x y h2) (fun x'' : real => fun h0 : term385 x' x y x'' => @lem5288743 x' x'' x y h1 h0)). Qed.
Lemma lem5288745 (x : real) (y : real) (h1 : term193) (h2 : term388 x y) : False.
Proof. exact (ex_elim (@lem5287247 x y h2) (fun x' : real => fun h0 : term387 x y x' => @lem5288744 x' x y h1 h0)). Qed.
Lemma lem5288746 (x : real) (h1 : term193) (h2 : term390 x) : False.
Proof. exact (ex_elim (@lem5287246 x h2) (fun y : real => fun h0 : term389 x y => @lem5288745 x y h1 h0)). Qed.
Lemma lem5288747 (h1 : term193) (h2 : term188) : False.
Proof. exact (ex_elim (@lem5287177 h2) (fun x : real => fun h0 : term391 x => @lem5288746 x h1 h0)). Qed.
Lemma lem5288748 (h1 : term193) (h2 : term188) : term193 = False.
Proof. exact (prop_ext (fun h3 : term193 => @lem5288747 h1 h2) (fun h3 : False => @lem5287245 h1)). Qed.
Lemma lem5288749 (h1 : term193) (h2 : term188) : False.
Proof. exact (EQ_MP (@lem5288748 h1 h2) (@lem5287245 h1)). Qed.
Lemma lem5288750 (h1 : term188) : term191.
Proof. exact (fun h0 : term193 => @lem5288749 h0 h1). Qed.
Lemma lem5288751 : term191 = term192.
Proof. exact (@lem69 term193). Qed.
Lemma lem5288752 (h1 : term188) : term192.
Proof. exact (EQ_MP (@lem5288751) (@lem5288750 h1)). Qed.
Lemma lem5288753 : term194.
Proof. exact (fun h0 : term188 => @lem5288752 h0). Qed.
Lemma lem5288754 : term138.
Proof. exact (EQ_MP (@lem5286673) (@lem5288753)). Qed.
Lemma lem5288756 : term138.
Proof. exact (@lem5286125 (@lem5288754)). Qed.
Lemma lem5288757 (h1 : term137) : term191.
Proof. exact (@lem5288756 (@lem5286110 h1)). Qed.
Lemma lem5288758 (h1 : term137) : False.
Proof. exact (@lem5288757 h1 (@lem1339697)). Qed.
Lemma lem5288759 (h1 : term137) : term137 = False.
Proof. exact (prop_ext (fun h2 : term137 => @lem5288758 h1) (fun h2 : False => @lem5286110 h1)). Qed.
Lemma lem5288760 (h1 : term137) : False.
Proof. exact (EQ_MP (@lem5288759 h1) (@lem5286110 h1)). Qed.
Lemma lem5288761 : term136.
Proof. exact (fun h0 : term137 => @lem5288760 h0). Qed.
Lemma lem5288762 : term134.
Proof. exact (EQ_MP (@lem5286109) (@lem5288761)). Qed.
Lemma lem5288763 : term101.
Proof. exact (EQ_MP (@lem5286105) (@lem5288762)). Qed.
Lemma lem5288764 : term100.
Proof. exact (EQ_MP (@lem5285907) (@lem5288763)). Qed.
