Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MAX_SUP_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_RULES_spec.
Require Import IN_INSERT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_INSERT_EMPTY_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import REAL_LE_MAX_spec.
Require Import REAL_LE_SUP_FINITE_spec.
Require Import REAL_MAX_LE_spec.
Require Import REAL_SUP_LE_FINITE_spec.
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
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem5200100 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5200101 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem5200102 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem5200101 A x) (@lem5200100 A x)). Qed.
Lemma lem5200103 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5200105 {A : Type'} (x : A) : term3 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5200106 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem5200107 {A : Type'} (x : A) : term4 A x.
Proof. exact (EQ_MP (@lem5200106 A x) (@lem5200105 A x)). Qed.
Lemma lem5200108 {A : Type'} (x : A) (y : A) : term5 A x y.
Proof. exact (@lem5200107 A x y). Qed.
Lemma lem5200109 {A : Type'} (y : A) (x : A) : (term5 A x y) = (term6 A y x).
Proof. exact (eq_refl (term5 A x y)). Qed.
Lemma lem5200110 {A : Type'} (y : A) (x : A) : term6 A y x.
Proof. exact (EQ_MP (@lem5200109 A y x) (@lem5200108 A x y)). Qed.
Lemma lem5200111 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term7 A y x s.
Proof. exact (@lem5200110 A y x s). Qed.
Lemma lem5200112 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term7 A y x s) = ((term8 A x y s) = (term9 A y x s)).
Proof. exact (eq_refl (term7 A y x s)). Qed.
Lemma lem5200116 (x : real) (y : real) (h1 : (term10 y x) = (x = y)) : (term10 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem5200117 (x : real) (y : real) (h1 : (term10 y x) = (x = y)) : (x = y) = (term10 y x).
Proof. exact (SYM (@lem5200116 x y h1)). Qed.
Lemma lem5200118 (y : real) (x : real) (h1 : (x = y) = (term10 y x)) : (x = y) = (term10 y x).
Proof. exact (h1). Qed.
Lemma lem5200119 (y : real) (x : real) (h1 : (x = y) = (term10 y x)) : (term10 y x) = (x = y).
Proof. exact (SYM (@lem5200118 y x h1)). Qed.
Lemma lem5200120 (y : real) (x : real) : ((term10 y x) = (x = y)) = ((x = y) = (term10 y x)).
Proof. exact (prop_ext (fun h1 : (term10 y x) = (x = y) => @lem5200117 x y h1) (fun h1 : (x = y) = (term10 y x) => @lem5200119 y x h1)). Qed.
Lemma lem5200121 (x : real) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem5200120 y x)). Qed.
Lemma lem5200122 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5200123 (x : real) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem5200122) (@lem5200121 x)). Qed.
Lemma lem5200124 : term15 = term16.
Proof. exact (fun_ext (fun x : real => @lem5200123 x)). Qed.
Lemma lem5200125 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5200126 : term17 = term18.
Proof. exact (MK_COMB (@lem5200125) (@lem5200124)). Qed.
Lemma lem5200127 : term18.
Proof. exact (EQ_MP (@lem5200126) (@lem1339379)). Qed.
Lemma lem5200128 (x : real) : term19 x.
Proof. exact (@lem1560900 x). Qed.
Lemma lem5200129 (x : real) : (term19 x) = (term20 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem5200130 (x : real) : term20 x.
Proof. exact (EQ_MP (@lem5200129 x) (@lem5200128 x)). Qed.
Lemma lem5200131 (x : real) (y : real) : term21 x y.
Proof. exact (@lem5200130 x y). Qed.
Lemma lem5200132 (x : real) (y : real) : (term21 x y) = (term22 x y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem5200133 (x : real) (y : real) : term22 x y.
Proof. exact (EQ_MP (@lem5200132 x y) (@lem5200131 x y)). Qed.
Lemma lem5200134 (x : real) (y : real) (z : real) : term23 x y z.
Proof. exact (@lem5200133 x y z). Qed.
Lemma lem5200135 (x : real) (z : real) (y : real) : (term23 x y z) = ((term24 z x y) = (term25 x z y)).
Proof. exact (eq_refl (term23 x y z)). Qed.
Lemma lem5200137 (x : real) : term26 x.
Proof. exact (@lem1566936 x). Qed.
Lemma lem5200138 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem5200139 (x : real) : term27 x.
Proof. exact (EQ_MP (@lem5200138 x) (@lem5200137 x)). Qed.
Lemma lem5200140 (x : real) (y : real) : term28 x y.
Proof. exact (@lem5200139 x y). Qed.
Lemma lem5200141 (x : real) (y : real) : (term28 x y) = (term29 x y).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem5200142 (x : real) (y : real) : term29 x y.
Proof. exact (EQ_MP (@lem5200141 x y) (@lem5200140 x y)). Qed.
Lemma lem5200143 (x : real) (y : real) (z : real) : term30 x y z.
Proof. exact (@lem5200142 x y z). Qed.
Lemma lem5200144 (x : real) (y : real) (z : real) : (term30 x y z) = ((term31 x y z) = (term32 x y z)).
Proof. exact (eq_refl (term30 x y z)). Qed.
Lemma lem5200146 {A : Type'} (x : A) : term33 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem5200147 {A : Type'} (x : A) : (term33 A x) = (term34 A x).
Proof. exact (eq_refl (term33 A x)). Qed.
Lemma lem5200148 {A : Type'} (x : A) : term34 A x.
Proof. exact (EQ_MP (@lem5200147 A x) (@lem5200146 A x)). Qed.
Lemma lem5200149 {A : Type'} (x : A) (s : A -> Prop) : term35 A x s.
Proof. exact (@lem5200148 A x s). Qed.
Lemma lem5200150 {A : Type'} (x : A) (s : A -> Prop) : (term35 A x s) = (term36 A x s).
Proof. exact (eq_refl (term35 A x s)). Qed.
Lemma lem5200151 {A : Type'} (x : A) (s : A -> Prop) : term36 A x s.
Proof. exact (EQ_MP (@lem5200150 A x s) (@lem5200149 A x s)). Qed.
Lemma lem5200152 {A : Type'} (x : A) (s : A -> Prop) : term37 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem5200165 {A : Type'} : term38 A.
Proof. exact (proj2 (@lem3197565 A)). Qed.
Lemma lem5200166 {A : Type'} (x : A) : term39 A x.
Proof. exact (@lem5200165 A x). Qed.
Lemma lem5200167 {A : Type'} (x : A) : (term39 A x) = (term40 A x).
Proof. exact (eq_refl (term39 A x)). Qed.
Lemma lem5200168 {A : Type'} (x : A) : term40 A x.
Proof. exact (EQ_MP (@lem5200167 A x) (@lem5200166 A x)). Qed.
Lemma lem5200169 {A : Type'} (x : A) (s : A -> Prop) : term41 A x s.
Proof. exact (@lem5200168 A x s). Qed.
Lemma lem5200170 {A : Type'} (x : A) (s : A -> Prop) : (term41 A x s) = (term42 A x s).
Proof. exact (eq_refl (term41 A x s)). Qed.
Lemma lem5200171 {A : Type'} (x : A) (s : A -> Prop) : term42 A x s.
Proof. exact (EQ_MP (@lem5200170 A x s) (@lem5200169 A x s)). Qed.
Lemma lem5200172 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5200173 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term43 A x s.
Proof. exact (@lem5200171 A x s (@lem5200172 A s h1)). Qed.
Lemma lem5200174 {A : Type'} (x : A) (s : A -> Prop) : (term43 A x s) = ((term43 A x s) = True).
Proof. exact (@lem7 (term43 A x s)). Qed.
Lemma lem5200175 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term43 A x s) = True.
Proof. exact (EQ_MP (@lem5200174 A x s) (@lem5200173 A x s h1)). Qed.
Lemma lem5200181 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem5200182 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem5200184 (s : real -> Prop) : term44 s.
Proof. exact (@lem5147521 s). Qed.
Lemma lem5200185 (s : real -> Prop) : (term44 s) = (term45 s).
Proof. exact (eq_refl (term44 s)). Qed.
Lemma lem5200186 (s : real -> Prop) : term45 s.
Proof. exact (EQ_MP (@lem5200185 s) (@lem5200184 s)). Qed.
Lemma lem5200187 (s : real -> Prop) (a : real) : term46 s a.
Proof. exact (@lem5200186 s a). Qed.
Lemma lem5200188 (s : real -> Prop) (a : real) : (term46 s a) = (term47 s a).
Proof. exact (eq_refl (term46 s a)). Qed.
Lemma lem5200189 (s : real -> Prop) (a : real) : term47 s a.
Proof. exact (EQ_MP (@lem5200188 s a) (@lem5200187 s a)). Qed.
Lemma lem5200190 (s : real -> Prop) (h1 : term48 s) : term48 s.
Proof. exact (h1). Qed.
Lemma lem5200191 (a : real) (s : real -> Prop) (h1 : term48 s) : (term49 a s) = (term50 s a).
Proof. exact (@lem5200189 s a (@lem5200190 s h1)). Qed.
Lemma lem5200197 (s : real -> Prop) : term51 s.
Proof. exact (@lem5149774 s). Qed.
Lemma lem5200198 (s : real -> Prop) : (term51 s) = (term52 s).
Proof. exact (eq_refl (term51 s)). Qed.
Lemma lem5200199 (s : real -> Prop) : term52 s.
Proof. exact (EQ_MP (@lem5200198 s) (@lem5200197 s)). Qed.
Lemma lem5200200 (s : real -> Prop) (a : real) : term53 s a.
Proof. exact (@lem5200199 s a). Qed.
Lemma lem5200201 (s : real -> Prop) (a : real) : (term53 s a) = (term54 s a).
Proof. exact (eq_refl (term53 s a)). Qed.
Lemma lem5200202 (s : real -> Prop) (a : real) : term54 s a.
Proof. exact (EQ_MP (@lem5200201 s a) (@lem5200200 s a)). Qed.
Lemma lem5200203 (s : real -> Prop) (h1 : term48 s) : term48 s.
Proof. exact (h1). Qed.
Lemma lem5200204 (a : real) (s : real -> Prop) (h1 : term48 s) : (term55 s a) = (term56 s a).
Proof. exact (@lem5200202 s a (@lem5200203 s h1)). Qed.
Lemma lem5200210 (x : real) : term57 x.
Proof. exact (@lem5200127 x). Qed.
Lemma lem5200211 (x : real) : (term57 x) = (term14 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem5200212 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem5200211 x) (@lem5200210 x)). Qed.
Lemma lem5200213 (x : real) (y : real) : term58 x y.
Proof. exact (@lem5200212 x y). Qed.
Lemma lem5200214 (y : real) (x : real) : (term58 x y) = ((x = y) = (term10 y x)).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem5200227 (y : real) (x : real) : (x = y) = (term10 y x).
Proof. exact (EQ_MP (@lem5200214 y x) (@lem5200213 x y)). Qed.
Lemma lem5200228 (x : real) (y : real) : ((real_max x y) = (term59 x y)) = (term60 x y).
Proof. exact (@lem5200227 (term59 x y) (real_max x y)). Qed.
Lemma lem5200232 (x : real) (y : real) (z : real) : (term31 x y z) = (term32 x y z).
Proof. exact (EQ_MP (@lem5200144 x y z) (@lem5200143 x y z)). Qed.
Lemma lem5200233 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (@lem5200232 x y (term59 x y)). Qed.
Lemma lem5200237 (s : real -> Prop) (a : real) : term47 s a.
Proof. exact (fun h0 : term48 s => @lem5200191 a s h0). Qed.
Lemma lem5200238 (y : real) (x : real) : term63 y x.
Proof. exact (@lem5200237 (term64 x y) x). Qed.
Lemma lem5200242 {A : Type'} (x : A) (s : A -> Prop) : term65 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5200175 A x s h0). Qed.
Lemma lem5200243 (x : real) (s : real -> Prop) : term66 x s.
Proof. exact (@lem5200242 real x s). Qed.
Lemma lem5200244 (x : real) (y : real) : term67 x y.
Proof. exact (@lem5200243 x (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5200246 {A : Type'} (x : A) (s : A -> Prop) : term65 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5200175 A x s h0). Qed.
Lemma lem5200247 (x : real) (s : real -> Prop) : term66 x s.
Proof. exact (@lem5200246 real x s). Qed.
Lemma lem5200248 (y : real) : term68 y.
Proof. exact (@lem5200247 y (@EMPTY real)). Qed.
Lemma lem5200250 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem5200182 A) (@lem5200181 A)). Qed.
Lemma lem5200251 : (@FINITE real (@EMPTY real)) = True.
Proof. exact (@lem5200250 real). Qed.
Lemma lem5200252 : True = (@FINITE real (@EMPTY real)).
Proof. exact (SYM (@lem5200251)). Qed.
Lemma lem5200253 : @FINITE real (@EMPTY real).
Proof. exact (EQ_MP (@lem5200252) (@lem0)). Qed.
Lemma lem5200254 (y : real) : (term69 y) = True.
Proof. exact (@lem5200248 y (@lem5200253)). Qed.
Lemma lem5200255 (y : real) : True = (term69 y).
Proof. exact (SYM (@lem5200254 y)). Qed.
Lemma lem5200256 (y : real) : term69 y.
Proof. exact (EQ_MP (@lem5200255 y) (@lem0)). Qed.
Lemma lem5200257 (x : real) (y : real) : (term70 x y) = True.
Proof. exact (@lem5200244 x y (@lem5200256 y)). Qed.
Lemma lem5200258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5200259 (x : real) (y : real) : (term71 x y) = (and True).
Proof. exact (MK_COMB (@lem5200258) (@lem5200257 x y)). Qed.
Lemma lem5200261 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5200152 A x s (@lem5200151 A x s)). Qed.
Lemma lem5200262 (x : real) (s : real -> Prop) : ((@INSERT real x s) = (@EMPTY real)) = False.
Proof. exact (@lem5200261 real x s). Qed.
Lemma lem5200263 (x : real) (y : real) : ((term64 x y) = (@EMPTY real)) = False.
Proof. exact (@lem5200262 x (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5200264 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5200265 (x : real) (y : real) : (term72 x y) = (~ False).
Proof. exact (MK_COMB (@lem5200264) (@lem5200263 x y)). Qed.
Lemma lem5200267 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5200268 (x : real) (y : real) : (term72 x y) = True.
Proof. exact (TRANS (@lem5200265 x y) (@lem5200267)). Qed.
Lemma lem5200269 (x : real) (y : real) : (term73 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem5200259 x y) (@lem5200268 x y)). Qed.
Lemma lem5200271 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5200272 : (True /\ True) = True.
Proof. exact (@lem5200271 True). Qed.
Lemma lem5200273 (x : real) (y : real) : (term73 x y) = True.
Proof. exact (TRANS (@lem5200269 x y) (@lem5200272)). Qed.
Lemma lem5200274 (x : real) (y : real) : True = (term73 x y).
Proof. exact (SYM (@lem5200273 x y)). Qed.
Lemma lem5200275 (x : real) (y : real) : term73 x y.
Proof. exact (EQ_MP (@lem5200274 x y) (@lem0)). Qed.
Lemma lem5200276 (y : real) (x : real) : (term74 x y) = (term75 y x).
Proof. exact (@lem5200238 y x (@lem5200275 x y)). Qed.
Lemma lem5200283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5200284 (y : real) (x : real) : (term76 x y) = (term77 y x).
Proof. exact (MK_COMB (@lem5200283) (@lem5200276 y x)). Qed.
Lemma lem5200292 (s : real -> Prop) (a : real) : term47 s a.
Proof. exact (fun h0 : term48 s => @lem5200191 a s h0). Qed.
Lemma lem5200293 (x : real) (y : real) : term78 x y.
Proof. exact (@lem5200292 (term64 x y) y). Qed.
Lemma lem5200297 {A : Type'} (x : A) (s : A -> Prop) : term65 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5200175 A x s h0). Qed.
Lemma lem5200298 (x : real) (s : real -> Prop) : term66 x s.
Proof. exact (@lem5200297 real x s). Qed.
Lemma lem5200299 (x : real) (y : real) : term67 x y.
Proof. exact (@lem5200298 x (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5200301 {A : Type'} (x : A) (s : A -> Prop) : term65 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5200175 A x s h0). Qed.
Lemma lem5200302 (x : real) (s : real -> Prop) : term66 x s.
Proof. exact (@lem5200301 real x s). Qed.
Lemma lem5200303 (y : real) : term68 y.
Proof. exact (@lem5200302 y (@EMPTY real)). Qed.
Lemma lem5200305 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem5200182 A) (@lem5200181 A)). Qed.
Lemma lem5200306 : (@FINITE real (@EMPTY real)) = True.
Proof. exact (@lem5200305 real). Qed.
Lemma lem5200307 : True = (@FINITE real (@EMPTY real)).
Proof. exact (SYM (@lem5200306)). Qed.
Lemma lem5200308 : @FINITE real (@EMPTY real).
Proof. exact (EQ_MP (@lem5200307) (@lem0)). Qed.
Lemma lem5200309 (y : real) : (term69 y) = True.
Proof. exact (@lem5200303 y (@lem5200308)). Qed.
Lemma lem5200310 (y : real) : True = (term69 y).
Proof. exact (SYM (@lem5200309 y)). Qed.
Lemma lem5200311 (y : real) : term69 y.
Proof. exact (EQ_MP (@lem5200310 y) (@lem0)). Qed.
Lemma lem5200312 (x : real) (y : real) : (term70 x y) = True.
Proof. exact (@lem5200299 x y (@lem5200311 y)). Qed.
Lemma lem5200313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5200314 (x : real) (y : real) : (term71 x y) = (and True).
Proof. exact (MK_COMB (@lem5200313) (@lem5200312 x y)). Qed.
Lemma lem5200316 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5200152 A x s (@lem5200151 A x s)). Qed.
Lemma lem5200317 (x : real) (s : real -> Prop) : ((@INSERT real x s) = (@EMPTY real)) = False.
Proof. exact (@lem5200316 real x s). Qed.
Lemma lem5200318 (x : real) (y : real) : ((term64 x y) = (@EMPTY real)) = False.
Proof. exact (@lem5200317 x (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5200319 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5200320 (x : real) (y : real) : (term72 x y) = (~ False).
Proof. exact (MK_COMB (@lem5200319) (@lem5200318 x y)). Qed.
Lemma lem5200322 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5200323 (x : real) (y : real) : (term72 x y) = True.
Proof. exact (TRANS (@lem5200320 x y) (@lem5200322)). Qed.
Lemma lem5200324 (x : real) (y : real) : (term73 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem5200314 x y) (@lem5200323 x y)). Qed.
Lemma lem5200326 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5200327 : (True /\ True) = True.
Proof. exact (@lem5200326 True). Qed.
Lemma lem5200328 (x : real) (y : real) : (term73 x y) = True.
Proof. exact (TRANS (@lem5200324 x y) (@lem5200327)). Qed.
Lemma lem5200329 (x : real) (y : real) : True = (term73 x y).
Proof. exact (SYM (@lem5200328 x y)). Qed.
Lemma lem5200330 (x : real) (y : real) : term73 x y.
Proof. exact (EQ_MP (@lem5200329 x y) (@lem0)). Qed.
Lemma lem5200331 (x : real) (y : real) : (term79 x y) = (term80 x y).
Proof. exact (@lem5200293 x y (@lem5200330 x y)). Qed.
Lemma lem5200338 (x : real) (y : real) : (term62 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem5200284 y x) (@lem5200331 x y)). Qed.
Lemma lem5200353 (x : real) (y : real) : (term61 x y) = (term81 x y).
Proof. exact (TRANS (@lem5200233 x y) (@lem5200338 x y)). Qed.
Lemma lem5200354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5200355 (x : real) (y : real) : (term82 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem5200354) (@lem5200353 x y)). Qed.
Lemma lem5200371 (s : real -> Prop) (a : real) : term54 s a.
Proof. exact (fun h0 : term48 s => @lem5200204 a s h0). Qed.
Lemma lem5200372 (x : real) (y : real) : term84 x y.
Proof. exact (@lem5200371 (term64 x y) (real_max x y)). Qed.
Lemma lem5200376 {A : Type'} (x : A) (s : A -> Prop) : term65 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5200175 A x s h0). Qed.
Lemma lem5200377 (x : real) (s : real -> Prop) : term66 x s.
Proof. exact (@lem5200376 real x s). Qed.
Lemma lem5200378 (x : real) (y : real) : term67 x y.
Proof. exact (@lem5200377 x (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5200380 {A : Type'} (x : A) (s : A -> Prop) : term65 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5200175 A x s h0). Qed.
Lemma lem5200381 (x : real) (s : real -> Prop) : term66 x s.
Proof. exact (@lem5200380 real x s). Qed.
Lemma lem5200382 (y : real) : term68 y.
Proof. exact (@lem5200381 y (@EMPTY real)). Qed.
Lemma lem5200384 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem5200182 A) (@lem5200181 A)). Qed.
Lemma lem5200385 : (@FINITE real (@EMPTY real)) = True.
Proof. exact (@lem5200384 real). Qed.
Lemma lem5200386 : True = (@FINITE real (@EMPTY real)).
Proof. exact (SYM (@lem5200385)). Qed.
Lemma lem5200387 : @FINITE real (@EMPTY real).
Proof. exact (EQ_MP (@lem5200386) (@lem0)). Qed.
Lemma lem5200388 (y : real) : (term69 y) = True.
Proof. exact (@lem5200382 y (@lem5200387)). Qed.
Lemma lem5200389 (y : real) : True = (term69 y).
Proof. exact (SYM (@lem5200388 y)). Qed.
Lemma lem5200390 (y : real) : term69 y.
Proof. exact (EQ_MP (@lem5200389 y) (@lem0)). Qed.
Lemma lem5200391 (x : real) (y : real) : (term70 x y) = True.
Proof. exact (@lem5200378 x y (@lem5200390 y)). Qed.
Lemma lem5200392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5200393 (x : real) (y : real) : (term71 x y) = (and True).
Proof. exact (MK_COMB (@lem5200392) (@lem5200391 x y)). Qed.
Lemma lem5200395 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5200152 A x s (@lem5200151 A x s)). Qed.
Lemma lem5200396 (x : real) (s : real -> Prop) : ((@INSERT real x s) = (@EMPTY real)) = False.
Proof. exact (@lem5200395 real x s). Qed.
Lemma lem5200397 (x : real) (y : real) : ((term64 x y) = (@EMPTY real)) = False.
Proof. exact (@lem5200396 x (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5200398 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5200399 (x : real) (y : real) : (term72 x y) = (~ False).
Proof. exact (MK_COMB (@lem5200398) (@lem5200397 x y)). Qed.
Lemma lem5200401 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5200402 (x : real) (y : real) : (term72 x y) = True.
Proof. exact (TRANS (@lem5200399 x y) (@lem5200401)). Qed.
Lemma lem5200403 (x : real) (y : real) : (term73 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem5200393 x y) (@lem5200402 x y)). Qed.
Lemma lem5200405 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5200406 : (True /\ True) = True.
Proof. exact (@lem5200405 True). Qed.
Lemma lem5200407 (x : real) (y : real) : (term73 x y) = True.
Proof. exact (TRANS (@lem5200403 x y) (@lem5200406)). Qed.
Lemma lem5200408 (x : real) (y : real) : True = (term73 x y).
Proof. exact (SYM (@lem5200407 x y)). Qed.
Lemma lem5200409 (x : real) (y : real) : term73 x y.
Proof. exact (EQ_MP (@lem5200408 x y) (@lem0)). Qed.
Lemma lem5200410 (x : real) (y : real) : (term85 x y) = (term86 x y).
Proof. exact (@lem5200372 x y (@lem5200409 x y)). Qed.
Lemma lem5200418 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term87 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5200419 (p : Prop) (q : Prop) (p' : Prop) : term88 p q p'.
Proof. exact (fun q' : Prop => @lem5200418 p q p' q'). Qed.
Lemma lem5200420 (p : Prop) (q : Prop) : term89 p q.
Proof. exact (fun p' : Prop => @lem5200419 p q p'). Qed.
Lemma lem5200421 (x' : real) (x : real) (y : real) : term90 x' x y.
Proof. exact (@lem5200420 (term91 x' x y) (term24 x' x y)). Qed.
Lemma lem5200422 (x' : real) (x : real) (y : real) (p' : Prop) : term92 x' x y p'.
Proof. exact (@lem5200421 x' x y p'). Qed.
Lemma lem5200423 (x' : real) (x : real) (y : real) (p' : Prop) : (term92 x' x y p') = (term93 x' x y p').
Proof. exact (eq_refl (term92 x' x y p')). Qed.
Lemma lem5200424 (x' : real) (x : real) (y : real) (p' : Prop) : term93 x' x y p'.
Proof. exact (EQ_MP (@lem5200423 x' x y p') (@lem5200422 x' x y p')). Qed.
Lemma lem5200425 (x' : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : term94 x' x y p' q'.
Proof. exact (@lem5200424 x' x y p' q'). Qed.
Lemma lem5200426 (x' : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : (term94 x' x y p' q') = (term95 x' x y p' q').
Proof. exact (eq_refl (term94 x' x y p' q')). Qed.
Lemma lem5200427 (x' : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : term95 x' x y p' q'.
Proof. exact (EQ_MP (@lem5200426 x' x y p' q') (@lem5200425 x' x y p' q')). Qed.
Lemma lem5200428 (x' : real) (x : real) (y : real) : (term91 x' x y) = (term91 x' x y).
Proof. exact (eq_refl (term91 x' x y)). Qed.
Lemma lem5200429 (x' : real) (x : real) (y : real) (q' : Prop) : term96 x' x y q'.
Proof. exact (@lem5200427 x' x y (term91 x' x y) q'). Qed.
Lemma lem5200430 (x' : real) (x : real) (y : real) (q' : Prop) : term97 x' x y q'.
Proof. exact (@lem5200429 x' x y q' (@lem5200428 x' x y)). Qed.
Lemma lem5200435 (x : real) (z : real) (y : real) : (term24 z x y) = (term25 x z y).
Proof. exact (EQ_MP (@lem5200135 x z y) (@lem5200134 x y z)). Qed.
Lemma lem5200436 (x : real) (x' : real) (y : real) : (term24 x' x y) = (term25 x x' y).
Proof. exact (@lem5200435 x x' y). Qed.
Lemma lem5200439 (x : real) (x' : real) (y : real) : term98 x x' y.
Proof. exact (fun h0 : term91 x' x y => @lem5200436 x x' y). Qed.
Lemma lem5200440 (x : real) (x' : real) (y : real) : term99 x x' y.
Proof. exact (@lem5200430 x' x y (term25 x x' y)). Qed.
Lemma lem5200441 (x : real) (x' : real) (y : real) : (term100 x' x y) = (term101 x x' y).
Proof. exact (@lem5200440 x x' y (@lem5200439 x x' y)). Qed.
Lemma lem5200469 (x : real) (y : real) : (term102 x y) = (term103 x y).
Proof. exact (fun_ext (fun x' : real => @lem5200441 x x' y)). Qed.
Lemma lem5200497 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5200498 (x : real) (y : real) : (term86 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem5200497) (@lem5200469 x y)). Qed.
Lemma lem5200530 (x : real) (y : real) : (term85 x y) = (term104 x y).
Proof. exact (TRANS (@lem5200410 x y) (@lem5200498 x y)). Qed.
Lemma lem5200531 (x : real) (y : real) : (term60 x y) = (term105 x y).
Proof. exact (MK_COMB (@lem5200355 x y) (@lem5200530 x y)). Qed.
Lemma lem5200579 (x : real) (y : real) : ((real_max x y) = (term59 x y)) = (term105 x y).
Proof. exact (TRANS (@lem5200228 x y) (@lem5200531 x y)). Qed.
Lemma lem5200580 (x : real) : (term106 x) = (term107 x).
Proof. exact (fun_ext (fun y : real => @lem5200579 x y)). Qed.
Lemma lem5200628 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5200629 (x : real) : (term108 x) = (term109 x).
Proof. exact (MK_COMB (@lem5200628) (@lem5200580 x)). Qed.
Lemma lem5200681 : term110 = term111.
Proof. exact (fun_ext (fun x : real => @lem5200629 x)). Qed.
Lemma lem5200733 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5200734 : term112 = term113.
Proof. exact (MK_COMB (@lem5200733) (@lem5200681)). Qed.
Lemma lem5200790 : term113 = term112.
Proof. exact (SYM (@lem5200734)). Qed.
Lemma lem5200810 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem5200112 A y x s) (@lem5200111 A y x s)). Qed.
Lemma lem5200811 (y : real) (x : real) (s : real -> Prop) : (term114 x y s) = (term115 y x s).
Proof. exact (@lem5200810 real y x s). Qed.
Lemma lem5200812 (x : real) (x' : real) (y : real) : (term91 x' x y) = (term116 x x' y).
Proof. exact (@lem5200811 x x' (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5200818 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem5200112 A y x s) (@lem5200111 A y x s)). Qed.
Lemma lem5200819 (y : real) (x : real) (s : real -> Prop) : (term114 x y s) = (term115 y x s).
Proof. exact (@lem5200818 real y x s). Qed.
Lemma lem5200820 (y : real) (x' : real) : (term117 x' y) = (term118 y x').
Proof. exact (@lem5200819 y x' (@EMPTY real)). Qed.
Lemma lem5200826 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5200103 A x (@lem5200102 A x)). Qed.
Lemma lem5200827 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5200826 real x). Qed.
Lemma lem5200828 (x' : real) : (@IN real x' (@EMPTY real)) = False.
Proof. exact (@lem5200827 x'). Qed.
Lemma lem5200829 (x' : real) (y : real) : (term119 x' y) = (term119 x' y).
Proof. exact (eq_refl (term119 x' y)). Qed.
Lemma lem5200830 (x' : real) (y : real) : (term118 y x') = (term120 x' y).
Proof. exact (MK_COMB (@lem5200829 x' y) (@lem5200828 x')). Qed.
Lemma lem5200832 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5200833 (x' : real) (y : real) : (term120 x' y) = (x' = y).
Proof. exact (@lem5200832 (x' = y)). Qed.
Lemma lem5200836 (x' : real) (y : real) : (term118 y x') = (x' = y).
Proof. exact (TRANS (@lem5200830 x' y) (@lem5200833 x' y)). Qed.
Lemma lem5200837 (x' : real) (y : real) : (term117 x' y) = (x' = y).
Proof. exact (TRANS (@lem5200820 y x') (@lem5200836 x' y)). Qed.
Lemma lem5200838 (x' : real) (x : real) : (term119 x' x) = (term119 x' x).
Proof. exact (eq_refl (term119 x' x)). Qed.
Lemma lem5200839 (x : real) (x' : real) (y : real) : (term116 x x' y) = (term121 x x' y).
Proof. exact (MK_COMB (@lem5200838 x' x) (@lem5200837 x' y)). Qed.
Lemma lem5200842 (x : real) (x' : real) (y : real) : (term91 x' x y) = (term121 x x' y).
Proof. exact (TRANS (@lem5200812 x x' y) (@lem5200839 x x' y)). Qed.
Lemma lem5200843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5200844 (x : real) (x' : real) (y : real) : (term122 x' x y) = (term123 x x' y).
Proof. exact (MK_COMB (@lem5200843) (@lem5200842 x x' y)). Qed.
Lemma lem5200845 (x : real) (x' : real) : (real_le x x') = (real_le x x').
Proof. exact (eq_refl (real_le x x')). Qed.
Lemma lem5200846 (y : real) (x : real) (x' : real) : (term124 y x x') = (term125 y x x').
Proof. exact (MK_COMB (@lem5200844 x x' y) (@lem5200845 x x')). Qed.
Lemma lem5200849 (y : real) (x : real) : (term126 y x) = (term127 y x).
Proof. exact (fun_ext (fun x' : real => @lem5200846 y x x')). Qed.
Lemma lem5200850 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5200851 (y : real) (x : real) : (term75 y x) = (term128 y x).
Proof. exact (MK_COMB (@lem5200850) (@lem5200849 y x)). Qed.
Lemma lem5200856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5200857 (y : real) (x : real) : (term77 y x) = (term129 y x).
Proof. exact (MK_COMB (@lem5200856) (@lem5200851 y x)). Qed.
Lemma lem5200865 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem5200112 A y x s) (@lem5200111 A y x s)). Qed.
Lemma lem5200866 (y : real) (x : real) (s : real -> Prop) : (term114 x y s) = (term115 y x s).
Proof. exact (@lem5200865 real y x s). Qed.
Lemma lem5200867 (x : real) (x' : real) (y : real) : (term91 x' x y) = (term116 x x' y).
Proof. exact (@lem5200866 x x' (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5200873 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem5200112 A y x s) (@lem5200111 A y x s)). Qed.
Lemma lem5200874 (y : real) (x : real) (s : real -> Prop) : (term114 x y s) = (term115 y x s).
Proof. exact (@lem5200873 real y x s). Qed.
Lemma lem5200875 (y : real) (x' : real) : (term117 x' y) = (term118 y x').
Proof. exact (@lem5200874 y x' (@EMPTY real)). Qed.
Lemma lem5200881 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5200103 A x (@lem5200102 A x)). Qed.
Lemma lem5200882 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5200881 real x). Qed.
Lemma lem5200883 (x' : real) : (@IN real x' (@EMPTY real)) = False.
Proof. exact (@lem5200882 x'). Qed.
Lemma lem5200884 (x' : real) (y : real) : (term119 x' y) = (term119 x' y).
Proof. exact (eq_refl (term119 x' y)). Qed.
Lemma lem5200885 (x' : real) (y : real) : (term118 y x') = (term120 x' y).
Proof. exact (MK_COMB (@lem5200884 x' y) (@lem5200883 x')). Qed.
Lemma lem5200887 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5200888 (x' : real) (y : real) : (term120 x' y) = (x' = y).
Proof. exact (@lem5200887 (x' = y)). Qed.
Lemma lem5200891 (x' : real) (y : real) : (term118 y x') = (x' = y).
Proof. exact (TRANS (@lem5200885 x' y) (@lem5200888 x' y)). Qed.
Lemma lem5200892 (x' : real) (y : real) : (term117 x' y) = (x' = y).
Proof. exact (TRANS (@lem5200875 y x') (@lem5200891 x' y)). Qed.
Lemma lem5200893 (x' : real) (x : real) : (term119 x' x) = (term119 x' x).
Proof. exact (eq_refl (term119 x' x)). Qed.
Lemma lem5200894 (x : real) (x' : real) (y : real) : (term116 x x' y) = (term121 x x' y).
Proof. exact (MK_COMB (@lem5200893 x' x) (@lem5200892 x' y)). Qed.
Lemma lem5200897 (x : real) (x' : real) (y : real) : (term91 x' x y) = (term121 x x' y).
Proof. exact (TRANS (@lem5200867 x x' y) (@lem5200894 x x' y)). Qed.
Lemma lem5200898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5200899 (x : real) (x' : real) (y : real) : (term122 x' x y) = (term123 x x' y).
Proof. exact (MK_COMB (@lem5200898) (@lem5200897 x x' y)). Qed.
Lemma lem5200900 (y : real) (x' : real) : (real_le y x') = (real_le y x').
Proof. exact (eq_refl (real_le y x')). Qed.
Lemma lem5200901 (x : real) (y : real) (x' : real) : (term130 x y x') = (term131 x y x').
Proof. exact (MK_COMB (@lem5200899 x x' y) (@lem5200900 y x')). Qed.
Lemma lem5200904 (x : real) (y : real) : (term132 x y) = (term133 x y).
Proof. exact (fun_ext (fun x' : real => @lem5200901 x y x')). Qed.
Lemma lem5200905 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5200906 (x : real) (y : real) : (term80 x y) = (term134 x y).
Proof. exact (MK_COMB (@lem5200905) (@lem5200904 x y)). Qed.
Lemma lem5200911 (x : real) (y : real) : (term81 x y) = (term135 x y).
Proof. exact (MK_COMB (@lem5200857 y x) (@lem5200906 x y)). Qed.
Lemma lem5200914 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5200915 (x : real) (y : real) : (term83 x y) = (term136 x y).
Proof. exact (MK_COMB (@lem5200914) (@lem5200911 x y)). Qed.
Lemma lem5200923 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem5200112 A y x s) (@lem5200111 A y x s)). Qed.
Lemma lem5200924 (y : real) (x : real) (s : real -> Prop) : (term114 x y s) = (term115 y x s).
Proof. exact (@lem5200923 real y x s). Qed.
Lemma lem5200925 (x : real) (x' : real) (y : real) : (term91 x' x y) = (term116 x x' y).
Proof. exact (@lem5200924 x x' (@INSERT real y (@EMPTY real))). Qed.
Lemma lem5200931 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem5200112 A y x s) (@lem5200111 A y x s)). Qed.
Lemma lem5200932 (y : real) (x : real) (s : real -> Prop) : (term114 x y s) = (term115 y x s).
Proof. exact (@lem5200931 real y x s). Qed.
Lemma lem5200933 (y : real) (x' : real) : (term117 x' y) = (term118 y x').
Proof. exact (@lem5200932 y x' (@EMPTY real)). Qed.
Lemma lem5200939 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5200103 A x (@lem5200102 A x)). Qed.
Lemma lem5200940 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5200939 real x). Qed.
Lemma lem5200941 (x' : real) : (@IN real x' (@EMPTY real)) = False.
Proof. exact (@lem5200940 x'). Qed.
Lemma lem5200942 (x' : real) (y : real) : (term119 x' y) = (term119 x' y).
Proof. exact (eq_refl (term119 x' y)). Qed.
Lemma lem5200943 (x' : real) (y : real) : (term118 y x') = (term120 x' y).
Proof. exact (MK_COMB (@lem5200942 x' y) (@lem5200941 x')). Qed.
Lemma lem5200945 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5200946 (x' : real) (y : real) : (term120 x' y) = (x' = y).
Proof. exact (@lem5200945 (x' = y)). Qed.
Lemma lem5200949 (x' : real) (y : real) : (term118 y x') = (x' = y).
Proof. exact (TRANS (@lem5200943 x' y) (@lem5200946 x' y)). Qed.
Lemma lem5200950 (x' : real) (y : real) : (term117 x' y) = (x' = y).
Proof. exact (TRANS (@lem5200933 y x') (@lem5200949 x' y)). Qed.
Lemma lem5200951 (x' : real) (x : real) : (term119 x' x) = (term119 x' x).
Proof. exact (eq_refl (term119 x' x)). Qed.
Lemma lem5200952 (x : real) (x' : real) (y : real) : (term116 x x' y) = (term121 x x' y).
Proof. exact (MK_COMB (@lem5200951 x' x) (@lem5200950 x' y)). Qed.
Lemma lem5200955 (x : real) (x' : real) (y : real) : (term91 x' x y) = (term121 x x' y).
Proof. exact (TRANS (@lem5200925 x x' y) (@lem5200952 x x' y)). Qed.
Lemma lem5200956 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5200957 (x : real) (x' : real) (y : real) : (term137 x' x y) = (term138 x x' y).
Proof. exact (MK_COMB (@lem5200956) (@lem5200955 x x' y)). Qed.
Lemma lem5200960 (x : real) (x' : real) (y : real) : (term25 x x' y) = (term25 x x' y).
Proof. exact (eq_refl (term25 x x' y)). Qed.
Lemma lem5200961 (x : real) (x' : real) (y : real) : (term101 x x' y) = (term139 x x' y).
Proof. exact (MK_COMB (@lem5200957 x x' y) (@lem5200960 x x' y)). Qed.
Lemma lem5200964 (x : real) (y : real) : (term103 x y) = (term140 x y).
Proof. exact (fun_ext (fun x' : real => @lem5200961 x x' y)). Qed.
Lemma lem5200965 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5200966 (x : real) (y : real) : (term104 x y) = (term141 x y).
Proof. exact (MK_COMB (@lem5200965) (@lem5200964 x y)). Qed.
Lemma lem5200971 (x : real) (y : real) : (term105 x y) = (term142 x y).
Proof. exact (MK_COMB (@lem5200915 x y) (@lem5200966 x y)). Qed.
Lemma lem5200974 (x : real) : (term107 x) = (term143 x).
Proof. exact (fun_ext (fun y : real => @lem5200971 x y)). Qed.
Lemma lem5200975 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5200976 (x : real) : (term109 x) = (term144 x).
Proof. exact (MK_COMB (@lem5200975) (@lem5200974 x)). Qed.
Lemma lem5200981 : term111 = term145.
Proof. exact (fun_ext (fun x : real => @lem5200976 x)). Qed.
Lemma lem5200982 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5200983 : term113 = term146.
Proof. exact (MK_COMB (@lem5200982) (@lem5200981)). Qed.
Lemma lem5200988 : term146 = term113.
Proof. exact (SYM (@lem5200983)). Qed.
Lemma lem5200990 (p : Prop) : p = (term147 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5200991 : term146 = term148.
Proof. exact (@lem5200990 term146). Qed.
Lemma lem5200992 : term148 = term146.
Proof. exact (SYM (@lem5200991)). Qed.
Lemma lem5200993 (h1 : term149) : term149.
Proof. exact (h1). Qed.
Lemma lem5200996 (h1 : term150) : term150.
Proof. exact (h1). Qed.
Lemma lem5200997 : term151.
Proof. exact (fun h0 : term150 => @lem5200996 h0). Qed.
Lemma lem5200998 (h1 : term151) : term151.
Proof. exact (h1). Qed.
Lemma lem5200999 (h1 : term150) : term150.
Proof. exact (h1). Qed.
Lemma lem5201000 (h1 : term150) (h2 : term151) : term150.
Proof. exact (@lem5200998 h2 (@lem5200999 h1)). Qed.
Lemma lem5201001 (h1 : term150) : term152.
Proof. exact (fun h0 : term151 => @lem5201000 h1 h0). Qed.
Lemma lem5201002 (h1 : term151) : term151.
Proof. exact (h1). Qed.
Lemma lem5201003 (h1 : term150) (h2 : term151) : term150.
Proof. exact (@lem5201001 h1 (@lem5201002 h2)). Qed.
Lemma lem5201004 (h1 : term151) : term151.
Proof. exact (fun h0 : term150 => @lem5201003 h0 h1). Qed.
Lemma lem5201005 : term153.
Proof. exact (fun h0 : term151 => @lem5201004 h0). Qed.
Lemma lem5201008 : term151.
Proof. exact (@lem5201005 (@lem5200997)). Qed.
Lemma lem5201016 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem5201017 (P : real -> Prop) (Q : real -> Prop) : (term156 P Q) = (term157 P Q).
Proof. exact (@lem5201016 real P Q). Qed.
Lemma lem5201018 (x : real) : (term158 x) = (term159 x).
Proof. exact (@lem5201017 (term160 x) (term161 x)). Qed.
Lemma lem5201019 (x : real) (y : real) : (term162 x y) = (term135 x y).
Proof. exact (eq_refl (term162 x y)). Qed.
Lemma lem5201020 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5201021 (x : real) (y : real) : (term163 x y) = (term136 x y).
Proof. exact (MK_COMB (@lem5201020) (@lem5201019 x y)). Qed.
Lemma lem5201022 (x : real) (y : real) : (term164 x y) = (term141 x y).
Proof. exact (eq_refl (term164 x y)). Qed.
Lemma lem5201023 (x : real) (y : real) : (term165 x y) = (term142 x y).
Proof. exact (MK_COMB (@lem5201021 x y) (@lem5201022 x y)). Qed.
Lemma lem5201024 (x : real) : (term166 x) = (term143 x).
Proof. exact (fun_ext (fun y : real => @lem5201023 x y)). Qed.
Lemma lem5201025 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201026 (x : real) : (term158 x) = (term144 x).
Proof. exact (MK_COMB (@lem5201025) (@lem5201024 x)). Qed.
Lemma lem5201027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5201028 (x : real) : (term167 x) = (term168 x).
Proof. exact (MK_COMB (@lem5201027) (@lem5201026 x)). Qed.
Lemma lem5201029 (x : real) (y : real) : (term162 x y) = (term135 x y).
Proof. exact (eq_refl (term162 x y)). Qed.
Lemma lem5201030 (x : real) : (term169 x) = (term160 x).
Proof. exact (fun_ext (fun y : real => @lem5201029 x y)). Qed.
Lemma lem5201031 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201032 (x : real) : (term170 x) = (term171 x).
Proof. exact (MK_COMB (@lem5201031) (@lem5201030 x)). Qed.
Lemma lem5201033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5201034 (x : real) : (term172 x) = (term173 x).
Proof. exact (MK_COMB (@lem5201033) (@lem5201032 x)). Qed.
Lemma lem5201035 (x : real) (y : real) : (term164 x y) = (term141 x y).
Proof. exact (eq_refl (term164 x y)). Qed.
Lemma lem5201036 (x : real) : (term174 x) = (term161 x).
Proof. exact (fun_ext (fun y : real => @lem5201035 x y)). Qed.
Lemma lem5201037 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201038 (x : real) : (term175 x) = (term176 x).
Proof. exact (MK_COMB (@lem5201037) (@lem5201036 x)). Qed.
Lemma lem5201039 (x : real) : (term159 x) = (term177 x).
Proof. exact (MK_COMB (@lem5201034 x) (@lem5201038 x)). Qed.
Lemma lem5201040 (x : real) : ((term158 x) = (term159 x)) = ((term144 x) = (term177 x)).
Proof. exact (MK_COMB (@lem5201028 x) (@lem5201039 x)). Qed.
Lemma lem5201041 (x : real) : (term144 x) = (term177 x).
Proof. exact (EQ_MP (@lem5201040 x) (@lem5201018 x)). Qed.
Lemma lem5201045 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem5201046 (P : real -> Prop) (Q : real -> Prop) : (term156 P Q) = (term157 P Q).
Proof. exact (@lem5201045 real P Q). Qed.
Lemma lem5201047 (x : real) : (term178 x) = (term179 x).
Proof. exact (@lem5201046 (term180 x) (term181 x)). Qed.
Lemma lem5201048 (y : real) (x : real) : (term182 x y) = (term128 y x).
Proof. exact (eq_refl (term182 x y)). Qed.
Lemma lem5201049 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5201050 (y : real) (x : real) : (term183 x y) = (term129 y x).
Proof. exact (MK_COMB (@lem5201049) (@lem5201048 y x)). Qed.
Lemma lem5201051 (x : real) (y : real) : (term184 x y) = (term134 x y).
Proof. exact (eq_refl (term184 x y)). Qed.
Lemma lem5201052 (x : real) (y : real) : (term185 x y) = (term135 x y).
Proof. exact (MK_COMB (@lem5201050 y x) (@lem5201051 x y)). Qed.
Lemma lem5201053 (x : real) : (term186 x) = (term160 x).
Proof. exact (fun_ext (fun y : real => @lem5201052 x y)). Qed.
Lemma lem5201054 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201055 (x : real) : (term178 x) = (term171 x).
Proof. exact (MK_COMB (@lem5201054) (@lem5201053 x)). Qed.
Lemma lem5201056 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5201057 (x : real) : (term187 x) = (term188 x).
Proof. exact (MK_COMB (@lem5201056) (@lem5201055 x)). Qed.
Lemma lem5201058 (y : real) (x : real) : (term182 x y) = (term128 y x).
Proof. exact (eq_refl (term182 x y)). Qed.
Lemma lem5201059 (x : real) : (term189 x) = (term180 x).
Proof. exact (fun_ext (fun y : real => @lem5201058 y x)). Qed.
Lemma lem5201060 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201061 (x : real) : (term190 x) = (term191 x).
Proof. exact (MK_COMB (@lem5201060) (@lem5201059 x)). Qed.
Lemma lem5201062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5201063 (x : real) : (term192 x) = (term193 x).
Proof. exact (MK_COMB (@lem5201062) (@lem5201061 x)). Qed.
Lemma lem5201064 (x : real) (y : real) : (term184 x y) = (term134 x y).
Proof. exact (eq_refl (term184 x y)). Qed.
Lemma lem5201065 (x : real) : (term194 x) = (term181 x).
Proof. exact (fun_ext (fun y : real => @lem5201064 x y)). Qed.
Lemma lem5201066 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201067 (x : real) : (term195 x) = (term196 x).
Proof. exact (MK_COMB (@lem5201066) (@lem5201065 x)). Qed.
Lemma lem5201068 (x : real) : (term179 x) = (term197 x).
Proof. exact (MK_COMB (@lem5201063 x) (@lem5201067 x)). Qed.
Lemma lem5201069 (x : real) : ((term178 x) = (term179 x)) = ((term171 x) = (term197 x)).
Proof. exact (MK_COMB (@lem5201057 x) (@lem5201068 x)). Qed.
Lemma lem5201070 (x : real) : (term171 x) = (term197 x).
Proof. exact (EQ_MP (@lem5201069 x) (@lem5201047 x)). Qed.
Lemma lem5201185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5201186 (x : real) : (term173 x) = (term198 x).
Proof. exact (MK_COMB (@lem5201185) (@lem5201070 x)). Qed.
Lemma lem5201201 (x : real) : (term176 x) = (term176 x).
Proof. exact (eq_refl (term176 x)). Qed.
Lemma lem5201202 (x : real) : (term177 x) = (term199 x).
Proof. exact (MK_COMB (@lem5201186 x) (@lem5201201 x)). Qed.
Lemma lem5201205 (x : real) : (term144 x) = (term199 x).
Proof. exact (TRANS (@lem5201041 x) (@lem5201202 x)). Qed.
Lemma lem5201206 : term145 = term200.
Proof. exact (fun_ext (fun x : real => @lem5201205 x)). Qed.
Lemma lem5201207 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201208 : term146 = term201.
Proof. exact (MK_COMB (@lem5201207) (@lem5201206)). Qed.
Lemma lem5201210 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem5201211 (P : real -> Prop) (Q : real -> Prop) : (term156 P Q) = (term157 P Q).
Proof. exact (@lem5201210 real P Q). Qed.
Lemma lem5201212 : term202 = term203.
Proof. exact (@lem5201211 term204 term205). Qed.
Lemma lem5201213 (x : real) : (term206 x) = (term197 x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem5201214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5201215 (x : real) : (term207 x) = (term198 x).
Proof. exact (MK_COMB (@lem5201214) (@lem5201213 x)). Qed.
Lemma lem5201216 (x : real) : (term208 x) = (term176 x).
Proof. exact (eq_refl (term208 x)). Qed.
Lemma lem5201217 (x : real) : (term209 x) = (term199 x).
Proof. exact (MK_COMB (@lem5201215 x) (@lem5201216 x)). Qed.
Lemma lem5201218 : term210 = term200.
Proof. exact (fun_ext (fun x : real => @lem5201217 x)). Qed.
Lemma lem5201219 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201220 : term202 = term201.
Proof. exact (MK_COMB (@lem5201219) (@lem5201218)). Qed.
Lemma lem5201221 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5201222 : term211 = term212.
Proof. exact (MK_COMB (@lem5201221) (@lem5201220)). Qed.
Lemma lem5201223 (x : real) : (term206 x) = (term197 x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem5201224 : term213 = term204.
Proof. exact (fun_ext (fun x : real => @lem5201223 x)). Qed.
Lemma lem5201225 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201226 : term214 = term215.
Proof. exact (MK_COMB (@lem5201225) (@lem5201224)). Qed.
Lemma lem5201227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5201228 : term216 = term217.
Proof. exact (MK_COMB (@lem5201227) (@lem5201226)). Qed.
Lemma lem5201229 (x : real) : (term208 x) = (term176 x).
Proof. exact (eq_refl (term208 x)). Qed.
Lemma lem5201230 : term218 = term205.
Proof. exact (fun_ext (fun x : real => @lem5201229 x)). Qed.
Lemma lem5201231 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201232 : term219 = term220.
Proof. exact (MK_COMB (@lem5201231) (@lem5201230)). Qed.
Lemma lem5201233 : term203 = term221.
Proof. exact (MK_COMB (@lem5201228) (@lem5201232)). Qed.
Lemma lem5201234 : (term202 = term203) = (term201 = term221).
Proof. exact (MK_COMB (@lem5201222) (@lem5201233)). Qed.
Lemma lem5201235 : term201 = term221.
Proof. exact (EQ_MP (@lem5201234) (@lem5201212)). Qed.
Lemma lem5201239 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem5201240 (P : real -> Prop) (Q : real -> Prop) : (term156 P Q) = (term157 P Q).
Proof. exact (@lem5201239 real P Q). Qed.
Lemma lem5201241 : term222 = term223.
Proof. exact (@lem5201240 term224 term225). Qed.
Lemma lem5201242 (x : real) : (term226 x) = (term191 x).
Proof. exact (eq_refl (term226 x)). Qed.
Lemma lem5201243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5201244 (x : real) : (term227 x) = (term193 x).
Proof. exact (MK_COMB (@lem5201243) (@lem5201242 x)). Qed.
Lemma lem5201245 (x : real) : (term228 x) = (term196 x).
Proof. exact (eq_refl (term228 x)). Qed.
Lemma lem5201246 (x : real) : (term229 x) = (term197 x).
Proof. exact (MK_COMB (@lem5201244 x) (@lem5201245 x)). Qed.
Lemma lem5201247 : term230 = term204.
Proof. exact (fun_ext (fun x : real => @lem5201246 x)). Qed.
Lemma lem5201248 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201249 : term222 = term215.
Proof. exact (MK_COMB (@lem5201248) (@lem5201247)). Qed.
Lemma lem5201250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5201251 : term231 = term232.
Proof. exact (MK_COMB (@lem5201250) (@lem5201249)). Qed.
Lemma lem5201252 (x : real) : (term226 x) = (term191 x).
Proof. exact (eq_refl (term226 x)). Qed.
Lemma lem5201253 : term233 = term224.
Proof. exact (fun_ext (fun x : real => @lem5201252 x)). Qed.
Lemma lem5201254 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201255 : term234 = term235.
Proof. exact (MK_COMB (@lem5201254) (@lem5201253)). Qed.
Lemma lem5201256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5201257 : term236 = term237.
Proof. exact (MK_COMB (@lem5201256) (@lem5201255)). Qed.
Lemma lem5201258 (x : real) : (term228 x) = (term196 x).
Proof. exact (eq_refl (term228 x)). Qed.
Lemma lem5201259 : term238 = term225.
Proof. exact (fun_ext (fun x : real => @lem5201258 x)). Qed.
Lemma lem5201260 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201261 : term239 = term240.
Proof. exact (MK_COMB (@lem5201260) (@lem5201259)). Qed.
Lemma lem5201262 : term223 = term241.
Proof. exact (MK_COMB (@lem5201257) (@lem5201261)). Qed.
Lemma lem5201263 : (term222 = term223) = (term215 = term241).
Proof. exact (MK_COMB (@lem5201251) (@lem5201262)). Qed.
Lemma lem5201264 : term215 = term241.
Proof. exact (EQ_MP (@lem5201263) (@lem5201241)). Qed.
Lemma lem5201387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5201388 : term217 = term242.
Proof. exact (MK_COMB (@lem5201387) (@lem5201264)). Qed.
Lemma lem5201407 : term220 = term220.
Proof. exact (eq_refl term220). Qed.
Lemma lem5201408 : term221 = term243.
Proof. exact (MK_COMB (@lem5201388) (@lem5201407)). Qed.
Lemma lem5201411 : term201 = term243.
Proof. exact (TRANS (@lem5201235) (@lem5201408)). Qed.
Lemma lem5201412 : term146 = term243.
Proof. exact (TRANS (@lem5201208) (@lem5201411)). Qed.
Lemma lem5201413 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5201414 : term149 = term244.
Proof. exact (MK_COMB (@lem5201413) (@lem5201412)). Qed.
Lemma lem5201415 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5201416 : term245 = term246.
Proof. exact (MK_COMB (@lem5201415) (@lem5201414)). Qed.
Lemma lem5201418 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5201419 : term247 = term248.
Proof. exact (@lem5201418 term249). Qed.
Lemma lem5201480 : term150 = term250.
Proof. exact (MK_COMB (@lem5201416) (@lem5201419)). Qed.
Lemma lem5201485 (y : real) (x : real) : (term251 y x) = (term251 y x).
Proof. exact (eq_refl (term251 y x)). Qed.
Lemma lem5201486 (x : real) : (term252 x) = (term252 x).
Proof. exact (fun_ext (fun y : real => @lem5201485 y x)). Qed.
Lemma lem5201487 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201488 (x : real) : (term253 x) = (term253 x).
Proof. exact (MK_COMB (@lem5201487) (@lem5201486 x)). Qed.
Lemma lem5201489 : term254 = term254.
Proof. exact (fun_ext (fun x : real => @lem5201488 x)). Qed.
Lemma lem5201490 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201491 : term249 = term249.
Proof. exact (MK_COMB (@lem5201490) (@lem5201489)). Qed.
Lemma lem5201492 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5201493 : term248 = term248.
Proof. exact (MK_COMB (@lem5201492) (@lem5201491)). Qed.
Lemma lem5201506 (x : real) (x' : real) (y : real) : (term139 x x' y) = (term139 x x' y).
Proof. exact (eq_refl (term139 x x' y)). Qed.
Lemma lem5201507 (x : real) (y : real) : (term140 x y) = (term140 x y).
Proof. exact (fun_ext (fun x' : real => @lem5201506 x x' y)). Qed.
Lemma lem5201508 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201509 (x : real) (y : real) : (term141 x y) = (term141 x y).
Proof. exact (MK_COMB (@lem5201508) (@lem5201507 x y)). Qed.
Lemma lem5201510 (x : real) : (term161 x) = (term161 x).
Proof. exact (fun_ext (fun y : real => @lem5201509 x y)). Qed.
Lemma lem5201511 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201512 (x : real) : (term176 x) = (term176 x).
Proof. exact (MK_COMB (@lem5201511) (@lem5201510 x)). Qed.
Lemma lem5201513 : term205 = term205.
Proof. exact (fun_ext (fun x : real => @lem5201512 x)). Qed.
Lemma lem5201514 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201515 : term220 = term220.
Proof. exact (MK_COMB (@lem5201514) (@lem5201513)). Qed.
Lemma lem5201524 (x : real) (y : real) (x' : real) : (term131 x y x') = (term131 x y x').
Proof. exact (eq_refl (term131 x y x')). Qed.
Lemma lem5201525 (x : real) (y : real) : (term133 x y) = (term133 x y).
Proof. exact (fun_ext (fun x' : real => @lem5201524 x y x')). Qed.
Lemma lem5201526 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5201527 (x : real) (y : real) : (term134 x y) = (term134 x y).
Proof. exact (MK_COMB (@lem5201526) (@lem5201525 x y)). Qed.
Lemma lem5201528 (x : real) : (term181 x) = (term181 x).
Proof. exact (fun_ext (fun y : real => @lem5201527 x y)). Qed.
Lemma lem5201529 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201530 (x : real) : (term196 x) = (term196 x).
Proof. exact (MK_COMB (@lem5201529) (@lem5201528 x)). Qed.
Lemma lem5201531 : term225 = term225.
Proof. exact (fun_ext (fun x : real => @lem5201530 x)). Qed.
Lemma lem5201532 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201533 : term240 = term240.
Proof. exact (MK_COMB (@lem5201532) (@lem5201531)). Qed.
Lemma lem5201542 (y : real) (x : real) (x' : real) : (term125 y x x') = (term125 y x x').
Proof. exact (eq_refl (term125 y x x')). Qed.
Lemma lem5201543 (y : real) (x : real) : (term127 y x) = (term127 y x).
Proof. exact (fun_ext (fun x' : real => @lem5201542 y x x')). Qed.
Lemma lem5201544 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5201545 (y : real) (x : real) : (term128 y x) = (term128 y x).
Proof. exact (MK_COMB (@lem5201544) (@lem5201543 y x)). Qed.
Lemma lem5201546 (x : real) : (term180 x) = (term180 x).
Proof. exact (fun_ext (fun y : real => @lem5201545 y x)). Qed.
Lemma lem5201547 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201548 (x : real) : (term191 x) = (term191 x).
Proof. exact (MK_COMB (@lem5201547) (@lem5201546 x)). Qed.
Lemma lem5201549 : term224 = term224.
Proof. exact (fun_ext (fun x : real => @lem5201548 x)). Qed.
Lemma lem5201550 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201551 : term235 = term235.
Proof. exact (MK_COMB (@lem5201550) (@lem5201549)). Qed.
Lemma lem5201552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5201553 : term237 = term237.
Proof. exact (MK_COMB (@lem5201552) (@lem5201551)). Qed.
Lemma lem5201554 : term241 = term241.
Proof. exact (MK_COMB (@lem5201553) (@lem5201533)). Qed.
Lemma lem5201555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5201556 : term242 = term242.
Proof. exact (MK_COMB (@lem5201555) (@lem5201554)). Qed.
Lemma lem5201557 : term243 = term243.
Proof. exact (MK_COMB (@lem5201556) (@lem5201515)). Qed.
Lemma lem5201558 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5201559 : term244 = term244.
Proof. exact (MK_COMB (@lem5201558) (@lem5201557)). Qed.
Lemma lem5201560 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5201561 : term246 = term246.
Proof. exact (MK_COMB (@lem5201560) (@lem5201559)). Qed.
Lemma lem5201562 : term250 = term250.
Proof. exact (MK_COMB (@lem5201561) (@lem5201493)). Qed.
Lemma lem5201653 : term150 = term250.
Proof. exact (TRANS (@lem5201480) (@lem5201562)). Qed.
Lemma lem5201654 : term250 = term150.
Proof. exact (SYM (@lem5201653)). Qed.
Lemma lem5201655 (h1 : term244) : term244.
Proof. exact (h1). Qed.
Lemma lem5201656 (h1 : term249) : term249.
Proof. exact (h1). Qed.
Lemma lem5201663 (x : real) (x' : real) (y : real) : (term255 x x' y) = (term256 x x' y).
Proof. exact (@lem17160 (x' = x) (x' = y)). Qed.
Lemma lem5201664 (x : real) (x' : real) : (term257 x x') = (term257 x x').
Proof. exact (eq_refl (term257 x x')). Qed.
Lemma lem5201665 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5201666 (x : real) (x' : real) (y : real) : (term258 x x' y) = (term259 x x' y).
Proof. exact (MK_COMB (@lem5201665) (@lem5201663 x x' y)). Qed.
Lemma lem5201667 (y : real) (x : real) (x' : real) : (term260 y x x') = (term261 y x x').
Proof. exact (MK_COMB (@lem5201666 x x' y) (@lem5201664 x x')). Qed.
Lemma lem5201668 (y : real) (x : real) (x' : real) : (term262 y x x') = (term260 y x x').
Proof. exact (@lem17045 (term121 x x' y) (real_le x x')). Qed.
Lemma lem5201669 (y : real) (x : real) (x' : real) : (term262 y x x') = (term261 y x x').
Proof. exact (TRANS (@lem5201668 y x x') (@lem5201667 y x x')). Qed.
Lemma lem5201670 (P : real -> Prop) : (term263 P) = (term264 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5201671 (y : real) (x : real) : (term265 y x) = (term266 y x).
Proof. exact (@lem5201670 (term127 y x)). Qed.
Lemma lem5201672 (y : real) (x : real) (x' : real) : (term267 y x x') = (term125 y x x').
Proof. exact (eq_refl (term267 y x x')). Qed.
Lemma lem5201673 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5201674 (y : real) (x : real) (x' : real) : (term268 y x x') = (term262 y x x').
Proof. exact (MK_COMB (@lem5201673) (@lem5201672 y x x')). Qed.
Lemma lem5201675 (y : real) (x : real) (x' : real) : (term268 y x x') = (term261 y x x').
Proof. exact (TRANS (@lem5201674 y x x') (@lem5201669 y x x')). Qed.
Lemma lem5201676 (y : real) (x : real) : (term269 y x) = (term270 y x).
Proof. exact (fun_ext (fun x' : real => @lem5201675 y x x')). Qed.
Lemma lem5201677 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201678 (y : real) (x : real) : (term266 y x) = (term271 y x).
Proof. exact (MK_COMB (@lem5201677) (@lem5201676 y x)). Qed.
Lemma lem5201679 (y : real) (x : real) : (term265 y x) = (term271 y x).
Proof. exact (TRANS (@lem5201671 y x) (@lem5201678 y x)). Qed.
Lemma lem5201680 (P : real -> Prop) : (term272 P) = (term273 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5201681 (x : real) : (term274 x) = (term275 x).
Proof. exact (@lem5201680 (term180 x)). Qed.
Lemma lem5201682 (y : real) (x : real) : (term182 x y) = (term128 y x).
Proof. exact (eq_refl (term182 x y)). Qed.
Lemma lem5201683 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5201684 (y : real) (x : real) : (term276 x y) = (term265 y x).
Proof. exact (MK_COMB (@lem5201683) (@lem5201682 y x)). Qed.
Lemma lem5201685 (y : real) (x : real) : (term276 x y) = (term271 y x).
Proof. exact (TRANS (@lem5201684 y x) (@lem5201679 y x)). Qed.
Lemma lem5201686 (x : real) : (term277 x) = (term278 x).
Proof. exact (fun_ext (fun y : real => @lem5201685 y x)). Qed.
Lemma lem5201687 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5201688 (x : real) : (term275 x) = (term279 x).
Proof. exact (MK_COMB (@lem5201687) (@lem5201686 x)). Qed.
Lemma lem5201689 (x : real) : (term274 x) = (term279 x).
Proof. exact (TRANS (@lem5201681 x) (@lem5201688 x)). Qed.
Lemma lem5201690 (P : real -> Prop) : (term272 P) = (term273 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5201691 : term280 = term281.
Proof. exact (@lem5201690 term224). Qed.
Lemma lem5201692 (x : real) : (term226 x) = (term191 x).
Proof. exact (eq_refl (term226 x)). Qed.
Lemma lem5201693 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5201694 (x : real) : (term282 x) = (term274 x).
Proof. exact (MK_COMB (@lem5201693) (@lem5201692 x)). Qed.
Lemma lem5201695 (x : real) : (term282 x) = (term279 x).
Proof. exact (TRANS (@lem5201694 x) (@lem5201689 x)). Qed.
Lemma lem5201696 : term283 = term284.
Proof. exact (fun_ext (fun x : real => @lem5201695 x)). Qed.
Lemma lem5201697 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5201698 : term281 = term285.
Proof. exact (MK_COMB (@lem5201697) (@lem5201696)). Qed.
Lemma lem5201699 : term280 = term285.
Proof. exact (TRANS (@lem5201691) (@lem5201698)). Qed.
Lemma lem5201706 (x : real) (x' : real) (y : real) : (term255 x x' y) = (term256 x x' y).
Proof. exact (@lem17160 (x' = x) (x' = y)). Qed.
Lemma lem5201707 (y : real) (x' : real) : (term257 y x') = (term257 y x').
Proof. exact (eq_refl (term257 y x')). Qed.
Lemma lem5201708 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5201709 (x : real) (x' : real) (y : real) : (term258 x x' y) = (term259 x x' y).
Proof. exact (MK_COMB (@lem5201708) (@lem5201706 x x' y)). Qed.
Lemma lem5201710 (x : real) (y : real) (x' : real) : (term286 x y x') = (term287 x y x').
Proof. exact (MK_COMB (@lem5201709 x x' y) (@lem5201707 y x')). Qed.
Lemma lem5201711 (x : real) (y : real) (x' : real) : (term288 x y x') = (term286 x y x').
Proof. exact (@lem17045 (term121 x x' y) (real_le y x')). Qed.
Lemma lem5201712 (x : real) (y : real) (x' : real) : (term288 x y x') = (term287 x y x').
Proof. exact (TRANS (@lem5201711 x y x') (@lem5201710 x y x')). Qed.
Lemma lem5201713 (P : real -> Prop) : (term263 P) = (term264 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5201714 (x : real) (y : real) : (term289 x y) = (term290 x y).
Proof. exact (@lem5201713 (term133 x y)). Qed.
Lemma lem5201715 (x : real) (y : real) (x' : real) : (term291 x y x') = (term131 x y x').
Proof. exact (eq_refl (term291 x y x')). Qed.
Lemma lem5201716 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5201717 (x : real) (y : real) (x' : real) : (term292 x y x') = (term288 x y x').
Proof. exact (MK_COMB (@lem5201716) (@lem5201715 x y x')). Qed.
Lemma lem5201718 (x : real) (y : real) (x' : real) : (term292 x y x') = (term287 x y x').
Proof. exact (TRANS (@lem5201717 x y x') (@lem5201712 x y x')). Qed.
Lemma lem5201719 (x : real) (y : real) : (term293 x y) = (term294 x y).
Proof. exact (fun_ext (fun x' : real => @lem5201718 x y x')). Qed.
Lemma lem5201720 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5201721 (x : real) (y : real) : (term290 x y) = (term295 x y).
Proof. exact (MK_COMB (@lem5201720) (@lem5201719 x y)). Qed.
Lemma lem5201722 (x : real) (y : real) : (term289 x y) = (term295 x y).
Proof. exact (TRANS (@lem5201714 x y) (@lem5201721 x y)). Qed.
Lemma lem5201723 (P : real -> Prop) : (term272 P) = (term273 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5201724 (x : real) : (term296 x) = (term297 x).
Proof. exact (@lem5201723 (term181 x)). Qed.
Lemma lem5201725 (x : real) (y : real) : (term184 x y) = (term134 x y).
Proof. exact (eq_refl (term184 x y)). Qed.
Lemma lem5201726 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5201727 (x : real) (y : real) : (term298 x y) = (term289 x y).
Proof. exact (MK_COMB (@lem5201726) (@lem5201725 x y)). Qed.
Lemma lem5201728 (x : real) (y : real) : (term298 x y) = (term295 x y).
Proof. exact (TRANS (@lem5201727 x y) (@lem5201722 x y)). Qed.
Lemma lem5201729 (x : real) : (term299 x) = (term300 x).
Proof. exact (fun_ext (fun y : real => @lem5201728 x y)). Qed.
Lemma lem5201730 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5201731 (x : real) : (term297 x) = (term301 x).
Proof. exact (MK_COMB (@lem5201730) (@lem5201729 x)). Qed.
Lemma lem5201732 (x : real) : (term296 x) = (term301 x).
Proof. exact (TRANS (@lem5201724 x) (@lem5201731 x)). Qed.
Lemma lem5201733 (P : real -> Prop) : (term272 P) = (term273 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5201734 : term302 = term303.
Proof. exact (@lem5201733 term225). Qed.
Lemma lem5201735 (x : real) : (term228 x) = (term196 x).
Proof. exact (eq_refl (term228 x)). Qed.
Lemma lem5201736 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5201737 (x : real) : (term304 x) = (term296 x).
Proof. exact (MK_COMB (@lem5201736) (@lem5201735 x)). Qed.
Lemma lem5201738 (x : real) : (term304 x) = (term301 x).
Proof. exact (TRANS (@lem5201737 x) (@lem5201732 x)). Qed.
Lemma lem5201739 : term305 = term306.
Proof. exact (fun_ext (fun x : real => @lem5201738 x)). Qed.
Lemma lem5201740 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5201741 : term303 = term307.
Proof. exact (MK_COMB (@lem5201740) (@lem5201739)). Qed.
Lemma lem5201742 : term302 = term307.
Proof. exact (TRANS (@lem5201734) (@lem5201741)). Qed.
Lemma lem5201743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5201744 : term308 = term309.
Proof. exact (MK_COMB (@lem5201743) (@lem5201699)). Qed.
Lemma lem5201745 : term310 = term311.
Proof. exact (MK_COMB (@lem5201744) (@lem5201742)). Qed.
Lemma lem5201746 : term312 = term310.
Proof. exact (@lem17045 term235 term240). Qed.
Lemma lem5201747 : term312 = term311.
Proof. exact (TRANS (@lem5201746) (@lem5201745)). Qed.
Lemma lem5201759 (x : real) (x' : real) (y : real) : (term313 x x' y) = (term314 x x' y).
Proof. exact (@lem17160 (real_le x' x) (real_le x' y)). Qed.
Lemma lem5201761 (x : real) (x' : real) (y : real) : (term123 x x' y) = (term123 x x' y).
Proof. exact (eq_refl (term123 x x' y)). Qed.
Lemma lem5201762 (x : real) (x' : real) (y : real) : (term315 x x' y) = (term316 x x' y).
Proof. exact (MK_COMB (@lem5201761 x x' y) (@lem5201759 x x' y)). Qed.
Lemma lem5201763 (x : real) (x' : real) (y : real) : (term317 x x' y) = (term315 x x' y).
Proof. exact (@lem17362 (term121 x x' y) (term25 x x' y)). Qed.
Lemma lem5201764 (x : real) (x' : real) (y : real) : (term317 x x' y) = (term316 x x' y).
Proof. exact (TRANS (@lem5201763 x x' y) (@lem5201762 x x' y)). Qed.
Lemma lem5201765 (P : real -> Prop) : (term272 P) = (term273 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5201766 (x : real) (y : real) : (term318 x y) = (term319 x y).
Proof. exact (@lem5201765 (term140 x y)). Qed.
Lemma lem5201767 (x : real) (x' : real) (y : real) : (term320 x y x') = (term139 x x' y).
Proof. exact (eq_refl (term320 x y x')). Qed.
Lemma lem5201768 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5201769 (x : real) (x' : real) (y : real) : (term321 x y x') = (term317 x x' y).
Proof. exact (MK_COMB (@lem5201768) (@lem5201767 x x' y)). Qed.
Lemma lem5201770 (x : real) (x' : real) (y : real) : (term321 x y x') = (term316 x x' y).
Proof. exact (TRANS (@lem5201769 x x' y) (@lem5201764 x x' y)). Qed.
Lemma lem5201771 (x : real) (y : real) : (term322 x y) = (term323 x y).
Proof. exact (fun_ext (fun x' : real => @lem5201770 x x' y)). Qed.
Lemma lem5201772 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5201773 (x : real) (y : real) : (term319 x y) = (term324 x y).
Proof. exact (MK_COMB (@lem5201772) (@lem5201771 x y)). Qed.
Lemma lem5201774 (x : real) (y : real) : (term318 x y) = (term324 x y).
Proof. exact (TRANS (@lem5201766 x y) (@lem5201773 x y)). Qed.
Lemma lem5201775 (P : real -> Prop) : (term272 P) = (term273 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5201776 (x : real) : (term325 x) = (term326 x).
Proof. exact (@lem5201775 (term161 x)). Qed.
Lemma lem5201777 (x : real) (y : real) : (term164 x y) = (term141 x y).
Proof. exact (eq_refl (term164 x y)). Qed.
Lemma lem5201778 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5201779 (x : real) (y : real) : (term327 x y) = (term318 x y).
Proof. exact (MK_COMB (@lem5201778) (@lem5201777 x y)). Qed.
Lemma lem5201780 (x : real) (y : real) : (term327 x y) = (term324 x y).
Proof. exact (TRANS (@lem5201779 x y) (@lem5201774 x y)). Qed.
Lemma lem5201781 (x : real) : (term328 x) = (term329 x).
Proof. exact (fun_ext (fun y : real => @lem5201780 x y)). Qed.
Lemma lem5201782 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5201783 (x : real) : (term326 x) = (term330 x).
Proof. exact (MK_COMB (@lem5201782) (@lem5201781 x)). Qed.
Lemma lem5201784 (x : real) : (term325 x) = (term330 x).
Proof. exact (TRANS (@lem5201776 x) (@lem5201783 x)). Qed.
Lemma lem5201785 (P : real -> Prop) : (term272 P) = (term273 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5201786 : term331 = term332.
Proof. exact (@lem5201785 term205). Qed.
Lemma lem5201787 (x : real) : (term208 x) = (term176 x).
Proof. exact (eq_refl (term208 x)). Qed.
Lemma lem5201788 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5201789 (x : real) : (term333 x) = (term325 x).
Proof. exact (MK_COMB (@lem5201788) (@lem5201787 x)). Qed.
Lemma lem5201790 (x : real) : (term333 x) = (term330 x).
Proof. exact (TRANS (@lem5201789 x) (@lem5201784 x)). Qed.
Lemma lem5201791 : term334 = term335.
Proof. exact (fun_ext (fun x : real => @lem5201790 x)). Qed.
Lemma lem5201792 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5201793 : term332 = term336.
Proof. exact (MK_COMB (@lem5201792) (@lem5201791)). Qed.
Lemma lem5201794 : term331 = term336.
Proof. exact (TRANS (@lem5201786) (@lem5201793)). Qed.
Lemma lem5201795 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5201796 : term337 = term338.
Proof. exact (MK_COMB (@lem5201795) (@lem5201747)). Qed.
Lemma lem5201797 : term339 = term340.
Proof. exact (MK_COMB (@lem5201796) (@lem5201794)). Qed.
Lemma lem5201798 : term244 = term339.
Proof. exact (@lem17045 term241 term220). Qed.
Lemma lem5201799 : term244 = term340.
Proof. exact (TRANS (@lem5201798) (@lem5201797)). Qed.
Lemma lem5201970 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term341 A P Q) = (term342 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5201971 (P : real -> Prop) (Q : real -> Prop) : (term343 P Q) = (term344 P Q).
Proof. exact (@lem5201970 real P Q). Qed.
Lemma lem5201972 : term345 = term346.
Proof. exact (@lem5201971 term284 term306). Qed.
Lemma lem5201973 (x : real) : (term347 x) = (term279 x).
Proof. exact (eq_refl (term347 x)). Qed.
Lemma lem5201974 : term348 = term284.
Proof. exact (fun_ext (fun x : real => @lem5201973 x)). Qed.
Lemma lem5201975 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5201976 : term349 = term285.
Proof. exact (MK_COMB (@lem5201975) (@lem5201974)). Qed.
Lemma lem5201977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5201978 : term350 = term309.
Proof. exact (MK_COMB (@lem5201977) (@lem5201976)). Qed.
Lemma lem5201979 (x : real) : (term351 x) = (term301 x).
Proof. exact (eq_refl (term351 x)). Qed.
Lemma lem5201980 : term352 = term306.
Proof. exact (fun_ext (fun x : real => @lem5201979 x)). Qed.
Lemma lem5201981 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5201982 : term353 = term307.
Proof. exact (MK_COMB (@lem5201981) (@lem5201980)). Qed.
Lemma lem5201983 : term345 = term311.
Proof. exact (MK_COMB (@lem5201978) (@lem5201982)). Qed.
Lemma lem5201984 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5201985 : term354 = term355.
Proof. exact (MK_COMB (@lem5201984) (@lem5201983)). Qed.
Lemma lem5201986 (x : real) : (term347 x) = (term279 x).
Proof. exact (eq_refl (term347 x)). Qed.
Lemma lem5201987 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5201988 (x : real) : (term356 x) = (term357 x).
Proof. exact (MK_COMB (@lem5201987) (@lem5201986 x)). Qed.
Lemma lem5201989 (x : real) : (term351 x) = (term301 x).
Proof. exact (eq_refl (term351 x)). Qed.
Lemma lem5201990 (x : real) : (term358 x) = (term359 x).
Proof. exact (MK_COMB (@lem5201988 x) (@lem5201989 x)). Qed.
Lemma lem5201991 : term360 = term361.
Proof. exact (fun_ext (fun x : real => @lem5201990 x)). Qed.
Lemma lem5201992 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5201993 : term346 = term362.
Proof. exact (MK_COMB (@lem5201992) (@lem5201991)). Qed.
Lemma lem5201994 : (term345 = term346) = (term311 = term362).
Proof. exact (MK_COMB (@lem5201985) (@lem5201993)). Qed.
Lemma lem5201995 : term311 = term362.
Proof. exact (EQ_MP (@lem5201994) (@lem5201972)). Qed.
Lemma lem5201997 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term341 A P Q) = (term342 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5201998 (P : real -> Prop) (Q : real -> Prop) : (term343 P Q) = (term344 P Q).
Proof. exact (@lem5201997 real P Q). Qed.
Lemma lem5201999 (x : real) : (term363 x) = (term364 x).
Proof. exact (@lem5201998 (term278 x) (term300 x)). Qed.
Lemma lem5202000 (y : real) (x : real) : (term365 x y) = (term271 y x).
Proof. exact (eq_refl (term365 x y)). Qed.
Lemma lem5202001 (x : real) : (term366 x) = (term278 x).
Proof. exact (fun_ext (fun y : real => @lem5202000 y x)). Qed.
Lemma lem5202002 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5202003 (x : real) : (term367 x) = (term279 x).
Proof. exact (MK_COMB (@lem5202002) (@lem5202001 x)). Qed.
Lemma lem5202004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5202005 (x : real) : (term368 x) = (term357 x).
Proof. exact (MK_COMB (@lem5202004) (@lem5202003 x)). Qed.
Lemma lem5202006 (x : real) (y : real) : (term369 x y) = (term295 x y).
Proof. exact (eq_refl (term369 x y)). Qed.
Lemma lem5202007 (x : real) : (term370 x) = (term300 x).
Proof. exact (fun_ext (fun y : real => @lem5202006 x y)). Qed.
Lemma lem5202008 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5202009 (x : real) : (term371 x) = (term301 x).
Proof. exact (MK_COMB (@lem5202008) (@lem5202007 x)). Qed.
Lemma lem5202010 (x : real) : (term363 x) = (term359 x).
Proof. exact (MK_COMB (@lem5202005 x) (@lem5202009 x)). Qed.
Lemma lem5202011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5202012 (x : real) : (term372 x) = (term373 x).
Proof. exact (MK_COMB (@lem5202011) (@lem5202010 x)). Qed.
Lemma lem5202013 (y : real) (x : real) : (term365 x y) = (term271 y x).
Proof. exact (eq_refl (term365 x y)). Qed.
Lemma lem5202014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5202015 (y : real) (x : real) : (term374 x y) = (term375 y x).
Proof. exact (MK_COMB (@lem5202014) (@lem5202013 y x)). Qed.
Lemma lem5202016 (x : real) (y : real) : (term369 x y) = (term295 x y).
Proof. exact (eq_refl (term369 x y)). Qed.
Lemma lem5202017 (x : real) (y : real) : (term376 x y) = (term377 x y).
Proof. exact (MK_COMB (@lem5202015 y x) (@lem5202016 x y)). Qed.
Lemma lem5202018 (x : real) : (term378 x) = (term379 x).
Proof. exact (fun_ext (fun y : real => @lem5202017 x y)). Qed.
Lemma lem5202019 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5202020 (x : real) : (term364 x) = (term380 x).
Proof. exact (MK_COMB (@lem5202019) (@lem5202018 x)). Qed.
Lemma lem5202021 (x : real) : ((term363 x) = (term364 x)) = ((term359 x) = (term380 x)).
Proof. exact (MK_COMB (@lem5202012 x) (@lem5202020 x)). Qed.
Lemma lem5202022 (x : real) : (term359 x) = (term380 x).
Proof. exact (EQ_MP (@lem5202021 x) (@lem5201999 x)). Qed.
Lemma lem5202023 : term361 = term381.
Proof. exact (fun_ext (fun x : real => @lem5202022 x)). Qed.
Lemma lem5202024 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5202025 : term362 = term382.
Proof. exact (MK_COMB (@lem5202024) (@lem5202023)). Qed.
Lemma lem5202026 : term311 = term382.
Proof. exact (TRANS (@lem5201995) (@lem5202025)). Qed.
Lemma lem5202027 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5202028 : term338 = term383.
Proof. exact (MK_COMB (@lem5202027) (@lem5202026)). Qed.
Lemma lem5202029 : term336 = term336.
Proof. exact (eq_refl term336). Qed.
Lemma lem5202030 : term340 = term384.
Proof. exact (MK_COMB (@lem5202028) (@lem5202029)). Qed.
Lemma lem5202032 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term341 A P Q) = (term342 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5202033 (P : real -> Prop) (Q : real -> Prop) : (term343 P Q) = (term344 P Q).
Proof. exact (@lem5202032 real P Q). Qed.
Lemma lem5202034 : term385 = term386.
Proof. exact (@lem5202033 term381 term335). Qed.
Lemma lem5202035 (x : real) : (term387 x) = (term380 x).
Proof. exact (eq_refl (term387 x)). Qed.
Lemma lem5202036 : term388 = term381.
Proof. exact (fun_ext (fun x : real => @lem5202035 x)). Qed.
Lemma lem5202037 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5202038 : term389 = term382.
Proof. exact (MK_COMB (@lem5202037) (@lem5202036)). Qed.
Lemma lem5202039 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5202040 : term390 = term383.
Proof. exact (MK_COMB (@lem5202039) (@lem5202038)). Qed.
Lemma lem5202041 (x : real) : (term391 x) = (term330 x).
Proof. exact (eq_refl (term391 x)). Qed.
Lemma lem5202042 : term392 = term335.
Proof. exact (fun_ext (fun x : real => @lem5202041 x)). Qed.
Lemma lem5202043 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5202044 : term393 = term336.
Proof. exact (MK_COMB (@lem5202043) (@lem5202042)). Qed.
Lemma lem5202045 : term385 = term384.
Proof. exact (MK_COMB (@lem5202040) (@lem5202044)). Qed.
Lemma lem5202046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5202047 : term394 = term395.
Proof. exact (MK_COMB (@lem5202046) (@lem5202045)). Qed.
Lemma lem5202048 (x : real) : (term387 x) = (term380 x).
Proof. exact (eq_refl (term387 x)). Qed.
Lemma lem5202049 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5202050 (x : real) : (term396 x) = (term397 x).
Proof. exact (MK_COMB (@lem5202049) (@lem5202048 x)). Qed.
Lemma lem5202051 (x : real) : (term391 x) = (term330 x).
Proof. exact (eq_refl (term391 x)). Qed.
Lemma lem5202052 (x : real) : (term398 x) = (term399 x).
Proof. exact (MK_COMB (@lem5202050 x) (@lem5202051 x)). Qed.
Lemma lem5202053 : term400 = term401.
Proof. exact (fun_ext (fun x : real => @lem5202052 x)). Qed.
Lemma lem5202054 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5202055 : term386 = term402.
Proof. exact (MK_COMB (@lem5202054) (@lem5202053)). Qed.
Lemma lem5202056 : (term385 = term386) = (term384 = term402).
Proof. exact (MK_COMB (@lem5202047) (@lem5202055)). Qed.
Lemma lem5202057 : term384 = term402.
Proof. exact (EQ_MP (@lem5202056) (@lem5202034)). Qed.
Lemma lem5202059 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term341 A P Q) = (term342 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5202060 (P : real -> Prop) (Q : real -> Prop) : (term343 P Q) = (term344 P Q).
Proof. exact (@lem5202059 real P Q). Qed.
Lemma lem5202061 (x : real) : (term403 x) = (term404 x).
Proof. exact (@lem5202060 (term379 x) (term329 x)). Qed.
Lemma lem5202062 (x : real) (y : real) : (term405 x y) = (term377 x y).
Proof. exact (eq_refl (term405 x y)). Qed.
Lemma lem5202063 (x : real) : (term406 x) = (term379 x).
Proof. exact (fun_ext (fun y : real => @lem5202062 x y)). Qed.
Lemma lem5202064 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5202065 (x : real) : (term407 x) = (term380 x).
Proof. exact (MK_COMB (@lem5202064) (@lem5202063 x)). Qed.
Lemma lem5202066 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5202067 (x : real) : (term408 x) = (term397 x).
Proof. exact (MK_COMB (@lem5202066) (@lem5202065 x)). Qed.
Lemma lem5202068 (x : real) (y : real) : (term409 x y) = (term324 x y).
Proof. exact (eq_refl (term409 x y)). Qed.
Lemma lem5202069 (x : real) : (term410 x) = (term329 x).
Proof. exact (fun_ext (fun y : real => @lem5202068 x y)). Qed.
Lemma lem5202070 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5202071 (x : real) : (term411 x) = (term330 x).
Proof. exact (MK_COMB (@lem5202070) (@lem5202069 x)). Qed.
Lemma lem5202072 (x : real) : (term403 x) = (term399 x).
Proof. exact (MK_COMB (@lem5202067 x) (@lem5202071 x)). Qed.
Lemma lem5202073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5202074 (x : real) : (term412 x) = (term413 x).
Proof. exact (MK_COMB (@lem5202073) (@lem5202072 x)). Qed.
Lemma lem5202075 (x : real) (y : real) : (term405 x y) = (term377 x y).
Proof. exact (eq_refl (term405 x y)). Qed.
Lemma lem5202076 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5202077 (x : real) (y : real) : (term414 x y) = (term415 x y).
Proof. exact (MK_COMB (@lem5202076) (@lem5202075 x y)). Qed.
Lemma lem5202078 (x : real) (y : real) : (term409 x y) = (term324 x y).
Proof. exact (eq_refl (term409 x y)). Qed.
Lemma lem5202079 (x : real) (y : real) : (term416 x y) = (term417 x y).
Proof. exact (MK_COMB (@lem5202077 x y) (@lem5202078 x y)). Qed.
Lemma lem5202080 (x : real) : (term418 x) = (term419 x).
Proof. exact (fun_ext (fun y : real => @lem5202079 x y)). Qed.
Lemma lem5202081 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5202082 (x : real) : (term404 x) = (term420 x).
Proof. exact (MK_COMB (@lem5202081) (@lem5202080 x)). Qed.
Lemma lem5202083 (x : real) : ((term403 x) = (term404 x)) = ((term399 x) = (term420 x)).
Proof. exact (MK_COMB (@lem5202074 x) (@lem5202082 x)). Qed.
Lemma lem5202084 (x : real) : (term399 x) = (term420 x).
Proof. exact (EQ_MP (@lem5202083 x) (@lem5202061 x)). Qed.
Lemma lem5202086 {A : Type'} (P : Prop) (Q : A -> Prop) : (term421 A P Q) = (term422 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5202087 (P : Prop) (Q : real -> Prop) : (term423 P Q) = (term424 P Q).
Proof. exact (@lem5202086 real P Q). Qed.
Lemma lem5202088 (x : real) (y : real) : (term425 x y) = (term426 x y).
Proof. exact (@lem5202087 (term377 x y) (term323 x y)). Qed.
Lemma lem5202089 (x : real) (x' : real) (y : real) : (term427 x y x') = (term316 x x' y).
Proof. exact (eq_refl (term427 x y x')). Qed.
Lemma lem5202090 (x : real) (y : real) : (term428 x y) = (term323 x y).
Proof. exact (fun_ext (fun x' : real => @lem5202089 x x' y)). Qed.
Lemma lem5202091 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5202092 (x : real) (y : real) : (term429 x y) = (term324 x y).
Proof. exact (MK_COMB (@lem5202091) (@lem5202090 x y)). Qed.
Lemma lem5202093 (x : real) (y : real) : (term415 x y) = (term415 x y).
Proof. exact (eq_refl (term415 x y)). Qed.
Lemma lem5202094 (x : real) (y : real) : (term425 x y) = (term417 x y).
Proof. exact (MK_COMB (@lem5202093 x y) (@lem5202092 x y)). Qed.
Lemma lem5202095 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5202096 (x : real) (y : real) : (term430 x y) = (term431 x y).
Proof. exact (MK_COMB (@lem5202095) (@lem5202094 x y)). Qed.
Lemma lem5202097 (x : real) (x' : real) (y : real) : (term427 x y x') = (term316 x x' y).
Proof. exact (eq_refl (term427 x y x')). Qed.
Lemma lem5202098 (x : real) (y : real) : (term415 x y) = (term415 x y).
Proof. exact (eq_refl (term415 x y)). Qed.
Lemma lem5202099 (x : real) (x' : real) (y : real) : (term432 x y x') = (term433 x x' y).
Proof. exact (MK_COMB (@lem5202098 x y) (@lem5202097 x x' y)). Qed.
Lemma lem5202100 (x : real) (y : real) : (term434 x y) = (term435 x y).
Proof. exact (fun_ext (fun x' : real => @lem5202099 x x' y)). Qed.
Lemma lem5202101 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5202102 (x : real) (y : real) : (term426 x y) = (term436 x y).
Proof. exact (MK_COMB (@lem5202101) (@lem5202100 x y)). Qed.
Lemma lem5202103 (x : real) (y : real) : ((term425 x y) = (term426 x y)) = ((term417 x y) = (term436 x y)).
Proof. exact (MK_COMB (@lem5202096 x y) (@lem5202102 x y)). Qed.
Lemma lem5202104 (x : real) (y : real) : (term417 x y) = (term436 x y).
Proof. exact (EQ_MP (@lem5202103 x y) (@lem5202088 x y)). Qed.
Lemma lem5202105 (x : real) : (term419 x) = (term437 x).
Proof. exact (fun_ext (fun y : real => @lem5202104 x y)). Qed.
Lemma lem5202106 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5202107 (x : real) : (term420 x) = (term438 x).
Proof. exact (MK_COMB (@lem5202106) (@lem5202105 x)). Qed.
Lemma lem5202108 (x : real) : (term399 x) = (term438 x).
Proof. exact (TRANS (@lem5202084 x) (@lem5202107 x)). Qed.
Lemma lem5202109 : term401 = term439.
Proof. exact (fun_ext (fun x : real => @lem5202108 x)). Qed.
Lemma lem5202110 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5202111 : term402 = term440.
Proof. exact (MK_COMB (@lem5202110) (@lem5202109)). Qed.
Lemma lem5202112 : term384 = term440.
Proof. exact (TRANS (@lem5202057) (@lem5202111)). Qed.
Lemma lem5202114 : term340 = term440.
Proof. exact (TRANS (@lem5202030) (@lem5202112)). Qed.
Lemma lem5202115 : term244 = term440.
Proof. exact (TRANS (@lem5201799) (@lem5202114)). Qed.
Lemma lem5202116 (h1 : term244) : term440.
Proof. exact (EQ_MP (@lem5202115) (@lem5201655 h1)). Qed.
Lemma lem5202121 (y : real) (x : real) : (term251 y x) = (term251 y x).
Proof. exact (eq_refl (term251 y x)). Qed.
Lemma lem5202122 (x : real) : (term252 x) = (term252 x).
Proof. exact (fun_ext (fun y : real => @lem5202121 y x)). Qed.
Lemma lem5202123 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202124 (x : real) : (term253 x) = (term253 x).
Proof. exact (MK_COMB (@lem5202123) (@lem5202122 x)). Qed.
Lemma lem5202125 : term254 = term254.
Proof. exact (fun_ext (fun x : real => @lem5202124 x)). Qed.
Lemma lem5202126 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202183 : term249 = term249.
Proof. exact (MK_COMB (@lem5202126) (@lem5202125)). Qed.
Lemma lem5202184 (h1 : term249) : term249.
Proof. exact (EQ_MP (@lem5202183) (@lem5201656 h1)). Qed.
Lemma lem5202185 (x : real) (h1 : term438 x) : term438 x.
Proof. exact (h1). Qed.
Lemma lem5202186 (x : real) (y : real) (h1 : term436 x y) : term436 x y.
Proof. exact (h1). Qed.
Lemma lem5202187 (x : real) (x' : real) (y : real) (h1 : term433 x x' y) : term433 x x' y.
Proof. exact (h1). Qed.
Lemma lem5202200 (y : real) (x : real) : (term251 y x) = (term251 y x).
Proof. exact (eq_refl (term251 y x)). Qed.
Lemma lem5202201 (x : real) : (term252 x) = (term252 x).
Proof. exact (fun_ext (fun y : real => @lem5202200 y x)). Qed.
Lemma lem5202202 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202203 (x : real) : (term253 x) = (term253 x).
Proof. exact (MK_COMB (@lem5202202) (@lem5202201 x)). Qed.
Lemma lem5202204 : term254 = term254.
Proof. exact (fun_ext (fun x : real => @lem5202203 x)). Qed.
Lemma lem5202205 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202206 : term249 = term249.
Proof. exact (MK_COMB (@lem5202205) (@lem5202204)). Qed.
Lemma lem5202207 (h1 : term249) : term249.
Proof. exact (EQ_MP (@lem5202206) (@lem5202184 h1)). Qed.
Lemma lem5202240 (x : real) (x' : real) (y : real) : (term316 x x' y) = (term316 x x' y).
Proof. exact (eq_refl (term316 x x' y)). Qed.
Lemma lem5202267 (x : real) (y : real) (x' : real) : (term287 x y x') = (term287 x y x').
Proof. exact (eq_refl (term287 x y x')). Qed.
Lemma lem5202268 (x : real) (y : real) : (term294 x y) = (term294 x y).
Proof. exact (fun_ext (fun x' : real => @lem5202267 x y x')). Qed.
Lemma lem5202269 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202270 (x : real) (y : real) : (term295 x y) = (term295 x y).
Proof. exact (MK_COMB (@lem5202269) (@lem5202268 x y)). Qed.
Lemma lem5202297 (y : real) (x : real) (x' : real) : (term261 y x x') = (term261 y x x').
Proof. exact (eq_refl (term261 y x x')). Qed.
Lemma lem5202298 (y : real) (x : real) : (term270 y x) = (term270 y x).
Proof. exact (fun_ext (fun x' : real => @lem5202297 y x x')). Qed.
Lemma lem5202299 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202300 (y : real) (x : real) : (term271 y x) = (term271 y x).
Proof. exact (MK_COMB (@lem5202299) (@lem5202298 y x)). Qed.
Lemma lem5202301 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5202302 (y : real) (x : real) : (term375 y x) = (term375 y x).
Proof. exact (MK_COMB (@lem5202301) (@lem5202300 y x)). Qed.
Lemma lem5202303 (x : real) (y : real) : (term377 x y) = (term377 x y).
Proof. exact (MK_COMB (@lem5202302 y x) (@lem5202270 x y)). Qed.
Lemma lem5202304 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5202305 (x : real) (y : real) : (term415 x y) = (term415 x y).
Proof. exact (MK_COMB (@lem5202304) (@lem5202303 x y)). Qed.
Lemma lem5202306 (x : real) (x' : real) (y : real) : (term433 x x' y) = (term433 x x' y).
Proof. exact (MK_COMB (@lem5202305 x y) (@lem5202240 x x' y)). Qed.
Lemma lem5202307 (x : real) (x' : real) (y : real) (h1 : term433 x x' y) : term433 x x' y.
Proof. exact (EQ_MP (@lem5202306 x x' y) (@lem5202187 x x' y h1)). Qed.
Lemma lem5202308 (x : real) (y : real) (h1 : term377 x y) : term377 x y.
Proof. exact (h1). Qed.
Lemma lem5202309 (x : real) (x' : real) (y : real) (h1 : term316 x x' y) : term316 x x' y.
Proof. exact (h1). Qed.
Lemma lem5202310 (y : real) (x : real) (h1 : term271 y x) : term271 y x.
Proof. exact (h1). Qed.
Lemma lem5202311 (x : real) (y : real) (h1 : term295 x y) : term295 x y.
Proof. exact (h1). Qed.
Lemma lem5202312 (x : real) (x' : real) (y : real) (h1 : term316 x x' y) : term314 x x' y.
Proof. exact (proj2 (@lem5202309 x x' y h1)). Qed.
Lemma lem5202313 (x : real) (x' : real) (y : real) (h1 : term316 x x' y) : term121 x x' y.
Proof. exact (proj1 (@lem5202309 x x' y h1)). Qed.
Lemma lem5202325 (y : real) (x : real) : (term251 y x) = (term251 y x).
Proof. exact (eq_refl (term251 y x)). Qed.
Lemma lem5202326 (x : real) : (term252 x) = (term252 x).
Proof. exact (fun_ext (fun y : real => @lem5202325 y x)). Qed.
Lemma lem5202327 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202328 (x : real) : (term253 x) = (term253 x).
Proof. exact (MK_COMB (@lem5202327) (@lem5202326 x)). Qed.
Lemma lem5202329 : term254 = term254.
Proof. exact (fun_ext (fun x : real => @lem5202328 x)). Qed.
Lemma lem5202330 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202332 : term249 = term249.
Proof. exact (MK_COMB (@lem5202330) (@lem5202329)). Qed.
Lemma lem5202333 (h1 : term249) : term249.
Proof. exact (EQ_MP (@lem5202332) (@lem5202207 h1)). Qed.
Lemma lem5202351 (y : real) (x : real) (x' : real) : (term261 y x x') = (term441 y x x').
Proof. exact (@lem19699 (term442 x' x) (term442 x' y) (term257 x x')). Qed.
Lemma lem5202352 (y : real) (x : real) : (term270 y x) = (term443 y x).
Proof. exact (fun_ext (fun x' : real => @lem5202351 y x x')). Qed.
Lemma lem5202353 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202355 (y : real) (x : real) : (term271 y x) = (term444 y x).
Proof. exact (MK_COMB (@lem5202353) (@lem5202352 y x)). Qed.
Lemma lem5202356 (y : real) (x : real) (h1 : term271 y x) : term444 y x.
Proof. exact (EQ_MP (@lem5202355 y x) (@lem5202310 y x h1)). Qed.
Lemma lem5202364 (y : real) (x : real) : (term251 y x) = (term251 y x).
Proof. exact (eq_refl (term251 y x)). Qed.
Lemma lem5202365 (x : real) : (term252 x) = (term252 x).
Proof. exact (fun_ext (fun y : real => @lem5202364 y x)). Qed.
Lemma lem5202366 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202367 (x : real) : (term253 x) = (term253 x).
Proof. exact (MK_COMB (@lem5202366) (@lem5202365 x)). Qed.
Lemma lem5202368 : term254 = term254.
Proof. exact (fun_ext (fun x : real => @lem5202367 x)). Qed.
Lemma lem5202369 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202371 : term249 = term249.
Proof. exact (MK_COMB (@lem5202369) (@lem5202368)). Qed.
Lemma lem5202372 (h1 : term249) : term249.
Proof. exact (EQ_MP (@lem5202371) (@lem5202207 h1)). Qed.
Lemma lem5202390 (x : real) (y : real) (x' : real) : (term287 x y x') = (term445 x y x').
Proof. exact (@lem19699 (term442 x' x) (term442 x' y) (term257 y x')). Qed.
Lemma lem5202391 (x : real) (y : real) : (term294 x y) = (term446 x y).
Proof. exact (fun_ext (fun x' : real => @lem5202390 x y x')). Qed.
Lemma lem5202392 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202394 (x : real) (y : real) : (term295 x y) = (term447 x y).
Proof. exact (MK_COMB (@lem5202392) (@lem5202391 x y)). Qed.
Lemma lem5202395 (x : real) (y : real) (h1 : term295 x y) : term447 x y.
Proof. exact (EQ_MP (@lem5202394 x y) (@lem5202311 x y h1)). Qed.
Lemma lem5202403 (y : real) (x : real) : (term251 y x) = (term251 y x).
Proof. exact (eq_refl (term251 y x)). Qed.
Lemma lem5202404 (x : real) : (term252 x) = (term252 x).
Proof. exact (fun_ext (fun y : real => @lem5202403 y x)). Qed.
Lemma lem5202405 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202406 (x : real) : (term253 x) = (term253 x).
Proof. exact (MK_COMB (@lem5202405) (@lem5202404 x)). Qed.
Lemma lem5202407 : term254 = term254.
Proof. exact (fun_ext (fun x : real => @lem5202406 x)). Qed.
Lemma lem5202408 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202410 : term249 = term249.
Proof. exact (MK_COMB (@lem5202408) (@lem5202407)). Qed.
Lemma lem5202411 (h1 : term249) : term249.
Proof. exact (EQ_MP (@lem5202410) (@lem5202207 h1)). Qed.
Lemma lem5202423 (x' : real) (x : real) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5202431 (y : real) (x : real) : (term251 y x) = (term251 y x).
Proof. exact (eq_refl (term251 y x)). Qed.
Lemma lem5202432 (x : real) : (term252 x) = (term252 x).
Proof. exact (fun_ext (fun y : real => @lem5202431 y x)). Qed.
Lemma lem5202433 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202434 (x : real) : (term253 x) = (term253 x).
Proof. exact (MK_COMB (@lem5202433) (@lem5202432 x)). Qed.
Lemma lem5202435 : term254 = term254.
Proof. exact (fun_ext (fun x : real => @lem5202434 x)). Qed.
Lemma lem5202436 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5202438 : term249 = term249.
Proof. exact (MK_COMB (@lem5202436) (@lem5202435)). Qed.
Lemma lem5202439 (h1 : term249) : term249.
Proof. exact (EQ_MP (@lem5202438) (@lem5202207 h1)). Qed.
Lemma lem5202451 (x' : real) (y : real) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem5202452 (_67870 : real) (h1 : term249) : term448 _67870.
Proof. exact (@lem5202333 h1 _67870). Qed.
Lemma lem5202453 (_67870 : real) : (term448 _67870) = (term253 _67870).
Proof. exact (eq_refl (term448 _67870)). Qed.
Lemma lem5202454 (_67870 : real) (h1 : term249) : term253 _67870.
Proof. exact (EQ_MP (@lem5202453 _67870) (@lem5202452 _67870 h1)). Qed.
Lemma lem5202455 (_67870 : real) (_67871 : real) (h1 : term249) : term449 _67870 _67871.
Proof. exact (@lem5202454 _67870 h1 _67871). Qed.
Lemma lem5202456 (_67871 : real) (_67870 : real) : (term449 _67870 _67871) = (term251 _67871 _67870).
Proof. exact (eq_refl (term449 _67870 _67871)). Qed.
Lemma lem5202458 (_67872 : real) (y : real) (x : real) (h1 : term271 y x) : term450 y x _67872.
Proof. exact (@lem5202356 y x h1 _67872). Qed.
Lemma lem5202459 (y : real) (x : real) (_67872 : real) : (term450 y x _67872) = (term441 y x _67872).
Proof. exact (eq_refl (term450 y x _67872)). Qed.
Lemma lem5202460 (_67872 : real) (y : real) (x : real) (h1 : term271 y x) : term441 y x _67872.
Proof. exact (EQ_MP (@lem5202459 y x _67872) (@lem5202458 _67872 y x h1)). Qed.
Lemma lem5202461 (_67873 : real) (h1 : term249) : term448 _67873.
Proof. exact (@lem5202372 h1 _67873). Qed.
Lemma lem5202462 (_67873 : real) : (term448 _67873) = (term253 _67873).
Proof. exact (eq_refl (term448 _67873)). Qed.
Lemma lem5202463 (_67873 : real) (h1 : term249) : term253 _67873.
Proof. exact (EQ_MP (@lem5202462 _67873) (@lem5202461 _67873 h1)). Qed.
Lemma lem5202464 (_67873 : real) (_67874 : real) (h1 : term249) : term449 _67873 _67874.
Proof. exact (@lem5202463 _67873 h1 _67874). Qed.
Lemma lem5202465 (_67874 : real) (_67873 : real) : (term449 _67873 _67874) = (term251 _67874 _67873).
Proof. exact (eq_refl (term449 _67873 _67874)). Qed.
Lemma lem5202467 (_67875 : real) (x : real) (y : real) (h1 : term295 x y) : term451 x y _67875.
Proof. exact (@lem5202395 x y h1 _67875). Qed.
Lemma lem5202468 (x : real) (y : real) (_67875 : real) : (term451 x y _67875) = (term445 x y _67875).
Proof. exact (eq_refl (term451 x y _67875)). Qed.
Lemma lem5202469 (_67875 : real) (x : real) (y : real) (h1 : term295 x y) : term445 x y _67875.
Proof. exact (EQ_MP (@lem5202468 x y _67875) (@lem5202467 _67875 x y h1)). Qed.
Lemma lem5202470 (_67876 : real) (h1 : term249) : term448 _67876.
Proof. exact (@lem5202411 h1 _67876). Qed.
Lemma lem5202471 (_67876 : real) : (term448 _67876) = (term253 _67876).
Proof. exact (eq_refl (term448 _67876)). Qed.
Lemma lem5202472 (_67876 : real) (h1 : term249) : term253 _67876.
Proof. exact (EQ_MP (@lem5202471 _67876) (@lem5202470 _67876 h1)). Qed.
Lemma lem5202473 (_67876 : real) (_67877 : real) (h1 : term249) : term449 _67876 _67877.
Proof. exact (@lem5202472 _67876 h1 _67877). Qed.
Lemma lem5202474 (_67877 : real) (_67876 : real) : (term449 _67876 _67877) = (term251 _67877 _67876).
Proof. exact (eq_refl (term449 _67876 _67877)). Qed.
Lemma lem5202476 (_67878 : real) (h1 : term249) : term448 _67878.
Proof. exact (@lem5202439 h1 _67878). Qed.
Lemma lem5202477 (_67878 : real) : (term448 _67878) = (term253 _67878).
Proof. exact (eq_refl (term448 _67878)). Qed.
Lemma lem5202478 (_67878 : real) (h1 : term249) : term253 _67878.
Proof. exact (EQ_MP (@lem5202477 _67878) (@lem5202476 _67878 h1)). Qed.
Lemma lem5202479 (_67878 : real) (_67879 : real) (h1 : term249) : term449 _67878 _67879.
Proof. exact (@lem5202478 _67878 h1 _67879). Qed.
Lemma lem5202480 (_67879 : real) (_67878 : real) : (term449 _67878 _67879) = (term251 _67879 _67878).
Proof. exact (eq_refl (term449 _67878 _67879)). Qed.
Lemma lem5202491 (_67871 : real) (_67870 : real) (h1 : term249) : term251 _67871 _67870.
Proof. exact (EQ_MP (@lem5202456 _67871 _67870) (@lem5202455 _67870 _67871 h1)). Qed.
Lemma lem5202497 (_67872 : real) (y : real) (x : real) (h1 : term271 y x) : term452 x _67872.
Proof. exact (proj1 (@lem5202460 _67872 y x h1)). Qed.
Lemma lem5202509 (_67874 : real) (_67873 : real) (h1 : term249) : term251 _67874 _67873.
Proof. exact (EQ_MP (@lem5202465 _67874 _67873) (@lem5202464 _67873 _67874 h1)). Qed.
Lemma lem5202521 (_67875 : real) (x : real) (y : real) (h1 : term295 x y) : term452 y _67875.
Proof. exact (proj2 (@lem5202469 _67875 x y h1)). Qed.
Lemma lem5202529 (x : real) (x' : real) (y : real) (h1 : term316 x x' y) : term257 x' x.
Proof. exact (proj1 (@lem5202312 x x' y h1)). Qed.
Lemma lem5202533 (x' : real) (x : real) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem5202543 (x : real) (x' : real) (y : real) (h1 : term316 x x' y) : term257 x' y.
Proof. exact (proj2 (@lem5202312 x x' y h1)). Qed.
Lemma lem5202545 (x' : real) (y : real) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem5202573 (_67877 : real) (_67876 : real) (h1 : term249) : term251 _67877 _67876.
Proof. exact (EQ_MP (@lem5202474 _67877 _67876) (@lem5202473 _67876 _67877 h1)). Qed.
Lemma lem5202574 (x : real) : (term453 x) = (term453 x).
Proof. exact (eq_refl (term453 x)). Qed.
Lemma lem5202575 (x' : real) (x : real) (h1 : x' = x) : (term454 x x') = (term455 x).
Proof. exact (MK_COMB (@lem5202574 x) (@lem5202533 x' x h1)). Qed.
Lemma lem5202576 (x : real) : (term455 x) = (term456 x).
Proof. exact (eq_refl (term455 x)). Qed.
Lemma lem5202577 (x : real) (x' : real) : (term457 x x') = (term457 x x').
Proof. exact (eq_refl (term457 x x')). Qed.
Lemma lem5202578 (x' : real) (x : real) : ((term454 x x') = (term455 x)) = ((term454 x x') = (term456 x)).
Proof. exact (MK_COMB (@lem5202577 x x') (@lem5202576 x)). Qed.
Lemma lem5202579 (x' : real) (x : real) : (term454 x x') = (term257 x' x).
Proof. exact (eq_refl (term454 x x')). Qed.
Lemma lem5202580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5202581 (x' : real) (x : real) : (term457 x x') = (term458 x' x).
Proof. exact (MK_COMB (@lem5202580) (@lem5202579 x' x)). Qed.
Lemma lem5202582 (x : real) : (term456 x) = (term456 x).
Proof. exact (eq_refl (term456 x)). Qed.
Lemma lem5202583 (x' : real) (x : real) : ((term454 x x') = (term456 x)) = ((term257 x' x) = (term456 x)).
Proof. exact (MK_COMB (@lem5202581 x' x) (@lem5202582 x)). Qed.
Lemma lem5202584 (x' : real) (x : real) : ((term454 x x') = (term455 x)) = ((term257 x' x) = (term456 x)).
Proof. exact (TRANS (@lem5202578 x' x) (@lem5202583 x' x)). Qed.
Lemma lem5202585 (x' : real) (x : real) (h1 : x' = x) : (term257 x' x) = (term456 x).
Proof. exact (EQ_MP (@lem5202584 x' x) (@lem5202575 x' x h1)). Qed.
Lemma lem5202586 (y : real) (x' : real) (x : real) (h1 : term316 x x' y) (h2 : x' = x) : term456 x.
Proof. exact (EQ_MP (@lem5202585 x' x h2) (@lem5202529 x x' y h1)). Qed.
Lemma lem5202627 (_67879 : real) (_67878 : real) (h1 : term249) : term251 _67879 _67878.
Proof. exact (EQ_MP (@lem5202480 _67879 _67878) (@lem5202479 _67878 _67879 h1)). Qed.
Lemma lem5202641 (y : real) : (term453 y) = (term453 y).
Proof. exact (eq_refl (term453 y)). Qed.
Lemma lem5202642 (x' : real) (y : real) (h1 : x' = y) : (term454 y x') = (term455 y).
Proof. exact (MK_COMB (@lem5202641 y) (@lem5202545 x' y h1)). Qed.
Lemma lem5202643 (y : real) : (term455 y) = (term456 y).
Proof. exact (eq_refl (term455 y)). Qed.
Lemma lem5202644 (y : real) (x' : real) : (term457 y x') = (term457 y x').
Proof. exact (eq_refl (term457 y x')). Qed.
Lemma lem5202645 (x' : real) (y : real) : ((term454 y x') = (term455 y)) = ((term454 y x') = (term456 y)).
Proof. exact (MK_COMB (@lem5202644 y x') (@lem5202643 y)). Qed.
Lemma lem5202646 (x' : real) (y : real) : (term454 y x') = (term257 x' y).
Proof. exact (eq_refl (term454 y x')). Qed.
Lemma lem5202647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5202648 (x' : real) (y : real) : (term457 y x') = (term458 x' y).
Proof. exact (MK_COMB (@lem5202647) (@lem5202646 x' y)). Qed.
Lemma lem5202649 (y : real) : (term456 y) = (term456 y).
Proof. exact (eq_refl (term456 y)). Qed.
Lemma lem5202650 (x' : real) (y : real) : ((term454 y x') = (term456 y)) = ((term257 x' y) = (term456 y)).
Proof. exact (MK_COMB (@lem5202648 x' y) (@lem5202649 y)). Qed.
Lemma lem5202651 (x' : real) (y : real) : ((term454 y x') = (term455 y)) = ((term257 x' y) = (term456 y)).
Proof. exact (TRANS (@lem5202645 x' y) (@lem5202650 x' y)). Qed.
Lemma lem5202652 (x' : real) (y : real) (h1 : x' = y) : (term257 x' y) = (term456 y).
Proof. exact (EQ_MP (@lem5202651 x' y) (@lem5202642 x' y h1)). Qed.
Lemma lem5202653 (x : real) (x' : real) (y : real) (h1 : term316 x x' y) (h2 : x' = y) : term456 y.
Proof. exact (EQ_MP (@lem5202652 x' y h2) (@lem5202543 x x' y h1)). Qed.
Lemma lem5202676 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5202677 (x : real) : term459 x.
Proof. exact (fun h0 : term460 x => @lem5202676 x). Qed.
Lemma lem5202679 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5202680 (x : real) : (term459 x) = (x = x).
Proof. exact (@lem5202679 (x = x)). Qed.
Lemma lem5202681 (x : real) : x = x.
Proof. exact (EQ_MP (@lem5202680 x) (@lem5202677 x)). Qed.
Lemma lem5202684 (x : real) (h1 : term456 x) : term456 x.
Proof. exact (h1). Qed.
Lemma lem5202685 (x : real) (h1 : term456 x) : term462 x.
Proof. exact (fun h0 : real_le x x => @lem5202684 x h1). Qed.
Lemma lem5202687 (p : Prop) : (term463 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5202688 (x : real) : (term462 x) = (term456 x).
Proof. exact (@lem5202687 (real_le x x)). Qed.
Lemma lem5202689 (x : real) (h1 : term456 x) : term456 x.
Proof. exact (EQ_MP (@lem5202688 x) (@lem5202685 x h1)). Qed.
Lemma lem5202700 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5202701 (_67871 : real) (_67870 : real) : (term251 _67870 _67871) = (term251 _67871 _67870).
Proof. exact (@lem5202700 (real_le _67870 _67871) (real_le _67871 _67870)). Qed.
Lemma lem5202707 (_67871 : real) (_67870 : real) : (term464 _67871 _67870) = (term464 _67871 _67870).
Proof. exact (eq_refl (term464 _67871 _67870)). Qed.
Lemma lem5202708 (_67871 : real) (_67870 : real) : ((term251 _67871 _67870) = (term251 _67870 _67871)) = ((term251 _67871 _67870) = (term251 _67871 _67870)).
Proof. exact (MK_COMB (@lem5202707 _67871 _67870) (@lem5202701 _67871 _67870)). Qed.
Lemma lem5202710 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5202711 (x : Prop) : (x = x) = True.
Proof. exact (@lem5202710 Prop x). Qed.
Lemma lem5202712 (_67871 : real) (_67870 : real) : ((term251 _67871 _67870) = (term251 _67871 _67870)) = True.
Proof. exact (@lem5202711 (term251 _67871 _67870)). Qed.
Lemma lem5202713 (_67870 : real) (_67871 : real) : ((term251 _67871 _67870) = (term251 _67870 _67871)) = True.
Proof. exact (TRANS (@lem5202708 _67871 _67870) (@lem5202712 _67871 _67870)). Qed.
Lemma lem5202714 (_67870 : real) (_67871 : real) : True = ((term251 _67871 _67870) = (term251 _67870 _67871)).
Proof. exact (SYM (@lem5202713 _67870 _67871)). Qed.
Lemma lem5202715 (_67870 : real) (_67871 : real) : (term251 _67871 _67870) = (term251 _67870 _67871).
Proof. exact (EQ_MP (@lem5202714 _67870 _67871) (@lem0)). Qed.
Lemma lem5202716 (_67870 : real) (_67871 : real) (h1 : term249) : term251 _67870 _67871.
Proof. exact (EQ_MP (@lem5202715 _67870 _67871) (@lem5202491 _67871 _67870 h1)). Qed.
Lemma lem5202718 (b : Prop) (a : Prop) : (a \/ b) = (term465 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5202721 (_67871 : real) (_67870 : real) : (term251 _67870 _67871) = (term466 _67871 _67870).
Proof. exact (@lem5202718 (real_le _67870 _67871) (real_le _67871 _67870)). Qed.
Lemma lem5202724 (_67871 : real) (_67870 : real) (h1 : term249) : term466 _67871 _67870.
Proof. exact (EQ_MP (@lem5202721 _67871 _67870) (@lem5202716 _67870 _67871 h1)). Qed.
Lemma lem5202725 (x : real) (h1 : term249) : term467 x.
Proof. exact (@lem5202724 x x h1). Qed.
Lemma lem5202728 (x : real) (h1 : term249) (h2 : term456 x) : real_le x x.
Proof. exact (@lem5202725 x h1 (@lem5202689 x h2)). Qed.
Lemma lem5202729 (x : real) (h1 : term249) : term467 x.
Proof. exact (fun h0 : term456 x => @lem5202728 x h1 h0). Qed.
Lemma lem5202731 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5202732 (x : real) : (term467 x) = (real_le x x).
Proof. exact (@lem5202731 (real_le x x)). Qed.
Lemma lem5202733 (x : real) (h1 : term249) : real_le x x.
Proof. exact (EQ_MP (@lem5202732 x) (@lem5202729 x h1)). Qed.
Lemma lem5202735 (a : Prop) (b : Prop) : (term468 a b) = (term469 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5202736 (x : real) (_67872 : real) : (term452 x _67872) = (term470 x _67872).
Proof. exact (@lem5202735 (_67872 = x) (real_le x _67872)). Qed.
Lemma lem5202738 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5202739 (x : real) (_67872 : real) : (term470 x _67872) = (term471 x _67872).
Proof. exact (@lem5202738 (term472 x _67872)). Qed.
Lemma lem5202740 (x : real) (_67872 : real) : (term452 x _67872) = (term471 x _67872).
Proof. exact (TRANS (@lem5202736 x _67872) (@lem5202739 x _67872)). Qed.
Lemma lem5202742 (x : real) (h1 : term249) : term473 x.
Proof. exact (conj (@lem5202681 x) (@lem5202733 x h1)). Qed.
Lemma lem5202744 (_67872 : real) (y : real) (x : real) (h1 : term271 y x) : term471 x _67872.
Proof. exact (EQ_MP (@lem5202740 x _67872) (@lem5202497 _67872 y x h1)). Qed.
Lemma lem5202745 (y : real) (x : real) (h1 : term271 y x) : term474 x.
Proof. exact (@lem5202744 x y x h1). Qed.
Lemma lem5202748 (y : real) (x : real) (h1 : term249) (h2 : term271 y x) : False.
Proof. exact (@lem5202745 y x h2 (@lem5202742 x h1)). Qed.
Lemma lem5202749 (y : real) (x : real) (h1 : term249) (h2 : term271 y x) : term475.
Proof. exact (fun h0 : ~ False => @lem5202748 y x h1 h2). Qed.
Lemma lem5202751 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5202752 : term475 = False.
Proof. exact (@lem5202751 False). Qed.
Lemma lem5202753 (y : real) (x : real) (h1 : term249) (h2 : term271 y x) : False.
Proof. exact (EQ_MP (@lem5202752) (@lem5202749 y x h1 h2)). Qed.
Lemma lem5202776 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5202777 (y : real) : y = y.
Proof. exact (@lem5202776 y). Qed.
Lemma lem5202778 (y : real) : term459 y.
Proof. exact (fun h0 : term460 y => @lem5202777 y). Qed.
Lemma lem5202780 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5202781 (y : real) : (term459 y) = (y = y).
Proof. exact (@lem5202780 (y = y)). Qed.
Lemma lem5202782 (y : real) : y = y.
Proof. exact (EQ_MP (@lem5202781 y) (@lem5202778 y)). Qed.
Lemma lem5202785 (y : real) (h1 : term456 y) : term456 y.
Proof. exact (h1). Qed.
Lemma lem5202786 (y : real) (h1 : term456 y) : term462 y.
Proof. exact (fun h0 : real_le y y => @lem5202785 y h1). Qed.
Lemma lem5202788 (p : Prop) : (term463 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5202789 (y : real) : (term462 y) = (term456 y).
Proof. exact (@lem5202788 (real_le y y)). Qed.
Lemma lem5202790 (y : real) (h1 : term456 y) : term456 y.
Proof. exact (EQ_MP (@lem5202789 y) (@lem5202786 y h1)). Qed.
Lemma lem5202801 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5202802 (_67874 : real) (_67873 : real) : (term251 _67873 _67874) = (term251 _67874 _67873).
Proof. exact (@lem5202801 (real_le _67873 _67874) (real_le _67874 _67873)). Qed.
Lemma lem5202808 (_67874 : real) (_67873 : real) : (term464 _67874 _67873) = (term464 _67874 _67873).
Proof. exact (eq_refl (term464 _67874 _67873)). Qed.
Lemma lem5202809 (_67874 : real) (_67873 : real) : ((term251 _67874 _67873) = (term251 _67873 _67874)) = ((term251 _67874 _67873) = (term251 _67874 _67873)).
Proof. exact (MK_COMB (@lem5202808 _67874 _67873) (@lem5202802 _67874 _67873)). Qed.
Lemma lem5202811 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5202812 (x : Prop) : (x = x) = True.
Proof. exact (@lem5202811 Prop x). Qed.
Lemma lem5202813 (_67874 : real) (_67873 : real) : ((term251 _67874 _67873) = (term251 _67874 _67873)) = True.
Proof. exact (@lem5202812 (term251 _67874 _67873)). Qed.
Lemma lem5202814 (_67873 : real) (_67874 : real) : ((term251 _67874 _67873) = (term251 _67873 _67874)) = True.
Proof. exact (TRANS (@lem5202809 _67874 _67873) (@lem5202813 _67874 _67873)). Qed.
Lemma lem5202815 (_67873 : real) (_67874 : real) : True = ((term251 _67874 _67873) = (term251 _67873 _67874)).
Proof. exact (SYM (@lem5202814 _67873 _67874)). Qed.
Lemma lem5202816 (_67873 : real) (_67874 : real) : (term251 _67874 _67873) = (term251 _67873 _67874).
Proof. exact (EQ_MP (@lem5202815 _67873 _67874) (@lem0)). Qed.
Lemma lem5202817 (_67873 : real) (_67874 : real) (h1 : term249) : term251 _67873 _67874.
Proof. exact (EQ_MP (@lem5202816 _67873 _67874) (@lem5202509 _67874 _67873 h1)). Qed.
Lemma lem5202819 (b : Prop) (a : Prop) : (a \/ b) = (term465 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5202822 (_67874 : real) (_67873 : real) : (term251 _67873 _67874) = (term466 _67874 _67873).
Proof. exact (@lem5202819 (real_le _67873 _67874) (real_le _67874 _67873)). Qed.
Lemma lem5202825 (_67874 : real) (_67873 : real) (h1 : term249) : term466 _67874 _67873.
Proof. exact (EQ_MP (@lem5202822 _67874 _67873) (@lem5202817 _67873 _67874 h1)). Qed.
Lemma lem5202826 (y : real) (h1 : term249) : term467 y.
Proof. exact (@lem5202825 y y h1). Qed.
Lemma lem5202829 (y : real) (h1 : term249) (h2 : term456 y) : real_le y y.
Proof. exact (@lem5202826 y h1 (@lem5202790 y h2)). Qed.
Lemma lem5202830 (y : real) (h1 : term249) : term467 y.
Proof. exact (fun h0 : term456 y => @lem5202829 y h1 h0). Qed.
Lemma lem5202832 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5202833 (y : real) : (term467 y) = (real_le y y).
Proof. exact (@lem5202832 (real_le y y)). Qed.
Lemma lem5202834 (y : real) (h1 : term249) : real_le y y.
Proof. exact (EQ_MP (@lem5202833 y) (@lem5202830 y h1)). Qed.
Lemma lem5202836 (a : Prop) (b : Prop) : (term468 a b) = (term469 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5202837 (y : real) (_67875 : real) : (term452 y _67875) = (term470 y _67875).
Proof. exact (@lem5202836 (_67875 = y) (real_le y _67875)). Qed.
Lemma lem5202839 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5202840 (y : real) (_67875 : real) : (term470 y _67875) = (term471 y _67875).
Proof. exact (@lem5202839 (term472 y _67875)). Qed.
Lemma lem5202841 (y : real) (_67875 : real) : (term452 y _67875) = (term471 y _67875).
Proof. exact (TRANS (@lem5202837 y _67875) (@lem5202840 y _67875)). Qed.
Lemma lem5202843 (y : real) (h1 : term249) : term473 y.
Proof. exact (conj (@lem5202782 y) (@lem5202834 y h1)). Qed.
Lemma lem5202845 (_67875 : real) (x : real) (y : real) (h1 : term295 x y) : term471 y _67875.
Proof. exact (EQ_MP (@lem5202841 y _67875) (@lem5202521 _67875 x y h1)). Qed.
Lemma lem5202846 (x : real) (y : real) (h1 : term295 x y) : term474 y.
Proof. exact (@lem5202845 y x y h1). Qed.
Lemma lem5202849 (x : real) (y : real) (h1 : term249) (h2 : term295 x y) : False.
Proof. exact (@lem5202846 x y h2 (@lem5202843 y h1)). Qed.
Lemma lem5202850 (x : real) (y : real) (h1 : term249) (h2 : term295 x y) : term475.
Proof. exact (fun h0 : ~ False => @lem5202849 x y h1 h2). Qed.
Lemma lem5202852 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5202853 : term475 = False.
Proof. exact (@lem5202852 False). Qed.
Lemma lem5202854 (x : real) (y : real) (h1 : term249) (h2 : term295 x y) : False.
Proof. exact (EQ_MP (@lem5202853) (@lem5202850 x y h1 h2)). Qed.
Lemma lem5202857 (x : real) (h1 : term456 x) : term456 x.
Proof. exact (h1). Qed.
Lemma lem5202858 (x : real) (h1 : term456 x) : term462 x.
Proof. exact (fun h0 : real_le x x => @lem5202857 x h1). Qed.
Lemma lem5202860 (p : Prop) : (term463 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5202861 (x : real) : (term462 x) = (term456 x).
Proof. exact (@lem5202860 (real_le x x)). Qed.
Lemma lem5202862 (x : real) (h1 : term456 x) : term456 x.
Proof. exact (EQ_MP (@lem5202861 x) (@lem5202858 x h1)). Qed.
Lemma lem5202873 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5202874 (_67877 : real) (_67876 : real) : (term251 _67876 _67877) = (term251 _67877 _67876).
Proof. exact (@lem5202873 (real_le _67876 _67877) (real_le _67877 _67876)). Qed.
Lemma lem5202880 (_67877 : real) (_67876 : real) : (term464 _67877 _67876) = (term464 _67877 _67876).
Proof. exact (eq_refl (term464 _67877 _67876)). Qed.
Lemma lem5202881 (_67877 : real) (_67876 : real) : ((term251 _67877 _67876) = (term251 _67876 _67877)) = ((term251 _67877 _67876) = (term251 _67877 _67876)).
Proof. exact (MK_COMB (@lem5202880 _67877 _67876) (@lem5202874 _67877 _67876)). Qed.
Lemma lem5202883 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5202884 (x : Prop) : (x = x) = True.
Proof. exact (@lem5202883 Prop x). Qed.
Lemma lem5202885 (_67877 : real) (_67876 : real) : ((term251 _67877 _67876) = (term251 _67877 _67876)) = True.
Proof. exact (@lem5202884 (term251 _67877 _67876)). Qed.
Lemma lem5202886 (_67876 : real) (_67877 : real) : ((term251 _67877 _67876) = (term251 _67876 _67877)) = True.
Proof. exact (TRANS (@lem5202881 _67877 _67876) (@lem5202885 _67877 _67876)). Qed.
Lemma lem5202887 (_67876 : real) (_67877 : real) : True = ((term251 _67877 _67876) = (term251 _67876 _67877)).
Proof. exact (SYM (@lem5202886 _67876 _67877)). Qed.
Lemma lem5202888 (_67876 : real) (_67877 : real) : (term251 _67877 _67876) = (term251 _67876 _67877).
Proof. exact (EQ_MP (@lem5202887 _67876 _67877) (@lem0)). Qed.
Lemma lem5202889 (_67876 : real) (_67877 : real) (h1 : term249) : term251 _67876 _67877.
Proof. exact (EQ_MP (@lem5202888 _67876 _67877) (@lem5202573 _67877 _67876 h1)). Qed.
Lemma lem5202891 (b : Prop) (a : Prop) : (a \/ b) = (term465 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5202894 (_67877 : real) (_67876 : real) : (term251 _67876 _67877) = (term466 _67877 _67876).
Proof. exact (@lem5202891 (real_le _67876 _67877) (real_le _67877 _67876)). Qed.
Lemma lem5202897 (_67877 : real) (_67876 : real) (h1 : term249) : term466 _67877 _67876.
Proof. exact (EQ_MP (@lem5202894 _67877 _67876) (@lem5202889 _67876 _67877 h1)). Qed.
Lemma lem5202898 (x : real) (h1 : term249) : term467 x.
Proof. exact (@lem5202897 x x h1). Qed.
Lemma lem5202901 (x : real) (h1 : term249) (h2 : term456 x) : real_le x x.
Proof. exact (@lem5202898 x h1 (@lem5202862 x h2)). Qed.
Lemma lem5202902 (x : real) (h1 : term249) : term467 x.
Proof. exact (fun h0 : term456 x => @lem5202901 x h1 h0). Qed.
Lemma lem5202904 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5202905 (x : real) : (term467 x) = (real_le x x).
Proof. exact (@lem5202904 (real_le x x)). Qed.
Lemma lem5202906 (x : real) (h1 : term249) : real_le x x.
Proof. exact (EQ_MP (@lem5202905 x) (@lem5202902 x h1)). Qed.
Lemma lem5202909 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5202911 (x : real) : (term456 x) = (term476 x).
Proof. exact (@lem5202909 (real_le x x)). Qed.
Lemma lem5202914 (y : real) (x' : real) (x : real) (h1 : term316 x x' y) (h2 : x' = x) : term476 x.
Proof. exact (EQ_MP (@lem5202911 x) (@lem5202586 y x' x h1 h2)). Qed.
Lemma lem5202917 (y : real) (x' : real) (x : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = x) : False.
Proof. exact (@lem5202914 y x' x h2 h3 (@lem5202906 x h1)). Qed.
Lemma lem5202918 (y : real) (x' : real) (x : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = x) : term475.
Proof. exact (fun h0 : ~ False => @lem5202917 y x' x h1 h2 h3). Qed.
Lemma lem5202920 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5202921 : term475 = False.
Proof. exact (@lem5202920 False). Qed.
Lemma lem5202925 (y : real) (h1 : term456 y) : term456 y.
Proof. exact (h1). Qed.
Lemma lem5202926 (y : real) (h1 : term456 y) : term462 y.
Proof. exact (fun h0 : real_le y y => @lem5202925 y h1). Qed.
Lemma lem5202928 (p : Prop) : (term463 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5202929 (y : real) : (term462 y) = (term456 y).
Proof. exact (@lem5202928 (real_le y y)). Qed.
Lemma lem5202930 (y : real) (h1 : term456 y) : term456 y.
Proof. exact (EQ_MP (@lem5202929 y) (@lem5202926 y h1)). Qed.
Lemma lem5202941 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5202942 (_67879 : real) (_67878 : real) : (term251 _67878 _67879) = (term251 _67879 _67878).
Proof. exact (@lem5202941 (real_le _67878 _67879) (real_le _67879 _67878)). Qed.
Lemma lem5202948 (_67879 : real) (_67878 : real) : (term464 _67879 _67878) = (term464 _67879 _67878).
Proof. exact (eq_refl (term464 _67879 _67878)). Qed.
Lemma lem5202949 (_67879 : real) (_67878 : real) : ((term251 _67879 _67878) = (term251 _67878 _67879)) = ((term251 _67879 _67878) = (term251 _67879 _67878)).
Proof. exact (MK_COMB (@lem5202948 _67879 _67878) (@lem5202942 _67879 _67878)). Qed.
Lemma lem5202951 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5202952 (x : Prop) : (x = x) = True.
Proof. exact (@lem5202951 Prop x). Qed.
Lemma lem5202953 (_67879 : real) (_67878 : real) : ((term251 _67879 _67878) = (term251 _67879 _67878)) = True.
Proof. exact (@lem5202952 (term251 _67879 _67878)). Qed.
Lemma lem5202954 (_67878 : real) (_67879 : real) : ((term251 _67879 _67878) = (term251 _67878 _67879)) = True.
Proof. exact (TRANS (@lem5202949 _67879 _67878) (@lem5202953 _67879 _67878)). Qed.
Lemma lem5202955 (_67878 : real) (_67879 : real) : True = ((term251 _67879 _67878) = (term251 _67878 _67879)).
Proof. exact (SYM (@lem5202954 _67878 _67879)). Qed.
Lemma lem5202956 (_67878 : real) (_67879 : real) : (term251 _67879 _67878) = (term251 _67878 _67879).
Proof. exact (EQ_MP (@lem5202955 _67878 _67879) (@lem0)). Qed.
Lemma lem5202957 (_67878 : real) (_67879 : real) (h1 : term249) : term251 _67878 _67879.
Proof. exact (EQ_MP (@lem5202956 _67878 _67879) (@lem5202627 _67879 _67878 h1)). Qed.
Lemma lem5202959 (b : Prop) (a : Prop) : (a \/ b) = (term465 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5202962 (_67879 : real) (_67878 : real) : (term251 _67878 _67879) = (term466 _67879 _67878).
Proof. exact (@lem5202959 (real_le _67878 _67879) (real_le _67879 _67878)). Qed.
Lemma lem5202965 (_67879 : real) (_67878 : real) (h1 : term249) : term466 _67879 _67878.
Proof. exact (EQ_MP (@lem5202962 _67879 _67878) (@lem5202957 _67878 _67879 h1)). Qed.
Lemma lem5202966 (y : real) (h1 : term249) : term467 y.
Proof. exact (@lem5202965 y y h1). Qed.
Lemma lem5202969 (y : real) (h1 : term249) (h2 : term456 y) : real_le y y.
Proof. exact (@lem5202966 y h1 (@lem5202930 y h2)). Qed.
Lemma lem5202970 (y : real) (h1 : term249) : term467 y.
Proof. exact (fun h0 : term456 y => @lem5202969 y h1 h0). Qed.
Lemma lem5202972 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5202973 (y : real) : (term467 y) = (real_le y y).
Proof. exact (@lem5202972 (real_le y y)). Qed.
Lemma lem5202974 (y : real) (h1 : term249) : real_le y y.
Proof. exact (EQ_MP (@lem5202973 y) (@lem5202970 y h1)). Qed.
Lemma lem5202977 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5202979 (y : real) : (term456 y) = (term476 y).
Proof. exact (@lem5202977 (real_le y y)). Qed.
Lemma lem5202982 (x : real) (x' : real) (y : real) (h1 : term316 x x' y) (h2 : x' = y) : term476 y.
Proof. exact (EQ_MP (@lem5202979 y) (@lem5202653 x x' y h1 h2)). Qed.
Lemma lem5202985 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = y) : False.
Proof. exact (@lem5202982 x x' y h2 h3 (@lem5202974 y h1)). Qed.
Lemma lem5202986 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = y) : term475.
Proof. exact (fun h0 : ~ False => @lem5202985 x x' y h1 h2 h3). Qed.
Lemma lem5202988 (p : Prop) : (term461 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5202989 : term475 = False.
Proof. exact (@lem5202988 False). Qed.
Lemma lem5202991 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem5202989) (@lem5202986 x x' y h1 h2 h3)). Qed.
Lemma lem5202992 (y : real) (x' : real) (x : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5202921) (@lem5202918 y x' x h1 h2 h3)). Qed.
Lemma lem5202993 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem5202991 x x' y h1 h2 h3) (fun h4 : False => @lem5202545 x' y h3)). Qed.
Lemma lem5202994 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem5202993 x x' y h1 h2 h3) (@lem5202545 x' y h3)). Qed.
Lemma lem5202995 (y : real) (x' : real) (x : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5202992 y x' x h1 h2 h3) (fun h4 : False => @lem5202533 x' x h3)). Qed.
Lemma lem5202996 (y : real) (x' : real) (x : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5202995 y x' x h1 h2 h3) (@lem5202533 x' x h3)). Qed.
Lemma lem5202997 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem5202994 x x' y h1 h2 h3) (fun h4 : False => @lem5202451 x' y h3)). Qed.
Lemma lem5202998 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem5202997 x x' y h1 h2 h3) (@lem5202451 x' y h3)). Qed.
Lemma lem5202999 (y : real) (x' : real) (x : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5202996 y x' x h1 h2 h3) (fun h4 : False => @lem5202423 x' x h3)). Qed.
Lemma lem5203000 (y : real) (x' : real) (x : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5202999 y x' x h1 h2 h3) (@lem5202423 x' x h3)). Qed.
Lemma lem5203001 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem5202998 x x' y h1 h2 h3) (fun h4 : False => @lem5202451 x' y h3)). Qed.
Lemma lem5203002 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem5203001 x x' y h1 h2 h3) (@lem5202451 x' y h3)). Qed.
Lemma lem5203003 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = y) : term249 = False.
Proof. exact (prop_ext (fun h4 : term249 => @lem5203002 x x' y h1 h2 h3) (fun h4 : False => @lem5202439 h1)). Qed.
Lemma lem5203004 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = y) : False.
Proof. exact (EQ_MP (@lem5203003 x x' y h1 h2 h3) (@lem5202439 h1)). Qed.
Lemma lem5203005 (y : real) (x' : real) (x : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem5203000 y x' x h1 h2 h3) (fun h4 : False => @lem5202423 x' x h3)). Qed.
Lemma lem5203006 (y : real) (x' : real) (x : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5203005 y x' x h1 h2 h3) (@lem5202423 x' x h3)). Qed.
Lemma lem5203007 (y : real) (x' : real) (x : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = x) : term249 = False.
Proof. exact (prop_ext (fun h4 : term249 => @lem5203006 y x' x h1 h2 h3) (fun h4 : False => @lem5202411 h1)). Qed.
Lemma lem5203008 (y : real) (x' : real) (x : real) (h1 : term249) (h2 : term316 x x' y) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem5203007 y x' x h1 h2 h3) (@lem5202411 h1)). Qed.
Lemma lem5203009 (x : real) (y : real) (h1 : term249) (h2 : term295 x y) : term249 = False.
Proof. exact (prop_ext (fun h3 : term249 => @lem5202854 x y h1 h2) (fun h3 : False => @lem5202372 h1)). Qed.
Lemma lem5203010 (x : real) (y : real) (h1 : term249) (h2 : term295 x y) : False.
Proof. exact (EQ_MP (@lem5203009 x y h1 h2) (@lem5202372 h1)). Qed.
Lemma lem5203011 (y : real) (x : real) (h1 : term249) (h2 : term271 y x) : term249 = False.
Proof. exact (prop_ext (fun h3 : term249 => @lem5202753 y x h1 h2) (fun h3 : False => @lem5202333 h1)). Qed.
Lemma lem5203012 (y : real) (x : real) (h1 : term249) (h2 : term271 y x) : False.
Proof. exact (EQ_MP (@lem5203011 y x h1 h2) (@lem5202333 h1)). Qed.
Lemma lem5203013 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term316 x x' y) : False.
Proof. exact (or_elim (@lem5202313 x x' y h2) (fun h0 : x' = x => @lem5203008 y x' x h1 h2 h0) (fun h0 : x' = y => @lem5203004 x x' y h1 h2 h0)). Qed.
Lemma lem5203014 (x : real) (y : real) (h1 : term249) (h2 : term377 x y) : False.
Proof. exact (or_elim (@lem5202308 x y h2) (fun h0 : term271 y x => @lem5203012 y x h1 h0) (fun h0 : term295 x y => @lem5203010 x y h1 h0)). Qed.
Lemma lem5203015 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term433 x x' y) : False.
Proof. exact (or_elim (@lem5202307 x x' y h2) (fun h0 : term377 x y => @lem5203014 x y h1 h0) (fun h0 : term316 x x' y => @lem5203013 x x' y h1 h0)). Qed.
Lemma lem5203016 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term433 x x' y) : (term433 x x' y) = False.
Proof. exact (prop_ext (fun h3 : term433 x x' y => @lem5203015 x x' y h1 h2) (fun h3 : False => @lem5202307 x x' y h2)). Qed.
Lemma lem5203017 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term433 x x' y) : False.
Proof. exact (EQ_MP (@lem5203016 x x' y h1 h2) (@lem5202307 x x' y h2)). Qed.
Lemma lem5203018 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term433 x x' y) : term249 = False.
Proof. exact (prop_ext (fun h3 : term249 => @lem5203017 x x' y h1 h2) (fun h3 : False => @lem5202207 h1)). Qed.
Lemma lem5203019 (x : real) (x' : real) (y : real) (h1 : term249) (h2 : term433 x x' y) : False.
Proof. exact (EQ_MP (@lem5203018 x x' y h1 h2) (@lem5202207 h1)). Qed.
Lemma lem5203020 (x : real) (y : real) (h1 : term249) (h2 : term436 x y) : False.
Proof. exact (ex_elim (@lem5202186 x y h2) (fun x' : real => fun h0 : term435 x y x' => @lem5203019 x x' y h1 h0)). Qed.
Lemma lem5203021 (x : real) (h1 : term249) (h2 : term438 x) : False.
Proof. exact (ex_elim (@lem5202185 x h2) (fun y : real => fun h0 : term437 x y => @lem5203020 x y h1 h0)). Qed.
Lemma lem5203022 (h1 : term249) (h2 : term244) : False.
Proof. exact (ex_elim (@lem5202116 h2) (fun x : real => fun h0 : term439 x => @lem5203021 x h1 h0)). Qed.
Lemma lem5203023 (h1 : term249) (h2 : term244) : term249 = False.
Proof. exact (prop_ext (fun h3 : term249 => @lem5203022 h1 h2) (fun h3 : False => @lem5202184 h1)). Qed.
Lemma lem5203024 (h1 : term249) (h2 : term244) : False.
Proof. exact (EQ_MP (@lem5203023 h1 h2) (@lem5202184 h1)). Qed.
Lemma lem5203025 (h1 : term244) : term247.
Proof. exact (fun h0 : term249 => @lem5203024 h0 h1). Qed.
Lemma lem5203026 : term247 = term248.
Proof. exact (@lem69 term249). Qed.
Lemma lem5203027 (h1 : term244) : term248.
Proof. exact (EQ_MP (@lem5203026) (@lem5203025 h1)). Qed.
Lemma lem5203028 : term250.
Proof. exact (fun h0 : term244 => @lem5203027 h0). Qed.
Lemma lem5203029 : term150.
Proof. exact (EQ_MP (@lem5201654) (@lem5203028)). Qed.
Lemma lem5203031 : term150.
Proof. exact (@lem5201008 (@lem5203029)). Qed.
Lemma lem5203032 (h1 : term149) : term247.
Proof. exact (@lem5203031 (@lem5200993 h1)). Qed.
Lemma lem5203033 (h1 : term149) : False.
Proof. exact (@lem5203032 h1 (@lem1339697)). Qed.
Lemma lem5203034 (h1 : term149) : term149 = False.
Proof. exact (prop_ext (fun h2 : term149 => @lem5203033 h1) (fun h2 : False => @lem5200993 h1)). Qed.
Lemma lem5203035 (h1 : term149) : False.
Proof. exact (EQ_MP (@lem5203034 h1) (@lem5200993 h1)). Qed.
Lemma lem5203036 : term148.
Proof. exact (fun h0 : term149 => @lem5203035 h0). Qed.
Lemma lem5203037 : term146.
Proof. exact (EQ_MP (@lem5200992) (@lem5203036)). Qed.
Lemma lem5203038 : term113.
Proof. exact (EQ_MP (@lem5200988) (@lem5203037)). Qed.
Lemma lem5203039 : term112.
Proof. exact (EQ_MP (@lem5200790) (@lem5203038)). Qed.
