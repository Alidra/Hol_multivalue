Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_EQ_SELF_term_abbrevs.
Require Import DIV_0_spec.
Require Import DIV_1_spec.
Require Import DIV_ZERO_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LT_IMP_NE_spec.
Require Import LT_MULT_RCANCEL_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import ONE_spec.
Require Import RDIV_LT_EQ_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm80360_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Lemma lem199161 (h1 : term0 = term1) : term0 = term1.
Proof. exact (h1). Qed.
Lemma lem199162 (h1 : term0 = term1) : term1 = term0.
Proof. exact (SYM (@lem199161 h1)). Qed.
Lemma lem199163 (h1 : term1 = term0) : term1 = term0.
Proof. exact (h1). Qed.
Lemma lem199164 (h1 : term1 = term0) : term0 = term1.
Proof. exact (SYM (@lem199163 h1)). Qed.
Lemma lem199165 : (term0 = term1) = (term1 = term0).
Proof. exact (prop_ext (fun h1 : term0 = term1 => @lem199162 h1) (fun h1 : term1 = term0 => @lem199164 h1)). Qed.
Lemma lem199169 (n : nat) (m : nat) (h1 : (term2 m n) = (Peano.lt n m)) : (term2 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem199170 (n : nat) (m : nat) (h1 : (term2 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term2 m n).
Proof. exact (SYM (@lem199169 n m h1)). Qed.
Lemma lem199171 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term2 m n)) : (Peano.lt n m) = (term2 m n).
Proof. exact (h1). Qed.
Lemma lem199172 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term2 m n)) : (term2 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem199171 m n h1)). Qed.
Lemma lem199173 (m : nat) (n : nat) : ((term2 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term2 m n)).
Proof. exact (prop_ext (fun h1 : (term2 m n) = (Peano.lt n m) => @lem199170 n m h1) (fun h1 : (Peano.lt n m) = (term2 m n) => @lem199172 m n h1)). Qed.
Lemma lem199174 (m : nat) : (term3 m) = (term4 m).
Proof. exact (fun_ext (fun n : nat => @lem199173 m n)). Qed.
Lemma lem199175 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem199176 (m : nat) : (term5 m) = (term6 m).
Proof. exact (MK_COMB (@lem199175) (@lem199174 m)). Qed.
Lemma lem199177 : term7 = term8.
Proof. exact (fun_ext (fun m : nat => @lem199176 m)). Qed.
Lemma lem199178 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem199179 : term9 = term10.
Proof. exact (MK_COMB (@lem199178) (@lem199177)). Qed.
Lemma lem199180 : term10.
Proof. exact (EQ_MP (@lem199179) (@lem97961)). Qed.
Lemma lem199181 : term11.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem199182 (m : nat) : term12 m.
Proof. exact (@lem199181 m). Qed.
Lemma lem199183 (m : nat) : (term12 m) = (term13 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem199184 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem199183 m) (@lem199182 m)). Qed.
Lemma lem199185 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem199184 m n). Qed.
Lemma lem199186 (m : nat) (n : nat) : (term14 m n) = ((term15 m n) = (term16 m n)).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem199188 : term17.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem199189 (m : nat) : term18 m.
Proof. exact (@lem199188 m). Qed.
Lemma lem199190 (m : nat) : (term18 m) = ((term19 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem199192 (m : nat) : term20 m.
Proof. exact (@lem199180 m). Qed.
Lemma lem199193 (m : nat) : (term20 m) = (term6 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem199194 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem199193 m) (@lem199192 m)). Qed.
Lemma lem199195 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem199194 m n). Qed.
Lemma lem199196 (m : nat) (n : nat) : (term21 m n) = ((Peano.lt n m) = (term2 m n)).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem199198 : term22.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem199200 : term23.
Proof. exact (proj2 (@lem199198)). Qed.
Lemma lem199203 : term24.
Proof. exact (proj1 (@lem199200)). Qed.
Lemma lem199209 (n : nat) (h1 : (term25 n) = n) : (term25 n) = n.
Proof. exact (h1). Qed.
Lemma lem199210 (n : nat) (h1 : (term25 n) = n) : n = (term25 n).
Proof. exact (SYM (@lem199209 n h1)). Qed.
Lemma lem199211 (n : nat) (h1 : n = (term25 n)) : n = (term25 n).
Proof. exact (h1). Qed.
Lemma lem199212 (n : nat) (h1 : n = (term25 n)) : (term25 n) = n.
Proof. exact (SYM (@lem199211 n h1)). Qed.
Lemma lem199213 (n : nat) : ((term25 n) = n) = (n = (term25 n)).
Proof. exact (prop_ext (fun h1 : (term25 n) = n => @lem199210 n h1) (fun h1 : n = (term25 n) => @lem199212 n h1)). Qed.
Lemma lem199214 : term26 = term27.
Proof. exact (fun_ext (fun n : nat => @lem199213 n)). Qed.
Lemma lem199215 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem199216 : term24 = term28.
Proof. exact (MK_COMB (@lem199215) (@lem199214)). Qed.
Lemma lem199217 : term28.
Proof. exact (EQ_MP (@lem199216) (@lem199203)). Qed.
Lemma lem199218 (n : nat) : term29 n.
Proof. exact (@lem199217 n). Qed.
Lemma lem199219 (n : nat) : (term29 n) = (n = (term25 n)).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem199221 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem199222 (m : nat) (h1 : term30) : term31 m.
Proof. exact (@lem199221 h1 m). Qed.
Lemma lem199223 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem199224 (m : nat) (h1 : term30) : term32 m.
Proof. exact (EQ_MP (@lem199223 m) (@lem199222 m h1)). Qed.
Lemma lem199225 (m : nat) (n : nat) (h1 : term30) : term33 m n.
Proof. exact (@lem199224 m h1 n). Qed.
Lemma lem199226 (m : nat) (n : nat) : (term33 m n) = (term34 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem199227 (m : nat) (n : nat) (h1 : term30) : term34 m n.
Proof. exact (EQ_MP (@lem199226 m n) (@lem199225 m n h1)). Qed.
Lemma lem199228 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem199229 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.lt m n) : term35 m n.
Proof. exact (@lem199227 m n h1 (@lem199228 m n h2)). Qed.
Lemma lem199230 (m : nat) (n : nat) (h1 : Peano.lt m n) : term36 m n.
Proof. exact (fun h0 : term30 => @lem199229 m n h0 h1). Qed.
Lemma lem199231 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem199232 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.lt m n) : term35 m n.
Proof. exact (@lem199230 m n h2 (@lem199231 h1)). Qed.
Lemma lem199233 (m : nat) (n : nat) (h1 : term30) : term34 m n.
Proof. exact (fun h0 : Peano.lt m n => @lem199232 m n h1 h0). Qed.
Lemma lem199234 (m : nat) (h1 : term30) : term32 m.
Proof. exact (fun n : nat => @lem199233 m n h1). Qed.
Lemma lem199235 (h1 : term30) : term30.
Proof. exact (fun m : nat => @lem199234 m h1). Qed.
Lemma lem199236 : term37.
Proof. exact (fun h0 : term30 => @lem199235 h0). Qed.
Lemma lem199237 : term30.
Proof. exact (@lem199236 (@lem92038)). Qed.
Lemma lem199238 (m : nat) : term31 m.
Proof. exact (@lem199237 m). Qed.
Lemma lem199239 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem199240 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem199239 m) (@lem199238 m)). Qed.
Lemma lem199241 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem199240 m n). Qed.
Lemma lem199242 (m : nat) (n : nat) : (term33 m n) = (term34 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem199244 (n : nat) : term38 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem199245 (n : nat) : (term38 n) = (term39 n).
Proof. exact (eq_refl (term38 n)). Qed.
Lemma lem199246 (n : nat) : term39 n.
Proof. exact (EQ_MP (@lem199245 n) (@lem199244 n)). Qed.
Lemma lem199248 (n : nat) (h1 : term40 n) : term40 n.
Proof. exact (h1). Qed.
Lemma lem199249 (n : nat) : term41 n.
Proof. exact (@lem9784 (n = term0)). Qed.
Lemma lem199250 (n : nat) : (term41 n) = (term42 n).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem199251 (n : nat) : term42 n.
Proof. exact (EQ_MP (@lem199250 n) (@lem199249 n)). Qed.
Lemma lem199253 (n : nat) (h1 : term43 n) : term43 n.
Proof. exact (h1). Qed.
Lemma lem199254 (m : nat) : term38 m.
Proof. exact (@lem9784 (m = (NUMERAL 0))). Qed.
Lemma lem199255 (m : nat) : (term38 m) = (term39 m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem199256 (m : nat) : term39 m.
Proof. exact (EQ_MP (@lem199255 m) (@lem199254 m)). Qed.
Lemma lem199258 (m : nat) (h1 : term40 m) : term40 m.
Proof. exact (h1). Qed.
Lemma lem199259 (n : nat) : term44 n.
Proof. exact (@lem170051 n). Qed.
Lemma lem199260 (n : nat) : (term44 n) = ((term45 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term44 n)). Qed.
Lemma lem199267 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem199268 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem199269 (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.div m) = term46.
Proof. exact (MK_COMB (@lem199268) (@lem199267 m h1)). Qed.
Lemma lem199270 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem199271 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.div m n) = (term45 n).
Proof. exact (MK_COMB (@lem199269 m h1) (@lem199270 n)). Qed.
Lemma lem199273 (n : nat) : (term45 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem199260 n) (@lem199259 n)). Qed.
Lemma lem199274 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem199271 n m h1) (@lem199273 n)). Qed.
Lemma lem199275 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem199276 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term47 m n) = term48.
Proof. exact (MK_COMB (@lem199275) (@lem199274 n m h1)). Qed.
Lemma lem199278 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem199279 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((Nat.div m n) = m) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem199276 n m h1) (@lem199278 m h1)). Qed.
Lemma lem199281 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem199282 (x : nat) : (x = x) = True.
Proof. exact (@lem199281 nat x). Qed.
Lemma lem199283 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem199282 (NUMERAL 0)). Qed.
Lemma lem199284 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((Nat.div m n) = m) = True.
Proof. exact (TRANS (@lem199279 n m h1) (@lem199283)). Qed.
Lemma lem199285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem199286 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term49 n m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem199285) (@lem199284 n m h1)). Qed.
Lemma lem199292 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem199293 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem199294 (m : nat) (h1 : m = (NUMERAL 0)) : (@eq nat m) = term48.
Proof. exact (MK_COMB (@lem199293) (@lem199292 m h1)). Qed.
Lemma lem199295 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem199296 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem199294 m h1) (@lem199295)). Qed.
Lemma lem199298 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem199299 (x : nat) : (x = x) = True.
Proof. exact (@lem199298 nat x). Qed.
Lemma lem199300 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem199299 (NUMERAL 0)). Qed.
Lemma lem199301 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem199296 m h1) (@lem199300)). Qed.
Lemma lem199302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem199303 (m : nat) (h1 : m = (NUMERAL 0)) : (term50 m) = (or True).
Proof. exact (MK_COMB (@lem199302) (@lem199301 m h1)). Qed.
Lemma lem199306 (n : nat) : (n = term0) = (n = term0).
Proof. exact (eq_refl (n = term0)). Qed.
Lemma lem199307 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term51 m n) = (term52 n).
Proof. exact (MK_COMB (@lem199303 m h1) (@lem199306 n)). Qed.
Lemma lem199309 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem199310 (n : nat) : (term52 n) = True.
Proof. exact (@lem199309 (n = term0)). Qed.
Lemma lem199311 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term51 m n) = True.
Proof. exact (TRANS (@lem199307 n m h1) (@lem199310 n)). Qed.
Lemma lem199312 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (((Nat.div m n) = m) = (term51 m n)) = (True = True).
Proof. exact (MK_COMB (@lem199286 n m h1) (@lem199311 n m h1)). Qed.
Lemma lem199314 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem199315 : (True = True) = True.
Proof. exact (@lem199314 True). Qed.
Lemma lem199316 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (((Nat.div m n) = m) = (term51 m n)) = True.
Proof. exact (TRANS (@lem199312 n m h1) (@lem199315)). Qed.
Lemma lem199317 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : True = (((Nat.div m n) = m) = (term51 m n)).
Proof. exact (SYM (@lem199316 n m h1)). Qed.
Lemma lem199318 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((Nat.div m n) = m) = (term51 m n).
Proof. exact (EQ_MP (@lem199317 n m h1) (@lem0)). Qed.
Lemma lem199322 (m : nat) : term53 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem199342 (m : nat) (h1 : term40 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem199322 m (@lem199258 m h1)). Qed.
Lemma lem199343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem199344 (m : nat) (h1 : term40 m) : (term50 m) = (or False).
Proof. exact (MK_COMB (@lem199343) (@lem199342 m h1)). Qed.
Lemma lem199347 (n : nat) : (n = term0) = (n = term0).
Proof. exact (eq_refl (n = term0)). Qed.
Lemma lem199348 (n : nat) (m : nat) (h1 : term40 m) : (term51 m n) = (term54 n).
Proof. exact (MK_COMB (@lem199344 m h1) (@lem199347 n)). Qed.
Lemma lem199350 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem199351 (n : nat) : (term54 n) = (n = term0).
Proof. exact (@lem199350 (n = term0)). Qed.
Lemma lem199354 (n : nat) (m : nat) (h1 : term40 m) : (term51 m n) = (n = term0).
Proof. exact (TRANS (@lem199348 n m h1) (@lem199351 n)). Qed.
Lemma lem199355 (n : nat) (m : nat) : (term49 n m) = (term49 n m).
Proof. exact (eq_refl (term49 n m)). Qed.
Lemma lem199356 (n : nat) (m : nat) (h1 : term40 m) : (((Nat.div m n) = m) = (term51 m n)) = (((Nat.div m n) = m) = (n = term0)).
Proof. exact (MK_COMB (@lem199355 n m) (@lem199354 n m h1)). Qed.
Lemma lem199359 (n : nat) (m : nat) (h1 : term40 m) : (((Nat.div m n) = m) = (n = term0)) = (((Nat.div m n) = m) = (term51 m n)).
Proof. exact (SYM (@lem199356 n m h1)). Qed.
Lemma lem199360 (n : nat) : term55 n.
Proof. exact (@lem182043 n). Qed.
Lemma lem199361 (n : nat) : (term55 n) = ((term56 n) = n).
Proof. exact (eq_refl (term55 n)). Qed.
Lemma lem199381 (n : nat) (h1 : n = term0) : n = term0.
Proof. exact (h1). Qed.
Lemma lem199382 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem199383 (m : nat) (n : nat) (h1 : n = term0) : (Nat.div m n) = (term56 m).
Proof. exact (MK_COMB (@lem199382 m) (@lem199381 n h1)). Qed.
Lemma lem199385 (n : nat) : (term56 n) = n.
Proof. exact (EQ_MP (@lem199361 n) (@lem199360 n)). Qed.
Lemma lem199386 (m : nat) : (term56 m) = m.
Proof. exact (@lem199385 m). Qed.
Lemma lem199387 (m : nat) (n : nat) (h1 : n = term0) : (Nat.div m n) = m.
Proof. exact (TRANS (@lem199383 m n h1) (@lem199386 m)). Qed.
Lemma lem199388 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem199389 (m : nat) (n : nat) (h1 : n = term0) : (term47 m n) = (@eq nat m).
Proof. exact (MK_COMB (@lem199388) (@lem199387 m n h1)). Qed.
Lemma lem199390 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem199391 (m : nat) (n : nat) (h1 : n = term0) : ((Nat.div m n) = m) = (m = m).
Proof. exact (MK_COMB (@lem199389 m n h1) (@lem199390 m)). Qed.
Lemma lem199393 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem199394 (x : nat) : (x = x) = True.
Proof. exact (@lem199393 nat x). Qed.
Lemma lem199395 (m : nat) : (m = m) = True.
Proof. exact (@lem199394 m). Qed.
Lemma lem199396 (m : nat) (n : nat) (h1 : n = term0) : ((Nat.div m n) = m) = True.
Proof. exact (TRANS (@lem199391 m n h1) (@lem199395 m)). Qed.
Lemma lem199397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem199398 (m : nat) (n : nat) (h1 : n = term0) : (term49 n m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem199397) (@lem199396 m n h1)). Qed.
Lemma lem199402 (n : nat) (h1 : n = term0) : n = term0.
Proof. exact (h1). Qed.
Lemma lem199403 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem199404 (n : nat) (h1 : n = term0) : (@eq nat n) = term57.
Proof. exact (MK_COMB (@lem199403) (@lem199402 n h1)). Qed.
Lemma lem199405 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem199406 (n : nat) (h1 : n = term0) : (n = term0) = (term0 = term0).
Proof. exact (MK_COMB (@lem199404 n h1) (@lem199405)). Qed.
Lemma lem199408 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem199409 (x : nat) : (x = x) = True.
Proof. exact (@lem199408 nat x). Qed.
Lemma lem199410 : (term0 = term0) = True.
Proof. exact (@lem199409 term0). Qed.
Lemma lem199411 (n : nat) (h1 : n = term0) : (n = term0) = True.
Proof. exact (TRANS (@lem199406 n h1) (@lem199410)). Qed.
Lemma lem199412 (m : nat) (n : nat) (h1 : n = term0) : (((Nat.div m n) = m) = (n = term0)) = (True = True).
Proof. exact (MK_COMB (@lem199398 m n h1) (@lem199411 n h1)). Qed.
Lemma lem199414 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem199415 : (True = True) = True.
Proof. exact (@lem199414 True). Qed.
Lemma lem199416 (m : nat) (n : nat) (h1 : n = term0) : (((Nat.div m n) = m) = (n = term0)) = True.
Proof. exact (TRANS (@lem199412 m n h1) (@lem199415)). Qed.
Lemma lem199417 (m : nat) (n : nat) (h1 : n = term0) : True = (((Nat.div m n) = m) = (n = term0)).
Proof. exact (SYM (@lem199416 m n h1)). Qed.
Lemma lem199418 (m : nat) (n : nat) (h1 : n = term0) : ((Nat.div m n) = m) = (n = term0).
Proof. exact (EQ_MP (@lem199417 m n h1) (@lem0)). Qed.
Lemma lem199435 (n : nat) : term58 n.
Proof. exact (@lem82 (n = term0)). Qed.
Lemma lem199453 (n : nat) (h1 : term43 n) : (n = term0) = False.
Proof. exact (@lem199435 n (@lem199253 n h1)). Qed.
Lemma lem199454 (n : nat) (m : nat) : (term49 n m) = (term49 n m).
Proof. exact (eq_refl (term49 n m)). Qed.
Lemma lem199455 (m : nat) (n : nat) (h1 : term43 n) : (((Nat.div m n) = m) = (n = term0)) = (((Nat.div m n) = m) = False).
Proof. exact (MK_COMB (@lem199454 n m) (@lem199453 n h1)). Qed.
Lemma lem199457 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem199458 (n : nat) (m : nat) : (((Nat.div m n) = m) = False) = (term59 n m).
Proof. exact (@lem199457 ((Nat.div m n) = m)). Qed.
Lemma lem199461 (m : nat) (n : nat) (h1 : term43 n) : (((Nat.div m n) = m) = (n = term0)) = (term59 n m).
Proof. exact (TRANS (@lem199455 m n h1) (@lem199458 n m)). Qed.
Lemma lem199462 (m : nat) (n : nat) (h1 : term43 n) : (term59 n m) = (((Nat.div m n) = m) = (n = term0)).
Proof. exact (SYM (@lem199461 m n h1)). Qed.
Lemma lem199463 (n : nat) : term60 n.
Proof. exact (@lem158192 n). Qed.
Lemma lem199464 (n : nat) : (term60 n) = ((term61 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term60 n)). Qed.
Lemma lem199469 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem199470 (m : nat) (h1 : m = (NUMERAL 0)) : (NUMERAL 0) = m.
Proof. exact (SYM (@lem199469 m h1)). Qed.
Lemma lem199471 (m : nat) (h1 : (NUMERAL 0) = m) : (NUMERAL 0) = m.
Proof. exact (h1). Qed.
Lemma lem199472 (m : nat) (h1 : (NUMERAL 0) = m) : m = (NUMERAL 0).
Proof. exact (SYM (@lem199471 m h1)). Qed.
Lemma lem199473 (m : nat) : (m = (NUMERAL 0)) = ((NUMERAL 0) = m).
Proof. exact (prop_ext (fun h1 : m = (NUMERAL 0) => @lem199470 m h1) (fun h1 : (NUMERAL 0) = m => @lem199472 m h1)). Qed.
Lemma lem199474 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem199475 (m : nat) : (term40 m) = (term62 m).
Proof. exact (MK_COMB (@lem199474) (@lem199473 m)). Qed.
Lemma lem199476 (m : nat) (h1 : term40 m) : term62 m.
Proof. exact (EQ_MP (@lem199475 m) (@lem199258 m h1)). Qed.
Lemma lem199477 (m : nat) : term63 m.
Proof. exact (@lem82 ((NUMERAL 0) = m)). Qed.
Lemma lem199495 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem199496 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem199497 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (term61 m).
Proof. exact (MK_COMB (@lem199496 m) (@lem199495 n h1)). Qed.
Lemma lem199499 (n : nat) : (term61 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem199464 n) (@lem199463 n)). Qed.
Lemma lem199500 (m : nat) : (term61 m) = (NUMERAL 0).
Proof. exact (@lem199499 m). Qed.
Lemma lem199501 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem199497 m n h1) (@lem199500 m)). Qed.
Lemma lem199502 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem199503 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term47 m n) = term48.
Proof. exact (MK_COMB (@lem199502) (@lem199501 m n h1)). Qed.
Lemma lem199504 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem199505 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((Nat.div m n) = m) = ((NUMERAL 0) = m).
Proof. exact (MK_COMB (@lem199503 m n h1) (@lem199504 m)). Qed.
Lemma lem199507 (m : nat) (h1 : term40 m) : ((NUMERAL 0) = m) = False.
Proof. exact (@lem199477 m (@lem199476 m h1)). Qed.
Lemma lem199508 (m : nat) (n : nat) (h1 : term40 m) (h2 : n = (NUMERAL 0)) : ((Nat.div m n) = m) = False.
Proof. exact (TRANS (@lem199505 m n h2) (@lem199507 m h1)). Qed.
Lemma lem199509 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem199510 (m : nat) (n : nat) (h1 : term40 m) (h2 : n = (NUMERAL 0)) : (term59 n m) = (~ False).
Proof. exact (MK_COMB (@lem199509) (@lem199508 m n h1 h2)). Qed.
Lemma lem199512 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem199513 (m : nat) (n : nat) (h1 : term40 m) (h2 : n = (NUMERAL 0)) : (term59 n m) = True.
Proof. exact (TRANS (@lem199510 m n h1 h2) (@lem199512)). Qed.
Lemma lem199514 (m : nat) (n : nat) (h1 : term40 m) (h2 : n = (NUMERAL 0)) : True = (term59 n m).
Proof. exact (SYM (@lem199513 m n h1 h2)). Qed.
Lemma lem199515 (m : nat) (n : nat) (h1 : term40 m) (h2 : n = (NUMERAL 0)) : term59 n m.
Proof. exact (EQ_MP (@lem199514 m n h1 h2) (@lem0)). Qed.
Lemma lem199563 (m : nat) (n : nat) : term34 m n.
Proof. exact (EQ_MP (@lem199242 m n) (@lem199241 m n)). Qed.
Lemma lem199564 (n : nat) (m : nat) : term64 n m.
Proof. exact (@lem199563 (Nat.div m n) m). Qed.
Lemma lem199565 (a : nat) : term65 a.
Proof. exact (@lem188986 a). Qed.
Lemma lem199566 (a : nat) : (term65 a) = (term66 a).
Proof. exact (eq_refl (term65 a)). Qed.
Lemma lem199567 (a : nat) : term66 a.
Proof. exact (EQ_MP (@lem199566 a) (@lem199565 a)). Qed.
Lemma lem199568 (a : nat) (b : nat) : term67 a b.
Proof. exact (@lem199567 a b). Qed.
Lemma lem199569 (b : nat) (a : nat) : (term67 a b) = (term68 b a).
Proof. exact (eq_refl (term67 a b)). Qed.
Lemma lem199570 (b : nat) (a : nat) : term68 b a.
Proof. exact (EQ_MP (@lem199569 b a) (@lem199568 a b)). Qed.
Lemma lem199571 (b : nat) (a : nat) (n : nat) : term69 b a n.
Proof. exact (@lem199570 b a n). Qed.
Lemma lem199572 (b : nat) (a : nat) (n : nat) : (term69 b a n) = (term70 b a n).
Proof. exact (eq_refl (term69 b a n)). Qed.
Lemma lem199573 (b : nat) (a : nat) (n : nat) : term70 b a n.
Proof. exact (EQ_MP (@lem199572 b a n) (@lem199571 b a n)). Qed.
Lemma lem199574 (a : nat) (h1 : term40 a) : term40 a.
Proof. exact (h1). Qed.
Lemma lem199575 (b : nat) (n : nat) (a : nat) (h1 : term40 a) : (term71 b a n) = (term72 b a n).
Proof. exact (@lem199573 b a n (@lem199574 a h1)). Qed.
Lemma lem199607 (n : nat) : term53 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem199621 (b : nat) (a : nat) (n : nat) : term70 b a n.
Proof. exact (fun h0 : term40 a => @lem199575 b n a h0). Qed.
Lemma lem199622 (n : nat) (m : nat) : term73 n m.
Proof. exact (@lem199621 m n m). Qed.
Lemma lem199624 (n : nat) (h1 : term40 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem199607 n (@lem199248 n h1)). Qed.
Lemma lem199625 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem199626 (n : nat) (h1 : term40 n) : (term40 n) = (~ False).
Proof. exact (MK_COMB (@lem199625) (@lem199624 n h1)). Qed.
Lemma lem199628 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem199629 (n : nat) (h1 : term40 n) : (term40 n) = True.
Proof. exact (TRANS (@lem199626 n h1) (@lem199628)). Qed.
Lemma lem199630 (n : nat) (h1 : term40 n) : True = (term40 n).
Proof. exact (SYM (@lem199629 n h1)). Qed.
Lemma lem199631 (n : nat) (h1 : term40 n) : term40 n.
Proof. exact (EQ_MP (@lem199630 n h1) (@lem0)). Qed.
Lemma lem199632 (m : nat) (n : nat) (h1 : term40 n) : (term74 n m) = (term75 n m).
Proof. exact (@lem199622 n m (@lem199631 n h1)). Qed.
Lemma lem199633 (m : nat) (n : nat) (h1 : term40 n) : (term75 n m) = (term74 n m).
Proof. exact (SYM (@lem199632 m n h1)). Qed.
Lemma lem199635 (n : nat) : n = (term25 n).
Proof. exact (EQ_MP (@lem199219 n) (@lem199218 n)). Qed.
Lemma lem199636 (m : nat) : m = (term25 m).
Proof. exact (@lem199635 m). Qed.
Lemma lem199637 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem199638 (m : nat) : (Peano.lt m) = (term76 m).
Proof. exact (MK_COMB (@lem199637) (@lem199636 m)). Qed.
Lemma lem199639 (n : nat) (m : nat) : (Nat.mul n m) = (Nat.mul n m).
Proof. exact (eq_refl (Nat.mul n m)). Qed.
Lemma lem199640 (n : nat) (m : nat) : (term75 n m) = (term77 n m).
Proof. exact (MK_COMB (@lem199638 m) (@lem199639 n m)). Qed.
Lemma lem199641 (n : nat) (m : nat) : (term77 n m) = (term75 n m).
Proof. exact (SYM (@lem199640 n m)). Qed.
Lemma lem199642 (m : nat) : term78 m.
Proof. exact (@lem105963 m). Qed.
Lemma lem199643 (m : nat) : (term78 m) = (term79 m).
Proof. exact (eq_refl (term78 m)). Qed.
Lemma lem199644 (m : nat) : term79 m.
Proof. exact (EQ_MP (@lem199643 m) (@lem199642 m)). Qed.
Lemma lem199645 (m : nat) (n : nat) : term80 m n.
Proof. exact (@lem199644 m n). Qed.
Lemma lem199646 (m : nat) (n : nat) : (term80 m n) = (term81 m n).
Proof. exact (eq_refl (term80 m n)). Qed.
Lemma lem199647 (m : nat) (n : nat) : term81 m n.
Proof. exact (EQ_MP (@lem199646 m n) (@lem199645 m n)). Qed.
Lemma lem199648 (m : nat) (n : nat) (p : nat) : term82 m n p.
Proof. exact (@lem199647 m n p). Qed.
Lemma lem199649 (m : nat) (n : nat) (p : nat) : (term82 m n p) = ((term83 m n p) = (term84 m n p)).
Proof. exact (eq_refl (term82 m n p)). Qed.
Lemma lem199651 (m : nat) : term53 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem199691 (m : nat) (n : nat) (p : nat) : (term83 m n p) = (term84 m n p).
Proof. exact (EQ_MP (@lem199649 m n p) (@lem199648 m n p)). Qed.
Lemma lem199692 (n : nat) (m : nat) : (term77 n m) = (term85 n m).
Proof. exact (@lem199691 term0 n m). Qed.
Lemma lem199696 (m : nat) (h1 : term40 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem199651 m (@lem199258 m h1)). Qed.
Lemma lem199697 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem199698 (m : nat) (h1 : term40 m) : (term40 m) = (~ False).
Proof. exact (MK_COMB (@lem199697) (@lem199696 m h1)). Qed.
Lemma lem199700 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem199701 (m : nat) (h1 : term40 m) : (term40 m) = True.
Proof. exact (TRANS (@lem199698 m h1) (@lem199700)). Qed.
Lemma lem199702 (n : nat) : (term86 n) = (term86 n).
Proof. exact (eq_refl (term86 n)). Qed.
Lemma lem199703 (n : nat) (m : nat) (h1 : term40 m) : (term85 n m) = (term87 n).
Proof. exact (MK_COMB (@lem199702 n) (@lem199701 m h1)). Qed.
Lemma lem199705 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem199706 (n : nat) : (term87 n) = (term88 n).
Proof. exact (@lem199705 (term88 n)). Qed.
Lemma lem199707 (n : nat) (m : nat) (h1 : term40 m) : (term85 n m) = (term88 n).
Proof. exact (TRANS (@lem199703 n m h1) (@lem199706 n)). Qed.
Lemma lem199708 (n : nat) (m : nat) (h1 : term40 m) : (term77 n m) = (term88 n).
Proof. exact (TRANS (@lem199692 n m) (@lem199707 n m h1)). Qed.
Lemma lem199709 (n : nat) (m : nat) (h1 : term40 m) : (term88 n) = (term77 n m).
Proof. exact (SYM (@lem199708 n m h1)). Qed.
Lemma lem199711 (m : nat) (n : nat) : (Peano.lt n m) = (term2 m n).
Proof. exact (EQ_MP (@lem199196 m n) (@lem199195 m n)). Qed.
Lemma lem199712 (n : nat) : (term88 n) = (term89 n).
Proof. exact (@lem199711 n term0). Qed.
Lemma lem199714 : term0 = term1.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem199715 (n : nat) : (Peano.le n) = (Peano.le n).
Proof. exact (eq_refl (Peano.le n)). Qed.
Lemma lem199716 (n : nat) : (term90 n) = (term91 n).
Proof. exact (MK_COMB (@lem199715 n) (@lem199714)). Qed.
Lemma lem199718 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (EQ_MP (@lem199186 m n) (@lem199185 m n)). Qed.
Lemma lem199719 (n : nat) : (term91 n) = (term92 n).
Proof. exact (@lem199718 n (NUMERAL 0)). Qed.
Lemma lem199725 (m : nat) : (term19 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem199190 m) (@lem199189 m)). Qed.
Lemma lem199726 (n : nat) : (term19 n) = (n = (NUMERAL 0)).
Proof. exact (@lem199725 n). Qed.
Lemma lem199729 (n : nat) : (term93 n) = (term93 n).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem199730 (n : nat) : (term92 n) = (term94 n).
Proof. exact (MK_COMB (@lem199729 n) (@lem199726 n)). Qed.
Lemma lem199733 (n : nat) : (term91 n) = (term94 n).
Proof. exact (TRANS (@lem199719 n) (@lem199730 n)). Qed.
Lemma lem199734 (n : nat) : (term90 n) = (term94 n).
Proof. exact (TRANS (@lem199716 n) (@lem199733 n)). Qed.
Lemma lem199735 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem199736 (n : nat) : (term89 n) = (term95 n).
Proof. exact (MK_COMB (@lem199735) (@lem199734 n)). Qed.
Lemma lem199737 (n : nat) : (term88 n) = (term95 n).
Proof. exact (TRANS (@lem199712 n) (@lem199736 n)). Qed.
Lemma lem199738 (n : nat) : (term95 n) = (term88 n).
Proof. exact (SYM (@lem199737 n)). Qed.
Lemma lem199752 (n : nat) : term58 n.
Proof. exact (@lem82 (n = term0)). Qed.
Lemma lem199765 (n : nat) : term53 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem199783 : term1 = term0.
Proof. exact (EQ_MP (@lem199165) (@lem80361)). Qed.
Lemma lem199784 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem199785 (n : nat) : (n = term1) = (n = term0).
Proof. exact (MK_COMB (@lem199784 n) (@lem199783)). Qed.
Lemma lem199787 (n : nat) (h1 : term43 n) : (n = term0) = False.
Proof. exact (@lem199752 n (@lem199253 n h1)). Qed.
Lemma lem199788 (n : nat) (h1 : term43 n) : (n = term1) = False.
Proof. exact (TRANS (@lem199785 n) (@lem199787 n h1)). Qed.
Lemma lem199789 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem199790 (n : nat) (h1 : term43 n) : (term93 n) = (or False).
Proof. exact (MK_COMB (@lem199789) (@lem199788 n h1)). Qed.
Lemma lem199792 (n : nat) (h1 : term40 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem199765 n (@lem199248 n h1)). Qed.
Lemma lem199793 (n : nat) (h1 : term40 n) (h2 : term43 n) : (term94 n) = (False \/ False).
Proof. exact (MK_COMB (@lem199790 n h2) (@lem199792 n h1)). Qed.
Lemma lem199795 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem199796 : (False \/ False) = False.
Proof. exact (@lem199795 False). Qed.
Lemma lem199797 (n : nat) (h1 : term40 n) (h2 : term43 n) : (term94 n) = False.
Proof. exact (TRANS (@lem199793 n h1 h2) (@lem199796)). Qed.
Lemma lem199798 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem199799 (n : nat) (h1 : term40 n) (h2 : term43 n) : (term95 n) = (~ False).
Proof. exact (MK_COMB (@lem199798) (@lem199797 n h1 h2)). Qed.
Lemma lem199801 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem199802 (n : nat) (h1 : term40 n) (h2 : term43 n) : (term95 n) = True.
Proof. exact (TRANS (@lem199799 n h1 h2) (@lem199801)). Qed.
Lemma lem199803 (n : nat) (h1 : term40 n) (h2 : term43 n) : True = (term95 n).
Proof. exact (SYM (@lem199802 n h1 h2)). Qed.
Lemma lem199804 (n : nat) (h1 : term40 n) (h2 : term43 n) : term95 n.
Proof. exact (EQ_MP (@lem199803 n h1 h2) (@lem0)). Qed.
Lemma lem199805 (n : nat) (h1 : term40 n) (h2 : term43 n) : term88 n.
Proof. exact (EQ_MP (@lem199738 n) (@lem199804 n h1 h2)). Qed.
Lemma lem199806 (m : nat) (n : nat) (h1 : term40 m) (h2 : term40 n) (h3 : term43 n) : term77 n m.
Proof. exact (EQ_MP (@lem199709 n m h1) (@lem199805 n h2 h3)). Qed.
Lemma lem199807 (m : nat) (n : nat) (h1 : term40 m) (h2 : term40 n) (h3 : term43 n) : term75 n m.
Proof. exact (EQ_MP (@lem199641 n m) (@lem199806 m n h1 h2 h3)). Qed.
Lemma lem199808 (m : nat) (n : nat) (h1 : term40 m) (h2 : term40 n) (h3 : term43 n) : term74 n m.
Proof. exact (EQ_MP (@lem199633 m n h2) (@lem199807 m n h1 h2 h3)). Qed.
Lemma lem199810 (m : nat) (n : nat) (h1 : term40 m) (h2 : term40 n) (h3 : term43 n) : term59 n m.
Proof. exact (@lem199564 n m (@lem199808 m n h1 h2 h3)). Qed.
Lemma lem199811 (m : nat) (n : nat) (h1 : term40 m) (h2 : term43 n) : term59 n m.
Proof. exact (or_elim (@lem199246 n) (fun h0 : n = (NUMERAL 0) => @lem199515 m n h1 h0) (fun h0 : term40 n => @lem199810 m n h1 h0 h2)). Qed.
Lemma lem199812 (m : nat) (n : nat) (h1 : term40 m) (h2 : term43 n) : ((Nat.div m n) = m) = (n = term0).
Proof. exact (EQ_MP (@lem199462 m n h2) (@lem199811 m n h1 h2)). Qed.
Lemma lem199813 (n : nat) (m : nat) (h1 : term40 m) : ((Nat.div m n) = m) = (n = term0).
Proof. exact (or_elim (@lem199251 n) (fun h0 : n = term0 => @lem199418 m n h0) (fun h0 : term43 n => @lem199812 m n h1 h0)). Qed.
Lemma lem199814 (n : nat) (m : nat) (h1 : term40 m) : ((Nat.div m n) = m) = (term51 m n).
Proof. exact (EQ_MP (@lem199359 n m h1) (@lem199813 n m h1)). Qed.
Lemma lem199815 (m : nat) (n : nat) : ((Nat.div m n) = m) = (term51 m n).
Proof. exact (or_elim (@lem199256 m) (fun h0 : m = (NUMERAL 0) => @lem199318 n m h0) (fun h0 : term40 m => @lem199814 n m h0)). Qed.
Lemma lem199820 (m : nat) : term96 m.
Proof. exact (fun n : nat => @lem199815 m n). Qed.
Lemma lem199825 : term97.
Proof. exact (fun m : nat => @lem199820 m). Qed.
