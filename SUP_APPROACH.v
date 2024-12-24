Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUP_APPROACH_term_abbrevs.
Require Import DE_MORGAN_THM_spec.
Require Import DISJ_ACI_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import REAL_NOT_LT_spec.
Require Import SUP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm1823_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem5199225 (s : real -> Prop) : term0 s.
Proof. exact (@lem5136700 s). Qed.
Lemma lem5199226 (s : real -> Prop) : (term0 s) = (term1 s).
Proof. exact (eq_refl (term0 s)). Qed.
Lemma lem5199228 (x : real) : term2 x.
Proof. exact (@lem1376537 x). Qed.
Lemma lem5199229 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem5199230 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem5199229 x) (@lem5199228 x)). Qed.
Lemma lem5199231 (x : real) (y : real) : term4 x y.
Proof. exact (@lem5199230 x y). Qed.
Lemma lem5199232 (y : real) (x : real) : (term4 x y) = ((term5 x y) = (real_le y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem5199234 (x : real) : term2 x.
Proof. exact (@lem1376537 x). Qed.
Lemma lem5199235 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem5199236 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem5199235 x) (@lem5199234 x)). Qed.
Lemma lem5199237 (x : real) (y : real) : term4 x y.
Proof. exact (@lem5199236 x y). Qed.
Lemma lem5199238 (y : real) (x : real) : (term4 x y) = ((term5 x y) = (real_le y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem5199240 (t1 : Prop) : term6 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem5199241 (t1 : Prop) : (term6 t1) = (term7 t1).
Proof. exact (eq_refl (term6 t1)). Qed.
Lemma lem5199242 (t1 : Prop) : term7 t1.
Proof. exact (EQ_MP (@lem5199241 t1) (@lem5199240 t1)). Qed.
Lemma lem5199243 (t1 : Prop) (t2 : Prop) : term8 t1 t2.
Proof. exact (@lem5199242 t1 t2). Qed.
Lemma lem5199244 (t1 : Prop) (t2 : Prop) : (term8 t1 t2) = (term9 t1 t2).
Proof. exact (eq_refl (term8 t1 t2)). Qed.
Lemma lem5199245 (t1 : Prop) (t2 : Prop) : term9 t1 t2.
Proof. exact (EQ_MP (@lem5199244 t1 t2) (@lem5199243 t1 t2)). Qed.
Lemma lem5199248 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem5199249 {A : Type'} (P : A -> Prop) : (term10 A P) = ((term11 A P) = (term12 A P)).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem5199255 (c : real) (s : real -> Prop) (h1 : term13 c s) : term13 c s.
Proof. exact (h1). Qed.
Lemma lem5199256 (c : real) (s : real -> Prop) (h1 : term14 c s) : term14 c s.
Proof. exact (h1). Qed.
Lemma lem5199257 (s : real -> Prop) (h1 : term15 s) : term15 s.
Proof. exact (h1). Qed.
Lemma lem5199258 (c : real) (s : real -> Prop) (h1 : term16 c s) : term16 c s.
Proof. exact (h1). Qed.
Lemma lem5199259 (s : real -> Prop) (h1 : term17 s) : term17 s.
Proof. exact (h1). Qed.
Lemma lem5199261 (p : Prop) : p = (term18 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5199262 (s : real -> Prop) (c : real) : (term19 s c) = (term20 s c).
Proof. exact (@lem5199261 (term19 s c)). Qed.
Lemma lem5199263 (s : real -> Prop) (c : real) : (term20 s c) = (term19 s c).
Proof. exact (SYM (@lem5199262 s c)). Qed.
Lemma lem5199264 (s : real -> Prop) (c : real) (h1 : term21 s c) : term21 s c.
Proof. exact (h1). Qed.
Lemma lem5199266 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (EQ_MP (@lem5199249 A P) (@lem5199248 A P)). Qed.
Lemma lem5199267 (P : real -> Prop) : (term22 P) = (term23 P).
Proof. exact (@lem5199266 real P). Qed.
Lemma lem5199268 (s : real -> Prop) (c : real) : (term24 s c) = (term25 s c).
Proof. exact (@lem5199267 (term26 s c)). Qed.
Lemma lem5199269 (s : real -> Prop) (c : real) (x : real) : (term27 s c x) = (term28 s c x).
Proof. exact (eq_refl (term27 s c x)). Qed.
Lemma lem5199270 (s : real -> Prop) (c : real) : (term29 s c) = (term26 s c).
Proof. exact (fun_ext (fun x : real => @lem5199269 s c x)). Qed.
Lemma lem5199271 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5199272 (s : real -> Prop) (c : real) : (term30 s c) = (term19 s c).
Proof. exact (MK_COMB (@lem5199271) (@lem5199270 s c)). Qed.
Lemma lem5199273 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5199274 (s : real -> Prop) (c : real) : (term24 s c) = (term21 s c).
Proof. exact (MK_COMB (@lem5199273) (@lem5199272 s c)). Qed.
Lemma lem5199275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5199276 (s : real -> Prop) (c : real) : (term31 s c) = (term32 s c).
Proof. exact (MK_COMB (@lem5199275) (@lem5199274 s c)). Qed.
Lemma lem5199277 (s : real -> Prop) (c : real) (x : real) : (term27 s c x) = (term28 s c x).
Proof. exact (eq_refl (term27 s c x)). Qed.
Lemma lem5199278 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5199279 (s : real -> Prop) (c : real) (x : real) : (term33 s c x) = (term34 s c x).
Proof. exact (MK_COMB (@lem5199278) (@lem5199277 s c x)). Qed.
Lemma lem5199280 (s : real -> Prop) (c : real) : (term35 s c) = (term36 s c).
Proof. exact (fun_ext (fun x : real => @lem5199279 s c x)). Qed.
Lemma lem5199281 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5199282 (s : real -> Prop) (c : real) : (term25 s c) = (term37 s c).
Proof. exact (MK_COMB (@lem5199281) (@lem5199280 s c)). Qed.
Lemma lem5199283 (s : real -> Prop) (c : real) : ((term24 s c) = (term25 s c)) = ((term21 s c) = (term37 s c)).
Proof. exact (MK_COMB (@lem5199276 s c) (@lem5199282 s c)). Qed.
Lemma lem5199284 (s : real -> Prop) (c : real) : (term21 s c) = (term37 s c).
Proof. exact (EQ_MP (@lem5199283 s c) (@lem5199268 s c)). Qed.
Lemma lem5199290 (t1 : Prop) (t2 : Prop) : (term38 t1 t2) = (term39 t1 t2).
Proof. exact (proj1 (@lem5199245 t1 t2)). Qed.
Lemma lem5199291 (s : real -> Prop) (c : real) (x : real) : (term34 s c x) = (term40 s c x).
Proof. exact (@lem5199290 (@IN real x s) (real_lt c x)). Qed.
Lemma lem5199295 (y : real) (x : real) : (term5 x y) = (real_le y x).
Proof. exact (EQ_MP (@lem5199238 y x) (@lem5199237 x y)). Qed.
Lemma lem5199296 (x : real) (c : real) : (term5 c x) = (real_le x c).
Proof. exact (@lem5199295 x c). Qed.
Lemma lem5199297 (x : real) (s : real -> Prop) : (term41 x s) = (term41 x s).
Proof. exact (eq_refl (term41 x s)). Qed.
Lemma lem5199298 (s : real -> Prop) (x : real) (c : real) : (term40 s c x) = (term42 s x c).
Proof. exact (MK_COMB (@lem5199297 x s) (@lem5199296 x c)). Qed.
Lemma lem5199301 (s : real -> Prop) (x : real) (c : real) : (term34 s c x) = (term42 s x c).
Proof. exact (TRANS (@lem5199291 s c x) (@lem5199298 s x c)). Qed.
Lemma lem5199302 (s : real -> Prop) (c : real) : (term36 s c) = (term43 s c).
Proof. exact (fun_ext (fun x : real => @lem5199301 s x c)). Qed.
Lemma lem5199303 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5199304 (s : real -> Prop) (c : real) : (term37 s c) = (term44 s c).
Proof. exact (MK_COMB (@lem5199303) (@lem5199302 s c)). Qed.
Lemma lem5199309 (s : real -> Prop) (c : real) : (term21 s c) = (term44 s c).
Proof. exact (TRANS (@lem5199284 s c) (@lem5199304 s c)). Qed.
Lemma lem5199310 (s : real -> Prop) (c : real) (h1 : term21 s c) : term44 s c.
Proof. exact (EQ_MP (@lem5199309 s c) (@lem5199264 s c h1)). Qed.
Lemma lem5199312 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem5199313 (c : real) (s : real -> Prop) : (term45 c s) = (term46 c s).
Proof. exact (@lem5199312 (term16 c s)). Qed.
Lemma lem5199315 (y : real) (x : real) : (term5 x y) = (real_le y x).
Proof. exact (EQ_MP (@lem5199232 y x) (@lem5199231 x y)). Qed.
Lemma lem5199316 (s : real -> Prop) (c : real) : (term46 c s) = (term47 s c).
Proof. exact (@lem5199315 (sup s) c). Qed.
Lemma lem5199317 (s : real -> Prop) (c : real) : (term45 c s) = (term47 s c).
Proof. exact (TRANS (@lem5199313 c s) (@lem5199316 s c)). Qed.
Lemma lem5199318 (c : real) (s : real -> Prop) : (term47 s c) = (term45 c s).
Proof. exact (SYM (@lem5199317 s c)). Qed.
Lemma lem5199319 (s : real -> Prop) (h1 : term17 s) (h2 : term15 s) : term48 s.
Proof. exact (conj (@lem5199257 s h2) (@lem5199259 s h1)). Qed.
Lemma lem5199321 (s : real -> Prop) : term1 s.
Proof. exact (EQ_MP (@lem5199226 s) (@lem5199225 s)). Qed.
Lemma lem5199322 (s : real -> Prop) (h1 : term17 s) (h2 : term15 s) : term49 s.
Proof. exact (@lem5199321 s (@lem5199319 s h1 h2)). Qed.
Lemma lem5199323 (s : real -> Prop) (h1 : term49 s) : term49 s.
Proof. exact (h1). Qed.
Lemma lem5199324 (s : real -> Prop) (h1 : term50 s) : term50 s.
Proof. exact (h1). Qed.
Lemma lem5199326 (s : real -> Prop) (h1 : term50 s) : term50 s.
Proof. exact (h1). Qed.
Lemma lem5199327 (b : real) (s : real -> Prop) (h1 : term50 s) : term51 s b.
Proof. exact (@lem5199326 s h1 b). Qed.
Lemma lem5199328 (s : real -> Prop) (b : real) : (term51 s b) = (term52 s b).
Proof. exact (eq_refl (term51 s b)). Qed.
Lemma lem5199329 (b : real) (s : real -> Prop) (h1 : term50 s) : term52 s b.
Proof. exact (EQ_MP (@lem5199328 s b) (@lem5199327 b s h1)). Qed.
Lemma lem5199330 (s : real -> Prop) (b : real) (h1 : term53 s b) : term53 s b.
Proof. exact (h1). Qed.
Lemma lem5199331 (s : real -> Prop) (b : real) (h1 : term50 s) (h2 : term53 s b) : term47 s b.
Proof. exact (@lem5199329 b s h1 (@lem5199330 s b h2)). Qed.
Lemma lem5199332 (s : real -> Prop) (b : real) (h1 : term53 s b) : term54 s b.
Proof. exact (fun h0 : term50 s => @lem5199331 s b h0 h1). Qed.
Lemma lem5199333 (s : real -> Prop) (h1 : term50 s) : term50 s.
Proof. exact (h1). Qed.
Lemma lem5199334 (s : real -> Prop) (b : real) (h1 : term50 s) (h2 : term53 s b) : term47 s b.
Proof. exact (@lem5199332 s b h2 (@lem5199333 s h1)). Qed.
Lemma lem5199335 (b : real) (s : real -> Prop) (h1 : term50 s) : term52 s b.
Proof. exact (fun h0 : term53 s b => @lem5199334 s b h1 h0). Qed.
Lemma lem5199336 (s : real -> Prop) (h1 : term50 s) : term50 s.
Proof. exact (fun b : real => @lem5199335 b s h1). Qed.
Lemma lem5199337 (s : real -> Prop) : term55 s.
Proof. exact (fun h0 : term50 s => @lem5199336 s h0). Qed.
Lemma lem5199338 (s : real -> Prop) (h1 : term50 s) : term50 s.
Proof. exact (@lem5199337 s (@lem5199324 s h1)). Qed.
Lemma lem5199339 (b : real) (s : real -> Prop) (h1 : term50 s) : term51 s b.
Proof. exact (@lem5199338 s h1 b). Qed.
Lemma lem5199340 (s : real -> Prop) (b : real) : (term51 s b) = (term52 s b).
Proof. exact (eq_refl (term51 s b)). Qed.
Lemma lem5199343 (b : real) (s : real -> Prop) (h1 : term50 s) : term52 s b.
Proof. exact (EQ_MP (@lem5199340 s b) (@lem5199339 b s h1)). Qed.
Lemma lem5199344 (c : real) (s : real -> Prop) (h1 : term50 s) : term52 s c.
Proof. exact (@lem5199343 c s h1). Qed.
Lemma lem5199346 (p : Prop) : p = (term18 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5199347 (s : real -> Prop) (c : real) : (term53 s c) = (term56 s c).
Proof. exact (@lem5199346 (term53 s c)). Qed.
Lemma lem5199348 (s : real -> Prop) (c : real) : (term56 s c) = (term53 s c).
Proof. exact (SYM (@lem5199347 s c)). Qed.
Lemma lem5199349 (s : real -> Prop) (c : real) (h1 : term57 s c) : term57 s c.
Proof. exact (h1). Qed.
Lemma lem5199352 (s : real -> Prop) (c : real) (h1 : term58 s c) : term58 s c.
Proof. exact (h1). Qed.
Lemma lem5199353 (s : real -> Prop) (c : real) : term59 s c.
Proof. exact (fun h0 : term58 s c => @lem5199352 s c h0). Qed.
Lemma lem5199354 (s : real -> Prop) (c : real) (h1 : term59 s c) : term59 s c.
Proof. exact (h1). Qed.
Lemma lem5199355 (s : real -> Prop) (c : real) (h1 : term58 s c) : term58 s c.
Proof. exact (h1). Qed.
Lemma lem5199356 (s : real -> Prop) (c : real) (h1 : term58 s c) (h2 : term59 s c) : term58 s c.
Proof. exact (@lem5199354 s c h2 (@lem5199355 s c h1)). Qed.
Lemma lem5199357 (s : real -> Prop) (c : real) (h1 : term58 s c) : term60 s c.
Proof. exact (fun h0 : term59 s c => @lem5199356 s c h1 h0). Qed.
Lemma lem5199358 (s : real -> Prop) (c : real) (h1 : term59 s c) : term59 s c.
Proof. exact (h1). Qed.
Lemma lem5199359 (s : real -> Prop) (c : real) (h1 : term58 s c) (h2 : term59 s c) : term58 s c.
Proof. exact (@lem5199357 s c h1 (@lem5199358 s c h2)). Qed.
Lemma lem5199360 (s : real -> Prop) (c : real) (h1 : term59 s c) : term59 s c.
Proof. exact (fun h0 : term58 s c => @lem5199359 s c h0 h1). Qed.
Lemma lem5199361 (s : real -> Prop) (c : real) : term61 s c.
Proof. exact (fun h0 : term59 s c => @lem5199360 s c h0). Qed.
Lemma lem5199364 (s : real -> Prop) (c : real) : term59 s c.
Proof. exact (@lem5199361 s c (@lem5199353 s c)). Qed.
Lemma lem5199440 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5199441 (s : real -> Prop) (c : real) : (term56 s c) = (term62 s c).
Proof. exact (@lem5199440 (term57 s c)). Qed.
Lemma lem5199443 (t : Prop) : (term63 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5199444 (s : real -> Prop) (c : real) : (term62 s c) = (term53 s c).
Proof. exact (@lem5199443 (term53 s c)). Qed.
Lemma lem5199449 (s : real -> Prop) (c : real) : (term56 s c) = (term53 s c).
Proof. exact (TRANS (@lem5199441 s c) (@lem5199444 s c)). Qed.
Lemma lem5199452 (s : real -> Prop) (c : real) : (term64 s c) = (term64 s c).
Proof. exact (eq_refl (term64 s c)). Qed.
Lemma lem5199453 (s : real -> Prop) (c : real) : (term65 s c) = (term66 s c).
Proof. exact (MK_COMB (@lem5199452 s c) (@lem5199449 s c)). Qed.
Lemma lem5199456 (s : real -> Prop) : (term67 s) = (term67 s).
Proof. exact (eq_refl (term67 s)). Qed.
Lemma lem5199457 (s : real -> Prop) (c : real) : (term68 s c) = (term69 s c).
Proof. exact (MK_COMB (@lem5199456 s) (@lem5199453 s c)). Qed.
Lemma lem5199460 (s : real -> Prop) : (term70 s) = (term70 s).
Proof. exact (eq_refl (term70 s)). Qed.
Lemma lem5199461 (s : real -> Prop) (c : real) : (term58 s c) = (term71 s c).
Proof. exact (MK_COMB (@lem5199460 s) (@lem5199457 s c)). Qed.
Lemma lem5199464 (c : real) : (term72 c) = (term73 c).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5199461 s c)). Qed.
Lemma lem5199465 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5199466 (c : real) : (term74 c) = (term75 c).
Proof. exact (MK_COMB (@lem5199465) (@lem5199464 c)). Qed.
Lemma lem5199471 : term76 = term77.
Proof. exact (fun_ext (fun c : real => @lem5199466 c)). Qed.
Lemma lem5199472 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5199481 : term78 = term79.
Proof. exact (MK_COMB (@lem5199472) (@lem5199471)). Qed.
Lemma lem5199486 (s : real -> Prop) (x : real) (c : real) : (term80 s x c) = (term80 s x c).
Proof. exact (eq_refl (term80 s x c)). Qed.
Lemma lem5199487 (s : real -> Prop) (c : real) : (term81 s c) = (term81 s c).
Proof. exact (fun_ext (fun x : real => @lem5199486 s x c)). Qed.
Lemma lem5199488 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5199489 (s : real -> Prop) (c : real) : (term53 s c) = (term53 s c).
Proof. exact (MK_COMB (@lem5199488) (@lem5199487 s c)). Qed.
Lemma lem5199496 (s : real -> Prop) (x : real) (c : real) : (term42 s x c) = (term42 s x c).
Proof. exact (eq_refl (term42 s x c)). Qed.
Lemma lem5199497 (s : real -> Prop) (c : real) : (term43 s c) = (term43 s c).
Proof. exact (fun_ext (fun x : real => @lem5199496 s x c)). Qed.
Lemma lem5199498 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5199499 (s : real -> Prop) (c : real) : (term44 s c) = (term44 s c).
Proof. exact (MK_COMB (@lem5199498) (@lem5199497 s c)). Qed.
Lemma lem5199500 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5199501 (s : real -> Prop) (c : real) : (term64 s c) = (term64 s c).
Proof. exact (MK_COMB (@lem5199500) (@lem5199499 s c)). Qed.
Lemma lem5199502 (s : real -> Prop) (c : real) : (term66 s c) = (term66 s c).
Proof. exact (MK_COMB (@lem5199501 s c) (@lem5199489 s c)). Qed.
Lemma lem5199507 (s : real -> Prop) (x : real) (b : real) : (term80 s x b) = (term80 s x b).
Proof. exact (eq_refl (term80 s x b)). Qed.
Lemma lem5199508 (s : real -> Prop) (b : real) : (term81 s b) = (term81 s b).
Proof. exact (fun_ext (fun x : real => @lem5199507 s x b)). Qed.
Lemma lem5199509 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5199510 (s : real -> Prop) (b : real) : (term53 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5199509) (@lem5199508 s b)). Qed.
Lemma lem5199511 (s : real -> Prop) : (term82 s) = (term82 s).
Proof. exact (fun_ext (fun b : real => @lem5199510 s b)). Qed.
Lemma lem5199512 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5199513 (s : real -> Prop) : (term17 s) = (term17 s).
Proof. exact (MK_COMB (@lem5199512) (@lem5199511 s)). Qed.
Lemma lem5199514 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5199515 (s : real -> Prop) : (term67 s) = (term67 s).
Proof. exact (MK_COMB (@lem5199514) (@lem5199513 s)). Qed.
Lemma lem5199516 (s : real -> Prop) (c : real) : (term69 s c) = (term69 s c).
Proof. exact (MK_COMB (@lem5199515 s) (@lem5199502 s c)). Qed.
Lemma lem5199521 (s : real -> Prop) : (term70 s) = (term70 s).
Proof. exact (eq_refl (term70 s)). Qed.
Lemma lem5199522 (s : real -> Prop) (c : real) : (term71 s c) = (term71 s c).
Proof. exact (MK_COMB (@lem5199521 s) (@lem5199516 s c)). Qed.
Lemma lem5199523 (c : real) : (term73 c) = (term73 c).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5199522 s c)). Qed.
Lemma lem5199524 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5199525 (c : real) : (term75 c) = (term75 c).
Proof. exact (MK_COMB (@lem5199524) (@lem5199523 c)). Qed.
Lemma lem5199526 : term77 = term77.
Proof. exact (fun_ext (fun c : real => @lem5199525 c)). Qed.
Lemma lem5199527 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5199528 : term79 = term79.
Proof. exact (MK_COMB (@lem5199527) (@lem5199526)). Qed.
Lemma lem5199579 : term78 = term79.
Proof. exact (TRANS (@lem5199481) (@lem5199528)). Qed.
Lemma lem5199580 : term79 = term78.
Proof. exact (SYM (@lem5199579)). Qed.
Lemma lem5199582 (s : real -> Prop) (h1 : term17 s) : term17 s.
Proof. exact (h1). Qed.
Lemma lem5199583 (s : real -> Prop) (c : real) (h1 : term44 s c) : term44 s c.
Proof. exact (h1). Qed.
Lemma lem5199586 (p : Prop) : p = (term18 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5199587 (x : real) (c : real) : (real_le x c) = (term83 x c).
Proof. exact (@lem5199586 (real_le x c)). Qed.
Lemma lem5199588 (x : real) (c : real) : (term83 x c) = (real_le x c).
Proof. exact (SYM (@lem5199587 x c)). Qed.
Lemma lem5199589 (x : real) (c : real) (h1 : term84 x c) : term84 x c.
Proof. exact (h1). Qed.
Lemma lem5199602 (s : real -> Prop) (x : real) (b : real) : (term80 s x b) = (term42 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5199603 (s : real -> Prop) (b : real) : (term81 s b) = (term43 s b).
Proof. exact (fun_ext (fun x : real => @lem5199602 s x b)). Qed.
Lemma lem5199604 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5199605 (s : real -> Prop) (b : real) : (term53 s b) = (term44 s b).
Proof. exact (MK_COMB (@lem5199604) (@lem5199603 s b)). Qed.
Lemma lem5199606 (s : real -> Prop) : (term82 s) = (term85 s).
Proof. exact (fun_ext (fun b : real => @lem5199605 s b)). Qed.
Lemma lem5199607 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5199664 (s : real -> Prop) : (term17 s) = (term86 s).
Proof. exact (MK_COMB (@lem5199607) (@lem5199606 s)). Qed.
Lemma lem5199665 (s : real -> Prop) (h1 : term17 s) : term86 s.
Proof. exact (EQ_MP (@lem5199664 s) (@lem5199582 s h1)). Qed.
Lemma lem5199670 (s : real -> Prop) (x : real) (c : real) : (term42 s x c) = (term42 s x c).
Proof. exact (eq_refl (term42 s x c)). Qed.
Lemma lem5199671 (s : real -> Prop) (c : real) : (term43 s c) = (term43 s c).
Proof. exact (fun_ext (fun x : real => @lem5199670 s x c)). Qed.
Lemma lem5199672 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5199725 (s : real -> Prop) (c : real) : (term44 s c) = (term44 s c).
Proof. exact (MK_COMB (@lem5199672) (@lem5199671 s c)). Qed.
Lemma lem5199726 (s : real -> Prop) (c : real) (h1 : term44 s c) : term44 s c.
Proof. exact (EQ_MP (@lem5199725 s c) (@lem5199583 s c h1)). Qed.
Lemma lem5199732 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5199738 (x : real) (c : real) (h1 : term84 x c) : term84 x c.
Proof. exact (h1). Qed.
Lemma lem5199762 (s : real -> Prop) (x : real) (c : real) : (term42 s x c) = (term42 s x c).
Proof. exact (eq_refl (term42 s x c)). Qed.
Lemma lem5199763 (s : real -> Prop) (c : real) : (term43 s c) = (term43 s c).
Proof. exact (fun_ext (fun x : real => @lem5199762 s x c)). Qed.
Lemma lem5199764 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5199765 (s : real -> Prop) (c : real) : (term44 s c) = (term44 s c).
Proof. exact (MK_COMB (@lem5199764) (@lem5199763 s c)). Qed.
Lemma lem5199766 (s : real -> Prop) (c : real) (h1 : term44 s c) : term44 s c.
Proof. exact (EQ_MP (@lem5199765 s c) (@lem5199726 s c h1)). Qed.
Lemma lem5199772 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5199780 (x : real) (c : real) (h1 : term84 x c) : term84 x c.
Proof. exact (h1). Qed.
Lemma lem5199811 (s : real -> Prop) (x : real) (c : real) : (term42 s x c) = (term42 s x c).
Proof. exact (eq_refl (term42 s x c)). Qed.
Lemma lem5199812 (s : real -> Prop) (c : real) : (term43 s c) = (term43 s c).
Proof. exact (fun_ext (fun x : real => @lem5199811 s x c)). Qed.
Lemma lem5199813 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5199815 (s : real -> Prop) (c : real) : (term44 s c) = (term44 s c).
Proof. exact (MK_COMB (@lem5199813) (@lem5199812 s c)). Qed.
Lemma lem5199816 (s : real -> Prop) (c : real) (h1 : term44 s c) : term44 s c.
Proof. exact (EQ_MP (@lem5199815 s c) (@lem5199766 s c h1)). Qed.
Lemma lem5199820 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5199824 (x : real) (c : real) (h1 : term84 x c) : term84 x c.
Proof. exact (h1). Qed.
Lemma lem5199838 (_67860 : real) (s : real -> Prop) (c : real) (h1 : term44 s c) : term87 s c _67860.
Proof. exact (@lem5199816 s c h1 _67860). Qed.
Lemma lem5199839 (s : real -> Prop) (_67860 : real) (c : real) : (term87 s c _67860) = (term42 s _67860 c).
Proof. exact (eq_refl (term87 s c _67860)). Qed.
Lemma lem5199851 (_67860 : real) (s : real -> Prop) (c : real) (h1 : term44 s c) : term42 s _67860 c.
Proof. exact (EQ_MP (@lem5199839 s _67860 c) (@lem5199838 _67860 s c h1)). Qed.
Lemma lem5199853 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5199855 (x : real) (c : real) (h1 : term84 x c) : term84 x c.
Proof. exact (h1). Qed.
Lemma lem5199905 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5199906 (x : real) (s : real -> Prop) (h1 : @IN real x s) : term88 x s.
Proof. exact (fun h0 : term89 x s => @lem5199905 x s h1). Qed.
Lemma lem5199908 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5199909 (x : real) (s : real -> Prop) : (term88 x s) = (@IN real x s).
Proof. exact (@lem5199908 (@IN real x s)). Qed.
Lemma lem5199910 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (EQ_MP (@lem5199909 x s) (@lem5199906 x s h1)). Qed.
Lemma lem5199916 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5199917 (c : real) (_67860 : real) (s : real -> Prop) : (term42 s _67860 c) = (term91 c _67860 s).
Proof. exact (@lem5199916 (real_le _67860 c) (term89 _67860 s)). Qed.
Lemma lem5199923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5199924 (c : real) (_67860 : real) (s : real -> Prop) : (term92 s _67860 c) = (term93 c _67860 s).
Proof. exact (MK_COMB (@lem5199923) (@lem5199917 c _67860 s)). Qed.
Lemma lem5199930 (c : real) (_67860 : real) (s : real -> Prop) : (term91 c _67860 s) = (term91 c _67860 s).
Proof. exact (eq_refl (term91 c _67860 s)). Qed.
Lemma lem5199931 (c : real) (_67860 : real) (s : real -> Prop) : ((term42 s _67860 c) = (term91 c _67860 s)) = ((term91 c _67860 s) = (term91 c _67860 s)).
Proof. exact (MK_COMB (@lem5199924 c _67860 s) (@lem5199930 c _67860 s)). Qed.
Lemma lem5199933 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5199934 (x : Prop) : (x = x) = True.
Proof. exact (@lem5199933 Prop x). Qed.
Lemma lem5199935 (c : real) (_67860 : real) (s : real -> Prop) : ((term91 c _67860 s) = (term91 c _67860 s)) = True.
Proof. exact (@lem5199934 (term91 c _67860 s)). Qed.
Lemma lem5199936 (c : real) (_67860 : real) (s : real -> Prop) : ((term42 s _67860 c) = (term91 c _67860 s)) = True.
Proof. exact (TRANS (@lem5199931 c _67860 s) (@lem5199935 c _67860 s)). Qed.
Lemma lem5199937 (c : real) (_67860 : real) (s : real -> Prop) : True = ((term42 s _67860 c) = (term91 c _67860 s)).
Proof. exact (SYM (@lem5199936 c _67860 s)). Qed.
Lemma lem5199938 (c : real) (_67860 : real) (s : real -> Prop) : (term42 s _67860 c) = (term91 c _67860 s).
Proof. exact (EQ_MP (@lem5199937 c _67860 s) (@lem0)). Qed.
Lemma lem5199939 (_67860 : real) (s : real -> Prop) (c : real) (h1 : term44 s c) : term91 c _67860 s.
Proof. exact (EQ_MP (@lem5199938 c _67860 s) (@lem5199851 _67860 s c h1)). Qed.
Lemma lem5199941 (b : Prop) (a : Prop) : (a \/ b) = (term94 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5199942 (s : real -> Prop) (_67860 : real) (c : real) : (term91 c _67860 s) = (term95 s _67860 c).
Proof. exact (@lem5199941 (term89 _67860 s) (real_le _67860 c)). Qed.
Lemma lem5199944 (a : Prop) : (term63 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5199945 (_67860 : real) (s : real -> Prop) : (term96 _67860 s) = (@IN real _67860 s).
Proof. exact (@lem5199944 (@IN real _67860 s)). Qed.
Lemma lem5199946 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5199947 (_67860 : real) (s : real -> Prop) : (term97 _67860 s) = (term98 _67860 s).
Proof. exact (MK_COMB (@lem5199946) (@lem5199945 _67860 s)). Qed.
Lemma lem5199948 (_67860 : real) (c : real) : (real_le _67860 c) = (real_le _67860 c).
Proof. exact (eq_refl (real_le _67860 c)). Qed.
Lemma lem5199949 (s : real -> Prop) (_67860 : real) (c : real) : (term95 s _67860 c) = (term80 s _67860 c).
Proof. exact (MK_COMB (@lem5199947 _67860 s) (@lem5199948 _67860 c)). Qed.
Lemma lem5199950 (s : real -> Prop) (_67860 : real) (c : real) : (term91 c _67860 s) = (term80 s _67860 c).
Proof. exact (TRANS (@lem5199942 s _67860 c) (@lem5199949 s _67860 c)). Qed.
Lemma lem5199953 (_67860 : real) (s : real -> Prop) (c : real) (h1 : term44 s c) : term80 s _67860 c.
Proof. exact (EQ_MP (@lem5199950 s _67860 c) (@lem5199939 _67860 s c h1)). Qed.
Lemma lem5199954 (x : real) (s : real -> Prop) (c : real) (h1 : term44 s c) : term80 s x c.
Proof. exact (@lem5199953 x s c h1). Qed.
Lemma lem5199957 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : @IN real x s) : real_le x c.
Proof. exact (@lem5199954 x s c h1 (@lem5199910 x s h2)). Qed.
Lemma lem5199958 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : @IN real x s) : term99 x c.
Proof. exact (fun h0 : term84 x c => @lem5199957 c x s h1 h2). Qed.
Lemma lem5199960 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5199961 (x : real) (c : real) : (term99 x c) = (real_le x c).
Proof. exact (@lem5199960 (real_le x c)). Qed.
Lemma lem5199962 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : @IN real x s) : real_le x c.
Proof. exact (EQ_MP (@lem5199961 x c) (@lem5199958 c x s h1 h2)). Qed.
Lemma lem5199965 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5199967 (x : real) (c : real) : (term84 x c) = (term100 x c).
Proof. exact (@lem5199965 (real_le x c)). Qed.
Lemma lem5199970 (x : real) (c : real) (h1 : term84 x c) : term100 x c.
Proof. exact (EQ_MP (@lem5199967 x c) (@lem5199855 x c h1)). Qed.
Lemma lem5199973 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : False.
Proof. exact (@lem5199970 x c h2 (@lem5199962 c x s h1 h3)). Qed.
Lemma lem5199974 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : term101.
Proof. exact (fun h0 : ~ False => @lem5199973 c x s h1 h2 h3). Qed.
Lemma lem5199976 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5199977 : term101 = False.
Proof. exact (@lem5199976 False). Qed.
Lemma lem5199978 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5199977) (@lem5199974 c x s h1 h2 h3)). Qed.
Lemma lem5199979 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : (term84 x c) = False.
Proof. exact (prop_ext (fun h4 : term84 x c => @lem5199978 c x s h1 h2 h3) (fun h4 : False => @lem5199855 x c h2)). Qed.
Lemma lem5199980 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5199979 c x s h1 h2 h3) (@lem5199855 x c h2)). Qed.
Lemma lem5199981 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : (@IN real x s) = False.
Proof. exact (prop_ext (fun h4 : @IN real x s => @lem5199980 c x s h1 h2 h3) (fun h4 : False => @lem5199853 x s h3)). Qed.
Lemma lem5199982 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5199981 c x s h1 h2 h3) (@lem5199853 x s h3)). Qed.
Lemma lem5199983 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : (term84 x c) = False.
Proof. exact (prop_ext (fun h4 : term84 x c => @lem5199982 c x s h1 h2 h3) (fun h4 : False => @lem5199824 x c h2)). Qed.
Lemma lem5199984 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5199983 c x s h1 h2 h3) (@lem5199824 x c h2)). Qed.
Lemma lem5199985 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : (@IN real x s) = False.
Proof. exact (prop_ext (fun h4 : @IN real x s => @lem5199984 c x s h1 h2 h3) (fun h4 : False => @lem5199820 x s h3)). Qed.
Lemma lem5199986 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5199985 c x s h1 h2 h3) (@lem5199820 x s h3)). Qed.
Lemma lem5199987 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : (term84 x c) = False.
Proof. exact (prop_ext (fun h4 : term84 x c => @lem5199986 c x s h1 h2 h3) (fun h4 : False => @lem5199824 x c h2)). Qed.
Lemma lem5199988 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5199987 c x s h1 h2 h3) (@lem5199824 x c h2)). Qed.
Lemma lem5199989 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : (@IN real x s) = False.
Proof. exact (prop_ext (fun h4 : @IN real x s => @lem5199988 c x s h1 h2 h3) (fun h4 : False => @lem5199820 x s h3)). Qed.
Lemma lem5199990 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5199989 c x s h1 h2 h3) (@lem5199820 x s h3)). Qed.
Lemma lem5199991 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : (term44 s c) = False.
Proof. exact (prop_ext (fun h4 : term44 s c => @lem5199990 c x s h1 h2 h3) (fun h4 : False => @lem5199816 s c h1)). Qed.
Lemma lem5199992 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5199991 c x s h1 h2 h3) (@lem5199816 s c h1)). Qed.
Lemma lem5199993 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : (term84 x c) = False.
Proof. exact (prop_ext (fun h4 : term84 x c => @lem5199992 c x s h1 h2 h3) (fun h4 : False => @lem5199780 x c h2)). Qed.
Lemma lem5199994 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5199993 c x s h1 h2 h3) (@lem5199780 x c h2)). Qed.
Lemma lem5199995 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : (@IN real x s) = False.
Proof. exact (prop_ext (fun h4 : @IN real x s => @lem5199994 c x s h1 h2 h3) (fun h4 : False => @lem5199772 x s h3)). Qed.
Lemma lem5199996 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5199995 c x s h1 h2 h3) (@lem5199772 x s h3)). Qed.
Lemma lem5199997 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : (term44 s c) = False.
Proof. exact (prop_ext (fun h4 : term44 s c => @lem5199996 c x s h1 h2 h3) (fun h4 : False => @lem5199766 s c h1)). Qed.
Lemma lem5199998 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 x c) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5199997 c x s h1 h2 h3) (@lem5199766 s c h1)). Qed.
Lemma lem5199999 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 x c) (h4 : @IN real x s) : False.
Proof. exact (ex_elim (@lem5199665 s h2) (fun b : real => fun h0 : term85 s b => @lem5199998 c x s h1 h3 h4)). Qed.
Lemma lem5200000 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 x c) (h4 : @IN real x s) : (term84 x c) = False.
Proof. exact (prop_ext (fun h5 : term84 x c => @lem5199999 c x s h1 h2 h3 h4) (fun h5 : False => @lem5199738 x c h3)). Qed.
Lemma lem5200001 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 x c) (h4 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5200000 c x s h1 h2 h3 h4) (@lem5199738 x c h3)). Qed.
Lemma lem5200002 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 x c) (h4 : @IN real x s) : (@IN real x s) = False.
Proof. exact (prop_ext (fun h5 : @IN real x s => @lem5200001 c x s h1 h2 h3 h4) (fun h5 : False => @lem5199732 x s h4)). Qed.
Lemma lem5200003 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 x c) (h4 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5200002 c x s h1 h2 h3 h4) (@lem5199732 x s h4)). Qed.
Lemma lem5200004 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 x c) (h4 : @IN real x s) : (term44 s c) = False.
Proof. exact (prop_ext (fun h5 : term44 s c => @lem5200003 c x s h1 h2 h3 h4) (fun h5 : False => @lem5199726 s c h1)). Qed.
Lemma lem5200005 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 x c) (h4 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5200004 c x s h1 h2 h3 h4) (@lem5199726 s c h1)). Qed.
Lemma lem5200006 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 x c) (h4 : @IN real x s) : (term84 x c) = False.
Proof. exact (prop_ext (fun h5 : term84 x c => @lem5200005 c x s h1 h2 h3 h4) (fun h5 : False => @lem5199589 x c h3)). Qed.
Lemma lem5200007 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 x c) (h4 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5200006 c x s h1 h2 h3 h4) (@lem5199589 x c h3)). Qed.
Lemma lem5200008 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : @IN real x s) : term83 x c.
Proof. exact (fun h0 : term84 x c => @lem5200007 c x s h1 h2 h0 h3). Qed.
Lemma lem5200009 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : @IN real x s) : real_le x c.
Proof. exact (EQ_MP (@lem5199588 x c) (@lem5200008 c x s h1 h2 h3)). Qed.
Lemma lem5200010 (x : real) (c : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) : term80 s x c.
Proof. exact (fun h0 : @IN real x s => @lem5200009 c x s h1 h2 h0). Qed.
Lemma lem5200015 (c : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) : term53 s c.
Proof. exact (fun x : real => @lem5200010 x c s h1 h2). Qed.
Lemma lem5200016 (c : real) (s : real -> Prop) (h1 : term17 s) : term66 s c.
Proof. exact (fun h0 : term44 s c => @lem5200015 c s h0 h1). Qed.
Lemma lem5200017 (s : real -> Prop) (c : real) : term69 s c.
Proof. exact (fun h0 : term17 s => @lem5200016 c s h0). Qed.
Lemma lem5200018 (s : real -> Prop) (c : real) : term71 s c.
Proof. exact (fun h0 : term15 s => @lem5200017 s c). Qed.
Lemma lem5200023 (c : real) : term75 c.
Proof. exact (fun s : real -> Prop => @lem5200018 s c). Qed.
Lemma lem5200028 : term79.
Proof. exact (fun c : real => @lem5200023 c). Qed.
Lemma lem5200029 : term78.
Proof. exact (EQ_MP (@lem5199580) (@lem5200028)). Qed.
Lemma lem5200030 (c : real) : term102 c.
Proof. exact (@lem5200029 c). Qed.
Lemma lem5200031 (c : real) : (term102 c) = (term74 c).
Proof. exact (eq_refl (term102 c)). Qed.
Lemma lem5200032 (c : real) : term74 c.
Proof. exact (EQ_MP (@lem5200031 c) (@lem5200030 c)). Qed.
Lemma lem5200033 (c : real) (s : real -> Prop) : term103 c s.
Proof. exact (@lem5200032 c s). Qed.
Lemma lem5200034 (s : real -> Prop) (c : real) : (term103 c s) = (term58 s c).
Proof. exact (eq_refl (term103 c s)). Qed.
Lemma lem5200035 (s : real -> Prop) (c : real) : term58 s c.
Proof. exact (EQ_MP (@lem5200034 s c) (@lem5200033 c s)). Qed.
Lemma lem5200037 (s : real -> Prop) (c : real) : term58 s c.
Proof. exact (@lem5199364 s c (@lem5200035 s c)). Qed.
Lemma lem5200038 (c : real) (s : real -> Prop) (h1 : term15 s) : term68 s c.
Proof. exact (@lem5200037 s c (@lem5199257 s h1)). Qed.
Lemma lem5200039 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term15 s) : term65 s c.
Proof. exact (@lem5200038 c s h2 (@lem5199259 s h1)). Qed.
Lemma lem5200040 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) : term56 s c.
Proof. exact (@lem5200039 c s h1 h3 (@lem5199310 s c h2)). Qed.
Lemma lem5200041 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term57 s c) (h3 : term21 s c) (h4 : term15 s) : False.
Proof. exact (@lem5200040 c s h1 h3 h4 (@lem5199349 s c h2)). Qed.
Lemma lem5200042 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term57 s c) (h3 : term21 s c) (h4 : term15 s) : (term57 s c) = False.
Proof. exact (prop_ext (fun h5 : term57 s c => @lem5200041 c s h1 h2 h3 h4) (fun h5 : False => @lem5199349 s c h2)). Qed.
Lemma lem5200043 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term57 s c) (h3 : term21 s c) (h4 : term15 s) : False.
Proof. exact (EQ_MP (@lem5200042 c s h1 h2 h3 h4) (@lem5199349 s c h2)). Qed.
Lemma lem5200044 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) : term56 s c.
Proof. exact (fun h0 : term57 s c => @lem5200043 c s h1 h0 h2 h3). Qed.
Lemma lem5200045 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) : term53 s c.
Proof. exact (EQ_MP (@lem5199348 s c) (@lem5200044 c s h1 h2 h3)). Qed.
Lemma lem5200046 (c : real) (s : real -> Prop) (h1 : term50 s) (h2 : term17 s) (h3 : term21 s c) (h4 : term15 s) : term47 s c.
Proof. exact (@lem5199344 c s h1 (@lem5200045 c s h2 h3 h4)). Qed.
Lemma lem5200047 (s : real -> Prop) (h1 : term49 s) : term50 s.
Proof. exact (proj2 (@lem5199323 s h1)). Qed.
Lemma lem5200049 (c : real) (s : real -> Prop) (h1 : term50 s) (h2 : term17 s) (h3 : term21 s c) (h4 : term15 s) : (term50 s) = (term47 s c).
Proof. exact (prop_ext (fun h5 : term50 s => @lem5200046 c s h1 h2 h3 h4) (fun h5 : term47 s c => @lem5199324 s h1)). Qed.
Lemma lem5200050 (c : real) (s : real -> Prop) (h1 : term50 s) (h2 : term17 s) (h3 : term21 s c) (h4 : term15 s) : term47 s c.
Proof. exact (EQ_MP (@lem5200049 c s h1 h2 h3 h4) (@lem5199324 s h1)). Qed.
Lemma lem5200051 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) (h4 : term49 s) : (term50 s) = (term47 s c).
Proof. exact (prop_ext (fun h5 : term50 s => @lem5200050 c s h5 h1 h2 h3) (fun h5 : term47 s c => @lem5200047 s h4)). Qed.
Lemma lem5200052 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) (h4 : term49 s) : term47 s c.
Proof. exact (EQ_MP (@lem5200051 c s h1 h2 h3 h4) (@lem5200047 s h4)). Qed.
Lemma lem5200053 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) : term104 s c.
Proof. exact (fun h0 : term49 s => @lem5200052 c s h1 h2 h3 h0). Qed.
Lemma lem5200054 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) : term47 s c.
Proof. exact (@lem5200053 c s h1 h2 h3 (@lem5199322 s h1 h3)). Qed.
Lemma lem5200055 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) : term45 c s.
Proof. exact (EQ_MP (@lem5199318 c s) (@lem5200054 c s h1 h2 h3)). Qed.
Lemma lem5200056 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) (h4 : term16 c s) : False.
Proof. exact (@lem5200055 c s h1 h2 h3 (@lem5199258 c s h4)). Qed.
Lemma lem5200057 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term15 s) (h3 : term16 c s) : term20 s c.
Proof. exact (fun h0 : term21 s c => @lem5200056 c s h1 h0 h2 h3). Qed.
Lemma lem5200058 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term15 s) (h3 : term16 c s) : term19 s c.
Proof. exact (EQ_MP (@lem5199263 s c) (@lem5200057 c s h1 h2 h3)). Qed.
Lemma lem5200059 (c : real) (s : real -> Prop) (h1 : term13 c s) : term14 c s.
Proof. exact (proj2 (@lem5199255 c s h1)). Qed.
Lemma lem5200060 (c : real) (s : real -> Prop) (h1 : term13 c s) : term15 s.
Proof. exact (proj1 (@lem5199255 c s h1)). Qed.
Lemma lem5200061 (c : real) (s : real -> Prop) (h1 : term14 c s) : term16 c s.
Proof. exact (proj2 (@lem5199256 c s h1)). Qed.
Lemma lem5200062 (c : real) (s : real -> Prop) (h1 : term14 c s) : term17 s.
Proof. exact (proj1 (@lem5199256 c s h1)). Qed.
Lemma lem5200063 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term15 s) (h3 : term16 c s) : (term16 c s) = (term19 s c).
Proof. exact (prop_ext (fun h4 : term16 c s => @lem5200058 c s h1 h2 h3) (fun h4 : term19 s c => @lem5199258 c s h3)). Qed.
Lemma lem5200064 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term15 s) (h3 : term16 c s) : term19 s c.
Proof. exact (EQ_MP (@lem5200063 c s h1 h2 h3) (@lem5199258 c s h3)). Qed.
Lemma lem5200065 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term15 s) (h3 : term16 c s) : (term17 s) = (term19 s c).
Proof. exact (prop_ext (fun h4 : term17 s => @lem5200064 c s h1 h2 h3) (fun h4 : term19 s c => @lem5199259 s h1)). Qed.
Lemma lem5200066 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term15 s) (h3 : term16 c s) : term19 s c.
Proof. exact (EQ_MP (@lem5200065 c s h1 h2 h3) (@lem5199259 s h1)). Qed.
Lemma lem5200067 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term15 s) (h3 : term14 c s) : (term16 c s) = (term19 s c).
Proof. exact (prop_ext (fun h4 : term16 c s => @lem5200066 c s h1 h2 h4) (fun h4 : term19 s c => @lem5200061 c s h3)). Qed.
Lemma lem5200068 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term15 s) (h3 : term14 c s) : term19 s c.
Proof. exact (EQ_MP (@lem5200067 c s h1 h2 h3) (@lem5200061 c s h3)). Qed.
Lemma lem5200069 (c : real) (s : real -> Prop) (h1 : term15 s) (h2 : term14 c s) : (term17 s) = (term19 s c).
Proof. exact (prop_ext (fun h3 : term17 s => @lem5200068 c s h3 h1 h2) (fun h3 : term19 s c => @lem5200062 c s h2)). Qed.
Lemma lem5200070 (c : real) (s : real -> Prop) (h1 : term15 s) (h2 : term14 c s) : term19 s c.
Proof. exact (EQ_MP (@lem5200069 c s h1 h2) (@lem5200062 c s h2)). Qed.
Lemma lem5200071 (c : real) (s : real -> Prop) (h1 : term15 s) (h2 : term14 c s) : (term15 s) = (term19 s c).
Proof. exact (prop_ext (fun h3 : term15 s => @lem5200070 c s h1 h2) (fun h3 : term19 s c => @lem5199257 s h1)). Qed.
Lemma lem5200072 (c : real) (s : real -> Prop) (h1 : term15 s) (h2 : term14 c s) : term19 s c.
Proof. exact (EQ_MP (@lem5200071 c s h1 h2) (@lem5199257 s h1)). Qed.
Lemma lem5200073 (c : real) (s : real -> Prop) (h1 : term15 s) (h2 : term13 c s) : (term14 c s) = (term19 s c).
Proof. exact (prop_ext (fun h3 : term14 c s => @lem5200072 c s h1 h3) (fun h3 : term19 s c => @lem5200059 c s h2)). Qed.
Lemma lem5200074 (c : real) (s : real -> Prop) (h1 : term15 s) (h2 : term13 c s) : term19 s c.
Proof. exact (EQ_MP (@lem5200073 c s h1 h2) (@lem5200059 c s h2)). Qed.
Lemma lem5200075 (c : real) (s : real -> Prop) (h1 : term13 c s) : (term15 s) = (term19 s c).
Proof. exact (prop_ext (fun h2 : term15 s => @lem5200074 c s h2 h1) (fun h2 : term19 s c => @lem5200060 c s h1)). Qed.
Lemma lem5200076 (c : real) (s : real -> Prop) (h1 : term13 c s) : term19 s c.
Proof. exact (EQ_MP (@lem5200075 c s h1) (@lem5200060 c s h1)). Qed.
Lemma lem5200077 (s : real -> Prop) (c : real) : term105 s c.
Proof. exact (fun h0 : term13 c s => @lem5200076 c s h0). Qed.
Lemma lem5200083 (s : real -> Prop) : term106 s.
Proof. exact (fun c : real => @lem5200077 s c). Qed.
Lemma lem5200089 : term107.
Proof. exact (fun s : real -> Prop => @lem5200083 s). Qed.
