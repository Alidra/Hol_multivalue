Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUP_UNIQUE_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_LE_SUP_FINITE_spec.
Require Import REAL_SUP_LE_FINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339240_spec.
Require Import thm1339379_spec.
Require Import thm1339577_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
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
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem5171253 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5171254 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5171255 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5171254 t1) (@lem5171253 t1)). Qed.
Lemma lem5171256 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5171255 t1 t2). Qed.
Lemma lem5171257 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5171258 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5171257 t1 t2) (@lem5171256 t1 t2)). Qed.
Lemma lem5171259 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5171258 t1 t2 t3). Qed.
Lemma lem5171260 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5171261 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5171260 t1 t2 t3) (@lem5171259 t1 t2 t3)). Qed.
Lemma lem5171262 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5171261 t1 t2 t3)). Qed.
Lemma lem5171265 (x : real) (y : real) (h1 : (term7 y x) = (x = y)) : (term7 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem5171266 (x : real) (y : real) (h1 : (term7 y x) = (x = y)) : (x = y) = (term7 y x).
Proof. exact (SYM (@lem5171265 x y h1)). Qed.
Lemma lem5171267 (y : real) (x : real) (h1 : (x = y) = (term7 y x)) : (x = y) = (term7 y x).
Proof. exact (h1). Qed.
Lemma lem5171268 (y : real) (x : real) (h1 : (x = y) = (term7 y x)) : (term7 y x) = (x = y).
Proof. exact (SYM (@lem5171267 y x h1)). Qed.
Lemma lem5171269 (y : real) (x : real) : ((term7 y x) = (x = y)) = ((x = y) = (term7 y x)).
Proof. exact (prop_ext (fun h1 : (term7 y x) = (x = y) => @lem5171266 x y h1) (fun h1 : (x = y) = (term7 y x) => @lem5171268 y x h1)). Qed.
Lemma lem5171270 (x : real) : (term8 x) = (term9 x).
Proof. exact (fun_ext (fun y : real => @lem5171269 y x)). Qed.
Lemma lem5171271 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5171272 (x : real) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem5171271) (@lem5171270 x)). Qed.
Lemma lem5171273 : term12 = term13.
Proof. exact (fun_ext (fun x : real => @lem5171272 x)). Qed.
Lemma lem5171274 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5171275 : term14 = term15.
Proof. exact (MK_COMB (@lem5171274) (@lem5171273)). Qed.
Lemma lem5171276 : term15.
Proof. exact (EQ_MP (@lem5171275) (@lem1339379)). Qed.
Lemma lem5171304 (s : real -> Prop) : term16 s.
Proof. exact (@lem5149774 s). Qed.
Lemma lem5171305 (s : real -> Prop) : (term16 s) = (term17 s).
Proof. exact (eq_refl (term16 s)). Qed.
Lemma lem5171306 (s : real -> Prop) : term17 s.
Proof. exact (EQ_MP (@lem5171305 s) (@lem5171304 s)). Qed.
Lemma lem5171307 (s : real -> Prop) (a : real) : term18 s a.
Proof. exact (@lem5171306 s a). Qed.
Lemma lem5171308 (s : real -> Prop) (a : real) : (term18 s a) = (term19 s a).
Proof. exact (eq_refl (term18 s a)). Qed.
Lemma lem5171309 (s : real -> Prop) (a : real) : term19 s a.
Proof. exact (EQ_MP (@lem5171308 s a) (@lem5171307 s a)). Qed.
Lemma lem5171310 (s : real -> Prop) (h1 : term20 s) : term20 s.
Proof. exact (h1). Qed.
Lemma lem5171311 (a : real) (s : real -> Prop) (h1 : term20 s) : (term21 s a) = (term22 s a).
Proof. exact (@lem5171309 s a (@lem5171310 s h1)). Qed.
Lemma lem5171317 (s : real -> Prop) : term23 s.
Proof. exact (@lem5147521 s). Qed.
Lemma lem5171318 (s : real -> Prop) : (term23 s) = (term24 s).
Proof. exact (eq_refl (term23 s)). Qed.
Lemma lem5171319 (s : real -> Prop) : term24 s.
Proof. exact (EQ_MP (@lem5171318 s) (@lem5171317 s)). Qed.
Lemma lem5171320 (s : real -> Prop) (a : real) : term25 s a.
Proof. exact (@lem5171319 s a). Qed.
Lemma lem5171321 (s : real -> Prop) (a : real) : (term25 s a) = (term26 s a).
Proof. exact (eq_refl (term25 s a)). Qed.
Lemma lem5171322 (s : real -> Prop) (a : real) : term26 s a.
Proof. exact (EQ_MP (@lem5171321 s a) (@lem5171320 s a)). Qed.
Lemma lem5171323 (s : real -> Prop) (h1 : term20 s) : term20 s.
Proof. exact (h1). Qed.
Lemma lem5171324 (a : real) (s : real -> Prop) (h1 : term20 s) : (term27 a s) = (term28 s a).
Proof. exact (@lem5171322 s a (@lem5171323 s h1)). Qed.
Lemma lem5171330 (x : real) : term29 x.
Proof. exact (@lem5171276 x). Qed.
Lemma lem5171331 (x : real) : (term29 x) = (term11 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem5171332 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem5171331 x) (@lem5171330 x)). Qed.
Lemma lem5171333 (x : real) (y : real) : term30 x y.
Proof. exact (@lem5171332 x y). Qed.
Lemma lem5171334 (y : real) (x : real) : (term30 x y) = ((x = y) = (term7 y x)).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem5171343 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term31 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5171344 (p : Prop) (q : Prop) (p' : Prop) : term32 p q p'.
Proof. exact (fun q' : Prop => @lem5171343 p q p' q'). Qed.
Lemma lem5171345 (p : Prop) (q : Prop) : term33 p q.
Proof. exact (fun p' : Prop => @lem5171344 p q p'). Qed.
Lemma lem5171346 (s : real -> Prop) (a : real) : term34 s a.
Proof. exact (@lem5171345 (term20 s) (((sup s) = a) = (term35 s a))). Qed.
Lemma lem5171347 (s : real -> Prop) (a : real) (p' : Prop) : term36 s a p'.
Proof. exact (@lem5171346 s a p'). Qed.
Lemma lem5171348 (s : real -> Prop) (a : real) (p' : Prop) : (term36 s a p') = (term37 s a p').
Proof. exact (eq_refl (term36 s a p')). Qed.
Lemma lem5171349 (s : real -> Prop) (a : real) (p' : Prop) : term37 s a p'.
Proof. exact (EQ_MP (@lem5171348 s a p') (@lem5171347 s a p')). Qed.
Lemma lem5171350 (s : real -> Prop) (a : real) (p' : Prop) (q' : Prop) : term38 s a p' q'.
Proof. exact (@lem5171349 s a p' q'). Qed.
Lemma lem5171351 (s : real -> Prop) (a : real) (p' : Prop) (q' : Prop) : (term38 s a p' q') = (term39 s a p' q').
Proof. exact (eq_refl (term38 s a p' q')). Qed.
Lemma lem5171352 (s : real -> Prop) (a : real) (p' : Prop) (q' : Prop) : term39 s a p' q'.
Proof. exact (EQ_MP (@lem5171351 s a p' q') (@lem5171350 s a p' q')). Qed.
Lemma lem5171359 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5171360 (a : real) (s : real -> Prop) (q' : Prop) : term40 a s q'.
Proof. exact (@lem5171352 s a (term20 s) q'). Qed.
Lemma lem5171361 (a : real) (s : real -> Prop) (q' : Prop) : term41 a s q'.
Proof. exact (@lem5171360 a s q' (@lem5171359 s)). Qed.
Lemma lem5171362 (s : real -> Prop) (h1 : term20 s) : term20 s.
Proof. exact (h1). Qed.
Lemma lem5171363 (s : real -> Prop) (h1 : term20 s) : term42 s.
Proof. exact (proj2 (@lem5171362 s h1)). Qed.
Lemma lem5171364 (s : real -> Prop) : term43 s.
Proof. exact (@lem82 (s = (@EMPTY real))). Qed.
Lemma lem5171377 (s : real -> Prop) (h1 : term20 s) : @FINITE real s.
Proof. exact (proj1 (@lem5171362 s h1)). Qed.
Lemma lem5171378 (s : real -> Prop) : (@FINITE real s) = ((@FINITE real s) = True).
Proof. exact (@lem7 (@FINITE real s)). Qed.
Lemma lem5171387 (y : real) (x : real) : (x = y) = (term7 y x).
Proof. exact (EQ_MP (@lem5171334 y x) (@lem5171333 x y)). Qed.
Lemma lem5171388 (a : real) (s : real -> Prop) : ((sup s) = a) = (term44 a s).
Proof. exact (@lem5171387 a (sup s)). Qed.
Lemma lem5171392 (s : real -> Prop) (a : real) : term19 s a.
Proof. exact (fun h0 : term20 s => @lem5171311 a s h0). Qed.
Lemma lem5171396 (s : real -> Prop) (h1 : term20 s) : (@FINITE real s) = True.
Proof. exact (EQ_MP (@lem5171378 s) (@lem5171377 s h1)). Qed.
Lemma lem5171397 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5171398 (s : real -> Prop) (h1 : term20 s) : (term45 s) = (and True).
Proof. exact (MK_COMB (@lem5171397) (@lem5171396 s h1)). Qed.
Lemma lem5171400 (s : real -> Prop) (h1 : term20 s) : (s = (@EMPTY real)) = False.
Proof. exact (@lem5171364 s (@lem5171363 s h1)). Qed.
Lemma lem5171401 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5171402 (s : real -> Prop) (h1 : term20 s) : (term42 s) = (~ False).
Proof. exact (MK_COMB (@lem5171401) (@lem5171400 s h1)). Qed.
Lemma lem5171404 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5171405 (s : real -> Prop) (h1 : term20 s) : (term42 s) = True.
Proof. exact (TRANS (@lem5171402 s h1) (@lem5171404)). Qed.
Lemma lem5171406 (s : real -> Prop) (h1 : term20 s) : (term20 s) = (True /\ True).
Proof. exact (MK_COMB (@lem5171398 s h1) (@lem5171405 s h1)). Qed.
Lemma lem5171408 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5171409 : (True /\ True) = True.
Proof. exact (@lem5171408 True). Qed.
Lemma lem5171410 (s : real -> Prop) (h1 : term20 s) : (term20 s) = True.
Proof. exact (TRANS (@lem5171406 s h1) (@lem5171409)). Qed.
Lemma lem5171411 (s : real -> Prop) (h1 : term20 s) : True = (term20 s).
Proof. exact (SYM (@lem5171410 s h1)). Qed.
Lemma lem5171412 (s : real -> Prop) (h1 : term20 s) : term20 s.
Proof. exact (EQ_MP (@lem5171411 s h1) (@lem0)). Qed.
Lemma lem5171413 (a : real) (s : real -> Prop) (h1 : term20 s) : (term21 s a) = (term22 s a).
Proof. exact (@lem5171392 s a (@lem5171412 s h1)). Qed.
Lemma lem5171441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5171442 (a : real) (s : real -> Prop) (h1 : term20 s) : (term46 s a) = (term47 s a).
Proof. exact (MK_COMB (@lem5171441) (@lem5171413 a s h1)). Qed.
Lemma lem5171471 (s : real -> Prop) (a : real) : term26 s a.
Proof. exact (fun h0 : term20 s => @lem5171324 a s h0). Qed.
Lemma lem5171475 (s : real -> Prop) (h1 : term20 s) : (@FINITE real s) = True.
Proof. exact (EQ_MP (@lem5171378 s) (@lem5171377 s h1)). Qed.
Lemma lem5171476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5171477 (s : real -> Prop) (h1 : term20 s) : (term45 s) = (and True).
Proof. exact (MK_COMB (@lem5171476) (@lem5171475 s h1)). Qed.
Lemma lem5171479 (s : real -> Prop) (h1 : term20 s) : (s = (@EMPTY real)) = False.
Proof. exact (@lem5171364 s (@lem5171363 s h1)). Qed.
Lemma lem5171480 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5171481 (s : real -> Prop) (h1 : term20 s) : (term42 s) = (~ False).
Proof. exact (MK_COMB (@lem5171480) (@lem5171479 s h1)). Qed.
Lemma lem5171483 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5171484 (s : real -> Prop) (h1 : term20 s) : (term42 s) = True.
Proof. exact (TRANS (@lem5171481 s h1) (@lem5171483)). Qed.
Lemma lem5171485 (s : real -> Prop) (h1 : term20 s) : (term20 s) = (True /\ True).
Proof. exact (MK_COMB (@lem5171477 s h1) (@lem5171484 s h1)). Qed.
Lemma lem5171487 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5171488 : (True /\ True) = True.
Proof. exact (@lem5171487 True). Qed.
Lemma lem5171489 (s : real -> Prop) (h1 : term20 s) : (term20 s) = True.
Proof. exact (TRANS (@lem5171485 s h1) (@lem5171488)). Qed.
Lemma lem5171490 (s : real -> Prop) (h1 : term20 s) : True = (term20 s).
Proof. exact (SYM (@lem5171489 s h1)). Qed.
Lemma lem5171491 (s : real -> Prop) (h1 : term20 s) : term20 s.
Proof. exact (EQ_MP (@lem5171490 s h1) (@lem0)). Qed.
Lemma lem5171492 (a : real) (s : real -> Prop) (h1 : term20 s) : (term27 a s) = (term28 s a).
Proof. exact (@lem5171471 s a (@lem5171491 s h1)). Qed.
Lemma lem5171499 (a : real) (s : real -> Prop) (h1 : term20 s) : (term44 a s) = (term48 s a).
Proof. exact (MK_COMB (@lem5171442 a s h1) (@lem5171492 a s h1)). Qed.
Lemma lem5171535 (a : real) (s : real -> Prop) (h1 : term20 s) : ((sup s) = a) = (term48 s a).
Proof. exact (TRANS (@lem5171388 a s) (@lem5171499 a s h1)). Qed.
Lemma lem5171536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5171537 (a : real) (s : real -> Prop) (h1 : term20 s) : (term49 s a) = (term50 s a).
Proof. exact (MK_COMB (@lem5171536) (@lem5171535 a s h1)). Qed.
Lemma lem5171602 (s : real -> Prop) (a : real) : (term35 s a) = (term35 s a).
Proof. exact (eq_refl (term35 s a)). Qed.
Lemma lem5171603 (a : real) (s : real -> Prop) (h1 : term20 s) : (((sup s) = a) = (term35 s a)) = ((term48 s a) = (term35 s a)).
Proof. exact (MK_COMB (@lem5171537 a s h1) (@lem5171602 s a)). Qed.
Lemma lem5171672 (s : real -> Prop) (a : real) : term51 s a.
Proof. exact (fun h0 : term20 s => @lem5171603 a s h0). Qed.
Lemma lem5171673 (s : real -> Prop) (a : real) : term52 s a.
Proof. exact (@lem5171361 a s ((term48 s a) = (term35 s a))). Qed.
Lemma lem5171674 (s : real -> Prop) (a : real) : (term53 s a) = (term54 s a).
Proof. exact (@lem5171673 s a (@lem5171672 s a)). Qed.
Lemma lem5171861 (a : real) : (term55 a) = (term56 a).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5171674 s a)). Qed.
Lemma lem5172048 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5172049 (a : real) : (term57 a) = (term58 a).
Proof. exact (MK_COMB (@lem5172048) (@lem5171861 a)). Qed.
Lemma lem5172240 (a : real) : (term58 a) = (term57 a).
Proof. exact (SYM (@lem5172049 a)). Qed.
Lemma lem5172242 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5172243 (a : real) : (term58 a) = (term60 a).
Proof. exact (@lem5172242 (term58 a)). Qed.
Lemma lem5172244 (a : real) : (term60 a) = (term58 a).
Proof. exact (SYM (@lem5172243 a)). Qed.
Lemma lem5172245 (a : real) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem5172248 (a : real) (h1 : term62 a) : term62 a.
Proof. exact (h1). Qed.
Lemma lem5172249 (a : real) : term63 a.
Proof. exact (fun h0 : term62 a => @lem5172248 a h0). Qed.
Lemma lem5172250 (a : real) (h1 : term63 a) : term63 a.
Proof. exact (h1). Qed.
Lemma lem5172251 (a : real) (h1 : term62 a) : term62 a.
Proof. exact (h1). Qed.
Lemma lem5172252 (a : real) (h1 : term62 a) (h2 : term63 a) : term62 a.
Proof. exact (@lem5172250 a h2 (@lem5172251 a h1)). Qed.
Lemma lem5172253 (a : real) (h1 : term62 a) : term64 a.
Proof. exact (fun h0 : term63 a => @lem5172252 a h1 h0). Qed.
Lemma lem5172254 (a : real) (h1 : term63 a) : term63 a.
Proof. exact (h1). Qed.
Lemma lem5172255 (a : real) (h1 : term62 a) (h2 : term63 a) : term62 a.
Proof. exact (@lem5172253 a h1 (@lem5172254 a h2)). Qed.
Lemma lem5172256 (a : real) (h1 : term63 a) : term63 a.
Proof. exact (fun h0 : term62 a => @lem5172255 a h0 h1). Qed.
Lemma lem5172257 (a : real) : term65 a.
Proof. exact (fun h0 : term63 a => @lem5172256 a h0). Qed.
Lemma lem5172260 (a : real) : term63 a.
Proof. exact (@lem5172257 a (@lem5172249 a)). Qed.
Lemma lem5172372 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5172373 : term66 = term67.
Proof. exact (@lem5172372 term68). Qed.
Lemma lem5172378 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem5172379 : term70 = term71.
Proof. exact (MK_COMB (@lem5172378) (@lem5172373)). Qed.
Lemma lem5172382 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem5172383 : term73 = term74.
Proof. exact (MK_COMB (@lem5172382) (@lem5172379)). Qed.
Lemma lem5172386 (a : real) : (term75 a) = (term75 a).
Proof. exact (eq_refl (term75 a)). Qed.
Lemma lem5172387 (a : real) : (term62 a) = (term76 a).
Proof. exact (MK_COMB (@lem5172386 a) (@lem5172383)). Qed.
Lemma lem5172390 : term77 = term78.
Proof. exact (fun_ext (fun a : real => @lem5172387 a)). Qed.
Lemma lem5172391 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5172400 : term79 = term80.
Proof. exact (MK_COMB (@lem5172391) (@lem5172390)). Qed.
Lemma lem5172401 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5172402 : term81 = term81.
Proof. exact (fun_ext (fun x : real => @lem5172401 x)). Qed.
Lemma lem5172403 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5172404 : term68 = term68.
Proof. exact (MK_COMB (@lem5172403) (@lem5172402)). Qed.
Lemma lem5172405 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5172406 : term67 = term67.
Proof. exact (MK_COMB (@lem5172405) (@lem5172404)). Qed.
Lemma lem5172415 (y : real) (x : real) (z : real) : (term82 y x z) = (term82 y x z).
Proof. exact (eq_refl (term82 y x z)). Qed.
Lemma lem5172416 (y : real) (x : real) : (term83 y x) = (term83 y x).
Proof. exact (fun_ext (fun z : real => @lem5172415 y x z)). Qed.
Lemma lem5172417 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5172418 (y : real) (x : real) : (term84 y x) = (term84 y x).
Proof. exact (MK_COMB (@lem5172417) (@lem5172416 y x)). Qed.
Lemma lem5172419 (x : real) : (term85 x) = (term85 x).
Proof. exact (fun_ext (fun y : real => @lem5172418 y x)). Qed.
Lemma lem5172420 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5172421 (x : real) : (term86 x) = (term86 x).
Proof. exact (MK_COMB (@lem5172420) (@lem5172419 x)). Qed.
Lemma lem5172422 : term87 = term87.
Proof. exact (fun_ext (fun x : real => @lem5172421 x)). Qed.
Lemma lem5172423 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5172424 : term88 = term88.
Proof. exact (MK_COMB (@lem5172423) (@lem5172422)). Qed.
Lemma lem5172425 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5172426 : term69 = term69.
Proof. exact (MK_COMB (@lem5172425) (@lem5172424)). Qed.
Lemma lem5172427 : term71 = term71.
Proof. exact (MK_COMB (@lem5172426) (@lem5172406)). Qed.
Lemma lem5172436 (x : real) (y : real) : ((term7 y x) = (x = y)) = ((term7 y x) = (x = y)).
Proof. exact (eq_refl ((term7 y x) = (x = y))). Qed.
Lemma lem5172437 (x : real) : (term8 x) = (term8 x).
Proof. exact (fun_ext (fun y : real => @lem5172436 x y)). Qed.
Lemma lem5172438 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5172439 (x : real) : (term10 x) = (term10 x).
Proof. exact (MK_COMB (@lem5172438) (@lem5172437 x)). Qed.
Lemma lem5172440 : term12 = term12.
Proof. exact (fun_ext (fun x : real => @lem5172439 x)). Qed.
Lemma lem5172441 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5172442 : term14 = term14.
Proof. exact (MK_COMB (@lem5172441) (@lem5172440)). Qed.
Lemma lem5172443 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5172444 : term72 = term72.
Proof. exact (MK_COMB (@lem5172443) (@lem5172442)). Qed.
Lemma lem5172445 : term74 = term74.
Proof. exact (MK_COMB (@lem5172444) (@lem5172427)). Qed.
Lemma lem5172450 (s : real -> Prop) (y : real) (a : real) : (term89 s y a) = (term89 s y a).
Proof. exact (eq_refl (term89 s y a)). Qed.
Lemma lem5172451 (s : real -> Prop) (a : real) : (term90 s a) = (term90 s a).
Proof. exact (fun_ext (fun y : real => @lem5172450 s y a)). Qed.
Lemma lem5172452 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5172453 (s : real -> Prop) (a : real) : (term22 s a) = (term22 s a).
Proof. exact (MK_COMB (@lem5172452) (@lem5172451 s a)). Qed.
Lemma lem5172456 (a : real) (s : real -> Prop) : (term91 a s) = (term91 a s).
Proof. exact (eq_refl (term91 a s)). Qed.
Lemma lem5172457 (s : real -> Prop) (a : real) : (term35 s a) = (term35 s a).
Proof. exact (MK_COMB (@lem5172456 a s) (@lem5172453 s a)). Qed.
Lemma lem5172462 (s : real -> Prop) (a : real) (x : real) : (term92 s a x) = (term92 s a x).
Proof. exact (eq_refl (term92 s a x)). Qed.
Lemma lem5172463 (s : real -> Prop) (a : real) : (term93 s a) = (term93 s a).
Proof. exact (fun_ext (fun x : real => @lem5172462 s a x)). Qed.
Lemma lem5172464 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5172465 (s : real -> Prop) (a : real) : (term28 s a) = (term28 s a).
Proof. exact (MK_COMB (@lem5172464) (@lem5172463 s a)). Qed.
Lemma lem5172470 (s : real -> Prop) (x : real) (a : real) : (term89 s x a) = (term89 s x a).
Proof. exact (eq_refl (term89 s x a)). Qed.
Lemma lem5172471 (s : real -> Prop) (a : real) : (term90 s a) = (term90 s a).
Proof. exact (fun_ext (fun x : real => @lem5172470 s x a)). Qed.
Lemma lem5172472 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5172473 (s : real -> Prop) (a : real) : (term22 s a) = (term22 s a).
Proof. exact (MK_COMB (@lem5172472) (@lem5172471 s a)). Qed.
Lemma lem5172474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5172475 (s : real -> Prop) (a : real) : (term47 s a) = (term47 s a).
Proof. exact (MK_COMB (@lem5172474) (@lem5172473 s a)). Qed.
Lemma lem5172476 (s : real -> Prop) (a : real) : (term48 s a) = (term48 s a).
Proof. exact (MK_COMB (@lem5172475 s a) (@lem5172465 s a)). Qed.
Lemma lem5172477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5172478 (s : real -> Prop) (a : real) : (term50 s a) = (term50 s a).
Proof. exact (MK_COMB (@lem5172477) (@lem5172476 s a)). Qed.
Lemma lem5172479 (s : real -> Prop) (a : real) : ((term48 s a) = (term35 s a)) = ((term48 s a) = (term35 s a)).
Proof. exact (MK_COMB (@lem5172478 s a) (@lem5172457 s a)). Qed.
Lemma lem5172488 (s : real -> Prop) : (term94 s) = (term94 s).
Proof. exact (eq_refl (term94 s)). Qed.
Lemma lem5172489 (s : real -> Prop) (a : real) : (term54 s a) = (term54 s a).
Proof. exact (MK_COMB (@lem5172488 s) (@lem5172479 s a)). Qed.
Lemma lem5172490 (a : real) : (term56 a) = (term56 a).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5172489 s a)). Qed.
Lemma lem5172491 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5172492 (a : real) : (term58 a) = (term58 a).
Proof. exact (MK_COMB (@lem5172491) (@lem5172490 a)). Qed.
Lemma lem5172493 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5172494 (a : real) : (term61 a) = (term61 a).
Proof. exact (MK_COMB (@lem5172493) (@lem5172492 a)). Qed.
Lemma lem5172495 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5172496 (a : real) : (term75 a) = (term75 a).
Proof. exact (MK_COMB (@lem5172495) (@lem5172494 a)). Qed.
Lemma lem5172497 (a : real) : (term76 a) = (term76 a).
Proof. exact (MK_COMB (@lem5172496 a) (@lem5172445)). Qed.
Lemma lem5172498 : term78 = term78.
Proof. exact (fun_ext (fun a : real => @lem5172497 a)). Qed.
Lemma lem5172499 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5172500 : term80 = term80.
Proof. exact (MK_COMB (@lem5172499) (@lem5172498)). Qed.
Lemma lem5172595 : term79 = term80.
Proof. exact (TRANS (@lem5172400) (@lem5172500)). Qed.
Lemma lem5172596 : term80 = term79.
Proof. exact (SYM (@lem5172595)). Qed.
Lemma lem5172597 (a : real) (h1 : term61 a) : term61 a.
Proof. exact (h1). Qed.
Lemma lem5172598 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem5172600 (h1 : term68) : term68.
Proof. exact (h1). Qed.
Lemma lem5172614 (s : real -> Prop) (x : real) (a : real) : (term95 s x a) = (term96 s x a).
Proof. exact (@lem17362 (@IN real x s) (real_le x a)). Qed.
Lemma lem5172619 (s : real -> Prop) (x : real) (a : real) : (term89 s x a) = (term97 s x a).
Proof. exact (@lem17265 (@IN real x s) (real_le x a)). Qed.
Lemma lem5172620 (P : real -> Prop) : (term98 P) = (term99 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5172621 (s : real -> Prop) (a : real) : (term100 s a) = (term101 s a).
Proof. exact (@lem5172620 (term90 s a)). Qed.
Lemma lem5172622 (s : real -> Prop) (x : real) (a : real) : (term102 s a x) = (term89 s x a).
Proof. exact (eq_refl (term102 s a x)). Qed.
Lemma lem5172623 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5172624 (s : real -> Prop) (x : real) (a : real) : (term103 s a x) = (term95 s x a).
Proof. exact (MK_COMB (@lem5172623) (@lem5172622 s x a)). Qed.
Lemma lem5172625 (s : real -> Prop) (x : real) (a : real) : (term103 s a x) = (term96 s x a).
Proof. exact (TRANS (@lem5172624 s x a) (@lem5172614 s x a)). Qed.
Lemma lem5172626 (s : real -> Prop) (a : real) : (term104 s a) = (term105 s a).
Proof. exact (fun_ext (fun x : real => @lem5172625 s x a)). Qed.
Lemma lem5172627 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5172628 (s : real -> Prop) (a : real) : (term101 s a) = (term106 s a).
Proof. exact (MK_COMB (@lem5172627) (@lem5172626 s a)). Qed.
Lemma lem5172629 (s : real -> Prop) (a : real) : (term100 s a) = (term106 s a).
Proof. exact (TRANS (@lem5172621 s a) (@lem5172628 s a)). Qed.
Lemma lem5172630 (s : real -> Prop) (a : real) : (term90 s a) = (term107 s a).
Proof. exact (fun_ext (fun x : real => @lem5172619 s x a)). Qed.
Lemma lem5172631 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5172632 (s : real -> Prop) (a : real) : (term22 s a) = (term108 s a).
Proof. exact (MK_COMB (@lem5172631) (@lem5172630 s a)). Qed.
Lemma lem5172641 (s : real -> Prop) (a : real) (x : real) : (term109 s a x) = (term110 s a x).
Proof. exact (@lem17045 (@IN real x s) (real_le a x)). Qed.
Lemma lem5172644 (s : real -> Prop) (a : real) (x : real) : (term92 s a x) = (term92 s a x).
Proof. exact (eq_refl (term92 s a x)). Qed.
Lemma lem5172645 (P : real -> Prop) : (term111 P) = (term112 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5172646 (s : real -> Prop) (a : real) : (term113 s a) = (term114 s a).
Proof. exact (@lem5172645 (term93 s a)). Qed.
Lemma lem5172647 (s : real -> Prop) (a : real) (x : real) : (term115 s a x) = (term92 s a x).
Proof. exact (eq_refl (term115 s a x)). Qed.
Lemma lem5172648 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5172649 (s : real -> Prop) (a : real) (x : real) : (term116 s a x) = (term109 s a x).
Proof. exact (MK_COMB (@lem5172648) (@lem5172647 s a x)). Qed.
Lemma lem5172650 (s : real -> Prop) (a : real) (x : real) : (term116 s a x) = (term110 s a x).
Proof. exact (TRANS (@lem5172649 s a x) (@lem5172641 s a x)). Qed.
Lemma lem5172651 (s : real -> Prop) (a : real) : (term117 s a) = (term118 s a).
Proof. exact (fun_ext (fun x : real => @lem5172650 s a x)). Qed.
Lemma lem5172652 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5172653 (s : real -> Prop) (a : real) : (term114 s a) = (term119 s a).
Proof. exact (MK_COMB (@lem5172652) (@lem5172651 s a)). Qed.
Lemma lem5172654 (s : real -> Prop) (a : real) : (term113 s a) = (term119 s a).
Proof. exact (TRANS (@lem5172646 s a) (@lem5172653 s a)). Qed.
Lemma lem5172655 (s : real -> Prop) (a : real) : (term93 s a) = (term93 s a).
Proof. exact (fun_ext (fun x : real => @lem5172644 s a x)). Qed.
Lemma lem5172656 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5172657 (s : real -> Prop) (a : real) : (term28 s a) = (term28 s a).
Proof. exact (MK_COMB (@lem5172656) (@lem5172655 s a)). Qed.
Lemma lem5172658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5172659 (s : real -> Prop) (a : real) : (term120 s a) = (term121 s a).
Proof. exact (MK_COMB (@lem5172658) (@lem5172629 s a)). Qed.
Lemma lem5172660 (s : real -> Prop) (a : real) : (term122 s a) = (term123 s a).
Proof. exact (MK_COMB (@lem5172659 s a) (@lem5172654 s a)). Qed.
Lemma lem5172661 (s : real -> Prop) (a : real) : (term124 s a) = (term122 s a).
Proof. exact (@lem17045 (term22 s a) (term28 s a)). Qed.
Lemma lem5172662 (s : real -> Prop) (a : real) : (term124 s a) = (term123 s a).
Proof. exact (TRANS (@lem5172661 s a) (@lem5172660 s a)). Qed.
Lemma lem5172663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5172664 (s : real -> Prop) (a : real) : (term47 s a) = (term125 s a).
Proof. exact (MK_COMB (@lem5172663) (@lem5172632 s a)). Qed.
Lemma lem5172665 (s : real -> Prop) (a : real) : (term48 s a) = (term126 s a).
Proof. exact (MK_COMB (@lem5172664 s a) (@lem5172657 s a)). Qed.
Lemma lem5172676 (s : real -> Prop) (y : real) (a : real) : (term95 s y a) = (term96 s y a).
Proof. exact (@lem17362 (@IN real y s) (real_le y a)). Qed.
Lemma lem5172681 (s : real -> Prop) (y : real) (a : real) : (term89 s y a) = (term97 s y a).
Proof. exact (@lem17265 (@IN real y s) (real_le y a)). Qed.
Lemma lem5172682 (P : real -> Prop) : (term98 P) = (term99 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5172683 (s : real -> Prop) (a : real) : (term100 s a) = (term101 s a).
Proof. exact (@lem5172682 (term90 s a)). Qed.
Lemma lem5172684 (s : real -> Prop) (y : real) (a : real) : (term102 s a y) = (term89 s y a).
Proof. exact (eq_refl (term102 s a y)). Qed.
Lemma lem5172685 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5172686 (s : real -> Prop) (y : real) (a : real) : (term103 s a y) = (term95 s y a).
Proof. exact (MK_COMB (@lem5172685) (@lem5172684 s y a)). Qed.
Lemma lem5172687 (s : real -> Prop) (y : real) (a : real) : (term103 s a y) = (term96 s y a).
Proof. exact (TRANS (@lem5172686 s y a) (@lem5172676 s y a)). Qed.
Lemma lem5172688 (s : real -> Prop) (a : real) : (term104 s a) = (term105 s a).
Proof. exact (fun_ext (fun y : real => @lem5172687 s y a)). Qed.
Lemma lem5172689 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5172690 (s : real -> Prop) (a : real) : (term101 s a) = (term106 s a).
Proof. exact (MK_COMB (@lem5172689) (@lem5172688 s a)). Qed.
Lemma lem5172691 (s : real -> Prop) (a : real) : (term100 s a) = (term106 s a).
Proof. exact (TRANS (@lem5172683 s a) (@lem5172690 s a)). Qed.
Lemma lem5172692 (s : real -> Prop) (a : real) : (term90 s a) = (term107 s a).
Proof. exact (fun_ext (fun y : real => @lem5172681 s y a)). Qed.
Lemma lem5172693 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5172694 (s : real -> Prop) (a : real) : (term22 s a) = (term108 s a).
Proof. exact (MK_COMB (@lem5172693) (@lem5172692 s a)). Qed.
Lemma lem5172696 (a : real) (s : real -> Prop) : (term127 a s) = (term127 a s).
Proof. exact (eq_refl (term127 a s)). Qed.
Lemma lem5172697 (s : real -> Prop) (a : real) : (term128 s a) = (term129 s a).
Proof. exact (MK_COMB (@lem5172696 a s) (@lem5172691 s a)). Qed.
Lemma lem5172698 (s : real -> Prop) (a : real) : (term130 s a) = (term128 s a).
Proof. exact (@lem17045 (@IN real a s) (term22 s a)). Qed.
Lemma lem5172699 (s : real -> Prop) (a : real) : (term130 s a) = (term129 s a).
Proof. exact (TRANS (@lem5172698 s a) (@lem5172697 s a)). Qed.
Lemma lem5172701 (a : real) (s : real -> Prop) : (term91 a s) = (term91 a s).
Proof. exact (eq_refl (term91 a s)). Qed.
Lemma lem5172702 (s : real -> Prop) (a : real) : (term35 s a) = (term131 s a).
Proof. exact (MK_COMB (@lem5172701 a s) (@lem5172694 s a)). Qed.
Lemma lem5172703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5172704 (s : real -> Prop) (a : real) : (term132 s a) = (term133 s a).
Proof. exact (MK_COMB (@lem5172703) (@lem5172662 s a)). Qed.
Lemma lem5172705 (s : real -> Prop) (a : real) : (term134 s a) = (term135 s a).
Proof. exact (MK_COMB (@lem5172704 s a) (@lem5172702 s a)). Qed.
Lemma lem5172706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5172707 (s : real -> Prop) (a : real) : (term136 s a) = (term137 s a).
Proof. exact (MK_COMB (@lem5172706) (@lem5172665 s a)). Qed.
Lemma lem5172708 (s : real -> Prop) (a : real) : (term138 s a) = (term139 s a).
Proof. exact (MK_COMB (@lem5172707 s a) (@lem5172699 s a)). Qed.
Lemma lem5172709 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5172710 (s : real -> Prop) (a : real) : (term140 s a) = (term141 s a).
Proof. exact (MK_COMB (@lem5172709) (@lem5172708 s a)). Qed.
Lemma lem5172711 (s : real -> Prop) (a : real) : (term142 s a) = (term143 s a).
Proof. exact (MK_COMB (@lem5172710 s a) (@lem5172705 s a)). Qed.
Lemma lem5172712 (s : real -> Prop) (a : real) : (term144 s a) = (term142 s a).
Proof. exact (@lem17646 (term48 s a) (term35 s a)). Qed.
Lemma lem5172713 (s : real -> Prop) (a : real) : (term144 s a) = (term143 s a).
Proof. exact (TRANS (@lem5172712 s a) (@lem5172711 s a)). Qed.
Lemma lem5172715 (s : real -> Prop) : (term145 s) = (term145 s).
Proof. exact (eq_refl (term145 s)). Qed.
Lemma lem5172716 (s : real -> Prop) (a : real) : (term146 s a) = (term147 s a).
Proof. exact (MK_COMB (@lem5172715 s) (@lem5172713 s a)). Qed.
Lemma lem5172717 (s : real -> Prop) (a : real) : (term148 s a) = (term146 s a).
Proof. exact (@lem17362 (term20 s) ((term48 s a) = (term35 s a))). Qed.
Lemma lem5172718 (s : real -> Prop) (a : real) : (term148 s a) = (term147 s a).
Proof. exact (TRANS (@lem5172717 s a) (@lem5172716 s a)). Qed.
Lemma lem5172719 (P : type1022) : (term149 P) = (term150 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5172720 (a : real) : (term61 a) = (term151 a).
Proof. exact (@lem5172719 (term56 a)). Qed.
Lemma lem5172721 (s : real -> Prop) (a : real) : (term152 a s) = (term54 s a).
Proof. exact (eq_refl (term152 a s)). Qed.
Lemma lem5172722 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5172723 (s : real -> Prop) (a : real) : (term153 a s) = (term148 s a).
Proof. exact (MK_COMB (@lem5172722) (@lem5172721 s a)). Qed.
Lemma lem5172724 (s : real -> Prop) (a : real) : (term153 a s) = (term147 s a).
Proof. exact (TRANS (@lem5172723 s a) (@lem5172718 s a)). Qed.
Lemma lem5172725 (a : real) : (term154 a) = (term155 a).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5172724 s a)). Qed.
Lemma lem5172726 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5172727 (a : real) : (term151 a) = (term156 a).
Proof. exact (MK_COMB (@lem5172726) (@lem5172725 a)). Qed.
Lemma lem5172728 (a : real) : (term61 a) = (term156 a).
Proof. exact (TRANS (@lem5172720 a) (@lem5172727 a)). Qed.
Lemma lem5173067 {A : Type'} (P : Prop) (Q : A -> Prop) : (term157 A P Q) = (term158 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5173068 (P : Prop) (Q : real -> Prop) : (term159 P Q) = (term160 P Q).
Proof. exact (@lem5173067 real P Q). Qed.
Lemma lem5173069 (s : real -> Prop) (a : real) : (term161 s a) = (term162 s a).
Proof. exact (@lem5173068 (term108 s a) (term93 s a)). Qed.
Lemma lem5173070 (s : real -> Prop) (a : real) (x : real) : (term115 s a x) = (term92 s a x).
Proof. exact (eq_refl (term115 s a x)). Qed.
Lemma lem5173071 (s : real -> Prop) (a : real) : (term163 s a) = (term93 s a).
Proof. exact (fun_ext (fun x : real => @lem5173070 s a x)). Qed.
Lemma lem5173072 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173073 (s : real -> Prop) (a : real) : (term164 s a) = (term28 s a).
Proof. exact (MK_COMB (@lem5173072) (@lem5173071 s a)). Qed.
Lemma lem5173074 (s : real -> Prop) (a : real) : (term125 s a) = (term125 s a).
Proof. exact (eq_refl (term125 s a)). Qed.
Lemma lem5173075 (s : real -> Prop) (a : real) : (term161 s a) = (term126 s a).
Proof. exact (MK_COMB (@lem5173074 s a) (@lem5173073 s a)). Qed.
Lemma lem5173076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5173077 (s : real -> Prop) (a : real) : (term165 s a) = (term166 s a).
Proof. exact (MK_COMB (@lem5173076) (@lem5173075 s a)). Qed.
Lemma lem5173078 (s : real -> Prop) (a : real) (x : real) : (term115 s a x) = (term92 s a x).
Proof. exact (eq_refl (term115 s a x)). Qed.
Lemma lem5173079 (s : real -> Prop) (a : real) : (term125 s a) = (term125 s a).
Proof. exact (eq_refl (term125 s a)). Qed.
Lemma lem5173080 (s : real -> Prop) (a : real) (x : real) : (term167 s a x) = (term168 s a x).
Proof. exact (MK_COMB (@lem5173079 s a) (@lem5173078 s a x)). Qed.
Lemma lem5173081 (s : real -> Prop) (a : real) : (term169 s a) = (term170 s a).
Proof. exact (fun_ext (fun x : real => @lem5173080 s a x)). Qed.
Lemma lem5173082 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173083 (s : real -> Prop) (a : real) : (term162 s a) = (term171 s a).
Proof. exact (MK_COMB (@lem5173082) (@lem5173081 s a)). Qed.
Lemma lem5173084 (s : real -> Prop) (a : real) : ((term161 s a) = (term162 s a)) = ((term126 s a) = (term171 s a)).
Proof. exact (MK_COMB (@lem5173077 s a) (@lem5173083 s a)). Qed.
Lemma lem5173085 (s : real -> Prop) (a : real) : (term126 s a) = (term171 s a).
Proof. exact (EQ_MP (@lem5173084 s a) (@lem5173069 s a)). Qed.
Lemma lem5173086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5173087 (s : real -> Prop) (a : real) : (term137 s a) = (term172 s a).
Proof. exact (MK_COMB (@lem5173086) (@lem5173085 s a)). Qed.
Lemma lem5173089 {A : Type'} (P : Prop) (Q : A -> Prop) : (term173 A P Q) = (term174 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5173090 (P : Prop) (Q : real -> Prop) : (term175 P Q) = (term176 P Q).
Proof. exact (@lem5173089 real P Q). Qed.
Lemma lem5173091 (s : real -> Prop) (a : real) : (term177 s a) = (term178 s a).
Proof. exact (@lem5173090 (term179 a s) (term105 s a)). Qed.
Lemma lem5173092 (s : real -> Prop) (y : real) (a : real) : (term180 s a y) = (term96 s y a).
Proof. exact (eq_refl (term180 s a y)). Qed.
Lemma lem5173093 (s : real -> Prop) (a : real) : (term181 s a) = (term105 s a).
Proof. exact (fun_ext (fun y : real => @lem5173092 s y a)). Qed.
Lemma lem5173094 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173095 (s : real -> Prop) (a : real) : (term182 s a) = (term106 s a).
Proof. exact (MK_COMB (@lem5173094) (@lem5173093 s a)). Qed.
Lemma lem5173096 (a : real) (s : real -> Prop) : (term127 a s) = (term127 a s).
Proof. exact (eq_refl (term127 a s)). Qed.
Lemma lem5173097 (s : real -> Prop) (a : real) : (term177 s a) = (term129 s a).
Proof. exact (MK_COMB (@lem5173096 a s) (@lem5173095 s a)). Qed.
Lemma lem5173098 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5173099 (s : real -> Prop) (a : real) : (term183 s a) = (term184 s a).
Proof. exact (MK_COMB (@lem5173098) (@lem5173097 s a)). Qed.
Lemma lem5173100 (s : real -> Prop) (y : real) (a : real) : (term180 s a y) = (term96 s y a).
Proof. exact (eq_refl (term180 s a y)). Qed.
Lemma lem5173101 (a : real) (s : real -> Prop) : (term127 a s) = (term127 a s).
Proof. exact (eq_refl (term127 a s)). Qed.
Lemma lem5173102 (s : real -> Prop) (y : real) (a : real) : (term185 s a y) = (term186 s y a).
Proof. exact (MK_COMB (@lem5173101 a s) (@lem5173100 s y a)). Qed.
Lemma lem5173103 (s : real -> Prop) (a : real) : (term187 s a) = (term188 s a).
Proof. exact (fun_ext (fun y : real => @lem5173102 s y a)). Qed.
Lemma lem5173104 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173105 (s : real -> Prop) (a : real) : (term178 s a) = (term189 s a).
Proof. exact (MK_COMB (@lem5173104) (@lem5173103 s a)). Qed.
Lemma lem5173106 (s : real -> Prop) (a : real) : ((term177 s a) = (term178 s a)) = ((term129 s a) = (term189 s a)).
Proof. exact (MK_COMB (@lem5173099 s a) (@lem5173105 s a)). Qed.
Lemma lem5173107 (s : real -> Prop) (a : real) : (term129 s a) = (term189 s a).
Proof. exact (EQ_MP (@lem5173106 s a) (@lem5173091 s a)). Qed.
Lemma lem5173108 (s : real -> Prop) (a : real) : (term139 s a) = (term190 s a).
Proof. exact (MK_COMB (@lem5173087 s a) (@lem5173107 s a)). Qed.
Lemma lem5173110 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5173111 (P : real -> Prop) (Q : Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem5173110 real P Q). Qed.
Lemma lem5173112 (s : real -> Prop) (a : real) : (term195 s a) = (term196 s a).
Proof. exact (@lem5173111 (term170 s a) (term189 s a)). Qed.
Lemma lem5173113 (s : real -> Prop) (a : real) (x : real) : (term197 s a x) = (term168 s a x).
Proof. exact (eq_refl (term197 s a x)). Qed.
Lemma lem5173114 (s : real -> Prop) (a : real) : (term198 s a) = (term170 s a).
Proof. exact (fun_ext (fun x : real => @lem5173113 s a x)). Qed.
Lemma lem5173115 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173116 (s : real -> Prop) (a : real) : (term199 s a) = (term171 s a).
Proof. exact (MK_COMB (@lem5173115) (@lem5173114 s a)). Qed.
Lemma lem5173117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5173118 (s : real -> Prop) (a : real) : (term200 s a) = (term172 s a).
Proof. exact (MK_COMB (@lem5173117) (@lem5173116 s a)). Qed.
Lemma lem5173119 (s : real -> Prop) (a : real) : (term189 s a) = (term189 s a).
Proof. exact (eq_refl (term189 s a)). Qed.
Lemma lem5173120 (s : real -> Prop) (a : real) : (term195 s a) = (term190 s a).
Proof. exact (MK_COMB (@lem5173118 s a) (@lem5173119 s a)). Qed.
Lemma lem5173121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5173122 (s : real -> Prop) (a : real) : (term201 s a) = (term202 s a).
Proof. exact (MK_COMB (@lem5173121) (@lem5173120 s a)). Qed.
Lemma lem5173123 (s : real -> Prop) (a : real) (x : real) : (term197 s a x) = (term168 s a x).
Proof. exact (eq_refl (term197 s a x)). Qed.
Lemma lem5173124 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5173125 (s : real -> Prop) (a : real) (x : real) : (term203 s a x) = (term204 s a x).
Proof. exact (MK_COMB (@lem5173124) (@lem5173123 s a x)). Qed.
Lemma lem5173126 (s : real -> Prop) (a : real) : (term189 s a) = (term189 s a).
Proof. exact (eq_refl (term189 s a)). Qed.
Lemma lem5173127 (x : real) (s : real -> Prop) (a : real) : (term205 x s a) = (term206 x s a).
Proof. exact (MK_COMB (@lem5173125 s a x) (@lem5173126 s a)). Qed.
Lemma lem5173128 (s : real -> Prop) (a : real) : (term207 s a) = (term208 s a).
Proof. exact (fun_ext (fun x : real => @lem5173127 x s a)). Qed.
Lemma lem5173129 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173130 (s : real -> Prop) (a : real) : (term196 s a) = (term209 s a).
Proof. exact (MK_COMB (@lem5173129) (@lem5173128 s a)). Qed.
Lemma lem5173131 (s : real -> Prop) (a : real) : ((term195 s a) = (term196 s a)) = ((term190 s a) = (term209 s a)).
Proof. exact (MK_COMB (@lem5173122 s a) (@lem5173130 s a)). Qed.
Lemma lem5173132 (s : real -> Prop) (a : real) : (term190 s a) = (term209 s a).
Proof. exact (EQ_MP (@lem5173131 s a) (@lem5173112 s a)). Qed.
Lemma lem5173134 {A : Type'} (P : Prop) (Q : A -> Prop) : (term157 A P Q) = (term158 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5173135 (P : Prop) (Q : real -> Prop) : (term159 P Q) = (term160 P Q).
Proof. exact (@lem5173134 real P Q). Qed.
Lemma lem5173136 (x : real) (s : real -> Prop) (a : real) : (term210 x s a) = (term211 x s a).
Proof. exact (@lem5173135 (term168 s a x) (term188 s a)). Qed.
Lemma lem5173137 (s : real -> Prop) (y : real) (a : real) : (term212 s a y) = (term186 s y a).
Proof. exact (eq_refl (term212 s a y)). Qed.
Lemma lem5173138 (s : real -> Prop) (a : real) : (term213 s a) = (term188 s a).
Proof. exact (fun_ext (fun y : real => @lem5173137 s y a)). Qed.
Lemma lem5173139 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173140 (s : real -> Prop) (a : real) : (term214 s a) = (term189 s a).
Proof. exact (MK_COMB (@lem5173139) (@lem5173138 s a)). Qed.
Lemma lem5173141 (s : real -> Prop) (a : real) (x : real) : (term204 s a x) = (term204 s a x).
Proof. exact (eq_refl (term204 s a x)). Qed.
Lemma lem5173142 (x : real) (s : real -> Prop) (a : real) : (term210 x s a) = (term206 x s a).
Proof. exact (MK_COMB (@lem5173141 s a x) (@lem5173140 s a)). Qed.
Lemma lem5173143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5173144 (x : real) (s : real -> Prop) (a : real) : (term215 x s a) = (term216 x s a).
Proof. exact (MK_COMB (@lem5173143) (@lem5173142 x s a)). Qed.
Lemma lem5173145 (s : real -> Prop) (y : real) (a : real) : (term212 s a y) = (term186 s y a).
Proof. exact (eq_refl (term212 s a y)). Qed.
Lemma lem5173146 (s : real -> Prop) (a : real) (x : real) : (term204 s a x) = (term204 s a x).
Proof. exact (eq_refl (term204 s a x)). Qed.
Lemma lem5173147 (x : real) (s : real -> Prop) (y : real) (a : real) : (term217 x s a y) = (term218 x s y a).
Proof. exact (MK_COMB (@lem5173146 s a x) (@lem5173145 s y a)). Qed.
Lemma lem5173148 (x : real) (s : real -> Prop) (a : real) : (term219 x s a) = (term220 x s a).
Proof. exact (fun_ext (fun y : real => @lem5173147 x s y a)). Qed.
Lemma lem5173149 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173150 (x : real) (s : real -> Prop) (a : real) : (term211 x s a) = (term221 x s a).
Proof. exact (MK_COMB (@lem5173149) (@lem5173148 x s a)). Qed.
Lemma lem5173151 (x : real) (s : real -> Prop) (a : real) : ((term210 x s a) = (term211 x s a)) = ((term206 x s a) = (term221 x s a)).
Proof. exact (MK_COMB (@lem5173144 x s a) (@lem5173150 x s a)). Qed.
Lemma lem5173152 (x : real) (s : real -> Prop) (a : real) : (term206 x s a) = (term221 x s a).
Proof. exact (EQ_MP (@lem5173151 x s a) (@lem5173136 x s a)). Qed.
Lemma lem5173153 (s : real -> Prop) (a : real) : (term208 s a) = (term222 s a).
Proof. exact (fun_ext (fun x : real => @lem5173152 x s a)). Qed.
Lemma lem5173154 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173155 (s : real -> Prop) (a : real) : (term209 s a) = (term223 s a).
Proof. exact (MK_COMB (@lem5173154) (@lem5173153 s a)). Qed.
Lemma lem5173156 (s : real -> Prop) (a : real) : (term190 s a) = (term223 s a).
Proof. exact (TRANS (@lem5173132 s a) (@lem5173155 s a)). Qed.
Lemma lem5173157 (s : real -> Prop) (a : real) : (term139 s a) = (term223 s a).
Proof. exact (TRANS (@lem5173108 s a) (@lem5173156 s a)). Qed.
Lemma lem5173158 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5173159 (s : real -> Prop) (a : real) : (term141 s a) = (term224 s a).
Proof. exact (MK_COMB (@lem5173158) (@lem5173157 s a)). Qed.
Lemma lem5173161 {A : Type'} (P : A -> Prop) (Q : Prop) : (term225 A P Q) = (term226 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5173162 (P : real -> Prop) (Q : Prop) : (term227 P Q) = (term228 P Q).
Proof. exact (@lem5173161 real P Q). Qed.
Lemma lem5173163 (s : real -> Prop) (a : real) : (term229 s a) = (term230 s a).
Proof. exact (@lem5173162 (term105 s a) (term119 s a)). Qed.
Lemma lem5173164 (s : real -> Prop) (x : real) (a : real) : (term180 s a x) = (term96 s x a).
Proof. exact (eq_refl (term180 s a x)). Qed.
Lemma lem5173165 (s : real -> Prop) (a : real) : (term181 s a) = (term105 s a).
Proof. exact (fun_ext (fun x : real => @lem5173164 s x a)). Qed.
Lemma lem5173166 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173167 (s : real -> Prop) (a : real) : (term182 s a) = (term106 s a).
Proof. exact (MK_COMB (@lem5173166) (@lem5173165 s a)). Qed.
Lemma lem5173168 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5173169 (s : real -> Prop) (a : real) : (term231 s a) = (term121 s a).
Proof. exact (MK_COMB (@lem5173168) (@lem5173167 s a)). Qed.
Lemma lem5173170 (s : real -> Prop) (a : real) : (term119 s a) = (term119 s a).
Proof. exact (eq_refl (term119 s a)). Qed.
Lemma lem5173171 (s : real -> Prop) (a : real) : (term229 s a) = (term123 s a).
Proof. exact (MK_COMB (@lem5173169 s a) (@lem5173170 s a)). Qed.
Lemma lem5173172 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5173173 (s : real -> Prop) (a : real) : (term232 s a) = (term233 s a).
Proof. exact (MK_COMB (@lem5173172) (@lem5173171 s a)). Qed.
Lemma lem5173174 (s : real -> Prop) (x : real) (a : real) : (term180 s a x) = (term96 s x a).
Proof. exact (eq_refl (term180 s a x)). Qed.
Lemma lem5173175 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5173176 (s : real -> Prop) (x : real) (a : real) : (term234 s a x) = (term235 s x a).
Proof. exact (MK_COMB (@lem5173175) (@lem5173174 s x a)). Qed.
Lemma lem5173177 (s : real -> Prop) (a : real) : (term119 s a) = (term119 s a).
Proof. exact (eq_refl (term119 s a)). Qed.
Lemma lem5173178 (x : real) (s : real -> Prop) (a : real) : (term236 x s a) = (term237 x s a).
Proof. exact (MK_COMB (@lem5173176 s x a) (@lem5173177 s a)). Qed.
Lemma lem5173179 (s : real -> Prop) (a : real) : (term238 s a) = (term239 s a).
Proof. exact (fun_ext (fun x : real => @lem5173178 x s a)). Qed.
Lemma lem5173180 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173181 (s : real -> Prop) (a : real) : (term230 s a) = (term240 s a).
Proof. exact (MK_COMB (@lem5173180) (@lem5173179 s a)). Qed.
Lemma lem5173182 (s : real -> Prop) (a : real) : ((term229 s a) = (term230 s a)) = ((term123 s a) = (term240 s a)).
Proof. exact (MK_COMB (@lem5173173 s a) (@lem5173181 s a)). Qed.
Lemma lem5173183 (s : real -> Prop) (a : real) : (term123 s a) = (term240 s a).
Proof. exact (EQ_MP (@lem5173182 s a) (@lem5173163 s a)). Qed.
Lemma lem5173184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5173185 (s : real -> Prop) (a : real) : (term133 s a) = (term241 s a).
Proof. exact (MK_COMB (@lem5173184) (@lem5173183 s a)). Qed.
Lemma lem5173186 (s : real -> Prop) (a : real) : (term131 s a) = (term131 s a).
Proof. exact (eq_refl (term131 s a)). Qed.
Lemma lem5173187 (s : real -> Prop) (a : real) : (term135 s a) = (term242 s a).
Proof. exact (MK_COMB (@lem5173185 s a) (@lem5173186 s a)). Qed.
Lemma lem5173189 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5173190 (P : real -> Prop) (Q : Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem5173189 real P Q). Qed.
Lemma lem5173191 (s : real -> Prop) (a : real) : (term243 s a) = (term244 s a).
Proof. exact (@lem5173190 (term239 s a) (term131 s a)). Qed.
Lemma lem5173192 (x : real) (s : real -> Prop) (a : real) : (term245 s a x) = (term237 x s a).
Proof. exact (eq_refl (term245 s a x)). Qed.
Lemma lem5173193 (s : real -> Prop) (a : real) : (term246 s a) = (term239 s a).
Proof. exact (fun_ext (fun x : real => @lem5173192 x s a)). Qed.
Lemma lem5173194 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173195 (s : real -> Prop) (a : real) : (term247 s a) = (term240 s a).
Proof. exact (MK_COMB (@lem5173194) (@lem5173193 s a)). Qed.
Lemma lem5173196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5173197 (s : real -> Prop) (a : real) : (term248 s a) = (term241 s a).
Proof. exact (MK_COMB (@lem5173196) (@lem5173195 s a)). Qed.
Lemma lem5173198 (s : real -> Prop) (a : real) : (term131 s a) = (term131 s a).
Proof. exact (eq_refl (term131 s a)). Qed.
Lemma lem5173199 (s : real -> Prop) (a : real) : (term243 s a) = (term242 s a).
Proof. exact (MK_COMB (@lem5173197 s a) (@lem5173198 s a)). Qed.
Lemma lem5173200 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5173201 (s : real -> Prop) (a : real) : (term249 s a) = (term250 s a).
Proof. exact (MK_COMB (@lem5173200) (@lem5173199 s a)). Qed.
Lemma lem5173202 (x : real) (s : real -> Prop) (a : real) : (term245 s a x) = (term237 x s a).
Proof. exact (eq_refl (term245 s a x)). Qed.
Lemma lem5173203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5173204 (x : real) (s : real -> Prop) (a : real) : (term251 s a x) = (term252 x s a).
Proof. exact (MK_COMB (@lem5173203) (@lem5173202 x s a)). Qed.
Lemma lem5173205 (s : real -> Prop) (a : real) : (term131 s a) = (term131 s a).
Proof. exact (eq_refl (term131 s a)). Qed.
Lemma lem5173206 (x : real) (s : real -> Prop) (a : real) : (term253 x s a) = (term254 x s a).
Proof. exact (MK_COMB (@lem5173204 x s a) (@lem5173205 s a)). Qed.
Lemma lem5173207 (s : real -> Prop) (a : real) : (term255 s a) = (term256 s a).
Proof. exact (fun_ext (fun x : real => @lem5173206 x s a)). Qed.
Lemma lem5173208 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173209 (s : real -> Prop) (a : real) : (term244 s a) = (term257 s a).
Proof. exact (MK_COMB (@lem5173208) (@lem5173207 s a)). Qed.
Lemma lem5173210 (s : real -> Prop) (a : real) : ((term243 s a) = (term244 s a)) = ((term242 s a) = (term257 s a)).
Proof. exact (MK_COMB (@lem5173201 s a) (@lem5173209 s a)). Qed.
Lemma lem5173211 (s : real -> Prop) (a : real) : (term242 s a) = (term257 s a).
Proof. exact (EQ_MP (@lem5173210 s a) (@lem5173191 s a)). Qed.
Lemma lem5173212 (s : real -> Prop) (a : real) : (term135 s a) = (term257 s a).
Proof. exact (TRANS (@lem5173187 s a) (@lem5173211 s a)). Qed.
Lemma lem5173213 (s : real -> Prop) (a : real) : (term143 s a) = (term258 s a).
Proof. exact (MK_COMB (@lem5173159 s a) (@lem5173212 s a)). Qed.
Lemma lem5173215 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5173216 (P : real -> Prop) (Q : real -> Prop) : (term261 P Q) = (term262 P Q).
Proof. exact (@lem5173215 real P Q). Qed.
Lemma lem5173217 (s : real -> Prop) (a : real) : (term263 s a) = (term264 s a).
Proof. exact (@lem5173216 (term222 s a) (term256 s a)). Qed.
Lemma lem5173218 (x : real) (s : real -> Prop) (a : real) : (term265 s a x) = (term221 x s a).
Proof. exact (eq_refl (term265 s a x)). Qed.
Lemma lem5173219 (s : real -> Prop) (a : real) : (term266 s a) = (term222 s a).
Proof. exact (fun_ext (fun x : real => @lem5173218 x s a)). Qed.
Lemma lem5173220 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173221 (s : real -> Prop) (a : real) : (term267 s a) = (term223 s a).
Proof. exact (MK_COMB (@lem5173220) (@lem5173219 s a)). Qed.
Lemma lem5173222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5173223 (s : real -> Prop) (a : real) : (term268 s a) = (term224 s a).
Proof. exact (MK_COMB (@lem5173222) (@lem5173221 s a)). Qed.
Lemma lem5173224 (x : real) (s : real -> Prop) (a : real) : (term269 s a x) = (term254 x s a).
Proof. exact (eq_refl (term269 s a x)). Qed.
Lemma lem5173225 (s : real -> Prop) (a : real) : (term270 s a) = (term256 s a).
Proof. exact (fun_ext (fun x : real => @lem5173224 x s a)). Qed.
Lemma lem5173226 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173227 (s : real -> Prop) (a : real) : (term271 s a) = (term257 s a).
Proof. exact (MK_COMB (@lem5173226) (@lem5173225 s a)). Qed.
Lemma lem5173228 (s : real -> Prop) (a : real) : (term263 s a) = (term258 s a).
Proof. exact (MK_COMB (@lem5173223 s a) (@lem5173227 s a)). Qed.
Lemma lem5173229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5173230 (s : real -> Prop) (a : real) : (term272 s a) = (term273 s a).
Proof. exact (MK_COMB (@lem5173229) (@lem5173228 s a)). Qed.
Lemma lem5173231 (x : real) (s : real -> Prop) (a : real) : (term265 s a x) = (term221 x s a).
Proof. exact (eq_refl (term265 s a x)). Qed.
Lemma lem5173232 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5173233 (x : real) (s : real -> Prop) (a : real) : (term274 s a x) = (term275 x s a).
Proof. exact (MK_COMB (@lem5173232) (@lem5173231 x s a)). Qed.
Lemma lem5173234 (x : real) (s : real -> Prop) (a : real) : (term269 s a x) = (term254 x s a).
Proof. exact (eq_refl (term269 s a x)). Qed.
Lemma lem5173235 (x : real) (s : real -> Prop) (a : real) : (term276 s a x) = (term277 x s a).
Proof. exact (MK_COMB (@lem5173233 x s a) (@lem5173234 x s a)). Qed.
Lemma lem5173236 (s : real -> Prop) (a : real) : (term278 s a) = (term279 s a).
Proof. exact (fun_ext (fun x : real => @lem5173235 x s a)). Qed.
Lemma lem5173237 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173238 (s : real -> Prop) (a : real) : (term264 s a) = (term280 s a).
Proof. exact (MK_COMB (@lem5173237) (@lem5173236 s a)). Qed.
Lemma lem5173239 (s : real -> Prop) (a : real) : ((term263 s a) = (term264 s a)) = ((term258 s a) = (term280 s a)).
Proof. exact (MK_COMB (@lem5173230 s a) (@lem5173238 s a)). Qed.
Lemma lem5173240 (s : real -> Prop) (a : real) : (term258 s a) = (term280 s a).
Proof. exact (EQ_MP (@lem5173239 s a) (@lem5173217 s a)). Qed.
Lemma lem5173242 {A : Type'} (P : A -> Prop) (Q : Prop) : (term225 A P Q) = (term226 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5173243 (P : real -> Prop) (Q : Prop) : (term227 P Q) = (term228 P Q).
Proof. exact (@lem5173242 real P Q). Qed.
Lemma lem5173244 (x : real) (s : real -> Prop) (a : real) : (term281 x s a) = (term282 x s a).
Proof. exact (@lem5173243 (term220 x s a) (term254 x s a)). Qed.
Lemma lem5173245 (x : real) (s : real -> Prop) (y : real) (a : real) : (term283 x s a y) = (term218 x s y a).
Proof. exact (eq_refl (term283 x s a y)). Qed.
Lemma lem5173246 (x : real) (s : real -> Prop) (a : real) : (term284 x s a) = (term220 x s a).
Proof. exact (fun_ext (fun y : real => @lem5173245 x s y a)). Qed.
Lemma lem5173247 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173248 (x : real) (s : real -> Prop) (a : real) : (term285 x s a) = (term221 x s a).
Proof. exact (MK_COMB (@lem5173247) (@lem5173246 x s a)). Qed.
Lemma lem5173249 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5173250 (x : real) (s : real -> Prop) (a : real) : (term286 x s a) = (term275 x s a).
Proof. exact (MK_COMB (@lem5173249) (@lem5173248 x s a)). Qed.
Lemma lem5173251 (x : real) (s : real -> Prop) (a : real) : (term254 x s a) = (term254 x s a).
Proof. exact (eq_refl (term254 x s a)). Qed.
Lemma lem5173252 (x : real) (s : real -> Prop) (a : real) : (term281 x s a) = (term277 x s a).
Proof. exact (MK_COMB (@lem5173250 x s a) (@lem5173251 x s a)). Qed.
Lemma lem5173253 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5173254 (x : real) (s : real -> Prop) (a : real) : (term287 x s a) = (term288 x s a).
Proof. exact (MK_COMB (@lem5173253) (@lem5173252 x s a)). Qed.
Lemma lem5173255 (x : real) (s : real -> Prop) (y : real) (a : real) : (term283 x s a y) = (term218 x s y a).
Proof. exact (eq_refl (term283 x s a y)). Qed.
Lemma lem5173256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5173257 (x : real) (s : real -> Prop) (y : real) (a : real) : (term289 x s a y) = (term290 x s y a).
Proof. exact (MK_COMB (@lem5173256) (@lem5173255 x s y a)). Qed.
Lemma lem5173258 (x : real) (s : real -> Prop) (a : real) : (term254 x s a) = (term254 x s a).
Proof. exact (eq_refl (term254 x s a)). Qed.
Lemma lem5173259 (y : real) (x : real) (s : real -> Prop) (a : real) : (term291 y x s a) = (term292 y x s a).
Proof. exact (MK_COMB (@lem5173257 x s y a) (@lem5173258 x s a)). Qed.
Lemma lem5173260 (x : real) (s : real -> Prop) (a : real) : (term293 x s a) = (term294 x s a).
Proof. exact (fun_ext (fun y : real => @lem5173259 y x s a)). Qed.
Lemma lem5173261 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173262 (x : real) (s : real -> Prop) (a : real) : (term282 x s a) = (term295 x s a).
Proof. exact (MK_COMB (@lem5173261) (@lem5173260 x s a)). Qed.
Lemma lem5173263 (x : real) (s : real -> Prop) (a : real) : ((term281 x s a) = (term282 x s a)) = ((term277 x s a) = (term295 x s a)).
Proof. exact (MK_COMB (@lem5173254 x s a) (@lem5173262 x s a)). Qed.
Lemma lem5173264 (x : real) (s : real -> Prop) (a : real) : (term277 x s a) = (term295 x s a).
Proof. exact (EQ_MP (@lem5173263 x s a) (@lem5173244 x s a)). Qed.
Lemma lem5173265 (s : real -> Prop) (a : real) : (term279 s a) = (term296 s a).
Proof. exact (fun_ext (fun x : real => @lem5173264 x s a)). Qed.
Lemma lem5173266 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173267 (s : real -> Prop) (a : real) : (term280 s a) = (term297 s a).
Proof. exact (MK_COMB (@lem5173266) (@lem5173265 s a)). Qed.
Lemma lem5173268 (s : real -> Prop) (a : real) : (term258 s a) = (term297 s a).
Proof. exact (TRANS (@lem5173240 s a) (@lem5173267 s a)). Qed.
Lemma lem5173269 (s : real -> Prop) (a : real) : (term143 s a) = (term297 s a).
Proof. exact (TRANS (@lem5173213 s a) (@lem5173268 s a)). Qed.
Lemma lem5173270 (s : real -> Prop) : (term145 s) = (term145 s).
Proof. exact (eq_refl (term145 s)). Qed.
Lemma lem5173271 (s : real -> Prop) (a : real) : (term147 s a) = (term298 s a).
Proof. exact (MK_COMB (@lem5173270 s) (@lem5173269 s a)). Qed.
Lemma lem5173273 {A : Type'} (P : Prop) (Q : A -> Prop) : (term157 A P Q) = (term158 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5173274 (P : Prop) (Q : real -> Prop) : (term159 P Q) = (term160 P Q).
Proof. exact (@lem5173273 real P Q). Qed.
Lemma lem5173275 (s : real -> Prop) (a : real) : (term299 s a) = (term300 s a).
Proof. exact (@lem5173274 (term20 s) (term296 s a)). Qed.
Lemma lem5173276 (x : real) (s : real -> Prop) (a : real) : (term301 s a x) = (term295 x s a).
Proof. exact (eq_refl (term301 s a x)). Qed.
Lemma lem5173277 (s : real -> Prop) (a : real) : (term302 s a) = (term296 s a).
Proof. exact (fun_ext (fun x : real => @lem5173276 x s a)). Qed.
Lemma lem5173278 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173279 (s : real -> Prop) (a : real) : (term303 s a) = (term297 s a).
Proof. exact (MK_COMB (@lem5173278) (@lem5173277 s a)). Qed.
Lemma lem5173280 (s : real -> Prop) : (term145 s) = (term145 s).
Proof. exact (eq_refl (term145 s)). Qed.
Lemma lem5173281 (s : real -> Prop) (a : real) : (term299 s a) = (term298 s a).
Proof. exact (MK_COMB (@lem5173280 s) (@lem5173279 s a)). Qed.
Lemma lem5173282 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5173283 (s : real -> Prop) (a : real) : (term304 s a) = (term305 s a).
Proof. exact (MK_COMB (@lem5173282) (@lem5173281 s a)). Qed.
Lemma lem5173284 (x : real) (s : real -> Prop) (a : real) : (term301 s a x) = (term295 x s a).
Proof. exact (eq_refl (term301 s a x)). Qed.
Lemma lem5173285 (s : real -> Prop) : (term145 s) = (term145 s).
Proof. exact (eq_refl (term145 s)). Qed.
Lemma lem5173286 (x : real) (s : real -> Prop) (a : real) : (term306 s a x) = (term307 x s a).
Proof. exact (MK_COMB (@lem5173285 s) (@lem5173284 x s a)). Qed.
Lemma lem5173287 (s : real -> Prop) (a : real) : (term308 s a) = (term309 s a).
Proof. exact (fun_ext (fun x : real => @lem5173286 x s a)). Qed.
Lemma lem5173288 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173289 (s : real -> Prop) (a : real) : (term300 s a) = (term310 s a).
Proof. exact (MK_COMB (@lem5173288) (@lem5173287 s a)). Qed.
Lemma lem5173290 (s : real -> Prop) (a : real) : ((term299 s a) = (term300 s a)) = ((term298 s a) = (term310 s a)).
Proof. exact (MK_COMB (@lem5173283 s a) (@lem5173289 s a)). Qed.
Lemma lem5173291 (s : real -> Prop) (a : real) : (term298 s a) = (term310 s a).
Proof. exact (EQ_MP (@lem5173290 s a) (@lem5173275 s a)). Qed.
Lemma lem5173293 {A : Type'} (P : Prop) (Q : A -> Prop) : (term157 A P Q) = (term158 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5173294 (P : Prop) (Q : real -> Prop) : (term159 P Q) = (term160 P Q).
Proof. exact (@lem5173293 real P Q). Qed.
Lemma lem5173295 (x : real) (s : real -> Prop) (a : real) : (term311 x s a) = (term312 x s a).
Proof. exact (@lem5173294 (term20 s) (term294 x s a)). Qed.
Lemma lem5173296 (y : real) (x : real) (s : real -> Prop) (a : real) : (term313 x s a y) = (term292 y x s a).
Proof. exact (eq_refl (term313 x s a y)). Qed.
Lemma lem5173297 (x : real) (s : real -> Prop) (a : real) : (term314 x s a) = (term294 x s a).
Proof. exact (fun_ext (fun y : real => @lem5173296 y x s a)). Qed.
Lemma lem5173298 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173299 (x : real) (s : real -> Prop) (a : real) : (term315 x s a) = (term295 x s a).
Proof. exact (MK_COMB (@lem5173298) (@lem5173297 x s a)). Qed.
Lemma lem5173300 (s : real -> Prop) : (term145 s) = (term145 s).
Proof. exact (eq_refl (term145 s)). Qed.
Lemma lem5173301 (x : real) (s : real -> Prop) (a : real) : (term311 x s a) = (term307 x s a).
Proof. exact (MK_COMB (@lem5173300 s) (@lem5173299 x s a)). Qed.
Lemma lem5173302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5173303 (x : real) (s : real -> Prop) (a : real) : (term316 x s a) = (term317 x s a).
Proof. exact (MK_COMB (@lem5173302) (@lem5173301 x s a)). Qed.
Lemma lem5173304 (y : real) (x : real) (s : real -> Prop) (a : real) : (term313 x s a y) = (term292 y x s a).
Proof. exact (eq_refl (term313 x s a y)). Qed.
Lemma lem5173305 (s : real -> Prop) : (term145 s) = (term145 s).
Proof. exact (eq_refl (term145 s)). Qed.
Lemma lem5173306 (y : real) (x : real) (s : real -> Prop) (a : real) : (term318 x s a y) = (term319 y x s a).
Proof. exact (MK_COMB (@lem5173305 s) (@lem5173304 y x s a)). Qed.
Lemma lem5173307 (x : real) (s : real -> Prop) (a : real) : (term320 x s a) = (term321 x s a).
Proof. exact (fun_ext (fun y : real => @lem5173306 y x s a)). Qed.
Lemma lem5173308 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173309 (x : real) (s : real -> Prop) (a : real) : (term312 x s a) = (term322 x s a).
Proof. exact (MK_COMB (@lem5173308) (@lem5173307 x s a)). Qed.
Lemma lem5173310 (x : real) (s : real -> Prop) (a : real) : ((term311 x s a) = (term312 x s a)) = ((term307 x s a) = (term322 x s a)).
Proof. exact (MK_COMB (@lem5173303 x s a) (@lem5173309 x s a)). Qed.
Lemma lem5173311 (x : real) (s : real -> Prop) (a : real) : (term307 x s a) = (term322 x s a).
Proof. exact (EQ_MP (@lem5173310 x s a) (@lem5173295 x s a)). Qed.
Lemma lem5173312 (s : real -> Prop) (a : real) : (term309 s a) = (term323 s a).
Proof. exact (fun_ext (fun x : real => @lem5173311 x s a)). Qed.
Lemma lem5173313 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5173314 (s : real -> Prop) (a : real) : (term310 s a) = (term324 s a).
Proof. exact (MK_COMB (@lem5173313) (@lem5173312 s a)). Qed.
Lemma lem5173315 (s : real -> Prop) (a : real) : (term298 s a) = (term324 s a).
Proof. exact (TRANS (@lem5173291 s a) (@lem5173314 s a)). Qed.
Lemma lem5173316 (s : real -> Prop) (a : real) : (term147 s a) = (term324 s a).
Proof. exact (TRANS (@lem5173271 s a) (@lem5173315 s a)). Qed.
Lemma lem5173317 (a : real) : (term155 a) = (term325 a).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5173316 s a)). Qed.
Lemma lem5173318 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5173320 (a : real) : (term156 a) = (term326 a).
Proof. exact (MK_COMB (@lem5173318) (@lem5173317 a)). Qed.
Lemma lem5173321 (a : real) : (term61 a) = (term326 a).
Proof. exact (TRANS (@lem5172728 a) (@lem5173320 a)). Qed.
Lemma lem5173322 (a : real) (h1 : term61 a) : term326 a.
Proof. exact (EQ_MP (@lem5173321 a) (@lem5172597 a h1)). Qed.
Lemma lem5173331 (y : real) (x : real) : (term327 y x) = (term328 y x).
Proof. exact (@lem17045 (real_le x y) (real_le y x)). Qed.
Lemma lem5173336 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5173337 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5173338 (y : real) (x : real) : (term329 y x) = (term330 y x).
Proof. exact (MK_COMB (@lem5173337) (@lem5173331 y x)). Qed.
Lemma lem5173339 (x : real) (y : real) : (term331 x y) = (term332 x y).
Proof. exact (MK_COMB (@lem5173338 y x) (@lem5173336 x y)). Qed.
Lemma lem5173344 (x : real) (y : real) : (term333 x y) = (term333 x y).
Proof. exact (eq_refl (term333 x y)). Qed.
Lemma lem5173345 (x : real) (y : real) : (term334 x y) = (term335 x y).
Proof. exact (MK_COMB (@lem5173344 x y) (@lem5173339 x y)). Qed.
Lemma lem5173346 (x : real) (y : real) : ((term7 y x) = (x = y)) = (term334 x y).
Proof. exact (@lem17784 (term7 y x) (x = y)). Qed.
Lemma lem5173347 (x : real) (y : real) : ((term7 y x) = (x = y)) = (term335 x y).
Proof. exact (TRANS (@lem5173346 x y) (@lem5173345 x y)). Qed.
Lemma lem5173348 (x : real) : (term8 x) = (term336 x).
Proof. exact (fun_ext (fun y : real => @lem5173347 x y)). Qed.
Lemma lem5173349 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173350 (x : real) : (term10 x) = (term337 x).
Proof. exact (MK_COMB (@lem5173349) (@lem5173348 x)). Qed.
Lemma lem5173351 : term12 = term338.
Proof. exact (fun_ext (fun x : real => @lem5173350 x)). Qed.
Lemma lem5173352 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173353 : term14 = term339.
Proof. exact (MK_COMB (@lem5173352) (@lem5173351)). Qed.
Lemma lem5173359 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term340 A P Q) = (term341 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5173360 (P : real -> Prop) (Q : real -> Prop) : (term342 P Q) = (term343 P Q).
Proof. exact (@lem5173359 real P Q). Qed.
Lemma lem5173361 (x : real) : (term344 x) = (term345 x).
Proof. exact (@lem5173360 (term346 x) (term347 x)). Qed.
Lemma lem5173362 (x : real) (y : real) : (term348 x y) = (term349 x y).
Proof. exact (eq_refl (term348 x y)). Qed.
Lemma lem5173363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5173364 (x : real) (y : real) : (term350 x y) = (term333 x y).
Proof. exact (MK_COMB (@lem5173363) (@lem5173362 x y)). Qed.
Lemma lem5173365 (x : real) (y : real) : (term351 x y) = (term332 x y).
Proof. exact (eq_refl (term351 x y)). Qed.
Lemma lem5173366 (x : real) (y : real) : (term352 x y) = (term335 x y).
Proof. exact (MK_COMB (@lem5173364 x y) (@lem5173365 x y)). Qed.
Lemma lem5173367 (x : real) : (term353 x) = (term336 x).
Proof. exact (fun_ext (fun y : real => @lem5173366 x y)). Qed.
Lemma lem5173368 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173369 (x : real) : (term344 x) = (term337 x).
Proof. exact (MK_COMB (@lem5173368) (@lem5173367 x)). Qed.
Lemma lem5173370 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5173371 (x : real) : (term354 x) = (term355 x).
Proof. exact (MK_COMB (@lem5173370) (@lem5173369 x)). Qed.
Lemma lem5173372 (x : real) (y : real) : (term348 x y) = (term349 x y).
Proof. exact (eq_refl (term348 x y)). Qed.
Lemma lem5173373 (x : real) : (term356 x) = (term346 x).
Proof. exact (fun_ext (fun y : real => @lem5173372 x y)). Qed.
Lemma lem5173374 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173375 (x : real) : (term357 x) = (term358 x).
Proof. exact (MK_COMB (@lem5173374) (@lem5173373 x)). Qed.
Lemma lem5173376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5173377 (x : real) : (term359 x) = (term360 x).
Proof. exact (MK_COMB (@lem5173376) (@lem5173375 x)). Qed.
Lemma lem5173378 (x : real) (y : real) : (term351 x y) = (term332 x y).
Proof. exact (eq_refl (term351 x y)). Qed.
Lemma lem5173379 (x : real) : (term361 x) = (term347 x).
Proof. exact (fun_ext (fun y : real => @lem5173378 x y)). Qed.
Lemma lem5173380 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173381 (x : real) : (term362 x) = (term363 x).
Proof. exact (MK_COMB (@lem5173380) (@lem5173379 x)). Qed.
Lemma lem5173382 (x : real) : (term345 x) = (term364 x).
Proof. exact (MK_COMB (@lem5173377 x) (@lem5173381 x)). Qed.
Lemma lem5173383 (x : real) : ((term344 x) = (term345 x)) = ((term337 x) = (term364 x)).
Proof. exact (MK_COMB (@lem5173371 x) (@lem5173382 x)). Qed.
Lemma lem5173384 (x : real) : (term337 x) = (term364 x).
Proof. exact (EQ_MP (@lem5173383 x) (@lem5173361 x)). Qed.
Lemma lem5173481 : term338 = term365.
Proof. exact (fun_ext (fun x : real => @lem5173384 x)). Qed.
Lemma lem5173482 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173483 : term339 = term366.
Proof. exact (MK_COMB (@lem5173482) (@lem5173481)). Qed.
Lemma lem5173485 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term340 A P Q) = (term341 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5173486 (P : real -> Prop) (Q : real -> Prop) : (term342 P Q) = (term343 P Q).
Proof. exact (@lem5173485 real P Q). Qed.
Lemma lem5173487 : term367 = term368.
Proof. exact (@lem5173486 term369 term370). Qed.
Lemma lem5173488 (x : real) : (term371 x) = (term358 x).
Proof. exact (eq_refl (term371 x)). Qed.
Lemma lem5173489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5173490 (x : real) : (term372 x) = (term360 x).
Proof. exact (MK_COMB (@lem5173489) (@lem5173488 x)). Qed.
Lemma lem5173491 (x : real) : (term373 x) = (term363 x).
Proof. exact (eq_refl (term373 x)). Qed.
Lemma lem5173492 (x : real) : (term374 x) = (term364 x).
Proof. exact (MK_COMB (@lem5173490 x) (@lem5173491 x)). Qed.
Lemma lem5173493 : term375 = term365.
Proof. exact (fun_ext (fun x : real => @lem5173492 x)). Qed.
Lemma lem5173494 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173495 : term367 = term366.
Proof. exact (MK_COMB (@lem5173494) (@lem5173493)). Qed.
Lemma lem5173496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5173497 : term376 = term377.
Proof. exact (MK_COMB (@lem5173496) (@lem5173495)). Qed.
Lemma lem5173498 (x : real) : (term371 x) = (term358 x).
Proof. exact (eq_refl (term371 x)). Qed.
Lemma lem5173499 : term378 = term369.
Proof. exact (fun_ext (fun x : real => @lem5173498 x)). Qed.
Lemma lem5173500 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173501 : term379 = term380.
Proof. exact (MK_COMB (@lem5173500) (@lem5173499)). Qed.
Lemma lem5173502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5173503 : term381 = term382.
Proof. exact (MK_COMB (@lem5173502) (@lem5173501)). Qed.
Lemma lem5173504 (x : real) : (term373 x) = (term363 x).
Proof. exact (eq_refl (term373 x)). Qed.
Lemma lem5173505 : term383 = term370.
Proof. exact (fun_ext (fun x : real => @lem5173504 x)). Qed.
Lemma lem5173506 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173507 : term384 = term385.
Proof. exact (MK_COMB (@lem5173506) (@lem5173505)). Qed.
Lemma lem5173508 : term368 = term386.
Proof. exact (MK_COMB (@lem5173503) (@lem5173507)). Qed.
Lemma lem5173509 : (term367 = term368) = (term366 = term386).
Proof. exact (MK_COMB (@lem5173497) (@lem5173508)). Qed.
Lemma lem5173510 : term366 = term386.
Proof. exact (EQ_MP (@lem5173509) (@lem5173487)). Qed.
Lemma lem5173617 : term339 = term386.
Proof. exact (TRANS (@lem5173483) (@lem5173510)). Qed.
Lemma lem5173618 : term14 = term386.
Proof. exact (TRANS (@lem5173353) (@lem5173617)). Qed.
Lemma lem5173619 (h1 : term14) : term386.
Proof. exact (EQ_MP (@lem5173618) (@lem5172598 h1)). Qed.
Lemma lem5173703 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5173704 : term81 = term81.
Proof. exact (fun_ext (fun x : real => @lem5173703 x)). Qed.
Lemma lem5173705 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173714 : term68 = term68.
Proof. exact (MK_COMB (@lem5173705) (@lem5173704)). Qed.
Lemma lem5173715 (h1 : term68) : term68.
Proof. exact (EQ_MP (@lem5173714) (@lem5172600 h1)). Qed.
Lemma lem5173716 (s : real -> Prop) (a : real) (h1 : term324 s a) : term324 s a.
Proof. exact (h1). Qed.
Lemma lem5173717 (x : real) (s : real -> Prop) (a : real) (h1 : term322 x s a) : term322 x s a.
Proof. exact (h1). Qed.
Lemma lem5173718 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term319 y x s a) : term319 y x s a.
Proof. exact (h1). Qed.
Lemma lem5173743 (x : real) (y : real) : (term332 x y) = (term332 x y).
Proof. exact (eq_refl (term332 x y)). Qed.
Lemma lem5173744 (x : real) : (term347 x) = (term347 x).
Proof. exact (fun_ext (fun y : real => @lem5173743 x y)). Qed.
Lemma lem5173745 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173746 (x : real) : (term363 x) = (term363 x).
Proof. exact (MK_COMB (@lem5173745) (@lem5173744 x)). Qed.
Lemma lem5173747 : term370 = term370.
Proof. exact (fun_ext (fun x : real => @lem5173746 x)). Qed.
Lemma lem5173748 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173749 : term385 = term385.
Proof. exact (MK_COMB (@lem5173748) (@lem5173747)). Qed.
Lemma lem5173772 (x : real) (y : real) : (term349 x y) = (term349 x y).
Proof. exact (eq_refl (term349 x y)). Qed.
Lemma lem5173773 (x : real) : (term346 x) = (term346 x).
Proof. exact (fun_ext (fun y : real => @lem5173772 x y)). Qed.
Lemma lem5173774 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173775 (x : real) : (term358 x) = (term358 x).
Proof. exact (MK_COMB (@lem5173774) (@lem5173773 x)). Qed.
Lemma lem5173776 : term369 = term369.
Proof. exact (fun_ext (fun x : real => @lem5173775 x)). Qed.
Lemma lem5173777 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173778 : term380 = term380.
Proof. exact (MK_COMB (@lem5173777) (@lem5173776)). Qed.
Lemma lem5173779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5173780 : term382 = term382.
Proof. exact (MK_COMB (@lem5173779) (@lem5173778)). Qed.
Lemma lem5173781 : term386 = term386.
Proof. exact (MK_COMB (@lem5173780) (@lem5173749)). Qed.
Lemma lem5173782 (h1 : term14) : term386.
Proof. exact (EQ_MP (@lem5173781) (@lem5173619 h1)). Qed.
Lemma lem5173822 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5173823 : term81 = term81.
Proof. exact (fun_ext (fun x : real => @lem5173822 x)). Qed.
Lemma lem5173824 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173825 : term68 = term68.
Proof. exact (MK_COMB (@lem5173824) (@lem5173823)). Qed.
Lemma lem5173826 (h1 : term68) : term68.
Proof. exact (EQ_MP (@lem5173825) (@lem5173715 h1)). Qed.
Lemma lem5173841 (s : real -> Prop) (y : real) (a : real) : (term97 s y a) = (term97 s y a).
Proof. exact (eq_refl (term97 s y a)). Qed.
Lemma lem5173842 (s : real -> Prop) (a : real) : (term107 s a) = (term107 s a).
Proof. exact (fun_ext (fun y : real => @lem5173841 s y a)). Qed.
Lemma lem5173843 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173844 (s : real -> Prop) (a : real) : (term108 s a) = (term108 s a).
Proof. exact (MK_COMB (@lem5173843) (@lem5173842 s a)). Qed.
Lemma lem5173851 (a : real) (s : real -> Prop) : (term91 a s) = (term91 a s).
Proof. exact (eq_refl (term91 a s)). Qed.
Lemma lem5173852 (s : real -> Prop) (a : real) : (term131 s a) = (term131 s a).
Proof. exact (MK_COMB (@lem5173851 a s) (@lem5173844 s a)). Qed.
Lemma lem5173869 (s : real -> Prop) (a : real) (x : real) : (term110 s a x) = (term110 s a x).
Proof. exact (eq_refl (term110 s a x)). Qed.
Lemma lem5173870 (s : real -> Prop) (a : real) : (term118 s a) = (term118 s a).
Proof. exact (fun_ext (fun x : real => @lem5173869 s a x)). Qed.
Lemma lem5173871 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173872 (s : real -> Prop) (a : real) : (term119 s a) = (term119 s a).
Proof. exact (MK_COMB (@lem5173871) (@lem5173870 s a)). Qed.
Lemma lem5173889 (s : real -> Prop) (x : real) (a : real) : (term235 s x a) = (term235 s x a).
Proof. exact (eq_refl (term235 s x a)). Qed.
Lemma lem5173890 (x : real) (s : real -> Prop) (a : real) : (term237 x s a) = (term237 x s a).
Proof. exact (MK_COMB (@lem5173889 s x a) (@lem5173872 s a)). Qed.
Lemma lem5173891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5173892 (x : real) (s : real -> Prop) (a : real) : (term252 x s a) = (term252 x s a).
Proof. exact (MK_COMB (@lem5173891) (@lem5173890 x s a)). Qed.
Lemma lem5173893 (x : real) (s : real -> Prop) (a : real) : (term254 x s a) = (term254 x s a).
Proof. exact (MK_COMB (@lem5173892 x s a) (@lem5173852 s a)). Qed.
Lemma lem5173918 (s : real -> Prop) (y : real) (a : real) : (term186 s y a) = (term186 s y a).
Proof. exact (eq_refl (term186 s y a)). Qed.
Lemma lem5173931 (s : real -> Prop) (a : real) (x : real) : (term92 s a x) = (term92 s a x).
Proof. exact (eq_refl (term92 s a x)). Qed.
Lemma lem5173946 (s : real -> Prop) (x : real) (a : real) : (term97 s x a) = (term97 s x a).
Proof. exact (eq_refl (term97 s x a)). Qed.
Lemma lem5173947 (s : real -> Prop) (a : real) : (term107 s a) = (term107 s a).
Proof. exact (fun_ext (fun x : real => @lem5173946 s x a)). Qed.
Lemma lem5173948 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5173949 (s : real -> Prop) (a : real) : (term108 s a) = (term108 s a).
Proof. exact (MK_COMB (@lem5173948) (@lem5173947 s a)). Qed.
Lemma lem5173950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5173951 (s : real -> Prop) (a : real) : (term125 s a) = (term125 s a).
Proof. exact (MK_COMB (@lem5173950) (@lem5173949 s a)). Qed.
Lemma lem5173952 (s : real -> Prop) (a : real) (x : real) : (term168 s a x) = (term168 s a x).
Proof. exact (MK_COMB (@lem5173951 s a) (@lem5173931 s a x)). Qed.
Lemma lem5173953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5173954 (s : real -> Prop) (a : real) (x : real) : (term204 s a x) = (term204 s a x).
Proof. exact (MK_COMB (@lem5173953) (@lem5173952 s a x)). Qed.
Lemma lem5173955 (x : real) (s : real -> Prop) (y : real) (a : real) : (term218 x s y a) = (term218 x s y a).
Proof. exact (MK_COMB (@lem5173954 s a x) (@lem5173918 s y a)). Qed.
Lemma lem5173956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5173957 (x : real) (s : real -> Prop) (y : real) (a : real) : (term290 x s y a) = (term290 x s y a).
Proof. exact (MK_COMB (@lem5173956) (@lem5173955 x s y a)). Qed.
Lemma lem5173958 (y : real) (x : real) (s : real -> Prop) (a : real) : (term292 y x s a) = (term292 y x s a).
Proof. exact (MK_COMB (@lem5173957 x s y a) (@lem5173893 x s a)). Qed.
Lemma lem5173973 (s : real -> Prop) : (term145 s) = (term145 s).
Proof. exact (eq_refl (term145 s)). Qed.
Lemma lem5173974 (y : real) (x : real) (s : real -> Prop) (a : real) : (term319 y x s a) = (term319 y x s a).
Proof. exact (MK_COMB (@lem5173973 s) (@lem5173958 y x s a)). Qed.
Lemma lem5173975 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term319 y x s a) : term319 y x s a.
Proof. exact (EQ_MP (@lem5173974 y x s a) (@lem5173718 y x s a h1)). Qed.
Lemma lem5173976 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term319 y x s a) : term292 y x s a.
Proof. exact (proj2 (@lem5173975 y x s a h1)). Qed.
Lemma lem5173980 (h1 : term14) : term385.
Proof. exact (proj2 (@lem5173782 h1)). Qed.
Lemma lem5173982 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term218 x s y a.
Proof. exact (h1). Qed.
Lemma lem5173983 (x : real) (s : real -> Prop) (a : real) (h1 : term254 x s a) : term254 x s a.
Proof. exact (h1). Qed.
Lemma lem5173984 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term186 s y a.
Proof. exact (proj2 (@lem5173982 x s y a h1)). Qed.
Lemma lem5173985 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term168 s a x.
Proof. exact (proj1 (@lem5173982 x s y a h1)). Qed.
Lemma lem5173986 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term92 s a x.
Proof. exact (proj2 (@lem5173985 x s y a h1)). Qed.
Lemma lem5173987 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term108 s a.
Proof. exact (proj1 (@lem5173985 x s y a h1)). Qed.
Lemma lem5173991 (s : real -> Prop) (y : real) (a : real) (h1 : term96 s y a) : term96 s y a.
Proof. exact (h1). Qed.
Lemma lem5173994 (x : real) (s : real -> Prop) (a : real) (h1 : term254 x s a) : term131 s a.
Proof. exact (proj2 (@lem5173983 x s a h1)). Qed.
Lemma lem5173995 (x : real) (s : real -> Prop) (a : real) (h1 : term254 x s a) : term237 x s a.
Proof. exact (proj1 (@lem5173983 x s a h1)). Qed.
Lemma lem5173996 (x : real) (s : real -> Prop) (a : real) (h1 : term254 x s a) : term108 s a.
Proof. exact (proj2 (@lem5173994 x s a h1)). Qed.
Lemma lem5173998 (s : real -> Prop) (x : real) (a : real) (h1 : term96 s x a) : term96 s x a.
Proof. exact (h1). Qed.
Lemma lem5173999 (s : real -> Prop) (a : real) (h1 : term119 s a) : term119 s a.
Proof. exact (h1). Qed.
Lemma lem5174081 (x : real) (y : real) : (term332 x y) = (term332 x y).
Proof. exact (eq_refl (term332 x y)). Qed.
Lemma lem5174082 (x : real) : (term347 x) = (term347 x).
Proof. exact (fun_ext (fun y : real => @lem5174081 x y)). Qed.
Lemma lem5174083 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5174084 (x : real) : (term363 x) = (term363 x).
Proof. exact (MK_COMB (@lem5174083) (@lem5174082 x)). Qed.
Lemma lem5174085 : term370 = term370.
Proof. exact (fun_ext (fun x : real => @lem5174084 x)). Qed.
Lemma lem5174086 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5174088 : term385 = term385.
Proof. exact (MK_COMB (@lem5174086) (@lem5174085)). Qed.
Lemma lem5174089 (h1 : term14) : term385.
Proof. exact (EQ_MP (@lem5174088) (@lem5173980 h1)). Qed.
Lemma lem5174097 (s : real -> Prop) (x : real) (a : real) : (term97 s x a) = (term97 s x a).
Proof. exact (eq_refl (term97 s x a)). Qed.
Lemma lem5174098 (s : real -> Prop) (a : real) : (term107 s a) = (term107 s a).
Proof. exact (fun_ext (fun x : real => @lem5174097 s x a)). Qed.
Lemma lem5174099 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5174101 (s : real -> Prop) (a : real) : (term108 s a) = (term108 s a).
Proof. exact (MK_COMB (@lem5174099) (@lem5174098 s a)). Qed.
Lemma lem5174102 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term108 s a.
Proof. exact (EQ_MP (@lem5174101 s a) (@lem5173987 x s y a h1)). Qed.
Lemma lem5174114 (a : real) (s : real -> Prop) (h1 : term179 a s) : term179 a s.
Proof. exact (h1). Qed.
Lemma lem5174210 (s : real -> Prop) (x : real) (a : real) : (term97 s x a) = (term97 s x a).
Proof. exact (eq_refl (term97 s x a)). Qed.
Lemma lem5174211 (s : real -> Prop) (a : real) : (term107 s a) = (term107 s a).
Proof. exact (fun_ext (fun x : real => @lem5174210 s x a)). Qed.
Lemma lem5174212 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5174214 (s : real -> Prop) (a : real) : (term108 s a) = (term108 s a).
Proof. exact (MK_COMB (@lem5174212) (@lem5174211 s a)). Qed.
Lemma lem5174215 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term108 s a.
Proof. exact (EQ_MP (@lem5174214 s a) (@lem5173987 x s y a h1)). Qed.
Lemma lem5174331 (s : real -> Prop) (y : real) (a : real) : (term97 s y a) = (term97 s y a).
Proof. exact (eq_refl (term97 s y a)). Qed.
Lemma lem5174332 (s : real -> Prop) (a : real) : (term107 s a) = (term107 s a).
Proof. exact (fun_ext (fun y : real => @lem5174331 s y a)). Qed.
Lemma lem5174333 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5174335 (s : real -> Prop) (a : real) : (term108 s a) = (term108 s a).
Proof. exact (MK_COMB (@lem5174333) (@lem5174332 s a)). Qed.
Lemma lem5174336 (x : real) (s : real -> Prop) (a : real) (h1 : term254 x s a) : term108 s a.
Proof. exact (EQ_MP (@lem5174335 s a) (@lem5173996 x s a h1)). Qed.
Lemma lem5174371 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5174372 : term81 = term81.
Proof. exact (fun_ext (fun x : real => @lem5174371 x)). Qed.
Lemma lem5174373 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5174375 : term68 = term68.
Proof. exact (MK_COMB (@lem5174373) (@lem5174372)). Qed.
Lemma lem5174376 (h1 : term68) : term68.
Proof. exact (EQ_MP (@lem5174375) (@lem5173826 h1)). Qed.
Lemma lem5174457 (s : real -> Prop) (a : real) (x : real) : (term110 s a x) = (term110 s a x).
Proof. exact (eq_refl (term110 s a x)). Qed.
Lemma lem5174458 (s : real -> Prop) (a : real) : (term118 s a) = (term118 s a).
Proof. exact (fun_ext (fun x : real => @lem5174457 s a x)). Qed.
Lemma lem5174459 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5174461 (s : real -> Prop) (a : real) : (term119 s a) = (term119 s a).
Proof. exact (MK_COMB (@lem5174459) (@lem5174458 s a)). Qed.
Lemma lem5174462 (s : real -> Prop) (a : real) (h1 : term119 s a) : term119 s a.
Proof. exact (EQ_MP (@lem5174461 s a) (@lem5173999 s a h1)). Qed.
Lemma lem5174481 (_67547 : real) (h1 : term14) : term373 _67547.
Proof. exact (@lem5174089 h1 _67547). Qed.
Lemma lem5174482 (_67547 : real) : (term373 _67547) = (term363 _67547).
Proof. exact (eq_refl (term373 _67547)). Qed.
Lemma lem5174483 (_67547 : real) (h1 : term14) : term363 _67547.
Proof. exact (EQ_MP (@lem5174482 _67547) (@lem5174481 _67547 h1)). Qed.
Lemma lem5174484 (_67547 : real) (_67548 : real) (h1 : term14) : term351 _67547 _67548.
Proof. exact (@lem5174483 _67547 h1 _67548). Qed.
Lemma lem5174485 (_67547 : real) (_67548 : real) : (term351 _67547 _67548) = (term332 _67547 _67548).
Proof. exact (eq_refl (term351 _67547 _67548)). Qed.
Lemma lem5174486 (_67547 : real) (_67548 : real) (h1 : term14) : term332 _67547 _67548.
Proof. exact (EQ_MP (@lem5174485 _67547 _67548) (@lem5174484 _67547 _67548 h1)). Qed.
Lemma lem5174487 (_67549 : real) (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term387 s a _67549.
Proof. exact (@lem5174102 x s y a h1 _67549). Qed.
Lemma lem5174488 (s : real -> Prop) (_67549 : real) (a : real) : (term387 s a _67549) = (term97 s _67549 a).
Proof. exact (eq_refl (term387 s a _67549)). Qed.
Lemma lem5174514 (_67558 : real) (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term387 s a _67558.
Proof. exact (@lem5174215 x s y a h1 _67558). Qed.
Lemma lem5174515 (s : real -> Prop) (_67558 : real) (a : real) : (term387 s a _67558) = (term97 s _67558 a).
Proof. exact (eq_refl (term387 s a _67558)). Qed.
Lemma lem5174541 (_67567 : real) (x : real) (s : real -> Prop) (a : real) (h1 : term254 x s a) : term387 s a _67567.
Proof. exact (@lem5174336 x s a h1 _67567). Qed.
Lemma lem5174542 (s : real -> Prop) (_67567 : real) (a : real) : (term387 s a _67567) = (term97 s _67567 a).
Proof. exact (eq_refl (term387 s a _67567)). Qed.
Lemma lem5174553 (_67571 : real) (h1 : term68) : term388 _67571.
Proof. exact (@lem5174376 h1 _67571). Qed.
Lemma lem5174554 (_67571 : real) : (term388 _67571) = (real_le _67571 _67571).
Proof. exact (eq_refl (term388 _67571)). Qed.
Lemma lem5174571 (_67577 : real) (s : real -> Prop) (a : real) (h1 : term119 s a) : term389 s a _67577.
Proof. exact (@lem5174462 s a h1 _67577). Qed.
Lemma lem5174572 (s : real -> Prop) (a : real) (_67577 : real) : (term389 s a _67577) = (term110 s a _67577).
Proof. exact (eq_refl (term389 s a _67577)). Qed.
Lemma lem5174610 (_67547 : real) (_67548 : real) : (term332 _67547 _67548) = (term390 _67547 _67548).
Proof. exact (@lem5171262 (term391 _67547 _67548) (term391 _67548 _67547) (_67547 = _67548)). Qed.
Lemma lem5174611 (_67547 : real) (_67548 : real) (h1 : term14) : term390 _67547 _67548.
Proof. exact (EQ_MP (@lem5174610 _67547 _67548) (@lem5174486 _67547 _67548 h1)). Qed.
Lemma lem5174617 (_67549 : real) (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term97 s _67549 a.
Proof. exact (EQ_MP (@lem5174488 s _67549 a) (@lem5174487 _67549 x s y a h1)). Qed.
Lemma lem5174623 (a : real) (s : real -> Prop) (h1 : term179 a s) : term179 a s.
Proof. exact (h1). Qed.
Lemma lem5174671 (_67558 : real) (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term97 s _67558 a.
Proof. exact (EQ_MP (@lem5174515 s _67558 a) (@lem5174514 _67558 x s y a h1)). Qed.
Lemma lem5174679 (s : real -> Prop) (y : real) (a : real) (h1 : term96 s y a) : term391 y a.
Proof. exact (proj2 (@lem5173991 s y a h1)). Qed.
Lemma lem5174729 (_67567 : real) (x : real) (s : real -> Prop) (a : real) (h1 : term254 x s a) : term97 s _67567 a.
Proof. exact (EQ_MP (@lem5174542 s _67567 a) (@lem5174541 _67567 x s a h1)). Qed.
Lemma lem5174733 (s : real -> Prop) (x : real) (a : real) (h1 : term96 s x a) : term391 x a.
Proof. exact (proj2 (@lem5173998 s x a h1)). Qed.
Lemma lem5174789 (_67577 : real) (s : real -> Prop) (a : real) (h1 : term119 s a) : term110 s a _67577.
Proof. exact (EQ_MP (@lem5174572 s a _67577) (@lem5174571 _67577 s a h1)). Qed.
Lemma lem5174802 : (@IN real) = (@IN real).
Proof. exact (eq_refl (@IN real)). Qed.
Lemma lem5174803 (_67578 : real) (_67580 : real) (h1 : _67578 = _67580) : _67578 = _67580.
Proof. exact (h1). Qed.
Lemma lem5174804 (_67579 : real -> Prop) (_67581 : real -> Prop) (h1 : _67579 = _67581) : _67579 = _67581.
Proof. exact (h1). Qed.
Lemma lem5174805 (_67578 : real) (_67580 : real) (h1 : _67578 = _67580) : (@IN real _67578) = (@IN real _67580).
Proof. exact (MK_COMB (@lem5174802) (@lem5174803 _67578 _67580 h1)). Qed.
Lemma lem5174806 (_67579 : real -> Prop) (_67581 : real -> Prop) (_67578 : real) (_67580 : real) (h1 : _67579 = _67581) (h2 : _67578 = _67580) : (@IN real _67578 _67579) = (@IN real _67580 _67581).
Proof. exact (MK_COMB (@lem5174805 _67578 _67580 h2) (@lem5174804 _67579 _67581 h1)). Qed.
Lemma lem5174808 (b : Prop) (a : Prop) : term392 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5174809 (_67580 : real) (_67581 : real -> Prop) (_67578 : real) (_67579 : real -> Prop) : term393 _67580 _67581 _67578 _67579.
Proof. exact (@lem5174808 (@IN real _67580 _67581) (@IN real _67578 _67579)). Qed.
Lemma lem5174810 (_67579 : real -> Prop) (_67581 : real -> Prop) (_67578 : real) (_67580 : real) (h1 : _67579 = _67581) (h2 : _67578 = _67580) : term394 _67580 _67581 _67578 _67579.
Proof. exact (@lem5174809 _67580 _67581 _67578 _67579 (@lem5174806 _67579 _67581 _67578 _67580 h1 h2)). Qed.
Lemma lem5174811 (_67580 : real) (_67578 : real) (_67579 : real -> Prop) (_67581 : real -> Prop) (h1 : _67579 = _67581) : term395 _67580 _67581 _67578 _67579.
Proof. exact (fun h0 : _67578 = _67580 => @lem5174810 _67579 _67581 _67578 _67580 h1 h0). Qed.
Lemma lem5174813 (a : Prop) (b : Prop) : (a -> b) = (term396 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5174814 (_67580 : real) (_67581 : real -> Prop) (_67578 : real) (_67579 : real -> Prop) : (term395 _67580 _67581 _67578 _67579) = (term397 _67580 _67581 _67578 _67579).
Proof. exact (@lem5174813 (_67578 = _67580) (term394 _67580 _67581 _67578 _67579)). Qed.
Lemma lem5174815 (_67580 : real) (_67578 : real) (_67579 : real -> Prop) (_67581 : real -> Prop) (h1 : _67579 = _67581) : term397 _67580 _67581 _67578 _67579.
Proof. exact (EQ_MP (@lem5174814 _67580 _67581 _67578 _67579) (@lem5174811 _67580 _67578 _67579 _67581 h1)). Qed.
Lemma lem5174816 (_67580 : real) (_67581 : real -> Prop) (_67578 : real) (_67579 : real -> Prop) : term398 _67580 _67581 _67578 _67579.
Proof. exact (fun h0 : _67579 = _67581 => @lem5174815 _67580 _67578 _67579 _67581 h0). Qed.
Lemma lem5174818 (a : Prop) (b : Prop) : (a -> b) = (term396 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5174819 (_67580 : real) (_67581 : real -> Prop) (_67578 : real) (_67579 : real -> Prop) : (term398 _67580 _67581 _67578 _67579) = (term399 _67580 _67581 _67578 _67579).
Proof. exact (@lem5174818 (_67579 = _67581) (term397 _67580 _67581 _67578 _67579)). Qed.
Lemma lem5174820 (_67580 : real) (_67581 : real -> Prop) (_67578 : real) (_67579 : real -> Prop) : term399 _67580 _67581 _67578 _67579.
Proof. exact (EQ_MP (@lem5174819 _67580 _67581 _67578 _67579) (@lem5174816 _67580 _67581 _67578 _67579)). Qed.
Lemma lem5174857 (x : real -> Prop) : x = x.
Proof. exact (@lem21386 (real -> Prop) x). Qed.
Lemma lem5174858 (s : real -> Prop) : s = s.
Proof. exact (@lem5174857 s). Qed.
Lemma lem5174859 (s : real -> Prop) : term400 s.
Proof. exact (fun h0 : term401 s => @lem5174858 s). Qed.
Lemma lem5174861 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5174862 (s : real -> Prop) : (term400 s) = (s = s).
Proof. exact (@lem5174861 (s = s)). Qed.
Lemma lem5174863 (s : real -> Prop) : s = s.
Proof. exact (EQ_MP (@lem5174862 s) (@lem5174859 s)). Qed.
Lemma lem5174865 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : @IN real x s.
Proof. exact (proj1 (@lem5173986 x s y a h1)). Qed.
Lemma lem5174866 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term403 x s.
Proof. exact (fun h0 : term179 x s => @lem5174865 x s y a h1). Qed.
Lemma lem5174868 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5174869 (x : real) (s : real -> Prop) : (term403 x s) = (@IN real x s).
Proof. exact (@lem5174868 (@IN real x s)). Qed.
Lemma lem5174870 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : @IN real x s.
Proof. exact (EQ_MP (@lem5174869 x s) (@lem5174866 x s y a h1)). Qed.
Lemma lem5174876 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5174877 (a : real) (_67549 : real) (s : real -> Prop) : (term97 s _67549 a) = (term404 a _67549 s).
Proof. exact (@lem5174876 (real_le _67549 a) (term179 _67549 s)). Qed.
Lemma lem5174883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5174884 (a : real) (_67549 : real) (s : real -> Prop) : (term405 s _67549 a) = (term406 a _67549 s).
Proof. exact (MK_COMB (@lem5174883) (@lem5174877 a _67549 s)). Qed.
Lemma lem5174890 (a : real) (_67549 : real) (s : real -> Prop) : (term404 a _67549 s) = (term404 a _67549 s).
Proof. exact (eq_refl (term404 a _67549 s)). Qed.
Lemma lem5174891 (a : real) (_67549 : real) (s : real -> Prop) : ((term97 s _67549 a) = (term404 a _67549 s)) = ((term404 a _67549 s) = (term404 a _67549 s)).
Proof. exact (MK_COMB (@lem5174884 a _67549 s) (@lem5174890 a _67549 s)). Qed.
Lemma lem5174893 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5174894 (x : Prop) : (x = x) = True.
Proof. exact (@lem5174893 Prop x). Qed.
Lemma lem5174895 (a : real) (_67549 : real) (s : real -> Prop) : ((term404 a _67549 s) = (term404 a _67549 s)) = True.
Proof. exact (@lem5174894 (term404 a _67549 s)). Qed.
Lemma lem5174896 (a : real) (_67549 : real) (s : real -> Prop) : ((term97 s _67549 a) = (term404 a _67549 s)) = True.
Proof. exact (TRANS (@lem5174891 a _67549 s) (@lem5174895 a _67549 s)). Qed.
Lemma lem5174897 (a : real) (_67549 : real) (s : real -> Prop) : True = ((term97 s _67549 a) = (term404 a _67549 s)).
Proof. exact (SYM (@lem5174896 a _67549 s)). Qed.
Lemma lem5174898 (a : real) (_67549 : real) (s : real -> Prop) : (term97 s _67549 a) = (term404 a _67549 s).
Proof. exact (EQ_MP (@lem5174897 a _67549 s) (@lem0)). Qed.
Lemma lem5174899 (_67549 : real) (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term404 a _67549 s.
Proof. exact (EQ_MP (@lem5174898 a _67549 s) (@lem5174617 _67549 x s y a h1)). Qed.
Lemma lem5174901 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5174902 (s : real -> Prop) (_67549 : real) (a : real) : (term404 a _67549 s) = (term408 s _67549 a).
Proof. exact (@lem5174901 (term179 _67549 s) (real_le _67549 a)). Qed.
Lemma lem5174904 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5174905 (_67549 : real) (s : real -> Prop) : (term410 _67549 s) = (@IN real _67549 s).
Proof. exact (@lem5174904 (@IN real _67549 s)). Qed.
Lemma lem5174906 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5174907 (_67549 : real) (s : real -> Prop) : (term411 _67549 s) = (term412 _67549 s).
Proof. exact (MK_COMB (@lem5174906) (@lem5174905 _67549 s)). Qed.
Lemma lem5174908 (_67549 : real) (a : real) : (real_le _67549 a) = (real_le _67549 a).
Proof. exact (eq_refl (real_le _67549 a)). Qed.
Lemma lem5174909 (s : real -> Prop) (_67549 : real) (a : real) : (term408 s _67549 a) = (term89 s _67549 a).
Proof. exact (MK_COMB (@lem5174907 _67549 s) (@lem5174908 _67549 a)). Qed.
Lemma lem5174910 (s : real -> Prop) (_67549 : real) (a : real) : (term404 a _67549 s) = (term89 s _67549 a).
Proof. exact (TRANS (@lem5174902 s _67549 a) (@lem5174909 s _67549 a)). Qed.
Lemma lem5174913 (_67549 : real) (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term89 s _67549 a.
Proof. exact (EQ_MP (@lem5174910 s _67549 a) (@lem5174899 _67549 x s y a h1)). Qed.
Lemma lem5174914 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term89 s x a.
Proof. exact (@lem5174913 x x s y a h1). Qed.
Lemma lem5174917 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : real_le x a.
Proof. exact (@lem5174914 x s y a h1 (@lem5174870 x s y a h1)). Qed.
Lemma lem5174918 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term413 x a.
Proof. exact (fun h0 : term391 x a => @lem5174917 x s y a h1). Qed.
Lemma lem5174920 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5174921 (x : real) (a : real) : (term413 x a) = (real_le x a).
Proof. exact (@lem5174920 (real_le x a)). Qed.
Lemma lem5174922 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : real_le x a.
Proof. exact (EQ_MP (@lem5174921 x a) (@lem5174918 x s y a h1)). Qed.
Lemma lem5174924 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : real_le a x.
Proof. exact (proj2 (@lem5173986 x s y a h1)). Qed.
Lemma lem5174925 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term413 a x.
Proof. exact (fun h0 : term391 a x => @lem5174924 x s y a h1). Qed.
Lemma lem5174927 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5174928 (a : real) (x : real) : (term413 a x) = (real_le a x).
Proof. exact (@lem5174927 (real_le a x)). Qed.
Lemma lem5174929 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : real_le a x.
Proof. exact (EQ_MP (@lem5174928 a x) (@lem5174925 x s y a h1)). Qed.
Lemma lem5174945 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5174946 (_67548 : real) (_67547 : real) : (term414 _67547 _67548) = (term415 _67548 _67547).
Proof. exact (@lem5174945 (_67547 = _67548) (term391 _67548 _67547)). Qed.
Lemma lem5174954 (_67547 : real) (_67548 : real) : (term416 _67547 _67548) = (term416 _67547 _67548).
Proof. exact (eq_refl (term416 _67547 _67548)). Qed.
Lemma lem5174955 (_67548 : real) (_67547 : real) : (term390 _67547 _67548) = (term417 _67548 _67547).
Proof. exact (MK_COMB (@lem5174954 _67547 _67548) (@lem5174946 _67548 _67547)). Qed.
Lemma lem5174959 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5174960 (_67548 : real) (_67547 : real) : (term417 _67548 _67547) = (term418 _67548 _67547).
Proof. exact (@lem5174959 (_67547 = _67548) (term391 _67547 _67548) (term391 _67548 _67547)). Qed.
Lemma lem5174978 (_67548 : real) (_67547 : real) : (term390 _67547 _67548) = (term418 _67548 _67547).
Proof. exact (TRANS (@lem5174955 _67548 _67547) (@lem5174960 _67548 _67547)). Qed.
Lemma lem5174979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5174980 (_67548 : real) (_67547 : real) : (term419 _67547 _67548) = (term420 _67548 _67547).
Proof. exact (MK_COMB (@lem5174979) (@lem5174978 _67548 _67547)). Qed.
Lemma lem5174998 (_67548 : real) (_67547 : real) : (term418 _67548 _67547) = (term418 _67548 _67547).
Proof. exact (eq_refl (term418 _67548 _67547)). Qed.
Lemma lem5174999 (_67548 : real) (_67547 : real) : ((term390 _67547 _67548) = (term418 _67548 _67547)) = ((term418 _67548 _67547) = (term418 _67548 _67547)).
Proof. exact (MK_COMB (@lem5174980 _67548 _67547) (@lem5174998 _67548 _67547)). Qed.
Lemma lem5175001 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5175002 (x : Prop) : (x = x) = True.
Proof. exact (@lem5175001 Prop x). Qed.
Lemma lem5175003 (_67548 : real) (_67547 : real) : ((term418 _67548 _67547) = (term418 _67548 _67547)) = True.
Proof. exact (@lem5175002 (term418 _67548 _67547)). Qed.
Lemma lem5175004 (_67548 : real) (_67547 : real) : ((term390 _67547 _67548) = (term418 _67548 _67547)) = True.
Proof. exact (TRANS (@lem5174999 _67548 _67547) (@lem5175003 _67548 _67547)). Qed.
Lemma lem5175005 (_67548 : real) (_67547 : real) : True = ((term390 _67547 _67548) = (term418 _67548 _67547)).
Proof. exact (SYM (@lem5175004 _67548 _67547)). Qed.
Lemma lem5175006 (_67548 : real) (_67547 : real) : (term390 _67547 _67548) = (term418 _67548 _67547).
Proof. exact (EQ_MP (@lem5175005 _67548 _67547) (@lem0)). Qed.
Lemma lem5175007 (_67548 : real) (_67547 : real) (h1 : term14) : term418 _67548 _67547.
Proof. exact (EQ_MP (@lem5175006 _67548 _67547) (@lem5174611 _67547 _67548 h1)). Qed.
Lemma lem5175009 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5175010 (_67547 : real) (_67548 : real) : (term418 _67548 _67547) = (term421 _67547 _67548).
Proof. exact (@lem5175009 (term328 _67548 _67547) (_67547 = _67548)). Qed.
Lemma lem5175012 (a : Prop) (b : Prop) : (term422 a b) = (term423 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5175013 (_67548 : real) (_67547 : real) : (term424 _67548 _67547) = (term425 _67548 _67547).
Proof. exact (@lem5175012 (term391 _67547 _67548) (term391 _67548 _67547)). Qed.
Lemma lem5175015 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5175016 (_67547 : real) (_67548 : real) : (term426 _67547 _67548) = (real_le _67547 _67548).
Proof. exact (@lem5175015 (real_le _67547 _67548)). Qed.
Lemma lem5175017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5175018 (_67547 : real) (_67548 : real) : (term427 _67547 _67548) = (term428 _67547 _67548).
Proof. exact (MK_COMB (@lem5175017) (@lem5175016 _67547 _67548)). Qed.
Lemma lem5175020 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5175021 (_67548 : real) (_67547 : real) : (term426 _67548 _67547) = (real_le _67548 _67547).
Proof. exact (@lem5175020 (real_le _67548 _67547)). Qed.
Lemma lem5175022 (_67548 : real) (_67547 : real) : (term425 _67548 _67547) = (term7 _67548 _67547).
Proof. exact (MK_COMB (@lem5175018 _67547 _67548) (@lem5175021 _67548 _67547)). Qed.
Lemma lem5175023 (_67548 : real) (_67547 : real) : (term424 _67548 _67547) = (term7 _67548 _67547).
Proof. exact (TRANS (@lem5175013 _67548 _67547) (@lem5175022 _67548 _67547)). Qed.
Lemma lem5175024 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5175025 (_67548 : real) (_67547 : real) : (term429 _67548 _67547) = (term430 _67548 _67547).
Proof. exact (MK_COMB (@lem5175024) (@lem5175023 _67548 _67547)). Qed.
Lemma lem5175026 (_67547 : real) (_67548 : real) : (_67547 = _67548) = (_67547 = _67548).
Proof. exact (eq_refl (_67547 = _67548)). Qed.
Lemma lem5175027 (_67547 : real) (_67548 : real) : (term421 _67547 _67548) = (term431 _67547 _67548).
Proof. exact (MK_COMB (@lem5175025 _67548 _67547) (@lem5175026 _67547 _67548)). Qed.
Lemma lem5175028 (_67547 : real) (_67548 : real) : (term418 _67548 _67547) = (term431 _67547 _67548).
Proof. exact (TRANS (@lem5175010 _67547 _67548) (@lem5175027 _67547 _67548)). Qed.
Lemma lem5175030 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term7 a x.
Proof. exact (conj (@lem5174922 x s y a h1) (@lem5174929 x s y a h1)). Qed.
Lemma lem5175032 (_67547 : real) (_67548 : real) (h1 : term14) : term431 _67547 _67548.
Proof. exact (EQ_MP (@lem5175028 _67547 _67548) (@lem5175007 _67548 _67547 h1)). Qed.
Lemma lem5175033 (x : real) (a : real) (h1 : term14) : term431 x a.
Proof. exact (@lem5175032 x a h1). Qed.
Lemma lem5175036 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term218 x s y a) : x = a.
Proof. exact (@lem5175033 x a h1 (@lem5175030 x s y a h2)). Qed.
Lemma lem5175037 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term218 x s y a) : term432 x a.
Proof. exact (fun h0 : term433 x a => @lem5175036 x s y a h1 h2). Qed.
Lemma lem5175039 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5175040 (x : real) (a : real) : (term432 x a) = (x = a).
Proof. exact (@lem5175039 (x = a)). Qed.
Lemma lem5175041 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term218 x s y a) : x = a.
Proof. exact (EQ_MP (@lem5175040 x a) (@lem5175037 x s y a h1 h2)). Qed.
Lemma lem5175043 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : @IN real x s.
Proof. exact (proj1 (@lem5173986 x s y a h1)). Qed.
Lemma lem5175044 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term403 x s.
Proof. exact (fun h0 : term179 x s => @lem5175043 x s y a h1). Qed.
Lemma lem5175046 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5175047 (x : real) (s : real -> Prop) : (term403 x s) = (@IN real x s).
Proof. exact (@lem5175046 (@IN real x s)). Qed.
Lemma lem5175048 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : @IN real x s.
Proof. exact (EQ_MP (@lem5175047 x s) (@lem5175044 x s y a h1)). Qed.
Lemma lem5175066 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5175067 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : (term397 _67580 _67581 _67578 _67579) = (term434 _67581 _67580 _67578 _67579).
Proof. exact (@lem5175066 (@IN real _67580 _67581) (term433 _67578 _67580) (term179 _67578 _67579)). Qed.
Lemma lem5175085 (_67579 : real -> Prop) (_67581 : real -> Prop) : (term435 _67579 _67581) = (term435 _67579 _67581).
Proof. exact (eq_refl (term435 _67579 _67581)). Qed.
Lemma lem5175086 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : (term399 _67580 _67581 _67578 _67579) = (term436 _67581 _67580 _67578 _67579).
Proof. exact (MK_COMB (@lem5175085 _67579 _67581) (@lem5175067 _67581 _67580 _67578 _67579)). Qed.
Lemma lem5175090 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5175091 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : (term436 _67581 _67580 _67578 _67579) = (term437 _67581 _67580 _67578 _67579).
Proof. exact (@lem5175090 (@IN real _67580 _67581) (term438 _67579 _67581) (term439 _67580 _67578 _67579)). Qed.
Lemma lem5175121 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : (term399 _67580 _67581 _67578 _67579) = (term437 _67581 _67580 _67578 _67579).
Proof. exact (TRANS (@lem5175086 _67581 _67580 _67578 _67579) (@lem5175091 _67581 _67580 _67578 _67579)). Qed.
Lemma lem5175122 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5175123 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : (term440 _67580 _67581 _67578 _67579) = (term441 _67581 _67580 _67578 _67579).
Proof. exact (MK_COMB (@lem5175122) (@lem5175121 _67581 _67580 _67578 _67579)). Qed.
Lemma lem5175153 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : (term437 _67581 _67580 _67578 _67579) = (term437 _67581 _67580 _67578 _67579).
Proof. exact (eq_refl (term437 _67581 _67580 _67578 _67579)). Qed.
Lemma lem5175154 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : ((term399 _67580 _67581 _67578 _67579) = (term437 _67581 _67580 _67578 _67579)) = ((term437 _67581 _67580 _67578 _67579) = (term437 _67581 _67580 _67578 _67579)).
Proof. exact (MK_COMB (@lem5175123 _67581 _67580 _67578 _67579) (@lem5175153 _67581 _67580 _67578 _67579)). Qed.
Lemma lem5175156 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5175157 (x : Prop) : (x = x) = True.
Proof. exact (@lem5175156 Prop x). Qed.
Lemma lem5175158 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : ((term437 _67581 _67580 _67578 _67579) = (term437 _67581 _67580 _67578 _67579)) = True.
Proof. exact (@lem5175157 (term437 _67581 _67580 _67578 _67579)). Qed.
Lemma lem5175159 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : ((term399 _67580 _67581 _67578 _67579) = (term437 _67581 _67580 _67578 _67579)) = True.
Proof. exact (TRANS (@lem5175154 _67581 _67580 _67578 _67579) (@lem5175158 _67581 _67580 _67578 _67579)). Qed.
Lemma lem5175160 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : True = ((term399 _67580 _67581 _67578 _67579) = (term437 _67581 _67580 _67578 _67579)).
Proof. exact (SYM (@lem5175159 _67581 _67580 _67578 _67579)). Qed.
Lemma lem5175161 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : (term399 _67580 _67581 _67578 _67579) = (term437 _67581 _67580 _67578 _67579).
Proof. exact (EQ_MP (@lem5175160 _67581 _67580 _67578 _67579) (@lem0)). Qed.
Lemma lem5175162 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : term437 _67581 _67580 _67578 _67579.
Proof. exact (EQ_MP (@lem5175161 _67581 _67580 _67578 _67579) (@lem5174820 _67580 _67581 _67578 _67579)). Qed.
Lemma lem5175164 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5175165 (_67578 : real) (_67579 : real -> Prop) (_67580 : real) (_67581 : real -> Prop) : (term437 _67581 _67580 _67578 _67579) = (term442 _67578 _67579 _67580 _67581).
Proof. exact (@lem5175164 (term443 _67581 _67580 _67578 _67579) (@IN real _67580 _67581)). Qed.
Lemma lem5175167 (a : Prop) (b : Prop) : (term422 a b) = (term423 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5175168 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : (term444 _67581 _67580 _67578 _67579) = (term445 _67581 _67580 _67578 _67579).
Proof. exact (@lem5175167 (term438 _67579 _67581) (term439 _67580 _67578 _67579)). Qed.
Lemma lem5175170 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5175171 (_67579 : real -> Prop) (_67581 : real -> Prop) : (term446 _67579 _67581) = (_67579 = _67581).
Proof. exact (@lem5175170 (_67579 = _67581)). Qed.
Lemma lem5175172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5175173 (_67579 : real -> Prop) (_67581 : real -> Prop) : (term447 _67579 _67581) = (term448 _67579 _67581).
Proof. exact (MK_COMB (@lem5175172) (@lem5175171 _67579 _67581)). Qed.
Lemma lem5175175 (a : Prop) (b : Prop) : (term422 a b) = (term423 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5175176 (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : (term449 _67580 _67578 _67579) = (term450 _67580 _67578 _67579).
Proof. exact (@lem5175175 (term433 _67578 _67580) (term179 _67578 _67579)). Qed.
Lemma lem5175178 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5175179 (_67578 : real) (_67580 : real) : (term451 _67578 _67580) = (_67578 = _67580).
Proof. exact (@lem5175178 (_67578 = _67580)). Qed.
Lemma lem5175180 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5175181 (_67578 : real) (_67580 : real) : (term452 _67578 _67580) = (term453 _67578 _67580).
Proof. exact (MK_COMB (@lem5175180) (@lem5175179 _67578 _67580)). Qed.
Lemma lem5175183 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5175184 (_67578 : real) (_67579 : real -> Prop) : (term410 _67578 _67579) = (@IN real _67578 _67579).
Proof. exact (@lem5175183 (@IN real _67578 _67579)). Qed.
Lemma lem5175185 (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : (term450 _67580 _67578 _67579) = (term454 _67580 _67578 _67579).
Proof. exact (MK_COMB (@lem5175181 _67578 _67580) (@lem5175184 _67578 _67579)). Qed.
Lemma lem5175186 (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : (term449 _67580 _67578 _67579) = (term454 _67580 _67578 _67579).
Proof. exact (TRANS (@lem5175176 _67580 _67578 _67579) (@lem5175185 _67580 _67578 _67579)). Qed.
Lemma lem5175187 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : (term445 _67581 _67580 _67578 _67579) = (term455 _67581 _67580 _67578 _67579).
Proof. exact (MK_COMB (@lem5175173 _67579 _67581) (@lem5175186 _67580 _67578 _67579)). Qed.
Lemma lem5175188 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : (term444 _67581 _67580 _67578 _67579) = (term455 _67581 _67580 _67578 _67579).
Proof. exact (TRANS (@lem5175168 _67581 _67580 _67578 _67579) (@lem5175187 _67581 _67580 _67578 _67579)). Qed.
Lemma lem5175189 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5175190 (_67581 : real -> Prop) (_67580 : real) (_67578 : real) (_67579 : real -> Prop) : (term456 _67581 _67580 _67578 _67579) = (term457 _67581 _67580 _67578 _67579).
Proof. exact (MK_COMB (@lem5175189) (@lem5175188 _67581 _67580 _67578 _67579)). Qed.
Lemma lem5175191 (_67580 : real) (_67581 : real -> Prop) : (@IN real _67580 _67581) = (@IN real _67580 _67581).
Proof. exact (eq_refl (@IN real _67580 _67581)). Qed.
Lemma lem5175192 (_67578 : real) (_67579 : real -> Prop) (_67580 : real) (_67581 : real -> Prop) : (term442 _67578 _67579 _67580 _67581) = (term458 _67578 _67579 _67580 _67581).
Proof. exact (MK_COMB (@lem5175190 _67581 _67580 _67578 _67579) (@lem5175191 _67580 _67581)). Qed.
Lemma lem5175193 (_67578 : real) (_67579 : real -> Prop) (_67580 : real) (_67581 : real -> Prop) : (term437 _67581 _67580 _67578 _67579) = (term458 _67578 _67579 _67580 _67581).
Proof. exact (TRANS (@lem5175165 _67578 _67579 _67580 _67581) (@lem5175192 _67578 _67579 _67580 _67581)). Qed.
Lemma lem5175195 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term218 x s y a) : term454 a x s.
Proof. exact (conj (@lem5175041 x s y a h1 h2) (@lem5175048 x s y a h2)). Qed.
Lemma lem5175196 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term218 x s y a) : term459 a x s.
Proof. exact (conj (@lem5174863 s) (@lem5175195 x s y a h1 h2)). Qed.
Lemma lem5175198 (_67578 : real) (_67579 : real -> Prop) (_67580 : real) (_67581 : real -> Prop) : term458 _67578 _67579 _67580 _67581.
Proof. exact (EQ_MP (@lem5175193 _67578 _67579 _67580 _67581) (@lem5175162 _67581 _67580 _67578 _67579)). Qed.
Lemma lem5175199 (x : real) (a : real) (s : real -> Prop) : term460 x a s.
Proof. exact (@lem5175198 x s a s). Qed.
Lemma lem5175202 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term218 x s y a) : @IN real a s.
Proof. exact (@lem5175199 x a s (@lem5175196 x s y a h1 h2)). Qed.
Lemma lem5175203 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term218 x s y a) : term403 a s.
Proof. exact (fun h0 : term179 a s => @lem5175202 x s y a h1 h2). Qed.
Lemma lem5175205 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5175206 (a : real) (s : real -> Prop) : (term403 a s) = (@IN real a s).
Proof. exact (@lem5175205 (@IN real a s)). Qed.
Lemma lem5175207 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term218 x s y a) : @IN real a s.
Proof. exact (EQ_MP (@lem5175206 a s) (@lem5175203 x s y a h1 h2)). Qed.
Lemma lem5175210 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5175212 (a : real) (s : real -> Prop) : (term179 a s) = (term461 a s).
Proof. exact (@lem5175210 (@IN real a s)). Qed.
Lemma lem5175215 (a : real) (s : real -> Prop) (h1 : term179 a s) : term461 a s.
Proof. exact (EQ_MP (@lem5175212 a s) (@lem5174623 a s h1)). Qed.
Lemma lem5175218 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term179 a s) (h3 : term218 x s y a) : False.
Proof. exact (@lem5175215 a s h2 (@lem5175207 x s y a h1 h3)). Qed.
Lemma lem5175219 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term179 a s) (h3 : term218 x s y a) : term462.
Proof. exact (fun h0 : ~ False => @lem5175218 x s y a h1 h2 h3). Qed.
Lemma lem5175221 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5175222 : term462 = False.
Proof. exact (@lem5175221 False). Qed.
Lemma lem5175223 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term179 a s) (h3 : term218 x s y a) : False.
Proof. exact (EQ_MP (@lem5175222) (@lem5175219 x s y a h1 h2 h3)). Qed.
Lemma lem5175279 (s : real -> Prop) (y : real) (a : real) (h1 : term96 s y a) : @IN real y s.
Proof. exact (proj1 (@lem5173991 s y a h1)). Qed.
Lemma lem5175280 (s : real -> Prop) (y : real) (a : real) (h1 : term96 s y a) : term403 y s.
Proof. exact (fun h0 : term179 y s => @lem5175279 s y a h1). Qed.
Lemma lem5175282 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5175283 (y : real) (s : real -> Prop) : (term403 y s) = (@IN real y s).
Proof. exact (@lem5175282 (@IN real y s)). Qed.
Lemma lem5175284 (s : real -> Prop) (y : real) (a : real) (h1 : term96 s y a) : @IN real y s.
Proof. exact (EQ_MP (@lem5175283 y s) (@lem5175280 s y a h1)). Qed.
Lemma lem5175290 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5175291 (a : real) (_67558 : real) (s : real -> Prop) : (term97 s _67558 a) = (term404 a _67558 s).
Proof. exact (@lem5175290 (real_le _67558 a) (term179 _67558 s)). Qed.
Lemma lem5175297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5175298 (a : real) (_67558 : real) (s : real -> Prop) : (term405 s _67558 a) = (term406 a _67558 s).
Proof. exact (MK_COMB (@lem5175297) (@lem5175291 a _67558 s)). Qed.
Lemma lem5175304 (a : real) (_67558 : real) (s : real -> Prop) : (term404 a _67558 s) = (term404 a _67558 s).
Proof. exact (eq_refl (term404 a _67558 s)). Qed.
Lemma lem5175305 (a : real) (_67558 : real) (s : real -> Prop) : ((term97 s _67558 a) = (term404 a _67558 s)) = ((term404 a _67558 s) = (term404 a _67558 s)).
Proof. exact (MK_COMB (@lem5175298 a _67558 s) (@lem5175304 a _67558 s)). Qed.
Lemma lem5175307 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5175308 (x : Prop) : (x = x) = True.
Proof. exact (@lem5175307 Prop x). Qed.
Lemma lem5175309 (a : real) (_67558 : real) (s : real -> Prop) : ((term404 a _67558 s) = (term404 a _67558 s)) = True.
Proof. exact (@lem5175308 (term404 a _67558 s)). Qed.
Lemma lem5175310 (a : real) (_67558 : real) (s : real -> Prop) : ((term97 s _67558 a) = (term404 a _67558 s)) = True.
Proof. exact (TRANS (@lem5175305 a _67558 s) (@lem5175309 a _67558 s)). Qed.
Lemma lem5175311 (a : real) (_67558 : real) (s : real -> Prop) : True = ((term97 s _67558 a) = (term404 a _67558 s)).
Proof. exact (SYM (@lem5175310 a _67558 s)). Qed.
Lemma lem5175312 (a : real) (_67558 : real) (s : real -> Prop) : (term97 s _67558 a) = (term404 a _67558 s).
Proof. exact (EQ_MP (@lem5175311 a _67558 s) (@lem0)). Qed.
Lemma lem5175313 (_67558 : real) (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term404 a _67558 s.
Proof. exact (EQ_MP (@lem5175312 a _67558 s) (@lem5174671 _67558 x s y a h1)). Qed.
Lemma lem5175315 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5175316 (s : real -> Prop) (_67558 : real) (a : real) : (term404 a _67558 s) = (term408 s _67558 a).
Proof. exact (@lem5175315 (term179 _67558 s) (real_le _67558 a)). Qed.
Lemma lem5175318 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5175319 (_67558 : real) (s : real -> Prop) : (term410 _67558 s) = (@IN real _67558 s).
Proof. exact (@lem5175318 (@IN real _67558 s)). Qed.
Lemma lem5175320 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5175321 (_67558 : real) (s : real -> Prop) : (term411 _67558 s) = (term412 _67558 s).
Proof. exact (MK_COMB (@lem5175320) (@lem5175319 _67558 s)). Qed.
Lemma lem5175322 (_67558 : real) (a : real) : (real_le _67558 a) = (real_le _67558 a).
Proof. exact (eq_refl (real_le _67558 a)). Qed.
Lemma lem5175323 (s : real -> Prop) (_67558 : real) (a : real) : (term408 s _67558 a) = (term89 s _67558 a).
Proof. exact (MK_COMB (@lem5175321 _67558 s) (@lem5175322 _67558 a)). Qed.
Lemma lem5175324 (s : real -> Prop) (_67558 : real) (a : real) : (term404 a _67558 s) = (term89 s _67558 a).
Proof. exact (TRANS (@lem5175316 s _67558 a) (@lem5175323 s _67558 a)). Qed.
Lemma lem5175327 (_67558 : real) (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term89 s _67558 a.
Proof. exact (EQ_MP (@lem5175324 s _67558 a) (@lem5175313 _67558 x s y a h1)). Qed.
Lemma lem5175328 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) : term89 s y a.
Proof. exact (@lem5175327 y x s y a h1). Qed.
Lemma lem5175331 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) (h2 : term96 s y a) : real_le y a.
Proof. exact (@lem5175328 x s y a h1 (@lem5175284 s y a h2)). Qed.
Lemma lem5175332 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) (h2 : term96 s y a) : term413 y a.
Proof. exact (fun h0 : term391 y a => @lem5175331 x s y a h1 h2). Qed.
Lemma lem5175334 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5175335 (y : real) (a : real) : (term413 y a) = (real_le y a).
Proof. exact (@lem5175334 (real_le y a)). Qed.
Lemma lem5175336 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) (h2 : term96 s y a) : real_le y a.
Proof. exact (EQ_MP (@lem5175335 y a) (@lem5175332 x s y a h1 h2)). Qed.
Lemma lem5175339 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5175341 (y : real) (a : real) : (term391 y a) = (term463 y a).
Proof. exact (@lem5175339 (real_le y a)). Qed.
Lemma lem5175344 (s : real -> Prop) (y : real) (a : real) (h1 : term96 s y a) : term463 y a.
Proof. exact (EQ_MP (@lem5175341 y a) (@lem5174679 s y a h1)). Qed.
Lemma lem5175347 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) (h2 : term96 s y a) : False.
Proof. exact (@lem5175344 s y a h2 (@lem5175336 x s y a h1 h2)). Qed.
Lemma lem5175348 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) (h2 : term96 s y a) : term462.
Proof. exact (fun h0 : ~ False => @lem5175347 x s y a h1 h2). Qed.
Lemma lem5175350 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5175351 : term462 = False.
Proof. exact (@lem5175350 False). Qed.
Lemma lem5175352 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term218 x s y a) (h2 : term96 s y a) : False.
Proof. exact (EQ_MP (@lem5175351) (@lem5175348 x s y a h1 h2)). Qed.
Lemma lem5175408 (s : real -> Prop) (x : real) (a : real) (h1 : term96 s x a) : @IN real x s.
Proof. exact (proj1 (@lem5173998 s x a h1)). Qed.
Lemma lem5175409 (s : real -> Prop) (x : real) (a : real) (h1 : term96 s x a) : term403 x s.
Proof. exact (fun h0 : term179 x s => @lem5175408 s x a h1). Qed.
Lemma lem5175411 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5175412 (x : real) (s : real -> Prop) : (term403 x s) = (@IN real x s).
Proof. exact (@lem5175411 (@IN real x s)). Qed.
Lemma lem5175413 (s : real -> Prop) (x : real) (a : real) (h1 : term96 s x a) : @IN real x s.
Proof. exact (EQ_MP (@lem5175412 x s) (@lem5175409 s x a h1)). Qed.
Lemma lem5175419 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5175420 (a : real) (_67567 : real) (s : real -> Prop) : (term97 s _67567 a) = (term404 a _67567 s).
Proof. exact (@lem5175419 (real_le _67567 a) (term179 _67567 s)). Qed.
Lemma lem5175426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5175427 (a : real) (_67567 : real) (s : real -> Prop) : (term405 s _67567 a) = (term406 a _67567 s).
Proof. exact (MK_COMB (@lem5175426) (@lem5175420 a _67567 s)). Qed.
Lemma lem5175433 (a : real) (_67567 : real) (s : real -> Prop) : (term404 a _67567 s) = (term404 a _67567 s).
Proof. exact (eq_refl (term404 a _67567 s)). Qed.
Lemma lem5175434 (a : real) (_67567 : real) (s : real -> Prop) : ((term97 s _67567 a) = (term404 a _67567 s)) = ((term404 a _67567 s) = (term404 a _67567 s)).
Proof. exact (MK_COMB (@lem5175427 a _67567 s) (@lem5175433 a _67567 s)). Qed.
Lemma lem5175436 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5175437 (x : Prop) : (x = x) = True.
Proof. exact (@lem5175436 Prop x). Qed.
Lemma lem5175438 (a : real) (_67567 : real) (s : real -> Prop) : ((term404 a _67567 s) = (term404 a _67567 s)) = True.
Proof. exact (@lem5175437 (term404 a _67567 s)). Qed.
Lemma lem5175439 (a : real) (_67567 : real) (s : real -> Prop) : ((term97 s _67567 a) = (term404 a _67567 s)) = True.
Proof. exact (TRANS (@lem5175434 a _67567 s) (@lem5175438 a _67567 s)). Qed.
Lemma lem5175440 (a : real) (_67567 : real) (s : real -> Prop) : True = ((term97 s _67567 a) = (term404 a _67567 s)).
Proof. exact (SYM (@lem5175439 a _67567 s)). Qed.
Lemma lem5175441 (a : real) (_67567 : real) (s : real -> Prop) : (term97 s _67567 a) = (term404 a _67567 s).
Proof. exact (EQ_MP (@lem5175440 a _67567 s) (@lem0)). Qed.
Lemma lem5175442 (_67567 : real) (x : real) (s : real -> Prop) (a : real) (h1 : term254 x s a) : term404 a _67567 s.
Proof. exact (EQ_MP (@lem5175441 a _67567 s) (@lem5174729 _67567 x s a h1)). Qed.
Lemma lem5175444 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5175445 (s : real -> Prop) (_67567 : real) (a : real) : (term404 a _67567 s) = (term408 s _67567 a).
Proof. exact (@lem5175444 (term179 _67567 s) (real_le _67567 a)). Qed.
Lemma lem5175447 (a : Prop) : (term409 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5175448 (_67567 : real) (s : real -> Prop) : (term410 _67567 s) = (@IN real _67567 s).
Proof. exact (@lem5175447 (@IN real _67567 s)). Qed.
Lemma lem5175449 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5175450 (_67567 : real) (s : real -> Prop) : (term411 _67567 s) = (term412 _67567 s).
Proof. exact (MK_COMB (@lem5175449) (@lem5175448 _67567 s)). Qed.
Lemma lem5175451 (_67567 : real) (a : real) : (real_le _67567 a) = (real_le _67567 a).
Proof. exact (eq_refl (real_le _67567 a)). Qed.
Lemma lem5175452 (s : real -> Prop) (_67567 : real) (a : real) : (term408 s _67567 a) = (term89 s _67567 a).
Proof. exact (MK_COMB (@lem5175450 _67567 s) (@lem5175451 _67567 a)). Qed.
Lemma lem5175453 (s : real -> Prop) (_67567 : real) (a : real) : (term404 a _67567 s) = (term89 s _67567 a).
Proof. exact (TRANS (@lem5175445 s _67567 a) (@lem5175452 s _67567 a)). Qed.
Lemma lem5175456 (_67567 : real) (x : real) (s : real -> Prop) (a : real) (h1 : term254 x s a) : term89 s _67567 a.
Proof. exact (EQ_MP (@lem5175453 s _67567 a) (@lem5175442 _67567 x s a h1)). Qed.
Lemma lem5175457 (x : real) (s : real -> Prop) (a : real) (h1 : term254 x s a) : term89 s x a.
Proof. exact (@lem5175456 x x s a h1). Qed.
Lemma lem5175460 (x : real) (s : real -> Prop) (a : real) (h1 : term96 s x a) (h2 : term254 x s a) : real_le x a.
Proof. exact (@lem5175457 x s a h2 (@lem5175413 s x a h1)). Qed.
Lemma lem5175461 (x : real) (s : real -> Prop) (a : real) (h1 : term96 s x a) (h2 : term254 x s a) : term413 x a.
Proof. exact (fun h0 : term391 x a => @lem5175460 x s a h1 h2). Qed.
Lemma lem5175463 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5175464 (x : real) (a : real) : (term413 x a) = (real_le x a).
Proof. exact (@lem5175463 (real_le x a)). Qed.
Lemma lem5175465 (x : real) (s : real -> Prop) (a : real) (h1 : term96 s x a) (h2 : term254 x s a) : real_le x a.
Proof. exact (EQ_MP (@lem5175464 x a) (@lem5175461 x s a h1 h2)). Qed.
Lemma lem5175468 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5175470 (x : real) (a : real) : (term391 x a) = (term463 x a).
Proof. exact (@lem5175468 (real_le x a)). Qed.
Lemma lem5175473 (s : real -> Prop) (x : real) (a : real) (h1 : term96 s x a) : term463 x a.
Proof. exact (EQ_MP (@lem5175470 x a) (@lem5174733 s x a h1)). Qed.
Lemma lem5175476 (x : real) (s : real -> Prop) (a : real) (h1 : term96 s x a) (h2 : term254 x s a) : False.
Proof. exact (@lem5175473 s x a h1 (@lem5175465 x s a h1 h2)). Qed.
Lemma lem5175477 (x : real) (s : real -> Prop) (a : real) (h1 : term96 s x a) (h2 : term254 x s a) : term462.
Proof. exact (fun h0 : ~ False => @lem5175476 x s a h1 h2). Qed.
Lemma lem5175479 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5175480 : term462 = False.
Proof. exact (@lem5175479 False). Qed.
Lemma lem5175481 (x : real) (s : real -> Prop) (a : real) (h1 : term96 s x a) (h2 : term254 x s a) : False.
Proof. exact (EQ_MP (@lem5175480) (@lem5175477 x s a h1 h2)). Qed.
Lemma lem5175537 (x : real) (s : real -> Prop) (a : real) (h1 : term254 x s a) : @IN real a s.
Proof. exact (proj1 (@lem5173994 x s a h1)). Qed.
Lemma lem5175538 (x : real) (s : real -> Prop) (a : real) (h1 : term254 x s a) : term403 a s.
Proof. exact (fun h0 : term179 a s => @lem5175537 x s a h1). Qed.
Lemma lem5175540 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5175541 (a : real) (s : real -> Prop) : (term403 a s) = (@IN real a s).
Proof. exact (@lem5175540 (@IN real a s)). Qed.
Lemma lem5175542 (x : real) (s : real -> Prop) (a : real) (h1 : term254 x s a) : @IN real a s.
Proof. exact (EQ_MP (@lem5175541 a s) (@lem5175538 x s a h1)). Qed.
Lemma lem5175544 (_67571 : real) (h1 : term68) : real_le _67571 _67571.
Proof. exact (EQ_MP (@lem5174554 _67571) (@lem5174553 _67571 h1)). Qed.
Lemma lem5175545 (a : real) (h1 : term68) : real_le a a.
Proof. exact (@lem5175544 a h1). Qed.
Lemma lem5175546 (a : real) (h1 : term68) : term464 a.
Proof. exact (fun h0 : term465 a => @lem5175545 a h1). Qed.
Lemma lem5175548 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5175549 (a : real) : (term464 a) = (real_le a a).
Proof. exact (@lem5175548 (real_le a a)). Qed.
Lemma lem5175550 (a : real) (h1 : term68) : real_le a a.
Proof. exact (EQ_MP (@lem5175549 a) (@lem5175546 a h1)). Qed.
Lemma lem5175552 (a : Prop) (b : Prop) : (term466 a b) = (term467 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5175553 (s : real -> Prop) (a : real) (_67577 : real) : (term110 s a _67577) = (term109 s a _67577).
Proof. exact (@lem5175552 (@IN real _67577 s) (real_le a _67577)). Qed.
Lemma lem5175555 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5175556 (s : real -> Prop) (a : real) (_67577 : real) : (term109 s a _67577) = (term468 s a _67577).
Proof. exact (@lem5175555 (term92 s a _67577)). Qed.
Lemma lem5175557 (s : real -> Prop) (a : real) (_67577 : real) : (term110 s a _67577) = (term468 s a _67577).
Proof. exact (TRANS (@lem5175553 s a _67577) (@lem5175556 s a _67577)). Qed.
Lemma lem5175559 (x : real) (s : real -> Prop) (a : real) (h1 : term68) (h2 : term254 x s a) : term469 s a.
Proof. exact (conj (@lem5175542 x s a h2) (@lem5175550 a h1)). Qed.
Lemma lem5175561 (_67577 : real) (s : real -> Prop) (a : real) (h1 : term119 s a) : term468 s a _67577.
Proof. exact (EQ_MP (@lem5175557 s a _67577) (@lem5174789 _67577 s a h1)). Qed.
Lemma lem5175562 (s : real -> Prop) (a : real) (h1 : term119 s a) : term470 s a.
Proof. exact (@lem5175561 a s a h1). Qed.
Lemma lem5175565 (x : real) (s : real -> Prop) (a : real) (h1 : term119 s a) (h2 : term68) (h3 : term254 x s a) : False.
Proof. exact (@lem5175562 s a h1 (@lem5175559 x s a h2 h3)). Qed.
Lemma lem5175566 (x : real) (s : real -> Prop) (a : real) (h1 : term119 s a) (h2 : term68) (h3 : term254 x s a) : term462.
Proof. exact (fun h0 : ~ False => @lem5175565 x s a h1 h2 h3). Qed.
Lemma lem5175568 (p : Prop) : (term402 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5175569 : term462 = False.
Proof. exact (@lem5175568 False). Qed.
Lemma lem5175570 (x : real) (s : real -> Prop) (a : real) (h1 : term119 s a) (h2 : term68) (h3 : term254 x s a) : False.
Proof. exact (EQ_MP (@lem5175569) (@lem5175566 x s a h1 h2 h3)). Qed.
Lemma lem5175571 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term179 a s) (h3 : term218 x s y a) : (term179 a s) = False.
Proof. exact (prop_ext (fun h4 : term179 a s => @lem5175223 x s y a h1 h2 h3) (fun h4 : False => @lem5174623 a s h2)). Qed.
Lemma lem5175572 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term179 a s) (h3 : term218 x s y a) : False.
Proof. exact (EQ_MP (@lem5175571 x s y a h1 h2 h3) (@lem5174623 a s h2)). Qed.
Lemma lem5175573 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term179 a s) (h3 : term218 x s y a) : (term179 a s) = False.
Proof. exact (prop_ext (fun h4 : term179 a s => @lem5175572 x s y a h1 h2 h3) (fun h4 : False => @lem5174114 a s h2)). Qed.
Lemma lem5175574 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term179 a s) (h3 : term218 x s y a) : False.
Proof. exact (EQ_MP (@lem5175573 x s y a h1 h2 h3) (@lem5174114 a s h2)). Qed.
Lemma lem5175575 (x : real) (s : real -> Prop) (a : real) (h1 : term119 s a) (h2 : term68) (h3 : term254 x s a) : (term119 s a) = False.
Proof. exact (prop_ext (fun h4 : term119 s a => @lem5175570 x s a h1 h2 h3) (fun h4 : False => @lem5174462 s a h1)). Qed.
Lemma lem5175576 (x : real) (s : real -> Prop) (a : real) (h1 : term119 s a) (h2 : term68) (h3 : term254 x s a) : False.
Proof. exact (EQ_MP (@lem5175575 x s a h1 h2 h3) (@lem5174462 s a h1)). Qed.
Lemma lem5175577 (x : real) (s : real -> Prop) (a : real) (h1 : term119 s a) (h2 : term68) (h3 : term254 x s a) : term68 = False.
Proof. exact (prop_ext (fun h4 : term68 => @lem5175576 x s a h1 h2 h3) (fun h4 : False => @lem5174376 h2)). Qed.
Lemma lem5175578 (x : real) (s : real -> Prop) (a : real) (h1 : term119 s a) (h2 : term68) (h3 : term254 x s a) : False.
Proof. exact (EQ_MP (@lem5175577 x s a h1 h2 h3) (@lem5174376 h2)). Qed.
Lemma lem5175579 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term179 a s) (h3 : term218 x s y a) : (term179 a s) = False.
Proof. exact (prop_ext (fun h4 : term179 a s => @lem5175574 x s y a h1 h2 h3) (fun h4 : False => @lem5174114 a s h2)). Qed.
Lemma lem5175580 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term179 a s) (h3 : term218 x s y a) : False.
Proof. exact (EQ_MP (@lem5175579 x s y a h1 h2 h3) (@lem5174114 a s h2)). Qed.
Lemma lem5175581 (x : real) (s : real -> Prop) (a : real) (h1 : term68) (h2 : term254 x s a) : False.
Proof. exact (or_elim (@lem5173995 x s a h2) (fun h0 : term96 s x a => @lem5175481 x s a h0 h2) (fun h0 : term119 s a => @lem5175578 x s a h0 h1 h2)). Qed.
Lemma lem5175582 (x : real) (s : real -> Prop) (y : real) (a : real) (h1 : term14) (h2 : term218 x s y a) : False.
Proof. exact (or_elim (@lem5173984 x s y a h2) (fun h0 : term179 a s => @lem5175580 x s y a h1 h0 h2) (fun h0 : term96 s y a => @lem5175352 x s y a h2 h0)). Qed.
Lemma lem5175583 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term14) (h2 : term68) (h3 : term319 y x s a) : False.
Proof. exact (or_elim (@lem5173976 y x s a h3) (fun h0 : term218 x s y a => @lem5175582 x s y a h1 h0) (fun h0 : term254 x s a => @lem5175581 x s a h2 h0)). Qed.
Lemma lem5175584 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term14) (h2 : term68) (h3 : term319 y x s a) : (term319 y x s a) = False.
Proof. exact (prop_ext (fun h4 : term319 y x s a => @lem5175583 y x s a h1 h2 h3) (fun h4 : False => @lem5173975 y x s a h3)). Qed.
Lemma lem5175585 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term14) (h2 : term68) (h3 : term319 y x s a) : False.
Proof. exact (EQ_MP (@lem5175584 y x s a h1 h2 h3) (@lem5173975 y x s a h3)). Qed.
Lemma lem5175586 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term14) (h2 : term68) (h3 : term319 y x s a) : term68 = False.
Proof. exact (prop_ext (fun h4 : term68 => @lem5175585 y x s a h1 h2 h3) (fun h4 : False => @lem5173826 h2)). Qed.
Lemma lem5175587 (y : real) (x : real) (s : real -> Prop) (a : real) (h1 : term14) (h2 : term68) (h3 : term319 y x s a) : False.
Proof. exact (EQ_MP (@lem5175586 y x s a h1 h2 h3) (@lem5173826 h2)). Qed.
Lemma lem5175588 (x : real) (s : real -> Prop) (a : real) (h1 : term14) (h2 : term68) (h3 : term322 x s a) : False.
Proof. exact (ex_elim (@lem5173717 x s a h3) (fun y : real => fun h0 : term321 x s a y => @lem5175587 y x s a h1 h2 h0)). Qed.
Lemma lem5175589 (s : real -> Prop) (a : real) (h1 : term14) (h2 : term68) (h3 : term324 s a) : False.
Proof. exact (ex_elim (@lem5173716 s a h3) (fun x : real => fun h0 : term323 s a x => @lem5175588 x s a h1 h2 h0)). Qed.
Lemma lem5175590 (a : real) (h1 : term14) (h2 : term68) (h3 : term61 a) : False.
Proof. exact (ex_elim (@lem5173322 a h3) (fun s : real -> Prop => fun h0 : term325 a s => @lem5175589 s a h1 h2 h0)). Qed.
Lemma lem5175591 (a : real) (h1 : term14) (h2 : term68) (h3 : term61 a) : term68 = False.
Proof. exact (prop_ext (fun h4 : term68 => @lem5175590 a h1 h2 h3) (fun h4 : False => @lem5173715 h2)). Qed.
Lemma lem5175592 (a : real) (h1 : term14) (h2 : term68) (h3 : term61 a) : False.
Proof. exact (EQ_MP (@lem5175591 a h1 h2 h3) (@lem5173715 h2)). Qed.
Lemma lem5175593 (a : real) (h1 : term14) (h2 : term61 a) : term66.
Proof. exact (fun h0 : term68 => @lem5175592 a h1 h0 h2). Qed.
Lemma lem5175594 : term66 = term67.
Proof. exact (@lem69 term68). Qed.
Lemma lem5175595 (a : real) (h1 : term14) (h2 : term61 a) : term67.
Proof. exact (EQ_MP (@lem5175594) (@lem5175593 a h1 h2)). Qed.
Lemma lem5175596 (a : real) (h1 : term14) (h2 : term61 a) : term71.
Proof. exact (fun h0 : term88 => @lem5175595 a h1 h2). Qed.
Lemma lem5175597 (a : real) (h1 : term61 a) : term74.
Proof. exact (fun h0 : term14 => @lem5175596 a h0 h1). Qed.
Lemma lem5175598 (a : real) : term76 a.
Proof. exact (fun h0 : term61 a => @lem5175597 a h0). Qed.
Lemma lem5175603 : term80.
Proof. exact (fun a : real => @lem5175598 a). Qed.
Lemma lem5175604 : term79.
Proof. exact (EQ_MP (@lem5172596) (@lem5175603)). Qed.
Lemma lem5175605 (a : real) : term471 a.
Proof. exact (@lem5175604 a). Qed.
Lemma lem5175606 (a : real) : (term471 a) = (term62 a).
Proof. exact (eq_refl (term471 a)). Qed.
Lemma lem5175607 (a : real) : term62 a.
Proof. exact (EQ_MP (@lem5175606 a) (@lem5175605 a)). Qed.
Lemma lem5175609 (a : real) : term62 a.
Proof. exact (@lem5172260 a (@lem5175607 a)). Qed.
Lemma lem5175610 (a : real) (h1 : term61 a) : term73.
Proof. exact (@lem5175609 a (@lem5172245 a h1)). Qed.
Lemma lem5175611 (a : real) (h1 : term61 a) : term70.
Proof. exact (@lem5175610 a h1 (@lem1339379)). Qed.
Lemma lem5175612 (a : real) (h1 : term61 a) : term66.
Proof. exact (@lem5175611 a h1 (@lem1339577)). Qed.
Lemma lem5175613 (a : real) (h1 : term61 a) : False.
Proof. exact (@lem5175612 a h1 (@lem1339240)). Qed.
Lemma lem5175614 (a : real) (h1 : term61 a) : (term61 a) = False.
Proof. exact (prop_ext (fun h2 : term61 a => @lem5175613 a h1) (fun h2 : False => @lem5172245 a h1)). Qed.
Lemma lem5175615 (a : real) (h1 : term61 a) : False.
Proof. exact (EQ_MP (@lem5175614 a h1) (@lem5172245 a h1)). Qed.
Lemma lem5175616 (a : real) : term60 a.
Proof. exact (fun h0 : term61 a => @lem5175615 a h0). Qed.
Lemma lem5175617 (a : real) : term58 a.
Proof. exact (EQ_MP (@lem5172244 a) (@lem5175616 a)). Qed.
Lemma lem5175618 (a : real) : term57 a.
Proof. exact (EQ_MP (@lem5172240 a) (@lem5175617 a)). Qed.
