Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_REM_EQ_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import INT_LET_TRANS_spec.
Require Import INT_LT_REFL_spec.
Require Import INT_LT_REM_spec.
Require Import INT_REM_0_spec.
Require Import INT_REM_POS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem2403254 (p : Prop) (q : Prop) (r : Prop) : (term0 p q r) = (term1 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem2403255 (y : int) (x : int) (z : int) : (term2 y x z) = (term3 y x z).
Proof. exact (@lem2403254 (int_le x y) (int_lt y z) (int_lt x z)). Qed.
Lemma lem2403260 (y : int) (x : int) : (term4 y x) = (term5 y x).
Proof. exact (fun_ext (fun z : int => @lem2403255 y x z)). Qed.
Lemma lem2403261 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2403262 (y : int) (x : int) : (term6 y x) = (term7 y x).
Proof. exact (MK_COMB (@lem2403261) (@lem2403260 y x)). Qed.
Lemma lem2403267 (x : int) : (term8 x) = (term9 x).
Proof. exact (fun_ext (fun y : int => @lem2403262 y x)). Qed.
Lemma lem2403268 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2403269 (x : int) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem2403268) (@lem2403267 x)). Qed.
Lemma lem2403274 : term12 = term13.
Proof. exact (fun_ext (fun x : int => @lem2403269 x)). Qed.
Lemma lem2403275 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2403276 : term14 = term15.
Proof. exact (MK_COMB (@lem2403275) (@lem2403274)). Qed.
Lemma lem2403281 : term15.
Proof. exact (EQ_MP (@lem2403276) (@lem2302158)). Qed.
Lemma lem2403282 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem2403283 (x : int) (h1 : term15) : term16 x.
Proof. exact (@lem2403282 h1 x). Qed.
Lemma lem2403284 (x : int) : (term16 x) = (term11 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem2403285 (x : int) (h1 : term15) : term11 x.
Proof. exact (EQ_MP (@lem2403284 x) (@lem2403283 x h1)). Qed.
Lemma lem2403286 (x : int) (y : int) (h1 : term15) : term17 x y.
Proof. exact (@lem2403285 x h1 y). Qed.
Lemma lem2403287 (y : int) (x : int) : (term17 x y) = (term7 y x).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem2403288 (y : int) (x : int) (h1 : term15) : term7 y x.
Proof. exact (EQ_MP (@lem2403287 y x) (@lem2403286 x y h1)). Qed.
Lemma lem2403289 (y : int) (x : int) (z : int) (h1 : term15) : term18 y x z.
Proof. exact (@lem2403288 y x h1 z). Qed.
Lemma lem2403290 (y : int) (x : int) (z : int) : (term18 y x z) = (term3 y x z).
Proof. exact (eq_refl (term18 y x z)). Qed.
Lemma lem2403291 (y : int) (x : int) (z : int) (h1 : term15) : term3 y x z.
Proof. exact (EQ_MP (@lem2403290 y x z) (@lem2403289 y x z h1)). Qed.
Lemma lem2403292 (x : int) (y : int) (h1 : int_le x y) : int_le x y.
Proof. exact (h1). Qed.
Lemma lem2403293 (z : int) (x : int) (y : int) (h1 : term15) (h2 : int_le x y) : term19 y x z.
Proof. exact (@lem2403291 y x z h1 (@lem2403292 x y h2)). Qed.
Lemma lem2403294 (z : int) (x : int) (y : int) (h1 : int_le x y) : term20 y x z.
Proof. exact (fun h0 : term15 => @lem2403293 z x y h0 h1). Qed.
Lemma lem2403295 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem2403296 (z : int) (x : int) (y : int) (h1 : term15) (h2 : int_le x y) : term19 y x z.
Proof. exact (@lem2403294 z x y h2 (@lem2403295 h1)). Qed.
Lemma lem2403297 (y : int) (x : int) (z : int) (h1 : term15) : term3 y x z.
Proof. exact (fun h0 : int_le x y => @lem2403296 z x y h1 h0). Qed.
Lemma lem2403298 (y : int) (x : int) (h1 : term15) : term7 y x.
Proof. exact (fun z : int => @lem2403297 y x z h1). Qed.
Lemma lem2403299 (y : int) (h1 : term15) : term21 y.
Proof. exact (fun x : int => @lem2403298 y x h1). Qed.
Lemma lem2403300 (h1 : term15) : term22.
Proof. exact (fun y : int => @lem2403299 y h1). Qed.
Lemma lem2403301 : term23.
Proof. exact (fun h0 : term15 => @lem2403300 h0). Qed.
Lemma lem2403302 : term22.
Proof. exact (@lem2403301 (@lem2403281)). Qed.
Lemma lem2403303 (y : int) : term24 y.
Proof. exact (@lem2403302 y). Qed.
Lemma lem2403304 (y : int) : (term24 y) = (term21 y).
Proof. exact (eq_refl (term24 y)). Qed.
Lemma lem2403305 (y : int) : term21 y.
Proof. exact (EQ_MP (@lem2403304 y) (@lem2403303 y)). Qed.
Lemma lem2403306 (y : int) (x : int) : term25 y x.
Proof. exact (@lem2403305 y x). Qed.
Lemma lem2403307 (y : int) (x : int) : (term25 y x) = (term7 y x).
Proof. exact (eq_refl (term25 y x)). Qed.
Lemma lem2403308 (y : int) (x : int) : term7 y x.
Proof. exact (EQ_MP (@lem2403307 y x) (@lem2403306 y x)). Qed.
Lemma lem2403309 (y : int) (x : int) (z : int) : term18 y x z.
Proof. exact (@lem2403308 y x z). Qed.
Lemma lem2403310 (y : int) (x : int) (z : int) : (term18 y x z) = (term3 y x z).
Proof. exact (eq_refl (term18 y x z)). Qed.
Lemma lem2403312 (x : int) : term26 x.
Proof. exact (@lem2403240 x). Qed.
Lemma lem2403313 (x : int) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem2403314 (x : int) : term27 x.
Proof. exact (EQ_MP (@lem2403313 x) (@lem2403312 x)). Qed.
Lemma lem2403315 (x : int) (n : int) : term28 x n.
Proof. exact (@lem2403314 x n). Qed.
Lemma lem2403316 (x : int) (n : int) : (term28 x n) = (term29 x n).
Proof. exact (eq_refl (term28 x n)). Qed.
Lemma lem2403317 (x : int) (n : int) : term29 x n.
Proof. exact (EQ_MP (@lem2403316 x n) (@lem2403315 x n)). Qed.
Lemma lem2403318 (x : int) (n : int) : (term29 x n) = ((term29 x n) = True).
Proof. exact (@lem7 (term29 x n)). Qed.
Lemma lem2403320 (n : int) : term30 n.
Proof. exact (@lem9784 (n = term31)). Qed.
Lemma lem2403321 (n : int) : (term30 n) = (term32 n).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem2403322 (n : int) : term32 n.
Proof. exact (EQ_MP (@lem2403321 n) (@lem2403320 n)). Qed.
Lemma lem2403324 (n : int) (h1 : term33 n) : term33 n.
Proof. exact (h1). Qed.
Lemma lem2403325 (x : int) : term34 x.
Proof. exact (@lem2304778 x). Qed.
Lemma lem2403326 (x : int) : (term34 x) = (term35 x).
Proof. exact (eq_refl (term34 x)). Qed.
Lemma lem2403327 (x : int) : term35 x.
Proof. exact (EQ_MP (@lem2403326 x) (@lem2403325 x)). Qed.
Lemma lem2403328 (x : int) : term36 x.
Proof. exact (@lem82 (int_lt x x)). Qed.
Lemma lem2403330 (m : int) : term37 m.
Proof. exact (@lem2396893 m). Qed.
Lemma lem2403331 (m : int) : (term37 m) = ((term38 m) = m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem2403338 (n : int) (h1 : n = term31) : n = term31.
Proof. exact (h1). Qed.
Lemma lem2403339 (m : int) : (rem m) = (rem m).
Proof. exact (eq_refl (rem m)). Qed.
Lemma lem2403340 (m : int) (n : int) (h1 : n = term31) : (rem m n) = (term38 m).
Proof. exact (MK_COMB (@lem2403339 m) (@lem2403338 n h1)). Qed.
Lemma lem2403342 (m : int) : (term38 m) = m.
Proof. exact (EQ_MP (@lem2403331 m) (@lem2403330 m)). Qed.
Lemma lem2403343 (m : int) (n : int) (h1 : n = term31) : (rem m n) = m.
Proof. exact (TRANS (@lem2403340 m n h1) (@lem2403342 m)). Qed.
Lemma lem2403344 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem2403345 (m : int) (n : int) (h1 : n = term31) : (term39 m n) = (int_lt m).
Proof. exact (MK_COMB (@lem2403344) (@lem2403343 m n h1)). Qed.
Lemma lem2403347 (n : int) (h1 : n = term31) : n = term31.
Proof. exact (h1). Qed.
Lemma lem2403348 (m : int) (n : int) (h1 : n = term31) : (term40 m n) = (term41 m).
Proof. exact (MK_COMB (@lem2403345 m n h1) (@lem2403347 n h1)). Qed.
Lemma lem2403351 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2403352 (m : int) (n : int) (h1 : n = term31) : (term42 m n) = (term43 m).
Proof. exact (MK_COMB (@lem2403351) (@lem2403348 m n h1)). Qed.
Lemma lem2403360 (n : int) (h1 : n = term31) : n = term31.
Proof. exact (h1). Qed.
Lemma lem2403361 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2403362 (n : int) (h1 : n = term31) : (term45 n) = term46.
Proof. exact (MK_COMB (@lem2403361) (@lem2403360 n h1)). Qed.
Lemma lem2403364 (x : int) : (int_lt x x) = False.
Proof. exact (@lem2403328 x (@lem2403327 x)). Qed.
Lemma lem2403365 : term46 = False.
Proof. exact (@lem2403364 term31). Qed.
Lemma lem2403366 (n : int) (h1 : n = term31) : (term45 n) = False.
Proof. exact (TRANS (@lem2403362 n h1) (@lem2403365)). Qed.
Lemma lem2403367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2403368 (n : int) (h1 : n = term31) : (term47 n) = (or False).
Proof. exact (MK_COMB (@lem2403367) (@lem2403366 n h1)). Qed.
Lemma lem2403374 (n : int) (h1 : n = term31) : n = term31.
Proof. exact (h1). Qed.
Lemma lem2403375 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2403376 (n : int) (h1 : n = term31) : (@eq int n) = term48.
Proof. exact (MK_COMB (@lem2403375) (@lem2403374 n h1)). Qed.
Lemma lem2403377 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem2403378 (n : int) (h1 : n = term31) : (n = term31) = (term31 = term31).
Proof. exact (MK_COMB (@lem2403376 n h1) (@lem2403377)). Qed.
Lemma lem2403380 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2403381 (x : int) : (x = x) = True.
Proof. exact (@lem2403380 int x). Qed.
Lemma lem2403382 : (term31 = term31) = True.
Proof. exact (@lem2403381 term31). Qed.
Lemma lem2403383 (n : int) (h1 : n = term31) : (n = term31) = True.
Proof. exact (TRANS (@lem2403378 n h1) (@lem2403382)). Qed.
Lemma lem2403384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2403385 (n : int) (h1 : n = term31) : (term49 n) = (and True).
Proof. exact (MK_COMB (@lem2403384) (@lem2403383 n h1)). Qed.
Lemma lem2403388 (m : int) : (term41 m) = (term41 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem2403389 (m : int) (n : int) (h1 : n = term31) : (term50 n m) = (term51 m).
Proof. exact (MK_COMB (@lem2403385 n h1) (@lem2403388 m)). Qed.
Lemma lem2403391 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2403392 (m : int) : (term51 m) = (term41 m).
Proof. exact (@lem2403391 (term41 m)). Qed.
Lemma lem2403395 (m : int) (n : int) (h1 : n = term31) : (term50 n m) = (term41 m).
Proof. exact (TRANS (@lem2403389 m n h1) (@lem2403392 m)). Qed.
Lemma lem2403396 (m : int) (n : int) (h1 : n = term31) : (term52 n m) = (term53 m).
Proof. exact (MK_COMB (@lem2403368 n h1) (@lem2403395 m n h1)). Qed.
Lemma lem2403398 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem2403399 (m : int) : (term53 m) = (term41 m).
Proof. exact (@lem2403398 (term41 m)). Qed.
Lemma lem2403402 (m : int) (n : int) (h1 : n = term31) : (term52 n m) = (term41 m).
Proof. exact (TRANS (@lem2403396 m n h1) (@lem2403399 m)). Qed.
Lemma lem2403403 (m : int) (n : int) (h1 : n = term31) : ((term40 m n) = (term52 n m)) = ((term41 m) = (term41 m)).
Proof. exact (MK_COMB (@lem2403352 m n h1) (@lem2403402 m n h1)). Qed.
Lemma lem2403405 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2403406 (x : Prop) : (x = x) = True.
Proof. exact (@lem2403405 Prop x). Qed.
Lemma lem2403407 (m : int) : ((term41 m) = (term41 m)) = True.
Proof. exact (@lem2403406 (term41 m)). Qed.
Lemma lem2403408 (m : int) (n : int) (h1 : n = term31) : ((term40 m n) = (term52 n m)) = True.
Proof. exact (TRANS (@lem2403403 m n h1) (@lem2403407 m)). Qed.
Lemma lem2403409 (m : int) (n : int) (h1 : n = term31) : True = ((term40 m n) = (term52 n m)).
Proof. exact (SYM (@lem2403408 m n h1)). Qed.
Lemma lem2403410 (m : int) (n : int) (h1 : n = term31) : (term40 m n) = (term52 n m).
Proof. exact (EQ_MP (@lem2403409 m n h1) (@lem0)). Qed.
Lemma lem2403419 (n : int) : term54 n.
Proof. exact (@lem82 (n = term31)). Qed.
Lemma lem2403443 (n : int) (h1 : term33 n) : (n = term31) = False.
Proof. exact (@lem2403419 n (@lem2403324 n h1)). Qed.
Lemma lem2403444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2403445 (n : int) (h1 : term33 n) : (term49 n) = (and False).
Proof. exact (MK_COMB (@lem2403444) (@lem2403443 n h1)). Qed.
Lemma lem2403448 (m : int) : (term41 m) = (term41 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem2403449 (m : int) (n : int) (h1 : term33 n) : (term50 n m) = (term55 m).
Proof. exact (MK_COMB (@lem2403445 n h1) (@lem2403448 m)). Qed.
Lemma lem2403451 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem2403452 (m : int) : (term55 m) = False.
Proof. exact (@lem2403451 (term41 m)). Qed.
Lemma lem2403453 (m : int) (n : int) (h1 : term33 n) : (term50 n m) = False.
Proof. exact (TRANS (@lem2403449 m n h1) (@lem2403452 m)). Qed.
Lemma lem2403454 (n : int) : (term47 n) = (term47 n).
Proof. exact (eq_refl (term47 n)). Qed.
Lemma lem2403455 (m : int) (n : int) (h1 : term33 n) : (term52 n m) = (term56 n).
Proof. exact (MK_COMB (@lem2403454 n) (@lem2403453 m n h1)). Qed.
Lemma lem2403457 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem2403458 (n : int) : (term56 n) = (term45 n).
Proof. exact (@lem2403457 (term45 n)). Qed.
Lemma lem2403461 (m : int) (n : int) (h1 : term33 n) : (term52 n m) = (term45 n).
Proof. exact (TRANS (@lem2403455 m n h1) (@lem2403458 n)). Qed.
Lemma lem2403462 (m : int) (n : int) : (term42 m n) = (term42 m n).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem2403463 (m : int) (n : int) (h1 : term33 n) : ((term40 m n) = (term52 n m)) = ((term40 m n) = (term45 n)).
Proof. exact (MK_COMB (@lem2403462 m n) (@lem2403461 m n h1)). Qed.
Lemma lem2403470 (m : int) (n : int) (h1 : term33 n) : ((term40 m n) = (term45 n)) = ((term40 m n) = (term52 n m)).
Proof. exact (SYM (@lem2403463 m n h1)). Qed.
Lemma lem2403476 (x : int) (n : int) : (term29 x n) = True.
Proof. exact (EQ_MP (@lem2403318 x n) (@lem2403317 x n)). Qed.
Lemma lem2403477 (m : int) (n : int) : (term29 m n) = True.
Proof. exact (@lem2403476 m n). Qed.
Lemma lem2403478 (m : int) (n : int) : True = (term29 m n).
Proof. exact (SYM (@lem2403477 m n)). Qed.
Lemma lem2403479 (m : int) (n : int) : term29 m n.
Proof. exact (EQ_MP (@lem2403478 m n) (@lem0)). Qed.
Lemma lem2403481 (y : int) (x : int) (z : int) : term3 y x z.
Proof. exact (EQ_MP (@lem2403310 y x z) (@lem2403309 y x z)). Qed.
Lemma lem2403482 (m : int) (n : int) : term57 m n.
Proof. exact (@lem2403481 (rem m n) term31 n). Qed.
Lemma lem2403483 (a : int) : term58 a.
Proof. exact (@lem2394837 a). Qed.
Lemma lem2403484 (a : int) : (term58 a) = (term59 a).
Proof. exact (eq_refl (term58 a)). Qed.
Lemma lem2403485 (a : int) : term59 a.
Proof. exact (EQ_MP (@lem2403484 a) (@lem2403483 a)). Qed.
Lemma lem2403486 (a : int) (b : int) : term60 a b.
Proof. exact (@lem2403485 a b). Qed.
Lemma lem2403487 (a : int) (b : int) : (term60 a b) = (term61 a b).
Proof. exact (eq_refl (term60 a b)). Qed.
Lemma lem2403488 (a : int) (b : int) : term61 a b.
Proof. exact (EQ_MP (@lem2403487 a b) (@lem2403486 a b)). Qed.
Lemma lem2403489 (b : int) (h1 : term33 b) : term33 b.
Proof. exact (h1). Qed.
Lemma lem2403490 (a : int) (b : int) (h1 : term33 b) : term62 a b.
Proof. exact (@lem2403488 a b (@lem2403489 b h1)). Qed.
Lemma lem2403491 (a : int) (b : int) : (term62 a b) = ((term62 a b) = True).
Proof. exact (@lem7 (term62 a b)). Qed.
Lemma lem2403492 (a : int) (b : int) (h1 : term33 b) : (term62 a b) = True.
Proof. exact (EQ_MP (@lem2403491 a b) (@lem2403490 a b h1)). Qed.
Lemma lem2403498 (n : int) : term54 n.
Proof. exact (@lem82 (n = term31)). Qed.
Lemma lem2403512 (a : int) (b : int) : term63 a b.
Proof. exact (fun h0 : term33 b => @lem2403492 a b h0). Qed.
Lemma lem2403513 (m : int) (n : int) : term63 m n.
Proof. exact (@lem2403512 m n). Qed.
Lemma lem2403515 (n : int) (h1 : term33 n) : (n = term31) = False.
Proof. exact (@lem2403498 n (@lem2403324 n h1)). Qed.
Lemma lem2403516 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2403517 (n : int) (h1 : term33 n) : (term33 n) = (~ False).
Proof. exact (MK_COMB (@lem2403516) (@lem2403515 n h1)). Qed.
Lemma lem2403519 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2403520 (n : int) (h1 : term33 n) : (term33 n) = True.
Proof. exact (TRANS (@lem2403517 n h1) (@lem2403519)). Qed.
Lemma lem2403521 (n : int) (h1 : term33 n) : True = (term33 n).
Proof. exact (SYM (@lem2403520 n h1)). Qed.
Lemma lem2403522 (n : int) (h1 : term33 n) : term33 n.
Proof. exact (EQ_MP (@lem2403521 n h1) (@lem0)). Qed.
Lemma lem2403523 (m : int) (n : int) (h1 : term33 n) : (term62 m n) = True.
Proof. exact (@lem2403513 m n (@lem2403522 n h1)). Qed.
Lemma lem2403524 (m : int) (n : int) (h1 : term33 n) : True = (term62 m n).
Proof. exact (SYM (@lem2403523 m n h1)). Qed.
Lemma lem2403525 (m : int) (n : int) (h1 : term33 n) : term62 m n.
Proof. exact (EQ_MP (@lem2403524 m n h1) (@lem0)). Qed.
Lemma lem2403527 (m : int) (n : int) (h1 : term33 n) : term64 m n.
Proof. exact (@lem2403482 m n (@lem2403525 m n h1)). Qed.
Lemma lem2403528 (m : int) (n : int) (h1 : term33 n) : term65 m n.
Proof. exact (conj (@lem2403527 m n h1) (@lem2403479 m n)). Qed.
Lemma lem2403529 (m : int) (n : int) : (term65 m n) = ((term40 m n) = (term45 n)).
Proof. exact (@lem32 (term40 m n) (term45 n)). Qed.
Lemma lem2403530 (m : int) (n : int) (h1 : term33 n) : (term40 m n) = (term45 n).
Proof. exact (EQ_MP (@lem2403529 m n) (@lem2403528 m n h1)). Qed.
Lemma lem2403531 (m : int) (n : int) (h1 : term33 n) : (term40 m n) = (term52 n m).
Proof. exact (EQ_MP (@lem2403470 m n h1) (@lem2403530 m n h1)). Qed.
Lemma lem2403532 (n : int) (m : int) : (term40 m n) = (term52 n m).
Proof. exact (or_elim (@lem2403322 n) (fun h0 : n = term31 => @lem2403410 m n h0) (fun h0 : term33 n => @lem2403531 m n h0)). Qed.
Lemma lem2403537 (m : int) : term66 m.
Proof. exact (fun n : int => @lem2403532 n m). Qed.
Lemma lem2403542 : term67.
Proof. exact (fun m : int => @lem2403537 m). Qed.
