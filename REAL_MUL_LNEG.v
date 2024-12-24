Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MUL_LNEG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_MUL_RNEG_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338712_spec.
Require Import thm16474_spec.
Require Import thm18392_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem1360294 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1360295 : term1 = term2.
Proof. exact (@lem1360294 term1). Qed.
Lemma lem1360296 : term2 = term1.
Proof. exact (SYM (@lem1360295)). Qed.
Lemma lem1360297 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1360300 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1360301 : term5.
Proof. exact (fun h0 : term4 => @lem1360300 h0). Qed.
Lemma lem1360302 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1360303 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1360304 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1360302 h2 (@lem1360303 h1)). Qed.
Lemma lem1360305 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1360304 h1 h0). Qed.
Lemma lem1360306 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1360307 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1360305 h1 (@lem1360306 h2)). Qed.
Lemma lem1360308 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1360307 h0 h1). Qed.
Lemma lem1360309 : term7.
Proof. exact (fun h0 : term5 => @lem1360308 h0). Qed.
Lemma lem1360312 : term5.
Proof. exact (@lem1360309 (@lem1360301)). Qed.
Lemma lem1360334 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1360335 : term8 = term9.
Proof. exact (@lem1360334 term10). Qed.
Lemma lem1360344 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1360345 : term12 = term13.
Proof. exact (MK_COMB (@lem1360344) (@lem1360335)). Qed.
Lemma lem1360348 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1360355 : term4 = term15.
Proof. exact (MK_COMB (@lem1360348) (@lem1360345)). Qed.
Lemma lem1360356 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1360357 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1360356 y x)). Qed.
Lemma lem1360358 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360359 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1360358) (@lem1360357 x)). Qed.
Lemma lem1360360 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1360359 x)). Qed.
Lemma lem1360361 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360362 : term10 = term10.
Proof. exact (MK_COMB (@lem1360361) (@lem1360360)). Qed.
Lemma lem1360363 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1360364 : term9 = term9.
Proof. exact (MK_COMB (@lem1360363) (@lem1360362)). Qed.
Lemma lem1360365 (x : real) (y : real) : ((term19 x y) = (term20 x y)) = ((term19 x y) = (term20 x y)).
Proof. exact (eq_refl ((term19 x y) = (term20 x y))). Qed.
Lemma lem1360366 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1360365 x y)). Qed.
Lemma lem1360367 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360368 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1360367) (@lem1360366 x)). Qed.
Lemma lem1360369 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1360368 x)). Qed.
Lemma lem1360370 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360371 : term24 = term24.
Proof. exact (MK_COMB (@lem1360370) (@lem1360369)). Qed.
Lemma lem1360372 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1360373 : term11 = term11.
Proof. exact (MK_COMB (@lem1360372) (@lem1360371)). Qed.
Lemma lem1360374 : term13 = term13.
Proof. exact (MK_COMB (@lem1360373) (@lem1360364)). Qed.
Lemma lem1360375 (x : real) (y : real) : ((term25 x y) = (term20 x y)) = ((term25 x y) = (term20 x y)).
Proof. exact (eq_refl ((term25 x y) = (term20 x y))). Qed.
Lemma lem1360376 (x : real) : (term26 x) = (term26 x).
Proof. exact (fun_ext (fun y : real => @lem1360375 x y)). Qed.
Lemma lem1360377 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360378 (x : real) : (term27 x) = (term27 x).
Proof. exact (MK_COMB (@lem1360377) (@lem1360376 x)). Qed.
Lemma lem1360379 : term28 = term28.
Proof. exact (fun_ext (fun x : real => @lem1360378 x)). Qed.
Lemma lem1360380 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360381 : term1 = term1.
Proof. exact (MK_COMB (@lem1360380) (@lem1360379)). Qed.
Lemma lem1360382 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1360383 : term3 = term3.
Proof. exact (MK_COMB (@lem1360382) (@lem1360381)). Qed.
Lemma lem1360384 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1360385 : term14 = term14.
Proof. exact (MK_COMB (@lem1360384) (@lem1360383)). Qed.
Lemma lem1360386 : term15 = term15.
Proof. exact (MK_COMB (@lem1360385) (@lem1360374)). Qed.
Lemma lem1360429 : term4 = term15.
Proof. exact (TRANS (@lem1360355) (@lem1360386)). Qed.
Lemma lem1360430 : term15 = term4.
Proof. exact (SYM (@lem1360429)). Qed.
Lemma lem1360431 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1360432 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1360433 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1360435 (P : real -> Prop) : (term29 P) = (term30 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1360436 (x : real) : (term31 x) = (term32 x).
Proof. exact (@lem1360435 (term26 x)). Qed.
Lemma lem1360437 (x : real) (y : real) : (term33 x y) = ((term25 x y) = (term20 x y)).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem1360438 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1360440 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1360438) (@lem1360437 x y)). Qed.
Lemma lem1360441 (x : real) : (term36 x) = (term37 x).
Proof. exact (fun_ext (fun y : real => @lem1360440 x y)). Qed.
Lemma lem1360442 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1360443 (x : real) : (term32 x) = (term38 x).
Proof. exact (MK_COMB (@lem1360442) (@lem1360441 x)). Qed.
Lemma lem1360444 (x : real) : (term31 x) = (term38 x).
Proof. exact (TRANS (@lem1360436 x) (@lem1360443 x)). Qed.
Lemma lem1360445 (P : real -> Prop) : (term29 P) = (term30 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1360446 : term3 = term39.
Proof. exact (@lem1360445 term28). Qed.
Lemma lem1360447 (x : real) : (term40 x) = (term27 x).
Proof. exact (eq_refl (term40 x)). Qed.
Lemma lem1360448 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1360449 (x : real) : (term41 x) = (term31 x).
Proof. exact (MK_COMB (@lem1360448) (@lem1360447 x)). Qed.
Lemma lem1360450 (x : real) : (term41 x) = (term38 x).
Proof. exact (TRANS (@lem1360449 x) (@lem1360444 x)). Qed.
Lemma lem1360451 : term42 = term43.
Proof. exact (fun_ext (fun x : real => @lem1360450 x)). Qed.
Lemma lem1360452 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1360453 : term39 = term44.
Proof. exact (MK_COMB (@lem1360452) (@lem1360451)). Qed.
Lemma lem1360466 : term3 = term44.
Proof. exact (TRANS (@lem1360446) (@lem1360453)). Qed.
Lemma lem1360467 (h1 : term3) : term44.
Proof. exact (EQ_MP (@lem1360466) (@lem1360431 h1)). Qed.
Lemma lem1360468 (x : real) (y : real) : ((term19 x y) = (term20 x y)) = ((term19 x y) = (term20 x y)).
Proof. exact (eq_refl ((term19 x y) = (term20 x y))). Qed.
Lemma lem1360469 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1360468 x y)). Qed.
Lemma lem1360470 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360471 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1360470) (@lem1360469 x)). Qed.
Lemma lem1360472 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1360471 x)). Qed.
Lemma lem1360473 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360486 : term24 = term24.
Proof. exact (MK_COMB (@lem1360473) (@lem1360472)). Qed.
Lemma lem1360487 (h1 : term24) : term24.
Proof. exact (EQ_MP (@lem1360486) (@lem1360432 h1)). Qed.
Lemma lem1360488 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1360489 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1360488 y x)). Qed.
Lemma lem1360490 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360491 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1360490) (@lem1360489 x)). Qed.
Lemma lem1360492 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1360491 x)). Qed.
Lemma lem1360493 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360506 : term10 = term10.
Proof. exact (MK_COMB (@lem1360493) (@lem1360492)). Qed.
Lemma lem1360507 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1360506) (@lem1360433 h1)). Qed.
Lemma lem1360508 (x : real) (h1 : term38 x) : term38 x.
Proof. exact (h1). Qed.
Lemma lem1360526 (x : real) (y : real) : ((term19 x y) = (term20 x y)) = ((term19 x y) = (term20 x y)).
Proof. exact (eq_refl ((term19 x y) = (term20 x y))). Qed.
Lemma lem1360527 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1360526 x y)). Qed.
Lemma lem1360528 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360529 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1360528) (@lem1360527 x)). Qed.
Lemma lem1360530 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1360529 x)). Qed.
Lemma lem1360531 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360532 : term24 = term24.
Proof. exact (MK_COMB (@lem1360531) (@lem1360530)). Qed.
Lemma lem1360533 (h1 : term24) : term24.
Proof. exact (EQ_MP (@lem1360532) (@lem1360487 h1)). Qed.
Lemma lem1360546 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1360547 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1360546 y x)). Qed.
Lemma lem1360548 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360549 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1360548) (@lem1360547 x)). Qed.
Lemma lem1360550 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1360549 x)). Qed.
Lemma lem1360551 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360552 : term10 = term10.
Proof. exact (MK_COMB (@lem1360551) (@lem1360550)). Qed.
Lemma lem1360553 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1360552) (@lem1360507 h1)). Qed.
Lemma lem1360573 (x : real) (y : real) (h1 : term35 x y) : term35 x y.
Proof. exact (h1). Qed.
Lemma lem1360575 (x : real) (y : real) : ((term19 x y) = (term20 x y)) = ((term19 x y) = (term20 x y)).
Proof. exact (eq_refl ((term19 x y) = (term20 x y))). Qed.
Lemma lem1360576 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1360575 x y)). Qed.
Lemma lem1360577 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360578 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1360577) (@lem1360576 x)). Qed.
Lemma lem1360579 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1360578 x)). Qed.
Lemma lem1360580 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360582 : term24 = term24.
Proof. exact (MK_COMB (@lem1360580) (@lem1360579)). Qed.
Lemma lem1360583 (h1 : term24) : term24.
Proof. exact (EQ_MP (@lem1360582) (@lem1360533 h1)). Qed.
Lemma lem1360585 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1360586 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1360585 y x)). Qed.
Lemma lem1360587 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360588 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1360587) (@lem1360586 x)). Qed.
Lemma lem1360589 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1360588 x)). Qed.
Lemma lem1360590 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1360592 : term10 = term10.
Proof. exact (MK_COMB (@lem1360590) (@lem1360589)). Qed.
Lemma lem1360593 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1360592) (@lem1360553 h1)). Qed.
Lemma lem1360597 (x : real) (y : real) (h1 : term35 x y) : term35 x y.
Proof. exact (h1). Qed.
Lemma lem1360598 (_24195 : real) (h1 : term24) : term45 _24195.
Proof. exact (@lem1360583 h1 _24195). Qed.
Lemma lem1360599 (_24195 : real) : (term45 _24195) = (term22 _24195).
Proof. exact (eq_refl (term45 _24195)). Qed.
Lemma lem1360600 (_24195 : real) (h1 : term24) : term22 _24195.
Proof. exact (EQ_MP (@lem1360599 _24195) (@lem1360598 _24195 h1)). Qed.
Lemma lem1360601 (_24195 : real) (_24196 : real) (h1 : term24) : term46 _24195 _24196.
Proof. exact (@lem1360600 _24195 h1 _24196). Qed.
Lemma lem1360602 (_24195 : real) (_24196 : real) : (term46 _24195 _24196) = ((term19 _24195 _24196) = (term20 _24195 _24196)).
Proof. exact (eq_refl (term46 _24195 _24196)). Qed.
Lemma lem1360604 (_24197 : real) (h1 : term10) : term47 _24197.
Proof. exact (@lem1360593 h1 _24197). Qed.
Lemma lem1360605 (_24197 : real) : (term47 _24197) = (term17 _24197).
Proof. exact (eq_refl (term47 _24197)). Qed.
Lemma lem1360606 (_24197 : real) (h1 : term10) : term17 _24197.
Proof. exact (EQ_MP (@lem1360605 _24197) (@lem1360604 _24197 h1)). Qed.
Lemma lem1360607 (_24197 : real) (_24198 : real) (h1 : term10) : term48 _24197 _24198.
Proof. exact (@lem1360606 _24197 h1 _24198). Qed.
Lemma lem1360608 (_24198 : real) (_24197 : real) : (term48 _24197 _24198) = ((real_mul _24197 _24198) = (real_mul _24198 _24197)).
Proof. exact (eq_refl (term48 _24197 _24198)). Qed.
Lemma lem1360615 (x : real) (y : real) (h1 : term35 x y) : term35 x y.
Proof. exact (h1). Qed.
Lemma lem1360631 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1360632 (_24203 : real) (_24204 : real) (h1 : _24203 = _24204) : _24203 = _24204.
Proof. exact (h1). Qed.
Lemma lem1360633 (_24203 : real) (_24204 : real) (h1 : _24203 = _24204) : (real_neg _24203) = (real_neg _24204).
Proof. exact (MK_COMB (@lem1360631) (@lem1360632 _24203 _24204 h1)). Qed.
Lemma lem1360634 (_24203 : real) (_24204 : real) : term49 _24203 _24204.
Proof. exact (fun h0 : _24203 = _24204 => @lem1360633 _24203 _24204 h0). Qed.
Lemma lem1360636 (a : Prop) (b : Prop) : (a -> b) = (term50 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1360637 (_24203 : real) (_24204 : real) : (term49 _24203 _24204) = (term51 _24203 _24204).
Proof. exact (@lem1360636 (_24203 = _24204) ((real_neg _24203) = (real_neg _24204))). Qed.
Lemma lem1360638 (_24203 : real) (_24204 : real) : term51 _24203 _24204.
Proof. exact (EQ_MP (@lem1360637 _24203 _24204) (@lem1360634 _24203 _24204)). Qed.
Lemma lem1360640 (x : real) (y : real) (z : real) : term52 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1360642 (_24195 : real) (_24196 : real) (h1 : term24) : (term19 _24195 _24196) = (term20 _24195 _24196).
Proof. exact (EQ_MP (@lem1360602 _24195 _24196) (@lem1360601 _24195 _24196 h1)). Qed.
Lemma lem1360643 (y : real) (x : real) (h1 : term24) : (term19 y x) = (term20 y x).
Proof. exact (@lem1360642 y x h1). Qed.
Lemma lem1360644 (y : real) (x : real) (h1 : term24) : term53 y x.
Proof. exact (fun h0 : term54 y x => @lem1360643 y x h1). Qed.
Lemma lem1360646 (p : Prop) : (term55 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360647 (y : real) (x : real) : (term53 y x) = ((term19 y x) = (term20 y x)).
Proof. exact (@lem1360646 ((term19 y x) = (term20 y x))). Qed.
Lemma lem1360648 (y : real) (x : real) (h1 : term24) : (term19 y x) = (term20 y x).
Proof. exact (EQ_MP (@lem1360647 y x) (@lem1360644 y x h1)). Qed.
Lemma lem1360650 (_24198 : real) (_24197 : real) (h1 : term10) : (real_mul _24197 _24198) = (real_mul _24198 _24197).
Proof. exact (EQ_MP (@lem1360608 _24198 _24197) (@lem1360607 _24197 _24198 h1)). Qed.
Lemma lem1360651 (x : real) (y : real) (h1 : term10) : (term19 y x) = (term25 x y).
Proof. exact (@lem1360650 (real_neg x) y h1). Qed.
Lemma lem1360652 (x : real) (y : real) (h1 : term10) : term56 x y.
Proof. exact (fun h0 : term57 x y => @lem1360651 x y h1). Qed.
Lemma lem1360654 (p : Prop) : (term55 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360655 (x : real) (y : real) : (term56 x y) = ((term19 y x) = (term25 x y)).
Proof. exact (@lem1360654 ((term19 y x) = (term25 x y))). Qed.
Lemma lem1360656 (x : real) (y : real) (h1 : term10) : (term19 y x) = (term25 x y).
Proof. exact (EQ_MP (@lem1360655 x y) (@lem1360652 x y h1)). Qed.
Lemma lem1360674 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1360675 (y : real) (x : real) (z : real) : (term58 x y z) = (term59 y x z).
Proof. exact (@lem1360674 (y = z) (term60 x z)). Qed.
Lemma lem1360685 (x : real) (y : real) : (term61 x y) = (term61 x y).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem1360686 (y : real) (x : real) (z : real) : (term52 x y z) = (term62 y x z).
Proof. exact (MK_COMB (@lem1360685 x y) (@lem1360675 y x z)). Qed.
Lemma lem1360690 (q : Prop) (p : Prop) (r : Prop) : (term63 p q r) = (term63 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1360691 (y : real) (x : real) (z : real) : (term62 y x z) = (term64 y x z).
Proof. exact (@lem1360690 (y = z) (term60 x y) (term60 x z)). Qed.
Lemma lem1360713 (y : real) (x : real) (z : real) : (term52 x y z) = (term64 y x z).
Proof. exact (TRANS (@lem1360686 y x z) (@lem1360691 y x z)). Qed.
Lemma lem1360714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1360715 (y : real) (x : real) (z : real) : (term65 x y z) = (term66 y x z).
Proof. exact (MK_COMB (@lem1360714) (@lem1360713 y x z)). Qed.
Lemma lem1360737 (y : real) (x : real) (z : real) : (term64 y x z) = (term64 y x z).
Proof. exact (eq_refl (term64 y x z)). Qed.
Lemma lem1360738 (y : real) (x : real) (z : real) : ((term52 x y z) = (term64 y x z)) = ((term64 y x z) = (term64 y x z)).
Proof. exact (MK_COMB (@lem1360715 y x z) (@lem1360737 y x z)). Qed.
Lemma lem1360740 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1360741 (x : Prop) : (x = x) = True.
Proof. exact (@lem1360740 Prop x). Qed.
Lemma lem1360742 (y : real) (x : real) (z : real) : ((term64 y x z) = (term64 y x z)) = True.
Proof. exact (@lem1360741 (term64 y x z)). Qed.
Lemma lem1360743 (y : real) (x : real) (z : real) : ((term52 x y z) = (term64 y x z)) = True.
Proof. exact (TRANS (@lem1360738 y x z) (@lem1360742 y x z)). Qed.
Lemma lem1360744 (y : real) (x : real) (z : real) : True = ((term52 x y z) = (term64 y x z)).
Proof. exact (SYM (@lem1360743 y x z)). Qed.
Lemma lem1360745 (y : real) (x : real) (z : real) : (term52 x y z) = (term64 y x z).
Proof. exact (EQ_MP (@lem1360744 y x z) (@lem0)). Qed.
Lemma lem1360746 (y : real) (x : real) (z : real) : term64 y x z.
Proof. exact (EQ_MP (@lem1360745 y x z) (@lem1360640 x y z)). Qed.
Lemma lem1360748 (b : Prop) (a : Prop) : (a \/ b) = (term67 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1360749 (x : real) (y : real) (z : real) : (term64 y x z) = (term68 x y z).
Proof. exact (@lem1360748 (term69 y x z) (y = z)). Qed.
Lemma lem1360751 (a : Prop) (b : Prop) : (term70 a b) = (term71 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1360752 (y : real) (x : real) (z : real) : (term72 y x z) = (term73 y x z).
Proof. exact (@lem1360751 (term60 x y) (term60 x z)). Qed.
Lemma lem1360754 (a : Prop) : (term74 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1360755 (x : real) (y : real) : (term75 x y) = (x = y).
Proof. exact (@lem1360754 (x = y)). Qed.
Lemma lem1360756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1360757 (x : real) (y : real) : (term76 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem1360756) (@lem1360755 x y)). Qed.
Lemma lem1360759 (a : Prop) : (term74 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1360760 (x : real) (z : real) : (term75 x z) = (x = z).
Proof. exact (@lem1360759 (x = z)). Qed.
Lemma lem1360761 (y : real) (x : real) (z : real) : (term73 y x z) = (term78 y x z).
Proof. exact (MK_COMB (@lem1360757 x y) (@lem1360760 x z)). Qed.
Lemma lem1360762 (y : real) (x : real) (z : real) : (term72 y x z) = (term78 y x z).
Proof. exact (TRANS (@lem1360752 y x z) (@lem1360761 y x z)). Qed.
Lemma lem1360763 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1360764 (y : real) (x : real) (z : real) : (term79 y x z) = (term80 y x z).
Proof. exact (MK_COMB (@lem1360763) (@lem1360762 y x z)). Qed.
Lemma lem1360765 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1360766 (x : real) (y : real) (z : real) : (term68 x y z) = (term81 x y z).
Proof. exact (MK_COMB (@lem1360764 y x z) (@lem1360765 y z)). Qed.
Lemma lem1360767 (x : real) (y : real) (z : real) : (term64 y x z) = (term81 x y z).
Proof. exact (TRANS (@lem1360749 x y z) (@lem1360766 x y z)). Qed.
Lemma lem1360769 (x : real) (y : real) (h1 : term10) (h2 : term24) : term82 x y.
Proof. exact (conj (@lem1360648 y x h2) (@lem1360656 x y h1)). Qed.
Lemma lem1360771 (x : real) (y : real) (z : real) : term81 x y z.
Proof. exact (EQ_MP (@lem1360767 x y z) (@lem1360746 y x z)). Qed.
Lemma lem1360772 (x : real) (y : real) : term83 x y.
Proof. exact (@lem1360771 (term19 y x) (term20 y x) (term25 x y)). Qed.
Lemma lem1360775 (x : real) (y : real) (h1 : term10) (h2 : term24) : (term20 y x) = (term25 x y).
Proof. exact (@lem1360772 x y (@lem1360769 x y h1 h2)). Qed.
Lemma lem1360776 (x : real) (y : real) (h1 : term10) (h2 : term24) : term84 x y.
Proof. exact (fun h0 : term85 x y => @lem1360775 x y h1 h2). Qed.
Lemma lem1360778 (p : Prop) : (term55 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360779 (x : real) (y : real) : (term84 x y) = ((term20 y x) = (term25 x y)).
Proof. exact (@lem1360778 ((term20 y x) = (term25 x y))). Qed.
Lemma lem1360780 (x : real) (y : real) (h1 : term10) (h2 : term24) : (term20 y x) = (term25 x y).
Proof. exact (EQ_MP (@lem1360779 x y) (@lem1360776 x y h1 h2)). Qed.
Lemma lem1360782 (_24198 : real) (_24197 : real) (h1 : term10) : (real_mul _24197 _24198) = (real_mul _24198 _24197).
Proof. exact (EQ_MP (@lem1360608 _24198 _24197) (@lem1360607 _24197 _24198 h1)). Qed.
Lemma lem1360783 (x : real) (y : real) (h1 : term10) : (real_mul y x) = (real_mul x y).
Proof. exact (@lem1360782 x y h1). Qed.
Lemma lem1360784 (x : real) (y : real) (h1 : term10) : term86 x y.
Proof. exact (fun h0 : term87 x y => @lem1360783 x y h1). Qed.
Lemma lem1360786 (p : Prop) : (term55 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360787 (x : real) (y : real) : (term86 x y) = ((real_mul y x) = (real_mul x y)).
Proof. exact (@lem1360786 ((real_mul y x) = (real_mul x y))). Qed.
Lemma lem1360788 (x : real) (y : real) (h1 : term10) : (real_mul y x) = (real_mul x y).
Proof. exact (EQ_MP (@lem1360787 x y) (@lem1360784 x y h1)). Qed.
Lemma lem1360794 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1360795 (_24203 : real) (_24204 : real) : (term51 _24203 _24204) = (term88 _24203 _24204).
Proof. exact (@lem1360794 ((real_neg _24203) = (real_neg _24204)) (term60 _24203 _24204)). Qed.
Lemma lem1360805 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1360806 (_24203 : real) (_24204 : real) : (term89 _24203 _24204) = (term90 _24203 _24204).
Proof. exact (MK_COMB (@lem1360805) (@lem1360795 _24203 _24204)). Qed.
Lemma lem1360816 (_24203 : real) (_24204 : real) : (term88 _24203 _24204) = (term88 _24203 _24204).
Proof. exact (eq_refl (term88 _24203 _24204)). Qed.
Lemma lem1360817 (_24203 : real) (_24204 : real) : ((term51 _24203 _24204) = (term88 _24203 _24204)) = ((term88 _24203 _24204) = (term88 _24203 _24204)).
Proof. exact (MK_COMB (@lem1360806 _24203 _24204) (@lem1360816 _24203 _24204)). Qed.
Lemma lem1360819 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1360820 (x : Prop) : (x = x) = True.
Proof. exact (@lem1360819 Prop x). Qed.
Lemma lem1360821 (_24203 : real) (_24204 : real) : ((term88 _24203 _24204) = (term88 _24203 _24204)) = True.
Proof. exact (@lem1360820 (term88 _24203 _24204)). Qed.
Lemma lem1360822 (_24203 : real) (_24204 : real) : ((term51 _24203 _24204) = (term88 _24203 _24204)) = True.
Proof. exact (TRANS (@lem1360817 _24203 _24204) (@lem1360821 _24203 _24204)). Qed.
Lemma lem1360823 (_24203 : real) (_24204 : real) : True = ((term51 _24203 _24204) = (term88 _24203 _24204)).
Proof. exact (SYM (@lem1360822 _24203 _24204)). Qed.
Lemma lem1360824 (_24203 : real) (_24204 : real) : (term51 _24203 _24204) = (term88 _24203 _24204).
Proof. exact (EQ_MP (@lem1360823 _24203 _24204) (@lem0)). Qed.
Lemma lem1360825 (_24203 : real) (_24204 : real) : term88 _24203 _24204.
Proof. exact (EQ_MP (@lem1360824 _24203 _24204) (@lem1360638 _24203 _24204)). Qed.
Lemma lem1360827 (b : Prop) (a : Prop) : (a \/ b) = (term67 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1360828 (_24203 : real) (_24204 : real) : (term88 _24203 _24204) = (term91 _24203 _24204).
Proof. exact (@lem1360827 (term60 _24203 _24204) ((real_neg _24203) = (real_neg _24204))). Qed.
Lemma lem1360830 (a : Prop) : (term74 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1360831 (_24203 : real) (_24204 : real) : (term75 _24203 _24204) = (_24203 = _24204).
Proof. exact (@lem1360830 (_24203 = _24204)). Qed.
Lemma lem1360832 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1360833 (_24203 : real) (_24204 : real) : (term92 _24203 _24204) = (term93 _24203 _24204).
Proof. exact (MK_COMB (@lem1360832) (@lem1360831 _24203 _24204)). Qed.
Lemma lem1360834 (_24203 : real) (_24204 : real) : ((real_neg _24203) = (real_neg _24204)) = ((real_neg _24203) = (real_neg _24204)).
Proof. exact (eq_refl ((real_neg _24203) = (real_neg _24204))). Qed.
Lemma lem1360835 (_24203 : real) (_24204 : real) : (term91 _24203 _24204) = (term49 _24203 _24204).
Proof. exact (MK_COMB (@lem1360833 _24203 _24204) (@lem1360834 _24203 _24204)). Qed.
Lemma lem1360836 (_24203 : real) (_24204 : real) : (term88 _24203 _24204) = (term49 _24203 _24204).
Proof. exact (TRANS (@lem1360828 _24203 _24204) (@lem1360835 _24203 _24204)). Qed.
Lemma lem1360839 (_24203 : real) (_24204 : real) : term49 _24203 _24204.
Proof. exact (EQ_MP (@lem1360836 _24203 _24204) (@lem1360825 _24203 _24204)). Qed.
Lemma lem1360840 (x : real) (y : real) : term94 x y.
Proof. exact (@lem1360839 (real_mul y x) (real_mul x y)). Qed.
Lemma lem1360843 (x : real) (y : real) (h1 : term10) : (term20 y x) = (term20 x y).
Proof. exact (@lem1360840 x y (@lem1360788 x y h1)). Qed.
Lemma lem1360844 (x : real) (y : real) (h1 : term10) : term95 x y.
Proof. exact (fun h0 : term96 x y => @lem1360843 x y h1). Qed.
Lemma lem1360846 (p : Prop) : (term55 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360847 (x : real) (y : real) : (term95 x y) = ((term20 y x) = (term20 x y)).
Proof. exact (@lem1360846 ((term20 y x) = (term20 x y))). Qed.
Lemma lem1360848 (x : real) (y : real) (h1 : term10) : (term20 y x) = (term20 x y).
Proof. exact (EQ_MP (@lem1360847 x y) (@lem1360844 x y h1)). Qed.
Lemma lem1360849 (x : real) (y : real) (h1 : term10) (h2 : term24) : term97 x y.
Proof. exact (conj (@lem1360780 x y h1 h2) (@lem1360848 x y h1)). Qed.
Lemma lem1360851 (x : real) (y : real) (z : real) : term81 x y z.
Proof. exact (EQ_MP (@lem1360767 x y z) (@lem1360746 y x z)). Qed.
Lemma lem1360852 (x : real) (y : real) : term98 x y.
Proof. exact (@lem1360851 (term20 y x) (term25 x y) (term20 x y)). Qed.
Lemma lem1360855 (x : real) (y : real) (h1 : term10) (h2 : term24) : (term25 x y) = (term20 x y).
Proof. exact (@lem1360852 x y (@lem1360849 x y h1 h2)). Qed.
Lemma lem1360856 (x : real) (y : real) (h1 : term10) (h2 : term24) : term99 x y.
Proof. exact (fun h0 : term35 x y => @lem1360855 x y h1 h2). Qed.
Lemma lem1360858 (p : Prop) : (term55 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360859 (x : real) (y : real) : (term99 x y) = ((term25 x y) = (term20 x y)).
Proof. exact (@lem1360858 ((term25 x y) = (term20 x y))). Qed.
Lemma lem1360860 (x : real) (y : real) (h1 : term10) (h2 : term24) : (term25 x y) = (term20 x y).
Proof. exact (EQ_MP (@lem1360859 x y) (@lem1360856 x y h1 h2)). Qed.
Lemma lem1360863 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1360865 (x : real) (y : real) : (term35 x y) = (term100 x y).
Proof. exact (@lem1360863 ((term25 x y) = (term20 x y))). Qed.
Lemma lem1360868 (x : real) (y : real) (h1 : term35 x y) : term100 x y.
Proof. exact (EQ_MP (@lem1360865 x y) (@lem1360615 x y h1)). Qed.
Lemma lem1360871 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : False.
Proof. exact (@lem1360868 x y h3 (@lem1360860 x y h1 h2)). Qed.
Lemma lem1360872 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : term101.
Proof. exact (fun h0 : ~ False => @lem1360871 x y h1 h2 h3). Qed.
Lemma lem1360874 (p : Prop) : (term55 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360875 : term101 = False.
Proof. exact (@lem1360874 False). Qed.
Lemma lem1360876 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : False.
Proof. exact (EQ_MP (@lem1360875) (@lem1360872 x y h1 h2 h3)). Qed.
Lemma lem1360877 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : (term35 x y) = False.
Proof. exact (prop_ext (fun h4 : term35 x y => @lem1360876 x y h1 h2 h3) (fun h4 : False => @lem1360615 x y h3)). Qed.
Lemma lem1360878 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : False.
Proof. exact (EQ_MP (@lem1360877 x y h1 h2 h3) (@lem1360615 x y h3)). Qed.
Lemma lem1360879 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : (term35 x y) = False.
Proof. exact (prop_ext (fun h4 : term35 x y => @lem1360878 x y h1 h2 h3) (fun h4 : False => @lem1360597 x y h3)). Qed.
Lemma lem1360880 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : False.
Proof. exact (EQ_MP (@lem1360879 x y h1 h2 h3) (@lem1360597 x y h3)). Qed.
Lemma lem1360881 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : (term35 x y) = False.
Proof. exact (prop_ext (fun h4 : term35 x y => @lem1360880 x y h1 h2 h3) (fun h4 : False => @lem1360597 x y h3)). Qed.
Lemma lem1360882 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : False.
Proof. exact (EQ_MP (@lem1360881 x y h1 h2 h3) (@lem1360597 x y h3)). Qed.
Lemma lem1360883 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1360882 x y h1 h2 h3) (fun h4 : False => @lem1360593 h1)). Qed.
Lemma lem1360884 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : False.
Proof. exact (EQ_MP (@lem1360883 x y h1 h2 h3) (@lem1360593 h1)). Qed.
Lemma lem1360885 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : term24 = False.
Proof. exact (prop_ext (fun h4 : term24 => @lem1360884 x y h1 h2 h3) (fun h4 : False => @lem1360583 h2)). Qed.
Lemma lem1360886 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : False.
Proof. exact (EQ_MP (@lem1360885 x y h1 h2 h3) (@lem1360583 h2)). Qed.
Lemma lem1360887 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : (term35 x y) = False.
Proof. exact (prop_ext (fun h4 : term35 x y => @lem1360886 x y h1 h2 h3) (fun h4 : False => @lem1360573 x y h3)). Qed.
Lemma lem1360888 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : False.
Proof. exact (EQ_MP (@lem1360887 x y h1 h2 h3) (@lem1360573 x y h3)). Qed.
Lemma lem1360889 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1360888 x y h1 h2 h3) (fun h4 : False => @lem1360553 h1)). Qed.
Lemma lem1360890 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : False.
Proof. exact (EQ_MP (@lem1360889 x y h1 h2 h3) (@lem1360553 h1)). Qed.
Lemma lem1360891 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : term24 = False.
Proof. exact (prop_ext (fun h4 : term24 => @lem1360890 x y h1 h2 h3) (fun h4 : False => @lem1360533 h2)). Qed.
Lemma lem1360892 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term35 x y) : False.
Proof. exact (EQ_MP (@lem1360891 x y h1 h2 h3) (@lem1360533 h2)). Qed.
Lemma lem1360893 (x : real) (h1 : term10) (h2 : term24) (h3 : term38 x) : False.
Proof. exact (ex_elim (@lem1360508 x h3) (fun y : real => fun h0 : term37 x y => @lem1360892 x y h1 h2 h0)). Qed.
Lemma lem1360894 (h1 : term10) (h2 : term24) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1360467 h3) (fun x : real => fun h0 : term43 x => @lem1360893 x h1 h2 h0)). Qed.
Lemma lem1360895 (h1 : term10) (h2 : term24) (h3 : term3) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1360894 h1 h2 h3) (fun h4 : False => @lem1360507 h1)). Qed.
Lemma lem1360896 (h1 : term10) (h2 : term24) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1360895 h1 h2 h3) (@lem1360507 h1)). Qed.
Lemma lem1360897 (h1 : term10) (h2 : term24) (h3 : term3) : term24 = False.
Proof. exact (prop_ext (fun h4 : term24 => @lem1360896 h1 h2 h3) (fun h4 : False => @lem1360487 h2)). Qed.
Lemma lem1360898 (h1 : term10) (h2 : term24) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1360897 h1 h2 h3) (@lem1360487 h2)). Qed.
Lemma lem1360899 (h1 : term24) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1360898 h0 h1 h2). Qed.
Lemma lem1360900 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1360901 (h1 : term24) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem1360900) (@lem1360899 h1 h2)). Qed.
Lemma lem1360902 (h1 : term3) : term13.
Proof. exact (fun h0 : term24 => @lem1360901 h0 h1). Qed.
Lemma lem1360903 : term15.
Proof. exact (fun h0 : term3 => @lem1360902 h0). Qed.
Lemma lem1360904 : term4.
Proof. exact (EQ_MP (@lem1360430) (@lem1360903)). Qed.
Lemma lem1360906 : term4.
Proof. exact (@lem1360312 (@lem1360904)). Qed.
Lemma lem1360907 (h1 : term3) : term12.
Proof. exact (@lem1360906 (@lem1360297 h1)). Qed.
Lemma lem1360908 (h1 : term3) : term8.
Proof. exact (@lem1360907 h1 (@lem1360282)). Qed.
Lemma lem1360909 (h1 : term3) : False.
Proof. exact (@lem1360908 h1 (@lem1338712)). Qed.
Lemma lem1360910 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1360909 h1) (fun h2 : False => @lem1360297 h1)). Qed.
Lemma lem1360911 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1360910 h1) (@lem1360297 h1)). Qed.
Lemma lem1360912 : term2.
Proof. exact (fun h0 : term3 => @lem1360911 h0). Qed.
Lemma lem1360913 : term1.
Proof. exact (EQ_MP (@lem1360296) (@lem1360912)). Qed.
