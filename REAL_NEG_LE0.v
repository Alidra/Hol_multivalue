Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NEG_LE0_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1497270 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17646 (term2 x) (term3 x)). Qed.
Lemma lem1497271 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1497272 : term6 = term7.
Proof. exact (@lem1497271 term8). Qed.
Lemma lem1497273 (x : real) : (term9 x) = ((term2 x) = (term3 x)).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1497274 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1497275 (x : real) : (term10 x) = (term0 x).
Proof. exact (MK_COMB (@lem1497274) (@lem1497273 x)). Qed.
Lemma lem1497276 (x : real) : (term10 x) = (term1 x).
Proof. exact (TRANS (@lem1497275 x) (@lem1497270 x)). Qed.
Lemma lem1497277 : term11 = term12.
Proof. exact (fun_ext (fun x : real => @lem1497276 x)). Qed.
Lemma lem1497278 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497279 : term7 = term13.
Proof. exact (MK_COMB (@lem1497278) (@lem1497277)). Qed.
Lemma lem1497281 : term6 = term13.
Proof. exact (TRANS (@lem1497272) (@lem1497279)). Qed.
Lemma lem1497298 (x : real) : (term1 x) = (term1 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1497299 : term12 = term12.
Proof. exact (fun_ext (fun x : real => @lem1497298 x)). Qed.
Lemma lem1497300 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497301 : term13 = term13.
Proof. exact (MK_COMB (@lem1497300) (@lem1497299)). Qed.
Lemma lem1497302 : term6 = term13.
Proof. exact (TRANS (@lem1497281) (@lem1497301)). Qed.
Lemma lem1497303 (x : real) : (term2 x) = (term14 x).
Proof. exact (@lem1483523 term15 (real_neg x)). Qed.
Lemma lem1497310 (x : real) : (real_neg x) = (term16 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1497313 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1497314 (x : real) : (term18 x) = (term19 x).
Proof. exact (MK_COMB (@lem1497313) (@lem1497310 x)). Qed.
Lemma lem1497315 (x : real) : (term19 x) = (term20 x).
Proof. exact (@lem1483519 term15 (term16 x)). Qed.
Lemma lem1497316 (x : real) : (term21 x) = (term22 x).
Proof. exact (@lem1483476 term23 term23 x). Qed.
Lemma lem1497318 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1497319 : term26 = term27.
Proof. exact (@lem1497318 term28 term28). Qed.
Lemma lem1497320 : (term29 = (BIT1 0)) = (term30 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1497321 : term30 = term28.
Proof. exact (EQ_MP (@lem1497320) (@lem940073)). Qed.
Lemma lem1497322 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1497323 : term27 = term31.
Proof. exact (MK_COMB (@lem1497322) (@lem1497321)). Qed.
Lemma lem1497324 : term26 = term31.
Proof. exact (TRANS (@lem1497319) (@lem1497323)). Qed.
Lemma lem1497325 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1497326 : term32 = term33.
Proof. exact (MK_COMB (@lem1497325) (@lem1497324)). Qed.
Lemma lem1497327 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1497328 (x : real) : (term22 x) = (term34 x).
Proof. exact (MK_COMB (@lem1497326) (@lem1497327 x)). Qed.
Lemma lem1497329 (x : real) : (term21 x) = (term34 x).
Proof. exact (TRANS (@lem1497316 x) (@lem1497328 x)). Qed.
Lemma lem1497330 (x : real) : (term34 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1497331 (x : real) : (term21 x) = x.
Proof. exact (TRANS (@lem1497329 x) (@lem1497330 x)). Qed.
Lemma lem1497332 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1497333 (x : real) : (term20 x) = (term36 x).
Proof. exact (MK_COMB (@lem1497332) (@lem1497331 x)). Qed.
Lemma lem1497334 (x : real) : (term36 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1497335 (x : real) : (term20 x) = x.
Proof. exact (TRANS (@lem1497333 x) (@lem1497334 x)). Qed.
Lemma lem1497336 (x : real) : (term19 x) = x.
Proof. exact (TRANS (@lem1497315 x) (@lem1497335 x)). Qed.
Lemma lem1497337 (x : real) : (term18 x) = x.
Proof. exact (TRANS (@lem1497314 x) (@lem1497336 x)). Qed.
Lemma lem1497338 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1497339 (x : real) : (term37 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1497338) (@lem1497337 x)). Qed.
Lemma lem1497340 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497341 (x : real) : (term14 x) = (term38 x).
Proof. exact (MK_COMB (@lem1497339 x) (@lem1497340)). Qed.
Lemma lem1497342 (x : real) : (term2 x) = (term38 x).
Proof. exact (TRANS (@lem1497303 x) (@lem1497341 x)). Qed.
Lemma lem1497343 (x : real) : (term39 x) = (term40 x).
Proof. exact (@lem1483533 term15 x). Qed.
Lemma lem1497349 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1483519 term15 x). Qed.
Lemma lem1497354 (x : real) : (term42 x) = (term16 x).
Proof. exact (@lem1483448 (term16 x)). Qed.
Lemma lem1497356 (x : real) : (term41 x) = (term16 x).
Proof. exact (TRANS (@lem1497349 x) (@lem1497354 x)). Qed.
Lemma lem1497357 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1497358 (x : real) : (term43 x) = (term44 x).
Proof. exact (MK_COMB (@lem1497357) (@lem1497356 x)). Qed.
Lemma lem1497359 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497360 (x : real) : (term40 x) = (term45 x).
Proof. exact (MK_COMB (@lem1497358 x) (@lem1497359)). Qed.
Lemma lem1497361 (x : real) : (term39 x) = (term45 x).
Proof. exact (TRANS (@lem1497343 x) (@lem1497360 x)). Qed.
Lemma lem1497362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1497363 (x : real) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem1497362) (@lem1497342 x)). Qed.
Lemma lem1497364 (x : real) : (term48 x) = (term49 x).
Proof. exact (MK_COMB (@lem1497363 x) (@lem1497361 x)). Qed.
Lemma lem1497365 (x : real) : (term50 x) = (term51 x).
Proof. exact (@lem1483533 (real_neg x) term15). Qed.
Lemma lem1497366 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497373 (x : real) : (real_neg x) = (term16 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1497374 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1497375 (x : real) : (term52 x) = (term53 x).
Proof. exact (MK_COMB (@lem1497374) (@lem1497373 x)). Qed.
Lemma lem1497376 (x : real) : (term54 x) = (term55 x).
Proof. exact (MK_COMB (@lem1497375 x) (@lem1497366)). Qed.
Lemma lem1497377 (x : real) : (term55 x) = (term56 x).
Proof. exact (@lem1483519 (term16 x) term15). Qed.
Lemma lem1497379 (x : nat) : (term57 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1497380 : term58 = term15.
Proof. exact (@lem1497379 term28). Qed.
Lemma lem1497381 (x : real) : (term59 x) = (term59 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1497382 (x : real) : (term56 x) = (term60 x).
Proof. exact (MK_COMB (@lem1497381 x) (@lem1497380)). Qed.
Lemma lem1497383 (x : real) : (term60 x) = (term16 x).
Proof. exact (@lem1483450 (term16 x)). Qed.
Lemma lem1497384 (x : real) : (term56 x) = (term16 x).
Proof. exact (TRANS (@lem1497382 x) (@lem1497383 x)). Qed.
Lemma lem1497385 (x : real) : (term55 x) = (term16 x).
Proof. exact (TRANS (@lem1497377 x) (@lem1497384 x)). Qed.
Lemma lem1497386 (x : real) : (term54 x) = (term16 x).
Proof. exact (TRANS (@lem1497376 x) (@lem1497385 x)). Qed.
Lemma lem1497387 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1497388 (x : real) : (term61 x) = (term44 x).
Proof. exact (MK_COMB (@lem1497387) (@lem1497386 x)). Qed.
Lemma lem1497389 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497390 (x : real) : (term51 x) = (term45 x).
Proof. exact (MK_COMB (@lem1497388 x) (@lem1497389)). Qed.
Lemma lem1497391 (x : real) : (term50 x) = (term45 x).
Proof. exact (TRANS (@lem1497365 x) (@lem1497390 x)). Qed.
Lemma lem1497392 (x : real) : (term3 x) = (term62 x).
Proof. exact (@lem1483523 x term15). Qed.
Lemma lem1497398 (x : real) : (term63 x) = (term64 x).
Proof. exact (@lem1483519 x term15). Qed.
Lemma lem1497400 (x : nat) : (term57 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1497401 : term58 = term15.
Proof. exact (@lem1497400 term28). Qed.
Lemma lem1497402 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1497403 (x : real) : (term64 x) = (term65 x).
Proof. exact (MK_COMB (@lem1497402 x) (@lem1497401)). Qed.
Lemma lem1497404 (x : real) : (term65 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1497405 (x : real) : (term64 x) = x.
Proof. exact (TRANS (@lem1497403 x) (@lem1497404 x)). Qed.
Lemma lem1497407 (x : real) : (term63 x) = x.
Proof. exact (TRANS (@lem1497398 x) (@lem1497405 x)). Qed.
Lemma lem1497408 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1497409 (x : real) : (term66 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1497408) (@lem1497407 x)). Qed.
Lemma lem1497410 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497411 (x : real) : (term62 x) = (term38 x).
Proof. exact (MK_COMB (@lem1497409 x) (@lem1497410)). Qed.
Lemma lem1497412 (x : real) : (term3 x) = (term38 x).
Proof. exact (TRANS (@lem1497392 x) (@lem1497411 x)). Qed.
Lemma lem1497413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1497414 (x : real) : (term67 x) = (term68 x).
Proof. exact (MK_COMB (@lem1497413) (@lem1497391 x)). Qed.
Lemma lem1497415 (x : real) : (term69 x) = (term70 x).
Proof. exact (MK_COMB (@lem1497414 x) (@lem1497412 x)). Qed.
Lemma lem1497416 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1497417 (x : real) : (term71 x) = (term72 x).
Proof. exact (MK_COMB (@lem1497416) (@lem1497364 x)). Qed.
Lemma lem1497418 (x : real) : (term1 x) = (term73 x).
Proof. exact (MK_COMB (@lem1497417 x) (@lem1497415 x)). Qed.
Lemma lem1497419 : term12 = term74.
Proof. exact (fun_ext (fun x : real => @lem1497418 x)). Qed.
Lemma lem1497420 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497421 : term13 = term75.
Proof. exact (MK_COMB (@lem1497420) (@lem1497419)). Qed.
Lemma lem1497422 : term6 = term75.
Proof. exact (TRANS (@lem1497302) (@lem1497421)). Qed.
Lemma lem1497424 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1497425 (P : real -> Prop) (Q : real -> Prop) : (term78 P Q) = (term79 P Q).
Proof. exact (@lem1497424 real P Q). Qed.
Lemma lem1497426 : term80 = term81.
Proof. exact (@lem1497425 term82 term83). Qed.
Lemma lem1497427 (x : real) : (term84 x) = (term49 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1497428 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1497429 (x : real) : (term85 x) = (term72 x).
Proof. exact (MK_COMB (@lem1497428) (@lem1497427 x)). Qed.
Lemma lem1497430 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1497431 (x : real) : (term87 x) = (term73 x).
Proof. exact (MK_COMB (@lem1497429 x) (@lem1497430 x)). Qed.
Lemma lem1497432 : term88 = term74.
Proof. exact (fun_ext (fun x : real => @lem1497431 x)). Qed.
Lemma lem1497433 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497434 : term80 = term75.
Proof. exact (MK_COMB (@lem1497433) (@lem1497432)). Qed.
Lemma lem1497435 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1497436 : term89 = term90.
Proof. exact (MK_COMB (@lem1497435) (@lem1497434)). Qed.
Lemma lem1497437 (x : real) : (term84 x) = (term49 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1497438 : term91 = term82.
Proof. exact (fun_ext (fun x : real => @lem1497437 x)). Qed.
Lemma lem1497439 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497440 : term92 = term93.
Proof. exact (MK_COMB (@lem1497439) (@lem1497438)). Qed.
Lemma lem1497441 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1497442 : term94 = term95.
Proof. exact (MK_COMB (@lem1497441) (@lem1497440)). Qed.
Lemma lem1497443 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1497444 : term96 = term83.
Proof. exact (fun_ext (fun x : real => @lem1497443 x)). Qed.
Lemma lem1497445 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497446 : term97 = term98.
Proof. exact (MK_COMB (@lem1497445) (@lem1497444)). Qed.
Lemma lem1497447 : term81 = term99.
Proof. exact (MK_COMB (@lem1497442) (@lem1497446)). Qed.
Lemma lem1497448 : (term80 = term81) = (term75 = term99).
Proof. exact (MK_COMB (@lem1497436) (@lem1497447)). Qed.
Lemma lem1497449 : term75 = term99.
Proof. exact (EQ_MP (@lem1497448) (@lem1497426)). Qed.
Lemma lem1497547 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1497548 (P : real -> Prop) (Q : real -> Prop) : (term79 P Q) = (term78 P Q).
Proof. exact (@lem1497547 real P Q). Qed.
Lemma lem1497549 : term81 = term80.
Proof. exact (@lem1497548 term82 term83). Qed.
Lemma lem1497550 (x : real) : (term84 x) = (term49 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1497551 : term91 = term82.
Proof. exact (fun_ext (fun x : real => @lem1497550 x)). Qed.
Lemma lem1497552 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497553 : term92 = term93.
Proof. exact (MK_COMB (@lem1497552) (@lem1497551)). Qed.
Lemma lem1497554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1497555 : term94 = term95.
Proof. exact (MK_COMB (@lem1497554) (@lem1497553)). Qed.
Lemma lem1497556 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1497557 : term96 = term83.
Proof. exact (fun_ext (fun x : real => @lem1497556 x)). Qed.
Lemma lem1497558 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497559 : term97 = term98.
Proof. exact (MK_COMB (@lem1497558) (@lem1497557)). Qed.
Lemma lem1497560 : term81 = term99.
Proof. exact (MK_COMB (@lem1497555) (@lem1497559)). Qed.
Lemma lem1497561 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1497562 : term100 = term101.
Proof. exact (MK_COMB (@lem1497561) (@lem1497560)). Qed.
Lemma lem1497563 (x : real) : (term84 x) = (term49 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1497564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1497565 (x : real) : (term85 x) = (term72 x).
Proof. exact (MK_COMB (@lem1497564) (@lem1497563 x)). Qed.
Lemma lem1497566 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1497567 (x : real) : (term87 x) = (term73 x).
Proof. exact (MK_COMB (@lem1497565 x) (@lem1497566 x)). Qed.
Lemma lem1497568 : term88 = term74.
Proof. exact (fun_ext (fun x : real => @lem1497567 x)). Qed.
Lemma lem1497569 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497570 : term80 = term75.
Proof. exact (MK_COMB (@lem1497569) (@lem1497568)). Qed.
Lemma lem1497571 : (term81 = term80) = (term99 = term75).
Proof. exact (MK_COMB (@lem1497562) (@lem1497570)). Qed.
Lemma lem1497572 : term99 = term75.
Proof. exact (EQ_MP (@lem1497571) (@lem1497549)). Qed.
Lemma lem1497573 : term75 = term75.
Proof. exact (TRANS (@lem1497449) (@lem1497572)). Qed.
Lemma lem1497576 : term6 = term75.
Proof. exact (TRANS (@lem1497422) (@lem1497573)). Qed.
Lemma lem1497593 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1497594 : term74 = term74.
Proof. exact (fun_ext (fun x : real => @lem1497593 x)). Qed.
Lemma lem1497595 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497596 : term75 = term75.
Proof. exact (MK_COMB (@lem1497595) (@lem1497594)). Qed.
Lemma lem1497597 : term6 = term75.
Proof. exact (TRANS (@lem1497576) (@lem1497596)). Qed.
Lemma lem1497607 (x : real) (h1 : term73 x) : term73 x.
Proof. exact (h1). Qed.
Lemma lem1497608 (x : real) (h1 : term49 x) : term49 x.
Proof. exact (h1). Qed.
Lemma lem1497609 (x : real) (h1 : term49 x) : term45 x.
Proof. exact (proj2 (@lem1497608 x h1)). Qed.
Lemma lem1497610 (x : real) (h1 : term49 x) : term38 x.
Proof. exact (proj1 (@lem1497608 x h1)). Qed.
Lemma lem1497612 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1497613 : term103 = term104.
Proof. exact (@lem1497612 (NUMERAL 0) term28). Qed.
Lemma lem1497614 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1497615 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1497616 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1497615 h1) (fun h1 : term104 = True => @lem1497614)). Qed.
Lemma lem1497617 : term104 = True.
Proof. exact (EQ_MP (@lem1497616) (@lem1497614)). Qed.
Lemma lem1497618 : term103 = True.
Proof. exact (TRANS (@lem1497613) (@lem1497617)). Qed.
Lemma lem1497619 : True = term103.
Proof. exact (SYM (@lem1497618)). Qed.
Lemma lem1497620 : term103.
Proof. exact (EQ_MP (@lem1497619) (@lem0)). Qed.
Lemma lem1497621 (x : real) (h1 : term49 x) : term106 x.
Proof. exact (conj (@lem1497620) (@lem1497610 x h1)). Qed.
Lemma lem1497623 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1497624 (x : real) : term108 x.
Proof. exact (@lem1497623 term31 x). Qed.
Lemma lem1497625 (x : real) (h1 : term49 x) : term109 x.
Proof. exact (@lem1497624 x (@lem1497621 x h1)). Qed.
Lemma lem1497626 (x : real) : (term34 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1497627 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1497628 (x : real) : (term110 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1497627) (@lem1497626 x)). Qed.
Lemma lem1497629 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497630 (x : real) : (term109 x) = (term38 x).
Proof. exact (MK_COMB (@lem1497628 x) (@lem1497629)). Qed.
Lemma lem1497631 (x : real) (h1 : term49 x) : term38 x.
Proof. exact (EQ_MP (@lem1497630 x) (@lem1497625 x h1)). Qed.
Lemma lem1497633 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1497634 : term103 = term104.
Proof. exact (@lem1497633 (NUMERAL 0) term28). Qed.
Lemma lem1497635 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1497636 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1497637 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1497636 h1) (fun h1 : term104 = True => @lem1497635)). Qed.
Lemma lem1497638 : term104 = True.
Proof. exact (EQ_MP (@lem1497637) (@lem1497635)). Qed.
Lemma lem1497639 : term103 = True.
Proof. exact (TRANS (@lem1497634) (@lem1497638)). Qed.
Lemma lem1497640 : True = term103.
Proof. exact (SYM (@lem1497639)). Qed.
Lemma lem1497641 : term103.
Proof. exact (EQ_MP (@lem1497640) (@lem0)). Qed.
Lemma lem1497642 (x : real) (h1 : term49 x) : term111 x.
Proof. exact (conj (@lem1497641) (@lem1497609 x h1)). Qed.
Lemma lem1497644 (x : real) (y : real) : term112 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1497645 (x : real) : term113 x.
Proof. exact (@lem1497644 term31 (term16 x)). Qed.
Lemma lem1497646 (x : real) (h1 : term49 x) : term114 x.
Proof. exact (@lem1497645 x (@lem1497642 x h1)). Qed.
Lemma lem1497647 (x : real) : (term115 x) = (term16 x).
Proof. exact (@lem1483460 (term16 x)). Qed.
Lemma lem1497648 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1497649 (x : real) : (term116 x) = (term44 x).
Proof. exact (MK_COMB (@lem1497648) (@lem1497647 x)). Qed.
Lemma lem1497650 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497651 (x : real) : (term114 x) = (term45 x).
Proof. exact (MK_COMB (@lem1497649 x) (@lem1497650)). Qed.
Lemma lem1497652 (x : real) (h1 : term49 x) : term45 x.
Proof. exact (EQ_MP (@lem1497651 x) (@lem1497646 x h1)). Qed.
Lemma lem1497653 (x : real) (h1 : term49 x) : term70 x.
Proof. exact (conj (@lem1497652 x h1) (@lem1497631 x h1)). Qed.
Lemma lem1497655 (x : real) (y : real) : term117 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1497656 (x : real) : term118 x.
Proof. exact (@lem1497655 (term16 x) x). Qed.
Lemma lem1497657 (x : real) (h1 : term49 x) : term119 x.
Proof. exact (@lem1497656 x (@lem1497653 x h1)). Qed.
Lemma lem1497658 (x : real) : (term120 x) = (term121 x).
Proof. exact (@lem1483440 term23 x). Qed.
Lemma lem1497660 (m : nat) : (term122 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1497661 : term123 = term15.
Proof. exact (@lem1497660 term28). Qed.
Lemma lem1497662 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1497663 : term124 = term125.
Proof. exact (MK_COMB (@lem1497662) (@lem1497661)). Qed.
Lemma lem1497664 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1497665 (x : real) : (term121 x) = (term126 x).
Proof. exact (MK_COMB (@lem1497663) (@lem1497664 x)). Qed.
Lemma lem1497666 (x : real) : (term120 x) = (term126 x).
Proof. exact (TRANS (@lem1497658 x) (@lem1497665 x)). Qed.
Lemma lem1497667 (x : real) : (term126 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1497668 (x : real) : (term120 x) = term15.
Proof. exact (TRANS (@lem1497666 x) (@lem1497667 x)). Qed.
Lemma lem1497669 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1497670 (x : real) : (term127 x) = term128.
Proof. exact (MK_COMB (@lem1497669) (@lem1497668 x)). Qed.
Lemma lem1497671 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497672 (x : real) : (term119 x) = term129.
Proof. exact (MK_COMB (@lem1497670 x) (@lem1497671)). Qed.
Lemma lem1497673 (x : real) (h1 : term49 x) : term129.
Proof. exact (EQ_MP (@lem1497672 x) (@lem1497657 x h1)). Qed.
Lemma lem1497675 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1497676 : term129 = term130.
Proof. exact (@lem1497675 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1497677 : term130 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1497678 : term129 = False.
Proof. exact (TRANS (@lem1497676) (@lem1497677)). Qed.
Lemma lem1497679 (x : real) (h1 : term49 x) : False.
Proof. exact (EQ_MP (@lem1497678) (@lem1497673 x h1)). Qed.
Lemma lem1497680 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1497681 (x : real) (h1 : term70 x) : term38 x.
Proof. exact (proj2 (@lem1497680 x h1)). Qed.
Lemma lem1497682 (x : real) (h1 : term70 x) : term45 x.
Proof. exact (proj1 (@lem1497680 x h1)). Qed.
Lemma lem1497684 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1497685 : term103 = term104.
Proof. exact (@lem1497684 (NUMERAL 0) term28). Qed.
Lemma lem1497686 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1497687 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1497688 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1497687 h1) (fun h1 : term104 = True => @lem1497686)). Qed.
Lemma lem1497689 : term104 = True.
Proof. exact (EQ_MP (@lem1497688) (@lem1497686)). Qed.
Lemma lem1497690 : term103 = True.
Proof. exact (TRANS (@lem1497685) (@lem1497689)). Qed.
Lemma lem1497691 : True = term103.
Proof. exact (SYM (@lem1497690)). Qed.
Lemma lem1497692 : term103.
Proof. exact (EQ_MP (@lem1497691) (@lem0)). Qed.
Lemma lem1497693 (x : real) (h1 : term70 x) : term106 x.
Proof. exact (conj (@lem1497692) (@lem1497681 x h1)). Qed.
Lemma lem1497695 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1497696 (x : real) : term108 x.
Proof. exact (@lem1497695 term31 x). Qed.
Lemma lem1497697 (x : real) (h1 : term70 x) : term109 x.
Proof. exact (@lem1497696 x (@lem1497693 x h1)). Qed.
Lemma lem1497698 (x : real) : (term34 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1497699 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1497700 (x : real) : (term110 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1497699) (@lem1497698 x)). Qed.
Lemma lem1497701 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497702 (x : real) : (term109 x) = (term38 x).
Proof. exact (MK_COMB (@lem1497700 x) (@lem1497701)). Qed.
Lemma lem1497703 (x : real) (h1 : term70 x) : term38 x.
Proof. exact (EQ_MP (@lem1497702 x) (@lem1497697 x h1)). Qed.
Lemma lem1497705 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1497706 : term103 = term104.
Proof. exact (@lem1497705 (NUMERAL 0) term28). Qed.
Lemma lem1497707 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1497708 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1497709 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1497708 h1) (fun h1 : term104 = True => @lem1497707)). Qed.
Lemma lem1497710 : term104 = True.
Proof. exact (EQ_MP (@lem1497709) (@lem1497707)). Qed.
Lemma lem1497711 : term103 = True.
Proof. exact (TRANS (@lem1497706) (@lem1497710)). Qed.
Lemma lem1497712 : True = term103.
Proof. exact (SYM (@lem1497711)). Qed.
Lemma lem1497713 : term103.
Proof. exact (EQ_MP (@lem1497712) (@lem0)). Qed.
Lemma lem1497714 (x : real) (h1 : term70 x) : term111 x.
Proof. exact (conj (@lem1497713) (@lem1497682 x h1)). Qed.
Lemma lem1497716 (x : real) (y : real) : term112 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1497717 (x : real) : term113 x.
Proof. exact (@lem1497716 term31 (term16 x)). Qed.
Lemma lem1497718 (x : real) (h1 : term70 x) : term114 x.
Proof. exact (@lem1497717 x (@lem1497714 x h1)). Qed.
Lemma lem1497719 (x : real) : (term115 x) = (term16 x).
Proof. exact (@lem1483460 (term16 x)). Qed.
Lemma lem1497720 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1497721 (x : real) : (term116 x) = (term44 x).
Proof. exact (MK_COMB (@lem1497720) (@lem1497719 x)). Qed.
Lemma lem1497722 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497723 (x : real) : (term114 x) = (term45 x).
Proof. exact (MK_COMB (@lem1497721 x) (@lem1497722)). Qed.
Lemma lem1497724 (x : real) (h1 : term70 x) : term45 x.
Proof. exact (EQ_MP (@lem1497723 x) (@lem1497718 x h1)). Qed.
Lemma lem1497725 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (conj (@lem1497724 x h1) (@lem1497703 x h1)). Qed.
Lemma lem1497727 (x : real) (y : real) : term117 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1497728 (x : real) : term118 x.
Proof. exact (@lem1497727 (term16 x) x). Qed.
Lemma lem1497729 (x : real) (h1 : term70 x) : term119 x.
Proof. exact (@lem1497728 x (@lem1497725 x h1)). Qed.
Lemma lem1497730 (x : real) : (term120 x) = (term121 x).
Proof. exact (@lem1483440 term23 x). Qed.
Lemma lem1497732 (m : nat) : (term122 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1497733 : term123 = term15.
Proof. exact (@lem1497732 term28). Qed.
Lemma lem1497734 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1497735 : term124 = term125.
Proof. exact (MK_COMB (@lem1497734) (@lem1497733)). Qed.
Lemma lem1497736 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1497737 (x : real) : (term121 x) = (term126 x).
Proof. exact (MK_COMB (@lem1497735) (@lem1497736 x)). Qed.
Lemma lem1497738 (x : real) : (term120 x) = (term126 x).
Proof. exact (TRANS (@lem1497730 x) (@lem1497737 x)). Qed.
Lemma lem1497739 (x : real) : (term126 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1497740 (x : real) : (term120 x) = term15.
Proof. exact (TRANS (@lem1497738 x) (@lem1497739 x)). Qed.
Lemma lem1497741 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1497742 (x : real) : (term127 x) = term128.
Proof. exact (MK_COMB (@lem1497741) (@lem1497740 x)). Qed.
Lemma lem1497743 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497744 (x : real) : (term119 x) = term129.
Proof. exact (MK_COMB (@lem1497742 x) (@lem1497743)). Qed.
Lemma lem1497745 (x : real) (h1 : term70 x) : term129.
Proof. exact (EQ_MP (@lem1497744 x) (@lem1497729 x h1)). Qed.
Lemma lem1497747 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1497748 : term129 = term130.
Proof. exact (@lem1497747 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1497749 : term130 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1497750 : term129 = False.
Proof. exact (TRANS (@lem1497748) (@lem1497749)). Qed.
Lemma lem1497751 (x : real) (h1 : term70 x) : False.
Proof. exact (EQ_MP (@lem1497750) (@lem1497745 x h1)). Qed.
Lemma lem1497752 (x : real) (h1 : term73 x) : False.
Proof. exact (or_elim (@lem1497607 x h1) (fun h0 : term49 x => @lem1497679 x h0) (fun h0 : term70 x => @lem1497751 x h0)). Qed.
Lemma lem1497754 (x : real) (h1 : term73 x) : term73 x.
Proof. exact (h1). Qed.
Lemma lem1497755 (x : real) (h1 : term73 x) : (term73 x) = False.
Proof. exact (prop_ext (fun h2 : term73 x => @lem1497752 x h1) (fun h2 : False => @lem1497754 x h1)). Qed.
Lemma lem1497756 (x : real) (h1 : term73 x) : False.
Proof. exact (EQ_MP (@lem1497755 x h1) (@lem1497754 x h1)). Qed.
Lemma lem1497757 (h1 : term75) : term75.
Proof. exact (h1). Qed.
Lemma lem1497758 (h1 : term75) : False.
Proof. exact (ex_elim (@lem1497757 h1) (fun x : real => fun h0 : term74 x => @lem1497756 x h0)). Qed.
Lemma lem1497759 (h1 : term6) : term6.
Proof. exact (h1). Qed.
Lemma lem1497760 (h1 : term6) : term75.
Proof. exact (EQ_MP (@lem1497597) (@lem1497759 h1)). Qed.
Lemma lem1497761 (h1 : term6) : term75 = False.
Proof. exact (prop_ext (fun h2 : term75 => @lem1497758 h2) (fun h2 : False => @lem1497760 h1)). Qed.
Lemma lem1497762 (h1 : term6) : False.
Proof. exact (EQ_MP (@lem1497761 h1) (@lem1497760 h1)). Qed.
Lemma lem1497763 : term131.
Proof. exact (fun h0 : term6 => @lem1497762 h0). Qed.
Lemma lem1497764 : term132.
Proof. exact (@lem1386578 term133). Qed.
Lemma lem1497765 : term133.
Proof. exact (@lem1497764 (@lem1497763)). Qed.
