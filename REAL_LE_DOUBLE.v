Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_DOUBLE_term_abbrevs.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1483438_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
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
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem1505283 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17646 (term2 x) (term3 x)). Qed.
Lemma lem1505284 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1505285 : term6 = term7.
Proof. exact (@lem1505284 term8). Qed.
Lemma lem1505286 (x : real) : (term9 x) = ((term2 x) = (term3 x)).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1505287 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1505288 (x : real) : (term10 x) = (term0 x).
Proof. exact (MK_COMB (@lem1505287) (@lem1505286 x)). Qed.
Lemma lem1505289 (x : real) : (term10 x) = (term1 x).
Proof. exact (TRANS (@lem1505288 x) (@lem1505283 x)). Qed.
Lemma lem1505290 : term11 = term12.
Proof. exact (fun_ext (fun x : real => @lem1505289 x)). Qed.
Lemma lem1505291 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505292 : term7 = term13.
Proof. exact (MK_COMB (@lem1505291) (@lem1505290)). Qed.
Lemma lem1505294 : term6 = term13.
Proof. exact (TRANS (@lem1505285) (@lem1505292)). Qed.
Lemma lem1505311 (x : real) : (term1 x) = (term1 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1505312 : term12 = term12.
Proof. exact (fun_ext (fun x : real => @lem1505311 x)). Qed.
Lemma lem1505313 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505314 : term13 = term13.
Proof. exact (MK_COMB (@lem1505313) (@lem1505312)). Qed.
Lemma lem1505315 : term6 = term13.
Proof. exact (TRANS (@lem1505294) (@lem1505314)). Qed.
Lemma lem1505316 (x : real) : (term2 x) = (term14 x).
Proof. exact (@lem1483523 (real_add x x) term15). Qed.
Lemma lem1505317 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1505323 (x : real) : (real_add x x) = (term16 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1505324 : term17 = term18.
Proof. exact (@lem1367770 term19 term19). Qed.
Lemma lem1505325 : term20 = term21.
Proof. exact (@lem706885). Qed.
Lemma lem1505326 : (term20 = term21) = (term22 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term21). Qed.
Lemma lem1505327 : term22 = term23.
Proof. exact (EQ_MP (@lem1505326) (@lem1505325)). Qed.
Lemma lem1505328 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1505329 : term18 = term24.
Proof. exact (MK_COMB (@lem1505328) (@lem1505327)). Qed.
Lemma lem1505330 : term17 = term24.
Proof. exact (TRANS (@lem1505324) (@lem1505329)). Qed.
Lemma lem1505331 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1505332 : term25 = term26.
Proof. exact (MK_COMB (@lem1505331) (@lem1505330)). Qed.
Lemma lem1505333 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1505334 (x : real) : (term16 x) = (term27 x).
Proof. exact (MK_COMB (@lem1505332) (@lem1505333 x)). Qed.
Lemma lem1505336 (x : real) : (real_add x x) = (term27 x).
Proof. exact (TRANS (@lem1505323 x) (@lem1505334 x)). Qed.
Lemma lem1505337 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1505338 (x : real) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem1505337) (@lem1505336 x)). Qed.
Lemma lem1505339 (x : real) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem1505338 x) (@lem1505317)). Qed.
Lemma lem1505340 (x : real) : (term31 x) = (term32 x).
Proof. exact (@lem1483519 (term27 x) term15). Qed.
Lemma lem1505342 (x : nat) : (term33 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1505343 : term34 = term15.
Proof. exact (@lem1505342 term19). Qed.
Lemma lem1505344 (x : real) : (term35 x) = (term35 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1505345 (x : real) : (term32 x) = (term36 x).
Proof. exact (MK_COMB (@lem1505344 x) (@lem1505343)). Qed.
Lemma lem1505346 (x : real) : (term36 x) = (term27 x).
Proof. exact (@lem1483450 (term27 x)). Qed.
Lemma lem1505347 (x : real) : (term32 x) = (term27 x).
Proof. exact (TRANS (@lem1505345 x) (@lem1505346 x)). Qed.
Lemma lem1505348 (x : real) : (term31 x) = (term27 x).
Proof. exact (TRANS (@lem1505340 x) (@lem1505347 x)). Qed.
Lemma lem1505349 (x : real) : (term30 x) = (term27 x).
Proof. exact (TRANS (@lem1505339 x) (@lem1505348 x)). Qed.
Lemma lem1505350 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1505351 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1505350) (@lem1505349 x)). Qed.
Lemma lem1505352 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1505353 (x : real) : (term14 x) = (term39 x).
Proof. exact (MK_COMB (@lem1505351 x) (@lem1505352)). Qed.
Lemma lem1505354 (x : real) : (term2 x) = (term39 x).
Proof. exact (TRANS (@lem1505316 x) (@lem1505353 x)). Qed.
Lemma lem1505355 (x : real) : (term40 x) = (term41 x).
Proof. exact (@lem1483533 term15 x). Qed.
Lemma lem1505361 (x : real) : (term42 x) = (term43 x).
Proof. exact (@lem1483519 term15 x). Qed.
Lemma lem1505366 (x : real) : (term43 x) = (term44 x).
Proof. exact (@lem1483448 (term44 x)). Qed.
Lemma lem1505368 (x : real) : (term42 x) = (term44 x).
Proof. exact (TRANS (@lem1505361 x) (@lem1505366 x)). Qed.
Lemma lem1505369 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1505370 (x : real) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem1505369) (@lem1505368 x)). Qed.
Lemma lem1505371 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1505372 (x : real) : (term41 x) = (term47 x).
Proof. exact (MK_COMB (@lem1505370 x) (@lem1505371)). Qed.
Lemma lem1505373 (x : real) : (term40 x) = (term47 x).
Proof. exact (TRANS (@lem1505355 x) (@lem1505372 x)). Qed.
Lemma lem1505374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1505375 (x : real) : (term48 x) = (term49 x).
Proof. exact (MK_COMB (@lem1505374) (@lem1505354 x)). Qed.
Lemma lem1505376 (x : real) : (term50 x) = (term51 x).
Proof. exact (MK_COMB (@lem1505375 x) (@lem1505373 x)). Qed.
Lemma lem1505377 (x : real) : (term52 x) = (term53 x).
Proof. exact (@lem1483533 term15 (real_add x x)). Qed.
Lemma lem1505383 (x : real) : (real_add x x) = (term16 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1505384 : term17 = term18.
Proof. exact (@lem1367770 term19 term19). Qed.
Lemma lem1505385 : term20 = term21.
Proof. exact (@lem706885). Qed.
Lemma lem1505386 : (term20 = term21) = (term22 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term21). Qed.
Lemma lem1505387 : term22 = term23.
Proof. exact (EQ_MP (@lem1505386) (@lem1505385)). Qed.
Lemma lem1505388 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1505389 : term18 = term24.
Proof. exact (MK_COMB (@lem1505388) (@lem1505387)). Qed.
Lemma lem1505390 : term17 = term24.
Proof. exact (TRANS (@lem1505384) (@lem1505389)). Qed.
Lemma lem1505391 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1505392 : term25 = term26.
Proof. exact (MK_COMB (@lem1505391) (@lem1505390)). Qed.
Lemma lem1505393 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1505394 (x : real) : (term16 x) = (term27 x).
Proof. exact (MK_COMB (@lem1505392) (@lem1505393 x)). Qed.
Lemma lem1505396 (x : real) : (real_add x x) = (term27 x).
Proof. exact (TRANS (@lem1505383 x) (@lem1505394 x)). Qed.
Lemma lem1505399 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem1505400 (x : real) : (term55 x) = (term56 x).
Proof. exact (MK_COMB (@lem1505399) (@lem1505396 x)). Qed.
Lemma lem1505401 (x : real) : (term56 x) = (term57 x).
Proof. exact (@lem1483519 term15 (term27 x)). Qed.
Lemma lem1505402 (x : real) : (term58 x) = (term59 x).
Proof. exact (@lem1483476 term60 term24 x). Qed.
Lemma lem1505404 (m : nat) (n : nat) : (term61 m n) = (term62 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1505405 : term63 = term64.
Proof. exact (@lem1505404 term19 term23). Qed.
Lemma lem1505406 : term65 = term21.
Proof. exact (@lem996238 term21). Qed.
Lemma lem1505407 : (term65 = term21) = (term66 = term23).
Proof. exact (@lem1007663 (BIT1 0) term21 term21). Qed.
Lemma lem1505408 : term66 = term23.
Proof. exact (EQ_MP (@lem1505407) (@lem1505406)). Qed.
Lemma lem1505409 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1505410 : term67 = term24.
Proof. exact (MK_COMB (@lem1505409) (@lem1505408)). Qed.
Lemma lem1505411 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1505412 : term64 = term68.
Proof. exact (MK_COMB (@lem1505411) (@lem1505410)). Qed.
Lemma lem1505413 : term63 = term68.
Proof. exact (TRANS (@lem1505405) (@lem1505412)). Qed.
Lemma lem1505414 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1505415 : term69 = term70.
Proof. exact (MK_COMB (@lem1505414) (@lem1505413)). Qed.
Lemma lem1505416 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1505417 (x : real) : (term59 x) = (term71 x).
Proof. exact (MK_COMB (@lem1505415) (@lem1505416 x)). Qed.
Lemma lem1505418 (x : real) : (term58 x) = (term71 x).
Proof. exact (TRANS (@lem1505402 x) (@lem1505417 x)). Qed.
Lemma lem1505419 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem1505420 (x : real) : (term57 x) = (term73 x).
Proof. exact (MK_COMB (@lem1505419) (@lem1505418 x)). Qed.
Lemma lem1505421 (x : real) : (term73 x) = (term71 x).
Proof. exact (@lem1483448 (term71 x)). Qed.
Lemma lem1505422 (x : real) : (term57 x) = (term71 x).
Proof. exact (TRANS (@lem1505420 x) (@lem1505421 x)). Qed.
Lemma lem1505423 (x : real) : (term56 x) = (term71 x).
Proof. exact (TRANS (@lem1505401 x) (@lem1505422 x)). Qed.
Lemma lem1505424 (x : real) : (term55 x) = (term71 x).
Proof. exact (TRANS (@lem1505400 x) (@lem1505423 x)). Qed.
Lemma lem1505425 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1505426 (x : real) : (term74 x) = (term75 x).
Proof. exact (MK_COMB (@lem1505425) (@lem1505424 x)). Qed.
Lemma lem1505427 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1505428 (x : real) : (term53 x) = (term76 x).
Proof. exact (MK_COMB (@lem1505426 x) (@lem1505427)). Qed.
Lemma lem1505429 (x : real) : (term52 x) = (term76 x).
Proof. exact (TRANS (@lem1505377 x) (@lem1505428 x)). Qed.
Lemma lem1505430 (x : real) : (term3 x) = (term77 x).
Proof. exact (@lem1483523 x term15). Qed.
Lemma lem1505436 (x : real) : (term78 x) = (term79 x).
Proof. exact (@lem1483519 x term15). Qed.
Lemma lem1505438 (x : nat) : (term33 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1505439 : term34 = term15.
Proof. exact (@lem1505438 term19). Qed.
Lemma lem1505440 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1505441 (x : real) : (term79 x) = (term80 x).
Proof. exact (MK_COMB (@lem1505440 x) (@lem1505439)). Qed.
Lemma lem1505442 (x : real) : (term80 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1505443 (x : real) : (term79 x) = x.
Proof. exact (TRANS (@lem1505441 x) (@lem1505442 x)). Qed.
Lemma lem1505445 (x : real) : (term78 x) = x.
Proof. exact (TRANS (@lem1505436 x) (@lem1505443 x)). Qed.
Lemma lem1505446 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1505447 (x : real) : (term81 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1505446) (@lem1505445 x)). Qed.
Lemma lem1505448 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1505449 (x : real) : (term77 x) = (term82 x).
Proof. exact (MK_COMB (@lem1505447 x) (@lem1505448)). Qed.
Lemma lem1505450 (x : real) : (term3 x) = (term82 x).
Proof. exact (TRANS (@lem1505430 x) (@lem1505449 x)). Qed.
Lemma lem1505451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1505452 (x : real) : (term83 x) = (term84 x).
Proof. exact (MK_COMB (@lem1505451) (@lem1505429 x)). Qed.
Lemma lem1505453 (x : real) : (term85 x) = (term86 x).
Proof. exact (MK_COMB (@lem1505452 x) (@lem1505450 x)). Qed.
Lemma lem1505454 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1505455 (x : real) : (term87 x) = (term88 x).
Proof. exact (MK_COMB (@lem1505454) (@lem1505376 x)). Qed.
Lemma lem1505456 (x : real) : (term1 x) = (term89 x).
Proof. exact (MK_COMB (@lem1505455 x) (@lem1505453 x)). Qed.
Lemma lem1505457 : term12 = term90.
Proof. exact (fun_ext (fun x : real => @lem1505456 x)). Qed.
Lemma lem1505458 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505459 : term13 = term91.
Proof. exact (MK_COMB (@lem1505458) (@lem1505457)). Qed.
Lemma lem1505460 : term6 = term91.
Proof. exact (TRANS (@lem1505315) (@lem1505459)). Qed.
Lemma lem1505462 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1505463 (P : real -> Prop) (Q : real -> Prop) : (term94 P Q) = (term95 P Q).
Proof. exact (@lem1505462 real P Q). Qed.
Lemma lem1505464 : term96 = term97.
Proof. exact (@lem1505463 term98 term99). Qed.
Lemma lem1505465 (x : real) : (term100 x) = (term51 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1505466 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1505467 (x : real) : (term101 x) = (term88 x).
Proof. exact (MK_COMB (@lem1505466) (@lem1505465 x)). Qed.
Lemma lem1505468 (x : real) : (term102 x) = (term86 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1505469 (x : real) : (term103 x) = (term89 x).
Proof. exact (MK_COMB (@lem1505467 x) (@lem1505468 x)). Qed.
Lemma lem1505470 : term104 = term90.
Proof. exact (fun_ext (fun x : real => @lem1505469 x)). Qed.
Lemma lem1505471 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505472 : term96 = term91.
Proof. exact (MK_COMB (@lem1505471) (@lem1505470)). Qed.
Lemma lem1505473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1505474 : term105 = term106.
Proof. exact (MK_COMB (@lem1505473) (@lem1505472)). Qed.
Lemma lem1505475 (x : real) : (term100 x) = (term51 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1505476 : term107 = term98.
Proof. exact (fun_ext (fun x : real => @lem1505475 x)). Qed.
Lemma lem1505477 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505478 : term108 = term109.
Proof. exact (MK_COMB (@lem1505477) (@lem1505476)). Qed.
Lemma lem1505479 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1505480 : term110 = term111.
Proof. exact (MK_COMB (@lem1505479) (@lem1505478)). Qed.
Lemma lem1505481 (x : real) : (term102 x) = (term86 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1505482 : term112 = term99.
Proof. exact (fun_ext (fun x : real => @lem1505481 x)). Qed.
Lemma lem1505483 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505484 : term113 = term114.
Proof. exact (MK_COMB (@lem1505483) (@lem1505482)). Qed.
Lemma lem1505485 : term97 = term115.
Proof. exact (MK_COMB (@lem1505480) (@lem1505484)). Qed.
Lemma lem1505486 : (term96 = term97) = (term91 = term115).
Proof. exact (MK_COMB (@lem1505474) (@lem1505485)). Qed.
Lemma lem1505487 : term91 = term115.
Proof. exact (EQ_MP (@lem1505486) (@lem1505464)). Qed.
Lemma lem1505585 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1505586 (P : real -> Prop) (Q : real -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem1505585 real P Q). Qed.
Lemma lem1505587 : term97 = term96.
Proof. exact (@lem1505586 term98 term99). Qed.
Lemma lem1505588 (x : real) : (term100 x) = (term51 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1505589 : term107 = term98.
Proof. exact (fun_ext (fun x : real => @lem1505588 x)). Qed.
Lemma lem1505590 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505591 : term108 = term109.
Proof. exact (MK_COMB (@lem1505590) (@lem1505589)). Qed.
Lemma lem1505592 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1505593 : term110 = term111.
Proof. exact (MK_COMB (@lem1505592) (@lem1505591)). Qed.
Lemma lem1505594 (x : real) : (term102 x) = (term86 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1505595 : term112 = term99.
Proof. exact (fun_ext (fun x : real => @lem1505594 x)). Qed.
Lemma lem1505596 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505597 : term113 = term114.
Proof. exact (MK_COMB (@lem1505596) (@lem1505595)). Qed.
Lemma lem1505598 : term97 = term115.
Proof. exact (MK_COMB (@lem1505593) (@lem1505597)). Qed.
Lemma lem1505599 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1505600 : term116 = term117.
Proof. exact (MK_COMB (@lem1505599) (@lem1505598)). Qed.
Lemma lem1505601 (x : real) : (term100 x) = (term51 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1505602 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1505603 (x : real) : (term101 x) = (term88 x).
Proof. exact (MK_COMB (@lem1505602) (@lem1505601 x)). Qed.
Lemma lem1505604 (x : real) : (term102 x) = (term86 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1505605 (x : real) : (term103 x) = (term89 x).
Proof. exact (MK_COMB (@lem1505603 x) (@lem1505604 x)). Qed.
Lemma lem1505606 : term104 = term90.
Proof. exact (fun_ext (fun x : real => @lem1505605 x)). Qed.
Lemma lem1505607 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505608 : term96 = term91.
Proof. exact (MK_COMB (@lem1505607) (@lem1505606)). Qed.
Lemma lem1505609 : (term97 = term96) = (term115 = term91).
Proof. exact (MK_COMB (@lem1505600) (@lem1505608)). Qed.
Lemma lem1505610 : term115 = term91.
Proof. exact (EQ_MP (@lem1505609) (@lem1505587)). Qed.
Lemma lem1505611 : term91 = term91.
Proof. exact (TRANS (@lem1505487) (@lem1505610)). Qed.
Lemma lem1505614 : term6 = term91.
Proof. exact (TRANS (@lem1505460) (@lem1505611)). Qed.
Lemma lem1505631 (x : real) : (term89 x) = (term89 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1505632 : term90 = term90.
Proof. exact (fun_ext (fun x : real => @lem1505631 x)). Qed.
Lemma lem1505633 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505634 : term91 = term91.
Proof. exact (MK_COMB (@lem1505633) (@lem1505632)). Qed.
Lemma lem1505635 : term6 = term91.
Proof. exact (TRANS (@lem1505614) (@lem1505634)). Qed.
Lemma lem1505645 (x : real) (h1 : term89 x) : term89 x.
Proof. exact (h1). Qed.
Lemma lem1505646 (x : real) (h1 : term51 x) : term51 x.
Proof. exact (h1). Qed.
Lemma lem1505647 (x : real) (h1 : term51 x) : term47 x.
Proof. exact (proj2 (@lem1505646 x h1)). Qed.
Lemma lem1505648 (x : real) (h1 : term51 x) : term39 x.
Proof. exact (proj1 (@lem1505646 x h1)). Qed.
Lemma lem1505650 (n : nat) (m : nat) : (term118 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1505651 : term119 = term120.
Proof. exact (@lem1505650 (NUMERAL 0) term19). Qed.
Lemma lem1505652 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1505653 (h1 : term121 = (BIT1 0)) : term120 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1505654 : (term121 = (BIT1 0)) = (term120 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem1505653 h1) (fun h1 : term120 = True => @lem1505652)). Qed.
Lemma lem1505655 : term120 = True.
Proof. exact (EQ_MP (@lem1505654) (@lem1505652)). Qed.
Lemma lem1505656 : term119 = True.
Proof. exact (TRANS (@lem1505651) (@lem1505655)). Qed.
Lemma lem1505657 : True = term119.
Proof. exact (SYM (@lem1505656)). Qed.
Lemma lem1505658 : term119.
Proof. exact (EQ_MP (@lem1505657) (@lem0)). Qed.
Lemma lem1505659 (x : real) (h1 : term51 x) : term122 x.
Proof. exact (conj (@lem1505658) (@lem1505648 x h1)). Qed.
Lemma lem1505661 (x : real) (y : real) : term123 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1505662 (x : real) : term124 x.
Proof. exact (@lem1505661 term125 (term27 x)). Qed.
Lemma lem1505663 (x : real) (h1 : term51 x) : term126 x.
Proof. exact (@lem1505662 x (@lem1505659 x h1)). Qed.
Lemma lem1505664 (x : real) : (term127 x) = (term27 x).
Proof. exact (@lem1483460 (term27 x)). Qed.
Lemma lem1505665 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1505666 (x : real) : (term128 x) = (term38 x).
Proof. exact (MK_COMB (@lem1505665) (@lem1505664 x)). Qed.
Lemma lem1505667 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1505668 (x : real) : (term126 x) = (term39 x).
Proof. exact (MK_COMB (@lem1505666 x) (@lem1505667)). Qed.
Lemma lem1505669 (x : real) (h1 : term51 x) : term39 x.
Proof. exact (EQ_MP (@lem1505668 x) (@lem1505663 x h1)). Qed.
Lemma lem1505671 (n : nat) (m : nat) : (term118 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1505672 : term129 = term130.
Proof. exact (@lem1505671 (NUMERAL 0) term23). Qed.
Lemma lem1505673 : term131 = term21.
Proof. exact (@lem912803). Qed.
Lemma lem1505674 (h1 : term131 = term21) : term130 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term21 h1). Qed.
Lemma lem1505675 : (term131 = term21) = (term130 = True).
Proof. exact (prop_ext (fun h1 : term131 = term21 => @lem1505674 h1) (fun h1 : term130 = True => @lem1505673)). Qed.
Lemma lem1505676 : term130 = True.
Proof. exact (EQ_MP (@lem1505675) (@lem1505673)). Qed.
Lemma lem1505677 : term129 = True.
Proof. exact (TRANS (@lem1505672) (@lem1505676)). Qed.
Lemma lem1505678 : True = term129.
Proof. exact (SYM (@lem1505677)). Qed.
Lemma lem1505679 : term129.
Proof. exact (EQ_MP (@lem1505678) (@lem0)). Qed.
Lemma lem1505680 (x : real) (h1 : term51 x) : term132 x.
Proof. exact (conj (@lem1505679) (@lem1505647 x h1)). Qed.
Lemma lem1505682 (x : real) (y : real) : term133 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1505683 (x : real) : term134 x.
Proof. exact (@lem1505682 term24 (term44 x)). Qed.
Lemma lem1505684 (x : real) (h1 : term51 x) : term135 x.
Proof. exact (@lem1505683 x (@lem1505680 x h1)). Qed.
Lemma lem1505685 (x : real) : (term136 x) = (term137 x).
Proof. exact (@lem1483476 term24 term60 x). Qed.
Lemma lem1505687 (m : nat) (n : nat) : (term138 m n) = (term62 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1505688 : term139 = term140.
Proof. exact (@lem1505687 term23 term19). Qed.
Lemma lem1505689 : term141 = term21.
Proof. exact (@lem996237 term21). Qed.
Lemma lem1505690 : (term141 = term21) = (term142 = term23).
Proof. exact (@lem1007663 term21 (BIT1 0) term21). Qed.
Lemma lem1505691 : term142 = term23.
Proof. exact (EQ_MP (@lem1505690) (@lem1505689)). Qed.
Lemma lem1505692 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1505693 : term143 = term24.
Proof. exact (MK_COMB (@lem1505692) (@lem1505691)). Qed.
Lemma lem1505694 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1505695 : term140 = term68.
Proof. exact (MK_COMB (@lem1505694) (@lem1505693)). Qed.
Lemma lem1505696 : term139 = term68.
Proof. exact (TRANS (@lem1505688) (@lem1505695)). Qed.
Lemma lem1505697 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1505698 : term144 = term70.
Proof. exact (MK_COMB (@lem1505697) (@lem1505696)). Qed.
Lemma lem1505699 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1505700 (x : real) : (term137 x) = (term71 x).
Proof. exact (MK_COMB (@lem1505698) (@lem1505699 x)). Qed.
Lemma lem1505701 (x : real) : (term136 x) = (term71 x).
Proof. exact (TRANS (@lem1505685 x) (@lem1505700 x)). Qed.
Lemma lem1505702 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1505703 (x : real) : (term145 x) = (term75 x).
Proof. exact (MK_COMB (@lem1505702) (@lem1505701 x)). Qed.
Lemma lem1505704 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1505705 (x : real) : (term135 x) = (term76 x).
Proof. exact (MK_COMB (@lem1505703 x) (@lem1505704)). Qed.
Lemma lem1505706 (x : real) (h1 : term51 x) : term76 x.
Proof. exact (EQ_MP (@lem1505705 x) (@lem1505684 x h1)). Qed.
Lemma lem1505707 (x : real) (h1 : term51 x) : term146 x.
Proof. exact (conj (@lem1505706 x h1) (@lem1505669 x h1)). Qed.
Lemma lem1505709 (x : real) (y : real) : term147 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1505710 (x : real) : term148 x.
Proof. exact (@lem1505709 (term71 x) (term27 x)). Qed.
Lemma lem1505711 (x : real) (h1 : term51 x) : term149 x.
Proof. exact (@lem1505710 x (@lem1505707 x h1)). Qed.
Lemma lem1505712 (x : real) : (term150 x) = (term151 x).
Proof. exact (@lem1483438 term68 term24 x). Qed.
Lemma lem1505714 (m : nat) : (term152 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1505715 : term153 = term15.
Proof. exact (@lem1505714 term23). Qed.
Lemma lem1505716 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1505717 : term154 = term155.
Proof. exact (MK_COMB (@lem1505716) (@lem1505715)). Qed.
Lemma lem1505718 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1505719 (x : real) : (term151 x) = (term156 x).
Proof. exact (MK_COMB (@lem1505717) (@lem1505718 x)). Qed.
Lemma lem1505720 (x : real) : (term150 x) = (term156 x).
Proof. exact (TRANS (@lem1505712 x) (@lem1505719 x)). Qed.
Lemma lem1505721 (x : real) : (term156 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1505722 (x : real) : (term150 x) = term15.
Proof. exact (TRANS (@lem1505720 x) (@lem1505721 x)). Qed.
Lemma lem1505723 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1505724 (x : real) : (term157 x) = term158.
Proof. exact (MK_COMB (@lem1505723) (@lem1505722 x)). Qed.
Lemma lem1505725 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1505726 (x : real) : (term149 x) = term159.
Proof. exact (MK_COMB (@lem1505724 x) (@lem1505725)). Qed.
Lemma lem1505727 (x : real) (h1 : term51 x) : term159.
Proof. exact (EQ_MP (@lem1505726 x) (@lem1505711 x h1)). Qed.
Lemma lem1505729 (n : nat) (m : nat) : (term118 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1505730 : term159 = term160.
Proof. exact (@lem1505729 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1505731 : term160 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1505732 : term159 = False.
Proof. exact (TRANS (@lem1505730) (@lem1505731)). Qed.
Lemma lem1505733 (x : real) (h1 : term51 x) : False.
Proof. exact (EQ_MP (@lem1505732) (@lem1505727 x h1)). Qed.
Lemma lem1505734 (x : real) (h1 : term86 x) : term86 x.
Proof. exact (h1). Qed.
Lemma lem1505735 (x : real) (h1 : term86 x) : term82 x.
Proof. exact (proj2 (@lem1505734 x h1)). Qed.
Lemma lem1505736 (x : real) (h1 : term86 x) : term76 x.
Proof. exact (proj1 (@lem1505734 x h1)). Qed.
Lemma lem1505738 (n : nat) (m : nat) : (term118 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1505739 : term129 = term130.
Proof. exact (@lem1505738 (NUMERAL 0) term23). Qed.
Lemma lem1505740 : term131 = term21.
Proof. exact (@lem912803). Qed.
Lemma lem1505741 (h1 : term131 = term21) : term130 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term21 h1). Qed.
Lemma lem1505742 : (term131 = term21) = (term130 = True).
Proof. exact (prop_ext (fun h1 : term131 = term21 => @lem1505741 h1) (fun h1 : term130 = True => @lem1505740)). Qed.
Lemma lem1505743 : term130 = True.
Proof. exact (EQ_MP (@lem1505742) (@lem1505740)). Qed.
Lemma lem1505744 : term129 = True.
Proof. exact (TRANS (@lem1505739) (@lem1505743)). Qed.
Lemma lem1505745 : True = term129.
Proof. exact (SYM (@lem1505744)). Qed.
Lemma lem1505746 : term129.
Proof. exact (EQ_MP (@lem1505745) (@lem0)). Qed.
Lemma lem1505747 (x : real) (h1 : term86 x) : term161 x.
Proof. exact (conj (@lem1505746) (@lem1505735 x h1)). Qed.
Lemma lem1505749 (x : real) (y : real) : term123 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1505750 (x : real) : term162 x.
Proof. exact (@lem1505749 term24 x). Qed.
Lemma lem1505757 (x : real) (h1 : term86 x) : term39 x.
Proof. exact (@lem1505750 x (@lem1505747 x h1)). Qed.
Lemma lem1505759 (n : nat) (m : nat) : (term118 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1505760 : term119 = term120.
Proof. exact (@lem1505759 (NUMERAL 0) term19). Qed.
Lemma lem1505761 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1505762 (h1 : term121 = (BIT1 0)) : term120 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1505763 : (term121 = (BIT1 0)) = (term120 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem1505762 h1) (fun h1 : term120 = True => @lem1505761)). Qed.
Lemma lem1505764 : term120 = True.
Proof. exact (EQ_MP (@lem1505763) (@lem1505761)). Qed.
Lemma lem1505765 : term119 = True.
Proof. exact (TRANS (@lem1505760) (@lem1505764)). Qed.
Lemma lem1505766 : True = term119.
Proof. exact (SYM (@lem1505765)). Qed.
Lemma lem1505767 : term119.
Proof. exact (EQ_MP (@lem1505766) (@lem0)). Qed.
Lemma lem1505768 (x : real) (h1 : term86 x) : term163 x.
Proof. exact (conj (@lem1505767) (@lem1505736 x h1)). Qed.
Lemma lem1505770 (x : real) (y : real) : term133 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1505771 (x : real) : term164 x.
Proof. exact (@lem1505770 term125 (term71 x)). Qed.
Lemma lem1505772 (x : real) (h1 : term86 x) : term165 x.
Proof. exact (@lem1505771 x (@lem1505768 x h1)). Qed.
Lemma lem1505773 (x : real) : (term166 x) = (term71 x).
Proof. exact (@lem1483460 (term71 x)). Qed.
Lemma lem1505774 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1505775 (x : real) : (term167 x) = (term75 x).
Proof. exact (MK_COMB (@lem1505774) (@lem1505773 x)). Qed.
Lemma lem1505776 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1505777 (x : real) : (term165 x) = (term76 x).
Proof. exact (MK_COMB (@lem1505775 x) (@lem1505776)). Qed.
Lemma lem1505778 (x : real) (h1 : term86 x) : term76 x.
Proof. exact (EQ_MP (@lem1505777 x) (@lem1505772 x h1)). Qed.
Lemma lem1505779 (x : real) (h1 : term86 x) : term146 x.
Proof. exact (conj (@lem1505778 x h1) (@lem1505757 x h1)). Qed.
Lemma lem1505781 (x : real) (y : real) : term147 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1505782 (x : real) : term148 x.
Proof. exact (@lem1505781 (term71 x) (term27 x)). Qed.
Lemma lem1505783 (x : real) (h1 : term86 x) : term149 x.
Proof. exact (@lem1505782 x (@lem1505779 x h1)). Qed.
Lemma lem1505784 (x : real) : (term150 x) = (term151 x).
Proof. exact (@lem1483438 term68 term24 x). Qed.
Lemma lem1505786 (m : nat) : (term152 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1505787 : term153 = term15.
Proof. exact (@lem1505786 term23). Qed.
Lemma lem1505788 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1505789 : term154 = term155.
Proof. exact (MK_COMB (@lem1505788) (@lem1505787)). Qed.
Lemma lem1505790 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1505791 (x : real) : (term151 x) = (term156 x).
Proof. exact (MK_COMB (@lem1505789) (@lem1505790 x)). Qed.
Lemma lem1505792 (x : real) : (term150 x) = (term156 x).
Proof. exact (TRANS (@lem1505784 x) (@lem1505791 x)). Qed.
Lemma lem1505793 (x : real) : (term156 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1505794 (x : real) : (term150 x) = term15.
Proof. exact (TRANS (@lem1505792 x) (@lem1505793 x)). Qed.
Lemma lem1505795 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1505796 (x : real) : (term157 x) = term158.
Proof. exact (MK_COMB (@lem1505795) (@lem1505794 x)). Qed.
Lemma lem1505797 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1505798 (x : real) : (term149 x) = term159.
Proof. exact (MK_COMB (@lem1505796 x) (@lem1505797)). Qed.
Lemma lem1505799 (x : real) (h1 : term86 x) : term159.
Proof. exact (EQ_MP (@lem1505798 x) (@lem1505783 x h1)). Qed.
Lemma lem1505801 (n : nat) (m : nat) : (term118 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1505802 : term159 = term160.
Proof. exact (@lem1505801 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1505803 : term160 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1505804 : term159 = False.
Proof. exact (TRANS (@lem1505802) (@lem1505803)). Qed.
Lemma lem1505805 (x : real) (h1 : term86 x) : False.
Proof. exact (EQ_MP (@lem1505804) (@lem1505799 x h1)). Qed.
Lemma lem1505806 (x : real) (h1 : term89 x) : False.
Proof. exact (or_elim (@lem1505645 x h1) (fun h0 : term51 x => @lem1505733 x h0) (fun h0 : term86 x => @lem1505805 x h0)). Qed.
Lemma lem1505808 (x : real) (h1 : term89 x) : term89 x.
Proof. exact (h1). Qed.
Lemma lem1505809 (x : real) (h1 : term89 x) : (term89 x) = False.
Proof. exact (prop_ext (fun h2 : term89 x => @lem1505806 x h1) (fun h2 : False => @lem1505808 x h1)). Qed.
Lemma lem1505810 (x : real) (h1 : term89 x) : False.
Proof. exact (EQ_MP (@lem1505809 x h1) (@lem1505808 x h1)). Qed.
Lemma lem1505811 (h1 : term91) : term91.
Proof. exact (h1). Qed.
Lemma lem1505812 (h1 : term91) : False.
Proof. exact (ex_elim (@lem1505811 h1) (fun x : real => fun h0 : term90 x => @lem1505810 x h0)). Qed.
Lemma lem1505813 (h1 : term6) : term6.
Proof. exact (h1). Qed.
Lemma lem1505814 (h1 : term6) : term91.
Proof. exact (EQ_MP (@lem1505635) (@lem1505813 h1)). Qed.
Lemma lem1505815 (h1 : term6) : term91 = False.
Proof. exact (prop_ext (fun h2 : term91 => @lem1505812 h2) (fun h2 : False => @lem1505814 h1)). Qed.
Lemma lem1505816 (h1 : term6) : False.
Proof. exact (EQ_MP (@lem1505815 h1) (@lem1505814 h1)). Qed.
Lemma lem1505817 : term168.
Proof. exact (fun h0 : term6 => @lem1505816 h0). Qed.
Lemma lem1505818 : term169.
Proof. exact (@lem1386578 term170). Qed.
Lemma lem1505819 : term170.
Proof. exact (@lem1505818 (@lem1505817)). Qed.
