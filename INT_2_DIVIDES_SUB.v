Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_2_DIVIDES_SUB_term_abbrevs.
Require Import INT_REM_2_CASES_spec.
Require Import INT_REM_2_DIVIDES_spec.
Require Import INT_SUB_REM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1009824_spec.
Require Import thm1011471_spec.
Require Import thm1011992_spec.
Require Import thm1013352_spec.
Require Import thm1855_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2403914_spec.
Require Import thm2404231_spec.
Require Import thm2405481_spec.
Require Import thm2405528_spec.
Require Import thm2405621_spec.
Require Import thm2405757_spec.
Require Import thm2405813_spec.
Require Import thm2406277_spec.
Require Import thm2406280_spec.
Require Import thm2406281_spec.
Require Import thm2406287_spec.
Require Import thm2406288_spec.
Require Import thm2406442_spec.
Require Import thm2743639_spec.
Require Import thm706819_spec.
Require Import thm706821_spec.
Require Import thm706883_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912741_spec.
Require Import thm912803_spec.
Require Import thm996238_spec.
Lemma lem2744355 (n : int) : term0 n.
Proof. exact (@lem2716252 n). Qed.
Lemma lem2744356 (n : int) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2744357 (n : int) : term1 n.
Proof. exact (EQ_MP (@lem2744356 n) (@lem2744355 n)). Qed.
Lemma lem2744360 (m : int) : term0 m.
Proof. exact (@lem2716252 m). Qed.
Lemma lem2744361 (m : int) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2744362 (m : int) : term1 m.
Proof. exact (EQ_MP (@lem2744361 m) (@lem2744360 m)). Qed.
Lemma lem2744368 (m : int) (n : int) (p : int) (h1 : (term2 m n p) = (term3 m n p)) : (term2 m n p) = (term3 m n p).
Proof. exact (h1). Qed.
Lemma lem2744369 (m : int) (n : int) (p : int) (h1 : (term2 m n p) = (term3 m n p)) : (term3 m n p) = (term2 m n p).
Proof. exact (SYM (@lem2744368 m n p h1)). Qed.
Lemma lem2744370 (m : int) (n : int) (p : int) (h1 : (term3 m n p) = (term2 m n p)) : (term3 m n p) = (term2 m n p).
Proof. exact (h1). Qed.
Lemma lem2744371 (m : int) (n : int) (p : int) (h1 : (term3 m n p) = (term2 m n p)) : (term2 m n p) = (term3 m n p).
Proof. exact (SYM (@lem2744370 m n p h1)). Qed.
Lemma lem2744372 (m : int) (n : int) (p : int) : ((term2 m n p) = (term3 m n p)) = ((term3 m n p) = (term2 m n p)).
Proof. exact (prop_ext (fun h1 : (term2 m n p) = (term3 m n p) => @lem2744369 m n p h1) (fun h1 : (term3 m n p) = (term2 m n p) => @lem2744371 m n p h1)). Qed.
Lemma lem2744373 (m : int) (n : int) : (term4 m n) = (term5 m n).
Proof. exact (fun_ext (fun p : int => @lem2744372 m n p)). Qed.
Lemma lem2744374 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2744375 (m : int) (n : int) : (term6 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem2744374) (@lem2744373 m n)). Qed.
Lemma lem2744376 (m : int) : (term8 m) = (term9 m).
Proof. exact (fun_ext (fun n : int => @lem2744375 m n)). Qed.
Lemma lem2744377 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2744378 (m : int) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem2744377) (@lem2744376 m)). Qed.
Lemma lem2744379 : term12 = term13.
Proof. exact (fun_ext (fun m : int => @lem2744378 m)). Qed.
Lemma lem2744380 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2744381 : term14 = term15.
Proof. exact (MK_COMB (@lem2744380) (@lem2744379)). Qed.
Lemma lem2744382 : term15.
Proof. exact (EQ_MP (@lem2744381) (@lem2535923)). Qed.
Lemma lem2744383 (m : int) : term16 m.
Proof. exact (@lem2744382 m). Qed.
Lemma lem2744384 (m : int) : (term16 m) = (term11 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem2744385 (m : int) : term11 m.
Proof. exact (EQ_MP (@lem2744384 m) (@lem2744383 m)). Qed.
Lemma lem2744386 (m : int) (n : int) : term17 m n.
Proof. exact (@lem2744385 m n). Qed.
Lemma lem2744387 (m : int) (n : int) : (term17 m n) = (term7 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem2744388 (m : int) (n : int) : term7 m n.
Proof. exact (EQ_MP (@lem2744387 m n) (@lem2744386 m n)). Qed.
Lemma lem2744389 (m : int) (n : int) (p : int) : term18 m n p.
Proof. exact (@lem2744388 m n p). Qed.
Lemma lem2744390 (m : int) (n : int) (p : int) : (term18 m n p) = ((term3 m n p) = (term2 m n p)).
Proof. exact (eq_refl (term18 m n p)). Qed.
Lemma lem2744394 (n : int) (h1 : ((term19 n) = term20) = (term21 n)) : ((term19 n) = term20) = (term21 n).
Proof. exact (h1). Qed.
Lemma lem2744395 (n : int) (h1 : ((term19 n) = term20) = (term21 n)) : (term21 n) = ((term19 n) = term20).
Proof. exact (SYM (@lem2744394 n h1)). Qed.
Lemma lem2744396 (n : int) (h1 : (term21 n) = ((term19 n) = term20)) : (term21 n) = ((term19 n) = term20).
Proof. exact (h1). Qed.
Lemma lem2744397 (n : int) (h1 : (term21 n) = ((term19 n) = term20)) : ((term19 n) = term20) = (term21 n).
Proof. exact (SYM (@lem2744396 n h1)). Qed.
Lemma lem2744398 (n : int) : (((term19 n) = term20) = (term21 n)) = ((term21 n) = ((term19 n) = term20)).
Proof. exact (prop_ext (fun h1 : ((term19 n) = term20) = (term21 n) => @lem2744395 n h1) (fun h1 : (term21 n) = ((term19 n) = term20) => @lem2744397 n h1)). Qed.
Lemma lem2744399 : term22 = term23.
Proof. exact (fun_ext (fun n : int => @lem2744398 n)). Qed.
Lemma lem2744400 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2744401 : term24 = term25.
Proof. exact (MK_COMB (@lem2744400) (@lem2744399)). Qed.
Lemma lem2744402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2744403 : term26 = term27.
Proof. exact (MK_COMB (@lem2744402) (@lem2744401)). Qed.
Lemma lem2744405 (n : int) (h1 : ((term19 n) = term28) = (term29 n)) : ((term19 n) = term28) = (term29 n).
Proof. exact (h1). Qed.
Lemma lem2744406 (n : int) (h1 : ((term19 n) = term28) = (term29 n)) : (term29 n) = ((term19 n) = term28).
Proof. exact (SYM (@lem2744405 n h1)). Qed.
Lemma lem2744407 (n : int) (h1 : (term29 n) = ((term19 n) = term28)) : (term29 n) = ((term19 n) = term28).
Proof. exact (h1). Qed.
Lemma lem2744408 (n : int) (h1 : (term29 n) = ((term19 n) = term28)) : ((term19 n) = term28) = (term29 n).
Proof. exact (SYM (@lem2744407 n h1)). Qed.
Lemma lem2744409 (n : int) : (((term19 n) = term28) = (term29 n)) = ((term29 n) = ((term19 n) = term28)).
Proof. exact (prop_ext (fun h1 : ((term19 n) = term28) = (term29 n) => @lem2744406 n h1) (fun h1 : (term29 n) = ((term19 n) = term28) => @lem2744408 n h1)). Qed.
Lemma lem2744410 : term30 = term31.
Proof. exact (fun_ext (fun n : int => @lem2744409 n)). Qed.
Lemma lem2744411 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2744412 : term32 = term33.
Proof. exact (MK_COMB (@lem2744411) (@lem2744410)). Qed.
Lemma lem2744413 : term34 = term35.
Proof. exact (MK_COMB (@lem2744403) (@lem2744412)). Qed.
Lemma lem2744414 : term35.
Proof. exact (EQ_MP (@lem2744413) (@lem2725348)). Qed.
Lemma lem2744419 : term25.
Proof. exact (proj1 (@lem2744414)). Qed.
Lemma lem2744420 (n : int) : term36 n.
Proof. exact (@lem2744419 n). Qed.
Lemma lem2744421 (n : int) : (term36 n) = ((term21 n) = ((term19 n) = term20)).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem2744426 (n : int) : (term21 n) = ((term19 n) = term20).
Proof. exact (EQ_MP (@lem2744421 n) (@lem2744420 n)). Qed.
Lemma lem2744427 (m : int) (n : int) : (term37 m n) = ((term38 m n) = term20).
Proof. exact (@lem2744426 (int_sub m n)). Qed.
Lemma lem2744430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2744431 (m : int) (n : int) : (term39 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem2744430) (@lem2744427 m n)). Qed.
Lemma lem2744435 (n : int) : (term21 n) = ((term19 n) = term20).
Proof. exact (EQ_MP (@lem2744421 n) (@lem2744420 n)). Qed.
Lemma lem2744436 (m : int) : (term21 m) = ((term19 m) = term20).
Proof. exact (@lem2744435 m). Qed.
Lemma lem2744439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2744440 (m : int) : (term41 m) = (term42 m).
Proof. exact (MK_COMB (@lem2744439) (@lem2744436 m)). Qed.
Lemma lem2744442 (n : int) : (term21 n) = ((term19 n) = term20).
Proof. exact (EQ_MP (@lem2744421 n) (@lem2744420 n)). Qed.
Lemma lem2744445 (m : int) (n : int) : ((term21 m) = (term21 n)) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (MK_COMB (@lem2744440 m) (@lem2744442 n)). Qed.
Lemma lem2744448 (m : int) (n : int) : ((term37 m n) = ((term21 m) = (term21 n))) = (((term38 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))).
Proof. exact (MK_COMB (@lem2744431 m n) (@lem2744445 m n)). Qed.
Lemma lem2744451 (m : int) (n : int) : (((term38 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = ((term37 m n) = ((term21 m) = (term21 n))).
Proof. exact (SYM (@lem2744448 m n)). Qed.
Lemma lem2744457 (m : int) (n : int) (p : int) : (term3 m n p) = (term2 m n p).
Proof. exact (EQ_MP (@lem2744390 m n p) (@lem2744389 m n p)). Qed.
Lemma lem2744458 (m : int) (n : int) : (term38 m n) = (term43 m n).
Proof. exact (@lem2744457 m n term44). Qed.
Lemma lem2744459 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744460 (m : int) (n : int) : (term45 m n) = (term46 m n).
Proof. exact (MK_COMB (@lem2744459) (@lem2744458 m n)). Qed.
Lemma lem2744461 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744462 (m : int) (n : int) : ((term38 m n) = term20) = ((term43 m n) = term20).
Proof. exact (MK_COMB (@lem2744460 m n) (@lem2744461)). Qed.
Lemma lem2744463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2744464 (m : int) (n : int) : (term40 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem2744463) (@lem2744462 m n)). Qed.
Lemma lem2744471 (m : int) (n : int) : (((term19 m) = term20) = ((term19 n) = term20)) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (eq_refl (((term19 m) = term20) = ((term19 n) = term20))). Qed.
Lemma lem2744472 (m : int) (n : int) : (((term38 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))).
Proof. exact (MK_COMB (@lem2744464 m n) (@lem2744471 m n)). Qed.
Lemma lem2744473 (m : int) (n : int) : (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = (((term38 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))).
Proof. exact (SYM (@lem2744472 m n)). Qed.
Lemma lem2744479 (m : int) (h1 : (term19 m) = term20) : (term19 m) = term20.
Proof. exact (h1). Qed.
Lemma lem2744480 : int_sub = int_sub.
Proof. exact (eq_refl int_sub). Qed.
Lemma lem2744481 (m : int) (h1 : (term19 m) = term20) : (term48 m) = term49.
Proof. exact (MK_COMB (@lem2744480) (@lem2744479 m h1)). Qed.
Lemma lem2744483 (n : int) (h1 : (term19 n) = term20) : (term19 n) = term20.
Proof. exact (h1). Qed.
Lemma lem2744484 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term50 m n) = term51.
Proof. exact (MK_COMB (@lem2744481 m h1) (@lem2744483 n h2)). Qed.
Lemma lem2744485 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2744486 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term52 m n) = term53.
Proof. exact (MK_COMB (@lem2744485) (@lem2744484 m n h1 h2)). Qed.
Lemma lem2744487 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2744488 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term43 m n) = term54.
Proof. exact (MK_COMB (@lem2744486 m n h1 h2) (@lem2744487)). Qed.
Lemma lem2744489 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744490 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term46 m n) = term55.
Proof. exact (MK_COMB (@lem2744489) (@lem2744488 m n h1 h2)). Qed.
Lemma lem2744491 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744492 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : ((term43 m n) = term20) = (term54 = term20).
Proof. exact (MK_COMB (@lem2744490 m n h1 h2) (@lem2744491)). Qed.
Lemma lem2744495 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2744496 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term47 m n) = term56.
Proof. exact (MK_COMB (@lem2744495) (@lem2744492 m n h1 h2)). Qed.
Lemma lem2744502 (m : int) (h1 : (term19 m) = term20) : (term19 m) = term20.
Proof. exact (h1). Qed.
Lemma lem2744503 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744504 (m : int) (h1 : (term19 m) = term20) : (term57 m) = term58.
Proof. exact (MK_COMB (@lem2744503) (@lem2744502 m h1)). Qed.
Lemma lem2744505 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744506 (m : int) (h1 : (term19 m) = term20) : ((term19 m) = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2744504 m h1) (@lem2744505)). Qed.
Lemma lem2744508 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2744509 (x : int) : (x = x) = True.
Proof. exact (@lem2744508 int x). Qed.
Lemma lem2744510 : (term20 = term20) = True.
Proof. exact (@lem2744509 term20). Qed.
Lemma lem2744511 (m : int) (h1 : (term19 m) = term20) : ((term19 m) = term20) = True.
Proof. exact (TRANS (@lem2744506 m h1) (@lem2744510)). Qed.
Lemma lem2744512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2744513 (m : int) (h1 : (term19 m) = term20) : (term42 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem2744512) (@lem2744511 m h1)). Qed.
Lemma lem2744517 (n : int) (h1 : (term19 n) = term20) : (term19 n) = term20.
Proof. exact (h1). Qed.
Lemma lem2744518 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744519 (n : int) (h1 : (term19 n) = term20) : (term57 n) = term58.
Proof. exact (MK_COMB (@lem2744518) (@lem2744517 n h1)). Qed.
Lemma lem2744520 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744521 (n : int) (h1 : (term19 n) = term20) : ((term19 n) = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2744519 n h1) (@lem2744520)). Qed.
Lemma lem2744523 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2744524 (x : int) : (x = x) = True.
Proof. exact (@lem2744523 int x). Qed.
Lemma lem2744525 : (term20 = term20) = True.
Proof. exact (@lem2744524 term20). Qed.
Lemma lem2744526 (n : int) (h1 : (term19 n) = term20) : ((term19 n) = term20) = True.
Proof. exact (TRANS (@lem2744521 n h1) (@lem2744525)). Qed.
Lemma lem2744527 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (((term19 m) = term20) = ((term19 n) = term20)) = (True = True).
Proof. exact (MK_COMB (@lem2744513 m h1) (@lem2744526 n h2)). Qed.
Lemma lem2744529 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem2744530 : (True = True) = True.
Proof. exact (@lem2744529 True). Qed.
Lemma lem2744531 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (((term19 m) = term20) = ((term19 n) = term20)) = True.
Proof. exact (TRANS (@lem2744527 m n h1 h2) (@lem2744530)). Qed.
Lemma lem2744532 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = ((term54 = term20) = True).
Proof. exact (MK_COMB (@lem2744496 m n h1 h2) (@lem2744531 m n h1 h2)). Qed.
Lemma lem2744534 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem2744535 : ((term54 = term20) = True) = (term54 = term20).
Proof. exact (@lem2744534 (term54 = term20)). Qed.
Lemma lem2744538 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = (term54 = term20).
Proof. exact (TRANS (@lem2744532 m n h1 h2) (@lem2744535)). Qed.
Lemma lem2744539 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term54 = term20) = (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))).
Proof. exact (SYM (@lem2744538 m n h1 h2)). Qed.
Lemma lem2744545 (m : int) (h1 : (term19 m) = term20) : (term19 m) = term20.
Proof. exact (h1). Qed.
Lemma lem2744546 : int_sub = int_sub.
Proof. exact (eq_refl int_sub). Qed.
Lemma lem2744547 (m : int) (h1 : (term19 m) = term20) : (term48 m) = term49.
Proof. exact (MK_COMB (@lem2744546) (@lem2744545 m h1)). Qed.
Lemma lem2744549 (n : int) (h1 : (term19 n) = term28) : (term19 n) = term28.
Proof. exact (h1). Qed.
Lemma lem2744550 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term50 m n) = term59.
Proof. exact (MK_COMB (@lem2744547 m h1) (@lem2744549 n h2)). Qed.
Lemma lem2744551 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2744552 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term52 m n) = term60.
Proof. exact (MK_COMB (@lem2744551) (@lem2744550 m n h1 h2)). Qed.
Lemma lem2744553 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2744554 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term43 m n) = term61.
Proof. exact (MK_COMB (@lem2744552 m n h1 h2) (@lem2744553)). Qed.
Lemma lem2744555 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744556 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term46 m n) = term62.
Proof. exact (MK_COMB (@lem2744555) (@lem2744554 m n h1 h2)). Qed.
Lemma lem2744557 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744558 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : ((term43 m n) = term20) = (term61 = term20).
Proof. exact (MK_COMB (@lem2744556 m n h1 h2) (@lem2744557)). Qed.
Lemma lem2744561 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2744562 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term47 m n) = term63.
Proof. exact (MK_COMB (@lem2744561) (@lem2744558 m n h1 h2)). Qed.
Lemma lem2744568 (m : int) (h1 : (term19 m) = term20) : (term19 m) = term20.
Proof. exact (h1). Qed.
Lemma lem2744569 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744570 (m : int) (h1 : (term19 m) = term20) : (term57 m) = term58.
Proof. exact (MK_COMB (@lem2744569) (@lem2744568 m h1)). Qed.
Lemma lem2744571 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744572 (m : int) (h1 : (term19 m) = term20) : ((term19 m) = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2744570 m h1) (@lem2744571)). Qed.
Lemma lem2744574 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2744575 (x : int) : (x = x) = True.
Proof. exact (@lem2744574 int x). Qed.
Lemma lem2744576 : (term20 = term20) = True.
Proof. exact (@lem2744575 term20). Qed.
Lemma lem2744577 (m : int) (h1 : (term19 m) = term20) : ((term19 m) = term20) = True.
Proof. exact (TRANS (@lem2744572 m h1) (@lem2744576)). Qed.
Lemma lem2744578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2744579 (m : int) (h1 : (term19 m) = term20) : (term42 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem2744578) (@lem2744577 m h1)). Qed.
Lemma lem2744583 (n : int) (h1 : (term19 n) = term28) : (term19 n) = term28.
Proof. exact (h1). Qed.
Lemma lem2744584 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744585 (n : int) (h1 : (term19 n) = term28) : (term57 n) = term64.
Proof. exact (MK_COMB (@lem2744584) (@lem2744583 n h1)). Qed.
Lemma lem2744586 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744587 (n : int) (h1 : (term19 n) = term28) : ((term19 n) = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2744585 n h1) (@lem2744586)). Qed.
Lemma lem2744590 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (((term19 m) = term20) = ((term19 n) = term20)) = (True = (term28 = term20)).
Proof. exact (MK_COMB (@lem2744579 m h1) (@lem2744587 n h2)). Qed.
Lemma lem2744592 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem2744593 : (True = (term28 = term20)) = (term28 = term20).
Proof. exact (@lem2744592 (term28 = term20)). Qed.
Lemma lem2744596 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (((term19 m) = term20) = ((term19 n) = term20)) = (term28 = term20).
Proof. exact (TRANS (@lem2744590 m n h1 h2) (@lem2744593)). Qed.
Lemma lem2744597 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = ((term61 = term20) = (term28 = term20)).
Proof. exact (MK_COMB (@lem2744562 m n h1 h2) (@lem2744596 m n h1 h2)). Qed.
Lemma lem2744600 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : ((term61 = term20) = (term28 = term20)) = (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))).
Proof. exact (SYM (@lem2744597 m n h1 h2)). Qed.
Lemma lem2744606 (m : int) (h1 : (term19 m) = term28) : (term19 m) = term28.
Proof. exact (h1). Qed.
Lemma lem2744607 : int_sub = int_sub.
Proof. exact (eq_refl int_sub). Qed.
Lemma lem2744608 (m : int) (h1 : (term19 m) = term28) : (term48 m) = term65.
Proof. exact (MK_COMB (@lem2744607) (@lem2744606 m h1)). Qed.
Lemma lem2744610 (n : int) (h1 : (term19 n) = term20) : (term19 n) = term20.
Proof. exact (h1). Qed.
Lemma lem2744611 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term50 m n) = term66.
Proof. exact (MK_COMB (@lem2744608 m h1) (@lem2744610 n h2)). Qed.
Lemma lem2744612 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2744613 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term52 m n) = term67.
Proof. exact (MK_COMB (@lem2744612) (@lem2744611 m n h1 h2)). Qed.
Lemma lem2744614 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2744615 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term43 m n) = term68.
Proof. exact (MK_COMB (@lem2744613 m n h1 h2) (@lem2744614)). Qed.
Lemma lem2744616 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744617 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term46 m n) = term69.
Proof. exact (MK_COMB (@lem2744616) (@lem2744615 m n h1 h2)). Qed.
Lemma lem2744618 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744619 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : ((term43 m n) = term20) = (term68 = term20).
Proof. exact (MK_COMB (@lem2744617 m n h1 h2) (@lem2744618)). Qed.
Lemma lem2744622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2744623 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term47 m n) = term70.
Proof. exact (MK_COMB (@lem2744622) (@lem2744619 m n h1 h2)). Qed.
Lemma lem2744629 (m : int) (h1 : (term19 m) = term28) : (term19 m) = term28.
Proof. exact (h1). Qed.
Lemma lem2744630 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744631 (m : int) (h1 : (term19 m) = term28) : (term57 m) = term64.
Proof. exact (MK_COMB (@lem2744630) (@lem2744629 m h1)). Qed.
Lemma lem2744632 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744633 (m : int) (h1 : (term19 m) = term28) : ((term19 m) = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2744631 m h1) (@lem2744632)). Qed.
Lemma lem2744636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2744637 (m : int) (h1 : (term19 m) = term28) : (term42 m) = term71.
Proof. exact (MK_COMB (@lem2744636) (@lem2744633 m h1)). Qed.
Lemma lem2744641 (n : int) (h1 : (term19 n) = term20) : (term19 n) = term20.
Proof. exact (h1). Qed.
Lemma lem2744642 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744643 (n : int) (h1 : (term19 n) = term20) : (term57 n) = term58.
Proof. exact (MK_COMB (@lem2744642) (@lem2744641 n h1)). Qed.
Lemma lem2744644 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744645 (n : int) (h1 : (term19 n) = term20) : ((term19 n) = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2744643 n h1) (@lem2744644)). Qed.
Lemma lem2744647 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2744648 (x : int) : (x = x) = True.
Proof. exact (@lem2744647 int x). Qed.
Lemma lem2744649 : (term20 = term20) = True.
Proof. exact (@lem2744648 term20). Qed.
Lemma lem2744650 (n : int) (h1 : (term19 n) = term20) : ((term19 n) = term20) = True.
Proof. exact (TRANS (@lem2744645 n h1) (@lem2744649)). Qed.
Lemma lem2744651 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (((term19 m) = term20) = ((term19 n) = term20)) = ((term28 = term20) = True).
Proof. exact (MK_COMB (@lem2744637 m h1) (@lem2744650 n h2)). Qed.
Lemma lem2744653 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem2744654 : ((term28 = term20) = True) = (term28 = term20).
Proof. exact (@lem2744653 (term28 = term20)). Qed.
Lemma lem2744657 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (((term19 m) = term20) = ((term19 n) = term20)) = (term28 = term20).
Proof. exact (TRANS (@lem2744651 m n h1 h2) (@lem2744654)). Qed.
Lemma lem2744658 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = ((term68 = term20) = (term28 = term20)).
Proof. exact (MK_COMB (@lem2744623 m n h1 h2) (@lem2744657 m n h1 h2)). Qed.
Lemma lem2744661 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : ((term68 = term20) = (term28 = term20)) = (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))).
Proof. exact (SYM (@lem2744658 m n h1 h2)). Qed.
Lemma lem2744667 (m : int) (h1 : (term19 m) = term28) : (term19 m) = term28.
Proof. exact (h1). Qed.
Lemma lem2744668 : int_sub = int_sub.
Proof. exact (eq_refl int_sub). Qed.
Lemma lem2744669 (m : int) (h1 : (term19 m) = term28) : (term48 m) = term65.
Proof. exact (MK_COMB (@lem2744668) (@lem2744667 m h1)). Qed.
Lemma lem2744671 (n : int) (h1 : (term19 n) = term28) : (term19 n) = term28.
Proof. exact (h1). Qed.
Lemma lem2744672 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term50 m n) = term72.
Proof. exact (MK_COMB (@lem2744669 m h1) (@lem2744671 n h2)). Qed.
Lemma lem2744673 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2744674 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term52 m n) = term73.
Proof. exact (MK_COMB (@lem2744673) (@lem2744672 m n h1 h2)). Qed.
Lemma lem2744675 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2744676 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term43 m n) = term74.
Proof. exact (MK_COMB (@lem2744674 m n h1 h2) (@lem2744675)). Qed.
Lemma lem2744677 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744678 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term46 m n) = term75.
Proof. exact (MK_COMB (@lem2744677) (@lem2744676 m n h1 h2)). Qed.
Lemma lem2744679 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744680 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : ((term43 m n) = term20) = (term74 = term20).
Proof. exact (MK_COMB (@lem2744678 m n h1 h2) (@lem2744679)). Qed.
Lemma lem2744683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2744684 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term47 m n) = term76.
Proof. exact (MK_COMB (@lem2744683) (@lem2744680 m n h1 h2)). Qed.
Lemma lem2744690 (m : int) (h1 : (term19 m) = term28) : (term19 m) = term28.
Proof. exact (h1). Qed.
Lemma lem2744691 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744692 (m : int) (h1 : (term19 m) = term28) : (term57 m) = term64.
Proof. exact (MK_COMB (@lem2744691) (@lem2744690 m h1)). Qed.
Lemma lem2744693 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744694 (m : int) (h1 : (term19 m) = term28) : ((term19 m) = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2744692 m h1) (@lem2744693)). Qed.
Lemma lem2744697 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2744698 (m : int) (h1 : (term19 m) = term28) : (term42 m) = term71.
Proof. exact (MK_COMB (@lem2744697) (@lem2744694 m h1)). Qed.
Lemma lem2744702 (n : int) (h1 : (term19 n) = term28) : (term19 n) = term28.
Proof. exact (h1). Qed.
Lemma lem2744703 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744704 (n : int) (h1 : (term19 n) = term28) : (term57 n) = term64.
Proof. exact (MK_COMB (@lem2744703) (@lem2744702 n h1)). Qed.
Lemma lem2744705 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744706 (n : int) (h1 : (term19 n) = term28) : ((term19 n) = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2744704 n h1) (@lem2744705)). Qed.
Lemma lem2744709 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (((term19 m) = term20) = ((term19 n) = term20)) = ((term28 = term20) = (term28 = term20)).
Proof. exact (MK_COMB (@lem2744698 m h1) (@lem2744706 n h2)). Qed.
Lemma lem2744711 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2744712 (x : Prop) : (x = x) = True.
Proof. exact (@lem2744711 Prop x). Qed.
Lemma lem2744713 : ((term28 = term20) = (term28 = term20)) = True.
Proof. exact (@lem2744712 (term28 = term20)). Qed.
Lemma lem2744714 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (((term19 m) = term20) = ((term19 n) = term20)) = True.
Proof. exact (TRANS (@lem2744709 m n h1 h2) (@lem2744713)). Qed.
Lemma lem2744715 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = ((term74 = term20) = True).
Proof. exact (MK_COMB (@lem2744684 m n h1 h2) (@lem2744714 m n h1 h2)). Qed.
Lemma lem2744717 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem2744718 : ((term74 = term20) = True) = (term74 = term20).
Proof. exact (@lem2744717 (term74 = term20)). Qed.
Lemma lem2744721 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = (term74 = term20).
Proof. exact (TRANS (@lem2744715 m n h1 h2) (@lem2744718)). Qed.
Lemma lem2744722 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term74 = term20) = (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))).
Proof. exact (SYM (@lem2744721 m n h1 h2)). Qed.
Lemma lem2744724 (x : int) (y : int) : (int_sub x y) = (term77 x y).
Proof. exact (EQ_MP (@lem2406288 x y) (@lem2406287 x y)). Qed.
Lemma lem2744725 : term51 = term78.
Proof. exact (@lem2744724 term20 term20). Qed.
Lemma lem2744727 : term79 = term20.
Proof. exact (proj1 (@lem2405528 (@el nat))). Qed.
Lemma lem2744728 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2744729 : term78 = term81.
Proof. exact (MK_COMB (@lem2744728) (@lem2744727)). Qed.
Lemma lem2744730 : term51 = term81.
Proof. exact (TRANS (@lem2744725) (@lem2744729)). Qed.
Lemma lem2744731 : term81 = term82.
Proof. exact (@lem2406280 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2744732 : (Nat.add 0 0) = 0.
Proof. exact (@lem706819). Qed.
Lemma lem2744733 : ((Nat.add 0 0) = 0) = (term83 = (NUMERAL 0)).
Proof. exact (@lem1006570 0 0 0). Qed.
Lemma lem2744734 : term83 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem2744733) (@lem2744732)). Qed.
Lemma lem2744735 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744736 : term82 = term20.
Proof. exact (MK_COMB (@lem2744735) (@lem2744734)). Qed.
Lemma lem2744737 : term81 = term20.
Proof. exact (TRANS (@lem2744731) (@lem2744736)). Qed.
Lemma lem2744738 : term51 = term20.
Proof. exact (TRANS (@lem2744730) (@lem2744737)). Qed.
Lemma lem2744739 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2744740 : term53 = term84.
Proof. exact (MK_COMB (@lem2744739) (@lem2744738)). Qed.
Lemma lem2744741 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2744742 : term54 = term85.
Proof. exact (MK_COMB (@lem2744740) (@lem2744741)). Qed.
Lemma lem2744743 : term86.
Proof. exact (@lem2743639 term20 term20 term44 term20). Qed.
Lemma lem2744745 (x : nat) : (term87 x) = term20.
Proof. exact (proj1 (@lem2405621 x)). Qed.
Lemma lem2744746 : term88 = term20.
Proof. exact (@lem2744745 term89). Qed.
Lemma lem2744747 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2744748 : term90 = term80.
Proof. exact (MK_COMB (@lem2744747) (@lem2744746)). Qed.
Lemma lem2744749 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744750 : term91 = term81.
Proof. exact (MK_COMB (@lem2744748) (@lem2744749)). Qed.
Lemma lem2744751 : term81 = term82.
Proof. exact (@lem2406280 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2744752 : (Nat.add 0 0) = 0.
Proof. exact (@lem706819). Qed.
Lemma lem2744753 : ((Nat.add 0 0) = 0) = (term83 = (NUMERAL 0)).
Proof. exact (@lem1006570 0 0 0). Qed.
Lemma lem2744754 : term83 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem2744753) (@lem2744752)). Qed.
Lemma lem2744755 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744756 : term82 = term20.
Proof. exact (MK_COMB (@lem2744755) (@lem2744754)). Qed.
Lemma lem2744757 : term81 = term20.
Proof. exact (TRANS (@lem2744751) (@lem2744756)). Qed.
Lemma lem2744758 : term91 = term20.
Proof. exact (TRANS (@lem2744750) (@lem2744757)). Qed.
Lemma lem2744759 : term92.
Proof. exact (@lem2744743 (@lem2744758)). Qed.
Lemma lem2744761 (m : nat) (n : nat) : (term93 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2744762 : term94 = term95.
Proof. exact (@lem2744761 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2744763 : term95 = True.
Proof. exact (@lem1011992 0). Qed.
Lemma lem2744764 : term94 = True.
Proof. exact (TRANS (@lem2744762) (@lem2744763)). Qed.
Lemma lem2744765 : True = term94.
Proof. exact (SYM (@lem2744764)). Qed.
Lemma lem2744766 : term94.
Proof. exact (EQ_MP (@lem2744765) (@lem0)). Qed.
Lemma lem2744767 : term96.
Proof. exact (@lem2744759 (@lem2744766)). Qed.
Lemma lem2744769 (x : nat) : (term97 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem2744770 : term98 = term44.
Proof. exact (@lem2744769 term89). Qed.
Lemma lem2744771 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem2744772 : term100 = term101.
Proof. exact (MK_COMB (@lem2744771) (@lem2744770)). Qed.
Lemma lem2744774 (m : nat) (n : nat) : (term102 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem2404231 m n)). Qed.
Lemma lem2744775 : term101 = term103.
Proof. exact (@lem2744774 (NUMERAL 0) term89). Qed.
Lemma lem2744776 : term104 = term105.
Proof. exact (@lem912803). Qed.
Lemma lem2744777 (h1 : term104 = term105) : term103 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term105 h1). Qed.
Lemma lem2744778 : (term104 = term105) = (term103 = True).
Proof. exact (prop_ext (fun h1 : term104 = term105 => @lem2744777 h1) (fun h1 : term103 = True => @lem2744776)). Qed.
Lemma lem2744779 : term103 = True.
Proof. exact (EQ_MP (@lem2744778) (@lem2744776)). Qed.
Lemma lem2744780 : term101 = True.
Proof. exact (TRANS (@lem2744775) (@lem2744779)). Qed.
Lemma lem2744781 : term100 = True.
Proof. exact (TRANS (@lem2744772) (@lem2744780)). Qed.
Lemma lem2744782 : True = term100.
Proof. exact (SYM (@lem2744781)). Qed.
Lemma lem2744783 : term100.
Proof. exact (EQ_MP (@lem2744782) (@lem0)). Qed.
Lemma lem2744784 : term106.
Proof. exact (@lem2744767 (@lem2744783)). Qed.
Lemma lem2744785 : term85 = term20.
Proof. exact (proj2 (@lem2744784)). Qed.
Lemma lem2744786 : term54 = term20.
Proof. exact (TRANS (@lem2744742) (@lem2744785)). Qed.
Lemma lem2744787 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744788 : term55 = term58.
Proof. exact (MK_COMB (@lem2744787) (@lem2744786)). Qed.
Lemma lem2744789 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744790 : (term54 = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2744788) (@lem2744789)). Qed.
Lemma lem2744792 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2744793 (x : int) : (x = x) = True.
Proof. exact (@lem2744792 int x). Qed.
Lemma lem2744794 : (term20 = term20) = True.
Proof. exact (@lem2744793 term20). Qed.
Lemma lem2744795 : (term54 = term20) = True.
Proof. exact (TRANS (@lem2744790) (@lem2744794)). Qed.
Lemma lem2744796 : True = (term54 = term20).
Proof. exact (SYM (@lem2744795)). Qed.
Lemma lem2744797 : term54 = term20.
Proof. exact (EQ_MP (@lem2744796) (@lem0)). Qed.
Lemma lem2744799 (x : int) (y : int) : (int_sub x y) = (term77 x y).
Proof. exact (EQ_MP (@lem2406288 x y) (@lem2406287 x y)). Qed.
Lemma lem2744802 : term59 = term107.
Proof. exact (@lem2744799 term20 term28). Qed.
Lemma lem2744805 : term108 = term109.
Proof. exact (@lem2406281 (NUMERAL 0) term110). Qed.
Lemma lem2744806 : term111 = (BIT1 0).
Proof. exact (@lem706821). Qed.
Lemma lem2744807 : (term111 = (BIT1 0)) = (term112 = term110).
Proof. exact (@lem1006570 0 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2744808 : term112 = term110.
Proof. exact (EQ_MP (@lem2744807) (@lem2744806)). Qed.
Lemma lem2744809 : term110 = term112.
Proof. exact (SYM (@lem2744808)). Qed.
Lemma lem2744810 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744811 : term28 = term113.
Proof. exact (MK_COMB (@lem2744810) (@lem2744809)). Qed.
Lemma lem2744812 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem2744813 : term109 = term114.
Proof. exact (MK_COMB (@lem2744812) (@lem2744811)). Qed.
Lemma lem2744814 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem2744815 : term107 = term108.
Proof. exact (MK_COMB (@lem2744814) (@lem2744813)). Qed.
Lemma lem2744816 : term107 = term109.
Proof. exact (TRANS (@lem2744815) (@lem2744805)). Qed.
Lemma lem2744817 : term59 = term109.
Proof. exact (TRANS (@lem2744802) (@lem2744816)). Qed.
Lemma lem2744818 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2744819 : term60 = term115.
Proof. exact (MK_COMB (@lem2744818) (@lem2744817)). Qed.
Lemma lem2744820 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2744821 : term61 = term116.
Proof. exact (MK_COMB (@lem2744819) (@lem2744820)). Qed.
Lemma lem2744822 : term117.
Proof. exact (@lem2743639 term109 term109 term44 term28). Qed.
Lemma lem2744824 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (proj1 (@lem2405757 m n)). Qed.
Lemma lem2744825 : term120 = term121.
Proof. exact (@lem2744824 term110 term89). Qed.
Lemma lem2744826 : term122 = term105.
Proof. exact (@lem996238 term105). Qed.
Lemma lem2744827 : (term122 = term105) = (term123 = term89).
Proof. exact (@lem1007663 (BIT1 0) term105 term105). Qed.
Lemma lem2744828 : term123 = term89.
Proof. exact (EQ_MP (@lem2744827) (@lem2744826)). Qed.
Lemma lem2744829 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744830 : term124 = term44.
Proof. exact (MK_COMB (@lem2744829) (@lem2744828)). Qed.
Lemma lem2744831 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem2744832 : term121 = term125.
Proof. exact (MK_COMB (@lem2744831) (@lem2744830)). Qed.
Lemma lem2744833 : term120 = term125.
Proof. exact (TRANS (@lem2744825) (@lem2744832)). Qed.
Lemma lem2744834 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2744835 : term126 = term127.
Proof. exact (MK_COMB (@lem2744834) (@lem2744833)). Qed.
Lemma lem2744836 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem2744837 : term128 = term129.
Proof. exact (MK_COMB (@lem2744835) (@lem2744836)). Qed.
Lemma lem2744840 : term130 = term109.
Proof. exact (@lem2406277 term110 term110). Qed.
Lemma lem2744841 : term131 = term105.
Proof. exact (@lem706885). Qed.
Lemma lem2744842 : (term131 = term105) = (term132 = term89).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term105). Qed.
Lemma lem2744843 : term132 = term89.
Proof. exact (EQ_MP (@lem2744842) (@lem2744841)). Qed.
Lemma lem2744844 : term89 = term132.
Proof. exact (SYM (@lem2744843)). Qed.
Lemma lem2744845 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744846 : term44 = term133.
Proof. exact (MK_COMB (@lem2744845) (@lem2744844)). Qed.
Lemma lem2744847 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem2744848 : term125 = term134.
Proof. exact (MK_COMB (@lem2744847) (@lem2744846)). Qed.
Lemma lem2744849 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2744850 : term127 = term135.
Proof. exact (MK_COMB (@lem2744849) (@lem2744848)). Qed.
Lemma lem2744851 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem2744852 : term129 = term130.
Proof. exact (MK_COMB (@lem2744850) (@lem2744851)). Qed.
Lemma lem2744853 : term129 = term109.
Proof. exact (TRANS (@lem2744852) (@lem2744840)). Qed.
Lemma lem2744854 : term128 = term109.
Proof. exact (TRANS (@lem2744837) (@lem2744853)). Qed.
Lemma lem2744855 : term136.
Proof. exact (@lem2744822 (@lem2744854)). Qed.
Lemma lem2744857 (m : nat) (n : nat) : (term93 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2744858 : term137 = term138.
Proof. exact (@lem2744857 (NUMERAL 0) term110). Qed.
Lemma lem2744859 : term139 = (BIT1 0).
Proof. exact (@lem706883). Qed.
Lemma lem2744860 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1011471 (BIT1 0) 0 (BIT1 0) h1). Qed.
Lemma lem2744861 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem2744860 h1) (fun h1 : term138 = True => @lem2744859)). Qed.
Lemma lem2744862 : term138 = True.
Proof. exact (EQ_MP (@lem2744861) (@lem2744859)). Qed.
Lemma lem2744863 : term137 = True.
Proof. exact (TRANS (@lem2744858) (@lem2744862)). Qed.
Lemma lem2744864 : True = term137.
Proof. exact (SYM (@lem2744863)). Qed.
Lemma lem2744865 : term137.
Proof. exact (EQ_MP (@lem2744864) (@lem0)). Qed.
Lemma lem2744866 : term140.
Proof. exact (@lem2744855 (@lem2744865)). Qed.
Lemma lem2744868 (x : nat) : (term97 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem2744869 : term98 = term44.
Proof. exact (@lem2744868 term89). Qed.
Lemma lem2744870 : term141 = term141.
Proof. exact (eq_refl term141). Qed.
Lemma lem2744871 : term142 = term143.
Proof. exact (MK_COMB (@lem2744870) (@lem2744869)). Qed.
Lemma lem2744873 (m : nat) (n : nat) : (term102 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem2404231 m n)). Qed.
Lemma lem2744874 : term143 = term144.
Proof. exact (@lem2744873 term110 term89). Qed.
Lemma lem2744875 : term145 = term105.
Proof. exact (@lem912741). Qed.
Lemma lem2744876 (h1 : term145 = term105) : term144 = True.
Proof. exact (@lem1009824 0 (BIT1 0) term105 h1). Qed.
Lemma lem2744877 : (term145 = term105) = (term144 = True).
Proof. exact (prop_ext (fun h1 : term145 = term105 => @lem2744876 h1) (fun h1 : term144 = True => @lem2744875)). Qed.
Lemma lem2744878 : term144 = True.
Proof. exact (EQ_MP (@lem2744877) (@lem2744875)). Qed.
Lemma lem2744879 : term143 = True.
Proof. exact (TRANS (@lem2744874) (@lem2744878)). Qed.
Lemma lem2744880 : term142 = True.
Proof. exact (TRANS (@lem2744871) (@lem2744879)). Qed.
Lemma lem2744881 : True = term142.
Proof. exact (SYM (@lem2744880)). Qed.
Lemma lem2744882 : term142.
Proof. exact (EQ_MP (@lem2744881) (@lem0)). Qed.
Lemma lem2744883 : term146.
Proof. exact (@lem2744866 (@lem2744882)). Qed.
Lemma lem2744884 : term116 = term28.
Proof. exact (proj2 (@lem2744883)). Qed.
Lemma lem2744885 : term61 = term28.
Proof. exact (TRANS (@lem2744821) (@lem2744884)). Qed.
Lemma lem2744886 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744887 : term62 = term64.
Proof. exact (MK_COMB (@lem2744886) (@lem2744885)). Qed.
Lemma lem2744888 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744889 : (term61 = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2744887) (@lem2744888)). Qed.
Lemma lem2744893 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (proj1 (@lem2405481 m n)). Qed.
Lemma lem2744894 : (term28 = term20) = (term110 = (NUMERAL 0)).
Proof. exact (@lem2744893 term110 (NUMERAL 0)). Qed.
Lemma lem2744895 : term147 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2744896 (h1 : term147 = (BIT1 0)) : (term110 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2744897 : (term147 = (BIT1 0)) = ((term110 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term147 = (BIT1 0) => @lem2744896 h1) (fun h1 : (term110 = (NUMERAL 0)) = False => @lem2744895)). Qed.
Lemma lem2744898 : (term110 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2744897) (@lem2744895)). Qed.
Lemma lem2744899 : (term28 = term20) = False.
Proof. exact (TRANS (@lem2744894) (@lem2744898)). Qed.
Lemma lem2744900 : (term61 = term20) = False.
Proof. exact (TRANS (@lem2744889) (@lem2744899)). Qed.
Lemma lem2744901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2744902 : term63 = (@eq Prop False).
Proof. exact (MK_COMB (@lem2744901) (@lem2744900)). Qed.
Lemma lem2744906 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (proj1 (@lem2405481 m n)). Qed.
Lemma lem2744907 : (term28 = term20) = (term110 = (NUMERAL 0)).
Proof. exact (@lem2744906 term110 (NUMERAL 0)). Qed.
Lemma lem2744908 : term147 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2744909 (h1 : term147 = (BIT1 0)) : (term110 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2744910 : (term147 = (BIT1 0)) = ((term110 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term147 = (BIT1 0) => @lem2744909 h1) (fun h1 : (term110 = (NUMERAL 0)) = False => @lem2744908)). Qed.
Lemma lem2744911 : (term110 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2744910) (@lem2744908)). Qed.
Lemma lem2744912 : (term28 = term20) = False.
Proof. exact (TRANS (@lem2744907) (@lem2744911)). Qed.
Lemma lem2744913 : ((term61 = term20) = (term28 = term20)) = (False = False).
Proof. exact (MK_COMB (@lem2744902) (@lem2744912)). Qed.
Lemma lem2744915 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem2744916 : (False = False) = (~ False).
Proof. exact (@lem2744915 False). Qed.
Lemma lem2744918 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2744919 : (False = False) = True.
Proof. exact (TRANS (@lem2744916) (@lem2744918)). Qed.
Lemma lem2744920 : ((term61 = term20) = (term28 = term20)) = True.
Proof. exact (TRANS (@lem2744913) (@lem2744919)). Qed.
Lemma lem2744921 : True = ((term61 = term20) = (term28 = term20)).
Proof. exact (SYM (@lem2744920)). Qed.
Lemma lem2744922 : (term61 = term20) = (term28 = term20).
Proof. exact (EQ_MP (@lem2744921) (@lem0)). Qed.
Lemma lem2744924 (x : int) (y : int) : (int_sub x y) = (term77 x y).
Proof. exact (EQ_MP (@lem2406288 x y) (@lem2406287 x y)). Qed.
Lemma lem2744925 : term66 = term148.
Proof. exact (@lem2744924 term28 term20). Qed.
Lemma lem2744927 : term79 = term20.
Proof. exact (proj1 (@lem2405528 (@el nat))). Qed.
Lemma lem2744928 : term149 = term149.
Proof. exact (eq_refl term149). Qed.
Lemma lem2744929 : term148 = term150.
Proof. exact (MK_COMB (@lem2744928) (@lem2744927)). Qed.
Lemma lem2744930 : term66 = term150.
Proof. exact (TRANS (@lem2744925) (@lem2744929)). Qed.
Lemma lem2744931 : term150 = term151.
Proof. exact (@lem2406280 term110 (NUMERAL 0)). Qed.
Lemma lem2744932 : term139 = (BIT1 0).
Proof. exact (@lem706883). Qed.
Lemma lem2744933 : (term139 = (BIT1 0)) = (term152 = term110).
Proof. exact (@lem1006570 (BIT1 0) 0 (BIT1 0)). Qed.
Lemma lem2744934 : term152 = term110.
Proof. exact (EQ_MP (@lem2744933) (@lem2744932)). Qed.
Lemma lem2744935 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744936 : term151 = term28.
Proof. exact (MK_COMB (@lem2744935) (@lem2744934)). Qed.
Lemma lem2744937 : term150 = term28.
Proof. exact (TRANS (@lem2744931) (@lem2744936)). Qed.
Lemma lem2744938 : term66 = term28.
Proof. exact (TRANS (@lem2744930) (@lem2744937)). Qed.
Lemma lem2744939 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2744940 : term67 = term153.
Proof. exact (MK_COMB (@lem2744939) (@lem2744938)). Qed.
Lemma lem2744941 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2744942 : term68 = term154.
Proof. exact (MK_COMB (@lem2744940) (@lem2744941)). Qed.
Lemma lem2744943 : term155.
Proof. exact (@lem2743639 term20 term28 term44 term28). Qed.
Lemma lem2744945 (x : nat) : (term87 x) = term20.
Proof. exact (proj1 (@lem2405621 x)). Qed.
Lemma lem2744946 : term88 = term20.
Proof. exact (@lem2744945 term89). Qed.
Lemma lem2744947 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2744948 : term90 = term80.
Proof. exact (MK_COMB (@lem2744947) (@lem2744946)). Qed.
Lemma lem2744949 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem2744950 : term156 = term157.
Proof. exact (MK_COMB (@lem2744948) (@lem2744949)). Qed.
Lemma lem2744951 : term157 = term113.
Proof. exact (@lem2406280 (NUMERAL 0) term110). Qed.
Lemma lem2744952 : term111 = (BIT1 0).
Proof. exact (@lem706821). Qed.
Lemma lem2744953 : (term111 = (BIT1 0)) = (term112 = term110).
Proof. exact (@lem1006570 0 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2744954 : term112 = term110.
Proof. exact (EQ_MP (@lem2744953) (@lem2744952)). Qed.
Lemma lem2744955 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744956 : term113 = term28.
Proof. exact (MK_COMB (@lem2744955) (@lem2744954)). Qed.
Lemma lem2744957 : term157 = term28.
Proof. exact (TRANS (@lem2744951) (@lem2744956)). Qed.
Lemma lem2744958 : term156 = term28.
Proof. exact (TRANS (@lem2744950) (@lem2744957)). Qed.
Lemma lem2744959 : term158.
Proof. exact (@lem2744943 (@lem2744958)). Qed.
Lemma lem2744961 (m : nat) (n : nat) : (term93 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2744962 : term137 = term138.
Proof. exact (@lem2744961 (NUMERAL 0) term110). Qed.
Lemma lem2744963 : term139 = (BIT1 0).
Proof. exact (@lem706883). Qed.
Lemma lem2744964 (h1 : term139 = (BIT1 0)) : term138 = True.
Proof. exact (@lem1011471 (BIT1 0) 0 (BIT1 0) h1). Qed.
Lemma lem2744965 : (term139 = (BIT1 0)) = (term138 = True).
Proof. exact (prop_ext (fun h1 : term139 = (BIT1 0) => @lem2744964 h1) (fun h1 : term138 = True => @lem2744963)). Qed.
Lemma lem2744966 : term138 = True.
Proof. exact (EQ_MP (@lem2744965) (@lem2744963)). Qed.
Lemma lem2744967 : term137 = True.
Proof. exact (TRANS (@lem2744962) (@lem2744966)). Qed.
Lemma lem2744968 : True = term137.
Proof. exact (SYM (@lem2744967)). Qed.
Lemma lem2744969 : term137.
Proof. exact (EQ_MP (@lem2744968) (@lem0)). Qed.
Lemma lem2744970 : term159.
Proof. exact (@lem2744959 (@lem2744969)). Qed.
Lemma lem2744972 (x : nat) : (term97 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem2744973 : term98 = term44.
Proof. exact (@lem2744972 term89). Qed.
Lemma lem2744974 : term141 = term141.
Proof. exact (eq_refl term141). Qed.
Lemma lem2744975 : term142 = term143.
Proof. exact (MK_COMB (@lem2744974) (@lem2744973)). Qed.
Lemma lem2744977 (m : nat) (n : nat) : (term102 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem2404231 m n)). Qed.
Lemma lem2744978 : term143 = term144.
Proof. exact (@lem2744977 term110 term89). Qed.
Lemma lem2744979 : term145 = term105.
Proof. exact (@lem912741). Qed.
Lemma lem2744980 (h1 : term145 = term105) : term144 = True.
Proof. exact (@lem1009824 0 (BIT1 0) term105 h1). Qed.
Lemma lem2744981 : (term145 = term105) = (term144 = True).
Proof. exact (prop_ext (fun h1 : term145 = term105 => @lem2744980 h1) (fun h1 : term144 = True => @lem2744979)). Qed.
Lemma lem2744982 : term144 = True.
Proof. exact (EQ_MP (@lem2744981) (@lem2744979)). Qed.
Lemma lem2744983 : term143 = True.
Proof. exact (TRANS (@lem2744978) (@lem2744982)). Qed.
Lemma lem2744984 : term142 = True.
Proof. exact (TRANS (@lem2744975) (@lem2744983)). Qed.
Lemma lem2744985 : True = term142.
Proof. exact (SYM (@lem2744984)). Qed.
Lemma lem2744986 : term142.
Proof. exact (EQ_MP (@lem2744985) (@lem0)). Qed.
Lemma lem2744987 : term160.
Proof. exact (@lem2744970 (@lem2744986)). Qed.
Lemma lem2744988 : term154 = term28.
Proof. exact (proj2 (@lem2744987)). Qed.
Lemma lem2744989 : term68 = term28.
Proof. exact (TRANS (@lem2744942) (@lem2744988)). Qed.
Lemma lem2744990 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744991 : term69 = term64.
Proof. exact (MK_COMB (@lem2744990) (@lem2744989)). Qed.
Lemma lem2744992 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744993 : (term68 = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2744991) (@lem2744992)). Qed.
Lemma lem2744997 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (proj1 (@lem2405481 m n)). Qed.
Lemma lem2744998 : (term28 = term20) = (term110 = (NUMERAL 0)).
Proof. exact (@lem2744997 term110 (NUMERAL 0)). Qed.
Lemma lem2744999 : term147 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2745000 (h1 : term147 = (BIT1 0)) : (term110 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2745001 : (term147 = (BIT1 0)) = ((term110 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term147 = (BIT1 0) => @lem2745000 h1) (fun h1 : (term110 = (NUMERAL 0)) = False => @lem2744999)). Qed.
Lemma lem2745002 : (term110 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2745001) (@lem2744999)). Qed.
Lemma lem2745003 : (term28 = term20) = False.
Proof. exact (TRANS (@lem2744998) (@lem2745002)). Qed.
Lemma lem2745004 : (term68 = term20) = False.
Proof. exact (TRANS (@lem2744993) (@lem2745003)). Qed.
Lemma lem2745005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2745006 : term70 = (@eq Prop False).
Proof. exact (MK_COMB (@lem2745005) (@lem2745004)). Qed.
Lemma lem2745010 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (proj1 (@lem2405481 m n)). Qed.
Lemma lem2745011 : (term28 = term20) = (term110 = (NUMERAL 0)).
Proof. exact (@lem2745010 term110 (NUMERAL 0)). Qed.
Lemma lem2745012 : term147 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2745013 (h1 : term147 = (BIT1 0)) : (term110 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2745014 : (term147 = (BIT1 0)) = ((term110 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term147 = (BIT1 0) => @lem2745013 h1) (fun h1 : (term110 = (NUMERAL 0)) = False => @lem2745012)). Qed.
Lemma lem2745015 : (term110 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2745014) (@lem2745012)). Qed.
Lemma lem2745016 : (term28 = term20) = False.
Proof. exact (TRANS (@lem2745011) (@lem2745015)). Qed.
Lemma lem2745017 : ((term68 = term20) = (term28 = term20)) = (False = False).
Proof. exact (MK_COMB (@lem2745006) (@lem2745016)). Qed.
Lemma lem2745019 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem2745020 : (False = False) = (~ False).
Proof. exact (@lem2745019 False). Qed.
Lemma lem2745022 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2745023 : (False = False) = True.
Proof. exact (TRANS (@lem2745020) (@lem2745022)). Qed.
Lemma lem2745024 : ((term68 = term20) = (term28 = term20)) = True.
Proof. exact (TRANS (@lem2745017) (@lem2745023)). Qed.
Lemma lem2745025 : True = ((term68 = term20) = (term28 = term20)).
Proof. exact (SYM (@lem2745024)). Qed.
Lemma lem2745026 : (term68 = term20) = (term28 = term20).
Proof. exact (EQ_MP (@lem2745025) (@lem0)). Qed.
Lemma lem2745028 (x : int) (y : int) : (int_sub x y) = (term77 x y).
Proof. exact (EQ_MP (@lem2406288 x y) (@lem2406287 x y)). Qed.
Lemma lem2745031 : term72 = term161.
Proof. exact (@lem2745028 term28 term28). Qed.
Lemma lem2745033 (m : nat) : (term162 m) = term20.
Proof. exact (proj2 (@lem2405813 m)). Qed.
Lemma lem2745034 : term161 = term20.
Proof. exact (@lem2745033 term110). Qed.
Lemma lem2745035 : term72 = term20.
Proof. exact (TRANS (@lem2745031) (@lem2745034)). Qed.
Lemma lem2745036 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2745037 : term73 = term84.
Proof. exact (MK_COMB (@lem2745036) (@lem2745035)). Qed.
Lemma lem2745038 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2745039 : term74 = term85.
Proof. exact (MK_COMB (@lem2745037) (@lem2745038)). Qed.
Lemma lem2745040 : term86.
Proof. exact (@lem2743639 term20 term20 term44 term20). Qed.
Lemma lem2745042 (x : nat) : (term87 x) = term20.
Proof. exact (proj1 (@lem2405621 x)). Qed.
Lemma lem2745043 : term88 = term20.
Proof. exact (@lem2745042 term89). Qed.
Lemma lem2745044 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2745045 : term90 = term80.
Proof. exact (MK_COMB (@lem2745044) (@lem2745043)). Qed.
Lemma lem2745046 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745047 : term91 = term81.
Proof. exact (MK_COMB (@lem2745045) (@lem2745046)). Qed.
Lemma lem2745048 : term81 = term82.
Proof. exact (@lem2406280 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2745049 : (Nat.add 0 0) = 0.
Proof. exact (@lem706819). Qed.
Lemma lem2745050 : ((Nat.add 0 0) = 0) = (term83 = (NUMERAL 0)).
Proof. exact (@lem1006570 0 0 0). Qed.
Lemma lem2745051 : term83 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem2745050) (@lem2745049)). Qed.
Lemma lem2745052 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2745053 : term82 = term20.
Proof. exact (MK_COMB (@lem2745052) (@lem2745051)). Qed.
Lemma lem2745054 : term81 = term20.
Proof. exact (TRANS (@lem2745048) (@lem2745053)). Qed.
Lemma lem2745055 : term91 = term20.
Proof. exact (TRANS (@lem2745047) (@lem2745054)). Qed.
Lemma lem2745056 : term92.
Proof. exact (@lem2745040 (@lem2745055)). Qed.
Lemma lem2745058 (m : nat) (n : nat) : (term93 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2745059 : term94 = term95.
Proof. exact (@lem2745058 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2745060 : term95 = True.
Proof. exact (@lem1011992 0). Qed.
Lemma lem2745061 : term94 = True.
Proof. exact (TRANS (@lem2745059) (@lem2745060)). Qed.
Lemma lem2745062 : True = term94.
Proof. exact (SYM (@lem2745061)). Qed.
Lemma lem2745063 : term94.
Proof. exact (EQ_MP (@lem2745062) (@lem0)). Qed.
Lemma lem2745064 : term96.
Proof. exact (@lem2745056 (@lem2745063)). Qed.
Lemma lem2745066 (x : nat) : (term97 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem2745067 : term98 = term44.
Proof. exact (@lem2745066 term89). Qed.
Lemma lem2745068 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem2745069 : term100 = term101.
Proof. exact (MK_COMB (@lem2745068) (@lem2745067)). Qed.
Lemma lem2745071 (m : nat) (n : nat) : (term102 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem2404231 m n)). Qed.
Lemma lem2745072 : term101 = term103.
Proof. exact (@lem2745071 (NUMERAL 0) term89). Qed.
Lemma lem2745073 : term104 = term105.
Proof. exact (@lem912803). Qed.
Lemma lem2745074 (h1 : term104 = term105) : term103 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term105 h1). Qed.
Lemma lem2745075 : (term104 = term105) = (term103 = True).
Proof. exact (prop_ext (fun h1 : term104 = term105 => @lem2745074 h1) (fun h1 : term103 = True => @lem2745073)). Qed.
Lemma lem2745076 : term103 = True.
Proof. exact (EQ_MP (@lem2745075) (@lem2745073)). Qed.
Lemma lem2745077 : term101 = True.
Proof. exact (TRANS (@lem2745072) (@lem2745076)). Qed.
Lemma lem2745078 : term100 = True.
Proof. exact (TRANS (@lem2745069) (@lem2745077)). Qed.
Lemma lem2745079 : True = term100.
Proof. exact (SYM (@lem2745078)). Qed.
Lemma lem2745080 : term100.
Proof. exact (EQ_MP (@lem2745079) (@lem0)). Qed.
Lemma lem2745081 : term106.
Proof. exact (@lem2745064 (@lem2745080)). Qed.
Lemma lem2745082 : term85 = term20.
Proof. exact (proj2 (@lem2745081)). Qed.
Lemma lem2745083 : term74 = term20.
Proof. exact (TRANS (@lem2745039) (@lem2745082)). Qed.
Lemma lem2745084 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2745085 : term75 = term58.
Proof. exact (MK_COMB (@lem2745084) (@lem2745083)). Qed.
Lemma lem2745086 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2745087 : (term74 = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2745085) (@lem2745086)). Qed.
Lemma lem2745089 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2745090 (x : int) : (x = x) = True.
Proof. exact (@lem2745089 int x). Qed.
Lemma lem2745091 : (term20 = term20) = True.
Proof. exact (@lem2745090 term20). Qed.
Lemma lem2745092 : (term74 = term20) = True.
Proof. exact (TRANS (@lem2745087) (@lem2745091)). Qed.
Lemma lem2745093 : True = (term74 = term20).
Proof. exact (SYM (@lem2745092)). Qed.
Lemma lem2745094 : term74 = term20.
Proof. exact (EQ_MP (@lem2745093) (@lem0)). Qed.
Lemma lem2745095 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : ((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (EQ_MP (@lem2744722 m n h1 h2) (@lem2745094)). Qed.
Lemma lem2745096 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : ((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (EQ_MP (@lem2744661 m n h1 h2) (@lem2745026)). Qed.
Lemma lem2745097 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : ((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (EQ_MP (@lem2744600 m n h1 h2) (@lem2744922)). Qed.
Lemma lem2745098 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : ((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (EQ_MP (@lem2744539 m n h1 h2) (@lem2744797)). Qed.
Lemma lem2745099 (n : int) (m : int) (h1 : (term19 m) = term28) : ((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (or_elim (@lem2744357 n) (fun h0 : (term19 n) = term20 => @lem2745096 m n h1 h0) (fun h0 : (term19 n) = term28 => @lem2745095 m n h1 h0)). Qed.
Lemma lem2745100 (n : int) (m : int) (h1 : (term19 m) = term20) : ((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (or_elim (@lem2744357 n) (fun h0 : (term19 n) = term20 => @lem2745098 m n h1 h0) (fun h0 : (term19 n) = term28 => @lem2745097 m n h1 h0)). Qed.
Lemma lem2745101 (m : int) (n : int) : ((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (or_elim (@lem2744362 m) (fun h0 : (term19 m) = term20 => @lem2745100 n m h0) (fun h0 : (term19 m) = term28 => @lem2745099 n m h0)). Qed.
Lemma lem2745102 (m : int) (n : int) : ((term38 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (EQ_MP (@lem2744473 m n) (@lem2745101 m n)). Qed.
Lemma lem2745103 (m : int) (n : int) : (term37 m n) = ((term21 m) = (term21 n)).
Proof. exact (EQ_MP (@lem2744451 m n) (@lem2745102 m n)). Qed.
Lemma lem2745108 (m : int) : term163 m.
Proof. exact (fun n : int => @lem2745103 m n). Qed.
Lemma lem2745113 : term164.
Proof. exact (fun m : int => @lem2745108 m). Qed.
