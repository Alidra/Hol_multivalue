Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_NEG_term_abbrevs.
Require Import SUM_LMUL_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982719_spec.
Require Import thm1982749_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988318_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7070369 {A : Type'} (f : A -> real) : term0 A f.
Proof. exact (@lem7070264 A f). Qed.
Lemma lem7070370 {A : Type'} (f : A -> real) : (term0 A f) = (term1 A f).
Proof. exact (eq_refl (term0 A f)). Qed.
Lemma lem7070371 {A : Type'} (f : A -> real) : term1 A f.
Proof. exact (EQ_MP (@lem7070370 A f) (@lem7070369 A f)). Qed.
Lemma lem7070372 {A : Type'} (f : A -> real) (c : real) : term2 A f c.
Proof. exact (@lem7070371 A f c). Qed.
Lemma lem7070373 {A : Type'} (c : real) (f : A -> real) : (term2 A f c) = (term3 A c f).
Proof. exact (eq_refl (term2 A f c)). Qed.
Lemma lem7070374 {A : Type'} (c : real) (f : A -> real) : term3 A c f.
Proof. exact (EQ_MP (@lem7070373 A c f) (@lem7070372 A f c)). Qed.
Lemma lem7070375 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) : term4 A c f s.
Proof. exact (@lem7070374 A c f s). Qed.
Lemma lem7070376 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term4 A c f s) = ((term5 A s c f) = (term6 A c s f)).
Proof. exact (eq_refl (term4 A c f s)). Qed.
Lemma lem7070388 (x : real) : (term7 x) = (term8 x).
Proof. exact (@lem1988318 (real_neg x) (term9 x)). Qed.
Lemma lem7070395 (x : real) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem7070402 (x : real) : (real_neg x) = (term9 x).
Proof. exact (@lem1982785 x). Qed.
Lemma lem7070403 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7070404 (x : real) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem7070403) (@lem7070402 x)). Qed.
Lemma lem7070405 (x : real) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem7070404 x) (@lem7070395 x)). Qed.
Lemma lem7070406 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1982792 (term9 x) (term9 x)). Qed.
Lemma lem7070407 (x : real) : (term15 x) = (term16 x).
Proof. exact (@lem1982749 term17 term17 x). Qed.
Lemma lem7070409 (x : nat) : (term18 x) = (term19 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7070410 : term17 = term20.
Proof. exact (@lem7070409 term21). Qed.
Lemma lem7070412 (x : nat) : (term18 x) = (term19 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7070413 : term17 = term20.
Proof. exact (@lem7070412 term21). Qed.
Lemma lem7070414 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7070415 : term22 = term23.
Proof. exact (MK_COMB (@lem7070414) (@lem7070413)). Qed.
Lemma lem7070416 : term24 = term25.
Proof. exact (MK_COMB (@lem7070415) (@lem7070410)). Qed.
Lemma lem7070417 : term25 = term26.
Proof. exact (@lem1981613 term17 term17 term27 term27). Qed.
Lemma lem7070419 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7070420 : term30 = term31.
Proof. exact (@lem7070419 term21 term21). Qed.
Lemma lem7070421 : (term32 = (BIT1 0)) = (term33 = term21).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7070422 : term33 = term21.
Proof. exact (EQ_MP (@lem7070421) (@lem940073)). Qed.
Lemma lem7070423 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7070424 : term31 = term27.
Proof. exact (MK_COMB (@lem7070423) (@lem7070422)). Qed.
Lemma lem7070425 : term30 = term27.
Proof. exact (TRANS (@lem7070420) (@lem7070424)). Qed.
Lemma lem7070427 (m : nat) (n : nat) : (term34 m n) = (term29 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7070428 : term24 = term31.
Proof. exact (@lem7070427 term21 term21). Qed.
Lemma lem7070429 : (term32 = (BIT1 0)) = (term33 = term21).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7070430 : term33 = term21.
Proof. exact (EQ_MP (@lem7070429) (@lem940073)). Qed.
Lemma lem7070431 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7070432 : term31 = term27.
Proof. exact (MK_COMB (@lem7070431) (@lem7070430)). Qed.
Lemma lem7070433 : term24 = term27.
Proof. exact (TRANS (@lem7070428) (@lem7070432)). Qed.
Lemma lem7070434 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7070435 : term35 = term36.
Proof. exact (MK_COMB (@lem7070434) (@lem7070433)). Qed.
Lemma lem7070436 : term26 = term37.
Proof. exact (MK_COMB (@lem7070435) (@lem7070425)). Qed.
Lemma lem7070437 : term25 = term37.
Proof. exact (TRANS (@lem7070417) (@lem7070436)). Qed.
Lemma lem7070438 : term24 = term37.
Proof. exact (TRANS (@lem7070416) (@lem7070437)). Qed.
Lemma lem7070440 (x : real) : (term38 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7070441 : term37 = term27.
Proof. exact (@lem7070440 term27). Qed.
Lemma lem7070442 : term24 = term27.
Proof. exact (TRANS (@lem7070438) (@lem7070441)). Qed.
Lemma lem7070443 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7070444 : term39 = term40.
Proof. exact (MK_COMB (@lem7070443) (@lem7070442)). Qed.
Lemma lem7070445 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7070446 (x : real) : (term16 x) = (term41 x).
Proof. exact (MK_COMB (@lem7070444) (@lem7070445 x)). Qed.
Lemma lem7070447 (x : real) : (term15 x) = (term41 x).
Proof. exact (TRANS (@lem7070407 x) (@lem7070446 x)). Qed.
Lemma lem7070448 (x : real) : (term41 x) = x.
Proof. exact (@lem1982709 x). Qed.
Lemma lem7070449 (x : real) : (term15 x) = x.
Proof. exact (TRANS (@lem7070447 x) (@lem7070448 x)). Qed.
Lemma lem7070450 (x : real) : (term42 x) = (term42 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem7070451 (x : real) : (term14 x) = (term43 x).
Proof. exact (MK_COMB (@lem7070450 x) (@lem7070449 x)). Qed.
Lemma lem7070452 (x : real) : (term43 x) = (term44 x).
Proof. exact (@lem1982713 term17 x). Qed.
Lemma lem7070454 (x : nat) : (real_of_num x) = (term45 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7070455 : term27 = term37.
Proof. exact (@lem7070454 term21). Qed.
Lemma lem7070457 (x : nat) : (term18 x) = (term19 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7070458 : term17 = term20.
Proof. exact (@lem7070457 term21). Qed.
Lemma lem7070459 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7070460 : term46 = term47.
Proof. exact (MK_COMB (@lem7070459) (@lem7070458)). Qed.
Lemma lem7070461 : term48 = term49.
Proof. exact (MK_COMB (@lem7070460) (@lem7070455)). Qed.
Lemma lem7070462 : term50.
Proof. exact (@lem1981473 term17 term27 term27 term27 term51 term27). Qed.
Lemma lem7070464 (m : nat) (n : nat) : (term52 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7070465 : term53 = term54.
Proof. exact (@lem7070464 (NUMERAL 0) term21). Qed.
Lemma lem7070466 : term55 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7070467 (h1 : term55 = (BIT1 0)) : term54 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7070468 : (term55 = (BIT1 0)) = (term54 = True).
Proof. exact (prop_ext (fun h1 : term55 = (BIT1 0) => @lem7070467 h1) (fun h1 : term54 = True => @lem7070466)). Qed.
Lemma lem7070469 : term54 = True.
Proof. exact (EQ_MP (@lem7070468) (@lem7070466)). Qed.
Lemma lem7070470 : term53 = True.
Proof. exact (TRANS (@lem7070465) (@lem7070469)). Qed.
Lemma lem7070471 : True = term53.
Proof. exact (SYM (@lem7070470)). Qed.
Lemma lem7070472 : term53.
Proof. exact (EQ_MP (@lem7070471) (@lem0)). Qed.
Lemma lem7070473 : term56.
Proof. exact (@lem7070462 (@lem7070472)). Qed.
Lemma lem7070475 (m : nat) (n : nat) : (term52 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7070476 : term53 = term54.
Proof. exact (@lem7070475 (NUMERAL 0) term21). Qed.
Lemma lem7070477 : term55 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7070478 (h1 : term55 = (BIT1 0)) : term54 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7070479 : (term55 = (BIT1 0)) = (term54 = True).
Proof. exact (prop_ext (fun h1 : term55 = (BIT1 0) => @lem7070478 h1) (fun h1 : term54 = True => @lem7070477)). Qed.
Lemma lem7070480 : term54 = True.
Proof. exact (EQ_MP (@lem7070479) (@lem7070477)). Qed.
Lemma lem7070481 : term53 = True.
Proof. exact (TRANS (@lem7070476) (@lem7070480)). Qed.
Lemma lem7070482 : True = term53.
Proof. exact (SYM (@lem7070481)). Qed.
Lemma lem7070483 : term53.
Proof. exact (EQ_MP (@lem7070482) (@lem0)). Qed.
Lemma lem7070484 : term57.
Proof. exact (@lem7070473 (@lem7070483)). Qed.
Lemma lem7070486 (m : nat) (n : nat) : (term52 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7070487 : term53 = term54.
Proof. exact (@lem7070486 (NUMERAL 0) term21). Qed.
Lemma lem7070488 : term55 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7070489 (h1 : term55 = (BIT1 0)) : term54 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7070490 : (term55 = (BIT1 0)) = (term54 = True).
Proof. exact (prop_ext (fun h1 : term55 = (BIT1 0) => @lem7070489 h1) (fun h1 : term54 = True => @lem7070488)). Qed.
Lemma lem7070491 : term54 = True.
Proof. exact (EQ_MP (@lem7070490) (@lem7070488)). Qed.
Lemma lem7070492 : term53 = True.
Proof. exact (TRANS (@lem7070487) (@lem7070491)). Qed.
Lemma lem7070493 : True = term53.
Proof. exact (SYM (@lem7070492)). Qed.
Lemma lem7070494 : term53.
Proof. exact (EQ_MP (@lem7070493) (@lem0)). Qed.
Lemma lem7070495 : term58.
Proof. exact (@lem7070484 (@lem7070494)). Qed.
Lemma lem7070497 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7070498 : term30 = term31.
Proof. exact (@lem7070497 term21 term21). Qed.
Lemma lem7070499 : (term32 = (BIT1 0)) = (term33 = term21).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7070500 : term33 = term21.
Proof. exact (EQ_MP (@lem7070499) (@lem940073)). Qed.
Lemma lem7070501 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7070502 : term31 = term27.
Proof. exact (MK_COMB (@lem7070501) (@lem7070500)). Qed.
Lemma lem7070503 : term30 = term27.
Proof. exact (TRANS (@lem7070498) (@lem7070502)). Qed.
Lemma lem7070505 (m : nat) (n : nat) : (term59 m n) = (term60 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7070506 : term61 = term62.
Proof. exact (@lem7070505 term21 term21). Qed.
Lemma lem7070507 : (term32 = (BIT1 0)) = (term33 = term21).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7070508 : term33 = term21.
Proof. exact (EQ_MP (@lem7070507) (@lem940073)). Qed.
Lemma lem7070509 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7070510 : term31 = term27.
Proof. exact (MK_COMB (@lem7070509) (@lem7070508)). Qed.
Lemma lem7070511 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7070512 : term62 = term17.
Proof. exact (MK_COMB (@lem7070511) (@lem7070510)). Qed.
Lemma lem7070513 : term61 = term17.
Proof. exact (TRANS (@lem7070506) (@lem7070512)). Qed.
Lemma lem7070514 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7070515 : term63 = term46.
Proof. exact (MK_COMB (@lem7070514) (@lem7070513)). Qed.
Lemma lem7070516 : term64 = term48.
Proof. exact (MK_COMB (@lem7070515) (@lem7070503)). Qed.
Lemma lem7070518 (m : nat) : (term65 m) = term51.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7070519 : term48 = term51.
Proof. exact (@lem7070518 term21). Qed.
Lemma lem7070520 : term64 = term51.
Proof. exact (TRANS (@lem7070516) (@lem7070519)). Qed.
Lemma lem7070521 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7070522 : term66 = term67.
Proof. exact (MK_COMB (@lem7070521) (@lem7070520)). Qed.
Lemma lem7070523 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem7070524 : term68 = term69.
Proof. exact (MK_COMB (@lem7070522) (@lem7070523)). Qed.
Lemma lem7070526 (x : nat) : (term70 x) = term51.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7070527 : term69 = term51.
Proof. exact (@lem7070526 term21). Qed.
Lemma lem7070528 : term68 = term51.
Proof. exact (TRANS (@lem7070524) (@lem7070527)). Qed.
Lemma lem7070530 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7070531 : term30 = term31.
Proof. exact (@lem7070530 term21 term21). Qed.
Lemma lem7070532 : (term32 = (BIT1 0)) = (term33 = term21).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7070533 : term33 = term21.
Proof. exact (EQ_MP (@lem7070532) (@lem940073)). Qed.
Lemma lem7070534 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7070535 : term31 = term27.
Proof. exact (MK_COMB (@lem7070534) (@lem7070533)). Qed.
Lemma lem7070536 : term30 = term27.
Proof. exact (TRANS (@lem7070531) (@lem7070535)). Qed.
Lemma lem7070537 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem7070538 : term71 = term69.
Proof. exact (MK_COMB (@lem7070537) (@lem7070536)). Qed.
Lemma lem7070540 (x : nat) : (term70 x) = term51.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7070541 : term69 = term51.
Proof. exact (@lem7070540 term21). Qed.
Lemma lem7070542 : term71 = term51.
Proof. exact (TRANS (@lem7070538) (@lem7070541)). Qed.
Lemma lem7070543 : term51 = term71.
Proof. exact (SYM (@lem7070542)). Qed.
Lemma lem7070544 : term68 = term71.
Proof. exact (TRANS (@lem7070528) (@lem7070543)). Qed.
Lemma lem7070545 : term49 = term72.
Proof. exact (@lem7070495 (@lem7070544)). Qed.
Lemma lem7070546 : term48 = term72.
Proof. exact (TRANS (@lem7070461) (@lem7070545)). Qed.
Lemma lem7070548 (x : real) : (term38 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7070549 : term72 = term51.
Proof. exact (@lem7070548 term51). Qed.
Lemma lem7070550 : term48 = term51.
Proof. exact (TRANS (@lem7070546) (@lem7070549)). Qed.
Lemma lem7070551 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7070552 : term73 = term67.
Proof. exact (MK_COMB (@lem7070551) (@lem7070550)). Qed.
Lemma lem7070553 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7070554 (x : real) : (term44 x) = (term74 x).
Proof. exact (MK_COMB (@lem7070552) (@lem7070553 x)). Qed.
Lemma lem7070555 (x : real) : (term43 x) = (term74 x).
Proof. exact (TRANS (@lem7070452 x) (@lem7070554 x)). Qed.
Lemma lem7070556 (x : real) : (term74 x) = term51.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7070557 (x : real) : (term43 x) = term51.
Proof. exact (TRANS (@lem7070555 x) (@lem7070556 x)). Qed.
Lemma lem7070558 (x : real) : (term14 x) = term51.
Proof. exact (TRANS (@lem7070451 x) (@lem7070557 x)). Qed.
Lemma lem7070559 (x : real) : (term13 x) = term51.
Proof. exact (TRANS (@lem7070406 x) (@lem7070558 x)). Qed.
Lemma lem7070560 (x : real) : (term12 x) = term51.
Proof. exact (TRANS (@lem7070405 x) (@lem7070559 x)). Qed.
Lemma lem7070561 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7070562 (x : real) : (term75 x) = term76.
Proof. exact (MK_COMB (@lem7070561) (@lem7070560 x)). Qed.
Lemma lem7070563 : term76 = term77.
Proof. exact (@lem1982785 term51). Qed.
Lemma lem7070565 (x : nat) : (real_of_num x) = (term45 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7070566 : term51 = term72.
Proof. exact (@lem7070565 (NUMERAL 0)). Qed.
Lemma lem7070568 (x : nat) : (term18 x) = (term19 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7070569 : term17 = term20.
Proof. exact (@lem7070568 term21). Qed.
Lemma lem7070570 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7070571 : term22 = term23.
Proof. exact (MK_COMB (@lem7070570) (@lem7070569)). Qed.
Lemma lem7070572 : term77 = term78.
Proof. exact (MK_COMB (@lem7070571) (@lem7070566)). Qed.
Lemma lem7070573 : term78 = term79.
Proof. exact (@lem1981613 term17 term51 term27 term27). Qed.
Lemma lem7070575 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7070576 : term30 = term31.
Proof. exact (@lem7070575 term21 term21). Qed.
Lemma lem7070577 : (term32 = (BIT1 0)) = (term33 = term21).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7070578 : term33 = term21.
Proof. exact (EQ_MP (@lem7070577) (@lem940073)). Qed.
Lemma lem7070579 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7070580 : term31 = term27.
Proof. exact (MK_COMB (@lem7070579) (@lem7070578)). Qed.
Lemma lem7070581 : term30 = term27.
Proof. exact (TRANS (@lem7070576) (@lem7070580)). Qed.
Lemma lem7070583 (x : nat) : (term80 x) = term51.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7070584 : term77 = term51.
Proof. exact (@lem7070583 term21). Qed.
Lemma lem7070585 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7070586 : term81 = term82.
Proof. exact (MK_COMB (@lem7070585) (@lem7070584)). Qed.
Lemma lem7070587 : term79 = term72.
Proof. exact (MK_COMB (@lem7070586) (@lem7070581)). Qed.
Lemma lem7070588 : term78 = term72.
Proof. exact (TRANS (@lem7070573) (@lem7070587)). Qed.
Lemma lem7070589 : term77 = term72.
Proof. exact (TRANS (@lem7070572) (@lem7070588)). Qed.
Lemma lem7070591 (x : real) : (term38 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7070592 : term72 = term51.
Proof. exact (@lem7070591 term51). Qed.
Lemma lem7070593 : term77 = term51.
Proof. exact (TRANS (@lem7070589) (@lem7070592)). Qed.
Lemma lem7070594 : term76 = term51.
Proof. exact (TRANS (@lem7070563) (@lem7070593)). Qed.
Lemma lem7070595 (x : real) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem7070596 (x : real) : ((term75 x) = term76) = ((term75 x) = term51).
Proof. exact (MK_COMB (@lem7070595 x) (@lem7070594)). Qed.
Lemma lem7070597 (x : real) : (term75 x) = term51.
Proof. exact (EQ_MP (@lem7070596 x) (@lem7070562 x)). Qed.
Lemma lem7070598 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7070599 (x : real) : (term84 x) = term85.
Proof. exact (MK_COMB (@lem7070598) (@lem7070597 x)). Qed.
Lemma lem7070600 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem7070601 (x : real) : (term86 x) = term87.
Proof. exact (MK_COMB (@lem7070599 x) (@lem7070600)). Qed.
Lemma lem7070602 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7070603 (x : real) : (term88 x) = term85.
Proof. exact (MK_COMB (@lem7070602) (@lem7070560 x)). Qed.
Lemma lem7070604 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem7070605 (x : real) : (term89 x) = term87.
Proof. exact (MK_COMB (@lem7070603 x) (@lem7070604)). Qed.
Lemma lem7070606 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7070607 (x : real) : (term90 x) = term91.
Proof. exact (MK_COMB (@lem7070606) (@lem7070605 x)). Qed.
Lemma lem7070608 (x : real) : (term8 x) = term92.
Proof. exact (MK_COMB (@lem7070607 x) (@lem7070601 x)). Qed.
Lemma lem7070622 (x : real) : (term7 x) = term92.
Proof. exact (TRANS (@lem7070388 x) (@lem7070608 x)). Qed.
Lemma lem7070632 (h1 : term92) : term92.
Proof. exact (h1). Qed.
Lemma lem7070633 (h1 : term87) : term87.
Proof. exact (h1). Qed.
Lemma lem7070635 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7070636 : term87 = term93.
Proof. exact (@lem7070635 term51 term51). Qed.
Lemma lem7070638 (x : nat) : (real_of_num x) = (term45 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7070639 : term51 = term72.
Proof. exact (@lem7070638 (NUMERAL 0)). Qed.
Lemma lem7070641 (x : nat) : (real_of_num x) = (term45 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7070642 : term51 = term72.
Proof. exact (@lem7070641 (NUMERAL 0)). Qed.
Lemma lem7070643 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7070644 : term94 = term95.
Proof. exact (MK_COMB (@lem7070643) (@lem7070642)). Qed.
Lemma lem7070645 : term93 = term96.
Proof. exact (MK_COMB (@lem7070644) (@lem7070639)). Qed.
Lemma lem7070646 : term97.
Proof. exact (@lem1980255 term51 term27 term51 term27). Qed.
Lemma lem7070648 (m : nat) (n : nat) : (term52 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7070649 : term53 = term54.
Proof. exact (@lem7070648 (NUMERAL 0) term21). Qed.
Lemma lem7070650 : term55 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7070651 (h1 : term55 = (BIT1 0)) : term54 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7070652 : (term55 = (BIT1 0)) = (term54 = True).
Proof. exact (prop_ext (fun h1 : term55 = (BIT1 0) => @lem7070651 h1) (fun h1 : term54 = True => @lem7070650)). Qed.
Lemma lem7070653 : term54 = True.
Proof. exact (EQ_MP (@lem7070652) (@lem7070650)). Qed.
Lemma lem7070654 : term53 = True.
Proof. exact (TRANS (@lem7070649) (@lem7070653)). Qed.
Lemma lem7070655 : True = term53.
Proof. exact (SYM (@lem7070654)). Qed.
Lemma lem7070656 : term53.
Proof. exact (EQ_MP (@lem7070655) (@lem0)). Qed.
Lemma lem7070657 : term98.
Proof. exact (@lem7070646 (@lem7070656)). Qed.
Lemma lem7070659 (m : nat) (n : nat) : (term52 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7070660 : term53 = term54.
Proof. exact (@lem7070659 (NUMERAL 0) term21). Qed.
Lemma lem7070661 : term55 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7070662 (h1 : term55 = (BIT1 0)) : term54 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7070663 : (term55 = (BIT1 0)) = (term54 = True).
Proof. exact (prop_ext (fun h1 : term55 = (BIT1 0) => @lem7070662 h1) (fun h1 : term54 = True => @lem7070661)). Qed.
Lemma lem7070664 : term54 = True.
Proof. exact (EQ_MP (@lem7070663) (@lem7070661)). Qed.
Lemma lem7070665 : term53 = True.
Proof. exact (TRANS (@lem7070660) (@lem7070664)). Qed.
Lemma lem7070666 : True = term53.
Proof. exact (SYM (@lem7070665)). Qed.
Lemma lem7070667 : term53.
Proof. exact (EQ_MP (@lem7070666) (@lem0)). Qed.
Lemma lem7070668 : term96 = term99.
Proof. exact (@lem7070657 (@lem7070667)). Qed.
Lemma lem7070670 (x : nat) : (term70 x) = term51.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7070671 : term69 = term51.
Proof. exact (@lem7070670 term21). Qed.
Lemma lem7070673 (x : nat) : (term70 x) = term51.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7070674 : term69 = term51.
Proof. exact (@lem7070673 term21). Qed.
Lemma lem7070675 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7070676 : term100 = term94.
Proof. exact (MK_COMB (@lem7070675) (@lem7070674)). Qed.
Lemma lem7070677 : term99 = term93.
Proof. exact (MK_COMB (@lem7070676) (@lem7070671)). Qed.
Lemma lem7070679 (m : nat) (n : nat) : (term52 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7070680 : term93 = term101.
Proof. exact (@lem7070679 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7070681 : term101 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7070682 : term93 = False.
Proof. exact (TRANS (@lem7070680) (@lem7070681)). Qed.
Lemma lem7070683 : term99 = False.
Proof. exact (TRANS (@lem7070677) (@lem7070682)). Qed.
Lemma lem7070684 : term96 = False.
Proof. exact (TRANS (@lem7070668) (@lem7070683)). Qed.
Lemma lem7070685 : term93 = False.
Proof. exact (TRANS (@lem7070645) (@lem7070684)). Qed.
Lemma lem7070686 : term87 = False.
Proof. exact (TRANS (@lem7070636) (@lem7070685)). Qed.
Lemma lem7070687 (h1 : term87) : False.
Proof. exact (EQ_MP (@lem7070686) (@lem7070633 h1)). Qed.
Lemma lem7070688 (h1 : term87) : term87.
Proof. exact (h1). Qed.
Lemma lem7070690 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7070691 : term87 = term93.
Proof. exact (@lem7070690 term51 term51). Qed.
Lemma lem7070693 (x : nat) : (real_of_num x) = (term45 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7070694 : term51 = term72.
Proof. exact (@lem7070693 (NUMERAL 0)). Qed.
Lemma lem7070696 (x : nat) : (real_of_num x) = (term45 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7070697 : term51 = term72.
Proof. exact (@lem7070696 (NUMERAL 0)). Qed.
Lemma lem7070698 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7070699 : term94 = term95.
Proof. exact (MK_COMB (@lem7070698) (@lem7070697)). Qed.
Lemma lem7070700 : term93 = term96.
Proof. exact (MK_COMB (@lem7070699) (@lem7070694)). Qed.
Lemma lem7070701 : term97.
Proof. exact (@lem1980255 term51 term27 term51 term27). Qed.
Lemma lem7070703 (m : nat) (n : nat) : (term52 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7070704 : term53 = term54.
Proof. exact (@lem7070703 (NUMERAL 0) term21). Qed.
Lemma lem7070705 : term55 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7070706 (h1 : term55 = (BIT1 0)) : term54 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7070707 : (term55 = (BIT1 0)) = (term54 = True).
Proof. exact (prop_ext (fun h1 : term55 = (BIT1 0) => @lem7070706 h1) (fun h1 : term54 = True => @lem7070705)). Qed.
Lemma lem7070708 : term54 = True.
Proof. exact (EQ_MP (@lem7070707) (@lem7070705)). Qed.
Lemma lem7070709 : term53 = True.
Proof. exact (TRANS (@lem7070704) (@lem7070708)). Qed.
Lemma lem7070710 : True = term53.
Proof. exact (SYM (@lem7070709)). Qed.
Lemma lem7070711 : term53.
Proof. exact (EQ_MP (@lem7070710) (@lem0)). Qed.
Lemma lem7070712 : term98.
Proof. exact (@lem7070701 (@lem7070711)). Qed.
Lemma lem7070714 (m : nat) (n : nat) : (term52 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7070715 : term53 = term54.
Proof. exact (@lem7070714 (NUMERAL 0) term21). Qed.
Lemma lem7070716 : term55 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7070717 (h1 : term55 = (BIT1 0)) : term54 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7070718 : (term55 = (BIT1 0)) = (term54 = True).
Proof. exact (prop_ext (fun h1 : term55 = (BIT1 0) => @lem7070717 h1) (fun h1 : term54 = True => @lem7070716)). Qed.
Lemma lem7070719 : term54 = True.
Proof. exact (EQ_MP (@lem7070718) (@lem7070716)). Qed.
Lemma lem7070720 : term53 = True.
Proof. exact (TRANS (@lem7070715) (@lem7070719)). Qed.
Lemma lem7070721 : True = term53.
Proof. exact (SYM (@lem7070720)). Qed.
Lemma lem7070722 : term53.
Proof. exact (EQ_MP (@lem7070721) (@lem0)). Qed.
Lemma lem7070723 : term96 = term99.
Proof. exact (@lem7070712 (@lem7070722)). Qed.
Lemma lem7070725 (x : nat) : (term70 x) = term51.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7070726 : term69 = term51.
Proof. exact (@lem7070725 term21). Qed.
Lemma lem7070728 (x : nat) : (term70 x) = term51.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7070729 : term69 = term51.
Proof. exact (@lem7070728 term21). Qed.
Lemma lem7070730 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7070731 : term100 = term94.
Proof. exact (MK_COMB (@lem7070730) (@lem7070729)). Qed.
Lemma lem7070732 : term99 = term93.
Proof. exact (MK_COMB (@lem7070731) (@lem7070726)). Qed.
Lemma lem7070734 (m : nat) (n : nat) : (term52 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7070735 : term93 = term101.
Proof. exact (@lem7070734 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7070736 : term101 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7070737 : term93 = False.
Proof. exact (TRANS (@lem7070735) (@lem7070736)). Qed.
Lemma lem7070738 : term99 = False.
Proof. exact (TRANS (@lem7070732) (@lem7070737)). Qed.
Lemma lem7070739 : term96 = False.
Proof. exact (TRANS (@lem7070723) (@lem7070738)). Qed.
Lemma lem7070740 : term93 = False.
Proof. exact (TRANS (@lem7070700) (@lem7070739)). Qed.
Lemma lem7070741 : term87 = False.
Proof. exact (TRANS (@lem7070691) (@lem7070740)). Qed.
Lemma lem7070742 (h1 : term87) : False.
Proof. exact (EQ_MP (@lem7070741) (@lem7070688 h1)). Qed.
Lemma lem7070743 (h1 : term92) : False.
Proof. exact (or_elim (@lem7070632 h1) (fun h0 : term87 => @lem7070687 h0) (fun h0 : term87 => @lem7070742 h0)). Qed.
Lemma lem7070745 (h1 : term92) : term92.
Proof. exact (h1). Qed.
Lemma lem7070746 (h1 : term92) : term92 = False.
Proof. exact (prop_ext (fun h2 : term92 => @lem7070743 h1) (fun h2 : False => @lem7070745 h1)). Qed.
Lemma lem7070747 (h1 : term92) : False.
Proof. exact (EQ_MP (@lem7070746 h1) (@lem7070745 h1)). Qed.
Lemma lem7070748 (x : real) (h1 : term7 x) : term7 x.
Proof. exact (h1). Qed.
Lemma lem7070749 (x : real) (h1 : term7 x) : term92.
Proof. exact (EQ_MP (@lem7070622 x) (@lem7070748 x h1)). Qed.
Lemma lem7070750 (x : real) (h1 : term7 x) : term92 = False.
Proof. exact (prop_ext (fun h2 : term92 => @lem7070747 h2) (fun h2 : False => @lem7070749 x h1)). Qed.
Lemma lem7070751 (x : real) (h1 : term7 x) : False.
Proof. exact (EQ_MP (@lem7070750 x h1) (@lem7070749 x h1)). Qed.
Lemma lem7070752 (x : real) : term102 x.
Proof. exact (fun h0 : term7 x => @lem7070751 x h0). Qed.
Lemma lem7070753 (x : real) : term103 x.
Proof. exact (@lem1386578 ((real_neg x) = (term9 x))). Qed.
Lemma lem7070768 (x : real) : (real_neg x) = (term9 x).
Proof. exact (@lem7070753 x (@lem7070752 x)). Qed.
Lemma lem7070769 {_132004 : Type'} (f : _132004 -> real) (x : _132004) : (term104 _132004 f x) = (term105 _132004 f x).
Proof. exact (@lem7070768 (f x)). Qed.
Lemma lem7070770 {_132004 : Type'} (f : _132004 -> real) : (term106 _132004 f) = (term107 _132004 f).
Proof. exact (fun_ext (fun x : _132004 => @lem7070769 _132004 f x)). Qed.
Lemma lem7070771 {_132004 : Type'} (s : _132004 -> Prop) : (@sum _132004 s) = (@sum _132004 s).
Proof. exact (eq_refl (@sum _132004 s)). Qed.
Lemma lem7070772 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : (term108 _132004 s f) = (term109 _132004 s f).
Proof. exact (MK_COMB (@lem7070771 _132004 s) (@lem7070770 _132004 f)). Qed.
Lemma lem7070773 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7070774 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : (term110 _132004 s f) = (term111 _132004 s f).
Proof. exact (MK_COMB (@lem7070773) (@lem7070772 _132004 s f)). Qed.
Lemma lem7070776 (x : real) : (real_neg x) = (term9 x).
Proof. exact (@lem7070753 x (@lem7070752 x)). Qed.
Lemma lem7070777 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : (term112 _132004 s f) = (term113 _132004 s f).
Proof. exact (@lem7070776 (@sum _132004 s f)). Qed.
Lemma lem7070778 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : ((term108 _132004 s f) = (term112 _132004 s f)) = ((term109 _132004 s f) = (term113 _132004 s f)).
Proof. exact (MK_COMB (@lem7070774 _132004 s f) (@lem7070777 _132004 s f)). Qed.
Lemma lem7070779 {_132004 : Type'} (f : _132004 -> real) : (term114 _132004 f) = (term115 _132004 f).
Proof. exact (fun_ext (fun s : _132004 -> Prop => @lem7070778 _132004 s f)). Qed.
Lemma lem7070780 {_132004 : Type'} : (@all (_132004 -> Prop)) = (@all (_132004 -> Prop)).
Proof. exact (eq_refl (@all (_132004 -> Prop))). Qed.
Lemma lem7070781 {_132004 : Type'} (f : _132004 -> real) : (term116 _132004 f) = (term117 _132004 f).
Proof. exact (MK_COMB (@lem7070780 _132004) (@lem7070779 _132004 f)). Qed.
Lemma lem7070782 {_132004 : Type'} : (term118 _132004) = (term119 _132004).
Proof. exact (fun_ext (fun f : _132004 -> real => @lem7070781 _132004 f)). Qed.
Lemma lem7070783 {_132004 : Type'} : (@all (_132004 -> real)) = (@all (_132004 -> real)).
Proof. exact (eq_refl (@all (_132004 -> real))). Qed.
Lemma lem7070784 {_132004 : Type'} : (term120 _132004) = (term121 _132004).
Proof. exact (MK_COMB (@lem7070783 _132004) (@lem7070782 _132004)). Qed.
Lemma lem7070785 {_132004 : Type'} : (term121 _132004) = (term120 _132004).
Proof. exact (SYM (@lem7070784 _132004)). Qed.
Lemma lem7070797 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term5 A s c f) = (term6 A c s f).
Proof. exact (EQ_MP (@lem7070376 A c s f) (@lem7070375 A c f s)). Qed.
Lemma lem7070798 {_132004 : Type'} (c : real) (s : _132004 -> Prop) (f : _132004 -> real) : (term5 _132004 s c f) = (term6 _132004 c s f).
Proof. exact (@lem7070797 _132004 c s f). Qed.
Lemma lem7070799 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : (term109 _132004 s f) = (term113 _132004 s f).
Proof. exact (@lem7070798 _132004 term17 s f). Qed.
Lemma lem7070800 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7070801 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : (term111 _132004 s f) = (term122 _132004 s f).
Proof. exact (MK_COMB (@lem7070800) (@lem7070799 _132004 s f)). Qed.
Lemma lem7070802 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : (term113 _132004 s f) = (term113 _132004 s f).
Proof. exact (eq_refl (term113 _132004 s f)). Qed.
Lemma lem7070803 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : ((term109 _132004 s f) = (term113 _132004 s f)) = ((term113 _132004 s f) = (term113 _132004 s f)).
Proof. exact (MK_COMB (@lem7070801 _132004 s f) (@lem7070802 _132004 s f)). Qed.
Lemma lem7070805 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7070806 (x : real) : (x = x) = True.
Proof. exact (@lem7070805 real x). Qed.
Lemma lem7070807 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : ((term113 _132004 s f) = (term113 _132004 s f)) = True.
Proof. exact (@lem7070806 (term113 _132004 s f)). Qed.
Lemma lem7070808 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : ((term109 _132004 s f) = (term113 _132004 s f)) = True.
Proof. exact (TRANS (@lem7070803 _132004 s f) (@lem7070807 _132004 s f)). Qed.
Lemma lem7070809 {_132004 : Type'} (f : _132004 -> real) : (term115 _132004 f) = (term123 _132004).
Proof. exact (fun_ext (fun s : _132004 -> Prop => @lem7070808 _132004 s f)). Qed.
Lemma lem7070810 {_132004 : Type'} : (@all (_132004 -> Prop)) = (@all (_132004 -> Prop)).
Proof. exact (eq_refl (@all (_132004 -> Prop))). Qed.
Lemma lem7070811 {_132004 : Type'} (f : _132004 -> real) : (term117 _132004 f) = (term124 _132004).
Proof. exact (MK_COMB (@lem7070810 _132004) (@lem7070809 _132004 f)). Qed.
Lemma lem7070813 {A : Type'} (t : Prop) : (term125 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7070814 {_132004 : Type'} (t : Prop) : (term126 _132004 t) = t.
Proof. exact (@lem7070813 (_132004 -> Prop) t). Qed.
Lemma lem7070815 {_132004 : Type'} : (term124 _132004) = True.
Proof. exact (@lem7070814 _132004 True). Qed.
Lemma lem7070816 {_132004 : Type'} (f : _132004 -> real) : (term117 _132004 f) = True.
Proof. exact (TRANS (@lem7070811 _132004 f) (@lem7070815 _132004)). Qed.
Lemma lem7070817 {_132004 : Type'} : (term119 _132004) = (term127 _132004).
Proof. exact (fun_ext (fun f : _132004 -> real => @lem7070816 _132004 f)). Qed.
Lemma lem7070818 {_132004 : Type'} : (@all (_132004 -> real)) = (@all (_132004 -> real)).
Proof. exact (eq_refl (@all (_132004 -> real))). Qed.
Lemma lem7070819 {_132004 : Type'} : (term121 _132004) = (term128 _132004).
Proof. exact (MK_COMB (@lem7070818 _132004) (@lem7070817 _132004)). Qed.
Lemma lem7070821 {A : Type'} (t : Prop) : (term125 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7070822 {_132004 : Type'} (t : Prop) : (term129 _132004 t) = t.
Proof. exact (@lem7070821 (_132004 -> real) t). Qed.
Lemma lem7070823 {_132004 : Type'} : (term128 _132004) = True.
Proof. exact (@lem7070822 _132004 True). Qed.
Lemma lem7070824 {_132004 : Type'} : (term121 _132004) = True.
Proof. exact (TRANS (@lem7070819 _132004) (@lem7070823 _132004)). Qed.
Lemma lem7070825 {_132004 : Type'} : True = (term121 _132004).
Proof. exact (SYM (@lem7070824 _132004)). Qed.
Lemma lem7070826 {_132004 : Type'} : term121 _132004.
Proof. exact (EQ_MP (@lem7070825 _132004) (@lem0)). Qed.
Lemma lem7070827 {_132004 : Type'} : term120 _132004.
Proof. exact (EQ_MP (@lem7070785 _132004) (@lem7070826 _132004)). Qed.
