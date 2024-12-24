Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416504_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16451_spec.
Require Import thm16452_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm2318497_spec.
Require Import thm2318526_spec.
Require Import thm2318527_spec.
Require Import thm2318532_spec.
Require Import thm2318533_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318541_spec.
Require Import thm2318542_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem2414415 : term0 = term1.
Proof. exact (@lem2318604 term1). Qed.
Lemma lem2414436 (P : int -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2414437 : term4 = term5.
Proof. exact (@lem2414436 term6). Qed.
Lemma lem2414438 (x : int) : (term7 x) = ((int_neg x) = (term8 x)).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2414439 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2414441 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2414439) (@lem2414438 x)). Qed.
Lemma lem2414442 : term11 = term12.
Proof. exact (fun_ext (fun x : int => @lem2414441 x)). Qed.
Lemma lem2414443 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414444 : term5 = term13.
Proof. exact (MK_COMB (@lem2414443) (@lem2414442)). Qed.
Lemma lem2414445 : term4 = term13.
Proof. exact (TRANS (@lem2414437) (@lem2414444)). Qed.
Lemma lem2414447 (P : int -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2414448 (x : int) : (term14 x) = (term15 x).
Proof. exact (@lem2414447 (term16 x)). Qed.
Lemma lem2414449 (x : int) (y : int) : (term17 x y) = ((int_sub x y) = (term18 x y)).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem2414450 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2414452 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem2414450) (@lem2414449 x y)). Qed.
Lemma lem2414453 (x : int) : (term21 x) = (term22 x).
Proof. exact (fun_ext (fun y : int => @lem2414452 x y)). Qed.
Lemma lem2414454 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414455 (x : int) : (term15 x) = (term23 x).
Proof. exact (MK_COMB (@lem2414454) (@lem2414453 x)). Qed.
Lemma lem2414456 (x : int) : (term14 x) = (term23 x).
Proof. exact (TRANS (@lem2414448 x) (@lem2414455 x)). Qed.
Lemma lem2414457 (P : int -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2414458 : term24 = term25.
Proof. exact (@lem2414457 term26). Qed.
Lemma lem2414459 (x : int) : (term27 x) = (term28 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem2414460 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2414461 (x : int) : (term29 x) = (term14 x).
Proof. exact (MK_COMB (@lem2414460) (@lem2414459 x)). Qed.
Lemma lem2414462 (x : int) : (term29 x) = (term23 x).
Proof. exact (TRANS (@lem2414461 x) (@lem2414456 x)). Qed.
Lemma lem2414463 : term30 = term31.
Proof. exact (fun_ext (fun x : int => @lem2414462 x)). Qed.
Lemma lem2414464 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414465 : term25 = term32.
Proof. exact (MK_COMB (@lem2414464) (@lem2414463)). Qed.
Lemma lem2414466 : term24 = term32.
Proof. exact (TRANS (@lem2414458) (@lem2414465)). Qed.
Lemma lem2414467 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414468 : term33 = term34.
Proof. exact (MK_COMB (@lem2414467) (@lem2414445)). Qed.
Lemma lem2414469 : term35 = term36.
Proof. exact (MK_COMB (@lem2414468) (@lem2414466)). Qed.
Lemma lem2414470 : term37 = term35.
Proof. exact (@lem17045 term38 term39). Qed.
Lemma lem2414472 : term37 = term36.
Proof. exact (TRANS (@lem2414470) (@lem2414469)). Qed.
Lemma lem2414475 (x : int) : (term10 x) = (term10 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem2414476 : term12 = term12.
Proof. exact (fun_ext (fun x : int => @lem2414475 x)). Qed.
Lemma lem2414477 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414478 : term13 = term13.
Proof. exact (MK_COMB (@lem2414477) (@lem2414476)). Qed.
Lemma lem2414481 (x : int) (y : int) : (term20 x y) = (term20 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem2414482 (x : int) : (term22 x) = (term22 x).
Proof. exact (fun_ext (fun y : int => @lem2414481 x y)). Qed.
Lemma lem2414483 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414484 (x : int) : (term23 x) = (term23 x).
Proof. exact (MK_COMB (@lem2414483) (@lem2414482 x)). Qed.
Lemma lem2414485 : term31 = term31.
Proof. exact (fun_ext (fun x : int => @lem2414484 x)). Qed.
Lemma lem2414486 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414487 : term32 = term32.
Proof. exact (MK_COMB (@lem2414486) (@lem2414485)). Qed.
Lemma lem2414488 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414489 : term34 = term34.
Proof. exact (MK_COMB (@lem2414488) (@lem2414478)). Qed.
Lemma lem2414490 : term36 = term36.
Proof. exact (MK_COMB (@lem2414489) (@lem2414487)). Qed.
Lemma lem2414491 : term37 = term36.
Proof. exact (TRANS (@lem2414472) (@lem2414490)). Qed.
Lemma lem2414493 (y : int) (x : int) : (term40 x y) = (term41 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2414494 (x : int) : (term10 x) = (term42 x).
Proof. exact (@lem2414493 (term8 x) (int_neg x)). Qed.
Lemma lem2414496 (x : int) (y : int) : (int_le x y) = (term43 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2414497 (x : int) : (term44 x) = (term45 x).
Proof. exact (@lem2414496 (term46 x) (term8 x)). Qed.
Lemma lem2414499 (x : int) (y : int) : (term47 x y) = (term48 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2414500 (x : int) : (term49 x) = (term50 x).
Proof. exact (@lem2414499 (int_neg x) term51). Qed.
Lemma lem2414502 (x : int) : (term52 x) = (term53 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2414503 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2414504 (x : int) : (term54 x) = (term55 x).
Proof. exact (MK_COMB (@lem2414503) (@lem2414502 x)). Qed.
Lemma lem2414506 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2414507 : term57 = term58.
Proof. exact (@lem2414506 term59). Qed.
Lemma lem2414508 (x : int) : (term50 x) = (term60 x).
Proof. exact (MK_COMB (@lem2414504 x) (@lem2414507)). Qed.
Lemma lem2414509 (x : int) : (term49 x) = (term60 x).
Proof. exact (TRANS (@lem2414500 x) (@lem2414508 x)). Qed.
Lemma lem2414510 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2414511 (x : int) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem2414510) (@lem2414509 x)). Qed.
Lemma lem2414513 (x : int) (y : int) : (term63 x y) = (term64 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2414514 (x : int) : (term65 x) = (term66 x).
Proof. exact (@lem2414513 term67 x). Qed.
Lemma lem2414516 (x : int) : (term52 x) = (term53 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2414517 : term68 = term69.
Proof. exact (@lem2414516 term51). Qed.
Lemma lem2414519 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2414520 : term57 = term58.
Proof. exact (@lem2414519 term59). Qed.
Lemma lem2414521 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2414522 : term69 = term70.
Proof. exact (MK_COMB (@lem2414521) (@lem2414520)). Qed.
Lemma lem2414523 : term68 = term70.
Proof. exact (TRANS (@lem2414517) (@lem2414522)). Qed.
Lemma lem2414524 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2414525 : term71 = term72.
Proof. exact (MK_COMB (@lem2414524) (@lem2414523)). Qed.
Lemma lem2414526 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2414527 (x : int) : (term66 x) = (term73 x).
Proof. exact (MK_COMB (@lem2414525) (@lem2414526 x)). Qed.
Lemma lem2414528 (x : int) : (term65 x) = (term73 x).
Proof. exact (TRANS (@lem2414514 x) (@lem2414527 x)). Qed.
Lemma lem2414529 (x : int) : (term45 x) = (term74 x).
Proof. exact (MK_COMB (@lem2414511 x) (@lem2414528 x)). Qed.
Lemma lem2414530 (x : int) : (term44 x) = (term74 x).
Proof. exact (TRANS (@lem2414497 x) (@lem2414529 x)). Qed.
Lemma lem2414531 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414532 (x : int) : (term75 x) = (term76 x).
Proof. exact (MK_COMB (@lem2414531) (@lem2414530 x)). Qed.
Lemma lem2414534 (x : int) (y : int) : (int_le x y) = (term43 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2414535 (x : int) : (term77 x) = (term78 x).
Proof. exact (@lem2414534 (term79 x) (int_neg x)). Qed.
Lemma lem2414537 (x : int) (y : int) : (term47 x y) = (term48 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2414538 (x : int) : (term80 x) = (term81 x).
Proof. exact (@lem2414537 (term8 x) term51). Qed.
Lemma lem2414540 (x : int) (y : int) : (term63 x y) = (term64 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2414541 (x : int) : (term65 x) = (term66 x).
Proof. exact (@lem2414540 term67 x). Qed.
Lemma lem2414543 (x : int) : (term52 x) = (term53 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2414544 : term68 = term69.
Proof. exact (@lem2414543 term51). Qed.
Lemma lem2414546 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2414547 : term57 = term58.
Proof. exact (@lem2414546 term59). Qed.
Lemma lem2414548 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2414549 : term69 = term70.
Proof. exact (MK_COMB (@lem2414548) (@lem2414547)). Qed.
Lemma lem2414550 : term68 = term70.
Proof. exact (TRANS (@lem2414544) (@lem2414549)). Qed.
Lemma lem2414551 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2414552 : term71 = term72.
Proof. exact (MK_COMB (@lem2414551) (@lem2414550)). Qed.
Lemma lem2414553 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2414554 (x : int) : (term66 x) = (term73 x).
Proof. exact (MK_COMB (@lem2414552) (@lem2414553 x)). Qed.
Lemma lem2414555 (x : int) : (term65 x) = (term73 x).
Proof. exact (TRANS (@lem2414541 x) (@lem2414554 x)). Qed.
Lemma lem2414556 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2414557 (x : int) : (term82 x) = (term83 x).
Proof. exact (MK_COMB (@lem2414556) (@lem2414555 x)). Qed.
Lemma lem2414559 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2414560 : term57 = term58.
Proof. exact (@lem2414559 term59). Qed.
Lemma lem2414561 (x : int) : (term81 x) = (term84 x).
Proof. exact (MK_COMB (@lem2414557 x) (@lem2414560)). Qed.
Lemma lem2414562 (x : int) : (term80 x) = (term84 x).
Proof. exact (TRANS (@lem2414538 x) (@lem2414561 x)). Qed.
Lemma lem2414563 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2414564 (x : int) : (term85 x) = (term86 x).
Proof. exact (MK_COMB (@lem2414563) (@lem2414562 x)). Qed.
Lemma lem2414566 (x : int) : (term52 x) = (term53 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2414567 (x : int) : (term78 x) = (term87 x).
Proof. exact (MK_COMB (@lem2414564 x) (@lem2414566 x)). Qed.
Lemma lem2414568 (x : int) : (term77 x) = (term87 x).
Proof. exact (TRANS (@lem2414535 x) (@lem2414567 x)). Qed.
Lemma lem2414569 (x : int) : (term42 x) = (term88 x).
Proof. exact (MK_COMB (@lem2414532 x) (@lem2414568 x)). Qed.
Lemma lem2414570 (x : int) : (term10 x) = (term88 x).
Proof. exact (TRANS (@lem2414494 x) (@lem2414569 x)). Qed.
Lemma lem2414571 : term12 = term89.
Proof. exact (fun_ext (fun x : int => @lem2414570 x)). Qed.
Lemma lem2414572 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414573 : term13 = term90.
Proof. exact (MK_COMB (@lem2414572) (@lem2414571)). Qed.
Lemma lem2414575 (y : int) (x : int) : (term40 x y) = (term41 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2414576 (x : int) (y : int) : (term20 x y) = (term91 x y).
Proof. exact (@lem2414575 (term18 x y) (int_sub x y)). Qed.
Lemma lem2414578 (x : int) (y : int) : (int_le x y) = (term43 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2414579 (x : int) (y : int) : (term92 x y) = (term93 x y).
Proof. exact (@lem2414578 (term94 x y) (term18 x y)). Qed.
Lemma lem2414581 (x : int) (y : int) : (term47 x y) = (term48 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2414582 (x : int) (y : int) : (term95 x y) = (term96 x y).
Proof. exact (@lem2414581 (int_sub x y) term51). Qed.
Lemma lem2414584 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2414585 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2414586 (x : int) (y : int) : (term99 x y) = (term100 x y).
Proof. exact (MK_COMB (@lem2414585) (@lem2414584 x y)). Qed.
Lemma lem2414588 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2414589 : term57 = term58.
Proof. exact (@lem2414588 term59). Qed.
Lemma lem2414590 (x : int) (y : int) : (term96 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem2414586 x y) (@lem2414589)). Qed.
Lemma lem2414591 (x : int) (y : int) : (term95 x y) = (term101 x y).
Proof. exact (TRANS (@lem2414582 x y) (@lem2414590 x y)). Qed.
Lemma lem2414592 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2414593 (x : int) (y : int) : (term102 x y) = (term103 x y).
Proof. exact (MK_COMB (@lem2414592) (@lem2414591 x y)). Qed.
Lemma lem2414595 (x : int) (y : int) : (term47 x y) = (term48 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2414596 (x : int) (y : int) : (term104 x y) = (term105 x y).
Proof. exact (@lem2414595 x (term8 y)). Qed.
Lemma lem2414598 (x : int) (y : int) : (term63 x y) = (term64 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2414599 (y : int) : (term65 y) = (term66 y).
Proof. exact (@lem2414598 term67 y). Qed.
Lemma lem2414601 (x : int) : (term52 x) = (term53 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2414602 : term68 = term69.
Proof. exact (@lem2414601 term51). Qed.
Lemma lem2414604 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2414605 : term57 = term58.
Proof. exact (@lem2414604 term59). Qed.
Lemma lem2414606 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2414607 : term69 = term70.
Proof. exact (MK_COMB (@lem2414606) (@lem2414605)). Qed.
Lemma lem2414608 : term68 = term70.
Proof. exact (TRANS (@lem2414602) (@lem2414607)). Qed.
Lemma lem2414609 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2414610 : term71 = term72.
Proof. exact (MK_COMB (@lem2414609) (@lem2414608)). Qed.
Lemma lem2414611 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2414612 (y : int) : (term66 y) = (term73 y).
Proof. exact (MK_COMB (@lem2414610) (@lem2414611 y)). Qed.
Lemma lem2414613 (y : int) : (term65 y) = (term73 y).
Proof. exact (TRANS (@lem2414599 y) (@lem2414612 y)). Qed.
Lemma lem2414614 (x : int) : (term106 x) = (term106 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem2414615 (x : int) (y : int) : (term105 x y) = (term107 x y).
Proof. exact (MK_COMB (@lem2414614 x) (@lem2414613 y)). Qed.
Lemma lem2414616 (x : int) (y : int) : (term104 x y) = (term107 x y).
Proof. exact (TRANS (@lem2414596 x y) (@lem2414615 x y)). Qed.
Lemma lem2414617 (x : int) (y : int) : (term93 x y) = (term108 x y).
Proof. exact (MK_COMB (@lem2414593 x y) (@lem2414616 x y)). Qed.
Lemma lem2414618 (x : int) (y : int) : (term92 x y) = (term108 x y).
Proof. exact (TRANS (@lem2414579 x y) (@lem2414617 x y)). Qed.
Lemma lem2414619 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414620 (x : int) (y : int) : (term109 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem2414619) (@lem2414618 x y)). Qed.
Lemma lem2414622 (x : int) (y : int) : (int_le x y) = (term43 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2414623 (x : int) (y : int) : (term111 x y) = (term112 x y).
Proof. exact (@lem2414622 (term113 x y) (int_sub x y)). Qed.
Lemma lem2414625 (x : int) (y : int) : (term47 x y) = (term48 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2414626 (x : int) (y : int) : (term114 x y) = (term115 x y).
Proof. exact (@lem2414625 (term18 x y) term51). Qed.
Lemma lem2414628 (x : int) (y : int) : (term47 x y) = (term48 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2414629 (x : int) (y : int) : (term104 x y) = (term105 x y).
Proof. exact (@lem2414628 x (term8 y)). Qed.
Lemma lem2414631 (x : int) (y : int) : (term63 x y) = (term64 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2414632 (y : int) : (term65 y) = (term66 y).
Proof. exact (@lem2414631 term67 y). Qed.
Lemma lem2414634 (x : int) : (term52 x) = (term53 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2414635 : term68 = term69.
Proof. exact (@lem2414634 term51). Qed.
Lemma lem2414637 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2414638 : term57 = term58.
Proof. exact (@lem2414637 term59). Qed.
Lemma lem2414639 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2414640 : term69 = term70.
Proof. exact (MK_COMB (@lem2414639) (@lem2414638)). Qed.
Lemma lem2414641 : term68 = term70.
Proof. exact (TRANS (@lem2414635) (@lem2414640)). Qed.
Lemma lem2414642 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2414643 : term71 = term72.
Proof. exact (MK_COMB (@lem2414642) (@lem2414641)). Qed.
Lemma lem2414644 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2414645 (y : int) : (term66 y) = (term73 y).
Proof. exact (MK_COMB (@lem2414643) (@lem2414644 y)). Qed.
Lemma lem2414646 (y : int) : (term65 y) = (term73 y).
Proof. exact (TRANS (@lem2414632 y) (@lem2414645 y)). Qed.
Lemma lem2414647 (x : int) : (term106 x) = (term106 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem2414648 (x : int) (y : int) : (term105 x y) = (term107 x y).
Proof. exact (MK_COMB (@lem2414647 x) (@lem2414646 y)). Qed.
Lemma lem2414649 (x : int) (y : int) : (term104 x y) = (term107 x y).
Proof. exact (TRANS (@lem2414629 x y) (@lem2414648 x y)). Qed.
Lemma lem2414650 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2414651 (x : int) (y : int) : (term116 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem2414650) (@lem2414649 x y)). Qed.
Lemma lem2414653 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2414654 : term57 = term58.
Proof. exact (@lem2414653 term59). Qed.
Lemma lem2414655 (x : int) (y : int) : (term115 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem2414651 x y) (@lem2414654)). Qed.
Lemma lem2414656 (x : int) (y : int) : (term114 x y) = (term118 x y).
Proof. exact (TRANS (@lem2414626 x y) (@lem2414655 x y)). Qed.
Lemma lem2414657 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2414658 (x : int) (y : int) : (term119 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem2414657) (@lem2414656 x y)). Qed.
Lemma lem2414660 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2414661 (x : int) (y : int) : (term112 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem2414658 x y) (@lem2414660 x y)). Qed.
Lemma lem2414662 (x : int) (y : int) : (term111 x y) = (term121 x y).
Proof. exact (TRANS (@lem2414623 x y) (@lem2414661 x y)). Qed.
Lemma lem2414663 (x : int) (y : int) : (term91 x y) = (term122 x y).
Proof. exact (MK_COMB (@lem2414620 x y) (@lem2414662 x y)). Qed.
Lemma lem2414664 (x : int) (y : int) : (term20 x y) = (term122 x y).
Proof. exact (TRANS (@lem2414576 x y) (@lem2414663 x y)). Qed.
Lemma lem2414665 (x : int) : (term22 x) = (term123 x).
Proof. exact (fun_ext (fun y : int => @lem2414664 x y)). Qed.
Lemma lem2414666 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414667 (x : int) : (term23 x) = (term124 x).
Proof. exact (MK_COMB (@lem2414666) (@lem2414665 x)). Qed.
Lemma lem2414668 : term31 = term125.
Proof. exact (fun_ext (fun x : int => @lem2414667 x)). Qed.
Lemma lem2414669 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414670 : term32 = term126.
Proof. exact (MK_COMB (@lem2414669) (@lem2414668)). Qed.
Lemma lem2414671 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414672 : term34 = term127.
Proof. exact (MK_COMB (@lem2414671) (@lem2414573)). Qed.
Lemma lem2414673 : term36 = term128.
Proof. exact (MK_COMB (@lem2414672) (@lem2414670)). Qed.
Lemma lem2414674 : term37 = term128.
Proof. exact (TRANS (@lem2414491) (@lem2414673)). Qed.
Lemma lem2414678 (t : Prop) : (term129 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2414679 : term130 = term128.
Proof. exact (@lem2414678 term128). Qed.
Lemma lem2414683 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2414684 (P : int -> Prop) (Q : int -> Prop) : (term133 P Q) = (term134 P Q).
Proof. exact (@lem2414683 int P Q). Qed.
Lemma lem2414685 : term135 = term136.
Proof. exact (@lem2414684 term137 term138). Qed.
Lemma lem2414686 (x : int) : (term139 x) = (term74 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem2414687 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414688 (x : int) : (term140 x) = (term76 x).
Proof. exact (MK_COMB (@lem2414687) (@lem2414686 x)). Qed.
Lemma lem2414689 (x : int) : (term141 x) = (term87 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem2414690 (x : int) : (term142 x) = (term88 x).
Proof. exact (MK_COMB (@lem2414688 x) (@lem2414689 x)). Qed.
Lemma lem2414691 : term143 = term89.
Proof. exact (fun_ext (fun x : int => @lem2414690 x)). Qed.
Lemma lem2414692 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414693 : term135 = term90.
Proof. exact (MK_COMB (@lem2414692) (@lem2414691)). Qed.
Lemma lem2414694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2414695 : term144 = term145.
Proof. exact (MK_COMB (@lem2414694) (@lem2414693)). Qed.
Lemma lem2414696 (x : int) : (term139 x) = (term74 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem2414697 : term146 = term137.
Proof. exact (fun_ext (fun x : int => @lem2414696 x)). Qed.
Lemma lem2414698 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414699 : term147 = term148.
Proof. exact (MK_COMB (@lem2414698) (@lem2414697)). Qed.
Lemma lem2414700 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414701 : term149 = term150.
Proof. exact (MK_COMB (@lem2414700) (@lem2414699)). Qed.
Lemma lem2414702 (x : int) : (term141 x) = (term87 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem2414703 : term151 = term138.
Proof. exact (fun_ext (fun x : int => @lem2414702 x)). Qed.
Lemma lem2414704 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414705 : term152 = term153.
Proof. exact (MK_COMB (@lem2414704) (@lem2414703)). Qed.
Lemma lem2414706 : term136 = term154.
Proof. exact (MK_COMB (@lem2414701) (@lem2414705)). Qed.
Lemma lem2414707 : (term135 = term136) = (term90 = term154).
Proof. exact (MK_COMB (@lem2414695) (@lem2414706)). Qed.
Lemma lem2414708 : term90 = term154.
Proof. exact (EQ_MP (@lem2414707) (@lem2414685)). Qed.
Lemma lem2414719 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414720 : term127 = term155.
Proof. exact (MK_COMB (@lem2414719) (@lem2414708)). Qed.
Lemma lem2414726 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2414727 (P : int -> Prop) (Q : int -> Prop) : (term133 P Q) = (term134 P Q).
Proof. exact (@lem2414726 int P Q). Qed.
Lemma lem2414728 (x : int) : (term156 x) = (term157 x).
Proof. exact (@lem2414727 (term158 x) (term159 x)). Qed.
Lemma lem2414729 (x : int) (y : int) : (term160 x y) = (term108 x y).
Proof. exact (eq_refl (term160 x y)). Qed.
Lemma lem2414730 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414731 (x : int) (y : int) : (term161 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem2414730) (@lem2414729 x y)). Qed.
Lemma lem2414732 (x : int) (y : int) : (term162 x y) = (term121 x y).
Proof. exact (eq_refl (term162 x y)). Qed.
Lemma lem2414733 (x : int) (y : int) : (term163 x y) = (term122 x y).
Proof. exact (MK_COMB (@lem2414731 x y) (@lem2414732 x y)). Qed.
Lemma lem2414734 (x : int) : (term164 x) = (term123 x).
Proof. exact (fun_ext (fun y : int => @lem2414733 x y)). Qed.
Lemma lem2414735 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414736 (x : int) : (term156 x) = (term124 x).
Proof. exact (MK_COMB (@lem2414735) (@lem2414734 x)). Qed.
Lemma lem2414737 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2414738 (x : int) : (term165 x) = (term166 x).
Proof. exact (MK_COMB (@lem2414737) (@lem2414736 x)). Qed.
Lemma lem2414739 (x : int) (y : int) : (term160 x y) = (term108 x y).
Proof. exact (eq_refl (term160 x y)). Qed.
Lemma lem2414740 (x : int) : (term167 x) = (term158 x).
Proof. exact (fun_ext (fun y : int => @lem2414739 x y)). Qed.
Lemma lem2414741 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414742 (x : int) : (term168 x) = (term169 x).
Proof. exact (MK_COMB (@lem2414741) (@lem2414740 x)). Qed.
Lemma lem2414743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414744 (x : int) : (term170 x) = (term171 x).
Proof. exact (MK_COMB (@lem2414743) (@lem2414742 x)). Qed.
Lemma lem2414745 (x : int) (y : int) : (term162 x y) = (term121 x y).
Proof. exact (eq_refl (term162 x y)). Qed.
Lemma lem2414746 (x : int) : (term172 x) = (term159 x).
Proof. exact (fun_ext (fun y : int => @lem2414745 x y)). Qed.
Lemma lem2414747 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414748 (x : int) : (term173 x) = (term174 x).
Proof. exact (MK_COMB (@lem2414747) (@lem2414746 x)). Qed.
Lemma lem2414749 (x : int) : (term157 x) = (term175 x).
Proof. exact (MK_COMB (@lem2414744 x) (@lem2414748 x)). Qed.
Lemma lem2414750 (x : int) : ((term156 x) = (term157 x)) = ((term124 x) = (term175 x)).
Proof. exact (MK_COMB (@lem2414738 x) (@lem2414749 x)). Qed.
Lemma lem2414751 (x : int) : (term124 x) = (term175 x).
Proof. exact (EQ_MP (@lem2414750 x) (@lem2414728 x)). Qed.
Lemma lem2414762 : term125 = term176.
Proof. exact (fun_ext (fun x : int => @lem2414751 x)). Qed.
Lemma lem2414763 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414764 : term126 = term177.
Proof. exact (MK_COMB (@lem2414763) (@lem2414762)). Qed.
Lemma lem2414766 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2414767 (P : int -> Prop) (Q : int -> Prop) : (term133 P Q) = (term134 P Q).
Proof. exact (@lem2414766 int P Q). Qed.
Lemma lem2414768 : term178 = term179.
Proof. exact (@lem2414767 term180 term181). Qed.
Lemma lem2414769 (x : int) : (term182 x) = (term169 x).
Proof. exact (eq_refl (term182 x)). Qed.
Lemma lem2414770 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414771 (x : int) : (term183 x) = (term171 x).
Proof. exact (MK_COMB (@lem2414770) (@lem2414769 x)). Qed.
Lemma lem2414772 (x : int) : (term184 x) = (term174 x).
Proof. exact (eq_refl (term184 x)). Qed.
Lemma lem2414773 (x : int) : (term185 x) = (term175 x).
Proof. exact (MK_COMB (@lem2414771 x) (@lem2414772 x)). Qed.
Lemma lem2414774 : term186 = term176.
Proof. exact (fun_ext (fun x : int => @lem2414773 x)). Qed.
Lemma lem2414775 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414776 : term178 = term177.
Proof. exact (MK_COMB (@lem2414775) (@lem2414774)). Qed.
Lemma lem2414777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2414778 : term187 = term188.
Proof. exact (MK_COMB (@lem2414777) (@lem2414776)). Qed.
Lemma lem2414779 (x : int) : (term182 x) = (term169 x).
Proof. exact (eq_refl (term182 x)). Qed.
Lemma lem2414780 : term189 = term180.
Proof. exact (fun_ext (fun x : int => @lem2414779 x)). Qed.
Lemma lem2414781 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414782 : term190 = term191.
Proof. exact (MK_COMB (@lem2414781) (@lem2414780)). Qed.
Lemma lem2414783 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414784 : term192 = term193.
Proof. exact (MK_COMB (@lem2414783) (@lem2414782)). Qed.
Lemma lem2414785 (x : int) : (term184 x) = (term174 x).
Proof. exact (eq_refl (term184 x)). Qed.
Lemma lem2414786 : term194 = term181.
Proof. exact (fun_ext (fun x : int => @lem2414785 x)). Qed.
Lemma lem2414787 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414788 : term195 = term196.
Proof. exact (MK_COMB (@lem2414787) (@lem2414786)). Qed.
Lemma lem2414789 : term179 = term197.
Proof. exact (MK_COMB (@lem2414784) (@lem2414788)). Qed.
Lemma lem2414790 : (term178 = term179) = (term177 = term197).
Proof. exact (MK_COMB (@lem2414778) (@lem2414789)). Qed.
Lemma lem2414791 : term177 = term197.
Proof. exact (EQ_MP (@lem2414790) (@lem2414768)). Qed.
Lemma lem2414810 : term126 = term197.
Proof. exact (TRANS (@lem2414764) (@lem2414791)). Qed.
Lemma lem2414811 : term128 = term198.
Proof. exact (MK_COMB (@lem2414720) (@lem2414810)). Qed.
Lemma lem2414815 : term130 = term198.
Proof. exact (TRANS (@lem2414679) (@lem2414811)). Qed.
Lemma lem2414816 (x : int) : (term74 x) = (term74 x).
Proof. exact (eq_refl (term74 x)). Qed.
Lemma lem2414817 : term137 = term137.
Proof. exact (fun_ext (fun x : int => @lem2414816 x)). Qed.
Lemma lem2414818 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414819 : term148 = term148.
Proof. exact (MK_COMB (@lem2414818) (@lem2414817)). Qed.
Lemma lem2414820 (x : int) : (term87 x) = (term87 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem2414821 : term138 = term138.
Proof. exact (fun_ext (fun x : int => @lem2414820 x)). Qed.
Lemma lem2414822 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414823 : term153 = term153.
Proof. exact (MK_COMB (@lem2414822) (@lem2414821)). Qed.
Lemma lem2414824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414825 : term150 = term150.
Proof. exact (MK_COMB (@lem2414824) (@lem2414819)). Qed.
Lemma lem2414826 : term154 = term154.
Proof. exact (MK_COMB (@lem2414825) (@lem2414823)). Qed.
Lemma lem2414827 (x : int) (y : int) : (term108 x y) = (term108 x y).
Proof. exact (eq_refl (term108 x y)). Qed.
Lemma lem2414828 (x : int) : (term158 x) = (term158 x).
Proof. exact (fun_ext (fun y : int => @lem2414827 x y)). Qed.
Lemma lem2414829 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414830 (x : int) : (term169 x) = (term169 x).
Proof. exact (MK_COMB (@lem2414829) (@lem2414828 x)). Qed.
Lemma lem2414831 : term180 = term180.
Proof. exact (fun_ext (fun x : int => @lem2414830 x)). Qed.
Lemma lem2414832 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414833 : term191 = term191.
Proof. exact (MK_COMB (@lem2414832) (@lem2414831)). Qed.
Lemma lem2414834 (x : int) (y : int) : (term121 x y) = (term121 x y).
Proof. exact (eq_refl (term121 x y)). Qed.
Lemma lem2414835 (x : int) : (term159 x) = (term159 x).
Proof. exact (fun_ext (fun y : int => @lem2414834 x y)). Qed.
Lemma lem2414836 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414837 (x : int) : (term174 x) = (term174 x).
Proof. exact (MK_COMB (@lem2414836) (@lem2414835 x)). Qed.
Lemma lem2414838 : term181 = term181.
Proof. exact (fun_ext (fun x : int => @lem2414837 x)). Qed.
Lemma lem2414839 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414840 : term196 = term196.
Proof. exact (MK_COMB (@lem2414839) (@lem2414838)). Qed.
Lemma lem2414841 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414842 : term193 = term193.
Proof. exact (MK_COMB (@lem2414841) (@lem2414833)). Qed.
Lemma lem2414843 : term197 = term197.
Proof. exact (MK_COMB (@lem2414842) (@lem2414840)). Qed.
Lemma lem2414844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414845 : term155 = term155.
Proof. exact (MK_COMB (@lem2414844) (@lem2414826)). Qed.
Lemma lem2414846 : term198 = term198.
Proof. exact (MK_COMB (@lem2414845) (@lem2414843)). Qed.
Lemma lem2414847 : term130 = term198.
Proof. exact (TRANS (@lem2414815) (@lem2414846)). Qed.
Lemma lem2414848 (x : int) : (term74 x) = (term74 x).
Proof. exact (eq_refl (term74 x)). Qed.
Lemma lem2414849 : term137 = term137.
Proof. exact (fun_ext (fun x : int => @lem2414848 x)). Qed.
Lemma lem2414850 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414851 : term148 = term148.
Proof. exact (MK_COMB (@lem2414850) (@lem2414849)). Qed.
Lemma lem2414852 (x : int) : (term87 x) = (term87 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem2414853 : term138 = term138.
Proof. exact (fun_ext (fun x : int => @lem2414852 x)). Qed.
Lemma lem2414854 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414855 : term153 = term153.
Proof. exact (MK_COMB (@lem2414854) (@lem2414853)). Qed.
Lemma lem2414856 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414857 : term150 = term150.
Proof. exact (MK_COMB (@lem2414856) (@lem2414851)). Qed.
Lemma lem2414858 : term154 = term154.
Proof. exact (MK_COMB (@lem2414857) (@lem2414855)). Qed.
Lemma lem2414859 (x : int) (y : int) : (term108 x y) = (term108 x y).
Proof. exact (eq_refl (term108 x y)). Qed.
Lemma lem2414860 (x : int) : (term158 x) = (term158 x).
Proof. exact (fun_ext (fun y : int => @lem2414859 x y)). Qed.
Lemma lem2414861 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414862 (x : int) : (term169 x) = (term169 x).
Proof. exact (MK_COMB (@lem2414861) (@lem2414860 x)). Qed.
Lemma lem2414863 : term180 = term180.
Proof. exact (fun_ext (fun x : int => @lem2414862 x)). Qed.
Lemma lem2414864 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414865 : term191 = term191.
Proof. exact (MK_COMB (@lem2414864) (@lem2414863)). Qed.
Lemma lem2414866 (x : int) (y : int) : (term121 x y) = (term121 x y).
Proof. exact (eq_refl (term121 x y)). Qed.
Lemma lem2414867 (x : int) : (term159 x) = (term159 x).
Proof. exact (fun_ext (fun y : int => @lem2414866 x y)). Qed.
Lemma lem2414868 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414869 (x : int) : (term174 x) = (term174 x).
Proof. exact (MK_COMB (@lem2414868) (@lem2414867 x)). Qed.
Lemma lem2414870 : term181 = term181.
Proof. exact (fun_ext (fun x : int => @lem2414869 x)). Qed.
Lemma lem2414871 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2414872 : term196 = term196.
Proof. exact (MK_COMB (@lem2414871) (@lem2414870)). Qed.
Lemma lem2414873 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414874 : term193 = term193.
Proof. exact (MK_COMB (@lem2414873) (@lem2414865)). Qed.
Lemma lem2414875 : term197 = term197.
Proof. exact (MK_COMB (@lem2414874) (@lem2414872)). Qed.
Lemma lem2414876 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2414877 : term155 = term155.
Proof. exact (MK_COMB (@lem2414876) (@lem2414858)). Qed.
Lemma lem2414878 : term198 = term198.
Proof. exact (MK_COMB (@lem2414877) (@lem2414875)). Qed.
Lemma lem2414879 : term130 = term198.
Proof. exact (TRANS (@lem2414847) (@lem2414878)). Qed.
Lemma lem2414880 (x : int) : (term74 x) = (term199 x).
Proof. exact (@lem1988287 (term73 x) (term60 x)). Qed.
Lemma lem2414881 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem2414888 (x : int) : (term53 x) = (term73 x).
Proof. exact (@lem1982785 (real_of_int x)). Qed.
Lemma lem2414889 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2414890 (x : int) : (term55 x) = (term83 x).
Proof. exact (MK_COMB (@lem2414889) (@lem2414888 x)). Qed.
Lemma lem2414893 (x : int) : (term60 x) = (term84 x).
Proof. exact (MK_COMB (@lem2414890 x) (@lem2414881)). Qed.
Lemma lem2414902 (x : int) : (term200 x) = (term200 x).
Proof. exact (eq_refl (term200 x)). Qed.
Lemma lem2414903 (x : int) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem2414902 x) (@lem2414893 x)). Qed.
Lemma lem2414904 (x : int) : (term202 x) = (term203 x).
Proof. exact (@lem1982792 (term73 x) (term84 x)). Qed.
Lemma lem2414905 (x : int) : (term204 x) = (term205 x).
Proof. exact (@lem1982781 (term73 x) term70 term58). Qed.
Lemma lem2414907 (x : nat) : (real_of_num x) = (term206 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2414908 : term58 = term207.
Proof. exact (@lem2414907 term59). Qed.
Lemma lem2414910 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2414911 : term70 = term210.
Proof. exact (@lem2414910 term59). Qed.
Lemma lem2414912 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2414913 : term72 = term211.
Proof. exact (MK_COMB (@lem2414912) (@lem2414911)). Qed.
Lemma lem2414914 : term212 = term213.
Proof. exact (MK_COMB (@lem2414913) (@lem2414908)). Qed.
Lemma lem2414915 : term213 = term214.
Proof. exact (@lem1981613 term70 term58 term58 term58). Qed.
Lemma lem2414917 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2414918 : term217 = term218.
Proof. exact (@lem2414917 term59 term59). Qed.
Lemma lem2414919 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2414920 : term220 = term59.
Proof. exact (EQ_MP (@lem2414919) (@lem940073)). Qed.
Lemma lem2414921 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2414922 : term218 = term58.
Proof. exact (MK_COMB (@lem2414921) (@lem2414920)). Qed.
Lemma lem2414923 : term217 = term58.
Proof. exact (TRANS (@lem2414918) (@lem2414922)). Qed.
Lemma lem2414925 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2414926 : term212 = term223.
Proof. exact (@lem2414925 term59 term59). Qed.
Lemma lem2414927 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2414928 : term220 = term59.
Proof. exact (EQ_MP (@lem2414927) (@lem940073)). Qed.
Lemma lem2414929 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2414930 : term218 = term58.
Proof. exact (MK_COMB (@lem2414929) (@lem2414928)). Qed.
Lemma lem2414931 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2414932 : term223 = term70.
Proof. exact (MK_COMB (@lem2414931) (@lem2414930)). Qed.
Lemma lem2414933 : term212 = term70.
Proof. exact (TRANS (@lem2414926) (@lem2414932)). Qed.
Lemma lem2414934 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2414935 : term224 = term225.
Proof. exact (MK_COMB (@lem2414934) (@lem2414933)). Qed.
Lemma lem2414936 : term214 = term210.
Proof. exact (MK_COMB (@lem2414935) (@lem2414923)). Qed.
Lemma lem2414937 : term213 = term210.
Proof. exact (TRANS (@lem2414915) (@lem2414936)). Qed.
Lemma lem2414938 : term212 = term210.
Proof. exact (TRANS (@lem2414914) (@lem2414937)). Qed.
Lemma lem2414940 (x : real) : (term226 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2414941 : term210 = term70.
Proof. exact (@lem2414940 term70). Qed.
Lemma lem2414942 : term212 = term70.
Proof. exact (TRANS (@lem2414938) (@lem2414941)). Qed.
Lemma lem2414943 (x : int) : (term227 x) = (term228 x).
Proof. exact (@lem1982749 term70 term70 (real_of_int x)). Qed.
Lemma lem2414945 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2414946 : term70 = term210.
Proof. exact (@lem2414945 term59). Qed.
Lemma lem2414948 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2414949 : term70 = term210.
Proof. exact (@lem2414948 term59). Qed.
Lemma lem2414950 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2414951 : term72 = term211.
Proof. exact (MK_COMB (@lem2414950) (@lem2414949)). Qed.
Lemma lem2414952 : term229 = term230.
Proof. exact (MK_COMB (@lem2414951) (@lem2414946)). Qed.
Lemma lem2414953 : term230 = term231.
Proof. exact (@lem1981613 term70 term70 term58 term58). Qed.
Lemma lem2414955 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2414956 : term217 = term218.
Proof. exact (@lem2414955 term59 term59). Qed.
Lemma lem2414957 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2414958 : term220 = term59.
Proof. exact (EQ_MP (@lem2414957) (@lem940073)). Qed.
Lemma lem2414959 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2414960 : term218 = term58.
Proof. exact (MK_COMB (@lem2414959) (@lem2414958)). Qed.
Lemma lem2414961 : term217 = term58.
Proof. exact (TRANS (@lem2414956) (@lem2414960)). Qed.
Lemma lem2414963 (m : nat) (n : nat) : (term232 m n) = (term216 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2414964 : term229 = term218.
Proof. exact (@lem2414963 term59 term59). Qed.
Lemma lem2414965 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2414966 : term220 = term59.
Proof. exact (EQ_MP (@lem2414965) (@lem940073)). Qed.
Lemma lem2414967 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2414968 : term218 = term58.
Proof. exact (MK_COMB (@lem2414967) (@lem2414966)). Qed.
Lemma lem2414969 : term229 = term58.
Proof. exact (TRANS (@lem2414964) (@lem2414968)). Qed.
Lemma lem2414970 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2414971 : term233 = term234.
Proof. exact (MK_COMB (@lem2414970) (@lem2414969)). Qed.
Lemma lem2414972 : term231 = term207.
Proof. exact (MK_COMB (@lem2414971) (@lem2414961)). Qed.
Lemma lem2414973 : term230 = term207.
Proof. exact (TRANS (@lem2414953) (@lem2414972)). Qed.
Lemma lem2414974 : term229 = term207.
Proof. exact (TRANS (@lem2414952) (@lem2414973)). Qed.
Lemma lem2414976 (x : real) : (term226 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2414977 : term207 = term58.
Proof. exact (@lem2414976 term58). Qed.
Lemma lem2414978 : term229 = term58.
Proof. exact (TRANS (@lem2414974) (@lem2414977)). Qed.
Lemma lem2414979 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2414980 : term235 = term236.
Proof. exact (MK_COMB (@lem2414979) (@lem2414978)). Qed.
Lemma lem2414981 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2414982 (x : int) : (term228 x) = (term237 x).
Proof. exact (MK_COMB (@lem2414980) (@lem2414981 x)). Qed.
Lemma lem2414983 (x : int) : (term227 x) = (term237 x).
Proof. exact (TRANS (@lem2414943 x) (@lem2414982 x)). Qed.
Lemma lem2414984 (x : int) : (term237 x) = (real_of_int x).
Proof. exact (@lem1982709 (real_of_int x)). Qed.
Lemma lem2414985 (x : int) : (term227 x) = (real_of_int x).
Proof. exact (TRANS (@lem2414983 x) (@lem2414984 x)). Qed.
Lemma lem2414986 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2414987 (x : int) : (term238 x) = (term106 x).
Proof. exact (MK_COMB (@lem2414986) (@lem2414985 x)). Qed.
Lemma lem2414988 (x : int) : (term205 x) = (term239 x).
Proof. exact (MK_COMB (@lem2414987 x) (@lem2414942)). Qed.
Lemma lem2414989 (x : int) : (term204 x) = (term239 x).
Proof. exact (TRANS (@lem2414905 x) (@lem2414988 x)). Qed.
Lemma lem2414990 (x : int) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem2414991 (x : int) : (term203 x) = (term240 x).
Proof. exact (MK_COMB (@lem2414990 x) (@lem2414989 x)). Qed.
Lemma lem2414992 (x : int) : (term240 x) = (term241 x).
Proof. exact (@lem1982763 (term73 x) (real_of_int x) term70). Qed.
Lemma lem2414993 (x : int) : (term242 x) = (term243 x).
Proof. exact (@lem1982713 term70 (real_of_int x)). Qed.
Lemma lem2414995 (x : nat) : (real_of_num x) = (term206 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2414996 : term58 = term207.
Proof. exact (@lem2414995 term59). Qed.
Lemma lem2414998 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2414999 : term70 = term210.
Proof. exact (@lem2414998 term59). Qed.
Lemma lem2415000 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415001 : term244 = term245.
Proof. exact (MK_COMB (@lem2415000) (@lem2414999)). Qed.
Lemma lem2415002 : term246 = term247.
Proof. exact (MK_COMB (@lem2415001) (@lem2414996)). Qed.
Lemma lem2415003 : term248.
Proof. exact (@lem1981473 term70 term58 term58 term58 term249 term58). Qed.
Lemma lem2415005 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415006 : term251 = term252.
Proof. exact (@lem2415005 (NUMERAL 0) term59). Qed.
Lemma lem2415007 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415008 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415009 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415008 h1) (fun h1 : term252 = True => @lem2415007)). Qed.
Lemma lem2415010 : term252 = True.
Proof. exact (EQ_MP (@lem2415009) (@lem2415007)). Qed.
Lemma lem2415011 : term251 = True.
Proof. exact (TRANS (@lem2415006) (@lem2415010)). Qed.
Lemma lem2415012 : True = term251.
Proof. exact (SYM (@lem2415011)). Qed.
Lemma lem2415013 : term251.
Proof. exact (EQ_MP (@lem2415012) (@lem0)). Qed.
Lemma lem2415014 : term254.
Proof. exact (@lem2415003 (@lem2415013)). Qed.
Lemma lem2415016 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415017 : term251 = term252.
Proof. exact (@lem2415016 (NUMERAL 0) term59). Qed.
Lemma lem2415018 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415019 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415020 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415019 h1) (fun h1 : term252 = True => @lem2415018)). Qed.
Lemma lem2415021 : term252 = True.
Proof. exact (EQ_MP (@lem2415020) (@lem2415018)). Qed.
Lemma lem2415022 : term251 = True.
Proof. exact (TRANS (@lem2415017) (@lem2415021)). Qed.
Lemma lem2415023 : True = term251.
Proof. exact (SYM (@lem2415022)). Qed.
Lemma lem2415024 : term251.
Proof. exact (EQ_MP (@lem2415023) (@lem0)). Qed.
Lemma lem2415025 : term255.
Proof. exact (@lem2415014 (@lem2415024)). Qed.
Lemma lem2415027 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415028 : term251 = term252.
Proof. exact (@lem2415027 (NUMERAL 0) term59). Qed.
Lemma lem2415029 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415030 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415031 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415030 h1) (fun h1 : term252 = True => @lem2415029)). Qed.
Lemma lem2415032 : term252 = True.
Proof. exact (EQ_MP (@lem2415031) (@lem2415029)). Qed.
Lemma lem2415033 : term251 = True.
Proof. exact (TRANS (@lem2415028) (@lem2415032)). Qed.
Lemma lem2415034 : True = term251.
Proof. exact (SYM (@lem2415033)). Qed.
Lemma lem2415035 : term251.
Proof. exact (EQ_MP (@lem2415034) (@lem0)). Qed.
Lemma lem2415036 : term256.
Proof. exact (@lem2415025 (@lem2415035)). Qed.
Lemma lem2415038 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415039 : term217 = term218.
Proof. exact (@lem2415038 term59 term59). Qed.
Lemma lem2415040 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415041 : term220 = term59.
Proof. exact (EQ_MP (@lem2415040) (@lem940073)). Qed.
Lemma lem2415042 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415043 : term218 = term58.
Proof. exact (MK_COMB (@lem2415042) (@lem2415041)). Qed.
Lemma lem2415044 : term217 = term58.
Proof. exact (TRANS (@lem2415039) (@lem2415043)). Qed.
Lemma lem2415046 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2415047 : term212 = term223.
Proof. exact (@lem2415046 term59 term59). Qed.
Lemma lem2415048 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415049 : term220 = term59.
Proof. exact (EQ_MP (@lem2415048) (@lem940073)). Qed.
Lemma lem2415050 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415051 : term218 = term58.
Proof. exact (MK_COMB (@lem2415050) (@lem2415049)). Qed.
Lemma lem2415052 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2415053 : term223 = term70.
Proof. exact (MK_COMB (@lem2415052) (@lem2415051)). Qed.
Lemma lem2415054 : term212 = term70.
Proof. exact (TRANS (@lem2415047) (@lem2415053)). Qed.
Lemma lem2415055 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415056 : term257 = term244.
Proof. exact (MK_COMB (@lem2415055) (@lem2415054)). Qed.
Lemma lem2415057 : term258 = term246.
Proof. exact (MK_COMB (@lem2415056) (@lem2415044)). Qed.
Lemma lem2415059 (m : nat) : (term259 m) = term249.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2415060 : term246 = term249.
Proof. exact (@lem2415059 term59). Qed.
Lemma lem2415061 : term258 = term249.
Proof. exact (TRANS (@lem2415057) (@lem2415060)). Qed.
Lemma lem2415062 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415063 : term260 = term261.
Proof. exact (MK_COMB (@lem2415062) (@lem2415061)). Qed.
Lemma lem2415064 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem2415065 : term262 = term263.
Proof. exact (MK_COMB (@lem2415063) (@lem2415064)). Qed.
Lemma lem2415067 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2415068 : term263 = term249.
Proof. exact (@lem2415067 term59). Qed.
Lemma lem2415069 : term262 = term249.
Proof. exact (TRANS (@lem2415065) (@lem2415068)). Qed.
Lemma lem2415071 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415072 : term217 = term218.
Proof. exact (@lem2415071 term59 term59). Qed.
Lemma lem2415073 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415074 : term220 = term59.
Proof. exact (EQ_MP (@lem2415073) (@lem940073)). Qed.
Lemma lem2415075 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415076 : term218 = term58.
Proof. exact (MK_COMB (@lem2415075) (@lem2415074)). Qed.
Lemma lem2415077 : term217 = term58.
Proof. exact (TRANS (@lem2415072) (@lem2415076)). Qed.
Lemma lem2415078 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem2415079 : term265 = term263.
Proof. exact (MK_COMB (@lem2415078) (@lem2415077)). Qed.
Lemma lem2415081 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2415082 : term263 = term249.
Proof. exact (@lem2415081 term59). Qed.
Lemma lem2415083 : term265 = term249.
Proof. exact (TRANS (@lem2415079) (@lem2415082)). Qed.
Lemma lem2415084 : term249 = term265.
Proof. exact (SYM (@lem2415083)). Qed.
Lemma lem2415085 : term262 = term265.
Proof. exact (TRANS (@lem2415069) (@lem2415084)). Qed.
Lemma lem2415086 : term247 = term266.
Proof. exact (@lem2415036 (@lem2415085)). Qed.
Lemma lem2415087 : term246 = term266.
Proof. exact (TRANS (@lem2415002) (@lem2415086)). Qed.
Lemma lem2415089 (x : real) : (term226 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2415090 : term266 = term249.
Proof. exact (@lem2415089 term249). Qed.
Lemma lem2415091 : term246 = term249.
Proof. exact (TRANS (@lem2415087) (@lem2415090)). Qed.
Lemma lem2415092 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415093 : term267 = term261.
Proof. exact (MK_COMB (@lem2415092) (@lem2415091)). Qed.
Lemma lem2415094 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2415095 (x : int) : (term243 x) = (term268 x).
Proof. exact (MK_COMB (@lem2415093) (@lem2415094 x)). Qed.
Lemma lem2415096 (x : int) : (term242 x) = (term268 x).
Proof. exact (TRANS (@lem2414993 x) (@lem2415095 x)). Qed.
Lemma lem2415097 (x : int) : (term268 x) = term249.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2415098 (x : int) : (term242 x) = term249.
Proof. exact (TRANS (@lem2415096 x) (@lem2415097 x)). Qed.
Lemma lem2415099 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415100 (x : int) : (term269 x) = term270.
Proof. exact (MK_COMB (@lem2415099) (@lem2415098 x)). Qed.
Lemma lem2415101 : term70 = term70.
Proof. exact (eq_refl term70). Qed.
Lemma lem2415102 (x : int) : (term241 x) = term271.
Proof. exact (MK_COMB (@lem2415100 x) (@lem2415101)). Qed.
Lemma lem2415103 (x : int) : (term240 x) = term271.
Proof. exact (TRANS (@lem2414992 x) (@lem2415102 x)). Qed.
Lemma lem2415104 : term271 = term70.
Proof. exact (@lem1982721 term70). Qed.
Lemma lem2415105 (x : int) : (term240 x) = term70.
Proof. exact (TRANS (@lem2415103 x) (@lem2415104)). Qed.
Lemma lem2415106 (x : int) : (term203 x) = term70.
Proof. exact (TRANS (@lem2414991 x) (@lem2415105 x)). Qed.
Lemma lem2415107 (x : int) : (term202 x) = term70.
Proof. exact (TRANS (@lem2414904 x) (@lem2415106 x)). Qed.
Lemma lem2415108 (x : int) : (term201 x) = term70.
Proof. exact (TRANS (@lem2414903 x) (@lem2415107 x)). Qed.
Lemma lem2415109 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2415110 (x : int) : (term272 x) = term273.
Proof. exact (MK_COMB (@lem2415109) (@lem2415108 x)). Qed.
Lemma lem2415111 : term249 = term249.
Proof. exact (eq_refl term249). Qed.
Lemma lem2415112 (x : int) : (term199 x) = term274.
Proof. exact (MK_COMB (@lem2415110 x) (@lem2415111)). Qed.
Lemma lem2415113 (x : int) : (term74 x) = term274.
Proof. exact (TRANS (@lem2414880 x) (@lem2415112 x)). Qed.
Lemma lem2415114 : term137 = term275.
Proof. exact (fun_ext (fun x : int => @lem2415113 x)). Qed.
Lemma lem2415115 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2415116 : term148 = term276.
Proof. exact (MK_COMB (@lem2415115) (@lem2415114)). Qed.
Lemma lem2415117 (x : int) : (term87 x) = (term277 x).
Proof. exact (@lem1988287 (term53 x) (term84 x)). Qed.
Lemma lem2415130 (x : int) : (term84 x) = (term84 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem2415137 (x : int) : (term53 x) = (term73 x).
Proof. exact (@lem1982785 (real_of_int x)). Qed.
Lemma lem2415138 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2415139 (x : int) : (term278 x) = (term200 x).
Proof. exact (MK_COMB (@lem2415138) (@lem2415137 x)). Qed.
Lemma lem2415140 (x : int) : (term279 x) = (term202 x).
Proof. exact (MK_COMB (@lem2415139 x) (@lem2415130 x)). Qed.
Lemma lem2415141 (x : int) : (term202 x) = (term203 x).
Proof. exact (@lem1982792 (term73 x) (term84 x)). Qed.
Lemma lem2415142 (x : int) : (term204 x) = (term205 x).
Proof. exact (@lem1982781 (term73 x) term70 term58). Qed.
Lemma lem2415144 (x : nat) : (real_of_num x) = (term206 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2415145 : term58 = term207.
Proof. exact (@lem2415144 term59). Qed.
Lemma lem2415147 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2415148 : term70 = term210.
Proof. exact (@lem2415147 term59). Qed.
Lemma lem2415149 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415150 : term72 = term211.
Proof. exact (MK_COMB (@lem2415149) (@lem2415148)). Qed.
Lemma lem2415151 : term212 = term213.
Proof. exact (MK_COMB (@lem2415150) (@lem2415145)). Qed.
Lemma lem2415152 : term213 = term214.
Proof. exact (@lem1981613 term70 term58 term58 term58). Qed.
Lemma lem2415154 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415155 : term217 = term218.
Proof. exact (@lem2415154 term59 term59). Qed.
Lemma lem2415156 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415157 : term220 = term59.
Proof. exact (EQ_MP (@lem2415156) (@lem940073)). Qed.
Lemma lem2415158 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415159 : term218 = term58.
Proof. exact (MK_COMB (@lem2415158) (@lem2415157)). Qed.
Lemma lem2415160 : term217 = term58.
Proof. exact (TRANS (@lem2415155) (@lem2415159)). Qed.
Lemma lem2415162 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2415163 : term212 = term223.
Proof. exact (@lem2415162 term59 term59). Qed.
Lemma lem2415164 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415165 : term220 = term59.
Proof. exact (EQ_MP (@lem2415164) (@lem940073)). Qed.
Lemma lem2415166 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415167 : term218 = term58.
Proof. exact (MK_COMB (@lem2415166) (@lem2415165)). Qed.
Lemma lem2415168 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2415169 : term223 = term70.
Proof. exact (MK_COMB (@lem2415168) (@lem2415167)). Qed.
Lemma lem2415170 : term212 = term70.
Proof. exact (TRANS (@lem2415163) (@lem2415169)). Qed.
Lemma lem2415171 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2415172 : term224 = term225.
Proof. exact (MK_COMB (@lem2415171) (@lem2415170)). Qed.
Lemma lem2415173 : term214 = term210.
Proof. exact (MK_COMB (@lem2415172) (@lem2415160)). Qed.
Lemma lem2415174 : term213 = term210.
Proof. exact (TRANS (@lem2415152) (@lem2415173)). Qed.
Lemma lem2415175 : term212 = term210.
Proof. exact (TRANS (@lem2415151) (@lem2415174)). Qed.
Lemma lem2415177 (x : real) : (term226 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2415178 : term210 = term70.
Proof. exact (@lem2415177 term70). Qed.
Lemma lem2415179 : term212 = term70.
Proof. exact (TRANS (@lem2415175) (@lem2415178)). Qed.
Lemma lem2415180 (x : int) : (term227 x) = (term228 x).
Proof. exact (@lem1982749 term70 term70 (real_of_int x)). Qed.
Lemma lem2415182 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2415183 : term70 = term210.
Proof. exact (@lem2415182 term59). Qed.
Lemma lem2415185 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2415186 : term70 = term210.
Proof. exact (@lem2415185 term59). Qed.
Lemma lem2415187 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415188 : term72 = term211.
Proof. exact (MK_COMB (@lem2415187) (@lem2415186)). Qed.
Lemma lem2415189 : term229 = term230.
Proof. exact (MK_COMB (@lem2415188) (@lem2415183)). Qed.
Lemma lem2415190 : term230 = term231.
Proof. exact (@lem1981613 term70 term70 term58 term58). Qed.
Lemma lem2415192 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415193 : term217 = term218.
Proof. exact (@lem2415192 term59 term59). Qed.
Lemma lem2415194 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415195 : term220 = term59.
Proof. exact (EQ_MP (@lem2415194) (@lem940073)). Qed.
Lemma lem2415196 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415197 : term218 = term58.
Proof. exact (MK_COMB (@lem2415196) (@lem2415195)). Qed.
Lemma lem2415198 : term217 = term58.
Proof. exact (TRANS (@lem2415193) (@lem2415197)). Qed.
Lemma lem2415200 (m : nat) (n : nat) : (term232 m n) = (term216 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2415201 : term229 = term218.
Proof. exact (@lem2415200 term59 term59). Qed.
Lemma lem2415202 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415203 : term220 = term59.
Proof. exact (EQ_MP (@lem2415202) (@lem940073)). Qed.
Lemma lem2415204 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415205 : term218 = term58.
Proof. exact (MK_COMB (@lem2415204) (@lem2415203)). Qed.
Lemma lem2415206 : term229 = term58.
Proof. exact (TRANS (@lem2415201) (@lem2415205)). Qed.
Lemma lem2415207 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2415208 : term233 = term234.
Proof. exact (MK_COMB (@lem2415207) (@lem2415206)). Qed.
Lemma lem2415209 : term231 = term207.
Proof. exact (MK_COMB (@lem2415208) (@lem2415198)). Qed.
Lemma lem2415210 : term230 = term207.
Proof. exact (TRANS (@lem2415190) (@lem2415209)). Qed.
Lemma lem2415211 : term229 = term207.
Proof. exact (TRANS (@lem2415189) (@lem2415210)). Qed.
Lemma lem2415213 (x : real) : (term226 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2415214 : term207 = term58.
Proof. exact (@lem2415213 term58). Qed.
Lemma lem2415215 : term229 = term58.
Proof. exact (TRANS (@lem2415211) (@lem2415214)). Qed.
Lemma lem2415216 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415217 : term235 = term236.
Proof. exact (MK_COMB (@lem2415216) (@lem2415215)). Qed.
Lemma lem2415218 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2415219 (x : int) : (term228 x) = (term237 x).
Proof. exact (MK_COMB (@lem2415217) (@lem2415218 x)). Qed.
Lemma lem2415220 (x : int) : (term227 x) = (term237 x).
Proof. exact (TRANS (@lem2415180 x) (@lem2415219 x)). Qed.
Lemma lem2415221 (x : int) : (term237 x) = (real_of_int x).
Proof. exact (@lem1982709 (real_of_int x)). Qed.
Lemma lem2415222 (x : int) : (term227 x) = (real_of_int x).
Proof. exact (TRANS (@lem2415220 x) (@lem2415221 x)). Qed.
Lemma lem2415223 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415224 (x : int) : (term238 x) = (term106 x).
Proof. exact (MK_COMB (@lem2415223) (@lem2415222 x)). Qed.
Lemma lem2415225 (x : int) : (term205 x) = (term239 x).
Proof. exact (MK_COMB (@lem2415224 x) (@lem2415179)). Qed.
Lemma lem2415226 (x : int) : (term204 x) = (term239 x).
Proof. exact (TRANS (@lem2415142 x) (@lem2415225 x)). Qed.
Lemma lem2415227 (x : int) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem2415228 (x : int) : (term203 x) = (term240 x).
Proof. exact (MK_COMB (@lem2415227 x) (@lem2415226 x)). Qed.
Lemma lem2415229 (x : int) : (term240 x) = (term241 x).
Proof. exact (@lem1982763 (term73 x) (real_of_int x) term70). Qed.
Lemma lem2415230 (x : int) : (term242 x) = (term243 x).
Proof. exact (@lem1982713 term70 (real_of_int x)). Qed.
Lemma lem2415232 (x : nat) : (real_of_num x) = (term206 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2415233 : term58 = term207.
Proof. exact (@lem2415232 term59). Qed.
Lemma lem2415235 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2415236 : term70 = term210.
Proof. exact (@lem2415235 term59). Qed.
Lemma lem2415237 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415238 : term244 = term245.
Proof. exact (MK_COMB (@lem2415237) (@lem2415236)). Qed.
Lemma lem2415239 : term246 = term247.
Proof. exact (MK_COMB (@lem2415238) (@lem2415233)). Qed.
Lemma lem2415240 : term248.
Proof. exact (@lem1981473 term70 term58 term58 term58 term249 term58). Qed.
Lemma lem2415242 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415243 : term251 = term252.
Proof. exact (@lem2415242 (NUMERAL 0) term59). Qed.
Lemma lem2415244 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415245 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415246 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415245 h1) (fun h1 : term252 = True => @lem2415244)). Qed.
Lemma lem2415247 : term252 = True.
Proof. exact (EQ_MP (@lem2415246) (@lem2415244)). Qed.
Lemma lem2415248 : term251 = True.
Proof. exact (TRANS (@lem2415243) (@lem2415247)). Qed.
Lemma lem2415249 : True = term251.
Proof. exact (SYM (@lem2415248)). Qed.
Lemma lem2415250 : term251.
Proof. exact (EQ_MP (@lem2415249) (@lem0)). Qed.
Lemma lem2415251 : term254.
Proof. exact (@lem2415240 (@lem2415250)). Qed.
Lemma lem2415253 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415254 : term251 = term252.
Proof. exact (@lem2415253 (NUMERAL 0) term59). Qed.
Lemma lem2415255 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415256 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415257 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415256 h1) (fun h1 : term252 = True => @lem2415255)). Qed.
Lemma lem2415258 : term252 = True.
Proof. exact (EQ_MP (@lem2415257) (@lem2415255)). Qed.
Lemma lem2415259 : term251 = True.
Proof. exact (TRANS (@lem2415254) (@lem2415258)). Qed.
Lemma lem2415260 : True = term251.
Proof. exact (SYM (@lem2415259)). Qed.
Lemma lem2415261 : term251.
Proof. exact (EQ_MP (@lem2415260) (@lem0)). Qed.
Lemma lem2415262 : term255.
Proof. exact (@lem2415251 (@lem2415261)). Qed.
Lemma lem2415264 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415265 : term251 = term252.
Proof. exact (@lem2415264 (NUMERAL 0) term59). Qed.
Lemma lem2415266 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415267 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415268 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415267 h1) (fun h1 : term252 = True => @lem2415266)). Qed.
Lemma lem2415269 : term252 = True.
Proof. exact (EQ_MP (@lem2415268) (@lem2415266)). Qed.
Lemma lem2415270 : term251 = True.
Proof. exact (TRANS (@lem2415265) (@lem2415269)). Qed.
Lemma lem2415271 : True = term251.
Proof. exact (SYM (@lem2415270)). Qed.
Lemma lem2415272 : term251.
Proof. exact (EQ_MP (@lem2415271) (@lem0)). Qed.
Lemma lem2415273 : term256.
Proof. exact (@lem2415262 (@lem2415272)). Qed.
Lemma lem2415275 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415276 : term217 = term218.
Proof. exact (@lem2415275 term59 term59). Qed.
Lemma lem2415277 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415278 : term220 = term59.
Proof. exact (EQ_MP (@lem2415277) (@lem940073)). Qed.
Lemma lem2415279 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415280 : term218 = term58.
Proof. exact (MK_COMB (@lem2415279) (@lem2415278)). Qed.
Lemma lem2415281 : term217 = term58.
Proof. exact (TRANS (@lem2415276) (@lem2415280)). Qed.
Lemma lem2415283 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2415284 : term212 = term223.
Proof. exact (@lem2415283 term59 term59). Qed.
Lemma lem2415285 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415286 : term220 = term59.
Proof. exact (EQ_MP (@lem2415285) (@lem940073)). Qed.
Lemma lem2415287 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415288 : term218 = term58.
Proof. exact (MK_COMB (@lem2415287) (@lem2415286)). Qed.
Lemma lem2415289 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2415290 : term223 = term70.
Proof. exact (MK_COMB (@lem2415289) (@lem2415288)). Qed.
Lemma lem2415291 : term212 = term70.
Proof. exact (TRANS (@lem2415284) (@lem2415290)). Qed.
Lemma lem2415292 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415293 : term257 = term244.
Proof. exact (MK_COMB (@lem2415292) (@lem2415291)). Qed.
Lemma lem2415294 : term258 = term246.
Proof. exact (MK_COMB (@lem2415293) (@lem2415281)). Qed.
Lemma lem2415296 (m : nat) : (term259 m) = term249.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2415297 : term246 = term249.
Proof. exact (@lem2415296 term59). Qed.
Lemma lem2415298 : term258 = term249.
Proof. exact (TRANS (@lem2415294) (@lem2415297)). Qed.
Lemma lem2415299 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415300 : term260 = term261.
Proof. exact (MK_COMB (@lem2415299) (@lem2415298)). Qed.
Lemma lem2415301 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem2415302 : term262 = term263.
Proof. exact (MK_COMB (@lem2415300) (@lem2415301)). Qed.
Lemma lem2415304 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2415305 : term263 = term249.
Proof. exact (@lem2415304 term59). Qed.
Lemma lem2415306 : term262 = term249.
Proof. exact (TRANS (@lem2415302) (@lem2415305)). Qed.
Lemma lem2415308 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415309 : term217 = term218.
Proof. exact (@lem2415308 term59 term59). Qed.
Lemma lem2415310 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415311 : term220 = term59.
Proof. exact (EQ_MP (@lem2415310) (@lem940073)). Qed.
Lemma lem2415312 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415313 : term218 = term58.
Proof. exact (MK_COMB (@lem2415312) (@lem2415311)). Qed.
Lemma lem2415314 : term217 = term58.
Proof. exact (TRANS (@lem2415309) (@lem2415313)). Qed.
Lemma lem2415315 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem2415316 : term265 = term263.
Proof. exact (MK_COMB (@lem2415315) (@lem2415314)). Qed.
Lemma lem2415318 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2415319 : term263 = term249.
Proof. exact (@lem2415318 term59). Qed.
Lemma lem2415320 : term265 = term249.
Proof. exact (TRANS (@lem2415316) (@lem2415319)). Qed.
Lemma lem2415321 : term249 = term265.
Proof. exact (SYM (@lem2415320)). Qed.
Lemma lem2415322 : term262 = term265.
Proof. exact (TRANS (@lem2415306) (@lem2415321)). Qed.
Lemma lem2415323 : term247 = term266.
Proof. exact (@lem2415273 (@lem2415322)). Qed.
Lemma lem2415324 : term246 = term266.
Proof. exact (TRANS (@lem2415239) (@lem2415323)). Qed.
Lemma lem2415326 (x : real) : (term226 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2415327 : term266 = term249.
Proof. exact (@lem2415326 term249). Qed.
Lemma lem2415328 : term246 = term249.
Proof. exact (TRANS (@lem2415324) (@lem2415327)). Qed.
Lemma lem2415329 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415330 : term267 = term261.
Proof. exact (MK_COMB (@lem2415329) (@lem2415328)). Qed.
Lemma lem2415331 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2415332 (x : int) : (term243 x) = (term268 x).
Proof. exact (MK_COMB (@lem2415330) (@lem2415331 x)). Qed.
Lemma lem2415333 (x : int) : (term242 x) = (term268 x).
Proof. exact (TRANS (@lem2415230 x) (@lem2415332 x)). Qed.
Lemma lem2415334 (x : int) : (term268 x) = term249.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2415335 (x : int) : (term242 x) = term249.
Proof. exact (TRANS (@lem2415333 x) (@lem2415334 x)). Qed.
Lemma lem2415336 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415337 (x : int) : (term269 x) = term270.
Proof. exact (MK_COMB (@lem2415336) (@lem2415335 x)). Qed.
Lemma lem2415338 : term70 = term70.
Proof. exact (eq_refl term70). Qed.
Lemma lem2415339 (x : int) : (term241 x) = term271.
Proof. exact (MK_COMB (@lem2415337 x) (@lem2415338)). Qed.
Lemma lem2415340 (x : int) : (term240 x) = term271.
Proof. exact (TRANS (@lem2415229 x) (@lem2415339 x)). Qed.
Lemma lem2415341 : term271 = term70.
Proof. exact (@lem1982721 term70). Qed.
Lemma lem2415342 (x : int) : (term240 x) = term70.
Proof. exact (TRANS (@lem2415340 x) (@lem2415341)). Qed.
Lemma lem2415343 (x : int) : (term203 x) = term70.
Proof. exact (TRANS (@lem2415228 x) (@lem2415342 x)). Qed.
Lemma lem2415344 (x : int) : (term202 x) = term70.
Proof. exact (TRANS (@lem2415141 x) (@lem2415343 x)). Qed.
Lemma lem2415345 (x : int) : (term279 x) = term70.
Proof. exact (TRANS (@lem2415140 x) (@lem2415344 x)). Qed.
Lemma lem2415346 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2415347 (x : int) : (term280 x) = term273.
Proof. exact (MK_COMB (@lem2415346) (@lem2415345 x)). Qed.
Lemma lem2415348 : term249 = term249.
Proof. exact (eq_refl term249). Qed.
Lemma lem2415349 (x : int) : (term277 x) = term274.
Proof. exact (MK_COMB (@lem2415347 x) (@lem2415348)). Qed.
Lemma lem2415350 (x : int) : (term87 x) = term274.
Proof. exact (TRANS (@lem2415117 x) (@lem2415349 x)). Qed.
Lemma lem2415351 : term138 = term275.
Proof. exact (fun_ext (fun x : int => @lem2415350 x)). Qed.
Lemma lem2415352 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2415353 : term153 = term276.
Proof. exact (MK_COMB (@lem2415352) (@lem2415351)). Qed.
Lemma lem2415354 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2415355 : term150 = term281.
Proof. exact (MK_COMB (@lem2415354) (@lem2415116)). Qed.
Lemma lem2415356 : term154 = term282.
Proof. exact (MK_COMB (@lem2415355) (@lem2415353)). Qed.
Lemma lem2415357 (x : int) (y : int) : (term108 x y) = (term283 x y).
Proof. exact (@lem1988287 (term107 x y) (term101 x y)). Qed.
Lemma lem2415358 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem2415371 (x : int) (y : int) : (term98 x y) = (term107 x y).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2415372 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415373 (x : int) (y : int) : (term100 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem2415372) (@lem2415371 x y)). Qed.
Lemma lem2415374 (x : int) (y : int) : (term101 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem2415373 x y) (@lem2415358)). Qed.
Lemma lem2415379 (x : int) (y : int) : (term118 x y) = (term284 x y).
Proof. exact (@lem1982755 (real_of_int x) (term73 y) term58). Qed.
Lemma lem2415380 (x : int) (y : int) : (term101 x y) = (term284 x y).
Proof. exact (TRANS (@lem2415374 x y) (@lem2415379 x y)). Qed.
Lemma lem2415395 (x : int) (y : int) : (term285 x y) = (term285 x y).
Proof. exact (eq_refl (term285 x y)). Qed.
Lemma lem2415396 (x : int) (y : int) : (term286 x y) = (term287 x y).
Proof. exact (MK_COMB (@lem2415395 x y) (@lem2415380 x y)). Qed.
Lemma lem2415397 (x : int) (y : int) : (term287 x y) = (term288 x y).
Proof. exact (@lem1982792 (term107 x y) (term284 x y)). Qed.
Lemma lem2415398 (x : int) (y : int) : (term289 x y) = (term290 x y).
Proof. exact (@lem1982781 (real_of_int x) term70 (term84 y)). Qed.
Lemma lem2415399 (y : int) : (term204 y) = (term205 y).
Proof. exact (@lem1982781 (term73 y) term70 term58). Qed.
Lemma lem2415401 (x : nat) : (real_of_num x) = (term206 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2415402 : term58 = term207.
Proof. exact (@lem2415401 term59). Qed.
Lemma lem2415404 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2415405 : term70 = term210.
Proof. exact (@lem2415404 term59). Qed.
Lemma lem2415406 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415407 : term72 = term211.
Proof. exact (MK_COMB (@lem2415406) (@lem2415405)). Qed.
Lemma lem2415408 : term212 = term213.
Proof. exact (MK_COMB (@lem2415407) (@lem2415402)). Qed.
Lemma lem2415409 : term213 = term214.
Proof. exact (@lem1981613 term70 term58 term58 term58). Qed.
Lemma lem2415411 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415412 : term217 = term218.
Proof. exact (@lem2415411 term59 term59). Qed.
Lemma lem2415413 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415414 : term220 = term59.
Proof. exact (EQ_MP (@lem2415413) (@lem940073)). Qed.
Lemma lem2415415 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415416 : term218 = term58.
Proof. exact (MK_COMB (@lem2415415) (@lem2415414)). Qed.
Lemma lem2415417 : term217 = term58.
Proof. exact (TRANS (@lem2415412) (@lem2415416)). Qed.
Lemma lem2415419 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2415420 : term212 = term223.
Proof. exact (@lem2415419 term59 term59). Qed.
Lemma lem2415421 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415422 : term220 = term59.
Proof. exact (EQ_MP (@lem2415421) (@lem940073)). Qed.
Lemma lem2415423 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415424 : term218 = term58.
Proof. exact (MK_COMB (@lem2415423) (@lem2415422)). Qed.
Lemma lem2415425 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2415426 : term223 = term70.
Proof. exact (MK_COMB (@lem2415425) (@lem2415424)). Qed.
Lemma lem2415427 : term212 = term70.
Proof. exact (TRANS (@lem2415420) (@lem2415426)). Qed.
Lemma lem2415428 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2415429 : term224 = term225.
Proof. exact (MK_COMB (@lem2415428) (@lem2415427)). Qed.
Lemma lem2415430 : term214 = term210.
Proof. exact (MK_COMB (@lem2415429) (@lem2415417)). Qed.
Lemma lem2415431 : term213 = term210.
Proof. exact (TRANS (@lem2415409) (@lem2415430)). Qed.
Lemma lem2415432 : term212 = term210.
Proof. exact (TRANS (@lem2415408) (@lem2415431)). Qed.
Lemma lem2415434 (x : real) : (term226 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2415435 : term210 = term70.
Proof. exact (@lem2415434 term70). Qed.
Lemma lem2415436 : term212 = term70.
Proof. exact (TRANS (@lem2415432) (@lem2415435)). Qed.
Lemma lem2415437 (y : int) : (term227 y) = (term228 y).
Proof. exact (@lem1982749 term70 term70 (real_of_int y)). Qed.
Lemma lem2415439 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2415440 : term70 = term210.
Proof. exact (@lem2415439 term59). Qed.
Lemma lem2415442 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2415443 : term70 = term210.
Proof. exact (@lem2415442 term59). Qed.
Lemma lem2415444 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415445 : term72 = term211.
Proof. exact (MK_COMB (@lem2415444) (@lem2415443)). Qed.
Lemma lem2415446 : term229 = term230.
Proof. exact (MK_COMB (@lem2415445) (@lem2415440)). Qed.
Lemma lem2415447 : term230 = term231.
Proof. exact (@lem1981613 term70 term70 term58 term58). Qed.
Lemma lem2415449 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415450 : term217 = term218.
Proof. exact (@lem2415449 term59 term59). Qed.
Lemma lem2415451 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415452 : term220 = term59.
Proof. exact (EQ_MP (@lem2415451) (@lem940073)). Qed.
Lemma lem2415453 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415454 : term218 = term58.
Proof. exact (MK_COMB (@lem2415453) (@lem2415452)). Qed.
Lemma lem2415455 : term217 = term58.
Proof. exact (TRANS (@lem2415450) (@lem2415454)). Qed.
Lemma lem2415457 (m : nat) (n : nat) : (term232 m n) = (term216 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2415458 : term229 = term218.
Proof. exact (@lem2415457 term59 term59). Qed.
Lemma lem2415459 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415460 : term220 = term59.
Proof. exact (EQ_MP (@lem2415459) (@lem940073)). Qed.
Lemma lem2415461 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415462 : term218 = term58.
Proof. exact (MK_COMB (@lem2415461) (@lem2415460)). Qed.
Lemma lem2415463 : term229 = term58.
Proof. exact (TRANS (@lem2415458) (@lem2415462)). Qed.
Lemma lem2415464 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2415465 : term233 = term234.
Proof. exact (MK_COMB (@lem2415464) (@lem2415463)). Qed.
Lemma lem2415466 : term231 = term207.
Proof. exact (MK_COMB (@lem2415465) (@lem2415455)). Qed.
Lemma lem2415467 : term230 = term207.
Proof. exact (TRANS (@lem2415447) (@lem2415466)). Qed.
Lemma lem2415468 : term229 = term207.
Proof. exact (TRANS (@lem2415446) (@lem2415467)). Qed.
Lemma lem2415470 (x : real) : (term226 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2415471 : term207 = term58.
Proof. exact (@lem2415470 term58). Qed.
Lemma lem2415472 : term229 = term58.
Proof. exact (TRANS (@lem2415468) (@lem2415471)). Qed.
Lemma lem2415473 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415474 : term235 = term236.
Proof. exact (MK_COMB (@lem2415473) (@lem2415472)). Qed.
Lemma lem2415475 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2415476 (y : int) : (term228 y) = (term237 y).
Proof. exact (MK_COMB (@lem2415474) (@lem2415475 y)). Qed.
Lemma lem2415477 (y : int) : (term227 y) = (term237 y).
Proof. exact (TRANS (@lem2415437 y) (@lem2415476 y)). Qed.
Lemma lem2415478 (y : int) : (term237 y) = (real_of_int y).
Proof. exact (@lem1982709 (real_of_int y)). Qed.
Lemma lem2415479 (y : int) : (term227 y) = (real_of_int y).
Proof. exact (TRANS (@lem2415477 y) (@lem2415478 y)). Qed.
Lemma lem2415480 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415481 (y : int) : (term238 y) = (term106 y).
Proof. exact (MK_COMB (@lem2415480) (@lem2415479 y)). Qed.
Lemma lem2415482 (y : int) : (term205 y) = (term239 y).
Proof. exact (MK_COMB (@lem2415481 y) (@lem2415436)). Qed.
Lemma lem2415483 (y : int) : (term204 y) = (term239 y).
Proof. exact (TRANS (@lem2415399 y) (@lem2415482 y)). Qed.
Lemma lem2415486 (x : int) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem2415487 (x : int) (y : int) : (term290 x y) = (term291 x y).
Proof. exact (MK_COMB (@lem2415486 x) (@lem2415483 y)). Qed.
Lemma lem2415488 (x : int) (y : int) : (term289 x y) = (term291 x y).
Proof. exact (TRANS (@lem2415398 x y) (@lem2415487 x y)). Qed.
Lemma lem2415489 (x : int) (y : int) : (term117 x y) = (term117 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem2415490 (x : int) (y : int) : (term288 x y) = (term292 x y).
Proof. exact (MK_COMB (@lem2415489 x y) (@lem2415488 x y)). Qed.
Lemma lem2415491 (x : int) (y : int) : (term292 x y) = (term293 x y).
Proof. exact (@lem1982753 (real_of_int x) (term73 x) (term73 y) (term239 y)). Qed.
Lemma lem2415492 (x : int) : (term294 x) = (term243 x).
Proof. exact (@lem1982715 term70 (real_of_int x)). Qed.
Lemma lem2415494 (x : nat) : (real_of_num x) = (term206 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2415495 : term58 = term207.
Proof. exact (@lem2415494 term59). Qed.
Lemma lem2415497 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2415498 : term70 = term210.
Proof. exact (@lem2415497 term59). Qed.
Lemma lem2415499 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415500 : term244 = term245.
Proof. exact (MK_COMB (@lem2415499) (@lem2415498)). Qed.
Lemma lem2415501 : term246 = term247.
Proof. exact (MK_COMB (@lem2415500) (@lem2415495)). Qed.
Lemma lem2415502 : term248.
Proof. exact (@lem1981473 term70 term58 term58 term58 term249 term58). Qed.
Lemma lem2415504 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415505 : term251 = term252.
Proof. exact (@lem2415504 (NUMERAL 0) term59). Qed.
Lemma lem2415506 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415507 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415508 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415507 h1) (fun h1 : term252 = True => @lem2415506)). Qed.
Lemma lem2415509 : term252 = True.
Proof. exact (EQ_MP (@lem2415508) (@lem2415506)). Qed.
Lemma lem2415510 : term251 = True.
Proof. exact (TRANS (@lem2415505) (@lem2415509)). Qed.
Lemma lem2415511 : True = term251.
Proof. exact (SYM (@lem2415510)). Qed.
Lemma lem2415512 : term251.
Proof. exact (EQ_MP (@lem2415511) (@lem0)). Qed.
Lemma lem2415513 : term254.
Proof. exact (@lem2415502 (@lem2415512)). Qed.
Lemma lem2415515 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415516 : term251 = term252.
Proof. exact (@lem2415515 (NUMERAL 0) term59). Qed.
Lemma lem2415517 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415518 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415519 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415518 h1) (fun h1 : term252 = True => @lem2415517)). Qed.
Lemma lem2415520 : term252 = True.
Proof. exact (EQ_MP (@lem2415519) (@lem2415517)). Qed.
Lemma lem2415521 : term251 = True.
Proof. exact (TRANS (@lem2415516) (@lem2415520)). Qed.
Lemma lem2415522 : True = term251.
Proof. exact (SYM (@lem2415521)). Qed.
Lemma lem2415523 : term251.
Proof. exact (EQ_MP (@lem2415522) (@lem0)). Qed.
Lemma lem2415524 : term255.
Proof. exact (@lem2415513 (@lem2415523)). Qed.
Lemma lem2415526 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415527 : term251 = term252.
Proof. exact (@lem2415526 (NUMERAL 0) term59). Qed.
Lemma lem2415528 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415529 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415530 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415529 h1) (fun h1 : term252 = True => @lem2415528)). Qed.
Lemma lem2415531 : term252 = True.
Proof. exact (EQ_MP (@lem2415530) (@lem2415528)). Qed.
Lemma lem2415532 : term251 = True.
Proof. exact (TRANS (@lem2415527) (@lem2415531)). Qed.
Lemma lem2415533 : True = term251.
Proof. exact (SYM (@lem2415532)). Qed.
Lemma lem2415534 : term251.
Proof. exact (EQ_MP (@lem2415533) (@lem0)). Qed.
Lemma lem2415535 : term256.
Proof. exact (@lem2415524 (@lem2415534)). Qed.
Lemma lem2415537 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415538 : term217 = term218.
Proof. exact (@lem2415537 term59 term59). Qed.
Lemma lem2415539 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415540 : term220 = term59.
Proof. exact (EQ_MP (@lem2415539) (@lem940073)). Qed.
Lemma lem2415541 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415542 : term218 = term58.
Proof. exact (MK_COMB (@lem2415541) (@lem2415540)). Qed.
Lemma lem2415543 : term217 = term58.
Proof. exact (TRANS (@lem2415538) (@lem2415542)). Qed.
Lemma lem2415545 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2415546 : term212 = term223.
Proof. exact (@lem2415545 term59 term59). Qed.
Lemma lem2415547 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415548 : term220 = term59.
Proof. exact (EQ_MP (@lem2415547) (@lem940073)). Qed.
Lemma lem2415549 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415550 : term218 = term58.
Proof. exact (MK_COMB (@lem2415549) (@lem2415548)). Qed.
Lemma lem2415551 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2415552 : term223 = term70.
Proof. exact (MK_COMB (@lem2415551) (@lem2415550)). Qed.
Lemma lem2415553 : term212 = term70.
Proof. exact (TRANS (@lem2415546) (@lem2415552)). Qed.
Lemma lem2415554 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415555 : term257 = term244.
Proof. exact (MK_COMB (@lem2415554) (@lem2415553)). Qed.
Lemma lem2415556 : term258 = term246.
Proof. exact (MK_COMB (@lem2415555) (@lem2415543)). Qed.
Lemma lem2415558 (m : nat) : (term259 m) = term249.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2415559 : term246 = term249.
Proof. exact (@lem2415558 term59). Qed.
Lemma lem2415560 : term258 = term249.
Proof. exact (TRANS (@lem2415556) (@lem2415559)). Qed.
Lemma lem2415561 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415562 : term260 = term261.
Proof. exact (MK_COMB (@lem2415561) (@lem2415560)). Qed.
Lemma lem2415563 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem2415564 : term262 = term263.
Proof. exact (MK_COMB (@lem2415562) (@lem2415563)). Qed.
Lemma lem2415566 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2415567 : term263 = term249.
Proof. exact (@lem2415566 term59). Qed.
Lemma lem2415568 : term262 = term249.
Proof. exact (TRANS (@lem2415564) (@lem2415567)). Qed.
Lemma lem2415570 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415571 : term217 = term218.
Proof. exact (@lem2415570 term59 term59). Qed.
Lemma lem2415572 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415573 : term220 = term59.
Proof. exact (EQ_MP (@lem2415572) (@lem940073)). Qed.
Lemma lem2415574 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415575 : term218 = term58.
Proof. exact (MK_COMB (@lem2415574) (@lem2415573)). Qed.
Lemma lem2415576 : term217 = term58.
Proof. exact (TRANS (@lem2415571) (@lem2415575)). Qed.
Lemma lem2415577 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem2415578 : term265 = term263.
Proof. exact (MK_COMB (@lem2415577) (@lem2415576)). Qed.
Lemma lem2415580 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2415581 : term263 = term249.
Proof. exact (@lem2415580 term59). Qed.
Lemma lem2415582 : term265 = term249.
Proof. exact (TRANS (@lem2415578) (@lem2415581)). Qed.
Lemma lem2415583 : term249 = term265.
Proof. exact (SYM (@lem2415582)). Qed.
Lemma lem2415584 : term262 = term265.
Proof. exact (TRANS (@lem2415568) (@lem2415583)). Qed.
Lemma lem2415585 : term247 = term266.
Proof. exact (@lem2415535 (@lem2415584)). Qed.
Lemma lem2415586 : term246 = term266.
Proof. exact (TRANS (@lem2415501) (@lem2415585)). Qed.
Lemma lem2415588 (x : real) : (term226 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2415589 : term266 = term249.
Proof. exact (@lem2415588 term249). Qed.
Lemma lem2415590 : term246 = term249.
Proof. exact (TRANS (@lem2415586) (@lem2415589)). Qed.
Lemma lem2415591 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415592 : term267 = term261.
Proof. exact (MK_COMB (@lem2415591) (@lem2415590)). Qed.
Lemma lem2415593 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2415594 (x : int) : (term243 x) = (term268 x).
Proof. exact (MK_COMB (@lem2415592) (@lem2415593 x)). Qed.
Lemma lem2415595 (x : int) : (term294 x) = (term268 x).
Proof. exact (TRANS (@lem2415492 x) (@lem2415594 x)). Qed.
Lemma lem2415596 (x : int) : (term268 x) = term249.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2415597 (x : int) : (term294 x) = term249.
Proof. exact (TRANS (@lem2415595 x) (@lem2415596 x)). Qed.
Lemma lem2415598 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415599 (x : int) : (term295 x) = term270.
Proof. exact (MK_COMB (@lem2415598) (@lem2415597 x)). Qed.
Lemma lem2415600 (y : int) : (term240 y) = (term241 y).
Proof. exact (@lem1982763 (term73 y) (real_of_int y) term70). Qed.
Lemma lem2415601 (y : int) : (term242 y) = (term243 y).
Proof. exact (@lem1982713 term70 (real_of_int y)). Qed.
Lemma lem2415603 (x : nat) : (real_of_num x) = (term206 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2415604 : term58 = term207.
Proof. exact (@lem2415603 term59). Qed.
Lemma lem2415606 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2415607 : term70 = term210.
Proof. exact (@lem2415606 term59). Qed.
Lemma lem2415608 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415609 : term244 = term245.
Proof. exact (MK_COMB (@lem2415608) (@lem2415607)). Qed.
Lemma lem2415610 : term246 = term247.
Proof. exact (MK_COMB (@lem2415609) (@lem2415604)). Qed.
Lemma lem2415611 : term248.
Proof. exact (@lem1981473 term70 term58 term58 term58 term249 term58). Qed.
Lemma lem2415613 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415614 : term251 = term252.
Proof. exact (@lem2415613 (NUMERAL 0) term59). Qed.
Lemma lem2415615 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415616 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415617 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415616 h1) (fun h1 : term252 = True => @lem2415615)). Qed.
Lemma lem2415618 : term252 = True.
Proof. exact (EQ_MP (@lem2415617) (@lem2415615)). Qed.
Lemma lem2415619 : term251 = True.
Proof. exact (TRANS (@lem2415614) (@lem2415618)). Qed.
Lemma lem2415620 : True = term251.
Proof. exact (SYM (@lem2415619)). Qed.
Lemma lem2415621 : term251.
Proof. exact (EQ_MP (@lem2415620) (@lem0)). Qed.
Lemma lem2415622 : term254.
Proof. exact (@lem2415611 (@lem2415621)). Qed.
Lemma lem2415624 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415625 : term251 = term252.
Proof. exact (@lem2415624 (NUMERAL 0) term59). Qed.
Lemma lem2415626 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415627 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415628 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415627 h1) (fun h1 : term252 = True => @lem2415626)). Qed.
Lemma lem2415629 : term252 = True.
Proof. exact (EQ_MP (@lem2415628) (@lem2415626)). Qed.
Lemma lem2415630 : term251 = True.
Proof. exact (TRANS (@lem2415625) (@lem2415629)). Qed.
Lemma lem2415631 : True = term251.
Proof. exact (SYM (@lem2415630)). Qed.
Lemma lem2415632 : term251.
Proof. exact (EQ_MP (@lem2415631) (@lem0)). Qed.
Lemma lem2415633 : term255.
Proof. exact (@lem2415622 (@lem2415632)). Qed.
Lemma lem2415635 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415636 : term251 = term252.
Proof. exact (@lem2415635 (NUMERAL 0) term59). Qed.
Lemma lem2415637 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415638 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415639 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415638 h1) (fun h1 : term252 = True => @lem2415637)). Qed.
Lemma lem2415640 : term252 = True.
Proof. exact (EQ_MP (@lem2415639) (@lem2415637)). Qed.
Lemma lem2415641 : term251 = True.
Proof. exact (TRANS (@lem2415636) (@lem2415640)). Qed.
Lemma lem2415642 : True = term251.
Proof. exact (SYM (@lem2415641)). Qed.
Lemma lem2415643 : term251.
Proof. exact (EQ_MP (@lem2415642) (@lem0)). Qed.
Lemma lem2415644 : term256.
Proof. exact (@lem2415633 (@lem2415643)). Qed.
Lemma lem2415646 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415647 : term217 = term218.
Proof. exact (@lem2415646 term59 term59). Qed.
Lemma lem2415648 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415649 : term220 = term59.
Proof. exact (EQ_MP (@lem2415648) (@lem940073)). Qed.
Lemma lem2415650 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415651 : term218 = term58.
Proof. exact (MK_COMB (@lem2415650) (@lem2415649)). Qed.
Lemma lem2415652 : term217 = term58.
Proof. exact (TRANS (@lem2415647) (@lem2415651)). Qed.
Lemma lem2415654 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2415655 : term212 = term223.
Proof. exact (@lem2415654 term59 term59). Qed.
Lemma lem2415656 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415657 : term220 = term59.
Proof. exact (EQ_MP (@lem2415656) (@lem940073)). Qed.
Lemma lem2415658 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415659 : term218 = term58.
Proof. exact (MK_COMB (@lem2415658) (@lem2415657)). Qed.
Lemma lem2415660 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2415661 : term223 = term70.
Proof. exact (MK_COMB (@lem2415660) (@lem2415659)). Qed.
Lemma lem2415662 : term212 = term70.
Proof. exact (TRANS (@lem2415655) (@lem2415661)). Qed.
Lemma lem2415663 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415664 : term257 = term244.
Proof. exact (MK_COMB (@lem2415663) (@lem2415662)). Qed.
Lemma lem2415665 : term258 = term246.
Proof. exact (MK_COMB (@lem2415664) (@lem2415652)). Qed.
Lemma lem2415667 (m : nat) : (term259 m) = term249.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2415668 : term246 = term249.
Proof. exact (@lem2415667 term59). Qed.
Lemma lem2415669 : term258 = term249.
Proof. exact (TRANS (@lem2415665) (@lem2415668)). Qed.
Lemma lem2415670 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415671 : term260 = term261.
Proof. exact (MK_COMB (@lem2415670) (@lem2415669)). Qed.
Lemma lem2415672 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem2415673 : term262 = term263.
Proof. exact (MK_COMB (@lem2415671) (@lem2415672)). Qed.
Lemma lem2415675 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2415676 : term263 = term249.
Proof. exact (@lem2415675 term59). Qed.
Lemma lem2415677 : term262 = term249.
Proof. exact (TRANS (@lem2415673) (@lem2415676)). Qed.
Lemma lem2415679 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415680 : term217 = term218.
Proof. exact (@lem2415679 term59 term59). Qed.
Lemma lem2415681 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415682 : term220 = term59.
Proof. exact (EQ_MP (@lem2415681) (@lem940073)). Qed.
Lemma lem2415683 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415684 : term218 = term58.
Proof. exact (MK_COMB (@lem2415683) (@lem2415682)). Qed.
Lemma lem2415685 : term217 = term58.
Proof. exact (TRANS (@lem2415680) (@lem2415684)). Qed.
Lemma lem2415686 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem2415687 : term265 = term263.
Proof. exact (MK_COMB (@lem2415686) (@lem2415685)). Qed.
Lemma lem2415689 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2415690 : term263 = term249.
Proof. exact (@lem2415689 term59). Qed.
Lemma lem2415691 : term265 = term249.
Proof. exact (TRANS (@lem2415687) (@lem2415690)). Qed.
Lemma lem2415692 : term249 = term265.
Proof. exact (SYM (@lem2415691)). Qed.
Lemma lem2415693 : term262 = term265.
Proof. exact (TRANS (@lem2415677) (@lem2415692)). Qed.
Lemma lem2415694 : term247 = term266.
Proof. exact (@lem2415644 (@lem2415693)). Qed.
Lemma lem2415695 : term246 = term266.
Proof. exact (TRANS (@lem2415610) (@lem2415694)). Qed.
Lemma lem2415697 (x : real) : (term226 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2415698 : term266 = term249.
Proof. exact (@lem2415697 term249). Qed.
Lemma lem2415699 : term246 = term249.
Proof. exact (TRANS (@lem2415695) (@lem2415698)). Qed.
Lemma lem2415700 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415701 : term267 = term261.
Proof. exact (MK_COMB (@lem2415700) (@lem2415699)). Qed.
Lemma lem2415702 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2415703 (y : int) : (term243 y) = (term268 y).
Proof. exact (MK_COMB (@lem2415701) (@lem2415702 y)). Qed.
Lemma lem2415704 (y : int) : (term242 y) = (term268 y).
Proof. exact (TRANS (@lem2415601 y) (@lem2415703 y)). Qed.
Lemma lem2415705 (y : int) : (term268 y) = term249.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2415706 (y : int) : (term242 y) = term249.
Proof. exact (TRANS (@lem2415704 y) (@lem2415705 y)). Qed.
Lemma lem2415707 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415708 (y : int) : (term269 y) = term270.
Proof. exact (MK_COMB (@lem2415707) (@lem2415706 y)). Qed.
Lemma lem2415709 : term70 = term70.
Proof. exact (eq_refl term70). Qed.
Lemma lem2415710 (y : int) : (term241 y) = term271.
Proof. exact (MK_COMB (@lem2415708 y) (@lem2415709)). Qed.
Lemma lem2415711 (y : int) : (term240 y) = term271.
Proof. exact (TRANS (@lem2415600 y) (@lem2415710 y)). Qed.
Lemma lem2415712 : term271 = term70.
Proof. exact (@lem1982721 term70). Qed.
Lemma lem2415713 (y : int) : (term240 y) = term70.
Proof. exact (TRANS (@lem2415711 y) (@lem2415712)). Qed.
Lemma lem2415714 (x : int) (y : int) : (term293 x y) = term271.
Proof. exact (MK_COMB (@lem2415599 x) (@lem2415713 y)). Qed.
Lemma lem2415715 (x : int) (y : int) : (term292 x y) = term271.
Proof. exact (TRANS (@lem2415491 x y) (@lem2415714 x y)). Qed.
Lemma lem2415716 : term271 = term70.
Proof. exact (@lem1982721 term70). Qed.
Lemma lem2415717 (x : int) (y : int) : (term292 x y) = term70.
Proof. exact (TRANS (@lem2415715 x y) (@lem2415716)). Qed.
Lemma lem2415718 (x : int) (y : int) : (term288 x y) = term70.
Proof. exact (TRANS (@lem2415490 x y) (@lem2415717 x y)). Qed.
Lemma lem2415719 (x : int) (y : int) : (term287 x y) = term70.
Proof. exact (TRANS (@lem2415397 x y) (@lem2415718 x y)). Qed.
Lemma lem2415720 (x : int) (y : int) : (term286 x y) = term70.
Proof. exact (TRANS (@lem2415396 x y) (@lem2415719 x y)). Qed.
Lemma lem2415721 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2415722 (x : int) (y : int) : (term296 x y) = term273.
Proof. exact (MK_COMB (@lem2415721) (@lem2415720 x y)). Qed.
Lemma lem2415723 : term249 = term249.
Proof. exact (eq_refl term249). Qed.
Lemma lem2415724 (x : int) (y : int) : (term283 x y) = term274.
Proof. exact (MK_COMB (@lem2415722 x y) (@lem2415723)). Qed.
Lemma lem2415725 (x : int) (y : int) : (term108 x y) = term274.
Proof. exact (TRANS (@lem2415357 x y) (@lem2415724 x y)). Qed.
Lemma lem2415726 (x : int) : (term158 x) = term275.
Proof. exact (fun_ext (fun y : int => @lem2415725 x y)). Qed.
Lemma lem2415727 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2415728 (x : int) : (term169 x) = term276.
Proof. exact (MK_COMB (@lem2415727) (@lem2415726 x)). Qed.
Lemma lem2415729 : term180 = term297.
Proof. exact (fun_ext (fun x : int => @lem2415728 x)). Qed.
Lemma lem2415730 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2415731 : term191 = term298.
Proof. exact (MK_COMB (@lem2415730) (@lem2415729)). Qed.
Lemma lem2415732 (x : int) (y : int) : (term121 x y) = (term299 x y).
Proof. exact (@lem1988287 (term98 x y) (term118 x y)). Qed.
Lemma lem2415755 (x : int) (y : int) : (term118 x y) = (term284 x y).
Proof. exact (@lem1982755 (real_of_int x) (term73 y) term58). Qed.
Lemma lem2415768 (x : int) (y : int) : (term98 x y) = (term107 x y).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2415769 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2415770 (x : int) (y : int) : (term300 x y) = (term285 x y).
Proof. exact (MK_COMB (@lem2415769) (@lem2415768 x y)). Qed.
Lemma lem2415771 (x : int) (y : int) : (term301 x y) = (term287 x y).
Proof. exact (MK_COMB (@lem2415770 x y) (@lem2415755 x y)). Qed.
Lemma lem2415772 (x : int) (y : int) : (term287 x y) = (term288 x y).
Proof. exact (@lem1982792 (term107 x y) (term284 x y)). Qed.
Lemma lem2415773 (x : int) (y : int) : (term289 x y) = (term290 x y).
Proof. exact (@lem1982781 (real_of_int x) term70 (term84 y)). Qed.
Lemma lem2415774 (y : int) : (term204 y) = (term205 y).
Proof. exact (@lem1982781 (term73 y) term70 term58). Qed.
Lemma lem2415776 (x : nat) : (real_of_num x) = (term206 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2415777 : term58 = term207.
Proof. exact (@lem2415776 term59). Qed.
Lemma lem2415779 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2415780 : term70 = term210.
Proof. exact (@lem2415779 term59). Qed.
Lemma lem2415781 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415782 : term72 = term211.
Proof. exact (MK_COMB (@lem2415781) (@lem2415780)). Qed.
Lemma lem2415783 : term212 = term213.
Proof. exact (MK_COMB (@lem2415782) (@lem2415777)). Qed.
Lemma lem2415784 : term213 = term214.
Proof. exact (@lem1981613 term70 term58 term58 term58). Qed.
Lemma lem2415786 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415787 : term217 = term218.
Proof. exact (@lem2415786 term59 term59). Qed.
Lemma lem2415788 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415789 : term220 = term59.
Proof. exact (EQ_MP (@lem2415788) (@lem940073)). Qed.
Lemma lem2415790 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415791 : term218 = term58.
Proof. exact (MK_COMB (@lem2415790) (@lem2415789)). Qed.
Lemma lem2415792 : term217 = term58.
Proof. exact (TRANS (@lem2415787) (@lem2415791)). Qed.
Lemma lem2415794 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2415795 : term212 = term223.
Proof. exact (@lem2415794 term59 term59). Qed.
Lemma lem2415796 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415797 : term220 = term59.
Proof. exact (EQ_MP (@lem2415796) (@lem940073)). Qed.
Lemma lem2415798 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415799 : term218 = term58.
Proof. exact (MK_COMB (@lem2415798) (@lem2415797)). Qed.
Lemma lem2415800 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2415801 : term223 = term70.
Proof. exact (MK_COMB (@lem2415800) (@lem2415799)). Qed.
Lemma lem2415802 : term212 = term70.
Proof. exact (TRANS (@lem2415795) (@lem2415801)). Qed.
Lemma lem2415803 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2415804 : term224 = term225.
Proof. exact (MK_COMB (@lem2415803) (@lem2415802)). Qed.
Lemma lem2415805 : term214 = term210.
Proof. exact (MK_COMB (@lem2415804) (@lem2415792)). Qed.
Lemma lem2415806 : term213 = term210.
Proof. exact (TRANS (@lem2415784) (@lem2415805)). Qed.
Lemma lem2415807 : term212 = term210.
Proof. exact (TRANS (@lem2415783) (@lem2415806)). Qed.
Lemma lem2415809 (x : real) : (term226 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2415810 : term210 = term70.
Proof. exact (@lem2415809 term70). Qed.
Lemma lem2415811 : term212 = term70.
Proof. exact (TRANS (@lem2415807) (@lem2415810)). Qed.
Lemma lem2415812 (y : int) : (term227 y) = (term228 y).
Proof. exact (@lem1982749 term70 term70 (real_of_int y)). Qed.
Lemma lem2415814 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2415815 : term70 = term210.
Proof. exact (@lem2415814 term59). Qed.
Lemma lem2415817 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2415818 : term70 = term210.
Proof. exact (@lem2415817 term59). Qed.
Lemma lem2415819 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415820 : term72 = term211.
Proof. exact (MK_COMB (@lem2415819) (@lem2415818)). Qed.
Lemma lem2415821 : term229 = term230.
Proof. exact (MK_COMB (@lem2415820) (@lem2415815)). Qed.
Lemma lem2415822 : term230 = term231.
Proof. exact (@lem1981613 term70 term70 term58 term58). Qed.
Lemma lem2415824 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415825 : term217 = term218.
Proof. exact (@lem2415824 term59 term59). Qed.
Lemma lem2415826 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415827 : term220 = term59.
Proof. exact (EQ_MP (@lem2415826) (@lem940073)). Qed.
Lemma lem2415828 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415829 : term218 = term58.
Proof. exact (MK_COMB (@lem2415828) (@lem2415827)). Qed.
Lemma lem2415830 : term217 = term58.
Proof. exact (TRANS (@lem2415825) (@lem2415829)). Qed.
Lemma lem2415832 (m : nat) (n : nat) : (term232 m n) = (term216 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2415833 : term229 = term218.
Proof. exact (@lem2415832 term59 term59). Qed.
Lemma lem2415834 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415835 : term220 = term59.
Proof. exact (EQ_MP (@lem2415834) (@lem940073)). Qed.
Lemma lem2415836 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415837 : term218 = term58.
Proof. exact (MK_COMB (@lem2415836) (@lem2415835)). Qed.
Lemma lem2415838 : term229 = term58.
Proof. exact (TRANS (@lem2415833) (@lem2415837)). Qed.
Lemma lem2415839 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2415840 : term233 = term234.
Proof. exact (MK_COMB (@lem2415839) (@lem2415838)). Qed.
Lemma lem2415841 : term231 = term207.
Proof. exact (MK_COMB (@lem2415840) (@lem2415830)). Qed.
Lemma lem2415842 : term230 = term207.
Proof. exact (TRANS (@lem2415822) (@lem2415841)). Qed.
Lemma lem2415843 : term229 = term207.
Proof. exact (TRANS (@lem2415821) (@lem2415842)). Qed.
Lemma lem2415845 (x : real) : (term226 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2415846 : term207 = term58.
Proof. exact (@lem2415845 term58). Qed.
Lemma lem2415847 : term229 = term58.
Proof. exact (TRANS (@lem2415843) (@lem2415846)). Qed.
Lemma lem2415848 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415849 : term235 = term236.
Proof. exact (MK_COMB (@lem2415848) (@lem2415847)). Qed.
Lemma lem2415850 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2415851 (y : int) : (term228 y) = (term237 y).
Proof. exact (MK_COMB (@lem2415849) (@lem2415850 y)). Qed.
Lemma lem2415852 (y : int) : (term227 y) = (term237 y).
Proof. exact (TRANS (@lem2415812 y) (@lem2415851 y)). Qed.
Lemma lem2415853 (y : int) : (term237 y) = (real_of_int y).
Proof. exact (@lem1982709 (real_of_int y)). Qed.
Lemma lem2415854 (y : int) : (term227 y) = (real_of_int y).
Proof. exact (TRANS (@lem2415852 y) (@lem2415853 y)). Qed.
Lemma lem2415855 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415856 (y : int) : (term238 y) = (term106 y).
Proof. exact (MK_COMB (@lem2415855) (@lem2415854 y)). Qed.
Lemma lem2415857 (y : int) : (term205 y) = (term239 y).
Proof. exact (MK_COMB (@lem2415856 y) (@lem2415811)). Qed.
Lemma lem2415858 (y : int) : (term204 y) = (term239 y).
Proof. exact (TRANS (@lem2415774 y) (@lem2415857 y)). Qed.
Lemma lem2415861 (x : int) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem2415862 (x : int) (y : int) : (term290 x y) = (term291 x y).
Proof. exact (MK_COMB (@lem2415861 x) (@lem2415858 y)). Qed.
Lemma lem2415863 (x : int) (y : int) : (term289 x y) = (term291 x y).
Proof. exact (TRANS (@lem2415773 x y) (@lem2415862 x y)). Qed.
Lemma lem2415864 (x : int) (y : int) : (term117 x y) = (term117 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem2415865 (x : int) (y : int) : (term288 x y) = (term292 x y).
Proof. exact (MK_COMB (@lem2415864 x y) (@lem2415863 x y)). Qed.
Lemma lem2415866 (x : int) (y : int) : (term292 x y) = (term293 x y).
Proof. exact (@lem1982753 (real_of_int x) (term73 x) (term73 y) (term239 y)). Qed.
Lemma lem2415867 (x : int) : (term294 x) = (term243 x).
Proof. exact (@lem1982715 term70 (real_of_int x)). Qed.
Lemma lem2415869 (x : nat) : (real_of_num x) = (term206 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2415870 : term58 = term207.
Proof. exact (@lem2415869 term59). Qed.
Lemma lem2415872 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2415873 : term70 = term210.
Proof. exact (@lem2415872 term59). Qed.
Lemma lem2415874 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415875 : term244 = term245.
Proof. exact (MK_COMB (@lem2415874) (@lem2415873)). Qed.
Lemma lem2415876 : term246 = term247.
Proof. exact (MK_COMB (@lem2415875) (@lem2415870)). Qed.
Lemma lem2415877 : term248.
Proof. exact (@lem1981473 term70 term58 term58 term58 term249 term58). Qed.
Lemma lem2415879 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415880 : term251 = term252.
Proof. exact (@lem2415879 (NUMERAL 0) term59). Qed.
Lemma lem2415881 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415882 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415883 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415882 h1) (fun h1 : term252 = True => @lem2415881)). Qed.
Lemma lem2415884 : term252 = True.
Proof. exact (EQ_MP (@lem2415883) (@lem2415881)). Qed.
Lemma lem2415885 : term251 = True.
Proof. exact (TRANS (@lem2415880) (@lem2415884)). Qed.
Lemma lem2415886 : True = term251.
Proof. exact (SYM (@lem2415885)). Qed.
Lemma lem2415887 : term251.
Proof. exact (EQ_MP (@lem2415886) (@lem0)). Qed.
Lemma lem2415888 : term254.
Proof. exact (@lem2415877 (@lem2415887)). Qed.
Lemma lem2415890 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415891 : term251 = term252.
Proof. exact (@lem2415890 (NUMERAL 0) term59). Qed.
Lemma lem2415892 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415893 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415894 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415893 h1) (fun h1 : term252 = True => @lem2415892)). Qed.
Lemma lem2415895 : term252 = True.
Proof. exact (EQ_MP (@lem2415894) (@lem2415892)). Qed.
Lemma lem2415896 : term251 = True.
Proof. exact (TRANS (@lem2415891) (@lem2415895)). Qed.
Lemma lem2415897 : True = term251.
Proof. exact (SYM (@lem2415896)). Qed.
Lemma lem2415898 : term251.
Proof. exact (EQ_MP (@lem2415897) (@lem0)). Qed.
Lemma lem2415899 : term255.
Proof. exact (@lem2415888 (@lem2415898)). Qed.
Lemma lem2415901 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415902 : term251 = term252.
Proof. exact (@lem2415901 (NUMERAL 0) term59). Qed.
Lemma lem2415903 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415904 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415905 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415904 h1) (fun h1 : term252 = True => @lem2415903)). Qed.
Lemma lem2415906 : term252 = True.
Proof. exact (EQ_MP (@lem2415905) (@lem2415903)). Qed.
Lemma lem2415907 : term251 = True.
Proof. exact (TRANS (@lem2415902) (@lem2415906)). Qed.
Lemma lem2415908 : True = term251.
Proof. exact (SYM (@lem2415907)). Qed.
Lemma lem2415909 : term251.
Proof. exact (EQ_MP (@lem2415908) (@lem0)). Qed.
Lemma lem2415910 : term256.
Proof. exact (@lem2415899 (@lem2415909)). Qed.
Lemma lem2415912 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415913 : term217 = term218.
Proof. exact (@lem2415912 term59 term59). Qed.
Lemma lem2415914 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415915 : term220 = term59.
Proof. exact (EQ_MP (@lem2415914) (@lem940073)). Qed.
Lemma lem2415916 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415917 : term218 = term58.
Proof. exact (MK_COMB (@lem2415916) (@lem2415915)). Qed.
Lemma lem2415918 : term217 = term58.
Proof. exact (TRANS (@lem2415913) (@lem2415917)). Qed.
Lemma lem2415920 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2415921 : term212 = term223.
Proof. exact (@lem2415920 term59 term59). Qed.
Lemma lem2415922 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415923 : term220 = term59.
Proof. exact (EQ_MP (@lem2415922) (@lem940073)). Qed.
Lemma lem2415924 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415925 : term218 = term58.
Proof. exact (MK_COMB (@lem2415924) (@lem2415923)). Qed.
Lemma lem2415926 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2415927 : term223 = term70.
Proof. exact (MK_COMB (@lem2415926) (@lem2415925)). Qed.
Lemma lem2415928 : term212 = term70.
Proof. exact (TRANS (@lem2415921) (@lem2415927)). Qed.
Lemma lem2415929 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415930 : term257 = term244.
Proof. exact (MK_COMB (@lem2415929) (@lem2415928)). Qed.
Lemma lem2415931 : term258 = term246.
Proof. exact (MK_COMB (@lem2415930) (@lem2415918)). Qed.
Lemma lem2415933 (m : nat) : (term259 m) = term249.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2415934 : term246 = term249.
Proof. exact (@lem2415933 term59). Qed.
Lemma lem2415935 : term258 = term249.
Proof. exact (TRANS (@lem2415931) (@lem2415934)). Qed.
Lemma lem2415936 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415937 : term260 = term261.
Proof. exact (MK_COMB (@lem2415936) (@lem2415935)). Qed.
Lemma lem2415938 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem2415939 : term262 = term263.
Proof. exact (MK_COMB (@lem2415937) (@lem2415938)). Qed.
Lemma lem2415941 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2415942 : term263 = term249.
Proof. exact (@lem2415941 term59). Qed.
Lemma lem2415943 : term262 = term249.
Proof. exact (TRANS (@lem2415939) (@lem2415942)). Qed.
Lemma lem2415945 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2415946 : term217 = term218.
Proof. exact (@lem2415945 term59 term59). Qed.
Lemma lem2415947 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2415948 : term220 = term59.
Proof. exact (EQ_MP (@lem2415947) (@lem940073)). Qed.
Lemma lem2415949 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2415950 : term218 = term58.
Proof. exact (MK_COMB (@lem2415949) (@lem2415948)). Qed.
Lemma lem2415951 : term217 = term58.
Proof. exact (TRANS (@lem2415946) (@lem2415950)). Qed.
Lemma lem2415952 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem2415953 : term265 = term263.
Proof. exact (MK_COMB (@lem2415952) (@lem2415951)). Qed.
Lemma lem2415955 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2415956 : term263 = term249.
Proof. exact (@lem2415955 term59). Qed.
Lemma lem2415957 : term265 = term249.
Proof. exact (TRANS (@lem2415953) (@lem2415956)). Qed.
Lemma lem2415958 : term249 = term265.
Proof. exact (SYM (@lem2415957)). Qed.
Lemma lem2415959 : term262 = term265.
Proof. exact (TRANS (@lem2415943) (@lem2415958)). Qed.
Lemma lem2415960 : term247 = term266.
Proof. exact (@lem2415910 (@lem2415959)). Qed.
Lemma lem2415961 : term246 = term266.
Proof. exact (TRANS (@lem2415876) (@lem2415960)). Qed.
Lemma lem2415963 (x : real) : (term226 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2415964 : term266 = term249.
Proof. exact (@lem2415963 term249). Qed.
Lemma lem2415965 : term246 = term249.
Proof. exact (TRANS (@lem2415961) (@lem2415964)). Qed.
Lemma lem2415966 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2415967 : term267 = term261.
Proof. exact (MK_COMB (@lem2415966) (@lem2415965)). Qed.
Lemma lem2415968 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2415969 (x : int) : (term243 x) = (term268 x).
Proof. exact (MK_COMB (@lem2415967) (@lem2415968 x)). Qed.
Lemma lem2415970 (x : int) : (term294 x) = (term268 x).
Proof. exact (TRANS (@lem2415867 x) (@lem2415969 x)). Qed.
Lemma lem2415971 (x : int) : (term268 x) = term249.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2415972 (x : int) : (term294 x) = term249.
Proof. exact (TRANS (@lem2415970 x) (@lem2415971 x)). Qed.
Lemma lem2415973 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415974 (x : int) : (term295 x) = term270.
Proof. exact (MK_COMB (@lem2415973) (@lem2415972 x)). Qed.
Lemma lem2415975 (y : int) : (term240 y) = (term241 y).
Proof. exact (@lem1982763 (term73 y) (real_of_int y) term70). Qed.
Lemma lem2415976 (y : int) : (term242 y) = (term243 y).
Proof. exact (@lem1982713 term70 (real_of_int y)). Qed.
Lemma lem2415978 (x : nat) : (real_of_num x) = (term206 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2415979 : term58 = term207.
Proof. exact (@lem2415978 term59). Qed.
Lemma lem2415981 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2415982 : term70 = term210.
Proof. exact (@lem2415981 term59). Qed.
Lemma lem2415983 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2415984 : term244 = term245.
Proof. exact (MK_COMB (@lem2415983) (@lem2415982)). Qed.
Lemma lem2415985 : term246 = term247.
Proof. exact (MK_COMB (@lem2415984) (@lem2415979)). Qed.
Lemma lem2415986 : term248.
Proof. exact (@lem1981473 term70 term58 term58 term58 term249 term58). Qed.
Lemma lem2415988 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2415989 : term251 = term252.
Proof. exact (@lem2415988 (NUMERAL 0) term59). Qed.
Lemma lem2415990 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2415991 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2415992 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2415991 h1) (fun h1 : term252 = True => @lem2415990)). Qed.
Lemma lem2415993 : term252 = True.
Proof. exact (EQ_MP (@lem2415992) (@lem2415990)). Qed.
Lemma lem2415994 : term251 = True.
Proof. exact (TRANS (@lem2415989) (@lem2415993)). Qed.
Lemma lem2415995 : True = term251.
Proof. exact (SYM (@lem2415994)). Qed.
Lemma lem2415996 : term251.
Proof. exact (EQ_MP (@lem2415995) (@lem0)). Qed.
Lemma lem2415997 : term254.
Proof. exact (@lem2415986 (@lem2415996)). Qed.
Lemma lem2415999 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2416000 : term251 = term252.
Proof. exact (@lem2415999 (NUMERAL 0) term59). Qed.
Lemma lem2416001 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2416002 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2416003 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2416002 h1) (fun h1 : term252 = True => @lem2416001)). Qed.
Lemma lem2416004 : term252 = True.
Proof. exact (EQ_MP (@lem2416003) (@lem2416001)). Qed.
Lemma lem2416005 : term251 = True.
Proof. exact (TRANS (@lem2416000) (@lem2416004)). Qed.
Lemma lem2416006 : True = term251.
Proof. exact (SYM (@lem2416005)). Qed.
Lemma lem2416007 : term251.
Proof. exact (EQ_MP (@lem2416006) (@lem0)). Qed.
Lemma lem2416008 : term255.
Proof. exact (@lem2415997 (@lem2416007)). Qed.
Lemma lem2416010 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2416011 : term251 = term252.
Proof. exact (@lem2416010 (NUMERAL 0) term59). Qed.
Lemma lem2416012 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2416013 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2416014 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2416013 h1) (fun h1 : term252 = True => @lem2416012)). Qed.
Lemma lem2416015 : term252 = True.
Proof. exact (EQ_MP (@lem2416014) (@lem2416012)). Qed.
Lemma lem2416016 : term251 = True.
Proof. exact (TRANS (@lem2416011) (@lem2416015)). Qed.
Lemma lem2416017 : True = term251.
Proof. exact (SYM (@lem2416016)). Qed.
Lemma lem2416018 : term251.
Proof. exact (EQ_MP (@lem2416017) (@lem0)). Qed.
Lemma lem2416019 : term256.
Proof. exact (@lem2416008 (@lem2416018)). Qed.
Lemma lem2416021 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2416022 : term217 = term218.
Proof. exact (@lem2416021 term59 term59). Qed.
Lemma lem2416023 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2416024 : term220 = term59.
Proof. exact (EQ_MP (@lem2416023) (@lem940073)). Qed.
Lemma lem2416025 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2416026 : term218 = term58.
Proof. exact (MK_COMB (@lem2416025) (@lem2416024)). Qed.
Lemma lem2416027 : term217 = term58.
Proof. exact (TRANS (@lem2416022) (@lem2416026)). Qed.
Lemma lem2416029 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2416030 : term212 = term223.
Proof. exact (@lem2416029 term59 term59). Qed.
Lemma lem2416031 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2416032 : term220 = term59.
Proof. exact (EQ_MP (@lem2416031) (@lem940073)). Qed.
Lemma lem2416033 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2416034 : term218 = term58.
Proof. exact (MK_COMB (@lem2416033) (@lem2416032)). Qed.
Lemma lem2416035 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2416036 : term223 = term70.
Proof. exact (MK_COMB (@lem2416035) (@lem2416034)). Qed.
Lemma lem2416037 : term212 = term70.
Proof. exact (TRANS (@lem2416030) (@lem2416036)). Qed.
Lemma lem2416038 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2416039 : term257 = term244.
Proof. exact (MK_COMB (@lem2416038) (@lem2416037)). Qed.
Lemma lem2416040 : term258 = term246.
Proof. exact (MK_COMB (@lem2416039) (@lem2416027)). Qed.
Lemma lem2416042 (m : nat) : (term259 m) = term249.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2416043 : term246 = term249.
Proof. exact (@lem2416042 term59). Qed.
Lemma lem2416044 : term258 = term249.
Proof. exact (TRANS (@lem2416040) (@lem2416043)). Qed.
Lemma lem2416045 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2416046 : term260 = term261.
Proof. exact (MK_COMB (@lem2416045) (@lem2416044)). Qed.
Lemma lem2416047 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem2416048 : term262 = term263.
Proof. exact (MK_COMB (@lem2416046) (@lem2416047)). Qed.
Lemma lem2416050 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2416051 : term263 = term249.
Proof. exact (@lem2416050 term59). Qed.
Lemma lem2416052 : term262 = term249.
Proof. exact (TRANS (@lem2416048) (@lem2416051)). Qed.
Lemma lem2416054 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2416055 : term217 = term218.
Proof. exact (@lem2416054 term59 term59). Qed.
Lemma lem2416056 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2416057 : term220 = term59.
Proof. exact (EQ_MP (@lem2416056) (@lem940073)). Qed.
Lemma lem2416058 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2416059 : term218 = term58.
Proof. exact (MK_COMB (@lem2416058) (@lem2416057)). Qed.
Lemma lem2416060 : term217 = term58.
Proof. exact (TRANS (@lem2416055) (@lem2416059)). Qed.
Lemma lem2416061 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem2416062 : term265 = term263.
Proof. exact (MK_COMB (@lem2416061) (@lem2416060)). Qed.
Lemma lem2416064 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2416065 : term263 = term249.
Proof. exact (@lem2416064 term59). Qed.
Lemma lem2416066 : term265 = term249.
Proof. exact (TRANS (@lem2416062) (@lem2416065)). Qed.
Lemma lem2416067 : term249 = term265.
Proof. exact (SYM (@lem2416066)). Qed.
Lemma lem2416068 : term262 = term265.
Proof. exact (TRANS (@lem2416052) (@lem2416067)). Qed.
Lemma lem2416069 : term247 = term266.
Proof. exact (@lem2416019 (@lem2416068)). Qed.
Lemma lem2416070 : term246 = term266.
Proof. exact (TRANS (@lem2415985) (@lem2416069)). Qed.
Lemma lem2416072 (x : real) : (term226 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2416073 : term266 = term249.
Proof. exact (@lem2416072 term249). Qed.
Lemma lem2416074 : term246 = term249.
Proof. exact (TRANS (@lem2416070) (@lem2416073)). Qed.
Lemma lem2416075 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2416076 : term267 = term261.
Proof. exact (MK_COMB (@lem2416075) (@lem2416074)). Qed.
Lemma lem2416077 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2416078 (y : int) : (term243 y) = (term268 y).
Proof. exact (MK_COMB (@lem2416076) (@lem2416077 y)). Qed.
Lemma lem2416079 (y : int) : (term242 y) = (term268 y).
Proof. exact (TRANS (@lem2415976 y) (@lem2416078 y)). Qed.
Lemma lem2416080 (y : int) : (term268 y) = term249.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2416081 (y : int) : (term242 y) = term249.
Proof. exact (TRANS (@lem2416079 y) (@lem2416080 y)). Qed.
Lemma lem2416082 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2416083 (y : int) : (term269 y) = term270.
Proof. exact (MK_COMB (@lem2416082) (@lem2416081 y)). Qed.
Lemma lem2416084 : term70 = term70.
Proof. exact (eq_refl term70). Qed.
Lemma lem2416085 (y : int) : (term241 y) = term271.
Proof. exact (MK_COMB (@lem2416083 y) (@lem2416084)). Qed.
Lemma lem2416086 (y : int) : (term240 y) = term271.
Proof. exact (TRANS (@lem2415975 y) (@lem2416085 y)). Qed.
Lemma lem2416087 : term271 = term70.
Proof. exact (@lem1982721 term70). Qed.
Lemma lem2416088 (y : int) : (term240 y) = term70.
Proof. exact (TRANS (@lem2416086 y) (@lem2416087)). Qed.
Lemma lem2416089 (x : int) (y : int) : (term293 x y) = term271.
Proof. exact (MK_COMB (@lem2415974 x) (@lem2416088 y)). Qed.
Lemma lem2416090 (x : int) (y : int) : (term292 x y) = term271.
Proof. exact (TRANS (@lem2415866 x y) (@lem2416089 x y)). Qed.
Lemma lem2416091 : term271 = term70.
Proof. exact (@lem1982721 term70). Qed.
Lemma lem2416092 (x : int) (y : int) : (term292 x y) = term70.
Proof. exact (TRANS (@lem2416090 x y) (@lem2416091)). Qed.
Lemma lem2416093 (x : int) (y : int) : (term288 x y) = term70.
Proof. exact (TRANS (@lem2415865 x y) (@lem2416092 x y)). Qed.
Lemma lem2416094 (x : int) (y : int) : (term287 x y) = term70.
Proof. exact (TRANS (@lem2415772 x y) (@lem2416093 x y)). Qed.
Lemma lem2416095 (x : int) (y : int) : (term301 x y) = term70.
Proof. exact (TRANS (@lem2415771 x y) (@lem2416094 x y)). Qed.
Lemma lem2416096 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2416097 (x : int) (y : int) : (term302 x y) = term273.
Proof. exact (MK_COMB (@lem2416096) (@lem2416095 x y)). Qed.
Lemma lem2416098 : term249 = term249.
Proof. exact (eq_refl term249). Qed.
Lemma lem2416099 (x : int) (y : int) : (term299 x y) = term274.
Proof. exact (MK_COMB (@lem2416097 x y) (@lem2416098)). Qed.
Lemma lem2416100 (x : int) (y : int) : (term121 x y) = term274.
Proof. exact (TRANS (@lem2415732 x y) (@lem2416099 x y)). Qed.
Lemma lem2416101 (x : int) : (term159 x) = term275.
Proof. exact (fun_ext (fun y : int => @lem2416100 x y)). Qed.
Lemma lem2416102 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2416103 (x : int) : (term174 x) = term276.
Proof. exact (MK_COMB (@lem2416102) (@lem2416101 x)). Qed.
Lemma lem2416104 : term181 = term297.
Proof. exact (fun_ext (fun x : int => @lem2416103 x)). Qed.
Lemma lem2416105 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2416106 : term196 = term298.
Proof. exact (MK_COMB (@lem2416105) (@lem2416104)). Qed.
Lemma lem2416107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2416108 : term193 = term303.
Proof. exact (MK_COMB (@lem2416107) (@lem2415731)). Qed.
Lemma lem2416109 : term197 = term304.
Proof. exact (MK_COMB (@lem2416108) (@lem2416106)). Qed.
Lemma lem2416110 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2416111 : term155 = term305.
Proof. exact (MK_COMB (@lem2416110) (@lem2415356)). Qed.
Lemma lem2416112 : term198 = term306.
Proof. exact (MK_COMB (@lem2416111) (@lem2416109)). Qed.
Lemma lem2416113 : term130 = term306.
Proof. exact (TRANS (@lem2414879) (@lem2416112)). Qed.
Lemma lem2416115 {A : Type'} (t : Prop) : (term307 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2416116 (t : Prop) : (term308 t) = t.
Proof. exact (@lem2416115 int t). Qed.
Lemma lem2416117 : term276 = term274.
Proof. exact (@lem2416116 term274). Qed.
Lemma lem2416118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2416119 : term281 = term309.
Proof. exact (MK_COMB (@lem2416118) (@lem2416117)). Qed.
Lemma lem2416121 {A : Type'} (t : Prop) : (term307 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2416122 (t : Prop) : (term308 t) = t.
Proof. exact (@lem2416121 int t). Qed.
Lemma lem2416123 : term276 = term274.
Proof. exact (@lem2416122 term274). Qed.
Lemma lem2416124 : term282 = term310.
Proof. exact (MK_COMB (@lem2416119) (@lem2416123)). Qed.
Lemma lem2416125 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2416126 : term305 = term311.
Proof. exact (MK_COMB (@lem2416125) (@lem2416124)). Qed.
Lemma lem2416128 {A : Type'} (t : Prop) : (term307 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2416129 (t : Prop) : (term308 t) = t.
Proof. exact (@lem2416128 int t). Qed.
Lemma lem2416130 : term298 = term276.
Proof. exact (@lem2416129 term276). Qed.
Lemma lem2416132 {A : Type'} (t : Prop) : (term307 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2416133 (t : Prop) : (term308 t) = t.
Proof. exact (@lem2416132 int t). Qed.
Lemma lem2416134 : term276 = term274.
Proof. exact (@lem2416133 term274). Qed.
Lemma lem2416135 : term298 = term274.
Proof. exact (TRANS (@lem2416130) (@lem2416134)). Qed.
Lemma lem2416136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2416137 : term303 = term309.
Proof. exact (MK_COMB (@lem2416136) (@lem2416135)). Qed.
Lemma lem2416139 {A : Type'} (t : Prop) : (term307 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2416140 (t : Prop) : (term308 t) = t.
Proof. exact (@lem2416139 int t). Qed.
Lemma lem2416141 : term298 = term276.
Proof. exact (@lem2416140 term276). Qed.
Lemma lem2416143 {A : Type'} (t : Prop) : (term307 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2416144 (t : Prop) : (term308 t) = t.
Proof. exact (@lem2416143 int t). Qed.
Lemma lem2416145 : term276 = term274.
Proof. exact (@lem2416144 term274). Qed.
Lemma lem2416146 : term298 = term274.
Proof. exact (TRANS (@lem2416141) (@lem2416145)). Qed.
Lemma lem2416147 : term304 = term310.
Proof. exact (MK_COMB (@lem2416137) (@lem2416146)). Qed.
Lemma lem2416150 : term306 = term312.
Proof. exact (MK_COMB (@lem2416126) (@lem2416147)). Qed.
Lemma lem2416167 : term130 = term312.
Proof. exact (TRANS (@lem2416113) (@lem2416150)). Qed.
Lemma lem2416189 (h1 : term312) : term312.
Proof. exact (h1). Qed.
Lemma lem2416190 (h1 : term310) : term310.
Proof. exact (h1). Qed.
Lemma lem2416191 (h1 : term274) : term274.
Proof. exact (h1). Qed.
Lemma lem2416193 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2416194 : term274 = term313.
Proof. exact (@lem2416193 term249 term70). Qed.
Lemma lem2416196 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2416197 : term70 = term210.
Proof. exact (@lem2416196 term59). Qed.
Lemma lem2416199 (x : nat) : (real_of_num x) = (term206 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2416200 : term249 = term266.
Proof. exact (@lem2416199 (NUMERAL 0)). Qed.
Lemma lem2416201 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2416202 : term314 = term315.
Proof. exact (MK_COMB (@lem2416201) (@lem2416200)). Qed.
Lemma lem2416203 : term313 = term316.
Proof. exact (MK_COMB (@lem2416202) (@lem2416197)). Qed.
Lemma lem2416204 : term317.
Proof. exact (@lem1980026 term249 term58 term70 term58). Qed.
Lemma lem2416206 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2416207 : term251 = term252.
Proof. exact (@lem2416206 (NUMERAL 0) term59). Qed.
Lemma lem2416208 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2416209 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2416210 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2416209 h1) (fun h1 : term252 = True => @lem2416208)). Qed.
Lemma lem2416211 : term252 = True.
Proof. exact (EQ_MP (@lem2416210) (@lem2416208)). Qed.
Lemma lem2416212 : term251 = True.
Proof. exact (TRANS (@lem2416207) (@lem2416211)). Qed.
Lemma lem2416213 : True = term251.
Proof. exact (SYM (@lem2416212)). Qed.
Lemma lem2416214 : term251.
Proof. exact (EQ_MP (@lem2416213) (@lem0)). Qed.
Lemma lem2416215 : term318.
Proof. exact (@lem2416204 (@lem2416214)). Qed.
Lemma lem2416217 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2416218 : term251 = term252.
Proof. exact (@lem2416217 (NUMERAL 0) term59). Qed.
Lemma lem2416219 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2416220 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2416221 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2416220 h1) (fun h1 : term252 = True => @lem2416219)). Qed.
Lemma lem2416222 : term252 = True.
Proof. exact (EQ_MP (@lem2416221) (@lem2416219)). Qed.
Lemma lem2416223 : term251 = True.
Proof. exact (TRANS (@lem2416218) (@lem2416222)). Qed.
Lemma lem2416224 : True = term251.
Proof. exact (SYM (@lem2416223)). Qed.
Lemma lem2416225 : term251.
Proof. exact (EQ_MP (@lem2416224) (@lem0)). Qed.
Lemma lem2416226 : term316 = term319.
Proof. exact (@lem2416215 (@lem2416225)). Qed.
Lemma lem2416228 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2416229 : term212 = term223.
Proof. exact (@lem2416228 term59 term59). Qed.
Lemma lem2416230 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2416231 : term220 = term59.
Proof. exact (EQ_MP (@lem2416230) (@lem940073)). Qed.
Lemma lem2416232 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2416233 : term218 = term58.
Proof. exact (MK_COMB (@lem2416232) (@lem2416231)). Qed.
Lemma lem2416234 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2416235 : term223 = term70.
Proof. exact (MK_COMB (@lem2416234) (@lem2416233)). Qed.
Lemma lem2416236 : term212 = term70.
Proof. exact (TRANS (@lem2416229) (@lem2416235)). Qed.
Lemma lem2416238 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2416239 : term263 = term249.
Proof. exact (@lem2416238 term59). Qed.
Lemma lem2416240 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2416241 : term320 = term314.
Proof. exact (MK_COMB (@lem2416240) (@lem2416239)). Qed.
Lemma lem2416242 : term319 = term313.
Proof. exact (MK_COMB (@lem2416241) (@lem2416236)). Qed.
Lemma lem2416244 (m : nat) (n : nat) : (term321 m n) = (term322 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2416245 : term313 = term323.
Proof. exact (@lem2416244 (NUMERAL 0) term59). Qed.
Lemma lem2416246 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2416247 (h1 : term253 = (BIT1 0)) : (term59 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2416248 : (term253 = (BIT1 0)) = ((term59 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2416247 h1) (fun h1 : (term59 = (NUMERAL 0)) = False => @lem2416246)). Qed.
Lemma lem2416249 : (term59 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2416248) (@lem2416246)). Qed.
Lemma lem2416250 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2416251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2416252 : term324 = (and True).
Proof. exact (MK_COMB (@lem2416251) (@lem2416250)). Qed.
Lemma lem2416253 : term323 = (True /\ False).
Proof. exact (MK_COMB (@lem2416252) (@lem2416249)). Qed.
Lemma lem2416255 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2416256 : term323 = False.
Proof. exact (TRANS (@lem2416253) (@lem2416255)). Qed.
Lemma lem2416257 : term313 = False.
Proof. exact (TRANS (@lem2416245) (@lem2416256)). Qed.
Lemma lem2416258 : term319 = False.
Proof. exact (TRANS (@lem2416242) (@lem2416257)). Qed.
Lemma lem2416259 : term316 = False.
Proof. exact (TRANS (@lem2416226) (@lem2416258)). Qed.
Lemma lem2416260 : term313 = False.
Proof. exact (TRANS (@lem2416203) (@lem2416259)). Qed.
Lemma lem2416261 : term274 = False.
Proof. exact (TRANS (@lem2416194) (@lem2416260)). Qed.
Lemma lem2416262 (h1 : term274) : False.
Proof. exact (EQ_MP (@lem2416261) (@lem2416191 h1)). Qed.
Lemma lem2416263 (h1 : term274) : term274.
Proof. exact (h1). Qed.
Lemma lem2416265 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2416266 : term274 = term313.
Proof. exact (@lem2416265 term249 term70). Qed.
Lemma lem2416268 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2416269 : term70 = term210.
Proof. exact (@lem2416268 term59). Qed.
Lemma lem2416271 (x : nat) : (real_of_num x) = (term206 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2416272 : term249 = term266.
Proof. exact (@lem2416271 (NUMERAL 0)). Qed.
Lemma lem2416273 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2416274 : term314 = term315.
Proof. exact (MK_COMB (@lem2416273) (@lem2416272)). Qed.
Lemma lem2416275 : term313 = term316.
Proof. exact (MK_COMB (@lem2416274) (@lem2416269)). Qed.
Lemma lem2416276 : term317.
Proof. exact (@lem1980026 term249 term58 term70 term58). Qed.
Lemma lem2416278 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2416279 : term251 = term252.
Proof. exact (@lem2416278 (NUMERAL 0) term59). Qed.
Lemma lem2416280 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2416281 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2416282 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2416281 h1) (fun h1 : term252 = True => @lem2416280)). Qed.
Lemma lem2416283 : term252 = True.
Proof. exact (EQ_MP (@lem2416282) (@lem2416280)). Qed.
Lemma lem2416284 : term251 = True.
Proof. exact (TRANS (@lem2416279) (@lem2416283)). Qed.
Lemma lem2416285 : True = term251.
Proof. exact (SYM (@lem2416284)). Qed.
Lemma lem2416286 : term251.
Proof. exact (EQ_MP (@lem2416285) (@lem0)). Qed.
Lemma lem2416287 : term318.
Proof. exact (@lem2416276 (@lem2416286)). Qed.
Lemma lem2416289 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2416290 : term251 = term252.
Proof. exact (@lem2416289 (NUMERAL 0) term59). Qed.
Lemma lem2416291 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2416292 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2416293 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2416292 h1) (fun h1 : term252 = True => @lem2416291)). Qed.
Lemma lem2416294 : term252 = True.
Proof. exact (EQ_MP (@lem2416293) (@lem2416291)). Qed.
Lemma lem2416295 : term251 = True.
Proof. exact (TRANS (@lem2416290) (@lem2416294)). Qed.
Lemma lem2416296 : True = term251.
Proof. exact (SYM (@lem2416295)). Qed.
Lemma lem2416297 : term251.
Proof. exact (EQ_MP (@lem2416296) (@lem0)). Qed.
Lemma lem2416298 : term316 = term319.
Proof. exact (@lem2416287 (@lem2416297)). Qed.
Lemma lem2416300 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2416301 : term212 = term223.
Proof. exact (@lem2416300 term59 term59). Qed.
Lemma lem2416302 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2416303 : term220 = term59.
Proof. exact (EQ_MP (@lem2416302) (@lem940073)). Qed.
Lemma lem2416304 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2416305 : term218 = term58.
Proof. exact (MK_COMB (@lem2416304) (@lem2416303)). Qed.
Lemma lem2416306 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2416307 : term223 = term70.
Proof. exact (MK_COMB (@lem2416306) (@lem2416305)). Qed.
Lemma lem2416308 : term212 = term70.
Proof. exact (TRANS (@lem2416301) (@lem2416307)). Qed.
Lemma lem2416310 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2416311 : term263 = term249.
Proof. exact (@lem2416310 term59). Qed.
Lemma lem2416312 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2416313 : term320 = term314.
Proof. exact (MK_COMB (@lem2416312) (@lem2416311)). Qed.
Lemma lem2416314 : term319 = term313.
Proof. exact (MK_COMB (@lem2416313) (@lem2416308)). Qed.
Lemma lem2416316 (m : nat) (n : nat) : (term321 m n) = (term322 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2416317 : term313 = term323.
Proof. exact (@lem2416316 (NUMERAL 0) term59). Qed.
Lemma lem2416318 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2416319 (h1 : term253 = (BIT1 0)) : (term59 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2416320 : (term253 = (BIT1 0)) = ((term59 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2416319 h1) (fun h1 : (term59 = (NUMERAL 0)) = False => @lem2416318)). Qed.
Lemma lem2416321 : (term59 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2416320) (@lem2416318)). Qed.
Lemma lem2416322 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2416323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2416324 : term324 = (and True).
Proof. exact (MK_COMB (@lem2416323) (@lem2416322)). Qed.
Lemma lem2416325 : term323 = (True /\ False).
Proof. exact (MK_COMB (@lem2416324) (@lem2416321)). Qed.
Lemma lem2416327 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2416328 : term323 = False.
Proof. exact (TRANS (@lem2416325) (@lem2416327)). Qed.
Lemma lem2416329 : term313 = False.
Proof. exact (TRANS (@lem2416317) (@lem2416328)). Qed.
Lemma lem2416330 : term319 = False.
Proof. exact (TRANS (@lem2416314) (@lem2416329)). Qed.
Lemma lem2416331 : term316 = False.
Proof. exact (TRANS (@lem2416298) (@lem2416330)). Qed.
Lemma lem2416332 : term313 = False.
Proof. exact (TRANS (@lem2416275) (@lem2416331)). Qed.
Lemma lem2416333 : term274 = False.
Proof. exact (TRANS (@lem2416266) (@lem2416332)). Qed.
Lemma lem2416334 (h1 : term274) : False.
Proof. exact (EQ_MP (@lem2416333) (@lem2416263 h1)). Qed.
Lemma lem2416335 (h1 : term310) : False.
Proof. exact (or_elim (@lem2416190 h1) (fun h0 : term274 => @lem2416262 h0) (fun h0 : term274 => @lem2416334 h0)). Qed.
Lemma lem2416336 (h1 : term310) : term310.
Proof. exact (h1). Qed.
Lemma lem2416337 (h1 : term274) : term274.
Proof. exact (h1). Qed.
Lemma lem2416339 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2416340 : term274 = term313.
Proof. exact (@lem2416339 term249 term70). Qed.
Lemma lem2416342 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2416343 : term70 = term210.
Proof. exact (@lem2416342 term59). Qed.
Lemma lem2416345 (x : nat) : (real_of_num x) = (term206 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2416346 : term249 = term266.
Proof. exact (@lem2416345 (NUMERAL 0)). Qed.
Lemma lem2416347 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2416348 : term314 = term315.
Proof. exact (MK_COMB (@lem2416347) (@lem2416346)). Qed.
Lemma lem2416349 : term313 = term316.
Proof. exact (MK_COMB (@lem2416348) (@lem2416343)). Qed.
Lemma lem2416350 : term317.
Proof. exact (@lem1980026 term249 term58 term70 term58). Qed.
Lemma lem2416352 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2416353 : term251 = term252.
Proof. exact (@lem2416352 (NUMERAL 0) term59). Qed.
Lemma lem2416354 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2416355 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2416356 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2416355 h1) (fun h1 : term252 = True => @lem2416354)). Qed.
Lemma lem2416357 : term252 = True.
Proof. exact (EQ_MP (@lem2416356) (@lem2416354)). Qed.
Lemma lem2416358 : term251 = True.
Proof. exact (TRANS (@lem2416353) (@lem2416357)). Qed.
Lemma lem2416359 : True = term251.
Proof. exact (SYM (@lem2416358)). Qed.
Lemma lem2416360 : term251.
Proof. exact (EQ_MP (@lem2416359) (@lem0)). Qed.
Lemma lem2416361 : term318.
Proof. exact (@lem2416350 (@lem2416360)). Qed.
Lemma lem2416363 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2416364 : term251 = term252.
Proof. exact (@lem2416363 (NUMERAL 0) term59). Qed.
Lemma lem2416365 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2416366 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2416367 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2416366 h1) (fun h1 : term252 = True => @lem2416365)). Qed.
Lemma lem2416368 : term252 = True.
Proof. exact (EQ_MP (@lem2416367) (@lem2416365)). Qed.
Lemma lem2416369 : term251 = True.
Proof. exact (TRANS (@lem2416364) (@lem2416368)). Qed.
Lemma lem2416370 : True = term251.
Proof. exact (SYM (@lem2416369)). Qed.
Lemma lem2416371 : term251.
Proof. exact (EQ_MP (@lem2416370) (@lem0)). Qed.
Lemma lem2416372 : term316 = term319.
Proof. exact (@lem2416361 (@lem2416371)). Qed.
Lemma lem2416374 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2416375 : term212 = term223.
Proof. exact (@lem2416374 term59 term59). Qed.
Lemma lem2416376 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2416377 : term220 = term59.
Proof. exact (EQ_MP (@lem2416376) (@lem940073)). Qed.
Lemma lem2416378 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2416379 : term218 = term58.
Proof. exact (MK_COMB (@lem2416378) (@lem2416377)). Qed.
Lemma lem2416380 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2416381 : term223 = term70.
Proof. exact (MK_COMB (@lem2416380) (@lem2416379)). Qed.
Lemma lem2416382 : term212 = term70.
Proof. exact (TRANS (@lem2416375) (@lem2416381)). Qed.
Lemma lem2416384 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2416385 : term263 = term249.
Proof. exact (@lem2416384 term59). Qed.
Lemma lem2416386 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2416387 : term320 = term314.
Proof. exact (MK_COMB (@lem2416386) (@lem2416385)). Qed.
Lemma lem2416388 : term319 = term313.
Proof. exact (MK_COMB (@lem2416387) (@lem2416382)). Qed.
Lemma lem2416390 (m : nat) (n : nat) : (term321 m n) = (term322 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2416391 : term313 = term323.
Proof. exact (@lem2416390 (NUMERAL 0) term59). Qed.
Lemma lem2416392 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2416393 (h1 : term253 = (BIT1 0)) : (term59 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2416394 : (term253 = (BIT1 0)) = ((term59 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2416393 h1) (fun h1 : (term59 = (NUMERAL 0)) = False => @lem2416392)). Qed.
Lemma lem2416395 : (term59 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2416394) (@lem2416392)). Qed.
Lemma lem2416396 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2416397 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2416398 : term324 = (and True).
Proof. exact (MK_COMB (@lem2416397) (@lem2416396)). Qed.
Lemma lem2416399 : term323 = (True /\ False).
Proof. exact (MK_COMB (@lem2416398) (@lem2416395)). Qed.
Lemma lem2416401 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2416402 : term323 = False.
Proof. exact (TRANS (@lem2416399) (@lem2416401)). Qed.
Lemma lem2416403 : term313 = False.
Proof. exact (TRANS (@lem2416391) (@lem2416402)). Qed.
Lemma lem2416404 : term319 = False.
Proof. exact (TRANS (@lem2416388) (@lem2416403)). Qed.
Lemma lem2416405 : term316 = False.
Proof. exact (TRANS (@lem2416372) (@lem2416404)). Qed.
Lemma lem2416406 : term313 = False.
Proof. exact (TRANS (@lem2416349) (@lem2416405)). Qed.
Lemma lem2416407 : term274 = False.
Proof. exact (TRANS (@lem2416340) (@lem2416406)). Qed.
Lemma lem2416408 (h1 : term274) : False.
Proof. exact (EQ_MP (@lem2416407) (@lem2416337 h1)). Qed.
Lemma lem2416409 (h1 : term274) : term274.
Proof. exact (h1). Qed.
Lemma lem2416411 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2416412 : term274 = term313.
Proof. exact (@lem2416411 term249 term70). Qed.
Lemma lem2416414 (x : nat) : (term208 x) = (term209 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2416415 : term70 = term210.
Proof. exact (@lem2416414 term59). Qed.
Lemma lem2416417 (x : nat) : (real_of_num x) = (term206 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2416418 : term249 = term266.
Proof. exact (@lem2416417 (NUMERAL 0)). Qed.
Lemma lem2416419 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2416420 : term314 = term315.
Proof. exact (MK_COMB (@lem2416419) (@lem2416418)). Qed.
Lemma lem2416421 : term313 = term316.
Proof. exact (MK_COMB (@lem2416420) (@lem2416415)). Qed.
Lemma lem2416422 : term317.
Proof. exact (@lem1980026 term249 term58 term70 term58). Qed.
Lemma lem2416424 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2416425 : term251 = term252.
Proof. exact (@lem2416424 (NUMERAL 0) term59). Qed.
Lemma lem2416426 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2416427 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2416428 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2416427 h1) (fun h1 : term252 = True => @lem2416426)). Qed.
Lemma lem2416429 : term252 = True.
Proof. exact (EQ_MP (@lem2416428) (@lem2416426)). Qed.
Lemma lem2416430 : term251 = True.
Proof. exact (TRANS (@lem2416425) (@lem2416429)). Qed.
Lemma lem2416431 : True = term251.
Proof. exact (SYM (@lem2416430)). Qed.
Lemma lem2416432 : term251.
Proof. exact (EQ_MP (@lem2416431) (@lem0)). Qed.
Lemma lem2416433 : term318.
Proof. exact (@lem2416422 (@lem2416432)). Qed.
Lemma lem2416435 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2416436 : term251 = term252.
Proof. exact (@lem2416435 (NUMERAL 0) term59). Qed.
Lemma lem2416437 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2416438 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2416439 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2416438 h1) (fun h1 : term252 = True => @lem2416437)). Qed.
Lemma lem2416440 : term252 = True.
Proof. exact (EQ_MP (@lem2416439) (@lem2416437)). Qed.
Lemma lem2416441 : term251 = True.
Proof. exact (TRANS (@lem2416436) (@lem2416440)). Qed.
Lemma lem2416442 : True = term251.
Proof. exact (SYM (@lem2416441)). Qed.
Lemma lem2416443 : term251.
Proof. exact (EQ_MP (@lem2416442) (@lem0)). Qed.
Lemma lem2416444 : term316 = term319.
Proof. exact (@lem2416433 (@lem2416443)). Qed.
Lemma lem2416446 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2416447 : term212 = term223.
Proof. exact (@lem2416446 term59 term59). Qed.
Lemma lem2416448 : (term219 = (BIT1 0)) = (term220 = term59).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2416449 : term220 = term59.
Proof. exact (EQ_MP (@lem2416448) (@lem940073)). Qed.
Lemma lem2416450 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2416451 : term218 = term58.
Proof. exact (MK_COMB (@lem2416450) (@lem2416449)). Qed.
Lemma lem2416452 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2416453 : term223 = term70.
Proof. exact (MK_COMB (@lem2416452) (@lem2416451)). Qed.
Lemma lem2416454 : term212 = term70.
Proof. exact (TRANS (@lem2416447) (@lem2416453)). Qed.
Lemma lem2416456 (x : nat) : (term264 x) = term249.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2416457 : term263 = term249.
Proof. exact (@lem2416456 term59). Qed.
Lemma lem2416458 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2416459 : term320 = term314.
Proof. exact (MK_COMB (@lem2416458) (@lem2416457)). Qed.
Lemma lem2416460 : term319 = term313.
Proof. exact (MK_COMB (@lem2416459) (@lem2416454)). Qed.
Lemma lem2416462 (m : nat) (n : nat) : (term321 m n) = (term322 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2416463 : term313 = term323.
Proof. exact (@lem2416462 (NUMERAL 0) term59). Qed.
Lemma lem2416464 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2416465 (h1 : term253 = (BIT1 0)) : (term59 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2416466 : (term253 = (BIT1 0)) = ((term59 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem2416465 h1) (fun h1 : (term59 = (NUMERAL 0)) = False => @lem2416464)). Qed.
Lemma lem2416467 : (term59 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2416466) (@lem2416464)). Qed.
Lemma lem2416468 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2416469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2416470 : term324 = (and True).
Proof. exact (MK_COMB (@lem2416469) (@lem2416468)). Qed.
Lemma lem2416471 : term323 = (True /\ False).
Proof. exact (MK_COMB (@lem2416470) (@lem2416467)). Qed.
Lemma lem2416473 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2416474 : term323 = False.
Proof. exact (TRANS (@lem2416471) (@lem2416473)). Qed.
Lemma lem2416475 : term313 = False.
Proof. exact (TRANS (@lem2416463) (@lem2416474)). Qed.
Lemma lem2416476 : term319 = False.
Proof. exact (TRANS (@lem2416460) (@lem2416475)). Qed.
Lemma lem2416477 : term316 = False.
Proof. exact (TRANS (@lem2416444) (@lem2416476)). Qed.
Lemma lem2416478 : term313 = False.
Proof. exact (TRANS (@lem2416421) (@lem2416477)). Qed.
Lemma lem2416479 : term274 = False.
Proof. exact (TRANS (@lem2416412) (@lem2416478)). Qed.
Lemma lem2416480 (h1 : term274) : False.
Proof. exact (EQ_MP (@lem2416479) (@lem2416409 h1)). Qed.
Lemma lem2416481 (h1 : term310) : False.
Proof. exact (or_elim (@lem2416336 h1) (fun h0 : term274 => @lem2416408 h0) (fun h0 : term274 => @lem2416480 h0)). Qed.
Lemma lem2416482 (h1 : term312) : False.
Proof. exact (or_elim (@lem2416189 h1) (fun h0 : term310 => @lem2416335 h0) (fun h0 : term310 => @lem2416481 h0)). Qed.
Lemma lem2416484 (h1 : term312) : term312.
Proof. exact (h1). Qed.
Lemma lem2416485 (h1 : term312) : term312 = False.
Proof. exact (prop_ext (fun h2 : term312 => @lem2416482 h1) (fun h2 : False => @lem2416484 h1)). Qed.
Lemma lem2416486 (h1 : term312) : False.
Proof. exact (EQ_MP (@lem2416485 h1) (@lem2416484 h1)). Qed.
Lemma lem2416487 (h1 : term130) : term130.
Proof. exact (h1). Qed.
Lemma lem2416488 (h1 : term130) : term312.
Proof. exact (EQ_MP (@lem2416167) (@lem2416487 h1)). Qed.
Lemma lem2416489 (h1 : term130) : term312 = False.
Proof. exact (prop_ext (fun h2 : term312 => @lem2416486 h2) (fun h2 : False => @lem2416488 h1)). Qed.
Lemma lem2416490 (h1 : term130) : False.
Proof. exact (EQ_MP (@lem2416489 h1) (@lem2416488 h1)). Qed.
Lemma lem2416491 : term325.
Proof. exact (fun h0 : term130 => @lem2416490 h0). Qed.
Lemma lem2416492 : term326.
Proof. exact (@lem1386578 term327). Qed.
Lemma lem2416495 : term327.
Proof. exact (@lem2416492 (@lem2416491)). Qed.
Lemma lem2416496 : term128 = term37.
Proof. exact (SYM (@lem2414674)). Qed.
Lemma lem2416497 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2416498 : term327 = term0.
Proof. exact (MK_COMB (@lem2416497) (@lem2416496)). Qed.
Lemma lem2416499 : term0.
Proof. exact (EQ_MP (@lem2416498) (@lem2416495)). Qed.
Lemma lem2416500 : term1.
Proof. exact (EQ_MP (@lem2414415) (@lem2416499)). Qed.
Lemma lem2416501 : term1 = (term1 = True).
Proof. exact (@lem7 term1). Qed.
Lemma lem2416502 : term1 = True.
Proof. exact (EQ_MP (@lem2416501) (@lem2416500)). Qed.
Lemma lem2416503 : True = term1.
Proof. exact (SYM (@lem2416502)). Qed.
Lemma lem2416504 : term1.
Proof. exact (EQ_MP (@lem2416503) (@lem0)). Qed.
