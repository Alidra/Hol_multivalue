Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_LT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339379_spec.
Require Import thm1339697_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem1374338 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1374339 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1374340 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1374339 t1) (@lem1374338 t1)). Qed.
Lemma lem1374341 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1374340 t1 t2). Qed.
Lemma lem1374342 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1374343 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1374342 t1 t2) (@lem1374341 t1 t2)). Qed.
Lemma lem1374344 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1374343 t1 t2 t3). Qed.
Lemma lem1374345 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1374346 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1374345 t1 t2 t3) (@lem1374344 t1 t2 t3)). Qed.
Lemma lem1374347 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1374346 t1 t2 t3)). Qed.
Lemma lem1374348 (y : real) : term7 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1374349 (y : real) : (term7 y) = (term8 y).
Proof. exact (eq_refl (term7 y)). Qed.
Lemma lem1374350 (y : real) : term8 y.
Proof. exact (EQ_MP (@lem1374349 y) (@lem1374348 y)). Qed.
Lemma lem1374351 (y : real) (x : real) : term9 y x.
Proof. exact (@lem1374350 y x). Qed.
Lemma lem1374352 (y : real) (x : real) : (term9 y x) = ((real_lt x y) = (term10 y x)).
Proof. exact (eq_refl (term9 y x)). Qed.
Lemma lem1374367 (y : real) (x : real) : (real_lt x y) = (term10 y x).
Proof. exact (EQ_MP (@lem1374352 y x) (@lem1374351 y x)). Qed.
Lemma lem1374368 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1374369 (y : real) (x : real) : (term11 x y) = (term12 y x).
Proof. exact (MK_COMB (@lem1374368) (@lem1374367 y x)). Qed.
Lemma lem1374372 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1374373 (x : real) (y : real) : (term13 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem1374369 y x) (@lem1374372 x y)). Qed.
Lemma lem1374376 (x : real) (y : real) : (term15 x y) = (term15 x y).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1374377 (x : real) (y : real) : ((real_le x y) = (term13 x y)) = ((real_le x y) = (term14 x y)).
Proof. exact (MK_COMB (@lem1374376 x y) (@lem1374373 x y)). Qed.
Lemma lem1374380 (x : real) : (term16 x) = (term17 x).
Proof. exact (fun_ext (fun y : real => @lem1374377 x y)). Qed.
Lemma lem1374381 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374382 (x : real) : (term18 x) = (term19 x).
Proof. exact (MK_COMB (@lem1374381) (@lem1374380 x)). Qed.
Lemma lem1374387 : term20 = term21.
Proof. exact (fun_ext (fun x : real => @lem1374382 x)). Qed.
Lemma lem1374388 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374389 : term22 = term23.
Proof. exact (MK_COMB (@lem1374388) (@lem1374387)). Qed.
Lemma lem1374394 : term23 = term22.
Proof. exact (SYM (@lem1374389)). Qed.
Lemma lem1374396 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1374397 : term23 = term25.
Proof. exact (@lem1374396 term23). Qed.
Lemma lem1374398 : term25 = term23.
Proof. exact (SYM (@lem1374397)). Qed.
Lemma lem1374399 (h1 : term26) : term26.
Proof. exact (h1). Qed.
Lemma lem1374402 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem1374403 : term28.
Proof. exact (fun h0 : term27 => @lem1374402 h0). Qed.
Lemma lem1374404 (h1 : term28) : term28.
Proof. exact (h1). Qed.
Lemma lem1374405 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem1374406 (h1 : term27) (h2 : term28) : term27.
Proof. exact (@lem1374404 h2 (@lem1374405 h1)). Qed.
Lemma lem1374407 (h1 : term27) : term29.
Proof. exact (fun h0 : term28 => @lem1374406 h1 h0). Qed.
Lemma lem1374408 (h1 : term28) : term28.
Proof. exact (h1). Qed.
Lemma lem1374409 (h1 : term27) (h2 : term28) : term27.
Proof. exact (@lem1374407 h1 (@lem1374408 h2)). Qed.
Lemma lem1374410 (h1 : term28) : term28.
Proof. exact (fun h0 : term27 => @lem1374409 h0 h1). Qed.
Lemma lem1374411 : term30.
Proof. exact (fun h0 : term28 => @lem1374410 h0). Qed.
Lemma lem1374414 : term28.
Proof. exact (@lem1374411 (@lem1374403)). Qed.
Lemma lem1374484 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1374485 : term31 = term32.
Proof. exact (@lem1374484 term33). Qed.
Lemma lem1374496 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1374497 : term35 = term36.
Proof. exact (MK_COMB (@lem1374496) (@lem1374485)). Qed.
Lemma lem1374500 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1374507 : term27 = term38.
Proof. exact (MK_COMB (@lem1374500) (@lem1374497)). Qed.
Lemma lem1374516 (x : real) (y : real) : ((term39 y x) = (x = y)) = ((term39 y x) = (x = y)).
Proof. exact (eq_refl ((term39 y x) = (x = y))). Qed.
Lemma lem1374517 (x : real) : (term40 x) = (term40 x).
Proof. exact (fun_ext (fun y : real => @lem1374516 x y)). Qed.
Lemma lem1374518 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374519 (x : real) : (term41 x) = (term41 x).
Proof. exact (MK_COMB (@lem1374518) (@lem1374517 x)). Qed.
Lemma lem1374520 : term42 = term42.
Proof. exact (fun_ext (fun x : real => @lem1374519 x)). Qed.
Lemma lem1374521 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374522 : term33 = term33.
Proof. exact (MK_COMB (@lem1374521) (@lem1374520)). Qed.
Lemma lem1374523 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1374524 : term32 = term32.
Proof. exact (MK_COMB (@lem1374523) (@lem1374522)). Qed.
Lemma lem1374529 (y : real) (x : real) : (term43 y x) = (term43 y x).
Proof. exact (eq_refl (term43 y x)). Qed.
Lemma lem1374530 (x : real) : (term44 x) = (term44 x).
Proof. exact (fun_ext (fun y : real => @lem1374529 y x)). Qed.
Lemma lem1374531 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374532 (x : real) : (term45 x) = (term45 x).
Proof. exact (MK_COMB (@lem1374531) (@lem1374530 x)). Qed.
Lemma lem1374533 : term46 = term46.
Proof. exact (fun_ext (fun x : real => @lem1374532 x)). Qed.
Lemma lem1374534 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374535 : term47 = term47.
Proof. exact (MK_COMB (@lem1374534) (@lem1374533)). Qed.
Lemma lem1374536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1374537 : term34 = term34.
Proof. exact (MK_COMB (@lem1374536) (@lem1374535)). Qed.
Lemma lem1374538 : term36 = term36.
Proof. exact (MK_COMB (@lem1374537) (@lem1374524)). Qed.
Lemma lem1374549 (x : real) (y : real) : ((real_le x y) = (term14 x y)) = ((real_le x y) = (term14 x y)).
Proof. exact (eq_refl ((real_le x y) = (term14 x y))). Qed.
Lemma lem1374550 (x : real) : (term17 x) = (term17 x).
Proof. exact (fun_ext (fun y : real => @lem1374549 x y)). Qed.
Lemma lem1374551 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374552 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1374551) (@lem1374550 x)). Qed.
Lemma lem1374553 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1374552 x)). Qed.
Lemma lem1374554 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374555 : term23 = term23.
Proof. exact (MK_COMB (@lem1374554) (@lem1374553)). Qed.
Lemma lem1374556 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1374557 : term26 = term26.
Proof. exact (MK_COMB (@lem1374556) (@lem1374555)). Qed.
Lemma lem1374558 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1374559 : term37 = term37.
Proof. exact (MK_COMB (@lem1374558) (@lem1374557)). Qed.
Lemma lem1374560 : term38 = term38.
Proof. exact (MK_COMB (@lem1374559) (@lem1374538)). Qed.
Lemma lem1374609 : term27 = term38.
Proof. exact (TRANS (@lem1374507) (@lem1374560)). Qed.
Lemma lem1374610 : term38 = term27.
Proof. exact (SYM (@lem1374609)). Qed.
Lemma lem1374611 (h1 : term26) : term26.
Proof. exact (h1). Qed.
Lemma lem1374612 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem1374613 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1374619 (y : real) (x : real) : (term48 y x) = (real_le y x).
Proof. exact (@lem16933 (real_le y x)). Qed.
Lemma lem1374620 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1374622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1374623 (y : real) (x : real) : (term50 y x) = (term51 y x).
Proof. exact (MK_COMB (@lem1374622) (@lem1374619 y x)). Qed.
Lemma lem1374624 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1374623 y x) (@lem1374620 x y)). Qed.
Lemma lem1374625 (x : real) (y : real) : (term54 x y) = (term52 x y).
Proof. exact (@lem17160 (term10 y x) (x = y)). Qed.
Lemma lem1374626 (x : real) (y : real) : (term54 x y) = (term53 x y).
Proof. exact (TRANS (@lem1374625 x y) (@lem1374624 x y)). Qed.
Lemma lem1374632 (x : real) (y : real) : (term55 x y) = (term55 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1374634 (x : real) (y : real) : (term51 x y) = (term51 x y).
Proof. exact (eq_refl (term51 x y)). Qed.
Lemma lem1374635 (x : real) (y : real) : (term56 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem1374634 x y) (@lem1374626 x y)). Qed.
Lemma lem1374636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1374637 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1374636) (@lem1374635 x y)). Qed.
Lemma lem1374638 (x : real) (y : real) : (term60 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1374637 x y) (@lem1374632 x y)). Qed.
Lemma lem1374639 (x : real) (y : real) : (term62 x y) = (term60 x y).
Proof. exact (@lem17646 (real_le x y) (term14 x y)). Qed.
Lemma lem1374640 (x : real) (y : real) : (term62 x y) = (term61 x y).
Proof. exact (TRANS (@lem1374639 x y) (@lem1374638 x y)). Qed.
Lemma lem1374641 (P : real -> Prop) : (term63 P) = (term64 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1374642 (x : real) : (term65 x) = (term66 x).
Proof. exact (@lem1374641 (term17 x)). Qed.
Lemma lem1374643 (x : real) (y : real) : (term67 x y) = ((real_le x y) = (term14 x y)).
Proof. exact (eq_refl (term67 x y)). Qed.
Lemma lem1374644 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1374645 (x : real) (y : real) : (term68 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1374644) (@lem1374643 x y)). Qed.
Lemma lem1374646 (x : real) (y : real) : (term68 x y) = (term61 x y).
Proof. exact (TRANS (@lem1374645 x y) (@lem1374640 x y)). Qed.
Lemma lem1374647 (x : real) : (term69 x) = (term70 x).
Proof. exact (fun_ext (fun y : real => @lem1374646 x y)). Qed.
Lemma lem1374648 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374649 (x : real) : (term66 x) = (term71 x).
Proof. exact (MK_COMB (@lem1374648) (@lem1374647 x)). Qed.
Lemma lem1374650 (x : real) : (term65 x) = (term71 x).
Proof. exact (TRANS (@lem1374642 x) (@lem1374649 x)). Qed.
Lemma lem1374651 (P : real -> Prop) : (term63 P) = (term64 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1374652 : term26 = term72.
Proof. exact (@lem1374651 term21). Qed.
Lemma lem1374653 (x : real) : (term73 x) = (term19 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1374654 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1374655 (x : real) : (term74 x) = (term65 x).
Proof. exact (MK_COMB (@lem1374654) (@lem1374653 x)). Qed.
Lemma lem1374656 (x : real) : (term74 x) = (term71 x).
Proof. exact (TRANS (@lem1374655 x) (@lem1374650 x)). Qed.
Lemma lem1374657 : term75 = term76.
Proof. exact (fun_ext (fun x : real => @lem1374656 x)). Qed.
Lemma lem1374658 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374659 : term72 = term77.
Proof. exact (MK_COMB (@lem1374658) (@lem1374657)). Qed.
Lemma lem1374660 : term26 = term77.
Proof. exact (TRANS (@lem1374652) (@lem1374659)). Qed.
Lemma lem1374666 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term78 A P Q) = (term79 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1374667 (P : real -> Prop) (Q : real -> Prop) : (term80 P Q) = (term81 P Q).
Proof. exact (@lem1374666 real P Q). Qed.
Lemma lem1374668 (x : real) : (term82 x) = (term83 x).
Proof. exact (@lem1374667 (term84 x) (term85 x)). Qed.
Lemma lem1374669 (x : real) (y : real) : (term86 x y) = (term57 x y).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1374670 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1374671 (x : real) (y : real) : (term87 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1374670) (@lem1374669 x y)). Qed.
Lemma lem1374672 (x : real) (y : real) : (term88 x y) = (term55 x y).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1374673 (x : real) (y : real) : (term89 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1374671 x y) (@lem1374672 x y)). Qed.
Lemma lem1374674 (x : real) : (term90 x) = (term70 x).
Proof. exact (fun_ext (fun y : real => @lem1374673 x y)). Qed.
Lemma lem1374675 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374676 (x : real) : (term82 x) = (term71 x).
Proof. exact (MK_COMB (@lem1374675) (@lem1374674 x)). Qed.
Lemma lem1374677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1374678 (x : real) : (term91 x) = (term92 x).
Proof. exact (MK_COMB (@lem1374677) (@lem1374676 x)). Qed.
Lemma lem1374679 (x : real) (y : real) : (term86 x y) = (term57 x y).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1374680 (x : real) : (term93 x) = (term84 x).
Proof. exact (fun_ext (fun y : real => @lem1374679 x y)). Qed.
Lemma lem1374681 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374682 (x : real) : (term94 x) = (term95 x).
Proof. exact (MK_COMB (@lem1374681) (@lem1374680 x)). Qed.
Lemma lem1374683 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1374684 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem1374683) (@lem1374682 x)). Qed.
Lemma lem1374685 (x : real) (y : real) : (term88 x y) = (term55 x y).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1374686 (x : real) : (term98 x) = (term85 x).
Proof. exact (fun_ext (fun y : real => @lem1374685 x y)). Qed.
Lemma lem1374687 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374688 (x : real) : (term99 x) = (term100 x).
Proof. exact (MK_COMB (@lem1374687) (@lem1374686 x)). Qed.
Lemma lem1374689 (x : real) : (term83 x) = (term101 x).
Proof. exact (MK_COMB (@lem1374684 x) (@lem1374688 x)). Qed.
Lemma lem1374690 (x : real) : ((term82 x) = (term83 x)) = ((term71 x) = (term101 x)).
Proof. exact (MK_COMB (@lem1374678 x) (@lem1374689 x)). Qed.
Lemma lem1374691 (x : real) : (term71 x) = (term101 x).
Proof. exact (EQ_MP (@lem1374690 x) (@lem1374668 x)). Qed.
Lemma lem1374788 : term76 = term102.
Proof. exact (fun_ext (fun x : real => @lem1374691 x)). Qed.
Lemma lem1374789 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374790 : term77 = term103.
Proof. exact (MK_COMB (@lem1374789) (@lem1374788)). Qed.
Lemma lem1374792 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term78 A P Q) = (term79 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1374793 (P : real -> Prop) (Q : real -> Prop) : (term80 P Q) = (term81 P Q).
Proof. exact (@lem1374792 real P Q). Qed.
Lemma lem1374794 : term104 = term105.
Proof. exact (@lem1374793 term106 term107). Qed.
Lemma lem1374795 (x : real) : (term108 x) = (term95 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1374796 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1374797 (x : real) : (term109 x) = (term97 x).
Proof. exact (MK_COMB (@lem1374796) (@lem1374795 x)). Qed.
Lemma lem1374798 (x : real) : (term110 x) = (term100 x).
Proof. exact (eq_refl (term110 x)). Qed.
Lemma lem1374799 (x : real) : (term111 x) = (term101 x).
Proof. exact (MK_COMB (@lem1374797 x) (@lem1374798 x)). Qed.
Lemma lem1374800 : term112 = term102.
Proof. exact (fun_ext (fun x : real => @lem1374799 x)). Qed.
Lemma lem1374801 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374802 : term104 = term103.
Proof. exact (MK_COMB (@lem1374801) (@lem1374800)). Qed.
Lemma lem1374803 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1374804 : term113 = term114.
Proof. exact (MK_COMB (@lem1374803) (@lem1374802)). Qed.
Lemma lem1374805 (x : real) : (term108 x) = (term95 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1374806 : term115 = term106.
Proof. exact (fun_ext (fun x : real => @lem1374805 x)). Qed.
Lemma lem1374807 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374808 : term116 = term117.
Proof. exact (MK_COMB (@lem1374807) (@lem1374806)). Qed.
Lemma lem1374809 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1374810 : term118 = term119.
Proof. exact (MK_COMB (@lem1374809) (@lem1374808)). Qed.
Lemma lem1374811 (x : real) : (term110 x) = (term100 x).
Proof. exact (eq_refl (term110 x)). Qed.
Lemma lem1374812 : term120 = term107.
Proof. exact (fun_ext (fun x : real => @lem1374811 x)). Qed.
Lemma lem1374813 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374814 : term121 = term122.
Proof. exact (MK_COMB (@lem1374813) (@lem1374812)). Qed.
Lemma lem1374815 : term105 = term123.
Proof. exact (MK_COMB (@lem1374810) (@lem1374814)). Qed.
Lemma lem1374816 : (term104 = term105) = (term103 = term123).
Proof. exact (MK_COMB (@lem1374804) (@lem1374815)). Qed.
Lemma lem1374817 : term103 = term123.
Proof. exact (EQ_MP (@lem1374816) (@lem1374794)). Qed.
Lemma lem1374922 : term77 = term123.
Proof. exact (TRANS (@lem1374790) (@lem1374817)). Qed.
Lemma lem1374924 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term79 A P Q) = (term78 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1374925 (P : real -> Prop) (Q : real -> Prop) : (term81 P Q) = (term80 P Q).
Proof. exact (@lem1374924 real P Q). Qed.
Lemma lem1374926 : term105 = term104.
Proof. exact (@lem1374925 term106 term107). Qed.
Lemma lem1374927 (x : real) : (term108 x) = (term95 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1374928 : term115 = term106.
Proof. exact (fun_ext (fun x : real => @lem1374927 x)). Qed.
Lemma lem1374929 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374930 : term116 = term117.
Proof. exact (MK_COMB (@lem1374929) (@lem1374928)). Qed.
Lemma lem1374931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1374932 : term118 = term119.
Proof. exact (MK_COMB (@lem1374931) (@lem1374930)). Qed.
Lemma lem1374933 (x : real) : (term110 x) = (term100 x).
Proof. exact (eq_refl (term110 x)). Qed.
Lemma lem1374934 : term120 = term107.
Proof. exact (fun_ext (fun x : real => @lem1374933 x)). Qed.
Lemma lem1374935 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374936 : term121 = term122.
Proof. exact (MK_COMB (@lem1374935) (@lem1374934)). Qed.
Lemma lem1374937 : term105 = term123.
Proof. exact (MK_COMB (@lem1374932) (@lem1374936)). Qed.
Lemma lem1374938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1374939 : term124 = term125.
Proof. exact (MK_COMB (@lem1374938) (@lem1374937)). Qed.
Lemma lem1374940 (x : real) : (term108 x) = (term95 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1374941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1374942 (x : real) : (term109 x) = (term97 x).
Proof. exact (MK_COMB (@lem1374941) (@lem1374940 x)). Qed.
Lemma lem1374943 (x : real) : (term110 x) = (term100 x).
Proof. exact (eq_refl (term110 x)). Qed.
Lemma lem1374944 (x : real) : (term111 x) = (term101 x).
Proof. exact (MK_COMB (@lem1374942 x) (@lem1374943 x)). Qed.
Lemma lem1374945 : term112 = term102.
Proof. exact (fun_ext (fun x : real => @lem1374944 x)). Qed.
Lemma lem1374946 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374947 : term104 = term103.
Proof. exact (MK_COMB (@lem1374946) (@lem1374945)). Qed.
Lemma lem1374948 : (term105 = term104) = (term123 = term103).
Proof. exact (MK_COMB (@lem1374939) (@lem1374947)). Qed.
Lemma lem1374949 : term123 = term103.
Proof. exact (EQ_MP (@lem1374948) (@lem1374926)). Qed.
Lemma lem1374951 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term79 A P Q) = (term78 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1374952 (P : real -> Prop) (Q : real -> Prop) : (term81 P Q) = (term80 P Q).
Proof. exact (@lem1374951 real P Q). Qed.
Lemma lem1374953 (x : real) : (term83 x) = (term82 x).
Proof. exact (@lem1374952 (term84 x) (term85 x)). Qed.
Lemma lem1374954 (x : real) (y : real) : (term86 x y) = (term57 x y).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1374955 (x : real) : (term93 x) = (term84 x).
Proof. exact (fun_ext (fun y : real => @lem1374954 x y)). Qed.
Lemma lem1374956 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374957 (x : real) : (term94 x) = (term95 x).
Proof. exact (MK_COMB (@lem1374956) (@lem1374955 x)). Qed.
Lemma lem1374958 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1374959 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem1374958) (@lem1374957 x)). Qed.
Lemma lem1374960 (x : real) (y : real) : (term88 x y) = (term55 x y).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1374961 (x : real) : (term98 x) = (term85 x).
Proof. exact (fun_ext (fun y : real => @lem1374960 x y)). Qed.
Lemma lem1374962 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374963 (x : real) : (term99 x) = (term100 x).
Proof. exact (MK_COMB (@lem1374962) (@lem1374961 x)). Qed.
Lemma lem1374964 (x : real) : (term83 x) = (term101 x).
Proof. exact (MK_COMB (@lem1374959 x) (@lem1374963 x)). Qed.
Lemma lem1374965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1374966 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1374965) (@lem1374964 x)). Qed.
Lemma lem1374967 (x : real) (y : real) : (term86 x y) = (term57 x y).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1374968 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1374969 (x : real) (y : real) : (term87 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1374968) (@lem1374967 x y)). Qed.
Lemma lem1374970 (x : real) (y : real) : (term88 x y) = (term55 x y).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1374971 (x : real) (y : real) : (term89 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1374969 x y) (@lem1374970 x y)). Qed.
Lemma lem1374972 (x : real) : (term90 x) = (term70 x).
Proof. exact (fun_ext (fun y : real => @lem1374971 x y)). Qed.
Lemma lem1374973 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374974 (x : real) : (term82 x) = (term71 x).
Proof. exact (MK_COMB (@lem1374973) (@lem1374972 x)). Qed.
Lemma lem1374975 (x : real) : ((term83 x) = (term82 x)) = ((term101 x) = (term71 x)).
Proof. exact (MK_COMB (@lem1374966 x) (@lem1374974 x)). Qed.
Lemma lem1374976 (x : real) : (term101 x) = (term71 x).
Proof. exact (EQ_MP (@lem1374975 x) (@lem1374953 x)). Qed.
Lemma lem1374977 : term102 = term76.
Proof. exact (fun_ext (fun x : real => @lem1374976 x)). Qed.
Lemma lem1374978 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1374979 : term103 = term77.
Proof. exact (MK_COMB (@lem1374978) (@lem1374977)). Qed.
Lemma lem1374980 : term123 = term77.
Proof. exact (TRANS (@lem1374949) (@lem1374979)). Qed.
Lemma lem1374981 : term77 = term77.
Proof. exact (TRANS (@lem1374922) (@lem1374980)). Qed.
Lemma lem1374982 : term26 = term77.
Proof. exact (TRANS (@lem1374660) (@lem1374981)). Qed.
Lemma lem1374983 (h1 : term26) : term77.
Proof. exact (EQ_MP (@lem1374982) (@lem1374611 h1)). Qed.
Lemma lem1374988 (y : real) (x : real) : (term43 y x) = (term43 y x).
Proof. exact (eq_refl (term43 y x)). Qed.
Lemma lem1374989 (x : real) : (term44 x) = (term44 x).
Proof. exact (fun_ext (fun y : real => @lem1374988 y x)). Qed.
Lemma lem1374990 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374991 (x : real) : (term45 x) = (term45 x).
Proof. exact (MK_COMB (@lem1374990) (@lem1374989 x)). Qed.
Lemma lem1374992 : term46 = term46.
Proof. exact (fun_ext (fun x : real => @lem1374991 x)). Qed.
Lemma lem1374993 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375050 : term47 = term47.
Proof. exact (MK_COMB (@lem1374993) (@lem1374992)). Qed.
Lemma lem1375051 (h1 : term47) : term47.
Proof. exact (EQ_MP (@lem1375050) (@lem1374612 h1)). Qed.
Lemma lem1375060 (y : real) (x : real) : (term128 y x) = (term129 y x).
Proof. exact (@lem17045 (real_le x y) (real_le y x)). Qed.
Lemma lem1375065 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1375066 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1375067 (y : real) (x : real) : (term130 y x) = (term131 y x).
Proof. exact (MK_COMB (@lem1375066) (@lem1375060 y x)). Qed.
Lemma lem1375068 (x : real) (y : real) : (term132 x y) = (term133 x y).
Proof. exact (MK_COMB (@lem1375067 y x) (@lem1375065 x y)). Qed.
Lemma lem1375073 (x : real) (y : real) : (term134 x y) = (term134 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1375074 (x : real) (y : real) : (term135 x y) = (term136 x y).
Proof. exact (MK_COMB (@lem1375073 x y) (@lem1375068 x y)). Qed.
Lemma lem1375075 (x : real) (y : real) : ((term39 y x) = (x = y)) = (term135 x y).
Proof. exact (@lem17784 (term39 y x) (x = y)). Qed.
Lemma lem1375076 (x : real) (y : real) : ((term39 y x) = (x = y)) = (term136 x y).
Proof. exact (TRANS (@lem1375075 x y) (@lem1375074 x y)). Qed.
Lemma lem1375077 (x : real) : (term40 x) = (term137 x).
Proof. exact (fun_ext (fun y : real => @lem1375076 x y)). Qed.
Lemma lem1375078 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375079 (x : real) : (term41 x) = (term138 x).
Proof. exact (MK_COMB (@lem1375078) (@lem1375077 x)). Qed.
Lemma lem1375080 : term42 = term139.
Proof. exact (fun_ext (fun x : real => @lem1375079 x)). Qed.
Lemma lem1375081 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375082 : term33 = term140.
Proof. exact (MK_COMB (@lem1375081) (@lem1375080)). Qed.
Lemma lem1375088 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1375089 (P : real -> Prop) (Q : real -> Prop) : (term143 P Q) = (term144 P Q).
Proof. exact (@lem1375088 real P Q). Qed.
Lemma lem1375090 (x : real) : (term145 x) = (term146 x).
Proof. exact (@lem1375089 (term147 x) (term148 x)). Qed.
Lemma lem1375091 (x : real) (y : real) : (term149 x y) = (term150 x y).
Proof. exact (eq_refl (term149 x y)). Qed.
Lemma lem1375092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1375093 (x : real) (y : real) : (term151 x y) = (term134 x y).
Proof. exact (MK_COMB (@lem1375092) (@lem1375091 x y)). Qed.
Lemma lem1375094 (x : real) (y : real) : (term152 x y) = (term133 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem1375095 (x : real) (y : real) : (term153 x y) = (term136 x y).
Proof. exact (MK_COMB (@lem1375093 x y) (@lem1375094 x y)). Qed.
Lemma lem1375096 (x : real) : (term154 x) = (term137 x).
Proof. exact (fun_ext (fun y : real => @lem1375095 x y)). Qed.
Lemma lem1375097 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375098 (x : real) : (term145 x) = (term138 x).
Proof. exact (MK_COMB (@lem1375097) (@lem1375096 x)). Qed.
Lemma lem1375099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1375100 (x : real) : (term155 x) = (term156 x).
Proof. exact (MK_COMB (@lem1375099) (@lem1375098 x)). Qed.
Lemma lem1375101 (x : real) (y : real) : (term149 x y) = (term150 x y).
Proof. exact (eq_refl (term149 x y)). Qed.
Lemma lem1375102 (x : real) : (term157 x) = (term147 x).
Proof. exact (fun_ext (fun y : real => @lem1375101 x y)). Qed.
Lemma lem1375103 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375104 (x : real) : (term158 x) = (term159 x).
Proof. exact (MK_COMB (@lem1375103) (@lem1375102 x)). Qed.
Lemma lem1375105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1375106 (x : real) : (term160 x) = (term161 x).
Proof. exact (MK_COMB (@lem1375105) (@lem1375104 x)). Qed.
Lemma lem1375107 (x : real) (y : real) : (term152 x y) = (term133 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem1375108 (x : real) : (term162 x) = (term148 x).
Proof. exact (fun_ext (fun y : real => @lem1375107 x y)). Qed.
Lemma lem1375109 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375110 (x : real) : (term163 x) = (term164 x).
Proof. exact (MK_COMB (@lem1375109) (@lem1375108 x)). Qed.
Lemma lem1375111 (x : real) : (term146 x) = (term165 x).
Proof. exact (MK_COMB (@lem1375106 x) (@lem1375110 x)). Qed.
Lemma lem1375112 (x : real) : ((term145 x) = (term146 x)) = ((term138 x) = (term165 x)).
Proof. exact (MK_COMB (@lem1375100 x) (@lem1375111 x)). Qed.
Lemma lem1375113 (x : real) : (term138 x) = (term165 x).
Proof. exact (EQ_MP (@lem1375112 x) (@lem1375090 x)). Qed.
Lemma lem1375210 : term139 = term166.
Proof. exact (fun_ext (fun x : real => @lem1375113 x)). Qed.
Lemma lem1375211 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375212 : term140 = term167.
Proof. exact (MK_COMB (@lem1375211) (@lem1375210)). Qed.
Lemma lem1375214 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1375215 (P : real -> Prop) (Q : real -> Prop) : (term143 P Q) = (term144 P Q).
Proof. exact (@lem1375214 real P Q). Qed.
Lemma lem1375216 : term168 = term169.
Proof. exact (@lem1375215 term170 term171). Qed.
Lemma lem1375217 (x : real) : (term172 x) = (term159 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1375218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1375219 (x : real) : (term173 x) = (term161 x).
Proof. exact (MK_COMB (@lem1375218) (@lem1375217 x)). Qed.
Lemma lem1375220 (x : real) : (term174 x) = (term164 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem1375221 (x : real) : (term175 x) = (term165 x).
Proof. exact (MK_COMB (@lem1375219 x) (@lem1375220 x)). Qed.
Lemma lem1375222 : term176 = term166.
Proof. exact (fun_ext (fun x : real => @lem1375221 x)). Qed.
Lemma lem1375223 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375224 : term168 = term167.
Proof. exact (MK_COMB (@lem1375223) (@lem1375222)). Qed.
Lemma lem1375225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1375226 : term177 = term178.
Proof. exact (MK_COMB (@lem1375225) (@lem1375224)). Qed.
Lemma lem1375227 (x : real) : (term172 x) = (term159 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1375228 : term179 = term170.
Proof. exact (fun_ext (fun x : real => @lem1375227 x)). Qed.
Lemma lem1375229 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375230 : term180 = term181.
Proof. exact (MK_COMB (@lem1375229) (@lem1375228)). Qed.
Lemma lem1375231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1375232 : term182 = term183.
Proof. exact (MK_COMB (@lem1375231) (@lem1375230)). Qed.
Lemma lem1375233 (x : real) : (term174 x) = (term164 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem1375234 : term184 = term171.
Proof. exact (fun_ext (fun x : real => @lem1375233 x)). Qed.
Lemma lem1375235 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375236 : term185 = term186.
Proof. exact (MK_COMB (@lem1375235) (@lem1375234)). Qed.
Lemma lem1375237 : term169 = term187.
Proof. exact (MK_COMB (@lem1375232) (@lem1375236)). Qed.
Lemma lem1375238 : (term168 = term169) = (term167 = term187).
Proof. exact (MK_COMB (@lem1375226) (@lem1375237)). Qed.
Lemma lem1375239 : term167 = term187.
Proof. exact (EQ_MP (@lem1375238) (@lem1375216)). Qed.
Lemma lem1375346 : term140 = term187.
Proof. exact (TRANS (@lem1375212) (@lem1375239)). Qed.
Lemma lem1375347 : term33 = term187.
Proof. exact (TRANS (@lem1375082) (@lem1375346)). Qed.
Lemma lem1375348 (h1 : term33) : term187.
Proof. exact (EQ_MP (@lem1375347) (@lem1374613 h1)). Qed.
Lemma lem1375349 (x : real) (h1 : term71 x) : term71 x.
Proof. exact (h1). Qed.
Lemma lem1375363 (y : real) (x : real) : (term43 y x) = (term43 y x).
Proof. exact (eq_refl (term43 y x)). Qed.
Lemma lem1375364 (x : real) : (term44 x) = (term44 x).
Proof. exact (fun_ext (fun y : real => @lem1375363 y x)). Qed.
Lemma lem1375365 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375366 (x : real) : (term45 x) = (term45 x).
Proof. exact (MK_COMB (@lem1375365) (@lem1375364 x)). Qed.
Lemma lem1375367 : term46 = term46.
Proof. exact (fun_ext (fun x : real => @lem1375366 x)). Qed.
Lemma lem1375368 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375369 : term47 = term47.
Proof. exact (MK_COMB (@lem1375368) (@lem1375367)). Qed.
Lemma lem1375370 (h1 : term47) : term47.
Proof. exact (EQ_MP (@lem1375369) (@lem1375051 h1)). Qed.
Lemma lem1375395 (x : real) (y : real) : (term133 x y) = (term133 x y).
Proof. exact (eq_refl (term133 x y)). Qed.
Lemma lem1375396 (x : real) : (term148 x) = (term148 x).
Proof. exact (fun_ext (fun y : real => @lem1375395 x y)). Qed.
Lemma lem1375397 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375398 (x : real) : (term164 x) = (term164 x).
Proof. exact (MK_COMB (@lem1375397) (@lem1375396 x)). Qed.
Lemma lem1375399 : term171 = term171.
Proof. exact (fun_ext (fun x : real => @lem1375398 x)). Qed.
Lemma lem1375400 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375401 : term186 = term186.
Proof. exact (MK_COMB (@lem1375400) (@lem1375399)). Qed.
Lemma lem1375424 (x : real) (y : real) : (term150 x y) = (term150 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1375425 (x : real) : (term147 x) = (term147 x).
Proof. exact (fun_ext (fun y : real => @lem1375424 x y)). Qed.
Lemma lem1375426 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375427 (x : real) : (term159 x) = (term159 x).
Proof. exact (MK_COMB (@lem1375426) (@lem1375425 x)). Qed.
Lemma lem1375428 : term170 = term170.
Proof. exact (fun_ext (fun x : real => @lem1375427 x)). Qed.
Lemma lem1375429 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375430 : term181 = term181.
Proof. exact (MK_COMB (@lem1375429) (@lem1375428)). Qed.
Lemma lem1375431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1375432 : term183 = term183.
Proof. exact (MK_COMB (@lem1375431) (@lem1375430)). Qed.
Lemma lem1375433 : term187 = term187.
Proof. exact (MK_COMB (@lem1375432) (@lem1375401)). Qed.
Lemma lem1375434 (h1 : term33) : term187.
Proof. exact (EQ_MP (@lem1375433) (@lem1375348 h1)). Qed.
Lemma lem1375486 (x : real) (y : real) (h1 : term61 x y) : term61 x y.
Proof. exact (h1). Qed.
Lemma lem1375487 (h1 : term33) : term186.
Proof. exact (proj2 (@lem1375434 h1)). Qed.
Lemma lem1375488 (h1 : term33) : term181.
Proof. exact (proj1 (@lem1375434 h1)). Qed.
Lemma lem1375489 (x : real) (y : real) (h1 : term57 x y) : term57 x y.
Proof. exact (h1). Qed.
Lemma lem1375490 (x : real) (y : real) (h1 : term55 x y) : term55 x y.
Proof. exact (h1). Qed.
Lemma lem1375491 (x : real) (y : real) (h1 : term57 x y) : term53 x y.
Proof. exact (proj2 (@lem1375489 x y h1)). Qed.
Lemma lem1375495 (x : real) (y : real) (h1 : term55 x y) : term14 x y.
Proof. exact (proj2 (@lem1375490 x y h1)). Qed.
Lemma lem1375554 (x : real) (y : real) : (term133 x y) = (term133 x y).
Proof. exact (eq_refl (term133 x y)). Qed.
Lemma lem1375555 (x : real) : (term148 x) = (term148 x).
Proof. exact (fun_ext (fun y : real => @lem1375554 x y)). Qed.
Lemma lem1375556 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375557 (x : real) : (term164 x) = (term164 x).
Proof. exact (MK_COMB (@lem1375556) (@lem1375555 x)). Qed.
Lemma lem1375558 : term171 = term171.
Proof. exact (fun_ext (fun x : real => @lem1375557 x)). Qed.
Lemma lem1375559 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375561 : term186 = term186.
Proof. exact (MK_COMB (@lem1375559) (@lem1375558)). Qed.
Lemma lem1375562 (h1 : term33) : term186.
Proof. exact (EQ_MP (@lem1375561) (@lem1375487 h1)). Qed.
Lemma lem1375582 (y : real) (x : real) : (term43 y x) = (term43 y x).
Proof. exact (eq_refl (term43 y x)). Qed.
Lemma lem1375583 (x : real) : (term44 x) = (term44 x).
Proof. exact (fun_ext (fun y : real => @lem1375582 y x)). Qed.
Lemma lem1375584 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375585 (x : real) : (term45 x) = (term45 x).
Proof. exact (MK_COMB (@lem1375584) (@lem1375583 x)). Qed.
Lemma lem1375586 : term46 = term46.
Proof. exact (fun_ext (fun x : real => @lem1375585 x)). Qed.
Lemma lem1375587 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375589 : term47 = term47.
Proof. exact (MK_COMB (@lem1375587) (@lem1375586)). Qed.
Lemma lem1375590 (h1 : term47) : term47.
Proof. exact (EQ_MP (@lem1375589) (@lem1375370 h1)). Qed.
Lemma lem1375646 (y : real) (x : real) (h1 : term10 y x) : term10 y x.
Proof. exact (h1). Qed.
Lemma lem1375680 (x : real) (y : real) : (term150 x y) = (term188 x y).
Proof. exact (@lem19699 (real_le x y) (real_le y x) (term49 x y)). Qed.
Lemma lem1375681 (x : real) : (term147 x) = (term189 x).
Proof. exact (fun_ext (fun y : real => @lem1375680 x y)). Qed.
Lemma lem1375682 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375683 (x : real) : (term159 x) = (term190 x).
Proof. exact (MK_COMB (@lem1375682) (@lem1375681 x)). Qed.
Lemma lem1375684 : term170 = term191.
Proof. exact (fun_ext (fun x : real => @lem1375683 x)). Qed.
Lemma lem1375685 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1375687 : term181 = term192.
Proof. exact (MK_COMB (@lem1375685) (@lem1375684)). Qed.
Lemma lem1375688 (h1 : term33) : term192.
Proof. exact (EQ_MP (@lem1375687) (@lem1375488 h1)). Qed.
Lemma lem1375718 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1375731 (_24340 : real) (h1 : term33) : term174 _24340.
Proof. exact (@lem1375562 h1 _24340). Qed.
Lemma lem1375732 (_24340 : real) : (term174 _24340) = (term164 _24340).
Proof. exact (eq_refl (term174 _24340)). Qed.
Lemma lem1375733 (_24340 : real) (h1 : term33) : term164 _24340.
Proof. exact (EQ_MP (@lem1375732 _24340) (@lem1375731 _24340 h1)). Qed.
Lemma lem1375734 (_24340 : real) (_24341 : real) (h1 : term33) : term152 _24340 _24341.
Proof. exact (@lem1375733 _24340 h1 _24341). Qed.
Lemma lem1375735 (_24340 : real) (_24341 : real) : (term152 _24340 _24341) = (term133 _24340 _24341).
Proof. exact (eq_refl (term152 _24340 _24341)). Qed.
Lemma lem1375736 (_24340 : real) (_24341 : real) (h1 : term33) : term133 _24340 _24341.
Proof. exact (EQ_MP (@lem1375735 _24340 _24341) (@lem1375734 _24340 _24341 h1)). Qed.
Lemma lem1375737 (_24342 : real) (h1 : term47) : term193 _24342.
Proof. exact (@lem1375590 h1 _24342). Qed.
Lemma lem1375738 (_24342 : real) : (term193 _24342) = (term45 _24342).
Proof. exact (eq_refl (term193 _24342)). Qed.
Lemma lem1375739 (_24342 : real) (h1 : term47) : term45 _24342.
Proof. exact (EQ_MP (@lem1375738 _24342) (@lem1375737 _24342 h1)). Qed.
Lemma lem1375740 (_24342 : real) (_24343 : real) (h1 : term47) : term194 _24342 _24343.
Proof. exact (@lem1375739 _24342 h1 _24343). Qed.
Lemma lem1375741 (_24343 : real) (_24342 : real) : (term194 _24342 _24343) = (term43 _24343 _24342).
Proof. exact (eq_refl (term194 _24342 _24343)). Qed.
Lemma lem1375761 (_24350 : real) (h1 : term33) : term195 _24350.
Proof. exact (@lem1375688 h1 _24350). Qed.
Lemma lem1375762 (_24350 : real) : (term195 _24350) = (term190 _24350).
Proof. exact (eq_refl (term195 _24350)). Qed.
Lemma lem1375763 (_24350 : real) (h1 : term33) : term190 _24350.
Proof. exact (EQ_MP (@lem1375762 _24350) (@lem1375761 _24350 h1)). Qed.
Lemma lem1375764 (_24350 : real) (_24351 : real) (h1 : term33) : term196 _24350 _24351.
Proof. exact (@lem1375763 _24350 h1 _24351). Qed.
Lemma lem1375765 (_24350 : real) (_24351 : real) : (term196 _24350 _24351) = (term188 _24350 _24351).
Proof. exact (eq_refl (term196 _24350 _24351)). Qed.
Lemma lem1375766 (_24350 : real) (_24351 : real) (h1 : term33) : term188 _24350 _24351.
Proof. exact (EQ_MP (@lem1375765 _24350 _24351) (@lem1375764 _24350 _24351 h1)). Qed.
Lemma lem1375795 (_24340 : real) (_24341 : real) : (term133 _24340 _24341) = (term197 _24340 _24341).
Proof. exact (@lem1374347 (term10 _24340 _24341) (term10 _24341 _24340) (_24340 = _24341)). Qed.
Lemma lem1375796 (_24340 : real) (_24341 : real) (h1 : term33) : term197 _24340 _24341.
Proof. exact (EQ_MP (@lem1375795 _24340 _24341) (@lem1375736 _24340 _24341 h1)). Qed.
Lemma lem1375802 (x : real) (y : real) (h1 : term57 x y) : term49 x y.
Proof. exact (proj2 (@lem1375491 x y h1)). Qed.
Lemma lem1375820 (_24343 : real) (_24342 : real) (h1 : term47) : term43 _24343 _24342.
Proof. exact (EQ_MP (@lem1375741 _24343 _24342) (@lem1375740 _24342 _24343 h1)). Qed.
Lemma lem1375836 (y : real) (x : real) (h1 : term10 y x) : term10 y x.
Proof. exact (h1). Qed.
Lemma lem1375868 (x : real) (y : real) (h1 : term55 x y) : term10 x y.
Proof. exact (proj1 (@lem1375490 x y h1)). Qed.
Lemma lem1375870 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1375925 (y : real) : (term198 y) = (term198 y).
Proof. exact (eq_refl (term198 y)). Qed.
Lemma lem1375926 (x : real) (y : real) (h1 : x = y) : (term199 y x) = (term200 y).
Proof. exact (MK_COMB (@lem1375925 y) (@lem1375870 x y h1)). Qed.
Lemma lem1375927 (y : real) : (term200 y) = (term201 y).
Proof. exact (eq_refl (term200 y)). Qed.
Lemma lem1375928 (y : real) (x : real) : (term202 y x) = (term202 y x).
Proof. exact (eq_refl (term202 y x)). Qed.
Lemma lem1375929 (x : real) (y : real) : ((term199 y x) = (term200 y)) = ((term199 y x) = (term201 y)).
Proof. exact (MK_COMB (@lem1375928 y x) (@lem1375927 y)). Qed.
Lemma lem1375930 (x : real) (y : real) : (term199 y x) = (term10 x y).
Proof. exact (eq_refl (term199 y x)). Qed.
Lemma lem1375931 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1375932 (x : real) (y : real) : (term202 y x) = (term203 x y).
Proof. exact (MK_COMB (@lem1375931) (@lem1375930 x y)). Qed.
Lemma lem1375933 (y : real) : (term201 y) = (term201 y).
Proof. exact (eq_refl (term201 y)). Qed.
Lemma lem1375934 (x : real) (y : real) : ((term199 y x) = (term201 y)) = ((term10 x y) = (term201 y)).
Proof. exact (MK_COMB (@lem1375932 x y) (@lem1375933 y)). Qed.
Lemma lem1375935 (x : real) (y : real) : ((term199 y x) = (term200 y)) = ((term10 x y) = (term201 y)).
Proof. exact (TRANS (@lem1375929 x y) (@lem1375934 x y)). Qed.
Lemma lem1375936 (x : real) (y : real) (h1 : x = y) : (term10 x y) = (term201 y).
Proof. exact (EQ_MP (@lem1375935 x y) (@lem1375926 x y h1)). Qed.
Lemma lem1375937 (x : real) (y : real) (h1 : term55 x y) (h2 : x = y) : term201 y.
Proof. exact (EQ_MP (@lem1375936 x y h2) (@lem1375868 x y h1)). Qed.
Lemma lem1375965 (_24350 : real) (_24351 : real) (h1 : term33) : term204 _24350 _24351.
Proof. exact (proj2 (@lem1375766 _24350 _24351 h1)). Qed.
Lemma lem1375988 (x : real) (y : real) (h1 : term57 x y) : real_le x y.
Proof. exact (proj1 (@lem1375489 x y h1)). Qed.
Lemma lem1375989 (x : real) (y : real) (h1 : term57 x y) : term205 x y.
Proof. exact (fun h0 : term10 x y => @lem1375988 x y h1). Qed.
Lemma lem1375991 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1375992 (x : real) (y : real) : (term205 x y) = (real_le x y).
Proof. exact (@lem1375991 (real_le x y)). Qed.
Lemma lem1375993 (x : real) (y : real) (h1 : term57 x y) : real_le x y.
Proof. exact (EQ_MP (@lem1375992 x y) (@lem1375989 x y h1)). Qed.
Lemma lem1375995 (x : real) (y : real) (h1 : term57 x y) : real_le y x.
Proof. exact (proj1 (@lem1375491 x y h1)). Qed.
Lemma lem1375996 (x : real) (y : real) (h1 : term57 x y) : term205 y x.
Proof. exact (fun h0 : term10 y x => @lem1375995 x y h1). Qed.
Lemma lem1375998 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1375999 (y : real) (x : real) : (term205 y x) = (real_le y x).
Proof. exact (@lem1375998 (real_le y x)). Qed.
Lemma lem1376000 (x : real) (y : real) (h1 : term57 x y) : real_le y x.
Proof. exact (EQ_MP (@lem1375999 y x) (@lem1375996 x y h1)). Qed.
Lemma lem1376016 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1376017 (_24341 : real) (_24340 : real) : (term14 _24340 _24341) = (term207 _24341 _24340).
Proof. exact (@lem1376016 (_24340 = _24341) (term10 _24341 _24340)). Qed.
Lemma lem1376025 (_24340 : real) (_24341 : real) : (term12 _24340 _24341) = (term12 _24340 _24341).
Proof. exact (eq_refl (term12 _24340 _24341)). Qed.
Lemma lem1376026 (_24341 : real) (_24340 : real) : (term197 _24340 _24341) = (term208 _24341 _24340).
Proof. exact (MK_COMB (@lem1376025 _24340 _24341) (@lem1376017 _24341 _24340)). Qed.
Lemma lem1376030 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1376031 (_24341 : real) (_24340 : real) : (term208 _24341 _24340) = (term209 _24341 _24340).
Proof. exact (@lem1376030 (_24340 = _24341) (term10 _24340 _24341) (term10 _24341 _24340)). Qed.
Lemma lem1376049 (_24341 : real) (_24340 : real) : (term197 _24340 _24341) = (term209 _24341 _24340).
Proof. exact (TRANS (@lem1376026 _24341 _24340) (@lem1376031 _24341 _24340)). Qed.
Lemma lem1376050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1376051 (_24341 : real) (_24340 : real) : (term210 _24340 _24341) = (term211 _24341 _24340).
Proof. exact (MK_COMB (@lem1376050) (@lem1376049 _24341 _24340)). Qed.
Lemma lem1376069 (_24341 : real) (_24340 : real) : (term209 _24341 _24340) = (term209 _24341 _24340).
Proof. exact (eq_refl (term209 _24341 _24340)). Qed.
Lemma lem1376070 (_24341 : real) (_24340 : real) : ((term197 _24340 _24341) = (term209 _24341 _24340)) = ((term209 _24341 _24340) = (term209 _24341 _24340)).
Proof. exact (MK_COMB (@lem1376051 _24341 _24340) (@lem1376069 _24341 _24340)). Qed.
Lemma lem1376072 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1376073 (x : Prop) : (x = x) = True.
Proof. exact (@lem1376072 Prop x). Qed.
Lemma lem1376074 (_24341 : real) (_24340 : real) : ((term209 _24341 _24340) = (term209 _24341 _24340)) = True.
Proof. exact (@lem1376073 (term209 _24341 _24340)). Qed.
Lemma lem1376075 (_24341 : real) (_24340 : real) : ((term197 _24340 _24341) = (term209 _24341 _24340)) = True.
Proof. exact (TRANS (@lem1376070 _24341 _24340) (@lem1376074 _24341 _24340)). Qed.
Lemma lem1376076 (_24341 : real) (_24340 : real) : True = ((term197 _24340 _24341) = (term209 _24341 _24340)).
Proof. exact (SYM (@lem1376075 _24341 _24340)). Qed.
Lemma lem1376077 (_24341 : real) (_24340 : real) : (term197 _24340 _24341) = (term209 _24341 _24340).
Proof. exact (EQ_MP (@lem1376076 _24341 _24340) (@lem0)). Qed.
Lemma lem1376078 (_24341 : real) (_24340 : real) (h1 : term33) : term209 _24341 _24340.
Proof. exact (EQ_MP (@lem1376077 _24341 _24340) (@lem1375796 _24340 _24341 h1)). Qed.
Lemma lem1376080 (b : Prop) (a : Prop) : (a \/ b) = (term212 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1376081 (_24340 : real) (_24341 : real) : (term209 _24341 _24340) = (term213 _24340 _24341).
Proof. exact (@lem1376080 (term129 _24341 _24340) (_24340 = _24341)). Qed.
Lemma lem1376083 (a : Prop) (b : Prop) : (term214 a b) = (term215 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1376084 (_24341 : real) (_24340 : real) : (term216 _24341 _24340) = (term217 _24341 _24340).
Proof. exact (@lem1376083 (term10 _24340 _24341) (term10 _24341 _24340)). Qed.
Lemma lem1376086 (a : Prop) : (term218 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1376087 (_24340 : real) (_24341 : real) : (term48 _24340 _24341) = (real_le _24340 _24341).
Proof. exact (@lem1376086 (real_le _24340 _24341)). Qed.
Lemma lem1376088 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1376089 (_24340 : real) (_24341 : real) : (term50 _24340 _24341) = (term51 _24340 _24341).
Proof. exact (MK_COMB (@lem1376088) (@lem1376087 _24340 _24341)). Qed.
Lemma lem1376091 (a : Prop) : (term218 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1376092 (_24341 : real) (_24340 : real) : (term48 _24341 _24340) = (real_le _24341 _24340).
Proof. exact (@lem1376091 (real_le _24341 _24340)). Qed.
Lemma lem1376093 (_24341 : real) (_24340 : real) : (term217 _24341 _24340) = (term39 _24341 _24340).
Proof. exact (MK_COMB (@lem1376089 _24340 _24341) (@lem1376092 _24341 _24340)). Qed.
Lemma lem1376094 (_24341 : real) (_24340 : real) : (term216 _24341 _24340) = (term39 _24341 _24340).
Proof. exact (TRANS (@lem1376084 _24341 _24340) (@lem1376093 _24341 _24340)). Qed.
Lemma lem1376095 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1376096 (_24341 : real) (_24340 : real) : (term219 _24341 _24340) = (term220 _24341 _24340).
Proof. exact (MK_COMB (@lem1376095) (@lem1376094 _24341 _24340)). Qed.
Lemma lem1376097 (_24340 : real) (_24341 : real) : (_24340 = _24341) = (_24340 = _24341).
Proof. exact (eq_refl (_24340 = _24341)). Qed.
Lemma lem1376098 (_24340 : real) (_24341 : real) : (term213 _24340 _24341) = (term221 _24340 _24341).
Proof. exact (MK_COMB (@lem1376096 _24341 _24340) (@lem1376097 _24340 _24341)). Qed.
Lemma lem1376099 (_24340 : real) (_24341 : real) : (term209 _24341 _24340) = (term221 _24340 _24341).
Proof. exact (TRANS (@lem1376081 _24340 _24341) (@lem1376098 _24340 _24341)). Qed.
Lemma lem1376101 (x : real) (y : real) (h1 : term57 x y) : term39 y x.
Proof. exact (conj (@lem1375993 x y h1) (@lem1376000 x y h1)). Qed.
Lemma lem1376103 (_24340 : real) (_24341 : real) (h1 : term33) : term221 _24340 _24341.
Proof. exact (EQ_MP (@lem1376099 _24340 _24341) (@lem1376078 _24341 _24340 h1)). Qed.
Lemma lem1376104 (x : real) (y : real) (h1 : term33) : term221 x y.
Proof. exact (@lem1376103 x y h1). Qed.
Lemma lem1376107 (x : real) (y : real) (h1 : term33) (h2 : term57 x y) : x = y.
Proof. exact (@lem1376104 x y h1 (@lem1376101 x y h2)). Qed.
Lemma lem1376108 (x : real) (y : real) (h1 : term33) (h2 : term57 x y) : term222 x y.
Proof. exact (fun h0 : term49 x y => @lem1376107 x y h1 h2). Qed.
Lemma lem1376110 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1376111 (x : real) (y : real) : (term222 x y) = (x = y).
Proof. exact (@lem1376110 (x = y)). Qed.
Lemma lem1376112 (x : real) (y : real) (h1 : term33) (h2 : term57 x y) : x = y.
Proof. exact (EQ_MP (@lem1376111 x y) (@lem1376108 x y h1 h2)). Qed.
Lemma lem1376115 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1376117 (x : real) (y : real) : (term49 x y) = (term223 x y).
Proof. exact (@lem1376115 (x = y)). Qed.
Lemma lem1376120 (x : real) (y : real) (h1 : term57 x y) : term223 x y.
Proof. exact (EQ_MP (@lem1376117 x y) (@lem1375802 x y h1)). Qed.
Lemma lem1376123 (x : real) (y : real) (h1 : term33) (h2 : term57 x y) : False.
Proof. exact (@lem1376120 x y h2 (@lem1376112 x y h1 h2)). Qed.
Lemma lem1376124 (x : real) (y : real) (h1 : term33) (h2 : term57 x y) : term224.
Proof. exact (fun h0 : ~ False => @lem1376123 x y h1 h2). Qed.
Lemma lem1376126 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1376127 : term224 = False.
Proof. exact (@lem1376126 False). Qed.
Lemma lem1376128 (x : real) (y : real) (h1 : term33) (h2 : term57 x y) : False.
Proof. exact (EQ_MP (@lem1376127) (@lem1376124 x y h1 h2)). Qed.
Lemma lem1376151 (x : real) (y : real) (h1 : term55 x y) : term10 x y.
Proof. exact (proj1 (@lem1375490 x y h1)). Qed.
Lemma lem1376152 (x : real) (y : real) (h1 : term55 x y) : term225 x y.
Proof. exact (fun h0 : real_le x y => @lem1376151 x y h1). Qed.
Lemma lem1376154 (p : Prop) : (term226 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1376155 (x : real) (y : real) : (term225 x y) = (term10 x y).
Proof. exact (@lem1376154 (real_le x y)). Qed.
Lemma lem1376156 (x : real) (y : real) (h1 : term55 x y) : term10 x y.
Proof. exact (EQ_MP (@lem1376155 x y) (@lem1376152 x y h1)). Qed.
Lemma lem1376167 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1376168 (_24343 : real) (_24342 : real) : (term43 _24342 _24343) = (term43 _24343 _24342).
Proof. exact (@lem1376167 (real_le _24342 _24343) (real_le _24343 _24342)). Qed.
Lemma lem1376174 (_24343 : real) (_24342 : real) : (term227 _24343 _24342) = (term227 _24343 _24342).
Proof. exact (eq_refl (term227 _24343 _24342)). Qed.
Lemma lem1376175 (_24343 : real) (_24342 : real) : ((term43 _24343 _24342) = (term43 _24342 _24343)) = ((term43 _24343 _24342) = (term43 _24343 _24342)).
Proof. exact (MK_COMB (@lem1376174 _24343 _24342) (@lem1376168 _24343 _24342)). Qed.
Lemma lem1376177 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1376178 (x : Prop) : (x = x) = True.
Proof. exact (@lem1376177 Prop x). Qed.
Lemma lem1376179 (_24343 : real) (_24342 : real) : ((term43 _24343 _24342) = (term43 _24343 _24342)) = True.
Proof. exact (@lem1376178 (term43 _24343 _24342)). Qed.
Lemma lem1376180 (_24342 : real) (_24343 : real) : ((term43 _24343 _24342) = (term43 _24342 _24343)) = True.
Proof. exact (TRANS (@lem1376175 _24343 _24342) (@lem1376179 _24343 _24342)). Qed.
Lemma lem1376181 (_24342 : real) (_24343 : real) : True = ((term43 _24343 _24342) = (term43 _24342 _24343)).
Proof. exact (SYM (@lem1376180 _24342 _24343)). Qed.
Lemma lem1376182 (_24342 : real) (_24343 : real) : (term43 _24343 _24342) = (term43 _24342 _24343).
Proof. exact (EQ_MP (@lem1376181 _24342 _24343) (@lem0)). Qed.
Lemma lem1376183 (_24342 : real) (_24343 : real) (h1 : term47) : term43 _24342 _24343.
Proof. exact (EQ_MP (@lem1376182 _24342 _24343) (@lem1375820 _24343 _24342 h1)). Qed.
Lemma lem1376185 (b : Prop) (a : Prop) : (a \/ b) = (term212 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1376188 (_24343 : real) (_24342 : real) : (term43 _24342 _24343) = (term228 _24343 _24342).
Proof. exact (@lem1376185 (real_le _24342 _24343) (real_le _24343 _24342)). Qed.
Lemma lem1376191 (_24343 : real) (_24342 : real) (h1 : term47) : term228 _24343 _24342.
Proof. exact (EQ_MP (@lem1376188 _24343 _24342) (@lem1376183 _24342 _24343 h1)). Qed.
Lemma lem1376192 (y : real) (x : real) (h1 : term47) : term228 y x.
Proof. exact (@lem1376191 y x h1). Qed.
Lemma lem1376195 (x : real) (y : real) (h1 : term47) (h2 : term55 x y) : real_le y x.
Proof. exact (@lem1376192 y x h1 (@lem1376156 x y h2)). Qed.
Lemma lem1376196 (x : real) (y : real) (h1 : term47) (h2 : term55 x y) : term205 y x.
Proof. exact (fun h0 : term10 y x => @lem1376195 x y h1 h2). Qed.
Lemma lem1376198 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1376199 (y : real) (x : real) : (term205 y x) = (real_le y x).
Proof. exact (@lem1376198 (real_le y x)). Qed.
Lemma lem1376200 (x : real) (y : real) (h1 : term47) (h2 : term55 x y) : real_le y x.
Proof. exact (EQ_MP (@lem1376199 y x) (@lem1376196 x y h1 h2)). Qed.
Lemma lem1376203 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1376205 (y : real) (x : real) : (term10 y x) = (term229 y x).
Proof. exact (@lem1376203 (real_le y x)). Qed.
Lemma lem1376208 (y : real) (x : real) (h1 : term10 y x) : term229 y x.
Proof. exact (EQ_MP (@lem1376205 y x) (@lem1375836 y x h1)). Qed.
Lemma lem1376211 (x : real) (y : real) (h1 : term47) (h2 : term10 y x) (h3 : term55 x y) : False.
Proof. exact (@lem1376208 y x h2 (@lem1376200 x y h1 h3)). Qed.
Lemma lem1376212 (x : real) (y : real) (h1 : term47) (h2 : term10 y x) (h3 : term55 x y) : term224.
Proof. exact (fun h0 : ~ False => @lem1376211 x y h1 h2 h3). Qed.
Lemma lem1376214 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1376215 : term224 = False.
Proof. exact (@lem1376214 False). Qed.
Lemma lem1376216 (x : real) (y : real) (h1 : term47) (h2 : term10 y x) (h3 : term55 x y) : False.
Proof. exact (EQ_MP (@lem1376215) (@lem1376212 x y h1 h2 h3)). Qed.
Lemma lem1376239 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1376240 (y : real) : y = y.
Proof. exact (@lem1376239 y). Qed.
Lemma lem1376241 (y : real) : term230 y.
Proof. exact (fun h0 : term231 y => @lem1376240 y). Qed.
Lemma lem1376243 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1376244 (y : real) : (term230 y) = (y = y).
Proof. exact (@lem1376243 (y = y)). Qed.
Lemma lem1376245 (y : real) : y = y.
Proof. exact (EQ_MP (@lem1376244 y) (@lem1376241 y)). Qed.
Lemma lem1376247 (b : Prop) (a : Prop) : (a \/ b) = (term212 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1376248 (_24351 : real) (_24350 : real) : (term204 _24350 _24351) = (term232 _24351 _24350).
Proof. exact (@lem1376247 (term49 _24350 _24351) (real_le _24351 _24350)). Qed.
Lemma lem1376250 (a : Prop) : (term218 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1376251 (_24350 : real) (_24351 : real) : (term233 _24350 _24351) = (_24350 = _24351).
Proof. exact (@lem1376250 (_24350 = _24351)). Qed.
Lemma lem1376252 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1376253 (_24350 : real) (_24351 : real) : (term234 _24350 _24351) = (term235 _24350 _24351).
Proof. exact (MK_COMB (@lem1376252) (@lem1376251 _24350 _24351)). Qed.
Lemma lem1376254 (_24351 : real) (_24350 : real) : (real_le _24351 _24350) = (real_le _24351 _24350).
Proof. exact (eq_refl (real_le _24351 _24350)). Qed.
Lemma lem1376255 (_24351 : real) (_24350 : real) : (term232 _24351 _24350) = (term236 _24351 _24350).
Proof. exact (MK_COMB (@lem1376253 _24350 _24351) (@lem1376254 _24351 _24350)). Qed.
Lemma lem1376256 (_24351 : real) (_24350 : real) : (term204 _24350 _24351) = (term236 _24351 _24350).
Proof. exact (TRANS (@lem1376248 _24351 _24350) (@lem1376255 _24351 _24350)). Qed.
Lemma lem1376259 (_24351 : real) (_24350 : real) (h1 : term33) : term236 _24351 _24350.
Proof. exact (EQ_MP (@lem1376256 _24351 _24350) (@lem1375965 _24350 _24351 h1)). Qed.
Lemma lem1376260 (y : real) (h1 : term33) : term237 y.
Proof. exact (@lem1376259 y y h1). Qed.
Lemma lem1376263 (y : real) (h1 : term33) : real_le y y.
Proof. exact (@lem1376260 y h1 (@lem1376245 y)). Qed.
Lemma lem1376264 (y : real) (h1 : term33) : term238 y.
Proof. exact (fun h0 : term201 y => @lem1376263 y h1). Qed.
Lemma lem1376266 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1376267 (y : real) : (term238 y) = (real_le y y).
Proof. exact (@lem1376266 (real_le y y)). Qed.
Lemma lem1376268 (y : real) (h1 : term33) : real_le y y.
Proof. exact (EQ_MP (@lem1376267 y) (@lem1376264 y h1)). Qed.
Lemma lem1376271 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1376273 (y : real) : (term201 y) = (term239 y).
Proof. exact (@lem1376271 (real_le y y)). Qed.
Lemma lem1376276 (x : real) (y : real) (h1 : term55 x y) (h2 : x = y) : term239 y.
Proof. exact (EQ_MP (@lem1376273 y) (@lem1375937 x y h1 h2)). Qed.
Lemma lem1376279 (x : real) (y : real) (h1 : term33) (h2 : term55 x y) (h3 : x = y) : False.
Proof. exact (@lem1376276 x y h2 h3 (@lem1376268 y h1)). Qed.
Lemma lem1376280 (x : real) (y : real) (h1 : term33) (h2 : term55 x y) (h3 : x = y) : term224.
Proof. exact (fun h0 : ~ False => @lem1376279 x y h1 h2 h3). Qed.
Lemma lem1376282 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1376283 : term224 = False.
Proof. exact (@lem1376282 False). Qed.
Lemma lem1376285 (x : real) (y : real) (h1 : term33) (h2 : term55 x y) (h3 : x = y) : False.
Proof. exact (EQ_MP (@lem1376283) (@lem1376280 x y h1 h2 h3)). Qed.
Lemma lem1376286 (x : real) (y : real) (h1 : term33) (h2 : term55 x y) (h3 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h4 : x = y => @lem1376285 x y h1 h2 h3) (fun h4 : False => @lem1375870 x y h3)). Qed.
Lemma lem1376287 (x : real) (y : real) (h1 : term33) (h2 : term55 x y) (h3 : x = y) : False.
Proof. exact (EQ_MP (@lem1376286 x y h1 h2 h3) (@lem1375870 x y h3)). Qed.
Lemma lem1376288 (x : real) (y : real) (h1 : term47) (h2 : term10 y x) (h3 : term55 x y) : (term10 y x) = False.
Proof. exact (prop_ext (fun h4 : term10 y x => @lem1376216 x y h1 h2 h3) (fun h4 : False => @lem1375836 y x h2)). Qed.
Lemma lem1376289 (x : real) (y : real) (h1 : term47) (h2 : term10 y x) (h3 : term55 x y) : False.
Proof. exact (EQ_MP (@lem1376288 x y h1 h2 h3) (@lem1375836 y x h2)). Qed.
Lemma lem1376290 (x : real) (y : real) (h1 : term33) (h2 : term55 x y) (h3 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h4 : x = y => @lem1376287 x y h1 h2 h3) (fun h4 : False => @lem1375718 x y h3)). Qed.
Lemma lem1376291 (x : real) (y : real) (h1 : term33) (h2 : term55 x y) (h3 : x = y) : False.
Proof. exact (EQ_MP (@lem1376290 x y h1 h2 h3) (@lem1375718 x y h3)). Qed.
Lemma lem1376292 (x : real) (y : real) (h1 : term47) (h2 : term10 y x) (h3 : term55 x y) : (term10 y x) = False.
Proof. exact (prop_ext (fun h4 : term10 y x => @lem1376289 x y h1 h2 h3) (fun h4 : False => @lem1375646 y x h2)). Qed.
Lemma lem1376293 (x : real) (y : real) (h1 : term47) (h2 : term10 y x) (h3 : term55 x y) : False.
Proof. exact (EQ_MP (@lem1376292 x y h1 h2 h3) (@lem1375646 y x h2)). Qed.
Lemma lem1376294 (x : real) (y : real) (h1 : term33) (h2 : term55 x y) (h3 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h4 : x = y => @lem1376291 x y h1 h2 h3) (fun h4 : False => @lem1375718 x y h3)). Qed.
Lemma lem1376295 (x : real) (y : real) (h1 : term33) (h2 : term55 x y) (h3 : x = y) : False.
Proof. exact (EQ_MP (@lem1376294 x y h1 h2 h3) (@lem1375718 x y h3)). Qed.
Lemma lem1376296 (x : real) (y : real) (h1 : term47) (h2 : term10 y x) (h3 : term55 x y) : (term10 y x) = False.
Proof. exact (prop_ext (fun h4 : term10 y x => @lem1376293 x y h1 h2 h3) (fun h4 : False => @lem1375646 y x h2)). Qed.
Lemma lem1376297 (x : real) (y : real) (h1 : term47) (h2 : term10 y x) (h3 : term55 x y) : False.
Proof. exact (EQ_MP (@lem1376296 x y h1 h2 h3) (@lem1375646 y x h2)). Qed.
Lemma lem1376298 (x : real) (y : real) (h1 : term47) (h2 : term10 y x) (h3 : term55 x y) : term47 = False.
Proof. exact (prop_ext (fun h4 : term47 => @lem1376297 x y h1 h2 h3) (fun h4 : False => @lem1375590 h1)). Qed.
Lemma lem1376299 (x : real) (y : real) (h1 : term47) (h2 : term10 y x) (h3 : term55 x y) : False.
Proof. exact (EQ_MP (@lem1376298 x y h1 h2 h3) (@lem1375590 h1)). Qed.
Lemma lem1376300 (x : real) (y : real) (h1 : term33) (h2 : term47) (h3 : term55 x y) : False.
Proof. exact (or_elim (@lem1375495 x y h3) (fun h0 : term10 y x => @lem1376299 x y h2 h0 h3) (fun h0 : x = y => @lem1376295 x y h1 h3 h0)). Qed.
Lemma lem1376301 (x : real) (y : real) (h1 : term33) (h2 : term47) (h3 : term61 x y) : False.
Proof. exact (or_elim (@lem1375486 x y h3) (fun h0 : term57 x y => @lem1376128 x y h1 h0) (fun h0 : term55 x y => @lem1376300 x y h1 h2 h0)). Qed.
Lemma lem1376302 (x : real) (y : real) (h1 : term33) (h2 : term47) (h3 : term61 x y) : (term61 x y) = False.
Proof. exact (prop_ext (fun h4 : term61 x y => @lem1376301 x y h1 h2 h3) (fun h4 : False => @lem1375486 x y h3)). Qed.
Lemma lem1376303 (x : real) (y : real) (h1 : term33) (h2 : term47) (h3 : term61 x y) : False.
Proof. exact (EQ_MP (@lem1376302 x y h1 h2 h3) (@lem1375486 x y h3)). Qed.
Lemma lem1376304 (x : real) (y : real) (h1 : term33) (h2 : term47) (h3 : term61 x y) : term47 = False.
Proof. exact (prop_ext (fun h4 : term47 => @lem1376303 x y h1 h2 h3) (fun h4 : False => @lem1375370 h2)). Qed.
Lemma lem1376305 (x : real) (y : real) (h1 : term33) (h2 : term47) (h3 : term61 x y) : False.
Proof. exact (EQ_MP (@lem1376304 x y h1 h2 h3) (@lem1375370 h2)). Qed.
Lemma lem1376306 (x : real) (h1 : term33) (h2 : term47) (h3 : term71 x) : False.
Proof. exact (ex_elim (@lem1375349 x h3) (fun y : real => fun h0 : term70 x y => @lem1376305 x y h1 h2 h0)). Qed.
Lemma lem1376307 (h1 : term33) (h2 : term47) (h3 : term26) : False.
Proof. exact (ex_elim (@lem1374983 h3) (fun x : real => fun h0 : term76 x => @lem1376306 x h1 h2 h0)). Qed.
Lemma lem1376308 (h1 : term33) (h2 : term47) (h3 : term26) : term47 = False.
Proof. exact (prop_ext (fun h4 : term47 => @lem1376307 h1 h2 h3) (fun h4 : False => @lem1375051 h2)). Qed.
Lemma lem1376309 (h1 : term33) (h2 : term47) (h3 : term26) : False.
Proof. exact (EQ_MP (@lem1376308 h1 h2 h3) (@lem1375051 h2)). Qed.
Lemma lem1376310 (h1 : term47) (h2 : term26) : term31.
Proof. exact (fun h0 : term33 => @lem1376309 h0 h1 h2). Qed.
Lemma lem1376311 : term31 = term32.
Proof. exact (@lem69 term33). Qed.
Lemma lem1376312 (h1 : term47) (h2 : term26) : term32.
Proof. exact (EQ_MP (@lem1376311) (@lem1376310 h1 h2)). Qed.
Lemma lem1376313 (h1 : term26) : term36.
Proof. exact (fun h0 : term47 => @lem1376312 h0 h1). Qed.
Lemma lem1376314 : term38.
Proof. exact (fun h0 : term26 => @lem1376313 h0). Qed.
Lemma lem1376315 : term27.
Proof. exact (EQ_MP (@lem1374610) (@lem1376314)). Qed.
Lemma lem1376317 : term27.
Proof. exact (@lem1374414 (@lem1376315)). Qed.
Lemma lem1376318 (h1 : term26) : term35.
Proof. exact (@lem1376317 (@lem1374399 h1)). Qed.
Lemma lem1376319 (h1 : term26) : term31.
Proof. exact (@lem1376318 h1 (@lem1339697)). Qed.
Lemma lem1376320 (h1 : term26) : False.
Proof. exact (@lem1376319 h1 (@lem1339379)). Qed.
Lemma lem1376321 (h1 : term26) : term26 = False.
Proof. exact (prop_ext (fun h2 : term26 => @lem1376320 h1) (fun h2 : False => @lem1374399 h1)). Qed.
Lemma lem1376322 (h1 : term26) : False.
Proof. exact (EQ_MP (@lem1376321 h1) (@lem1374399 h1)). Qed.
Lemma lem1376323 : term25.
Proof. exact (fun h0 : term26 => @lem1376322 h0). Qed.
Lemma lem1376324 : term23.
Proof. exact (EQ_MP (@lem1374398) (@lem1376323)). Qed.
Lemma lem1376325 : term22.
Proof. exact (EQ_MP (@lem1374394) (@lem1376324)). Qed.
