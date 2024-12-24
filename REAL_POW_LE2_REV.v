Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_LE2_REV_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_NOT_LE_spec.
Require Import REAL_POW_LT2_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
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
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem1649380 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1649381 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1649382 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1649381 t1) (@lem1649380 t1)). Qed.
Lemma lem1649383 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1649382 t1 t2). Qed.
Lemma lem1649384 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1649385 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1649384 t1 t2) (@lem1649383 t1 t2)). Qed.
Lemma lem1649386 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1649385 t1 t2 t3). Qed.
Lemma lem1649387 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1649388 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1649387 t1 t2 t3) (@lem1649386 t1 t2 t3)). Qed.
Lemma lem1649389 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1649388 t1 t2 t3)). Qed.
Lemma lem1649391 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1649392 : term8 = term9.
Proof. exact (@lem1649391 term8). Qed.
Lemma lem1649393 : term9 = term8.
Proof. exact (SYM (@lem1649392)). Qed.
Lemma lem1649394 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1649397 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1649398 : term12.
Proof. exact (fun h0 : term11 => @lem1649397 h0). Qed.
Lemma lem1649399 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1649400 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1649401 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1649399 h2 (@lem1649400 h1)). Qed.
Lemma lem1649402 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1649401 h1 h0). Qed.
Lemma lem1649403 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1649404 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1649402 h1 (@lem1649403 h2)). Qed.
Lemma lem1649405 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1649404 h0 h1). Qed.
Lemma lem1649406 : term14.
Proof. exact (fun h0 : term12 => @lem1649405 h0). Qed.
Lemma lem1649409 : term12.
Proof. exact (@lem1649406 (@lem1649398)). Qed.
Lemma lem1649441 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1649442 : term15 = term16.
Proof. exact (@lem1649441 term17). Qed.
Lemma lem1649461 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1649462 : term19 = term20.
Proof. exact (MK_COMB (@lem1649461) (@lem1649442)). Qed.
Lemma lem1649465 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1649472 : term11 = term22.
Proof. exact (MK_COMB (@lem1649465) (@lem1649462)). Qed.
Lemma lem1649487 (x : real) (y : real) (n : nat) : (term23 x y n) = (term23 x y n).
Proof. exact (eq_refl (term23 x y n)). Qed.
Lemma lem1649488 (x : real) (n : nat) : (term24 x n) = (term24 x n).
Proof. exact (fun_ext (fun y : real => @lem1649487 x y n)). Qed.
Lemma lem1649489 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649490 (x : real) (n : nat) : (term25 x n) = (term25 x n).
Proof. exact (MK_COMB (@lem1649489) (@lem1649488 x n)). Qed.
Lemma lem1649491 (n : nat) : (term26 n) = (term26 n).
Proof. exact (fun_ext (fun x : real => @lem1649490 x n)). Qed.
Lemma lem1649492 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649493 (n : nat) : (term27 n) = (term27 n).
Proof. exact (MK_COMB (@lem1649492) (@lem1649491 n)). Qed.
Lemma lem1649494 : term28 = term28.
Proof. exact (fun_ext (fun n : nat => @lem1649493 n)). Qed.
Lemma lem1649495 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1649496 : term17 = term17.
Proof. exact (MK_COMB (@lem1649495) (@lem1649494)). Qed.
Lemma lem1649497 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1649498 : term16 = term16.
Proof. exact (MK_COMB (@lem1649497) (@lem1649496)). Qed.
Lemma lem1649505 (y : real) (x : real) : ((term29 x y) = (real_lt y x)) = ((term29 x y) = (real_lt y x)).
Proof. exact (eq_refl ((term29 x y) = (real_lt y x))). Qed.
Lemma lem1649506 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1649505 y x)). Qed.
Lemma lem1649507 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649508 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1649507) (@lem1649506 x)). Qed.
Lemma lem1649509 : term32 = term32.
Proof. exact (fun_ext (fun x : real => @lem1649508 x)). Qed.
Lemma lem1649510 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649511 : term33 = term33.
Proof. exact (MK_COMB (@lem1649510) (@lem1649509)). Qed.
Lemma lem1649512 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1649513 : term18 = term18.
Proof. exact (MK_COMB (@lem1649512) (@lem1649511)). Qed.
Lemma lem1649514 : term20 = term20.
Proof. exact (MK_COMB (@lem1649513) (@lem1649498)). Qed.
Lemma lem1649529 (n : nat) (x : real) (y : real) : (term34 n x y) = (term34 n x y).
Proof. exact (eq_refl (term34 n x y)). Qed.
Lemma lem1649530 (n : nat) (x : real) : (term35 n x) = (term35 n x).
Proof. exact (fun_ext (fun y : real => @lem1649529 n x y)). Qed.
Lemma lem1649531 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649532 (n : nat) (x : real) : (term36 n x) = (term36 n x).
Proof. exact (MK_COMB (@lem1649531) (@lem1649530 n x)). Qed.
Lemma lem1649533 (n : nat) : (term37 n) = (term37 n).
Proof. exact (fun_ext (fun x : real => @lem1649532 n x)). Qed.
Lemma lem1649534 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649535 (n : nat) : (term38 n) = (term38 n).
Proof. exact (MK_COMB (@lem1649534) (@lem1649533 n)). Qed.
Lemma lem1649536 : term39 = term39.
Proof. exact (fun_ext (fun n : nat => @lem1649535 n)). Qed.
Lemma lem1649537 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1649538 : term8 = term8.
Proof. exact (MK_COMB (@lem1649537) (@lem1649536)). Qed.
Lemma lem1649539 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1649540 : term10 = term10.
Proof. exact (MK_COMB (@lem1649539) (@lem1649538)). Qed.
Lemma lem1649541 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1649542 : term21 = term21.
Proof. exact (MK_COMB (@lem1649541) (@lem1649540)). Qed.
Lemma lem1649543 : term22 = term22.
Proof. exact (MK_COMB (@lem1649542) (@lem1649514)). Qed.
Lemma lem1649610 : term11 = term22.
Proof. exact (TRANS (@lem1649472) (@lem1649543)). Qed.
Lemma lem1649611 : term22 = term11.
Proof. exact (SYM (@lem1649610)). Qed.
Lemma lem1649612 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1649613 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1649614 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1649629 (n : nat) (x : real) (y : real) : (term40 n x y) = (term41 n x y).
Proof. exact (@lem17362 (term42 x y n) (real_le x y)). Qed.
Lemma lem1649630 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1649631 (n : nat) (x : real) : (term45 n x) = (term46 n x).
Proof. exact (@lem1649630 (term35 n x)). Qed.
Lemma lem1649632 (n : nat) (x : real) (y : real) : (term47 n x y) = (term34 n x y).
Proof. exact (eq_refl (term47 n x y)). Qed.
Lemma lem1649633 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1649634 (n : nat) (x : real) (y : real) : (term48 n x y) = (term40 n x y).
Proof. exact (MK_COMB (@lem1649633) (@lem1649632 n x y)). Qed.
Lemma lem1649635 (n : nat) (x : real) (y : real) : (term48 n x y) = (term41 n x y).
Proof. exact (TRANS (@lem1649634 n x y) (@lem1649629 n x y)). Qed.
Lemma lem1649636 (n : nat) (x : real) : (term49 n x) = (term50 n x).
Proof. exact (fun_ext (fun y : real => @lem1649635 n x y)). Qed.
Lemma lem1649637 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1649638 (n : nat) (x : real) : (term46 n x) = (term51 n x).
Proof. exact (MK_COMB (@lem1649637) (@lem1649636 n x)). Qed.
Lemma lem1649639 (n : nat) (x : real) : (term45 n x) = (term51 n x).
Proof. exact (TRANS (@lem1649631 n x) (@lem1649638 n x)). Qed.
Lemma lem1649640 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1649641 (n : nat) : (term52 n) = (term53 n).
Proof. exact (@lem1649640 (term37 n)). Qed.
Lemma lem1649642 (n : nat) (x : real) : (term54 n x) = (term36 n x).
Proof. exact (eq_refl (term54 n x)). Qed.
Lemma lem1649643 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1649644 (n : nat) (x : real) : (term55 n x) = (term45 n x).
Proof. exact (MK_COMB (@lem1649643) (@lem1649642 n x)). Qed.
Lemma lem1649645 (n : nat) (x : real) : (term55 n x) = (term51 n x).
Proof. exact (TRANS (@lem1649644 n x) (@lem1649639 n x)). Qed.
Lemma lem1649646 (n : nat) : (term56 n) = (term57 n).
Proof. exact (fun_ext (fun x : real => @lem1649645 n x)). Qed.
Lemma lem1649647 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1649648 (n : nat) : (term53 n) = (term58 n).
Proof. exact (MK_COMB (@lem1649647) (@lem1649646 n)). Qed.
Lemma lem1649649 (n : nat) : (term52 n) = (term58 n).
Proof. exact (TRANS (@lem1649641 n) (@lem1649648 n)). Qed.
Lemma lem1649650 (P : nat -> Prop) : (term59 P) = (term60 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1649651 : term10 = term61.
Proof. exact (@lem1649650 term39). Qed.
Lemma lem1649652 (n : nat) : (term62 n) = (term38 n).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem1649653 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1649654 (n : nat) : (term63 n) = (term52 n).
Proof. exact (MK_COMB (@lem1649653) (@lem1649652 n)). Qed.
Lemma lem1649655 (n : nat) : (term63 n) = (term58 n).
Proof. exact (TRANS (@lem1649654 n) (@lem1649649 n)). Qed.
Lemma lem1649656 : term64 = term65.
Proof. exact (fun_ext (fun n : nat => @lem1649655 n)). Qed.
Lemma lem1649657 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1649658 : term61 = term66.
Proof. exact (MK_COMB (@lem1649657) (@lem1649656)). Qed.
Lemma lem1649719 : term10 = term66.
Proof. exact (TRANS (@lem1649651) (@lem1649658)). Qed.
Lemma lem1649720 (h1 : term10) : term66.
Proof. exact (EQ_MP (@lem1649719) (@lem1649612 h1)). Qed.
Lemma lem1649724 (x : real) (y : real) : (term67 x y) = (real_le x y).
Proof. exact (@lem16933 (real_le x y)). Qed.
Lemma lem1649726 (y : real) (x : real) : (real_lt y x) = (real_lt y x).
Proof. exact (eq_refl (real_lt y x)). Qed.
Lemma lem1649727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1649728 (x : real) (y : real) : (term68 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1649727) (@lem1649724 x y)). Qed.
Lemma lem1649729 (y : real) (x : real) : (term70 y x) = (term71 y x).
Proof. exact (MK_COMB (@lem1649728 x y) (@lem1649726 y x)). Qed.
Lemma lem1649734 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (eq_refl (term72 y x)). Qed.
Lemma lem1649735 (y : real) (x : real) : (term73 y x) = (term74 y x).
Proof. exact (MK_COMB (@lem1649734 y x) (@lem1649729 y x)). Qed.
Lemma lem1649736 (y : real) (x : real) : ((term29 x y) = (real_lt y x)) = (term73 y x).
Proof. exact (@lem17784 (term29 x y) (real_lt y x)). Qed.
Lemma lem1649737 (y : real) (x : real) : ((term29 x y) = (real_lt y x)) = (term74 y x).
Proof. exact (TRANS (@lem1649736 y x) (@lem1649735 y x)). Qed.
Lemma lem1649738 (x : real) : (term30 x) = (term75 x).
Proof. exact (fun_ext (fun y : real => @lem1649737 y x)). Qed.
Lemma lem1649739 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649740 (x : real) : (term31 x) = (term76 x).
Proof. exact (MK_COMB (@lem1649739) (@lem1649738 x)). Qed.
Lemma lem1649741 : term32 = term77.
Proof. exact (fun_ext (fun x : real => @lem1649740 x)). Qed.
Lemma lem1649742 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649743 : term33 = term78.
Proof. exact (MK_COMB (@lem1649742) (@lem1649741)). Qed.
Lemma lem1649749 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term79 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1649750 (P : real -> Prop) (Q : real -> Prop) : (term81 P Q) = (term82 P Q).
Proof. exact (@lem1649749 real P Q). Qed.
Lemma lem1649751 (x : real) : (term83 x) = (term84 x).
Proof. exact (@lem1649750 (term85 x) (term86 x)). Qed.
Lemma lem1649752 (y : real) (x : real) : (term87 x y) = (term88 y x).
Proof. exact (eq_refl (term87 x y)). Qed.
Lemma lem1649753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1649754 (y : real) (x : real) : (term89 x y) = (term72 y x).
Proof. exact (MK_COMB (@lem1649753) (@lem1649752 y x)). Qed.
Lemma lem1649755 (y : real) (x : real) : (term90 x y) = (term71 y x).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem1649756 (y : real) (x : real) : (term91 x y) = (term74 y x).
Proof. exact (MK_COMB (@lem1649754 y x) (@lem1649755 y x)). Qed.
Lemma lem1649757 (x : real) : (term92 x) = (term75 x).
Proof. exact (fun_ext (fun y : real => @lem1649756 y x)). Qed.
Lemma lem1649758 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649759 (x : real) : (term83 x) = (term76 x).
Proof. exact (MK_COMB (@lem1649758) (@lem1649757 x)). Qed.
Lemma lem1649760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1649761 (x : real) : (term93 x) = (term94 x).
Proof. exact (MK_COMB (@lem1649760) (@lem1649759 x)). Qed.
Lemma lem1649762 (y : real) (x : real) : (term87 x y) = (term88 y x).
Proof. exact (eq_refl (term87 x y)). Qed.
Lemma lem1649763 (x : real) : (term95 x) = (term85 x).
Proof. exact (fun_ext (fun y : real => @lem1649762 y x)). Qed.
Lemma lem1649764 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649765 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem1649764) (@lem1649763 x)). Qed.
Lemma lem1649766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1649767 (x : real) : (term98 x) = (term99 x).
Proof. exact (MK_COMB (@lem1649766) (@lem1649765 x)). Qed.
Lemma lem1649768 (y : real) (x : real) : (term90 x y) = (term71 y x).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem1649769 (x : real) : (term100 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1649768 y x)). Qed.
Lemma lem1649770 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649771 (x : real) : (term101 x) = (term102 x).
Proof. exact (MK_COMB (@lem1649770) (@lem1649769 x)). Qed.
Lemma lem1649772 (x : real) : (term84 x) = (term103 x).
Proof. exact (MK_COMB (@lem1649767 x) (@lem1649771 x)). Qed.
Lemma lem1649773 (x : real) : ((term83 x) = (term84 x)) = ((term76 x) = (term103 x)).
Proof. exact (MK_COMB (@lem1649761 x) (@lem1649772 x)). Qed.
Lemma lem1649774 (x : real) : (term76 x) = (term103 x).
Proof. exact (EQ_MP (@lem1649773 x) (@lem1649751 x)). Qed.
Lemma lem1649871 : term77 = term104.
Proof. exact (fun_ext (fun x : real => @lem1649774 x)). Qed.
Lemma lem1649872 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649873 : term78 = term105.
Proof. exact (MK_COMB (@lem1649872) (@lem1649871)). Qed.
Lemma lem1649875 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term79 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1649876 (P : real -> Prop) (Q : real -> Prop) : (term81 P Q) = (term82 P Q).
Proof. exact (@lem1649875 real P Q). Qed.
Lemma lem1649877 : term106 = term107.
Proof. exact (@lem1649876 term108 term109). Qed.
Lemma lem1649878 (x : real) : (term110 x) = (term97 x).
Proof. exact (eq_refl (term110 x)). Qed.
Lemma lem1649879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1649880 (x : real) : (term111 x) = (term99 x).
Proof. exact (MK_COMB (@lem1649879) (@lem1649878 x)). Qed.
Lemma lem1649881 (x : real) : (term112 x) = (term102 x).
Proof. exact (eq_refl (term112 x)). Qed.
Lemma lem1649882 (x : real) : (term113 x) = (term103 x).
Proof. exact (MK_COMB (@lem1649880 x) (@lem1649881 x)). Qed.
Lemma lem1649883 : term114 = term104.
Proof. exact (fun_ext (fun x : real => @lem1649882 x)). Qed.
Lemma lem1649884 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649885 : term106 = term105.
Proof. exact (MK_COMB (@lem1649884) (@lem1649883)). Qed.
Lemma lem1649886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1649887 : term115 = term116.
Proof. exact (MK_COMB (@lem1649886) (@lem1649885)). Qed.
Lemma lem1649888 (x : real) : (term110 x) = (term97 x).
Proof. exact (eq_refl (term110 x)). Qed.
Lemma lem1649889 : term117 = term108.
Proof. exact (fun_ext (fun x : real => @lem1649888 x)). Qed.
Lemma lem1649890 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649891 : term118 = term119.
Proof. exact (MK_COMB (@lem1649890) (@lem1649889)). Qed.
Lemma lem1649892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1649893 : term120 = term121.
Proof. exact (MK_COMB (@lem1649892) (@lem1649891)). Qed.
Lemma lem1649894 (x : real) : (term112 x) = (term102 x).
Proof. exact (eq_refl (term112 x)). Qed.
Lemma lem1649895 : term122 = term109.
Proof. exact (fun_ext (fun x : real => @lem1649894 x)). Qed.
Lemma lem1649896 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1649897 : term123 = term124.
Proof. exact (MK_COMB (@lem1649896) (@lem1649895)). Qed.
Lemma lem1649898 : term107 = term125.
Proof. exact (MK_COMB (@lem1649893) (@lem1649897)). Qed.
Lemma lem1649899 : (term106 = term107) = (term105 = term125).
Proof. exact (MK_COMB (@lem1649887) (@lem1649898)). Qed.
Lemma lem1649900 : term105 = term125.
Proof. exact (EQ_MP (@lem1649899) (@lem1649877)). Qed.
Lemma lem1650007 : term78 = term125.
Proof. exact (TRANS (@lem1649873) (@lem1649900)). Qed.
Lemma lem1650008 : term33 = term125.
Proof. exact (TRANS (@lem1649743) (@lem1650007)). Qed.
Lemma lem1650009 (h1 : term33) : term125.
Proof. exact (EQ_MP (@lem1650008) (@lem1649613 h1)). Qed.
Lemma lem1650012 (n : nat) : (term126 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem1650019 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (@lem17045 (term129 x) (real_lt x y)). Qed.
Lemma lem1650020 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1650021 (n : nat) : (term130 n) = (term131 n).
Proof. exact (MK_COMB (@lem1650020) (@lem1650012 n)). Qed.
Lemma lem1650022 (n : nat) (x : real) (y : real) : (term132 n x y) = (term133 n x y).
Proof. exact (MK_COMB (@lem1650021 n) (@lem1650019 x y)). Qed.
Lemma lem1650023 (n : nat) (x : real) (y : real) : (term134 n x y) = (term132 n x y).
Proof. exact (@lem17045 (term135 n) (term136 x y)). Qed.
Lemma lem1650024 (n : nat) (x : real) (y : real) : (term134 n x y) = (term133 n x y).
Proof. exact (TRANS (@lem1650023 n x y) (@lem1650022 n x y)). Qed.
Lemma lem1650025 (x : real) (y : real) (n : nat) : (term137 x y n) = (term137 x y n).
Proof. exact (eq_refl (term137 x y n)). Qed.
Lemma lem1650026 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1650027 (n : nat) (x : real) (y : real) : (term138 n x y) = (term139 n x y).
Proof. exact (MK_COMB (@lem1650026) (@lem1650024 n x y)). Qed.
Lemma lem1650028 (x : real) (y : real) (n : nat) : (term140 x y n) = (term141 x y n).
Proof. exact (MK_COMB (@lem1650027 n x y) (@lem1650025 x y n)). Qed.
Lemma lem1650029 (x : real) (y : real) (n : nat) : (term23 x y n) = (term140 x y n).
Proof. exact (@lem17265 (term142 n x y) (term137 x y n)). Qed.
Lemma lem1650030 (x : real) (y : real) (n : nat) : (term23 x y n) = (term141 x y n).
Proof. exact (TRANS (@lem1650029 x y n) (@lem1650028 x y n)). Qed.
Lemma lem1650031 (x : real) (n : nat) : (term24 x n) = (term143 x n).
Proof. exact (fun_ext (fun y : real => @lem1650030 x y n)). Qed.
Lemma lem1650032 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650033 (x : real) (n : nat) : (term25 x n) = (term144 x n).
Proof. exact (MK_COMB (@lem1650032) (@lem1650031 x n)). Qed.
Lemma lem1650034 (n : nat) : (term26 n) = (term145 n).
Proof. exact (fun_ext (fun x : real => @lem1650033 x n)). Qed.
Lemma lem1650035 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650036 (n : nat) : (term27 n) = (term146 n).
Proof. exact (MK_COMB (@lem1650035) (@lem1650034 n)). Qed.
Lemma lem1650037 : term28 = term147.
Proof. exact (fun_ext (fun n : nat => @lem1650036 n)). Qed.
Lemma lem1650038 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1650099 : term17 = term148.
Proof. exact (MK_COMB (@lem1650038) (@lem1650037)). Qed.
Lemma lem1650100 (h1 : term17) : term148.
Proof. exact (EQ_MP (@lem1650099) (@lem1649614 h1)). Qed.
Lemma lem1650101 (n : nat) (h1 : term58 n) : term58 n.
Proof. exact (h1). Qed.
Lemma lem1650102 (n : nat) (x : real) (h1 : term51 n x) : term51 n x.
Proof. exact (h1). Qed.
Lemma lem1650116 (y : real) (x : real) : (term71 y x) = (term71 y x).
Proof. exact (eq_refl (term71 y x)). Qed.
Lemma lem1650117 (x : real) : (term86 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1650116 y x)). Qed.
Lemma lem1650118 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650119 (x : real) : (term102 x) = (term102 x).
Proof. exact (MK_COMB (@lem1650118) (@lem1650117 x)). Qed.
Lemma lem1650120 : term109 = term109.
Proof. exact (fun_ext (fun x : real => @lem1650119 x)). Qed.
Lemma lem1650121 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650122 : term124 = term124.
Proof. exact (MK_COMB (@lem1650121) (@lem1650120)). Qed.
Lemma lem1650139 (y : real) (x : real) : (term88 y x) = (term88 y x).
Proof. exact (eq_refl (term88 y x)). Qed.
Lemma lem1650140 (x : real) : (term85 x) = (term85 x).
Proof. exact (fun_ext (fun y : real => @lem1650139 y x)). Qed.
Lemma lem1650141 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650142 (x : real) : (term97 x) = (term97 x).
Proof. exact (MK_COMB (@lem1650141) (@lem1650140 x)). Qed.
Lemma lem1650143 : term108 = term108.
Proof. exact (fun_ext (fun x : real => @lem1650142 x)). Qed.
Lemma lem1650144 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650145 : term119 = term119.
Proof. exact (MK_COMB (@lem1650144) (@lem1650143)). Qed.
Lemma lem1650146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1650147 : term121 = term121.
Proof. exact (MK_COMB (@lem1650146) (@lem1650145)). Qed.
Lemma lem1650148 : term125 = term125.
Proof. exact (MK_COMB (@lem1650147) (@lem1650122)). Qed.
Lemma lem1650149 (h1 : term33) : term125.
Proof. exact (EQ_MP (@lem1650148) (@lem1650009 h1)). Qed.
Lemma lem1650196 (x : real) (y : real) (n : nat) : (term141 x y n) = (term141 x y n).
Proof. exact (eq_refl (term141 x y n)). Qed.
Lemma lem1650197 (x : real) (n : nat) : (term143 x n) = (term143 x n).
Proof. exact (fun_ext (fun y : real => @lem1650196 x y n)). Qed.
Lemma lem1650198 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650199 (x : real) (n : nat) : (term144 x n) = (term144 x n).
Proof. exact (MK_COMB (@lem1650198) (@lem1650197 x n)). Qed.
Lemma lem1650200 (n : nat) : (term145 n) = (term145 n).
Proof. exact (fun_ext (fun x : real => @lem1650199 x n)). Qed.
Lemma lem1650201 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650202 (n : nat) : (term146 n) = (term146 n).
Proof. exact (MK_COMB (@lem1650201) (@lem1650200 n)). Qed.
Lemma lem1650203 : term147 = term147.
Proof. exact (fun_ext (fun n : nat => @lem1650202 n)). Qed.
Lemma lem1650204 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1650205 : term148 = term148.
Proof. exact (MK_COMB (@lem1650204) (@lem1650203)). Qed.
Lemma lem1650206 (h1 : term17) : term148.
Proof. exact (EQ_MP (@lem1650205) (@lem1650100 h1)). Qed.
Lemma lem1650254 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term41 n x y.
Proof. exact (h1). Qed.
Lemma lem1650256 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term42 x y n.
Proof. exact (proj1 (@lem1650254 n x y h1)). Qed.
Lemma lem1650257 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term149 x y n.
Proof. exact (proj2 (@lem1650256 n x y h1)). Qed.
Lemma lem1650261 (h1 : term33) : term124.
Proof. exact (proj2 (@lem1650149 h1)). Qed.
Lemma lem1650262 (h1 : term33) : term119.
Proof. exact (proj1 (@lem1650149 h1)). Qed.
Lemma lem1650282 (x : real) (y : real) (n : nat) : (term141 x y n) = (term141 x y n).
Proof. exact (eq_refl (term141 x y n)). Qed.
Lemma lem1650283 (x : real) (n : nat) : (term143 x n) = (term143 x n).
Proof. exact (fun_ext (fun y : real => @lem1650282 x y n)). Qed.
Lemma lem1650284 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650285 (x : real) (n : nat) : (term144 x n) = (term144 x n).
Proof. exact (MK_COMB (@lem1650284) (@lem1650283 x n)). Qed.
Lemma lem1650286 (n : nat) : (term145 n) = (term145 n).
Proof. exact (fun_ext (fun x : real => @lem1650285 x n)). Qed.
Lemma lem1650287 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650288 (n : nat) : (term146 n) = (term146 n).
Proof. exact (MK_COMB (@lem1650287) (@lem1650286 n)). Qed.
Lemma lem1650289 : term147 = term147.
Proof. exact (fun_ext (fun n : nat => @lem1650288 n)). Qed.
Lemma lem1650290 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1650292 : term148 = term148.
Proof. exact (MK_COMB (@lem1650290) (@lem1650289)). Qed.
Lemma lem1650293 (h1 : term17) : term148.
Proof. exact (EQ_MP (@lem1650292) (@lem1650206 h1)). Qed.
Lemma lem1650317 (y : real) (x : real) : (term88 y x) = (term88 y x).
Proof. exact (eq_refl (term88 y x)). Qed.
Lemma lem1650318 (x : real) : (term85 x) = (term85 x).
Proof. exact (fun_ext (fun y : real => @lem1650317 y x)). Qed.
Lemma lem1650319 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650320 (x : real) : (term97 x) = (term97 x).
Proof. exact (MK_COMB (@lem1650319) (@lem1650318 x)). Qed.
Lemma lem1650321 : term108 = term108.
Proof. exact (fun_ext (fun x : real => @lem1650320 x)). Qed.
Lemma lem1650322 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650324 : term119 = term119.
Proof. exact (MK_COMB (@lem1650322) (@lem1650321)). Qed.
Lemma lem1650325 (h1 : term33) : term119.
Proof. exact (EQ_MP (@lem1650324) (@lem1650262 h1)). Qed.
Lemma lem1650333 (y : real) (x : real) : (term71 y x) = (term71 y x).
Proof. exact (eq_refl (term71 y x)). Qed.
Lemma lem1650334 (x : real) : (term86 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1650333 y x)). Qed.
Lemma lem1650335 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650336 (x : real) : (term102 x) = (term102 x).
Proof. exact (MK_COMB (@lem1650335) (@lem1650334 x)). Qed.
Lemma lem1650337 : term109 = term109.
Proof. exact (fun_ext (fun x : real => @lem1650336 x)). Qed.
Lemma lem1650338 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650340 : term124 = term124.
Proof. exact (MK_COMB (@lem1650338) (@lem1650337)). Qed.
Lemma lem1650341 (h1 : term33) : term124.
Proof. exact (EQ_MP (@lem1650340) (@lem1650261 h1)). Qed.
Lemma lem1650342 (_25579 : nat) (h1 : term17) : term150 _25579.
Proof. exact (@lem1650293 h1 _25579). Qed.
Lemma lem1650343 (_25579 : nat) : (term150 _25579) = (term146 _25579).
Proof. exact (eq_refl (term150 _25579)). Qed.
Lemma lem1650344 (_25579 : nat) (h1 : term17) : term146 _25579.
Proof. exact (EQ_MP (@lem1650343 _25579) (@lem1650342 _25579 h1)). Qed.
Lemma lem1650345 (_25579 : nat) (_25580 : real) (h1 : term17) : term151 _25579 _25580.
Proof. exact (@lem1650344 _25579 h1 _25580). Qed.
Lemma lem1650346 (_25580 : real) (_25579 : nat) : (term151 _25579 _25580) = (term144 _25580 _25579).
Proof. exact (eq_refl (term151 _25579 _25580)). Qed.
Lemma lem1650347 (_25580 : real) (_25579 : nat) (h1 : term17) : term144 _25580 _25579.
Proof. exact (EQ_MP (@lem1650346 _25580 _25579) (@lem1650345 _25579 _25580 h1)). Qed.
Lemma lem1650348 (_25580 : real) (_25579 : nat) (_25581 : real) (h1 : term17) : term152 _25580 _25579 _25581.
Proof. exact (@lem1650347 _25580 _25579 h1 _25581). Qed.
Lemma lem1650349 (_25580 : real) (_25581 : real) (_25579 : nat) : (term152 _25580 _25579 _25581) = (term141 _25580 _25581 _25579).
Proof. exact (eq_refl (term152 _25580 _25579 _25581)). Qed.
Lemma lem1650350 (_25580 : real) (_25581 : real) (_25579 : nat) (h1 : term17) : term141 _25580 _25581 _25579.
Proof. exact (EQ_MP (@lem1650349 _25580 _25581 _25579) (@lem1650348 _25580 _25579 _25581 h1)). Qed.
Lemma lem1650351 (_25582 : real) (h1 : term33) : term110 _25582.
Proof. exact (@lem1650325 h1 _25582). Qed.
Lemma lem1650352 (_25582 : real) : (term110 _25582) = (term97 _25582).
Proof. exact (eq_refl (term110 _25582)). Qed.
Lemma lem1650353 (_25582 : real) (h1 : term33) : term97 _25582.
Proof. exact (EQ_MP (@lem1650352 _25582) (@lem1650351 _25582 h1)). Qed.
Lemma lem1650354 (_25582 : real) (_25583 : real) (h1 : term33) : term87 _25582 _25583.
Proof. exact (@lem1650353 _25582 h1 _25583). Qed.
Lemma lem1650355 (_25583 : real) (_25582 : real) : (term87 _25582 _25583) = (term88 _25583 _25582).
Proof. exact (eq_refl (term87 _25582 _25583)). Qed.
Lemma lem1650357 (_25584 : real) (h1 : term33) : term112 _25584.
Proof. exact (@lem1650341 h1 _25584). Qed.
Lemma lem1650358 (_25584 : real) : (term112 _25584) = (term102 _25584).
Proof. exact (eq_refl (term112 _25584)). Qed.
Lemma lem1650359 (_25584 : real) (h1 : term33) : term102 _25584.
Proof. exact (EQ_MP (@lem1650358 _25584) (@lem1650357 _25584 h1)). Qed.
Lemma lem1650360 (_25584 : real) (_25585 : real) (h1 : term33) : term90 _25584 _25585.
Proof. exact (@lem1650359 _25584 h1 _25585). Qed.
Lemma lem1650361 (_25585 : real) (_25584 : real) : (term90 _25584 _25585) = (term71 _25585 _25584).
Proof. exact (eq_refl (term90 _25584 _25585)). Qed.
Lemma lem1650366 (_25580 : real) (_25581 : real) (_25579 : nat) : (term141 _25580 _25581 _25579) = (term153 _25580 _25581 _25579).
Proof. exact (@lem1649389 (_25579 = (NUMERAL 0)) (term128 _25580 _25581) (term137 _25580 _25581 _25579)). Qed.
Lemma lem1650373 (_25580 : real) (_25581 : real) (_25579 : nat) : (term154 _25580 _25581 _25579) = (term155 _25580 _25581 _25579).
Proof. exact (@lem1649389 (term156 _25580) (term157 _25580 _25581) (term137 _25580 _25581 _25579)). Qed.
Lemma lem1650374 (_25579 : nat) : (term131 _25579) = (term131 _25579).
Proof. exact (eq_refl (term131 _25579)). Qed.
Lemma lem1650377 (_25580 : real) (_25581 : real) (_25579 : nat) : (term153 _25580 _25581 _25579) = (term158 _25580 _25581 _25579).
Proof. exact (MK_COMB (@lem1650374 _25579) (@lem1650373 _25580 _25581 _25579)). Qed.
Lemma lem1650379 (_25580 : real) (_25581 : real) (_25579 : nat) : (term141 _25580 _25581 _25579) = (term158 _25580 _25581 _25579).
Proof. exact (TRANS (@lem1650366 _25580 _25581 _25579) (@lem1650377 _25580 _25581 _25579)). Qed.
Lemma lem1650380 (_25580 : real) (_25581 : real) (_25579 : nat) (h1 : term17) : term158 _25580 _25581 _25579.
Proof. exact (EQ_MP (@lem1650379 _25580 _25581 _25579) (@lem1650350 _25580 _25581 _25579 h1)). Qed.
Lemma lem1650382 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term29 x y.
Proof. exact (proj2 (@lem1650254 n x y h1)). Qed.
Lemma lem1650394 (_25583 : real) (_25582 : real) (h1 : term33) : term88 _25583 _25582.
Proof. exact (EQ_MP (@lem1650355 _25583 _25582) (@lem1650354 _25582 _25583 h1)). Qed.
Lemma lem1650400 (_25585 : real) (_25584 : real) (h1 : term33) : term71 _25585 _25584.
Proof. exact (EQ_MP (@lem1650361 _25585 _25584) (@lem1650360 _25584 _25585 h1)). Qed.
Lemma lem1650475 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term135 n.
Proof. exact (proj1 (@lem1650256 n x y h1)). Qed.
Lemma lem1650476 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term159 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem1650475 n x y h1). Qed.
Lemma lem1650478 (p : Prop) : (term160 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1650479 (n : nat) : (term159 n) = (term135 n).
Proof. exact (@lem1650478 (n = (NUMERAL 0))). Qed.
Lemma lem1650480 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term135 n.
Proof. exact (EQ_MP (@lem1650479 n) (@lem1650476 n x y h1)). Qed.
Lemma lem1650482 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term129 y.
Proof. exact (proj1 (@lem1650257 n x y h1)). Qed.
Lemma lem1650483 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term161 y.
Proof. exact (fun h0 : term156 y => @lem1650482 n x y h1). Qed.
Lemma lem1650485 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1650486 (y : real) : (term161 y) = (term129 y).
Proof. exact (@lem1650485 (term129 y)). Qed.
Lemma lem1650487 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term129 y.
Proof. exact (EQ_MP (@lem1650486 y) (@lem1650483 n x y h1)). Qed.
Lemma lem1650489 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term163 x y n.
Proof. exact (proj2 (@lem1650257 n x y h1)). Qed.
Lemma lem1650490 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term164 x y n.
Proof. exact (fun h0 : term165 x y n => @lem1650489 n x y h1). Qed.
Lemma lem1650492 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1650493 (x : real) (y : real) (n : nat) : (term164 x y n) = (term163 x y n).
Proof. exact (@lem1650492 (term163 x y n)). Qed.
Lemma lem1650494 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term163 x y n.
Proof. exact (EQ_MP (@lem1650493 x y n) (@lem1650490 n x y h1)). Qed.
Lemma lem1650505 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1650506 (_25583 : real) (_25582 : real) : (term166 _25582 _25583) = (term88 _25583 _25582).
Proof. exact (@lem1650505 (term29 _25582 _25583) (term157 _25583 _25582)). Qed.
Lemma lem1650512 (_25583 : real) (_25582 : real) : (term167 _25583 _25582) = (term167 _25583 _25582).
Proof. exact (eq_refl (term167 _25583 _25582)). Qed.
Lemma lem1650513 (_25583 : real) (_25582 : real) : ((term88 _25583 _25582) = (term166 _25582 _25583)) = ((term88 _25583 _25582) = (term88 _25583 _25582)).
Proof. exact (MK_COMB (@lem1650512 _25583 _25582) (@lem1650506 _25583 _25582)). Qed.
Lemma lem1650515 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1650516 (x : Prop) : (x = x) = True.
Proof. exact (@lem1650515 Prop x). Qed.
Lemma lem1650517 (_25583 : real) (_25582 : real) : ((term88 _25583 _25582) = (term88 _25583 _25582)) = True.
Proof. exact (@lem1650516 (term88 _25583 _25582)). Qed.
Lemma lem1650518 (_25582 : real) (_25583 : real) : ((term88 _25583 _25582) = (term166 _25582 _25583)) = True.
Proof. exact (TRANS (@lem1650513 _25583 _25582) (@lem1650517 _25583 _25582)). Qed.
Lemma lem1650519 (_25582 : real) (_25583 : real) : True = ((term88 _25583 _25582) = (term166 _25582 _25583)).
Proof. exact (SYM (@lem1650518 _25582 _25583)). Qed.
Lemma lem1650520 (_25582 : real) (_25583 : real) : (term88 _25583 _25582) = (term166 _25582 _25583).
Proof. exact (EQ_MP (@lem1650519 _25582 _25583) (@lem0)). Qed.
Lemma lem1650521 (_25582 : real) (_25583 : real) (h1 : term33) : term166 _25582 _25583.
Proof. exact (EQ_MP (@lem1650520 _25582 _25583) (@lem1650394 _25583 _25582 h1)). Qed.
Lemma lem1650523 (b : Prop) (a : Prop) : (a \/ b) = (term168 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1650524 (_25583 : real) (_25582 : real) : (term166 _25582 _25583) = (term169 _25583 _25582).
Proof. exact (@lem1650523 (term29 _25582 _25583) (term157 _25583 _25582)). Qed.
Lemma lem1650526 (a : Prop) : (term170 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1650527 (_25582 : real) (_25583 : real) : (term67 _25582 _25583) = (real_le _25582 _25583).
Proof. exact (@lem1650526 (real_le _25582 _25583)). Qed.
Lemma lem1650528 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1650529 (_25582 : real) (_25583 : real) : (term171 _25582 _25583) = (term172 _25582 _25583).
Proof. exact (MK_COMB (@lem1650528) (@lem1650527 _25582 _25583)). Qed.
Lemma lem1650530 (_25583 : real) (_25582 : real) : (term157 _25583 _25582) = (term157 _25583 _25582).
Proof. exact (eq_refl (term157 _25583 _25582)). Qed.
Lemma lem1650531 (_25583 : real) (_25582 : real) : (term169 _25583 _25582) = (term173 _25583 _25582).
Proof. exact (MK_COMB (@lem1650529 _25582 _25583) (@lem1650530 _25583 _25582)). Qed.
Lemma lem1650532 (_25583 : real) (_25582 : real) : (term166 _25582 _25583) = (term173 _25583 _25582).
Proof. exact (TRANS (@lem1650524 _25583 _25582) (@lem1650531 _25583 _25582)). Qed.
Lemma lem1650535 (_25583 : real) (_25582 : real) (h1 : term33) : term173 _25583 _25582.
Proof. exact (EQ_MP (@lem1650532 _25583 _25582) (@lem1650521 _25582 _25583 h1)). Qed.
Lemma lem1650536 (y : real) (x : real) (n : nat) (h1 : term33) : term174 y x n.
Proof. exact (@lem1650535 (real_pow y n) (real_pow x n) h1). Qed.
Lemma lem1650539 (n : nat) (x : real) (y : real) (h1 : term33) (h2 : term41 n x y) : term175 y x n.
Proof. exact (@lem1650536 y x n h1 (@lem1650494 n x y h2)). Qed.
Lemma lem1650540 (n : nat) (x : real) (y : real) (h1 : term33) (h2 : term41 n x y) : term176 y x n.
Proof. exact (fun h0 : term137 y x n => @lem1650539 n x y h1 h2). Qed.
Lemma lem1650542 (p : Prop) : (term160 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1650543 (y : real) (x : real) (n : nat) : (term176 y x n) = (term175 y x n).
Proof. exact (@lem1650542 (term137 y x n)). Qed.
Lemma lem1650544 (n : nat) (x : real) (y : real) (h1 : term33) (h2 : term41 n x y) : term175 y x n.
Proof. exact (EQ_MP (@lem1650543 y x n) (@lem1650540 n x y h1 h2)). Qed.
Lemma lem1650572 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1650573 (_25579 : nat) (_25580 : real) (_25581 : real) : (term177 _25580 _25581 _25579) = (term178 _25579 _25580 _25581).
Proof. exact (@lem1650572 (term137 _25580 _25581 _25579) (term157 _25580 _25581)). Qed.
Lemma lem1650579 (_25580 : real) : (term179 _25580) = (term179 _25580).
Proof. exact (eq_refl (term179 _25580)). Qed.
Lemma lem1650580 (_25579 : nat) (_25580 : real) (_25581 : real) : (term155 _25580 _25581 _25579) = (term180 _25579 _25580 _25581).
Proof. exact (MK_COMB (@lem1650579 _25580) (@lem1650573 _25579 _25580 _25581)). Qed.
Lemma lem1650584 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1650585 (_25579 : nat) (_25580 : real) (_25581 : real) : (term180 _25579 _25580 _25581) = (term181 _25579 _25580 _25581).
Proof. exact (@lem1650584 (term137 _25580 _25581 _25579) (term156 _25580) (term157 _25580 _25581)). Qed.
Lemma lem1650601 (_25579 : nat) (_25580 : real) (_25581 : real) : (term155 _25580 _25581 _25579) = (term181 _25579 _25580 _25581).
Proof. exact (TRANS (@lem1650580 _25579 _25580 _25581) (@lem1650585 _25579 _25580 _25581)). Qed.
Lemma lem1650602 (_25579 : nat) : (term131 _25579) = (term131 _25579).
Proof. exact (eq_refl (term131 _25579)). Qed.
Lemma lem1650603 (_25579 : nat) (_25580 : real) (_25581 : real) : (term158 _25580 _25581 _25579) = (term182 _25579 _25580 _25581).
Proof. exact (MK_COMB (@lem1650602 _25579) (@lem1650601 _25579 _25580 _25581)). Qed.
Lemma lem1650614 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1650615 (_25579 : nat) (_25580 : real) (_25581 : real) : (term183 _25580 _25581 _25579) = (term184 _25579 _25580 _25581).
Proof. exact (MK_COMB (@lem1650614) (@lem1650603 _25579 _25580 _25581)). Qed.
Lemma lem1650619 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1650620 (_25580 : real) (_25581 : real) (_25579 : nat) : (term185 _25580 _25581 _25579) = (term186 _25580 _25581 _25579).
Proof. exact (@lem1650619 (_25579 = (NUMERAL 0)) (term157 _25580 _25581) (term187 _25580 _25581 _25579)). Qed.
Lemma lem1650636 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1650637 (_25580 : real) (_25581 : real) (_25579 : nat) : (term188 _25580 _25581 _25579) = (term155 _25580 _25581 _25579).
Proof. exact (@lem1650636 (term156 _25580) (term157 _25580 _25581) (term137 _25580 _25581 _25579)). Qed.
Lemma lem1650651 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1650652 (_25579 : nat) (_25580 : real) (_25581 : real) : (term177 _25580 _25581 _25579) = (term178 _25579 _25580 _25581).
Proof. exact (@lem1650651 (term137 _25580 _25581 _25579) (term157 _25580 _25581)). Qed.
Lemma lem1650658 (_25580 : real) : (term179 _25580) = (term179 _25580).
Proof. exact (eq_refl (term179 _25580)). Qed.
Lemma lem1650659 (_25579 : nat) (_25580 : real) (_25581 : real) : (term155 _25580 _25581 _25579) = (term180 _25579 _25580 _25581).
Proof. exact (MK_COMB (@lem1650658 _25580) (@lem1650652 _25579 _25580 _25581)). Qed.
Lemma lem1650663 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1650664 (_25579 : nat) (_25580 : real) (_25581 : real) : (term180 _25579 _25580 _25581) = (term181 _25579 _25580 _25581).
Proof. exact (@lem1650663 (term137 _25580 _25581 _25579) (term156 _25580) (term157 _25580 _25581)). Qed.
Lemma lem1650680 (_25579 : nat) (_25580 : real) (_25581 : real) : (term155 _25580 _25581 _25579) = (term181 _25579 _25580 _25581).
Proof. exact (TRANS (@lem1650659 _25579 _25580 _25581) (@lem1650664 _25579 _25580 _25581)). Qed.
Lemma lem1650681 (_25579 : nat) (_25580 : real) (_25581 : real) : (term188 _25580 _25581 _25579) = (term181 _25579 _25580 _25581).
Proof. exact (TRANS (@lem1650637 _25580 _25581 _25579) (@lem1650680 _25579 _25580 _25581)). Qed.
Lemma lem1650682 (_25579 : nat) : (term131 _25579) = (term131 _25579).
Proof. exact (eq_refl (term131 _25579)). Qed.
Lemma lem1650683 (_25579 : nat) (_25580 : real) (_25581 : real) : (term186 _25580 _25581 _25579) = (term182 _25579 _25580 _25581).
Proof. exact (MK_COMB (@lem1650682 _25579) (@lem1650681 _25579 _25580 _25581)). Qed.
Lemma lem1650694 (_25579 : nat) (_25580 : real) (_25581 : real) : (term185 _25580 _25581 _25579) = (term182 _25579 _25580 _25581).
Proof. exact (TRANS (@lem1650620 _25580 _25581 _25579) (@lem1650683 _25579 _25580 _25581)). Qed.
Lemma lem1650695 (_25579 : nat) (_25580 : real) (_25581 : real) : ((term158 _25580 _25581 _25579) = (term185 _25580 _25581 _25579)) = ((term182 _25579 _25580 _25581) = (term182 _25579 _25580 _25581)).
Proof. exact (MK_COMB (@lem1650615 _25579 _25580 _25581) (@lem1650694 _25579 _25580 _25581)). Qed.
Lemma lem1650697 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1650698 (x : Prop) : (x = x) = True.
Proof. exact (@lem1650697 Prop x). Qed.
Lemma lem1650699 (_25579 : nat) (_25580 : real) (_25581 : real) : ((term182 _25579 _25580 _25581) = (term182 _25579 _25580 _25581)) = True.
Proof. exact (@lem1650698 (term182 _25579 _25580 _25581)). Qed.
Lemma lem1650700 (_25580 : real) (_25581 : real) (_25579 : nat) : ((term158 _25580 _25581 _25579) = (term185 _25580 _25581 _25579)) = True.
Proof. exact (TRANS (@lem1650695 _25579 _25580 _25581) (@lem1650699 _25579 _25580 _25581)). Qed.
Lemma lem1650701 (_25580 : real) (_25581 : real) (_25579 : nat) : True = ((term158 _25580 _25581 _25579) = (term185 _25580 _25581 _25579)).
Proof. exact (SYM (@lem1650700 _25580 _25581 _25579)). Qed.
Lemma lem1650702 (_25580 : real) (_25581 : real) (_25579 : nat) : (term158 _25580 _25581 _25579) = (term185 _25580 _25581 _25579).
Proof. exact (EQ_MP (@lem1650701 _25580 _25581 _25579) (@lem0)). Qed.
Lemma lem1650703 (_25580 : real) (_25581 : real) (_25579 : nat) (h1 : term17) : term185 _25580 _25581 _25579.
Proof. exact (EQ_MP (@lem1650702 _25580 _25581 _25579) (@lem1650380 _25580 _25581 _25579 h1)). Qed.
Lemma lem1650705 (b : Prop) (a : Prop) : (a \/ b) = (term168 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1650706 (_25579 : nat) (_25580 : real) (_25581 : real) : (term185 _25580 _25581 _25579) = (term189 _25579 _25580 _25581).
Proof. exact (@lem1650705 (term190 _25580 _25581 _25579) (term157 _25580 _25581)). Qed.
Lemma lem1650708 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1650709 (_25580 : real) (_25581 : real) (_25579 : nat) : (term193 _25580 _25581 _25579) = (term194 _25580 _25581 _25579).
Proof. exact (@lem1650708 (_25579 = (NUMERAL 0)) (term187 _25580 _25581 _25579)). Qed.
Lemma lem1650711 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1650712 (_25580 : real) (_25581 : real) (_25579 : nat) : (term195 _25580 _25581 _25579) = (term196 _25580 _25581 _25579).
Proof. exact (@lem1650711 (term156 _25580) (term137 _25580 _25581 _25579)). Qed.
Lemma lem1650714 (a : Prop) : (term170 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1650715 (_25580 : real) : (term197 _25580) = (term129 _25580).
Proof. exact (@lem1650714 (term129 _25580)). Qed.
Lemma lem1650716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1650717 (_25580 : real) : (term198 _25580) = (term199 _25580).
Proof. exact (MK_COMB (@lem1650716) (@lem1650715 _25580)). Qed.
Lemma lem1650718 (_25580 : real) (_25581 : real) (_25579 : nat) : (term175 _25580 _25581 _25579) = (term175 _25580 _25581 _25579).
Proof. exact (eq_refl (term175 _25580 _25581 _25579)). Qed.
Lemma lem1650719 (_25580 : real) (_25581 : real) (_25579 : nat) : (term196 _25580 _25581 _25579) = (term200 _25580 _25581 _25579).
Proof. exact (MK_COMB (@lem1650717 _25580) (@lem1650718 _25580 _25581 _25579)). Qed.
Lemma lem1650720 (_25580 : real) (_25581 : real) (_25579 : nat) : (term195 _25580 _25581 _25579) = (term200 _25580 _25581 _25579).
Proof. exact (TRANS (@lem1650712 _25580 _25581 _25579) (@lem1650719 _25580 _25581 _25579)). Qed.
Lemma lem1650721 (_25579 : nat) : (term201 _25579) = (term201 _25579).
Proof. exact (eq_refl (term201 _25579)). Qed.
Lemma lem1650722 (_25580 : real) (_25581 : real) (_25579 : nat) : (term194 _25580 _25581 _25579) = (term202 _25580 _25581 _25579).
Proof. exact (MK_COMB (@lem1650721 _25579) (@lem1650720 _25580 _25581 _25579)). Qed.
Lemma lem1650723 (_25580 : real) (_25581 : real) (_25579 : nat) : (term193 _25580 _25581 _25579) = (term202 _25580 _25581 _25579).
Proof. exact (TRANS (@lem1650709 _25580 _25581 _25579) (@lem1650722 _25580 _25581 _25579)). Qed.
Lemma lem1650724 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1650725 (_25580 : real) (_25581 : real) (_25579 : nat) : (term203 _25580 _25581 _25579) = (term204 _25580 _25581 _25579).
Proof. exact (MK_COMB (@lem1650724) (@lem1650723 _25580 _25581 _25579)). Qed.
Lemma lem1650726 (_25580 : real) (_25581 : real) : (term157 _25580 _25581) = (term157 _25580 _25581).
Proof. exact (eq_refl (term157 _25580 _25581)). Qed.
Lemma lem1650727 (_25579 : nat) (_25580 : real) (_25581 : real) : (term189 _25579 _25580 _25581) = (term205 _25579 _25580 _25581).
Proof. exact (MK_COMB (@lem1650725 _25580 _25581 _25579) (@lem1650726 _25580 _25581)). Qed.
Lemma lem1650728 (_25579 : nat) (_25580 : real) (_25581 : real) : (term185 _25580 _25581 _25579) = (term205 _25579 _25580 _25581).
Proof. exact (TRANS (@lem1650706 _25579 _25580 _25581) (@lem1650727 _25579 _25580 _25581)). Qed.
Lemma lem1650730 (n : nat) (x : real) (y : real) (h1 : term33) (h2 : term41 n x y) : term200 y x n.
Proof. exact (conj (@lem1650487 n x y h2) (@lem1650544 n x y h1 h2)). Qed.
Lemma lem1650731 (n : nat) (x : real) (y : real) (h1 : term33) (h2 : term41 n x y) : term202 y x n.
Proof. exact (conj (@lem1650480 n x y h2) (@lem1650730 n x y h1 h2)). Qed.
Lemma lem1650733 (_25579 : nat) (_25580 : real) (_25581 : real) (h1 : term17) : term205 _25579 _25580 _25581.
Proof. exact (EQ_MP (@lem1650728 _25579 _25580 _25581) (@lem1650703 _25580 _25581 _25579 h1)). Qed.
Lemma lem1650734 (n : nat) (y : real) (x : real) (h1 : term17) : term205 n y x.
Proof. exact (@lem1650733 n y x h1). Qed.
Lemma lem1650737 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : term157 y x.
Proof. exact (@lem1650734 n y x h1 (@lem1650731 n x y h2 h3)). Qed.
Lemma lem1650738 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : term206 y x.
Proof. exact (fun h0 : real_lt y x => @lem1650737 n x y h1 h2 h3). Qed.
Lemma lem1650740 (p : Prop) : (term160 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1650741 (y : real) (x : real) : (term206 y x) = (term157 y x).
Proof. exact (@lem1650740 (real_lt y x)). Qed.
Lemma lem1650742 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : term157 y x.
Proof. exact (EQ_MP (@lem1650741 y x) (@lem1650738 n x y h1 h2 h3)). Qed.
Lemma lem1650744 (b : Prop) (a : Prop) : (a \/ b) = (term168 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1650747 (_25584 : real) (_25585 : real) : (term71 _25585 _25584) = (term207 _25584 _25585).
Proof. exact (@lem1650744 (real_lt _25585 _25584) (real_le _25584 _25585)). Qed.
Lemma lem1650750 (_25584 : real) (_25585 : real) (h1 : term33) : term207 _25584 _25585.
Proof. exact (EQ_MP (@lem1650747 _25584 _25585) (@lem1650400 _25585 _25584 h1)). Qed.
Lemma lem1650751 (x : real) (y : real) (h1 : term33) : term207 x y.
Proof. exact (@lem1650750 x y h1). Qed.
Lemma lem1650754 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : real_le x y.
Proof. exact (@lem1650751 x y h2 (@lem1650742 n x y h1 h2 h3)). Qed.
Lemma lem1650755 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : term208 x y.
Proof. exact (fun h0 : term29 x y => @lem1650754 n x y h1 h2 h3). Qed.
Lemma lem1650757 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1650758 (x : real) (y : real) : (term208 x y) = (real_le x y).
Proof. exact (@lem1650757 (real_le x y)). Qed.
Lemma lem1650759 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : real_le x y.
Proof. exact (EQ_MP (@lem1650758 x y) (@lem1650755 n x y h1 h2 h3)). Qed.
Lemma lem1650762 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1650764 (x : real) (y : real) : (term29 x y) = (term209 x y).
Proof. exact (@lem1650762 (real_le x y)). Qed.
Lemma lem1650767 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term209 x y.
Proof. exact (EQ_MP (@lem1650764 x y) (@lem1650382 n x y h1)). Qed.
Lemma lem1650770 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : False.
Proof. exact (@lem1650767 n x y h3 (@lem1650759 n x y h1 h2 h3)). Qed.
Lemma lem1650771 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : term210.
Proof. exact (fun h0 : ~ False => @lem1650770 n x y h1 h2 h3). Qed.
Lemma lem1650773 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1650774 : term210 = False.
Proof. exact (@lem1650773 False). Qed.
Lemma lem1650775 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : False.
Proof. exact (EQ_MP (@lem1650774) (@lem1650771 n x y h1 h2 h3)). Qed.
Lemma lem1650776 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : (term41 n x y) = False.
Proof. exact (prop_ext (fun h4 : term41 n x y => @lem1650775 n x y h1 h2 h3) (fun h4 : False => @lem1650254 n x y h3)). Qed.
Lemma lem1650777 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : False.
Proof. exact (EQ_MP (@lem1650776 n x y h1 h2 h3) (@lem1650254 n x y h3)). Qed.
Lemma lem1650778 (n : nat) (x : real) (h1 : term17) (h2 : term33) (h3 : term51 n x) : False.
Proof. exact (ex_elim (@lem1650102 n x h3) (fun y : real => fun h0 : term50 n x y => @lem1650777 n x y h1 h2 h0)). Qed.
Lemma lem1650779 (n : nat) (h1 : term17) (h2 : term33) (h3 : term58 n) : False.
Proof. exact (ex_elim (@lem1650101 n h3) (fun x : real => fun h0 : term57 n x => @lem1650778 n x h1 h2 h0)). Qed.
Lemma lem1650780 (h1 : term17) (h2 : term33) (h3 : term10) : False.
Proof. exact (ex_elim (@lem1649720 h3) (fun n : nat => fun h0 : term65 n => @lem1650779 n h1 h2 h0)). Qed.
Lemma lem1650781 (h1 : term33) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1650780 h0 h1 h2). Qed.
Lemma lem1650782 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1650783 (h1 : term33) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem1650782) (@lem1650781 h1 h2)). Qed.
Lemma lem1650784 (h1 : term10) : term20.
Proof. exact (fun h0 : term33 => @lem1650783 h0 h1). Qed.
Lemma lem1650785 : term22.
Proof. exact (fun h0 : term10 => @lem1650784 h0). Qed.
Lemma lem1650786 : term11.
Proof. exact (EQ_MP (@lem1649611) (@lem1650785)). Qed.
Lemma lem1650788 : term11.
Proof. exact (@lem1649409 (@lem1650786)). Qed.
Lemma lem1650789 (h1 : term10) : term19.
Proof. exact (@lem1650788 (@lem1649394 h1)). Qed.
Lemma lem1650790 (h1 : term10) : term15.
Proof. exact (@lem1650789 h1 (@lem1495933)). Qed.
Lemma lem1650791 (h1 : term10) : False.
Proof. exact (@lem1650790 h1 (@lem1638321)). Qed.
Lemma lem1650792 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1650791 h1) (fun h2 : False => @lem1649394 h1)). Qed.
Lemma lem1650793 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1650792 h1) (@lem1649394 h1)). Qed.
Lemma lem1650794 : term9.
Proof. exact (fun h0 : term10 => @lem1650793 h0). Qed.
Lemma lem1650795 : term8.
Proof. exact (EQ_MP (@lem1649393) (@lem1650794)). Qed.
