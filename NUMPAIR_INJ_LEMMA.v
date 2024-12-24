Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMPAIR_INJ_LEMMA_term_abbrevs.
Require Import EQ_MULT_LCANCEL_spec.
Require Import EVEN_ADD_spec.
Require Import EVEN_MULT_spec.
Require Import MULT_ASSOC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import NUMPAIR_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm515916_spec.
Require Import thm516204_spec.
Require Import thm516372_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm86199_spec.
Lemma lem1047285 : term0.
Proof. exact (EQ_MP (@lem516372) (@lem0)). Qed.
Lemma lem1047286 : term1.
Proof. exact (proj2 (@lem1047285)). Qed.
Lemma lem1047287 : term2.
Proof. exact (proj2 (@lem1047286)). Qed.
Lemma lem1047288 : term3.
Proof. exact (proj2 (@lem1047287)). Qed.
Lemma lem1047289 (n : nat) : term4 n.
Proof. exact (@lem1047288 n). Qed.
Lemma lem1047290 (n : nat) : (term4 n) = ((term5 n) = False).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem1047292 : term6.
Proof. exact (proj1 (@lem1047287)). Qed.
Lemma lem1047293 (n : nat) : term7 n.
Proof. exact (@lem1047292 n). Qed.
Lemma lem1047294 (n : nat) : (term7 n) = ((term8 n) = True).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem1047297 : term9.
Proof. exact (proj1 (@lem1047285)). Qed.
Lemma lem1047298 (n : nat) : term10 n.
Proof. exact (@lem1047297 n). Qed.
Lemma lem1047299 (n : nat) : (term10 n) = ((term11 n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem1047519 (m : nat) : term12 m.
Proof. exact (@lem125496 m). Qed.
Lemma lem1047520 (m : nat) : (term12 m) = (term13 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem1047521 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem1047520 m) (@lem1047519 m)). Qed.
Lemma lem1047522 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem1047521 m n). Qed.
Lemma lem1047523 (m : nat) (n : nat) : (term14 m n) = ((term15 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem1047525 (m : nat) : term16 m.
Proof. exact (@lem126076 m). Qed.
Lemma lem1047526 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem1047527 (m : nat) : term17 m.
Proof. exact (EQ_MP (@lem1047526 m) (@lem1047525 m)). Qed.
Lemma lem1047528 (m : nat) (n : nat) : term18 m n.
Proof. exact (@lem1047527 m n). Qed.
Lemma lem1047529 (m : nat) (n : nat) : (term18 m n) = ((term19 m n) = (term20 m n)).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem1047531 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem1047534 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1047535 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem1047534 n h1)). Qed.
Lemma lem1047536 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem1047537 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem1047536 n h1)). Qed.
Lemma lem1047538 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem1047535 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem1047537 n h1)). Qed.
Lemma lem1047539 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1047540 (n : nat) : (term21 n) = (term22 n).
Proof. exact (MK_COMB (@lem1047539) (@lem1047538 n)). Qed.
Lemma lem1047541 : term23 = term24.
Proof. exact (fun_ext (fun n : nat => @lem1047540 n)). Qed.
Lemma lem1047542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1047543 : term25 = term26.
Proof. exact (MK_COMB (@lem1047542) (@lem1047541)). Qed.
Lemma lem1047544 : term26.
Proof. exact (EQ_MP (@lem1047543) (@lem75570)). Qed.
Lemma lem1047548 (m : nat) (n : nat) (p : nat) (h1 : (term27 m n p) = (term28 m n p)) : (term27 m n p) = (term28 m n p).
Proof. exact (h1). Qed.
Lemma lem1047549 (m : nat) (n : nat) (p : nat) (h1 : (term27 m n p) = (term28 m n p)) : (term28 m n p) = (term27 m n p).
Proof. exact (SYM (@lem1047548 m n p h1)). Qed.
Lemma lem1047550 (m : nat) (n : nat) (p : nat) (h1 : (term28 m n p) = (term27 m n p)) : (term28 m n p) = (term27 m n p).
Proof. exact (h1). Qed.
Lemma lem1047551 (m : nat) (n : nat) (p : nat) (h1 : (term28 m n p) = (term27 m n p)) : (term27 m n p) = (term28 m n p).
Proof. exact (SYM (@lem1047550 m n p h1)). Qed.
Lemma lem1047552 (m : nat) (n : nat) (p : nat) : ((term27 m n p) = (term28 m n p)) = ((term28 m n p) = (term27 m n p)).
Proof. exact (prop_ext (fun h1 : (term27 m n p) = (term28 m n p) => @lem1047549 m n p h1) (fun h1 : (term28 m n p) = (term27 m n p) => @lem1047551 m n p h1)). Qed.
Lemma lem1047553 (m : nat) (n : nat) : (term29 m n) = (term30 m n).
Proof. exact (fun_ext (fun p : nat => @lem1047552 m n p)). Qed.
Lemma lem1047554 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1047555 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (MK_COMB (@lem1047554) (@lem1047553 m n)). Qed.
Lemma lem1047556 (m : nat) : (term33 m) = (term34 m).
Proof. exact (fun_ext (fun n : nat => @lem1047555 m n)). Qed.
Lemma lem1047557 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1047558 (m : nat) : (term35 m) = (term36 m).
Proof. exact (MK_COMB (@lem1047557) (@lem1047556 m)). Qed.
Lemma lem1047559 : term37 = term38.
Proof. exact (fun_ext (fun m : nat => @lem1047558 m)). Qed.
Lemma lem1047560 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1047561 : term39 = term40.
Proof. exact (MK_COMB (@lem1047560) (@lem1047559)). Qed.
Lemma lem1047562 : term40.
Proof. exact (EQ_MP (@lem1047561) (@lem82357)). Qed.
Lemma lem1047563 (x : nat) : term41 x.
Proof. exact (@lem1046874 x). Qed.
Lemma lem1047564 (x : nat) : (term41 x) = (term42 x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1047565 (x : nat) : term42 x.
Proof. exact (EQ_MP (@lem1047564 x) (@lem1047563 x)). Qed.
Lemma lem1047566 (x : nat) (y : nat) : term43 x y.
Proof. exact (@lem1047565 x y). Qed.
Lemma lem1047567 (x : nat) (y : nat) : (term43 x y) = ((NUMPAIR x y) = (term44 x y)).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1047592 (x : nat) (y : nat) : (NUMPAIR x y) = (term44 x y).
Proof. exact (EQ_MP (@lem1047567 x y) (@lem1047566 x y)). Qed.
Lemma lem1047593 (x1 : nat) (y1 : nat) : (NUMPAIR x1 y1) = (term44 x1 y1).
Proof. exact (@lem1047592 x1 y1). Qed.
Lemma lem1047594 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1047595 (x1 : nat) (y1 : nat) : (term45 x1 y1) = (term46 x1 y1).
Proof. exact (MK_COMB (@lem1047594) (@lem1047593 x1 y1)). Qed.
Lemma lem1047597 (x : nat) (y : nat) : (NUMPAIR x y) = (term44 x y).
Proof. exact (EQ_MP (@lem1047567 x y) (@lem1047566 x y)). Qed.
Lemma lem1047598 (x2 : nat) (y2 : nat) : (NUMPAIR x2 y2) = (term44 x2 y2).
Proof. exact (@lem1047597 x2 y2). Qed.
Lemma lem1047599 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = ((term44 x1 y1) = (term44 x2 y2)).
Proof. exact (MK_COMB (@lem1047595 x1 y1) (@lem1047598 x2 y2)). Qed.
Lemma lem1047602 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1047603 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term47 x1 y1 x2 y2) = (term48 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1047602) (@lem1047599 x1 y1 x2 y2)). Qed.
Lemma lem1047606 (x1 : nat) (x2 : nat) : (x1 = x2) = (x1 = x2).
Proof. exact (eq_refl (x1 = x2)). Qed.
Lemma lem1047607 (y1 : nat) (y2 : nat) (x1 : nat) (x2 : nat) : (term49 y1 y2 x1 x2) = (term50 y1 y2 x1 x2).
Proof. exact (MK_COMB (@lem1047603 x1 y1 x2 y2) (@lem1047606 x1 x2)). Qed.
Lemma lem1047612 (y1 : nat) (x1 : nat) (x2 : nat) : (term51 y1 x1 x2) = (term52 y1 x1 x2).
Proof. exact (fun_ext (fun y2 : nat => @lem1047607 y1 y2 x1 x2)). Qed.
Lemma lem1047613 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1047614 (y1 : nat) (x1 : nat) (x2 : nat) : (term53 y1 x1 x2) = (term54 y1 x1 x2).
Proof. exact (MK_COMB (@lem1047613) (@lem1047612 y1 x1 x2)). Qed.
Lemma lem1047619 (y1 : nat) (x1 : nat) : (term55 y1 x1) = (term56 y1 x1).
Proof. exact (fun_ext (fun x2 : nat => @lem1047614 y1 x1 x2)). Qed.
Lemma lem1047620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1047621 (y1 : nat) (x1 : nat) : (term57 y1 x1) = (term58 y1 x1).
Proof. exact (MK_COMB (@lem1047620) (@lem1047619 y1 x1)). Qed.
Lemma lem1047626 (x1 : nat) : (term59 x1) = (term60 x1).
Proof. exact (fun_ext (fun y1 : nat => @lem1047621 y1 x1)). Qed.
Lemma lem1047627 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1047628 (x1 : nat) : (term61 x1) = (term62 x1).
Proof. exact (MK_COMB (@lem1047627) (@lem1047626 x1)). Qed.
Lemma lem1047633 : term63 = term64.
Proof. exact (fun_ext (fun x1 : nat => @lem1047628 x1)). Qed.
Lemma lem1047634 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1047635 : term65 = term66.
Proof. exact (MK_COMB (@lem1047634) (@lem1047633)). Qed.
Lemma lem1047640 : term66 = term65.
Proof. exact (SYM (@lem1047635)). Qed.
Lemma lem1047642 (P : nat -> Prop) : term67 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1047643 : term68.
Proof. exact (@lem1047642 term64). Qed.
Lemma lem1047644 : term69 = term70.
Proof. exact (eq_refl term69). Qed.
Lemma lem1047645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1047646 : term71 = term72.
Proof. exact (MK_COMB (@lem1047645) (@lem1047644)). Qed.
Lemma lem1047647 (x1 : nat) : (term73 x1) = (term62 x1).
Proof. exact (eq_refl (term73 x1)). Qed.
Lemma lem1047648 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1047649 (x1 : nat) : (term74 x1) = (term75 x1).
Proof. exact (MK_COMB (@lem1047648) (@lem1047647 x1)). Qed.
Lemma lem1047650 (x1 : nat) : (term76 x1) = (term77 x1).
Proof. exact (eq_refl (term76 x1)). Qed.
Lemma lem1047651 (x1 : nat) : (term78 x1) = (term79 x1).
Proof. exact (MK_COMB (@lem1047649 x1) (@lem1047650 x1)). Qed.
Lemma lem1047652 : term80 = term81.
Proof. exact (fun_ext (fun x1 : nat => @lem1047651 x1)). Qed.
Lemma lem1047653 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1047654 : term82 = term83.
Proof. exact (MK_COMB (@lem1047653) (@lem1047652)). Qed.
Lemma lem1047655 : term84 = term85.
Proof. exact (MK_COMB (@lem1047646) (@lem1047654)). Qed.
Lemma lem1047656 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1047657 : term86 = term87.
Proof. exact (MK_COMB (@lem1047656) (@lem1047655)). Qed.
Lemma lem1047658 (x1 : nat) : (term73 x1) = (term62 x1).
Proof. exact (eq_refl (term73 x1)). Qed.
Lemma lem1047659 : term88 = term64.
Proof. exact (fun_ext (fun x1 : nat => @lem1047658 x1)). Qed.
Lemma lem1047660 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1047661 : term89 = term66.
Proof. exact (MK_COMB (@lem1047660) (@lem1047659)). Qed.
Lemma lem1047662 : term68 = term90.
Proof. exact (MK_COMB (@lem1047657) (@lem1047661)). Qed.
Lemma lem1047663 : term90.
Proof. exact (EQ_MP (@lem1047662) (@lem1047643)). Qed.
Lemma lem1047664 (x1 : nat) (h1 : term62 x1) : term62 x1.
Proof. exact (h1). Qed.
Lemma lem1047666 (P : nat -> Prop) : term67 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1047667 (y1 : nat) : term91 y1.
Proof. exact (@lem1047666 (term92 y1)). Qed.
Lemma lem1047668 (y1 : nat) : (term93 y1) = (term94 y1).
Proof. exact (eq_refl (term93 y1)). Qed.
Lemma lem1047669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1047670 (y1 : nat) : (term95 y1) = (term96 y1).
Proof. exact (MK_COMB (@lem1047669) (@lem1047668 y1)). Qed.
Lemma lem1047671 (y1 : nat) (x2 : nat) : (term97 y1 x2) = (term98 y1 x2).
Proof. exact (eq_refl (term97 y1 x2)). Qed.
Lemma lem1047672 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1047673 (y1 : nat) (x2 : nat) : (term99 y1 x2) = (term100 y1 x2).
Proof. exact (MK_COMB (@lem1047672) (@lem1047671 y1 x2)). Qed.
Lemma lem1047674 (y1 : nat) (x2 : nat) : (term101 y1 x2) = (term102 y1 x2).
Proof. exact (eq_refl (term101 y1 x2)). Qed.
Lemma lem1047675 (y1 : nat) (x2 : nat) : (term103 y1 x2) = (term104 y1 x2).
Proof. exact (MK_COMB (@lem1047673 y1 x2) (@lem1047674 y1 x2)). Qed.
Lemma lem1047676 (y1 : nat) : (term105 y1) = (term106 y1).
Proof. exact (fun_ext (fun x2 : nat => @lem1047675 y1 x2)). Qed.
Lemma lem1047677 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1047678 (y1 : nat) : (term107 y1) = (term108 y1).
Proof. exact (MK_COMB (@lem1047677) (@lem1047676 y1)). Qed.
Lemma lem1047679 (y1 : nat) : (term109 y1) = (term110 y1).
Proof. exact (MK_COMB (@lem1047670 y1) (@lem1047678 y1)). Qed.
Lemma lem1047680 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1047681 (y1 : nat) : (term111 y1) = (term112 y1).
Proof. exact (MK_COMB (@lem1047680) (@lem1047679 y1)). Qed.
Lemma lem1047682 (y1 : nat) (x2 : nat) : (term97 y1 x2) = (term98 y1 x2).
Proof. exact (eq_refl (term97 y1 x2)). Qed.
Lemma lem1047683 (y1 : nat) : (term113 y1) = (term92 y1).
Proof. exact (fun_ext (fun x2 : nat => @lem1047682 y1 x2)). Qed.
Lemma lem1047684 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1047685 (y1 : nat) : (term114 y1) = (term115 y1).
Proof. exact (MK_COMB (@lem1047684) (@lem1047683 y1)). Qed.
Lemma lem1047686 (y1 : nat) : (term91 y1) = (term116 y1).
Proof. exact (MK_COMB (@lem1047681 y1) (@lem1047685 y1)). Qed.
Lemma lem1047687 (y1 : nat) : term116 y1.
Proof. exact (EQ_MP (@lem1047686 y1) (@lem1047667 y1)). Qed.
Lemma lem1047694 (P : nat -> Prop) : term67 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1047695 (y1 : nat) (x1 : nat) : term117 y1 x1.
Proof. exact (@lem1047694 (term118 y1 x1)). Qed.
Lemma lem1047696 (y1 : nat) (x1 : nat) : (term119 y1 x1) = (term120 y1 x1).
Proof. exact (eq_refl (term119 y1 x1)). Qed.
Lemma lem1047697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1047698 (y1 : nat) (x1 : nat) : (term121 y1 x1) = (term122 y1 x1).
Proof. exact (MK_COMB (@lem1047697) (@lem1047696 y1 x1)). Qed.
Lemma lem1047699 (y1 : nat) (x1 : nat) (x2 : nat) : (term123 y1 x1 x2) = (term124 y1 x1 x2).
Proof. exact (eq_refl (term123 y1 x1 x2)). Qed.
Lemma lem1047700 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1047701 (y1 : nat) (x1 : nat) (x2 : nat) : (term125 y1 x1 x2) = (term126 y1 x1 x2).
Proof. exact (MK_COMB (@lem1047700) (@lem1047699 y1 x1 x2)). Qed.
Lemma lem1047702 (y1 : nat) (x1 : nat) (x2 : nat) : (term127 y1 x1 x2) = (term128 y1 x1 x2).
Proof. exact (eq_refl (term127 y1 x1 x2)). Qed.
Lemma lem1047703 (y1 : nat) (x1 : nat) (x2 : nat) : (term129 y1 x1 x2) = (term130 y1 x1 x2).
Proof. exact (MK_COMB (@lem1047701 y1 x1 x2) (@lem1047702 y1 x1 x2)). Qed.
Lemma lem1047704 (y1 : nat) (x1 : nat) : (term131 y1 x1) = (term132 y1 x1).
Proof. exact (fun_ext (fun x2 : nat => @lem1047703 y1 x1 x2)). Qed.
Lemma lem1047705 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1047706 (y1 : nat) (x1 : nat) : (term133 y1 x1) = (term134 y1 x1).
Proof. exact (MK_COMB (@lem1047705) (@lem1047704 y1 x1)). Qed.
Lemma lem1047707 (y1 : nat) (x1 : nat) : (term135 y1 x1) = (term136 y1 x1).
Proof. exact (MK_COMB (@lem1047698 y1 x1) (@lem1047706 y1 x1)). Qed.
Lemma lem1047708 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1047709 (y1 : nat) (x1 : nat) : (term137 y1 x1) = (term138 y1 x1).
Proof. exact (MK_COMB (@lem1047708) (@lem1047707 y1 x1)). Qed.
Lemma lem1047710 (y1 : nat) (x1 : nat) (x2 : nat) : (term123 y1 x1 x2) = (term124 y1 x1 x2).
Proof. exact (eq_refl (term123 y1 x1 x2)). Qed.
Lemma lem1047711 (y1 : nat) (x1 : nat) : (term139 y1 x1) = (term118 y1 x1).
Proof. exact (fun_ext (fun x2 : nat => @lem1047710 y1 x1 x2)). Qed.
Lemma lem1047712 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1047713 (y1 : nat) (x1 : nat) : (term140 y1 x1) = (term141 y1 x1).
Proof. exact (MK_COMB (@lem1047712) (@lem1047711 y1 x1)). Qed.
Lemma lem1047714 (y1 : nat) (x1 : nat) : (term117 y1 x1) = (term142 y1 x1).
Proof. exact (MK_COMB (@lem1047709 y1 x1) (@lem1047713 y1 x1)). Qed.
Lemma lem1047715 (y1 : nat) (x1 : nat) : term142 y1 x1.
Proof. exact (EQ_MP (@lem1047714 y1 x1) (@lem1047695 y1 x1)). Qed.
Lemma lem1047759 (m : nat) : term143 m.
Proof. exact (@lem84830 m). Qed.
Lemma lem1047760 (m : nat) : (term143 m) = (term144 m).
Proof. exact (eq_refl (term143 m)). Qed.
Lemma lem1047761 (m : nat) : term144 m.
Proof. exact (EQ_MP (@lem1047760 m) (@lem1047759 m)). Qed.
Lemma lem1047762 (m : nat) (n : nat) : term145 m n.
Proof. exact (@lem1047761 m n). Qed.
Lemma lem1047763 (m : nat) (n : nat) : (term145 m n) = (term146 m n).
Proof. exact (eq_refl (term145 m n)). Qed.
Lemma lem1047764 (m : nat) (n : nat) : term146 m n.
Proof. exact (EQ_MP (@lem1047763 m n) (@lem1047762 m n)). Qed.
Lemma lem1047765 (m : nat) (n : nat) (p : nat) : term147 m n p.
Proof. exact (@lem1047764 m n p). Qed.
Lemma lem1047766 (m : nat) (n : nat) (p : nat) : (term147 m n p) = (((Nat.mul m n) = (Nat.mul m p)) = (term148 m n p)).
Proof. exact (eq_refl (term147 m n p)). Qed.
Lemma lem1048101 : term149.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem1048102 : term150.
Proof. exact (proj2 (@lem1048101)). Qed.
Lemma lem1048103 : term151.
Proof. exact (proj2 (@lem1048102)). Qed.
Lemma lem1048104 : term152.
Proof. exact (proj2 (@lem1048103)). Qed.
Lemma lem1048146 : term153.
Proof. exact (proj1 (@lem1048104)). Qed.
Lemma lem1048147 (n : nat) : term154 n.
Proof. exact (@lem1048146 n). Qed.
Lemma lem1048148 (n : nat) : (term154 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term154 n)). Qed.
Lemma lem1048155 : term155.
Proof. exact (proj1 (@lem1048101)). Qed.
Lemma lem1048156 (m : nat) : term156 m.
Proof. exact (@lem1048155 m). Qed.
Lemma lem1048157 (m : nat) : (term156 m) = (term157 m).
Proof. exact (eq_refl (term156 m)). Qed.
Lemma lem1048158 (m : nat) : term157 m.
Proof. exact (EQ_MP (@lem1048157 m) (@lem1048156 m)). Qed.
Lemma lem1048159 (m : nat) (n : nat) : term158 m n.
Proof. exact (@lem1048158 m n). Qed.
Lemma lem1048160 (m : nat) (n : nat) : (term158 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term158 m n)). Qed.
Lemma lem1048194 : term159.
Proof. exact (EQ_MP (@lem515916) (@lem516204)). Qed.
Lemma lem1048195 : term160.
Proof. exact (proj2 (@lem1048194)). Qed.
Lemma lem1048196 : term161.
Proof. exact (proj2 (@lem1048195)). Qed.
Lemma lem1048243 : term162.
Proof. exact (proj1 (@lem1048196)). Qed.
Lemma lem1048244 (m : nat) : term163 m.
Proof. exact (@lem1048243 m). Qed.
Lemma lem1048245 (m : nat) : (term163 m) = ((term164 m) = (BIT1 0)).
Proof. exact (eq_refl (term163 m)). Qed.
Lemma lem1048248 : term165.
Proof. exact (proj1 (@lem1048194)). Qed.
Lemma lem1048249 (m : nat) : term166 m.
Proof. exact (@lem1048248 m). Qed.
Lemma lem1048250 (m : nat) : (term166 m) = (term167 m).
Proof. exact (eq_refl (term166 m)). Qed.
Lemma lem1048251 (m : nat) : term167 m.
Proof. exact (EQ_MP (@lem1048250 m) (@lem1048249 m)). Qed.
Lemma lem1048252 (m : nat) (n : nat) : term168 m n.
Proof. exact (@lem1048251 m n). Qed.
Lemma lem1048253 (m : nat) (n : nat) : (term168 m n) = ((term169 m n) = (term170 m n)).
Proof. exact (eq_refl (term168 m n)). Qed.
Lemma lem1048437 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term148 m n p).
Proof. exact (EQ_MP (@lem1047766 m n p) (@lem1047765 m n p)). Qed.
Lemma lem1048438 (y1 : nat) (y2 : nat) : ((term171 y1) = (term171 y2)) = (term172 y1 y2).
Proof. exact (@lem1048437 term173 (term174 y1) (term174 y2)). Qed.
Lemma lem1048444 (m : nat) (n : nat) : (term169 m n) = (term170 m n).
Proof. exact (EQ_MP (@lem1048253 m n) (@lem1048252 m n)). Qed.
Lemma lem1048445 : term173 = term175.
Proof. exact (@lem1048444 term176 0). Qed.
Lemma lem1048447 (m : nat) : (term164 m) = (BIT1 0).
Proof. exact (EQ_MP (@lem1048245 m) (@lem1048244 m)). Qed.
Lemma lem1048448 : term177 = (BIT1 0).
Proof. exact (@lem1048447 (BIT1 0)). Qed.
Lemma lem1048449 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem1048450 : term175 = term178.
Proof. exact (MK_COMB (@lem1048449) (@lem1048448)). Qed.
Lemma lem1048451 : term173 = term178.
Proof. exact (TRANS (@lem1048445) (@lem1048450)). Qed.
Lemma lem1048452 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1048453 : term179 = term180.
Proof. exact (MK_COMB (@lem1048452) (@lem1048451)). Qed.
Lemma lem1048454 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1048455 : (term173 = (NUMERAL 0)) = (term178 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1048453) (@lem1048454)). Qed.
Lemma lem1048457 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1048160 m n) (@lem1048159 m n)). Qed.
Lemma lem1048458 : (term178 = (NUMERAL 0)) = ((BIT1 0) = 0).
Proof. exact (@lem1048457 (BIT1 0) 0). Qed.
Lemma lem1048460 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem1048148 n) (@lem1048147 n)). Qed.
Lemma lem1048461 : ((BIT1 0) = 0) = False.
Proof. exact (@lem1048460 0). Qed.
Lemma lem1048462 : (term178 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1048458) (@lem1048461)). Qed.
Lemma lem1048463 : (term173 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1048455) (@lem1048462)). Qed.
Lemma lem1048464 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1048465 : term181 = (or False).
Proof. exact (MK_COMB (@lem1048464) (@lem1048463)). Qed.
Lemma lem1048468 (y1 : nat) (y2 : nat) : ((term174 y1) = (term174 y2)) = ((term174 y1) = (term174 y2)).
Proof. exact (eq_refl ((term174 y1) = (term174 y2))). Qed.
Lemma lem1048469 (y1 : nat) (y2 : nat) : (term172 y1 y2) = (term182 y1 y2).
Proof. exact (MK_COMB (@lem1048465) (@lem1048468 y1 y2)). Qed.
Lemma lem1048471 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1048472 (y1 : nat) (y2 : nat) : (term182 y1 y2) = ((term174 y1) = (term174 y2)).
Proof. exact (@lem1048471 ((term174 y1) = (term174 y2))). Qed.
Lemma lem1048475 (y1 : nat) (y2 : nat) : (term172 y1 y2) = ((term174 y1) = (term174 y2)).
Proof. exact (TRANS (@lem1048469 y1 y2) (@lem1048472 y1 y2)). Qed.
Lemma lem1048476 (y1 : nat) (y2 : nat) : ((term171 y1) = (term171 y2)) = ((term174 y1) = (term174 y2)).
Proof. exact (TRANS (@lem1048438 y1 y2) (@lem1048475 y1 y2)). Qed.
Lemma lem1048477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1048478 (y1 : nat) (y2 : nat) : (term183 y1 y2) = (term184 y1 y2).
Proof. exact (MK_COMB (@lem1048477) (@lem1048476 y1 y2)). Qed.
Lemma lem1048480 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1048160 m n) (@lem1048159 m n)). Qed.
Lemma lem1048481 : ((NUMERAL 0) = (NUMERAL 0)) = (0 = 0).
Proof. exact (@lem1048480 0 0). Qed.
Lemma lem1048483 : (0 = 0) = True.
Proof. exact (proj1 (@lem1048102)). Qed.
Lemma lem1048484 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1048481) (@lem1048483)). Qed.
Lemma lem1048485 (y1 : nat) (y2 : nat) : (term185 y1 y2) = (term186 y1 y2).
Proof. exact (MK_COMB (@lem1048478 y1 y2) (@lem1048484)). Qed.
Lemma lem1048489 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1048490 (y1 : nat) (y2 : nat) : (term186 y1 y2) = True.
Proof. exact (@lem1048489 ((term174 y1) = (term174 y2))). Qed.
Lemma lem1048491 (y1 : nat) (y2 : nat) : (term185 y1 y2) = True.
Proof. exact (TRANS (@lem1048485 y1 y2) (@lem1048490 y1 y2)). Qed.
Lemma lem1048492 (y1 : nat) (y2 : nat) : True = (term185 y1 y2).
Proof. exact (SYM (@lem1048491 y1 y2)). Qed.
Lemma lem1048493 (y1 : nat) (y2 : nat) : term185 y1 y2.
Proof. exact (EQ_MP (@lem1048492 y1 y2) (@lem0)). Qed.
Lemma lem1048500 (n : nat) : term187 n.
Proof. exact (@lem1047544 n). Qed.
Lemma lem1048501 (n : nat) : (term187 n) = (term22 n).
Proof. exact (eq_refl (term187 n)). Qed.
Lemma lem1048502 (n : nat) : term22 n.
Proof. exact (EQ_MP (@lem1048501 n) (@lem1048500 n)). Qed.
Lemma lem1048503 (n : nat) : term188 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem1048967 : term159.
Proof. exact (EQ_MP (@lem515916) (@lem516204)). Qed.
Lemma lem1048968 : term160.
Proof. exact (proj2 (@lem1048967)). Qed.
Lemma lem1048969 : term161.
Proof. exact (proj2 (@lem1048968)). Qed.
Lemma lem1049016 : term162.
Proof. exact (proj1 (@lem1048969)). Qed.
Lemma lem1049017 (m : nat) : term163 m.
Proof. exact (@lem1049016 m). Qed.
Lemma lem1049018 (m : nat) : (term163 m) = ((term164 m) = (BIT1 0)).
Proof. exact (eq_refl (term163 m)). Qed.
Lemma lem1049021 : term165.
Proof. exact (proj1 (@lem1048967)). Qed.
Lemma lem1049022 (m : nat) : term166 m.
Proof. exact (@lem1049021 m). Qed.
Lemma lem1049023 (m : nat) : (term166 m) = (term167 m).
Proof. exact (eq_refl (term166 m)). Qed.
Lemma lem1049024 (m : nat) : term167 m.
Proof. exact (EQ_MP (@lem1049023 m) (@lem1049022 m)). Qed.
Lemma lem1049025 (m : nat) (n : nat) : term168 m n.
Proof. exact (@lem1049024 m n). Qed.
Lemma lem1049026 (m : nat) (n : nat) : (term168 m n) = ((term169 m n) = (term170 m n)).
Proof. exact (eq_refl (term168 m n)). Qed.
Lemma lem1049185 (m : nat) : term189 m.
Proof. exact (@lem1047562 m). Qed.
Lemma lem1049186 (m : nat) : (term189 m) = (term36 m).
Proof. exact (eq_refl (term189 m)). Qed.
Lemma lem1049187 (m : nat) : term36 m.
Proof. exact (EQ_MP (@lem1049186 m) (@lem1049185 m)). Qed.
Lemma lem1049188 (m : nat) (n : nat) : term190 m n.
Proof. exact (@lem1049187 m n). Qed.
Lemma lem1049189 (m : nat) (n : nat) : (term190 m n) = (term32 m n).
Proof. exact (eq_refl (term190 m n)). Qed.
Lemma lem1049190 (m : nat) (n : nat) : term32 m n.
Proof. exact (EQ_MP (@lem1049189 m n) (@lem1049188 m n)). Qed.
Lemma lem1049191 (m : nat) (n : nat) (p : nat) : term191 m n p.
Proof. exact (@lem1049190 m n p). Qed.
Lemma lem1049192 (m : nat) (n : nat) (p : nat) : (term191 m n p) = ((term28 m n p) = (term27 m n p)).
Proof. exact (eq_refl (term191 m n p)). Qed.
Lemma lem1049194 : term192.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem1049195 (m : nat) : term193 m.
Proof. exact (@lem1049194 m). Qed.
Lemma lem1049196 (m : nat) : (term193 m) = (term194 m).
Proof. exact (eq_refl (term193 m)). Qed.
Lemma lem1049197 (m : nat) : term194 m.
Proof. exact (EQ_MP (@lem1049196 m) (@lem1049195 m)). Qed.
Lemma lem1049198 (m : nat) (n : nat) : term195 m n.
Proof. exact (@lem1049197 m n). Qed.
Lemma lem1049199 (m : nat) (n : nat) : (term195 m n) = ((term196 m n) = (term197 m n)).
Proof. exact (eq_refl (term195 m n)). Qed.
Lemma lem1049219 (m : nat) (n : nat) : (term169 m n) = (term170 m n).
Proof. exact (EQ_MP (@lem1049026 m n) (@lem1049025 m n)). Qed.
Lemma lem1049220 : term173 = term175.
Proof. exact (@lem1049219 term176 0). Qed.
Lemma lem1049222 (m : nat) : (term164 m) = (BIT1 0).
Proof. exact (EQ_MP (@lem1049018 m) (@lem1049017 m)). Qed.
Lemma lem1049223 : term177 = (BIT1 0).
Proof. exact (@lem1049222 (BIT1 0)). Qed.
Lemma lem1049224 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem1049225 : term175 = term178.
Proof. exact (MK_COMB (@lem1049224) (@lem1049223)). Qed.
Lemma lem1049226 : term173 = term178.
Proof. exact (TRANS (@lem1049220) (@lem1049225)). Qed.
Lemma lem1049227 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1049228 : term198 = term199.
Proof. exact (MK_COMB (@lem1049227) (@lem1049226)). Qed.
Lemma lem1049229 (y1 : nat) : (term174 y1) = (term174 y1).
Proof. exact (eq_refl (term174 y1)). Qed.
Lemma lem1049230 (y1 : nat) : (term171 y1) = (term200 y1).
Proof. exact (MK_COMB (@lem1049228) (@lem1049229 y1)). Qed.
Lemma lem1049231 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1049232 (y1 : nat) : (term201 y1) = (term202 y1).
Proof. exact (MK_COMB (@lem1049231) (@lem1049230 y1)). Qed.
Lemma lem1049234 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (EQ_MP (@lem1049199 m n) (@lem1049198 m n)). Qed.
Lemma lem1049235 (x2 : nat) : (term203 x2) = (term204 x2).
Proof. exact (@lem1049234 term205 x2). Qed.
Lemma lem1049236 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1049237 (x2 : nat) : (term206 x2) = (term207 x2).
Proof. exact (MK_COMB (@lem1049236) (@lem1049235 x2)). Qed.
Lemma lem1049238 (y2 : nat) : (term174 y2) = (term174 y2).
Proof. exact (eq_refl (term174 y2)). Qed.
Lemma lem1049239 (x2 : nat) (y2 : nat) : (term208 x2 y2) = (term209 x2 y2).
Proof. exact (MK_COMB (@lem1049237 x2) (@lem1049238 y2)). Qed.
Lemma lem1049241 (m : nat) (n : nat) (p : nat) : (term28 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1049192 m n p) (@lem1049191 m n p)). Qed.
Lemma lem1049242 (x2 : nat) (y2 : nat) : (term209 x2 y2) = (term210 x2 y2).
Proof. exact (@lem1049241 term205 (term211 x2) (term174 y2)). Qed.
Lemma lem1049243 (x2 : nat) (y2 : nat) : (term208 x2 y2) = (term210 x2 y2).
Proof. exact (TRANS (@lem1049239 x2 y2) (@lem1049242 x2 y2)). Qed.
Lemma lem1049244 (y1 : nat) (x2 : nat) (y2 : nat) : ((term171 y1) = (term208 x2 y2)) = ((term200 y1) = (term210 x2 y2)).
Proof. exact (MK_COMB (@lem1049232 y1) (@lem1049243 x2 y2)). Qed.
Lemma lem1049249 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1049250 (y1 : nat) (x2 : nat) (y2 : nat) : (term212 y1 x2 y2) = (term213 y1 x2 y2).
Proof. exact (MK_COMB (@lem1049249) (@lem1049244 y1 x2 y2)). Qed.
Lemma lem1049252 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem1048503 n (@lem1048502 n)). Qed.
Lemma lem1049253 (x2 : nat) : ((NUMERAL 0) = (S x2)) = False.
Proof. exact (@lem1049252 x2). Qed.
Lemma lem1049254 (y1 : nat) (x2 : nat) (y2 : nat) : (term214 y1 y2 x2) = (term215 y1 x2 y2).
Proof. exact (MK_COMB (@lem1049250 y1 x2 y2) (@lem1049253 x2)). Qed.
Lemma lem1049258 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1049259 (y1 : nat) (x2 : nat) (y2 : nat) : (term215 y1 x2 y2) = (term216 y1 x2 y2).
Proof. exact (@lem1049258 ((term200 y1) = (term210 x2 y2))). Qed.
Lemma lem1049264 (y1 : nat) (x2 : nat) (y2 : nat) : (term214 y1 y2 x2) = (term216 y1 x2 y2).
Proof. exact (TRANS (@lem1049254 y1 x2 y2) (@lem1049259 y1 x2 y2)). Qed.
Lemma lem1049265 (y1 : nat) (y2 : nat) (x2 : nat) : (term216 y1 x2 y2) = (term214 y1 y2 x2).
Proof. exact (SYM (@lem1049264 y1 x2 y2)). Qed.
Lemma lem1049272 (n : nat) : term187 n.
Proof. exact (@lem1047544 n). Qed.
Lemma lem1049273 (n : nat) : (term187 n) = (term22 n).
Proof. exact (eq_refl (term187 n)). Qed.
Lemma lem1049274 (n : nat) : term22 n.
Proof. exact (EQ_MP (@lem1049273 n) (@lem1049272 n)). Qed.
Lemma lem1049278 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem1049279 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem1049278 n h1)). Qed.
Lemma lem1049280 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1049281 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem1049280 n h1)). Qed.
Lemma lem1049282 (n : nat) : ((NUMERAL 0) = (S n)) = ((S n) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h1 : (NUMERAL 0) = (S n) => @lem1049279 n h1) (fun h1 : (S n) = (NUMERAL 0) => @lem1049281 n h1)). Qed.
Lemma lem1049283 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1049284 (n : nat) : (term22 n) = (term21 n).
Proof. exact (MK_COMB (@lem1049283) (@lem1049282 n)). Qed.
Lemma lem1049285 (n : nat) : term21 n.
Proof. exact (EQ_MP (@lem1049284 n) (@lem1049274 n)). Qed.
Lemma lem1049286 (n : nat) : term217 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem1049739 : term159.
Proof. exact (EQ_MP (@lem515916) (@lem516204)). Qed.
Lemma lem1049740 : term160.
Proof. exact (proj2 (@lem1049739)). Qed.
Lemma lem1049741 : term161.
Proof. exact (proj2 (@lem1049740)). Qed.
Lemma lem1049788 : term162.
Proof. exact (proj1 (@lem1049741)). Qed.
Lemma lem1049789 (m : nat) : term163 m.
Proof. exact (@lem1049788 m). Qed.
Lemma lem1049790 (m : nat) : (term163 m) = ((term164 m) = (BIT1 0)).
Proof. exact (eq_refl (term163 m)). Qed.
Lemma lem1049793 : term165.
Proof. exact (proj1 (@lem1049739)). Qed.
Lemma lem1049794 (m : nat) : term166 m.
Proof. exact (@lem1049793 m). Qed.
Lemma lem1049795 (m : nat) : (term166 m) = (term167 m).
Proof. exact (eq_refl (term166 m)). Qed.
Lemma lem1049796 (m : nat) : term167 m.
Proof. exact (EQ_MP (@lem1049795 m) (@lem1049794 m)). Qed.
Lemma lem1049797 (m : nat) (n : nat) : term168 m n.
Proof. exact (@lem1049796 m n). Qed.
Lemma lem1049798 (m : nat) (n : nat) : (term168 m n) = ((term169 m n) = (term170 m n)).
Proof. exact (eq_refl (term168 m n)). Qed.
Lemma lem1049957 (m : nat) : term189 m.
Proof. exact (@lem1047562 m). Qed.
Lemma lem1049958 (m : nat) : (term189 m) = (term36 m).
Proof. exact (eq_refl (term189 m)). Qed.
Lemma lem1049959 (m : nat) : term36 m.
Proof. exact (EQ_MP (@lem1049958 m) (@lem1049957 m)). Qed.
Lemma lem1049960 (m : nat) (n : nat) : term190 m n.
Proof. exact (@lem1049959 m n). Qed.
Lemma lem1049961 (m : nat) (n : nat) : (term190 m n) = (term32 m n).
Proof. exact (eq_refl (term190 m n)). Qed.
Lemma lem1049962 (m : nat) (n : nat) : term32 m n.
Proof. exact (EQ_MP (@lem1049961 m n) (@lem1049960 m n)). Qed.
Lemma lem1049963 (m : nat) (n : nat) (p : nat) : term191 m n p.
Proof. exact (@lem1049962 m n p). Qed.
Lemma lem1049964 (m : nat) (n : nat) (p : nat) : (term191 m n p) = ((term28 m n p) = (term27 m n p)).
Proof. exact (eq_refl (term191 m n p)). Qed.
Lemma lem1049966 : term192.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem1049967 (m : nat) : term193 m.
Proof. exact (@lem1049966 m). Qed.
Lemma lem1049968 (m : nat) : (term193 m) = (term194 m).
Proof. exact (eq_refl (term193 m)). Qed.
Lemma lem1049969 (m : nat) : term194 m.
Proof. exact (EQ_MP (@lem1049968 m) (@lem1049967 m)). Qed.
Lemma lem1049970 (m : nat) (n : nat) : term195 m n.
Proof. exact (@lem1049969 m n). Qed.
Lemma lem1049971 (m : nat) (n : nat) : (term195 m n) = ((term196 m n) = (term197 m n)).
Proof. exact (eq_refl (term195 m n)). Qed.
Lemma lem1049997 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (EQ_MP (@lem1049971 m n) (@lem1049970 m n)). Qed.
Lemma lem1049998 (x1 : nat) : (term203 x1) = (term204 x1).
Proof. exact (@lem1049997 term205 x1). Qed.
Lemma lem1049999 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1050000 (x1 : nat) : (term206 x1) = (term207 x1).
Proof. exact (MK_COMB (@lem1049999) (@lem1049998 x1)). Qed.
Lemma lem1050001 (y1 : nat) : (term174 y1) = (term174 y1).
Proof. exact (eq_refl (term174 y1)). Qed.
Lemma lem1050002 (x1 : nat) (y1 : nat) : (term208 x1 y1) = (term209 x1 y1).
Proof. exact (MK_COMB (@lem1050000 x1) (@lem1050001 y1)). Qed.
Lemma lem1050004 (m : nat) (n : nat) (p : nat) : (term28 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1049964 m n p) (@lem1049963 m n p)). Qed.
Lemma lem1050005 (x1 : nat) (y1 : nat) : (term209 x1 y1) = (term210 x1 y1).
Proof. exact (@lem1050004 term205 (term211 x1) (term174 y1)). Qed.
Lemma lem1050006 (x1 : nat) (y1 : nat) : (term208 x1 y1) = (term210 x1 y1).
Proof. exact (TRANS (@lem1050002 x1 y1) (@lem1050005 x1 y1)). Qed.
Lemma lem1050007 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1050008 (x1 : nat) (y1 : nat) : (term218 x1 y1) = (term219 x1 y1).
Proof. exact (MK_COMB (@lem1050007) (@lem1050006 x1 y1)). Qed.
Lemma lem1050010 (m : nat) (n : nat) : (term169 m n) = (term170 m n).
Proof. exact (EQ_MP (@lem1049798 m n) (@lem1049797 m n)). Qed.
Lemma lem1050011 : term173 = term175.
Proof. exact (@lem1050010 term176 0). Qed.
Lemma lem1050013 (m : nat) : (term164 m) = (BIT1 0).
Proof. exact (EQ_MP (@lem1049790 m) (@lem1049789 m)). Qed.
Lemma lem1050014 : term177 = (BIT1 0).
Proof. exact (@lem1050013 (BIT1 0)). Qed.
Lemma lem1050015 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem1050016 : term175 = term178.
Proof. exact (MK_COMB (@lem1050015) (@lem1050014)). Qed.
Lemma lem1050017 : term173 = term178.
Proof. exact (TRANS (@lem1050011) (@lem1050016)). Qed.
Lemma lem1050018 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1050019 : term198 = term199.
Proof. exact (MK_COMB (@lem1050018) (@lem1050017)). Qed.
Lemma lem1050020 (y2 : nat) : (term174 y2) = (term174 y2).
Proof. exact (eq_refl (term174 y2)). Qed.
Lemma lem1050021 (y2 : nat) : (term171 y2) = (term200 y2).
Proof. exact (MK_COMB (@lem1050019) (@lem1050020 y2)). Qed.
Lemma lem1050022 (x1 : nat) (y1 : nat) (y2 : nat) : ((term208 x1 y1) = (term171 y2)) = ((term210 x1 y1) = (term200 y2)).
Proof. exact (MK_COMB (@lem1050008 x1 y1) (@lem1050021 y2)). Qed.
Lemma lem1050027 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1050028 (x1 : nat) (y1 : nat) (y2 : nat) : (term220 x1 y1 y2) = (term221 x1 y1 y2).
Proof. exact (MK_COMB (@lem1050027) (@lem1050022 x1 y1 y2)). Qed.
Lemma lem1050030 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1049286 n (@lem1049285 n)). Qed.
Lemma lem1050031 (x1 : nat) : ((S x1) = (NUMERAL 0)) = False.
Proof. exact (@lem1050030 x1). Qed.
Lemma lem1050032 (x1 : nat) (y1 : nat) (y2 : nat) : (term222 y1 y2 x1) = (term223 x1 y1 y2).
Proof. exact (MK_COMB (@lem1050028 x1 y1 y2) (@lem1050031 x1)). Qed.
Lemma lem1050036 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1050037 (x1 : nat) (y1 : nat) (y2 : nat) : (term223 x1 y1 y2) = (term224 x1 y1 y2).
Proof. exact (@lem1050036 ((term210 x1 y1) = (term200 y2))). Qed.
Lemma lem1050042 (x1 : nat) (y1 : nat) (y2 : nat) : (term222 y1 y2 x1) = (term224 x1 y1 y2).
Proof. exact (TRANS (@lem1050032 x1 y1 y2) (@lem1050037 x1 y1 y2)). Qed.
Lemma lem1050043 (y1 : nat) (y2 : nat) (x1 : nat) : (term224 x1 y1 y2) = (term222 y1 y2 x1).
Proof. exact (SYM (@lem1050042 x1 y1 y2)). Qed.
Lemma lem1050044 (m : nat) : term225 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem1050045 (m : nat) : (term225 m) = (term226 m).
Proof. exact (eq_refl (term225 m)). Qed.
Lemma lem1050046 (m : nat) : term226 m.
Proof. exact (EQ_MP (@lem1050045 m) (@lem1050044 m)). Qed.
Lemma lem1050047 (m : nat) (n : nat) : term227 m n.
Proof. exact (@lem1050046 m n). Qed.
Lemma lem1050048 (m : nat) (n : nat) : (term227 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term227 m n)). Qed.
Lemma lem1050082 (m : nat) : term143 m.
Proof. exact (@lem84830 m). Qed.
Lemma lem1050083 (m : nat) : (term143 m) = (term144 m).
Proof. exact (eq_refl (term143 m)). Qed.
Lemma lem1050084 (m : nat) : term144 m.
Proof. exact (EQ_MP (@lem1050083 m) (@lem1050082 m)). Qed.
Lemma lem1050085 (m : nat) (n : nat) : term145 m n.
Proof. exact (@lem1050084 m n). Qed.
Lemma lem1050086 (m : nat) (n : nat) : (term145 m n) = (term146 m n).
Proof. exact (eq_refl (term145 m n)). Qed.
Lemma lem1050087 (m : nat) (n : nat) : term146 m n.
Proof. exact (EQ_MP (@lem1050086 m n) (@lem1050085 m n)). Qed.
Lemma lem1050088 (m : nat) (n : nat) (p : nat) : term147 m n p.
Proof. exact (@lem1050087 m n p). Qed.
Lemma lem1050089 (m : nat) (n : nat) (p : nat) : (term147 m n p) = (((Nat.mul m n) = (Nat.mul m p)) = (term148 m n p)).
Proof. exact (eq_refl (term147 m n p)). Qed.
Lemma lem1050424 : term149.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem1050425 : term150.
Proof. exact (proj2 (@lem1050424)). Qed.
Lemma lem1050426 : term151.
Proof. exact (proj2 (@lem1050425)). Qed.
Lemma lem1050427 : term152.
Proof. exact (proj2 (@lem1050426)). Qed.
Lemma lem1050469 : term153.
Proof. exact (proj1 (@lem1050427)). Qed.
Lemma lem1050470 (n : nat) : term154 n.
Proof. exact (@lem1050469 n). Qed.
Lemma lem1050471 (n : nat) : (term154 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term154 n)). Qed.
Lemma lem1050473 : term228.
Proof. exact (proj1 (@lem1050426)). Qed.
Lemma lem1050474 (n : nat) : term229 n.
Proof. exact (@lem1050473 n). Qed.
Lemma lem1050475 (n : nat) : (term229 n) = (((BIT0 n) = 0) = (n = 0)).
Proof. exact (eq_refl (term229 n)). Qed.
Lemma lem1050478 : term155.
Proof. exact (proj1 (@lem1050424)). Qed.
Lemma lem1050479 (m : nat) : term156 m.
Proof. exact (@lem1050478 m). Qed.
Lemma lem1050480 (m : nat) : (term156 m) = (term157 m).
Proof. exact (eq_refl (term156 m)). Qed.
Lemma lem1050481 (m : nat) : term157 m.
Proof. exact (EQ_MP (@lem1050480 m) (@lem1050479 m)). Qed.
Lemma lem1050482 (m : nat) (n : nat) : term158 m n.
Proof. exact (@lem1050481 m n). Qed.
Lemma lem1050483 (m : nat) (n : nat) : (term158 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term158 m n)). Qed.
Lemma lem1050735 (m : nat) : term189 m.
Proof. exact (@lem1047562 m). Qed.
Lemma lem1050736 (m : nat) : (term189 m) = (term36 m).
Proof. exact (eq_refl (term189 m)). Qed.
Lemma lem1050737 (m : nat) : term36 m.
Proof. exact (EQ_MP (@lem1050736 m) (@lem1050735 m)). Qed.
Lemma lem1050738 (m : nat) (n : nat) : term190 m n.
Proof. exact (@lem1050737 m n). Qed.
Lemma lem1050739 (m : nat) (n : nat) : (term190 m n) = (term32 m n).
Proof. exact (eq_refl (term190 m n)). Qed.
Lemma lem1050740 (m : nat) (n : nat) : term32 m n.
Proof. exact (EQ_MP (@lem1050739 m n) (@lem1050738 m n)). Qed.
Lemma lem1050741 (m : nat) (n : nat) (p : nat) : term191 m n p.
Proof. exact (@lem1050740 m n p). Qed.
Lemma lem1050742 (m : nat) (n : nat) (p : nat) : (term191 m n p) = ((term28 m n p) = (term27 m n p)).
Proof. exact (eq_refl (term191 m n p)). Qed.
Lemma lem1050744 : term192.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem1050745 (m : nat) : term193 m.
Proof. exact (@lem1050744 m). Qed.
Lemma lem1050746 (m : nat) : (term193 m) = (term194 m).
Proof. exact (eq_refl (term193 m)). Qed.
Lemma lem1050747 (m : nat) : term194 m.
Proof. exact (EQ_MP (@lem1050746 m) (@lem1050745 m)). Qed.
Lemma lem1050748 (m : nat) (n : nat) : term195 m n.
Proof. exact (@lem1050747 m n). Qed.
Lemma lem1050749 (m : nat) (n : nat) : (term195 m n) = ((term196 m n) = (term197 m n)).
Proof. exact (eq_refl (term195 m n)). Qed.
Lemma lem1050755 (y1 : nat) (x1 : nat) (h1 : term62 x1) : term230 x1 y1.
Proof. exact (@lem1047664 x1 h1 y1). Qed.
Lemma lem1050756 (y1 : nat) (x1 : nat) : (term230 x1 y1) = (term58 y1 x1).
Proof. exact (eq_refl (term230 x1 y1)). Qed.
Lemma lem1050757 (y1 : nat) (x1 : nat) (h1 : term62 x1) : term58 y1 x1.
Proof. exact (EQ_MP (@lem1050756 y1 x1) (@lem1050755 y1 x1 h1)). Qed.
Lemma lem1050758 (y1 : nat) (x2 : nat) (x1 : nat) (h1 : term62 x1) : term231 y1 x1 x2.
Proof. exact (@lem1050757 y1 x1 h1 x2). Qed.
Lemma lem1050759 (y1 : nat) (x1 : nat) (x2 : nat) : (term231 y1 x1 x2) = (term54 y1 x1 x2).
Proof. exact (eq_refl (term231 y1 x1 x2)). Qed.
Lemma lem1050760 (y1 : nat) (x2 : nat) (x1 : nat) (h1 : term62 x1) : term54 y1 x1 x2.
Proof. exact (EQ_MP (@lem1050759 y1 x1 x2) (@lem1050758 y1 x2 x1 h1)). Qed.
Lemma lem1050761 (y1 : nat) (x2 : nat) (y2 : nat) (x1 : nat) (h1 : term62 x1) : term232 y1 x1 x2 y2.
Proof. exact (@lem1050760 y1 x2 x1 h1 y2). Qed.
Lemma lem1050762 (y1 : nat) (y2 : nat) (x1 : nat) (x2 : nat) : (term232 y1 x1 x2 y2) = (term50 y1 y2 x1 x2).
Proof. exact (eq_refl (term232 y1 x1 x2 y2)). Qed.
Lemma lem1050763 (y1 : nat) (y2 : nat) (x2 : nat) (x1 : nat) (h1 : term62 x1) : term50 y1 y2 x1 x2.
Proof. exact (EQ_MP (@lem1050762 y1 y2 x1 x2) (@lem1050761 y1 x2 y2 x1 h1)). Qed.
Lemma lem1050764 (y1 : nat) (y2 : nat) (x1 : nat) (x2 : nat) : (term50 y1 y2 x1 x2) = ((term50 y1 y2 x1 x2) = True).
Proof. exact (@lem7 (term50 y1 y2 x1 x2)). Qed.
Lemma lem1050780 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (EQ_MP (@lem1050749 m n) (@lem1050748 m n)). Qed.
Lemma lem1050781 (x1 : nat) : (term203 x1) = (term204 x1).
Proof. exact (@lem1050780 term205 x1). Qed.
Lemma lem1050782 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1050783 (x1 : nat) : (term206 x1) = (term207 x1).
Proof. exact (MK_COMB (@lem1050782) (@lem1050781 x1)). Qed.
Lemma lem1050784 (y1 : nat) : (term174 y1) = (term174 y1).
Proof. exact (eq_refl (term174 y1)). Qed.
Lemma lem1050785 (x1 : nat) (y1 : nat) : (term208 x1 y1) = (term209 x1 y1).
Proof. exact (MK_COMB (@lem1050783 x1) (@lem1050784 y1)). Qed.
Lemma lem1050787 (m : nat) (n : nat) (p : nat) : (term28 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1050742 m n p) (@lem1050741 m n p)). Qed.
Lemma lem1050788 (x1 : nat) (y1 : nat) : (term209 x1 y1) = (term210 x1 y1).
Proof. exact (@lem1050787 term205 (term211 x1) (term174 y1)). Qed.
Lemma lem1050789 (x1 : nat) (y1 : nat) : (term208 x1 y1) = (term210 x1 y1).
Proof. exact (TRANS (@lem1050785 x1 y1) (@lem1050788 x1 y1)). Qed.
Lemma lem1050790 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1050791 (x1 : nat) (y1 : nat) : (term218 x1 y1) = (term219 x1 y1).
Proof. exact (MK_COMB (@lem1050790) (@lem1050789 x1 y1)). Qed.
Lemma lem1050793 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (EQ_MP (@lem1050749 m n) (@lem1050748 m n)). Qed.
Lemma lem1050794 (x2 : nat) : (term203 x2) = (term204 x2).
Proof. exact (@lem1050793 term205 x2). Qed.
Lemma lem1050795 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1050796 (x2 : nat) : (term206 x2) = (term207 x2).
Proof. exact (MK_COMB (@lem1050795) (@lem1050794 x2)). Qed.
Lemma lem1050797 (y2 : nat) : (term174 y2) = (term174 y2).
Proof. exact (eq_refl (term174 y2)). Qed.
Lemma lem1050798 (x2 : nat) (y2 : nat) : (term208 x2 y2) = (term209 x2 y2).
Proof. exact (MK_COMB (@lem1050796 x2) (@lem1050797 y2)). Qed.
Lemma lem1050800 (m : nat) (n : nat) (p : nat) : (term28 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1050742 m n p) (@lem1050741 m n p)). Qed.
Lemma lem1050801 (x2 : nat) (y2 : nat) : (term209 x2 y2) = (term210 x2 y2).
Proof. exact (@lem1050800 term205 (term211 x2) (term174 y2)). Qed.
Lemma lem1050802 (x2 : nat) (y2 : nat) : (term208 x2 y2) = (term210 x2 y2).
Proof. exact (TRANS (@lem1050798 x2 y2) (@lem1050801 x2 y2)). Qed.
Lemma lem1050803 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : ((term208 x1 y1) = (term208 x2 y2)) = ((term210 x1 y1) = (term210 x2 y2)).
Proof. exact (MK_COMB (@lem1050791 x1 y1) (@lem1050802 x2 y2)). Qed.
Lemma lem1050805 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term148 m n p).
Proof. exact (EQ_MP (@lem1050089 m n p) (@lem1050088 m n p)). Qed.
Lemma lem1050806 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : ((term210 x1 y1) = (term210 x2 y2)) = (term233 x1 y1 x2 y2).
Proof. exact (@lem1050805 term205 (term44 x1 y1) (term44 x2 y2)). Qed.
Lemma lem1050810 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1050483 m n) (@lem1050482 m n)). Qed.
Lemma lem1050811 : (term205 = (NUMERAL 0)) = (term176 = 0).
Proof. exact (@lem1050810 term176 0). Qed.
Lemma lem1050813 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem1050475 n) (@lem1050474 n)). Qed.
Lemma lem1050814 : (term176 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem1050813 (BIT1 0)). Qed.
Lemma lem1050816 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem1050471 n) (@lem1050470 n)). Qed.
Lemma lem1050817 : ((BIT1 0) = 0) = False.
Proof. exact (@lem1050816 0). Qed.
Lemma lem1050818 : (term176 = 0) = False.
Proof. exact (TRANS (@lem1050814) (@lem1050817)). Qed.
Lemma lem1050819 : (term205 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1050811) (@lem1050818)). Qed.
Lemma lem1050820 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1050821 : term234 = (or False).
Proof. exact (MK_COMB (@lem1050820) (@lem1050819)). Qed.
Lemma lem1050826 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : ((term44 x1 y1) = (term44 x2 y2)) = ((term44 x1 y1) = (term44 x2 y2)).
Proof. exact (eq_refl ((term44 x1 y1) = (term44 x2 y2))). Qed.
Lemma lem1050827 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term233 x1 y1 x2 y2) = (term235 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1050821) (@lem1050826 x1 y1 x2 y2)). Qed.
Lemma lem1050829 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1050830 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term235 x1 y1 x2 y2) = ((term44 x1 y1) = (term44 x2 y2)).
Proof. exact (@lem1050829 ((term44 x1 y1) = (term44 x2 y2))). Qed.
Lemma lem1050835 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term233 x1 y1 x2 y2) = ((term44 x1 y1) = (term44 x2 y2)).
Proof. exact (TRANS (@lem1050827 x1 y1 x2 y2) (@lem1050830 x1 y1 x2 y2)). Qed.
Lemma lem1050836 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : ((term210 x1 y1) = (term210 x2 y2)) = ((term44 x1 y1) = (term44 x2 y2)).
Proof. exact (TRANS (@lem1050806 x1 y1 x2 y2) (@lem1050835 x1 y1 x2 y2)). Qed.
Lemma lem1050837 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : ((term208 x1 y1) = (term208 x2 y2)) = ((term44 x1 y1) = (term44 x2 y2)).
Proof. exact (TRANS (@lem1050803 x1 y1 x2 y2) (@lem1050836 x1 y1 x2 y2)). Qed.
Lemma lem1050838 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1050839 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term236 x1 y1 x2 y2) = (term48 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1050838) (@lem1050837 x1 y1 x2 y2)). Qed.
Lemma lem1050841 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem1050048 m n) (@lem1050047 m n)). Qed.
Lemma lem1050842 (x1 : nat) (x2 : nat) : ((S x1) = (S x2)) = (x1 = x2).
Proof. exact (@lem1050841 x1 x2). Qed.
Lemma lem1050845 (y1 : nat) (y2 : nat) (x1 : nat) (x2 : nat) : (term237 y1 y2 x1 x2) = (term50 y1 y2 x1 x2).
Proof. exact (MK_COMB (@lem1050839 x1 y1 x2 y2) (@lem1050842 x1 x2)). Qed.
Lemma lem1050847 (y1 : nat) (y2 : nat) (x2 : nat) (x1 : nat) (h1 : term62 x1) : (term50 y1 y2 x1 x2) = True.
Proof. exact (EQ_MP (@lem1050764 y1 y2 x1 x2) (@lem1050763 y1 y2 x2 x1 h1)). Qed.
Lemma lem1050848 (y1 : nat) (y2 : nat) (x2 : nat) (x1 : nat) (h1 : term62 x1) : (term237 y1 y2 x1 x2) = True.
Proof. exact (TRANS (@lem1050845 y1 y2 x1 x2) (@lem1050847 y1 y2 x2 x1 h1)). Qed.
Lemma lem1050849 (y1 : nat) (y2 : nat) (x2 : nat) (x1 : nat) (h1 : term62 x1) : True = (term237 y1 y2 x1 x2).
Proof. exact (SYM (@lem1050848 y1 y2 x2 x1 h1)). Qed.
Lemma lem1050850 (y1 : nat) (y2 : nat) (x2 : nat) (x1 : nat) (h1 : term62 x1) : term237 y1 y2 x1 x2.
Proof. exact (EQ_MP (@lem1050849 y1 y2 x2 x1 h1) (@lem0)). Qed.
Lemma lem1050851 (y1 : nat) (x2 : nat) (y2 : nat) (h1 : (term200 y1) = (term210 x2 y2)) : (term200 y1) = (term210 x2 y2).
Proof. exact (h1). Qed.
Lemma lem1050852 (y1 : nat) (x2 : nat) (y2 : nat) (h1 : (term200 y1) = (term210 x2 y2)) : (term238 y1) = (term239 x2 y2).
Proof. exact (MK_COMB (@lem1047531) (@lem1050851 y1 x2 y2 h1)). Qed.
Lemma lem1050853 (x1 : nat) (y1 : nat) (y2 : nat) (h1 : (term210 x1 y1) = (term200 y2)) : (term210 x1 y1) = (term200 y2).
Proof. exact (h1). Qed.
Lemma lem1050854 (x1 : nat) (y1 : nat) (y2 : nat) (h1 : (term210 x1 y1) = (term200 y2)) : (term239 x1 y1) = (term238 y2).
Proof. exact (MK_COMB (@lem1047531) (@lem1050853 x1 y1 y2 h1)). Qed.
Lemma lem1050858 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1050859 (y1 : nat) (x2 : nat) (y2 : nat) : (term240 y1 x2 y2) = (term241 y1 x2 y2).
Proof. exact (@lem1050858 ((term238 y1) = (term239 x2 y2))). Qed.
Lemma lem1050863 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem1047529 m n) (@lem1047528 m n)). Qed.
Lemma lem1050864 (y1 : nat) : (term238 y1) = (term242 y1).
Proof. exact (@lem1050863 term178 (term174 y1)). Qed.
Lemma lem1050868 (n : nat) : (term11 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1047299 n) (@lem1047298 n)). Qed.
Lemma lem1050869 : term243 = term244.
Proof. exact (@lem1050868 (BIT1 0)). Qed.
Lemma lem1050871 (n : nat) : (term5 n) = False.
Proof. exact (EQ_MP (@lem1047290 n) (@lem1047289 n)). Qed.
Lemma lem1050872 : term244 = False.
Proof. exact (@lem1050871 0). Qed.
Lemma lem1050873 : term243 = False.
Proof. exact (TRANS (@lem1050869) (@lem1050872)). Qed.
Lemma lem1050874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1050875 : term245 = (or False).
Proof. exact (MK_COMB (@lem1050874) (@lem1050873)). Qed.
Lemma lem1050877 (m : nat) (n : nat) : (term15 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (EQ_MP (@lem1047523 m n) (@lem1047522 m n)). Qed.
Lemma lem1050878 (y1 : nat) : (term246 y1) = ((term247 y1) = term243).
Proof. exact (@lem1050877 (term248 y1) term178). Qed.
Lemma lem1050882 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem1047529 m n) (@lem1047528 m n)). Qed.
Lemma lem1050883 (y1 : nat) : (term247 y1) = (term249 y1).
Proof. exact (@lem1050882 term205 y1). Qed.
Lemma lem1050887 (n : nat) : (term11 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1047299 n) (@lem1047298 n)). Qed.
Lemma lem1050888 : term250 = term251.
Proof. exact (@lem1050887 term176). Qed.
Lemma lem1050890 (n : nat) : (term8 n) = True.
Proof. exact (EQ_MP (@lem1047294 n) (@lem1047293 n)). Qed.
Lemma lem1050891 : term251 = True.
Proof. exact (@lem1050890 (BIT1 0)). Qed.
Lemma lem1050892 : term250 = True.
Proof. exact (TRANS (@lem1050888) (@lem1050891)). Qed.
Lemma lem1050893 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1050894 : term252 = (or True).
Proof. exact (MK_COMB (@lem1050893) (@lem1050892)). Qed.
Lemma lem1050895 (y1 : nat) : (Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y1).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even y1)). Qed.
Lemma lem1050896 (y1 : nat) : (term249 y1) = (term253 y1).
Proof. exact (MK_COMB (@lem1050894) (@lem1050895 y1)). Qed.
Lemma lem1050898 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1050899 (y1 : nat) : (term253 y1) = True.
Proof. exact (@lem1050898 (Coq.Arith.PeanoNat.Nat.Even y1)). Qed.
Lemma lem1050900 (y1 : nat) : (term249 y1) = True.
Proof. exact (TRANS (@lem1050896 y1) (@lem1050899 y1)). Qed.
Lemma lem1050901 (y1 : nat) : (term247 y1) = True.
Proof. exact (TRANS (@lem1050883 y1) (@lem1050900 y1)). Qed.
Lemma lem1050902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1050903 (y1 : nat) : (term254 y1) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1050902) (@lem1050901 y1)). Qed.
Lemma lem1050905 (n : nat) : (term11 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1047299 n) (@lem1047298 n)). Qed.
Lemma lem1050906 : term243 = term244.
Proof. exact (@lem1050905 (BIT1 0)). Qed.
Lemma lem1050908 (n : nat) : (term5 n) = False.
Proof. exact (EQ_MP (@lem1047290 n) (@lem1047289 n)). Qed.
Lemma lem1050909 : term244 = False.
Proof. exact (@lem1050908 0). Qed.
Lemma lem1050910 : term243 = False.
Proof. exact (TRANS (@lem1050906) (@lem1050909)). Qed.
Lemma lem1050911 (y1 : nat) : ((term247 y1) = term243) = (True = False).
Proof. exact (MK_COMB (@lem1050903 y1) (@lem1050910)). Qed.
Lemma lem1050913 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1050914 : (True = False) = False.
Proof. exact (@lem1050913 False). Qed.
Lemma lem1050915 (y1 : nat) : ((term247 y1) = term243) = False.
Proof. exact (TRANS (@lem1050911 y1) (@lem1050914)). Qed.
Lemma lem1050916 (y1 : nat) : (term246 y1) = False.
Proof. exact (TRANS (@lem1050878 y1) (@lem1050915 y1)). Qed.
Lemma lem1050917 (y1 : nat) : (term242 y1) = (False \/ False).
Proof. exact (MK_COMB (@lem1050875) (@lem1050916 y1)). Qed.
Lemma lem1050919 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1050920 : (False \/ False) = False.
Proof. exact (@lem1050919 False). Qed.
Lemma lem1050921 (y1 : nat) : (term242 y1) = False.
Proof. exact (TRANS (@lem1050917 y1) (@lem1050920)). Qed.
Lemma lem1050922 (y1 : nat) : (term238 y1) = False.
Proof. exact (TRANS (@lem1050864 y1) (@lem1050921 y1)). Qed.
Lemma lem1050923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1050924 (y1 : nat) : (term255 y1) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1050923) (@lem1050922 y1)). Qed.
Lemma lem1050926 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem1047529 m n) (@lem1047528 m n)). Qed.
Lemma lem1050927 (x2 : nat) (y2 : nat) : (term239 x2 y2) = (term256 x2 y2).
Proof. exact (@lem1050926 term205 (term44 x2 y2)). Qed.
Lemma lem1050931 (n : nat) : (term11 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1047299 n) (@lem1047298 n)). Qed.
Lemma lem1050932 : term250 = term251.
Proof. exact (@lem1050931 term176). Qed.
Lemma lem1050934 (n : nat) : (term8 n) = True.
Proof. exact (EQ_MP (@lem1047294 n) (@lem1047293 n)). Qed.
Lemma lem1050935 : term251 = True.
Proof. exact (@lem1050934 (BIT1 0)). Qed.
Lemma lem1050936 : term250 = True.
Proof. exact (TRANS (@lem1050932) (@lem1050935)). Qed.
Lemma lem1050937 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1050938 : term252 = (or True).
Proof. exact (MK_COMB (@lem1050937) (@lem1050936)). Qed.
Lemma lem1050940 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem1047529 m n) (@lem1047528 m n)). Qed.
Lemma lem1050941 (x2 : nat) (y2 : nat) : (term257 x2 y2) = (term258 x2 y2).
Proof. exact (@lem1050940 (term211 x2) (term174 y2)). Qed.
Lemma lem1050945 (m : nat) (n : nat) : (term15 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (EQ_MP (@lem1047523 m n) (@lem1047522 m n)). Qed.
Lemma lem1050946 (y2 : nat) : (term246 y2) = ((term247 y2) = term243).
Proof. exact (@lem1050945 (term248 y2) term178). Qed.
Lemma lem1050950 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem1047529 m n) (@lem1047528 m n)). Qed.
Lemma lem1050951 (y2 : nat) : (term247 y2) = (term249 y2).
Proof. exact (@lem1050950 term205 y2). Qed.
Lemma lem1050955 (n : nat) : (term11 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1047299 n) (@lem1047298 n)). Qed.
Lemma lem1050956 : term250 = term251.
Proof. exact (@lem1050955 term176). Qed.
Lemma lem1050958 (n : nat) : (term8 n) = True.
Proof. exact (EQ_MP (@lem1047294 n) (@lem1047293 n)). Qed.
Lemma lem1050959 : term251 = True.
Proof. exact (@lem1050958 (BIT1 0)). Qed.
Lemma lem1050960 : term250 = True.
Proof. exact (TRANS (@lem1050956) (@lem1050959)). Qed.
Lemma lem1050961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1050962 : term252 = (or True).
Proof. exact (MK_COMB (@lem1050961) (@lem1050960)). Qed.
Lemma lem1050963 (y2 : nat) : (Coq.Arith.PeanoNat.Nat.Even y2) = (Coq.Arith.PeanoNat.Nat.Even y2).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even y2)). Qed.
Lemma lem1050964 (y2 : nat) : (term249 y2) = (term253 y2).
Proof. exact (MK_COMB (@lem1050962) (@lem1050963 y2)). Qed.
Lemma lem1050966 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1050967 (y2 : nat) : (term253 y2) = True.
Proof. exact (@lem1050966 (Coq.Arith.PeanoNat.Nat.Even y2)). Qed.
Lemma lem1050968 (y2 : nat) : (term249 y2) = True.
Proof. exact (TRANS (@lem1050964 y2) (@lem1050967 y2)). Qed.
Lemma lem1050969 (y2 : nat) : (term247 y2) = True.
Proof. exact (TRANS (@lem1050951 y2) (@lem1050968 y2)). Qed.
Lemma lem1050970 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1050971 (y2 : nat) : (term254 y2) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1050970) (@lem1050969 y2)). Qed.
Lemma lem1050973 (n : nat) : (term11 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1047299 n) (@lem1047298 n)). Qed.
Lemma lem1050974 : term243 = term244.
Proof. exact (@lem1050973 (BIT1 0)). Qed.
Lemma lem1050976 (n : nat) : (term5 n) = False.
Proof. exact (EQ_MP (@lem1047290 n) (@lem1047289 n)). Qed.
Lemma lem1050977 : term244 = False.
Proof. exact (@lem1050976 0). Qed.
Lemma lem1050978 : term243 = False.
Proof. exact (TRANS (@lem1050974) (@lem1050977)). Qed.
Lemma lem1050979 (y2 : nat) : ((term247 y2) = term243) = (True = False).
Proof. exact (MK_COMB (@lem1050971 y2) (@lem1050978)). Qed.
Lemma lem1050981 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1050982 : (True = False) = False.
Proof. exact (@lem1050981 False). Qed.
Lemma lem1050983 (y2 : nat) : ((term247 y2) = term243) = False.
Proof. exact (TRANS (@lem1050979 y2) (@lem1050982)). Qed.
Lemma lem1050984 (y2 : nat) : (term246 y2) = False.
Proof. exact (TRANS (@lem1050946 y2) (@lem1050983 y2)). Qed.
Lemma lem1050985 (x2 : nat) : (term259 x2) = (term259 x2).
Proof. exact (eq_refl (term259 x2)). Qed.
Lemma lem1050986 (y2 : nat) (x2 : nat) : (term258 x2 y2) = (term260 x2).
Proof. exact (MK_COMB (@lem1050985 x2) (@lem1050984 y2)). Qed.
Lemma lem1050988 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1050989 (x2 : nat) : (term260 x2) = (term261 x2).
Proof. exact (@lem1050988 (term261 x2)). Qed.
Lemma lem1050990 (y2 : nat) (x2 : nat) : (term258 x2 y2) = (term261 x2).
Proof. exact (TRANS (@lem1050986 y2 x2) (@lem1050989 x2)). Qed.
Lemma lem1050991 (y2 : nat) (x2 : nat) : (term257 x2 y2) = (term261 x2).
Proof. exact (TRANS (@lem1050941 x2 y2) (@lem1050990 y2 x2)). Qed.
Lemma lem1050992 (y2 : nat) (x2 : nat) : (term256 x2 y2) = (term262 x2).
Proof. exact (MK_COMB (@lem1050938) (@lem1050991 y2 x2)). Qed.
Lemma lem1050994 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1050995 (x2 : nat) : (term262 x2) = True.
Proof. exact (@lem1050994 (term261 x2)). Qed.
Lemma lem1050996 (x2 : nat) (y2 : nat) : (term256 x2 y2) = True.
Proof. exact (TRANS (@lem1050992 y2 x2) (@lem1050995 x2)). Qed.
Lemma lem1050997 (x2 : nat) (y2 : nat) : (term239 x2 y2) = True.
Proof. exact (TRANS (@lem1050927 x2 y2) (@lem1050996 x2 y2)). Qed.
Lemma lem1050998 (y1 : nat) (x2 : nat) (y2 : nat) : ((term238 y1) = (term239 x2 y2)) = (False = True).
Proof. exact (MK_COMB (@lem1050924 y1) (@lem1050997 x2 y2)). Qed.
Lemma lem1051000 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1051001 : (False = True) = (~ True).
Proof. exact (@lem1051000 True). Qed.
Lemma lem1051003 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1051004 : (False = True) = False.
Proof. exact (TRANS (@lem1051001) (@lem1051003)). Qed.
Lemma lem1051005 (y1 : nat) (x2 : nat) (y2 : nat) : ((term238 y1) = (term239 x2 y2)) = False.
Proof. exact (TRANS (@lem1050998 y1 x2 y2) (@lem1051004)). Qed.
Lemma lem1051006 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1051007 (y1 : nat) (x2 : nat) (y2 : nat) : (term241 y1 x2 y2) = (~ False).
Proof. exact (MK_COMB (@lem1051006) (@lem1051005 y1 x2 y2)). Qed.
Lemma lem1051009 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1051010 (y1 : nat) (x2 : nat) (y2 : nat) : (term241 y1 x2 y2) = True.
Proof. exact (TRANS (@lem1051007 y1 x2 y2) (@lem1051009)). Qed.
Lemma lem1051011 (y1 : nat) (x2 : nat) (y2 : nat) : (term240 y1 x2 y2) = True.
Proof. exact (TRANS (@lem1050859 y1 x2 y2) (@lem1051010 y1 x2 y2)). Qed.
Lemma lem1051012 (y1 : nat) (x2 : nat) (y2 : nat) : True = (term240 y1 x2 y2).
Proof. exact (SYM (@lem1051011 y1 x2 y2)). Qed.
Lemma lem1051013 (y1 : nat) (x2 : nat) (y2 : nat) : term240 y1 x2 y2.
Proof. exact (EQ_MP (@lem1051012 y1 x2 y2) (@lem0)). Qed.
Lemma lem1051017 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1051018 (x1 : nat) (y1 : nat) (y2 : nat) : (term263 x1 y1 y2) = (term264 x1 y1 y2).
Proof. exact (@lem1051017 ((term239 x1 y1) = (term238 y2))). Qed.
Lemma lem1051022 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem1047529 m n) (@lem1047528 m n)). Qed.
Lemma lem1051023 (x1 : nat) (y1 : nat) : (term239 x1 y1) = (term256 x1 y1).
Proof. exact (@lem1051022 term205 (term44 x1 y1)). Qed.
Lemma lem1051027 (n : nat) : (term11 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1047299 n) (@lem1047298 n)). Qed.
Lemma lem1051028 : term250 = term251.
Proof. exact (@lem1051027 term176). Qed.
Lemma lem1051030 (n : nat) : (term8 n) = True.
Proof. exact (EQ_MP (@lem1047294 n) (@lem1047293 n)). Qed.
Lemma lem1051031 : term251 = True.
Proof. exact (@lem1051030 (BIT1 0)). Qed.
Lemma lem1051032 : term250 = True.
Proof. exact (TRANS (@lem1051028) (@lem1051031)). Qed.
Lemma lem1051033 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1051034 : term252 = (or True).
Proof. exact (MK_COMB (@lem1051033) (@lem1051032)). Qed.
Lemma lem1051036 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem1047529 m n) (@lem1047528 m n)). Qed.
Lemma lem1051037 (x1 : nat) (y1 : nat) : (term257 x1 y1) = (term258 x1 y1).
Proof. exact (@lem1051036 (term211 x1) (term174 y1)). Qed.
Lemma lem1051041 (m : nat) (n : nat) : (term15 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (EQ_MP (@lem1047523 m n) (@lem1047522 m n)). Qed.
Lemma lem1051042 (y1 : nat) : (term246 y1) = ((term247 y1) = term243).
Proof. exact (@lem1051041 (term248 y1) term178). Qed.
Lemma lem1051046 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem1047529 m n) (@lem1047528 m n)). Qed.
Lemma lem1051047 (y1 : nat) : (term247 y1) = (term249 y1).
Proof. exact (@lem1051046 term205 y1). Qed.
Lemma lem1051051 (n : nat) : (term11 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1047299 n) (@lem1047298 n)). Qed.
Lemma lem1051052 : term250 = term251.
Proof. exact (@lem1051051 term176). Qed.
Lemma lem1051054 (n : nat) : (term8 n) = True.
Proof. exact (EQ_MP (@lem1047294 n) (@lem1047293 n)). Qed.
Lemma lem1051055 : term251 = True.
Proof. exact (@lem1051054 (BIT1 0)). Qed.
Lemma lem1051056 : term250 = True.
Proof. exact (TRANS (@lem1051052) (@lem1051055)). Qed.
Lemma lem1051057 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1051058 : term252 = (or True).
Proof. exact (MK_COMB (@lem1051057) (@lem1051056)). Qed.
Lemma lem1051059 (y1 : nat) : (Coq.Arith.PeanoNat.Nat.Even y1) = (Coq.Arith.PeanoNat.Nat.Even y1).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even y1)). Qed.
Lemma lem1051060 (y1 : nat) : (term249 y1) = (term253 y1).
Proof. exact (MK_COMB (@lem1051058) (@lem1051059 y1)). Qed.
Lemma lem1051062 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1051063 (y1 : nat) : (term253 y1) = True.
Proof. exact (@lem1051062 (Coq.Arith.PeanoNat.Nat.Even y1)). Qed.
Lemma lem1051064 (y1 : nat) : (term249 y1) = True.
Proof. exact (TRANS (@lem1051060 y1) (@lem1051063 y1)). Qed.
Lemma lem1051065 (y1 : nat) : (term247 y1) = True.
Proof. exact (TRANS (@lem1051047 y1) (@lem1051064 y1)). Qed.
Lemma lem1051066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1051067 (y1 : nat) : (term254 y1) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1051066) (@lem1051065 y1)). Qed.
Lemma lem1051069 (n : nat) : (term11 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1047299 n) (@lem1047298 n)). Qed.
Lemma lem1051070 : term243 = term244.
Proof. exact (@lem1051069 (BIT1 0)). Qed.
Lemma lem1051072 (n : nat) : (term5 n) = False.
Proof. exact (EQ_MP (@lem1047290 n) (@lem1047289 n)). Qed.
Lemma lem1051073 : term244 = False.
Proof. exact (@lem1051072 0). Qed.
Lemma lem1051074 : term243 = False.
Proof. exact (TRANS (@lem1051070) (@lem1051073)). Qed.
Lemma lem1051075 (y1 : nat) : ((term247 y1) = term243) = (True = False).
Proof. exact (MK_COMB (@lem1051067 y1) (@lem1051074)). Qed.
Lemma lem1051077 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1051078 : (True = False) = False.
Proof. exact (@lem1051077 False). Qed.
Lemma lem1051079 (y1 : nat) : ((term247 y1) = term243) = False.
Proof. exact (TRANS (@lem1051075 y1) (@lem1051078)). Qed.
Lemma lem1051080 (y1 : nat) : (term246 y1) = False.
Proof. exact (TRANS (@lem1051042 y1) (@lem1051079 y1)). Qed.
Lemma lem1051081 (x1 : nat) : (term259 x1) = (term259 x1).
Proof. exact (eq_refl (term259 x1)). Qed.
Lemma lem1051082 (y1 : nat) (x1 : nat) : (term258 x1 y1) = (term260 x1).
Proof. exact (MK_COMB (@lem1051081 x1) (@lem1051080 y1)). Qed.
Lemma lem1051084 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1051085 (x1 : nat) : (term260 x1) = (term261 x1).
Proof. exact (@lem1051084 (term261 x1)). Qed.
Lemma lem1051086 (y1 : nat) (x1 : nat) : (term258 x1 y1) = (term261 x1).
Proof. exact (TRANS (@lem1051082 y1 x1) (@lem1051085 x1)). Qed.
Lemma lem1051087 (y1 : nat) (x1 : nat) : (term257 x1 y1) = (term261 x1).
Proof. exact (TRANS (@lem1051037 x1 y1) (@lem1051086 y1 x1)). Qed.
Lemma lem1051088 (y1 : nat) (x1 : nat) : (term256 x1 y1) = (term262 x1).
Proof. exact (MK_COMB (@lem1051034) (@lem1051087 y1 x1)). Qed.
Lemma lem1051090 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1051091 (x1 : nat) : (term262 x1) = True.
Proof. exact (@lem1051090 (term261 x1)). Qed.
Lemma lem1051092 (x1 : nat) (y1 : nat) : (term256 x1 y1) = True.
Proof. exact (TRANS (@lem1051088 y1 x1) (@lem1051091 x1)). Qed.
Lemma lem1051093 (x1 : nat) (y1 : nat) : (term239 x1 y1) = True.
Proof. exact (TRANS (@lem1051023 x1 y1) (@lem1051092 x1 y1)). Qed.
Lemma lem1051094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1051095 (x1 : nat) (y1 : nat) : (term265 x1 y1) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1051094) (@lem1051093 x1 y1)). Qed.
Lemma lem1051097 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem1047529 m n) (@lem1047528 m n)). Qed.
Lemma lem1051098 (y2 : nat) : (term238 y2) = (term242 y2).
Proof. exact (@lem1051097 term178 (term174 y2)). Qed.
Lemma lem1051102 (n : nat) : (term11 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1047299 n) (@lem1047298 n)). Qed.
Lemma lem1051103 : term243 = term244.
Proof. exact (@lem1051102 (BIT1 0)). Qed.
Lemma lem1051105 (n : nat) : (term5 n) = False.
Proof. exact (EQ_MP (@lem1047290 n) (@lem1047289 n)). Qed.
Lemma lem1051106 : term244 = False.
Proof. exact (@lem1051105 0). Qed.
Lemma lem1051107 : term243 = False.
Proof. exact (TRANS (@lem1051103) (@lem1051106)). Qed.
Lemma lem1051108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1051109 : term245 = (or False).
Proof. exact (MK_COMB (@lem1051108) (@lem1051107)). Qed.
Lemma lem1051111 (m : nat) (n : nat) : (term15 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (EQ_MP (@lem1047523 m n) (@lem1047522 m n)). Qed.
Lemma lem1051112 (y2 : nat) : (term246 y2) = ((term247 y2) = term243).
Proof. exact (@lem1051111 (term248 y2) term178). Qed.
Lemma lem1051116 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem1047529 m n) (@lem1047528 m n)). Qed.
Lemma lem1051117 (y2 : nat) : (term247 y2) = (term249 y2).
Proof. exact (@lem1051116 term205 y2). Qed.
Lemma lem1051121 (n : nat) : (term11 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1047299 n) (@lem1047298 n)). Qed.
Lemma lem1051122 : term250 = term251.
Proof. exact (@lem1051121 term176). Qed.
Lemma lem1051124 (n : nat) : (term8 n) = True.
Proof. exact (EQ_MP (@lem1047294 n) (@lem1047293 n)). Qed.
Lemma lem1051125 : term251 = True.
Proof. exact (@lem1051124 (BIT1 0)). Qed.
Lemma lem1051126 : term250 = True.
Proof. exact (TRANS (@lem1051122) (@lem1051125)). Qed.
Lemma lem1051127 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1051128 : term252 = (or True).
Proof. exact (MK_COMB (@lem1051127) (@lem1051126)). Qed.
Lemma lem1051129 (y2 : nat) : (Coq.Arith.PeanoNat.Nat.Even y2) = (Coq.Arith.PeanoNat.Nat.Even y2).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even y2)). Qed.
Lemma lem1051130 (y2 : nat) : (term249 y2) = (term253 y2).
Proof. exact (MK_COMB (@lem1051128) (@lem1051129 y2)). Qed.
Lemma lem1051132 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1051133 (y2 : nat) : (term253 y2) = True.
Proof. exact (@lem1051132 (Coq.Arith.PeanoNat.Nat.Even y2)). Qed.
Lemma lem1051134 (y2 : nat) : (term249 y2) = True.
Proof. exact (TRANS (@lem1051130 y2) (@lem1051133 y2)). Qed.
Lemma lem1051135 (y2 : nat) : (term247 y2) = True.
Proof. exact (TRANS (@lem1051117 y2) (@lem1051134 y2)). Qed.
Lemma lem1051136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1051137 (y2 : nat) : (term254 y2) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1051136) (@lem1051135 y2)). Qed.
Lemma lem1051139 (n : nat) : (term11 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1047299 n) (@lem1047298 n)). Qed.
Lemma lem1051140 : term243 = term244.
Proof. exact (@lem1051139 (BIT1 0)). Qed.
Lemma lem1051142 (n : nat) : (term5 n) = False.
Proof. exact (EQ_MP (@lem1047290 n) (@lem1047289 n)). Qed.
Lemma lem1051143 : term244 = False.
Proof. exact (@lem1051142 0). Qed.
Lemma lem1051144 : term243 = False.
Proof. exact (TRANS (@lem1051140) (@lem1051143)). Qed.
Lemma lem1051145 (y2 : nat) : ((term247 y2) = term243) = (True = False).
Proof. exact (MK_COMB (@lem1051137 y2) (@lem1051144)). Qed.
Lemma lem1051147 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1051148 : (True = False) = False.
Proof. exact (@lem1051147 False). Qed.
Lemma lem1051149 (y2 : nat) : ((term247 y2) = term243) = False.
Proof. exact (TRANS (@lem1051145 y2) (@lem1051148)). Qed.
Lemma lem1051150 (y2 : nat) : (term246 y2) = False.
Proof. exact (TRANS (@lem1051112 y2) (@lem1051149 y2)). Qed.
Lemma lem1051151 (y2 : nat) : (term242 y2) = (False \/ False).
Proof. exact (MK_COMB (@lem1051109) (@lem1051150 y2)). Qed.
Lemma lem1051153 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1051154 : (False \/ False) = False.
Proof. exact (@lem1051153 False). Qed.
Lemma lem1051155 (y2 : nat) : (term242 y2) = False.
Proof. exact (TRANS (@lem1051151 y2) (@lem1051154)). Qed.
Lemma lem1051156 (y2 : nat) : (term238 y2) = False.
Proof. exact (TRANS (@lem1051098 y2) (@lem1051155 y2)). Qed.
Lemma lem1051157 (x1 : nat) (y1 : nat) (y2 : nat) : ((term239 x1 y1) = (term238 y2)) = (True = False).
Proof. exact (MK_COMB (@lem1051095 x1 y1) (@lem1051156 y2)). Qed.
Lemma lem1051159 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1051160 : (True = False) = False.
Proof. exact (@lem1051159 False). Qed.
Lemma lem1051161 (x1 : nat) (y1 : nat) (y2 : nat) : ((term239 x1 y1) = (term238 y2)) = False.
Proof. exact (TRANS (@lem1051157 x1 y1 y2) (@lem1051160)). Qed.
Lemma lem1051162 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1051163 (x1 : nat) (y1 : nat) (y2 : nat) : (term264 x1 y1 y2) = (~ False).
Proof. exact (MK_COMB (@lem1051162) (@lem1051161 x1 y1 y2)). Qed.
Lemma lem1051165 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1051166 (x1 : nat) (y1 : nat) (y2 : nat) : (term264 x1 y1 y2) = True.
Proof. exact (TRANS (@lem1051163 x1 y1 y2) (@lem1051165)). Qed.
Lemma lem1051167 (x1 : nat) (y1 : nat) (y2 : nat) : (term263 x1 y1 y2) = True.
Proof. exact (TRANS (@lem1051018 x1 y1 y2) (@lem1051166 x1 y1 y2)). Qed.
Lemma lem1051168 (x1 : nat) (y1 : nat) (y2 : nat) : True = (term263 x1 y1 y2).
Proof. exact (SYM (@lem1051167 x1 y1 y2)). Qed.
Lemma lem1051169 (x1 : nat) (y1 : nat) (y2 : nat) : term263 x1 y1 y2.
Proof. exact (EQ_MP (@lem1051168 x1 y1 y2) (@lem0)). Qed.
Lemma lem1051170 (x1 : nat) (y1 : nat) (y2 : nat) (h1 : (term210 x1 y1) = (term200 y2)) : False.
Proof. exact (@lem1051169 x1 y1 y2 (@lem1050854 x1 y1 y2 h1)). Qed.
Lemma lem1051171 (x1 : nat) (y1 : nat) (y2 : nat) : term223 x1 y1 y2.
Proof. exact (fun h0 : (term210 x1 y1) = (term200 y2) => @lem1051170 x1 y1 y2 h0). Qed.
Lemma lem1051172 (x1 : nat) (y1 : nat) (y2 : nat) : (term223 x1 y1 y2) = (term224 x1 y1 y2).
Proof. exact (@lem69 ((term210 x1 y1) = (term200 y2))). Qed.
Lemma lem1051173 (x1 : nat) (y1 : nat) (y2 : nat) : term224 x1 y1 y2.
Proof. exact (EQ_MP (@lem1051172 x1 y1 y2) (@lem1051171 x1 y1 y2)). Qed.
Lemma lem1051174 (y1 : nat) (x2 : nat) (y2 : nat) (h1 : (term200 y1) = (term210 x2 y2)) : False.
Proof. exact (@lem1051013 y1 x2 y2 (@lem1050852 y1 x2 y2 h1)). Qed.
Lemma lem1051175 (y1 : nat) (x2 : nat) (y2 : nat) : term215 y1 x2 y2.
Proof. exact (fun h0 : (term200 y1) = (term210 x2 y2) => @lem1051174 y1 x2 y2 h0). Qed.
Lemma lem1051176 (y1 : nat) (x2 : nat) (y2 : nat) : (term215 y1 x2 y2) = (term216 y1 x2 y2).
Proof. exact (@lem69 ((term200 y1) = (term210 x2 y2))). Qed.
Lemma lem1051177 (y1 : nat) (x2 : nat) (y2 : nat) : term216 y1 x2 y2.
Proof. exact (EQ_MP (@lem1051176 y1 x2 y2) (@lem1051175 y1 x2 y2)). Qed.
Lemma lem1051178 (y1 : nat) (y2 : nat) (x1 : nat) : term222 y1 y2 x1.
Proof. exact (EQ_MP (@lem1050043 y1 y2 x1) (@lem1051173 x1 y1 y2)). Qed.
Lemma lem1051179 (y1 : nat) (y2 : nat) (x2 : nat) : term214 y1 y2 x2.
Proof. exact (EQ_MP (@lem1049265 y1 y2 x2) (@lem1051177 y1 x2 y2)). Qed.
Lemma lem1051184 (y1 : nat) (x2 : nat) (x1 : nat) (h1 : term62 x1) : term128 y1 x1 x2.
Proof. exact (fun y2 : nat => @lem1050850 y1 y2 x2 x1 h1). Qed.
Lemma lem1051189 (y1 : nat) (x1 : nat) : term120 y1 x1.
Proof. exact (fun y2 : nat => @lem1051178 y1 y2 x1). Qed.
Lemma lem1051190 (y1 : nat) (x2 : nat) (x1 : nat) (h1 : term62 x1) : term130 y1 x1 x2.
Proof. exact (fun h0 : term124 y1 x1 x2 => @lem1051184 y1 x2 x1 h1). Qed.
Lemma lem1051195 (y1 : nat) (x1 : nat) (h1 : term62 x1) : term134 y1 x1.
Proof. exact (fun x2 : nat => @lem1051190 y1 x2 x1 h1). Qed.
Lemma lem1051196 (y1 : nat) (x1 : nat) (h1 : term62 x1) : term136 y1 x1.
Proof. exact (conj (@lem1051189 y1 x1) (@lem1051195 y1 x1 h1)). Qed.
Lemma lem1051197 (y1 : nat) (x1 : nat) (h1 : term62 x1) : term141 y1 x1.
Proof. exact (@lem1047715 y1 x1 (@lem1051196 y1 x1 h1)). Qed.
Lemma lem1051202 (y1 : nat) (x2 : nat) : term102 y1 x2.
Proof. exact (fun y2 : nat => @lem1051179 y1 y2 x2). Qed.
Lemma lem1051207 (y1 : nat) : term94 y1.
Proof. exact (fun y2 : nat => @lem1048493 y1 y2). Qed.
Lemma lem1051208 (y1 : nat) (x2 : nat) : term104 y1 x2.
Proof. exact (fun h0 : term98 y1 x2 => @lem1051202 y1 x2). Qed.
Lemma lem1051213 (y1 : nat) : term108 y1.
Proof. exact (fun x2 : nat => @lem1051208 y1 x2). Qed.
Lemma lem1051214 (y1 : nat) : term110 y1.
Proof. exact (conj (@lem1051207 y1) (@lem1051213 y1)). Qed.
Lemma lem1051215 (y1 : nat) : term115 y1.
Proof. exact (@lem1047687 y1 (@lem1051214 y1)). Qed.
Lemma lem1051220 (x1 : nat) (h1 : term62 x1) : term77 x1.
Proof. exact (fun y1 : nat => @lem1051197 y1 x1 h1). Qed.
Lemma lem1051225 : term70.
Proof. exact (fun y1 : nat => @lem1051215 y1). Qed.
Lemma lem1051226 (x1 : nat) : term79 x1.
Proof. exact (fun h0 : term62 x1 => @lem1051220 x1 h0). Qed.
Lemma lem1051231 : term83.
Proof. exact (fun x1 : nat => @lem1051226 x1). Qed.
Lemma lem1051232 : term85.
Proof. exact (conj (@lem1051225) (@lem1051231)). Qed.
Lemma lem1051233 : term66.
Proof. exact (@lem1047663 (@lem1051232)). Qed.
Lemma lem1051234 : term65.
Proof. exact (EQ_MP (@lem1047640) (@lem1051233)). Qed.
