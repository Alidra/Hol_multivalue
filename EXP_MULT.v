Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_MULT_term_abbrevs.
Require Import EXP_ADD_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_EXP_spec.
Require Import MULT_SYM_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm86199_spec.
Lemma lem88510 (p : nat) : term0 p.
Proof. exact (@lem88509 p). Qed.
Lemma lem88511 (p : nat) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem88512 (p : nat) : term1 p.
Proof. exact (EQ_MP (@lem88511 p) (@lem88510 p)). Qed.
Lemma lem88513 (p : nat) (m : nat) : term2 p m.
Proof. exact (@lem88512 p m). Qed.
Lemma lem88514 (m : nat) (p : nat) : (term2 p m) = (term3 m p).
Proof. exact (eq_refl (term2 p m)). Qed.
Lemma lem88515 (m : nat) (p : nat) : term3 m p.
Proof. exact (EQ_MP (@lem88514 m p) (@lem88513 p m)). Qed.
Lemma lem88516 (m : nat) (p : nat) (n : nat) : term4 m p n.
Proof. exact (@lem88515 m p n). Qed.
Lemma lem88517 (m : nat) (n : nat) (p : nat) : (term4 m p n) = ((term5 m n p) = (term6 m n p)).
Proof. exact (eq_refl (term4 m p n)). Qed.
Lemma lem88520 (P : nat -> Prop) : term7 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem88521 (m : nat) : term8 m.
Proof. exact (@lem88520 (term9 m)). Qed.
Lemma lem88522 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem88523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem88524 (m : nat) : (term12 m) = (term13 m).
Proof. exact (MK_COMB (@lem88523) (@lem88522 m)). Qed.
Lemma lem88525 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem88526 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem88527 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (MK_COMB (@lem88526) (@lem88525 m n)). Qed.
Lemma lem88528 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem88529 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem88527 m n) (@lem88528 m n)). Qed.
Lemma lem88530 (m : nat) : (term22 m) = (term23 m).
Proof. exact (fun_ext (fun n : nat => @lem88529 m n)). Qed.
Lemma lem88531 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88532 (m : nat) : (term24 m) = (term25 m).
Proof. exact (MK_COMB (@lem88531) (@lem88530 m)). Qed.
Lemma lem88533 (m : nat) : (term26 m) = (term27 m).
Proof. exact (MK_COMB (@lem88524 m) (@lem88532 m)). Qed.
Lemma lem88534 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem88535 (m : nat) : (term28 m) = (term29 m).
Proof. exact (MK_COMB (@lem88534) (@lem88533 m)). Qed.
Lemma lem88536 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem88537 (m : nat) : (term30 m) = (term9 m).
Proof. exact (fun_ext (fun n : nat => @lem88536 m n)). Qed.
Lemma lem88538 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88539 (m : nat) : (term31 m) = (term32 m).
Proof. exact (MK_COMB (@lem88538) (@lem88537 m)). Qed.
Lemma lem88540 (m : nat) : (term8 m) = (term33 m).
Proof. exact (MK_COMB (@lem88535 m) (@lem88539 m)). Qed.
Lemma lem88541 (m : nat) : term33 m.
Proof. exact (EQ_MP (@lem88540 m) (@lem88521 m)). Qed.
Lemma lem88542 (m : nat) (n : nat) (h1 : term15 m n) : term15 m n.
Proof. exact (h1). Qed.
Lemma lem88573 : term34.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem88574 (n : nat) : term35 n.
Proof. exact (@lem88573 n). Qed.
Lemma lem88575 (n : nat) : (term35 n) = ((term36 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem88584 : term37.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem88585 (m : nat) : term38 m.
Proof. exact (@lem88584 m). Qed.
Lemma lem88586 (m : nat) : (term38 m) = ((term39 m) = term40).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem88604 (n : nat) : (term36 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem88575 n) (@lem88574 n)). Qed.
Lemma lem88605 (p : nat) : (term36 p) = (NUMERAL 0).
Proof. exact (@lem88604 p). Qed.
Lemma lem88606 (m : nat) : (Nat.pow m) = (Nat.pow m).
Proof. exact (eq_refl (Nat.pow m)). Qed.
Lemma lem88607 (p : nat) (m : nat) : (term41 m p) = (term39 m).
Proof. exact (MK_COMB (@lem88606 m) (@lem88605 p)). Qed.
Lemma lem88609 (m : nat) : (term39 m) = term40.
Proof. exact (EQ_MP (@lem88586 m) (@lem88585 m)). Qed.
Lemma lem88610 (m : nat) (p : nat) : (term41 m p) = term40.
Proof. exact (TRANS (@lem88607 p m) (@lem88609 m)). Qed.
Lemma lem88611 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem88612 (m : nat) (p : nat) : (term42 m p) = term43.
Proof. exact (MK_COMB (@lem88611) (@lem88610 m p)). Qed.
Lemma lem88614 (m : nat) : (term39 m) = term40.
Proof. exact (EQ_MP (@lem88586 m) (@lem88585 m)). Qed.
Lemma lem88615 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem88616 (m : nat) : (term44 m) = term45.
Proof. exact (MK_COMB (@lem88615) (@lem88614 m)). Qed.
Lemma lem88617 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem88618 (m : nat) (p : nat) : (term46 m p) = (term47 p).
Proof. exact (MK_COMB (@lem88616 m) (@lem88617 p)). Qed.
Lemma lem88619 (m : nat) (p : nat) : ((term41 m p) = (term46 m p)) = (term40 = (term47 p)).
Proof. exact (MK_COMB (@lem88612 m p) (@lem88618 m p)). Qed.
Lemma lem88622 (m : nat) : (term48 m) = term49.
Proof. exact (fun_ext (fun p : nat => @lem88619 m p)). Qed.
Lemma lem88623 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88624 (m : nat) : (term11 m) = term50.
Proof. exact (MK_COMB (@lem88623) (@lem88622 m)). Qed.
Lemma lem88629 (m : nat) : term50 = (term11 m).
Proof. exact (SYM (@lem88624 m)). Qed.
Lemma lem88630 : term51.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem88631 : term52.
Proof. exact (proj2 (@lem88630)). Qed.
Lemma lem88632 : term53.
Proof. exact (proj2 (@lem88631)). Qed.
Lemma lem88633 : term54.
Proof. exact (proj2 (@lem88632)). Qed.
Lemma lem88641 : term55.
Proof. exact (proj1 (@lem88633)). Qed.
Lemma lem88642 (m : nat) : term56 m.
Proof. exact (@lem88641 m). Qed.
Lemma lem88643 (m : nat) : (term56 m) = (term57 m).
Proof. exact (eq_refl (term56 m)). Qed.
Lemma lem88644 (m : nat) : term57 m.
Proof. exact (EQ_MP (@lem88643 m) (@lem88642 m)). Qed.
Lemma lem88645 (m : nat) (n : nat) : term58 m n.
Proof. exact (@lem88644 m n). Qed.
Lemma lem88646 (m : nat) (n : nat) : (term58 m n) = ((term59 m n) = (term60 m n)).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem88664 : term61.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem88665 (m : nat) : term62 m.
Proof. exact (@lem88664 m). Qed.
Lemma lem88666 (m : nat) : (term62 m) = (term63 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem88667 (m : nat) : term63 m.
Proof. exact (EQ_MP (@lem88666 m) (@lem88665 m)). Qed.
Lemma lem88668 (m : nat) (n : nat) : term64 m n.
Proof. exact (@lem88667 m n). Qed.
Lemma lem88669 (m : nat) (n : nat) : (term64 m n) = ((term65 m n) = (term66 m n)).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem88675 (m : nat) : term67 m.
Proof. exact (@lem87724 m). Qed.
Lemma lem88676 (m : nat) : (term67 m) = (term68 m).
Proof. exact (eq_refl (term67 m)). Qed.
Lemma lem88677 (m : nat) : term68 m.
Proof. exact (EQ_MP (@lem88676 m) (@lem88675 m)). Qed.
Lemma lem88678 (m : nat) (n : nat) : term69 m n.
Proof. exact (@lem88677 m n). Qed.
Lemma lem88679 (n : nat) (m : nat) : (term69 m n) = (term70 n m).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem88680 (n : nat) (m : nat) : term70 n m.
Proof. exact (EQ_MP (@lem88679 n m) (@lem88678 m n)). Qed.
Lemma lem88681 (n : nat) (m : nat) (p : nat) : term71 n m p.
Proof. exact (@lem88680 n m p). Qed.
Lemma lem88682 (n : nat) (m : nat) (p : nat) : (term71 n m p) = ((term72 m n p) = (term73 n m p)).
Proof. exact (eq_refl (term71 n m p)). Qed.
Lemma lem88684 (p : nat) (m : nat) (n : nat) (h1 : term15 m n) : term74 m n p.
Proof. exact (@lem88542 m n h1 p). Qed.
Lemma lem88685 (m : nat) (n : nat) (p : nat) : (term74 m n p) = ((term75 m n p) = (term76 m n p)).
Proof. exact (eq_refl (term74 m n p)). Qed.
Lemma lem88694 (m : nat) (n : nat) : (term59 m n) = (term60 m n).
Proof. exact (EQ_MP (@lem88646 m n) (@lem88645 m n)). Qed.
Lemma lem88695 (n : nat) (p : nat) : (term59 n p) = (term60 n p).
Proof. exact (@lem88694 n p). Qed.
Lemma lem88696 (m : nat) : (Nat.pow m) = (Nat.pow m).
Proof. exact (eq_refl (Nat.pow m)). Qed.
Lemma lem88697 (m : nat) (n : nat) (p : nat) : (term77 m n p) = (term78 m n p).
Proof. exact (MK_COMB (@lem88696 m) (@lem88695 n p)). Qed.
Lemma lem88699 (n : nat) (m : nat) (p : nat) : (term72 m n p) = (term73 n m p).
Proof. exact (EQ_MP (@lem88682 n m p) (@lem88681 n m p)). Qed.
Lemma lem88700 (n : nat) (m : nat) (p : nat) : (term78 m n p) = (term79 n m p).
Proof. exact (@lem88699 (Nat.mul n p) m p). Qed.
Lemma lem88702 (p : nat) (m : nat) (n : nat) (h1 : term15 m n) : (term75 m n p) = (term76 m n p).
Proof. exact (EQ_MP (@lem88685 m n p) (@lem88684 p m n h1)). Qed.
Lemma lem88703 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem88704 (p : nat) (m : nat) (n : nat) (h1 : term15 m n) : (term80 m n p) = (term81 m n p).
Proof. exact (MK_COMB (@lem88703) (@lem88702 p m n h1)). Qed.
Lemma lem88705 (m : nat) (p : nat) : (Nat.pow m p) = (Nat.pow m p).
Proof. exact (eq_refl (Nat.pow m p)). Qed.
Lemma lem88706 (p : nat) (m : nat) (n : nat) (h1 : term15 m n) : (term79 n m p) = (term82 n m p).
Proof. exact (MK_COMB (@lem88704 p m n h1) (@lem88705 m p)). Qed.
Lemma lem88707 (p : nat) (m : nat) (n : nat) (h1 : term15 m n) : (term78 m n p) = (term82 n m p).
Proof. exact (TRANS (@lem88700 n m p) (@lem88706 p m n h1)). Qed.
Lemma lem88708 (p : nat) (m : nat) (n : nat) (h1 : term15 m n) : (term77 m n p) = (term82 n m p).
Proof. exact (TRANS (@lem88697 m n p) (@lem88707 p m n h1)). Qed.
Lemma lem88709 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem88710 (p : nat) (m : nat) (n : nat) (h1 : term15 m n) : (term83 m n p) = (term84 n m p).
Proof. exact (MK_COMB (@lem88709) (@lem88708 p m n h1)). Qed.
Lemma lem88712 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (EQ_MP (@lem88669 m n) (@lem88668 m n)). Qed.
Lemma lem88713 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem88714 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (MK_COMB (@lem88713) (@lem88712 m n)). Qed.
Lemma lem88715 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem88716 (m : nat) (n : nat) (p : nat) : (term87 m n p) = (term88 m n p).
Proof. exact (MK_COMB (@lem88714 m n) (@lem88715 p)). Qed.
Lemma lem88717 (p : nat) (m : nat) (n : nat) (h1 : term15 m n) : ((term77 m n p) = (term87 m n p)) = ((term82 n m p) = (term88 m n p)).
Proof. exact (MK_COMB (@lem88710 p m n h1) (@lem88716 m n p)). Qed.
Lemma lem88720 (m : nat) (n : nat) (h1 : term15 m n) : (term89 m n) = (term90 m n).
Proof. exact (fun_ext (fun p : nat => @lem88717 p m n h1)). Qed.
Lemma lem88721 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88722 (m : nat) (n : nat) (h1 : term15 m n) : (term19 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem88721) (@lem88720 m n h1)). Qed.
Lemma lem88727 (m : nat) (n : nat) (h1 : term15 m n) : (term91 m n) = (term19 m n).
Proof. exact (SYM (@lem88722 m n h1)). Qed.
Lemma lem88729 (p : nat) (h1 : term40 = (term47 p)) : term40 = (term47 p).
Proof. exact (h1). Qed.
Lemma lem88730 (p : nat) (h1 : term40 = (term47 p)) : (term47 p) = term40.
Proof. exact (SYM (@lem88729 p h1)). Qed.
Lemma lem88731 (p : nat) (h1 : (term47 p) = term40) : (term47 p) = term40.
Proof. exact (h1). Qed.
Lemma lem88732 (p : nat) (h1 : (term47 p) = term40) : term40 = (term47 p).
Proof. exact (SYM (@lem88731 p h1)). Qed.
Lemma lem88733 (p : nat) : (term40 = (term47 p)) = ((term47 p) = term40).
Proof. exact (prop_ext (fun h1 : term40 = (term47 p) => @lem88730 p h1) (fun h1 : (term47 p) = term40 => @lem88732 p h1)). Qed.
Lemma lem88734 : term49 = term92.
Proof. exact (fun_ext (fun p : nat => @lem88733 p)). Qed.
Lemma lem88735 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88736 : term50 = term93.
Proof. exact (MK_COMB (@lem88735) (@lem88734)). Qed.
Lemma lem88737 : term93 = term50.
Proof. exact (SYM (@lem88736)). Qed.
Lemma lem88739 (P : nat -> Prop) : term7 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem88740 : term94.
Proof. exact (@lem88739 term92). Qed.
Lemma lem88741 : term95 = (term96 = term40).
Proof. exact (eq_refl term95). Qed.
Lemma lem88742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem88743 : term97 = term98.
Proof. exact (MK_COMB (@lem88742) (@lem88741)). Qed.
Lemma lem88744 (p : nat) : (term99 p) = ((term47 p) = term40).
Proof. exact (eq_refl (term99 p)). Qed.
Lemma lem88745 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem88746 (p : nat) : (term100 p) = (term101 p).
Proof. exact (MK_COMB (@lem88745) (@lem88744 p)). Qed.
Lemma lem88747 (p : nat) : (term102 p) = ((term103 p) = term40).
Proof. exact (eq_refl (term102 p)). Qed.
Lemma lem88748 (p : nat) : (term104 p) = (term105 p).
Proof. exact (MK_COMB (@lem88746 p) (@lem88747 p)). Qed.
Lemma lem88749 : term106 = term107.
Proof. exact (fun_ext (fun p : nat => @lem88748 p)). Qed.
Lemma lem88750 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88751 : term108 = term109.
Proof. exact (MK_COMB (@lem88750) (@lem88749)). Qed.
Lemma lem88752 : term110 = term111.
Proof. exact (MK_COMB (@lem88743) (@lem88751)). Qed.
Lemma lem88753 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem88754 : term112 = term113.
Proof. exact (MK_COMB (@lem88753) (@lem88752)). Qed.
Lemma lem88755 (p : nat) : (term99 p) = ((term47 p) = term40).
Proof. exact (eq_refl (term99 p)). Qed.
Lemma lem88756 : term114 = term92.
Proof. exact (fun_ext (fun p : nat => @lem88755 p)). Qed.
Lemma lem88757 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88758 : term115 = term93.
Proof. exact (MK_COMB (@lem88757) (@lem88756)). Qed.
Lemma lem88759 : term94 = term116.
Proof. exact (MK_COMB (@lem88754) (@lem88758)). Qed.
Lemma lem88760 : term116.
Proof. exact (EQ_MP (@lem88759) (@lem88740)). Qed.
Lemma lem88803 : term37.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem88804 (m : nat) : term38 m.
Proof. exact (@lem88803 m). Qed.
Lemma lem88805 (m : nat) : (term38 m) = ((term39 m) = term40).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem88810 (m : nat) : (term39 m) = term40.
Proof. exact (EQ_MP (@lem88805 m) (@lem88804 m)). Qed.
Lemma lem88811 : term96 = term40.
Proof. exact (@lem88810 term40). Qed.
Lemma lem88812 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem88813 : term117 = term43.
Proof. exact (MK_COMB (@lem88812) (@lem88811)). Qed.
Lemma lem88814 : term40 = term40.
Proof. exact (eq_refl term40). Qed.
Lemma lem88815 : (term96 = term40) = (term40 = term40).
Proof. exact (MK_COMB (@lem88813) (@lem88814)). Qed.
Lemma lem88817 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem88818 (x : nat) : (x = x) = True.
Proof. exact (@lem88817 nat x). Qed.
Lemma lem88819 : (term40 = term40) = True.
Proof. exact (@lem88818 term40). Qed.
Lemma lem88820 : (term96 = term40) = True.
Proof. exact (TRANS (@lem88815) (@lem88819)). Qed.
Lemma lem88821 : True = (term96 = term40).
Proof. exact (SYM (@lem88820)). Qed.
Lemma lem88822 : term96 = term40.
Proof. exact (EQ_MP (@lem88821) (@lem0)). Qed.
Lemma lem88823 : term51.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem88824 : term52.
Proof. exact (proj2 (@lem88823)). Qed.
Lemma lem88845 : term118.
Proof. exact (proj1 (@lem88824)). Qed.
Lemma lem88846 (n : nat) : term119 n.
Proof. exact (@lem88845 n). Qed.
Lemma lem88847 (n : nat) : (term119 n) = ((term120 n) = n).
Proof. exact (eq_refl (term119 n)). Qed.
Lemma lem88857 : term61.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem88858 (m : nat) : term62 m.
Proof. exact (@lem88857 m). Qed.
Lemma lem88859 (m : nat) : (term62 m) = (term63 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem88860 (m : nat) : term63 m.
Proof. exact (EQ_MP (@lem88859 m) (@lem88858 m)). Qed.
Lemma lem88861 (m : nat) (n : nat) : term64 m n.
Proof. exact (@lem88860 m n). Qed.
Lemma lem88862 (m : nat) (n : nat) : (term64 m n) = ((term65 m n) = (term66 m n)).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem88871 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (EQ_MP (@lem88862 m n) (@lem88861 m n)). Qed.
Lemma lem88872 (p : nat) : (term103 p) = (term121 p).
Proof. exact (@lem88871 term40 p). Qed.
Lemma lem88874 (n : nat) : (term120 n) = n.
Proof. exact (EQ_MP (@lem88847 n) (@lem88846 n)). Qed.
Lemma lem88875 (p : nat) : (term121 p) = (term47 p).
Proof. exact (@lem88874 (term47 p)). Qed.
Lemma lem88877 (p : nat) (h1 : (term47 p) = term40) : (term47 p) = term40.
Proof. exact (h1). Qed.
Lemma lem88878 (p : nat) (h1 : (term47 p) = term40) : (term121 p) = term40.
Proof. exact (TRANS (@lem88875 p) (@lem88877 p h1)). Qed.
Lemma lem88879 (p : nat) (h1 : (term47 p) = term40) : (term103 p) = term40.
Proof. exact (TRANS (@lem88872 p) (@lem88878 p h1)). Qed.
Lemma lem88880 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem88881 (p : nat) (h1 : (term47 p) = term40) : (term122 p) = term43.
Proof. exact (MK_COMB (@lem88880) (@lem88879 p h1)). Qed.
Lemma lem88882 : term40 = term40.
Proof. exact (eq_refl term40). Qed.
Lemma lem88883 (p : nat) (h1 : (term47 p) = term40) : ((term103 p) = term40) = (term40 = term40).
Proof. exact (MK_COMB (@lem88881 p h1) (@lem88882)). Qed.
Lemma lem88885 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem88886 (x : nat) : (x = x) = True.
Proof. exact (@lem88885 nat x). Qed.
Lemma lem88887 : (term40 = term40) = True.
Proof. exact (@lem88886 term40). Qed.
Lemma lem88888 (p : nat) (h1 : (term47 p) = term40) : ((term103 p) = term40) = True.
Proof. exact (TRANS (@lem88883 p h1) (@lem88887)). Qed.
Lemma lem88889 (p : nat) (h1 : (term47 p) = term40) : True = ((term103 p) = term40).
Proof. exact (SYM (@lem88888 p h1)). Qed.
Lemma lem88890 (p : nat) (h1 : (term47 p) = term40) : (term103 p) = term40.
Proof. exact (EQ_MP (@lem88889 p h1) (@lem0)). Qed.
Lemma lem88891 (p : nat) : term105 p.
Proof. exact (fun h0 : (term47 p) = term40 => @lem88890 p h0). Qed.
Lemma lem88896 : term109.
Proof. exact (fun p : nat => @lem88891 p). Qed.
Lemma lem88897 : term111.
Proof. exact (conj (@lem88822) (@lem88896)). Qed.
Lemma lem88898 : term93.
Proof. exact (@lem88760 (@lem88897)). Qed.
Lemma lem88899 : term50.
Proof. exact (EQ_MP (@lem88737) (@lem88898)). Qed.
Lemma lem88907 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (EQ_MP (@lem88517 m n p) (@lem88516 m p n)). Qed.
Lemma lem88908 (m : nat) (n : nat) (p : nat) : (term88 m n p) = (term123 m n p).
Proof. exact (@lem88907 m (Nat.pow m n) p). Qed.
Lemma lem88909 (n : nat) (m : nat) (p : nat) : (term84 n m p) = (term84 n m p).
Proof. exact (eq_refl (term84 n m p)). Qed.
Lemma lem88910 (m : nat) (n : nat) (p : nat) : ((term82 n m p) = (term88 m n p)) = ((term82 n m p) = (term123 m n p)).
Proof. exact (MK_COMB (@lem88909 n m p) (@lem88908 m n p)). Qed.
Lemma lem88913 (m : nat) (n : nat) : (term90 m n) = (term124 m n).
Proof. exact (fun_ext (fun p : nat => @lem88910 m n p)). Qed.
Lemma lem88914 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88915 (m : nat) (n : nat) : (term91 m n) = (term125 m n).
Proof. exact (MK_COMB (@lem88914) (@lem88913 m n)). Qed.
Lemma lem88920 (m : nat) (n : nat) : (term125 m n) = (term91 m n).
Proof. exact (SYM (@lem88915 m n)). Qed.
Lemma lem88921 (m : nat) : term126 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem88922 (m : nat) : (term126 m) = (term127 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem88923 (m : nat) : term127 m.
Proof. exact (EQ_MP (@lem88922 m) (@lem88921 m)). Qed.
Lemma lem88924 (m : nat) (n : nat) : term128 m n.
Proof. exact (@lem88923 m n). Qed.
Lemma lem88925 (n : nat) (m : nat) : (term128 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term128 m n)). Qed.
Lemma lem88928 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem88925 n m) (@lem88924 m n)). Qed.
Lemma lem88929 (m : nat) (n : nat) (p : nat) : (term82 n m p) = (term123 m n p).
Proof. exact (@lem88928 (Nat.pow m p) (term76 m n p)). Qed.
Lemma lem88934 (m : nat) (n : nat) : term125 m n.
Proof. exact (fun p : nat => @lem88929 m n p). Qed.
Lemma lem88935 (m : nat) (n : nat) : term91 m n.
Proof. exact (EQ_MP (@lem88920 m n) (@lem88934 m n)). Qed.
Lemma lem88936 (m : nat) (n : nat) (h1 : term15 m n) : term19 m n.
Proof. exact (EQ_MP (@lem88727 m n h1) (@lem88935 m n)). Qed.
Lemma lem88937 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem88629 m) (@lem88899)). Qed.
Lemma lem88938 (m : nat) (n : nat) : term21 m n.
Proof. exact (fun h0 : term15 m n => @lem88936 m n h0). Qed.
Lemma lem88943 (m : nat) : term25 m.
Proof. exact (fun n : nat => @lem88938 m n). Qed.
Lemma lem88944 (m : nat) : term27 m.
Proof. exact (conj (@lem88937 m) (@lem88943 m)). Qed.
Lemma lem88945 (m : nat) : term32 m.
Proof. exact (@lem88541 m (@lem88944 m)). Qed.
Lemma lem88950 : term129.
Proof. exact (fun m : nat => @lem88945 m). Qed.
