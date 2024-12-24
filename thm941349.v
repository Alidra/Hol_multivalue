Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm941349_term_abbrevs.
Require Import ADD_AC_spec.
Require Import ADD_CLAUSES_spec.
Require Import ADD_SYM_spec.
Require Import ARITH_EQ_spec.
Require Import BIT0_spec.
Require Import BIT1_spec.
Require Import EQ_ADD_RCANCEL_spec.
Require Import EQ_MULT_LCANCEL_spec.
Require Import EXP_2_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import MULT_2_spec.
Require Import MULT_AC_spec.
Require Import MULT_ASSOC_spec.
Require Import MULT_CLAUSES_spec.
Require Import REFL_CLAUSE_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem940533 (m : nat) : term0 m.
Proof. exact (@lem79714 m). Qed.
Lemma lem940534 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem940535 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem940534 m) (@lem940533 m)). Qed.
Lemma lem940536 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem940535 m n). Qed.
Lemma lem940537 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem940538 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem940537 m n) (@lem940536 m n)). Qed.
Lemma lem940539 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem940538 m n p). Qed.
Lemma lem940540 (p : nat) (m : nat) (n : nat) : (term4 m n p) = (((Nat.add m p) = (Nat.add n p)) = (m = n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem940542 (m : nat) : term5 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem940543 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem940544 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem940543 m) (@lem940542 m)). Qed.
Lemma lem940545 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem940544 m n). Qed.
Lemma lem940546 (n : nat) (m : nat) : (term7 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem940548 : term8.
Proof. exact (proj2 (@lem522076)). Qed.
Lemma lem940549 : term9.
Proof. exact (proj2 (@lem940548)). Qed.
Lemma lem940550 : term10.
Proof. exact (proj2 (@lem940549)). Qed.
Lemma lem940592 : term11.
Proof. exact (proj1 (@lem940550)). Qed.
Lemma lem940593 (n : nat) : term12 n.
Proof. exact (@lem940592 n). Qed.
Lemma lem940594 (n : nat) : (term12 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem940596 : term13.
Proof. exact (proj1 (@lem940549)). Qed.
Lemma lem940597 (n : nat) : term14 n.
Proof. exact (@lem940596 n). Qed.
Lemma lem940598 (n : nat) : (term14 n) = (((BIT0 n) = 0) = (n = 0)).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem940601 : term15.
Proof. exact (proj1 (@lem522076)). Qed.
Lemma lem940602 (m : nat) : term16 m.
Proof. exact (@lem940601 m). Qed.
Lemma lem940603 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem940604 (m : nat) : term17 m.
Proof. exact (EQ_MP (@lem940603 m) (@lem940602 m)). Qed.
Lemma lem940605 (m : nat) (n : nat) : term18 m n.
Proof. exact (@lem940604 m n). Qed.
Lemma lem940606 (m : nat) (n : nat) : (term18 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem940608 (m : nat) : term19 m.
Proof. exact (@lem84830 m). Qed.
Lemma lem940609 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem940610 (m : nat) : term20 m.
Proof. exact (EQ_MP (@lem940609 m) (@lem940608 m)). Qed.
Lemma lem940611 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem940610 m n). Qed.
Lemma lem940612 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem940613 (m : nat) (n : nat) : term22 m n.
Proof. exact (EQ_MP (@lem940612 m n) (@lem940611 m n)). Qed.
Lemma lem940614 (m : nat) (n : nat) (p : nat) : term23 m n p.
Proof. exact (@lem940613 m n p). Qed.
Lemma lem940615 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (((Nat.mul m n) = (Nat.mul m p)) = (term24 m n p)).
Proof. exact (eq_refl (term23 m n p)). Qed.
Lemma lem940620 (n : nat) (m : nat) (p : nat) (h1 : (term25 m n p) = (term26 n m p)) : (term25 m n p) = (term26 n m p).
Proof. exact (h1). Qed.
Lemma lem940621 (n : nat) (m : nat) (p : nat) (h1 : (term25 m n p) = (term26 n m p)) : (term26 n m p) = (term25 m n p).
Proof. exact (SYM (@lem940620 n m p h1)). Qed.
Lemma lem940622 (m : nat) (n : nat) (p : nat) (h1 : (term26 n m p) = (term25 m n p)) : (term26 n m p) = (term25 m n p).
Proof. exact (h1). Qed.
Lemma lem940623 (m : nat) (n : nat) (p : nat) (h1 : (term26 n m p) = (term25 m n p)) : (term25 m n p) = (term26 n m p).
Proof. exact (SYM (@lem940622 m n p h1)). Qed.
Lemma lem940624 (m : nat) (n : nat) (p : nat) : ((term25 m n p) = (term26 n m p)) = ((term26 n m p) = (term25 m n p)).
Proof. exact (prop_ext (fun h1 : (term25 m n p) = (term26 n m p) => @lem940621 n m p h1) (fun h1 : (term26 n m p) = (term25 m n p) => @lem940623 m n p h1)). Qed.
Lemma lem940625 (m : nat) (n : nat) : (term27 n m) = (term28 m n).
Proof. exact (fun_ext (fun p : nat => @lem940624 m n p)). Qed.
Lemma lem940626 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem940627 (m : nat) (n : nat) : (term29 n m) = (term30 m n).
Proof. exact (MK_COMB (@lem940626) (@lem940625 m n)). Qed.
Lemma lem940628 (m : nat) : (term31 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem940627 m n)). Qed.
Lemma lem940629 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem940630 (m : nat) : (term33 m) = (term34 m).
Proof. exact (MK_COMB (@lem940629) (@lem940628 m)). Qed.
Lemma lem940631 : term35 = term36.
Proof. exact (fun_ext (fun m : nat => @lem940630 m)). Qed.
Lemma lem940632 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem940633 : term37 = term38.
Proof. exact (MK_COMB (@lem940632) (@lem940631)). Qed.
Lemma lem940634 : term38.
Proof. exact (EQ_MP (@lem940633) (@lem82055)). Qed.
Lemma lem940653 (m : nat) : term39 m.
Proof. exact (@lem940634 m). Qed.
Lemma lem940654 (m : nat) : (term39 m) = (term34 m).
Proof. exact (eq_refl (term39 m)). Qed.
Lemma lem940655 (m : nat) : term34 m.
Proof. exact (EQ_MP (@lem940654 m) (@lem940653 m)). Qed.
Lemma lem940656 (m : nat) (n : nat) : term40 m n.
Proof. exact (@lem940655 m n). Qed.
Lemma lem940657 (m : nat) (n : nat) : (term40 m n) = (term30 m n).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem940658 (m : nat) (n : nat) : term30 m n.
Proof. exact (EQ_MP (@lem940657 m n) (@lem940656 m n)). Qed.
Lemma lem940659 (m : nat) (n : nat) (p : nat) : term41 m n p.
Proof. exact (@lem940658 m n p). Qed.
Lemma lem940660 (m : nat) (n : nat) (p : nat) : (term41 m n p) = ((term26 n m p) = (term25 m n p)).
Proof. exact (eq_refl (term41 m n p)). Qed.
Lemma lem940671 {A : Type'} (x : A) : term42 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem940672 {A : Type'} (x : A) : (term42 A x) = ((x = x) = True).
Proof. exact (eq_refl (term42 A x)). Qed.
Lemma lem940674 (n : nat) (m : nat) (p : nat) : term43 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem940687 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem940688 (m : nat) : (term44 m) = (term45 m).
Proof. exact (@lem940687 m term46). Qed.
Lemma lem940692 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem940693 (m : nat) : (term47 m) = (term48 m).
Proof. exact (MK_COMB (@lem940692 m) (@lem940688 m)). Qed.
Lemma lem940700 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem940701 (m : nat) : (term49 m) = (term50 m).
Proof. exact (MK_COMB (@lem940700) (@lem940693 m)). Qed.
Lemma lem940703 (n : nat) (m : nat) (p : nat) : (term51 m n p) = (term51 n m p).
Proof. exact (proj2 (@lem940674 n m p)). Qed.
Lemma lem940704 (m : nat) : (term52 m) = (term47 m).
Proof. exact (@lem940703 m term46 m). Qed.
Lemma lem940712 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem940713 (m : nat) : (term44 m) = (term45 m).
Proof. exact (@lem940712 m term46). Qed.
Lemma lem940717 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem940718 (m : nat) : (term47 m) = (term48 m).
Proof. exact (MK_COMB (@lem940717 m) (@lem940713 m)). Qed.
Lemma lem940725 (m : nat) : (term52 m) = (term48 m).
Proof. exact (TRANS (@lem940704 m) (@lem940718 m)). Qed.
Lemma lem940726 (m : nat) : ((term47 m) = (term52 m)) = ((term48 m) = (term48 m)).
Proof. exact (MK_COMB (@lem940701 m) (@lem940725 m)). Qed.
Lemma lem940728 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem940672 A x) (@lem940671 A x)). Qed.
Lemma lem940729 (x : nat) : (x = x) = True.
Proof. exact (@lem940728 nat x). Qed.
Lemma lem940730 (m : nat) : ((term48 m) = (term48 m)) = True.
Proof. exact (@lem940729 (term48 m)). Qed.
Lemma lem940731 (m : nat) : ((term47 m) = (term52 m)) = True.
Proof. exact (TRANS (@lem940726 m) (@lem940730 m)). Qed.
Lemma lem940732 (m : nat) : True = ((term47 m) = (term52 m)).
Proof. exact (SYM (@lem940731 m)). Qed.
Lemma lem940735 (n : nat) (h1 : (term44 n) = (Nat.add n n)) : (term44 n) = (Nat.add n n).
Proof. exact (h1). Qed.
Lemma lem940736 (n : nat) (h1 : (term44 n) = (Nat.add n n)) : (Nat.add n n) = (term44 n).
Proof. exact (SYM (@lem940735 n h1)). Qed.
Lemma lem940737 (n : nat) (h1 : (Nat.add n n) = (term44 n)) : (Nat.add n n) = (term44 n).
Proof. exact (h1). Qed.
Lemma lem940738 (n : nat) (h1 : (Nat.add n n) = (term44 n)) : (term44 n) = (Nat.add n n).
Proof. exact (SYM (@lem940737 n h1)). Qed.
Lemma lem940739 (n : nat) : ((term44 n) = (Nat.add n n)) = ((Nat.add n n) = (term44 n)).
Proof. exact (prop_ext (fun h1 : (term44 n) = (Nat.add n n) => @lem940736 n h1) (fun h1 : (Nat.add n n) = (term44 n) => @lem940738 n h1)). Qed.
Lemma lem940740 : term53 = term54.
Proof. exact (fun_ext (fun n : nat => @lem940739 n)). Qed.
Lemma lem940741 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem940742 : term55 = term56.
Proof. exact (MK_COMB (@lem940741) (@lem940740)). Qed.
Lemma lem940743 : term56.
Proof. exact (EQ_MP (@lem940742) (@lem84996)). Qed.
Lemma lem940744 (n : nat) : term57 n.
Proof. exact (@lem940743 n). Qed.
Lemma lem940745 (n : nat) : (term57 n) = ((Nat.add n n) = (term44 n)).
Proof. exact (eq_refl (term57 n)). Qed.
Lemma lem940747 {A : Type'} (x : A) : term42 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem940748 {A : Type'} (x : A) : (term42 A x) = ((x = x) = True).
Proof. exact (eq_refl (term42 A x)). Qed.
Lemma lem940750 (n : nat) (m : nat) (p : nat) : term58 n m p.
Proof. exact (proj2 (@lem79120 n m p)). Qed.
Lemma lem940757 (m : nat) (n : nat) (p : nat) : (term59 m n p) = (term60 m n p).
Proof. exact (proj1 (@lem940750 n m p)). Qed.
Lemma lem940758 (m : nat) : (term61 m) = (term62 m).
Proof. exact (@lem940757 m (term47 m) m). Qed.
Lemma lem940766 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem940767 (m : nat) : (term63 m) = (term64 m).
Proof. exact (@lem940766 m (term47 m)). Qed.
Lemma lem940771 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem940772 (m : nat) : (term62 m) = (term65 m).
Proof. exact (MK_COMB (@lem940771 m) (@lem940767 m)). Qed.
Lemma lem940779 (m : nat) : (term61 m) = (term65 m).
Proof. exact (TRANS (@lem940758 m) (@lem940772 m)). Qed.
Lemma lem940780 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem940781 (m : nat) : (term66 m) = (term67 m).
Proof. exact (MK_COMB (@lem940780) (@lem940779 m)). Qed.
Lemma lem940783 (n : nat) (m : nat) (p : nat) : (term60 m n p) = (term60 n m p).
Proof. exact (proj2 (@lem940750 n m p)). Qed.
Lemma lem940784 (m : nat) : (term68 m) = (term62 m).
Proof. exact (@lem940783 m (term47 m) m). Qed.
Lemma lem940792 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem940793 (m : nat) : (term63 m) = (term64 m).
Proof. exact (@lem940792 m (term47 m)). Qed.
Lemma lem940797 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem940798 (m : nat) : (term62 m) = (term65 m).
Proof. exact (MK_COMB (@lem940797 m) (@lem940793 m)). Qed.
Lemma lem940805 (m : nat) : (term68 m) = (term65 m).
Proof. exact (TRANS (@lem940784 m) (@lem940798 m)). Qed.
Lemma lem940806 (m : nat) : ((term61 m) = (term68 m)) = ((term65 m) = (term65 m)).
Proof. exact (MK_COMB (@lem940781 m) (@lem940805 m)). Qed.
Lemma lem940808 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem940748 A x) (@lem940747 A x)). Qed.
Lemma lem940809 (x : nat) : (x = x) = True.
Proof. exact (@lem940808 nat x). Qed.
Lemma lem940810 (m : nat) : ((term65 m) = (term65 m)) = True.
Proof. exact (@lem940809 (term65 m)). Qed.
Lemma lem940811 (m : nat) : ((term61 m) = (term68 m)) = True.
Proof. exact (TRANS (@lem940806 m) (@lem940810 m)). Qed.
Lemma lem940812 (m : nat) : True = ((term61 m) = (term68 m)).
Proof. exact (SYM (@lem940811 m)). Qed.
Lemma lem940817 (n : nat) (m : nat) (p : nat) (h1 : (term25 m n p) = (term26 n m p)) : (term25 m n p) = (term26 n m p).
Proof. exact (h1). Qed.
Lemma lem940818 (n : nat) (m : nat) (p : nat) (h1 : (term25 m n p) = (term26 n m p)) : (term26 n m p) = (term25 m n p).
Proof. exact (SYM (@lem940817 n m p h1)). Qed.
Lemma lem940819 (m : nat) (n : nat) (p : nat) (h1 : (term26 n m p) = (term25 m n p)) : (term26 n m p) = (term25 m n p).
Proof. exact (h1). Qed.
Lemma lem940820 (m : nat) (n : nat) (p : nat) (h1 : (term26 n m p) = (term25 m n p)) : (term25 m n p) = (term26 n m p).
Proof. exact (SYM (@lem940819 m n p h1)). Qed.
Lemma lem940821 (m : nat) (n : nat) (p : nat) : ((term25 m n p) = (term26 n m p)) = ((term26 n m p) = (term25 m n p)).
Proof. exact (prop_ext (fun h1 : (term25 m n p) = (term26 n m p) => @lem940818 n m p h1) (fun h1 : (term26 n m p) = (term25 m n p) => @lem940820 m n p h1)). Qed.
Lemma lem940822 (m : nat) (n : nat) : (term27 n m) = (term28 m n).
Proof. exact (fun_ext (fun p : nat => @lem940821 m n p)). Qed.
Lemma lem940823 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem940824 (m : nat) (n : nat) : (term29 n m) = (term30 m n).
Proof. exact (MK_COMB (@lem940823) (@lem940822 m n)). Qed.
Lemma lem940825 (m : nat) : (term31 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem940824 m n)). Qed.
Lemma lem940826 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem940827 (m : nat) : (term33 m) = (term34 m).
Proof. exact (MK_COMB (@lem940826) (@lem940825 m)). Qed.
Lemma lem940828 : term35 = term36.
Proof. exact (fun_ext (fun m : nat => @lem940827 m)). Qed.
Lemma lem940829 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem940830 : term37 = term38.
Proof. exact (MK_COMB (@lem940829) (@lem940828)). Qed.
Lemma lem940831 : term38.
Proof. exact (EQ_MP (@lem940830) (@lem82055)). Qed.
Lemma lem940835 (m : nat) (n : nat) (p : nat) (h1 : (term51 m n p) = (term69 m n p)) : (term51 m n p) = (term69 m n p).
Proof. exact (h1). Qed.
Lemma lem940836 (m : nat) (n : nat) (p : nat) (h1 : (term51 m n p) = (term69 m n p)) : (term69 m n p) = (term51 m n p).
Proof. exact (SYM (@lem940835 m n p h1)). Qed.
Lemma lem940837 (m : nat) (n : nat) (p : nat) (h1 : (term69 m n p) = (term51 m n p)) : (term69 m n p) = (term51 m n p).
Proof. exact (h1). Qed.
Lemma lem940838 (m : nat) (n : nat) (p : nat) (h1 : (term69 m n p) = (term51 m n p)) : (term51 m n p) = (term69 m n p).
Proof. exact (SYM (@lem940837 m n p h1)). Qed.
Lemma lem940839 (m : nat) (n : nat) (p : nat) : ((term51 m n p) = (term69 m n p)) = ((term69 m n p) = (term51 m n p)).
Proof. exact (prop_ext (fun h1 : (term51 m n p) = (term69 m n p) => @lem940836 m n p h1) (fun h1 : (term69 m n p) = (term51 m n p) => @lem940838 m n p h1)). Qed.
Lemma lem940840 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (fun_ext (fun p : nat => @lem940839 m n p)). Qed.
Lemma lem940841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem940842 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (MK_COMB (@lem940841) (@lem940840 m n)). Qed.
Lemma lem940843 (m : nat) : (term74 m) = (term75 m).
Proof. exact (fun_ext (fun n : nat => @lem940842 m n)). Qed.
Lemma lem940844 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem940845 (m : nat) : (term76 m) = (term77 m).
Proof. exact (MK_COMB (@lem940844) (@lem940843 m)). Qed.
Lemma lem940846 : term78 = term79.
Proof. exact (fun_ext (fun m : nat => @lem940845 m)). Qed.
Lemma lem940847 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem940848 : term80 = term81.
Proof. exact (MK_COMB (@lem940847) (@lem940846)). Qed.
Lemma lem940849 : term81.
Proof. exact (EQ_MP (@lem940848) (@lem82357)). Qed.
Lemma lem940850 (m : nat) : term39 m.
Proof. exact (@lem940831 m). Qed.
Lemma lem940851 (m : nat) : (term39 m) = (term34 m).
Proof. exact (eq_refl (term39 m)). Qed.
Lemma lem940852 (m : nat) : term34 m.
Proof. exact (EQ_MP (@lem940851 m) (@lem940850 m)). Qed.
Lemma lem940853 (m : nat) (n : nat) : term40 m n.
Proof. exact (@lem940852 m n). Qed.
Lemma lem940854 (m : nat) (n : nat) : (term40 m n) = (term30 m n).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem940855 (m : nat) (n : nat) : term30 m n.
Proof. exact (EQ_MP (@lem940854 m n) (@lem940853 m n)). Qed.
Lemma lem940856 (m : nat) (n : nat) (p : nat) : term41 m n p.
Proof. exact (@lem940855 m n p). Qed.
Lemma lem940857 (m : nat) (n : nat) (p : nat) : (term41 m n p) = ((term26 n m p) = (term25 m n p)).
Proof. exact (eq_refl (term41 m n p)). Qed.
Lemma lem940859 (m : nat) : term82 m.
Proof. exact (@lem940849 m). Qed.
Lemma lem940860 (m : nat) : (term82 m) = (term77 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem940861 (m : nat) : term77 m.
Proof. exact (EQ_MP (@lem940860 m) (@lem940859 m)). Qed.
Lemma lem940862 (m : nat) (n : nat) : term83 m n.
Proof. exact (@lem940861 m n). Qed.
Lemma lem940863 (m : nat) (n : nat) : (term83 m n) = (term73 m n).
Proof. exact (eq_refl (term83 m n)). Qed.
Lemma lem940864 (m : nat) (n : nat) : term73 m n.
Proof. exact (EQ_MP (@lem940863 m n) (@lem940862 m n)). Qed.
Lemma lem940865 (m : nat) (n : nat) (p : nat) : term84 m n p.
Proof. exact (@lem940864 m n p). Qed.
Lemma lem940866 (m : nat) (n : nat) (p : nat) : (term84 m n p) = ((term69 m n p) = (term51 m n p)).
Proof. exact (eq_refl (term84 m n p)). Qed.
Lemma lem940868 (m : nat) : term85 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem940869 (m : nat) : (term85 m) = (term86 m).
Proof. exact (eq_refl (term85 m)). Qed.
Lemma lem940870 (m : nat) : term86 m.
Proof. exact (EQ_MP (@lem940869 m) (@lem940868 m)). Qed.
Lemma lem940871 (m : nat) (n : nat) : term87 m n.
Proof. exact (@lem940870 m n). Qed.
Lemma lem940872 (m : nat) (n : nat) : (term87 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term87 m n)). Qed.
Lemma lem940874 : term88.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem940875 : term89.
Proof. exact (proj2 (@lem940874)). Qed.
Lemma lem940876 : term90.
Proof. exact (proj2 (@lem940875)). Qed.
Lemma lem940877 (m : nat) : term91 m.
Proof. exact (@lem940876 m). Qed.
Lemma lem940878 (m : nat) : (term91 m) = (term92 m).
Proof. exact (eq_refl (term91 m)). Qed.
Lemma lem940879 (m : nat) : term92 m.
Proof. exact (EQ_MP (@lem940878 m) (@lem940877 m)). Qed.
Lemma lem940880 (m : nat) (n : nat) : term93 m n.
Proof. exact (@lem940879 m n). Qed.
Lemma lem940881 (m : nat) (n : nat) : (term93 m n) = ((term94 m n) = (term95 m n)).
Proof. exact (eq_refl (term93 m n)). Qed.
Lemma lem940898 : term96.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem940899 : term97.
Proof. exact (proj2 (@lem940898)). Qed.
Lemma lem940900 : term98.
Proof. exact (proj2 (@lem940899)). Qed.
Lemma lem940901 : term99.
Proof. exact (proj2 (@lem940900)). Qed.
Lemma lem940902 : term100.
Proof. exact (proj2 (@lem940901)). Qed.
Lemma lem940903 (m : nat) : term101 m.
Proof. exact (@lem940902 m). Qed.
Lemma lem940904 (m : nat) : (term101 m) = (term102 m).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem940905 (m : nat) : term102 m.
Proof. exact (EQ_MP (@lem940904 m) (@lem940903 m)). Qed.
Lemma lem940906 (m : nat) (n : nat) : term103 m n.
Proof. exact (@lem940905 m n). Qed.
Lemma lem940907 (m : nat) (n : nat) : (term103 m n) = ((term104 m n) = (term105 m n)).
Proof. exact (eq_refl (term103 m n)). Qed.
Lemma lem940909 : term106.
Proof. exact (proj1 (@lem940901)). Qed.
Lemma lem940910 (m : nat) : term107 m.
Proof. exact (@lem940909 m). Qed.
Lemma lem940911 (m : nat) : (term107 m) = (term108 m).
Proof. exact (eq_refl (term107 m)). Qed.
Lemma lem940912 (m : nat) : term108 m.
Proof. exact (EQ_MP (@lem940911 m) (@lem940910 m)). Qed.
Lemma lem940913 (m : nat) (n : nat) : term109 m n.
Proof. exact (@lem940912 m n). Qed.
Lemma lem940914 (m : nat) (n : nat) : (term109 m n) = ((term110 m n) = (term111 m n)).
Proof. exact (eq_refl (term109 m n)). Qed.
Lemma lem940932 (n : nat) : term112 n.
Proof. exact (@lem88196 n). Qed.
Lemma lem940933 (n : nat) : (term112 n) = ((term113 n) = (Nat.mul n n)).
Proof. exact (eq_refl (term112 n)). Qed.
Lemma lem940936 (n : nat) (h1 : (term44 n) = (Nat.add n n)) : (term44 n) = (Nat.add n n).
Proof. exact (h1). Qed.
Lemma lem940937 (n : nat) (h1 : (term44 n) = (Nat.add n n)) : (Nat.add n n) = (term44 n).
Proof. exact (SYM (@lem940936 n h1)). Qed.
Lemma lem940938 (n : nat) (h1 : (Nat.add n n) = (term44 n)) : (Nat.add n n) = (term44 n).
Proof. exact (h1). Qed.
Lemma lem940939 (n : nat) (h1 : (Nat.add n n) = (term44 n)) : (term44 n) = (Nat.add n n).
Proof. exact (SYM (@lem940938 n h1)). Qed.
Lemma lem940940 (n : nat) : ((term44 n) = (Nat.add n n)) = ((Nat.add n n) = (term44 n)).
Proof. exact (prop_ext (fun h1 : (term44 n) = (Nat.add n n) => @lem940937 n h1) (fun h1 : (Nat.add n n) = (term44 n) => @lem940939 n h1)). Qed.
Lemma lem940941 : term53 = term54.
Proof. exact (fun_ext (fun n : nat => @lem940940 n)). Qed.
Lemma lem940942 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem940943 : term55 = term56.
Proof. exact (MK_COMB (@lem940942) (@lem940941)). Qed.
Lemma lem940944 : term56.
Proof. exact (EQ_MP (@lem940943) (@lem84996)). Qed.
Lemma lem940945 (n : nat) : term57 n.
Proof. exact (@lem940944 n). Qed.
Lemma lem940946 (n : nat) : (term57 n) = ((Nat.add n n) = (term44 n)).
Proof. exact (eq_refl (term57 n)). Qed.
Lemma lem940948 (n : nat) : term114 n.
Proof. exact (@lem80122 n). Qed.
Lemma lem940949 (n : nat) : (term114 n) = ((BIT1 n) = (term115 n)).
Proof. exact (eq_refl (term114 n)). Qed.
Lemma lem940951 (n : nat) : term116 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem940952 (n : nat) : (term116 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term116 n)). Qed.
Lemma lem940957 (two : nat) (h1 : term46 = two) : term46 = two.
Proof. exact (h1). Qed.
Lemma lem940958 (two : nat) (h1 : term46 = two) : term117.
Proof. exact (ex_intro term118 two (@lem940957 two h1)). Qed.
Lemma lem940959 (h1 : term117) : term117.
Proof. exact (h1). Qed.
Lemma lem940960 (h1 : term117) : term117.
Proof. exact (ex_elim (@lem940959 h1) (fun two : nat => fun h0 : term118 two => @lem940958 two h0)). Qed.
Lemma lem940961 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem940962 : term117.
Proof. exact (ex_intro term118 term46 (@lem940961)). Qed.
Lemma lem940963 : term117 = term117.
Proof. exact (prop_ext (fun h1 : term117 => @lem940960 h1) (fun h1 : term117 => @lem940962)). Qed.
Lemma lem940964 : term117.
Proof. exact (EQ_MP (@lem940963) (@lem940962)). Qed.
Lemma lem940965 (two : nat) (h1 : term46 = two) : term46 = two.
Proof. exact (h1). Qed.
Lemma lem940967 (two : nat) (h1 : term46 = two) : term46 = two.
Proof. exact (h1). Qed.
Lemma lem940968 (m : nat) : (Nat.pow m) = (Nat.pow m).
Proof. exact (eq_refl (Nat.pow m)). Qed.
Lemma lem940969 (m : nat) (two : nat) (h1 : term46 = two) : (term113 m) = (Nat.pow m two).
Proof. exact (MK_COMB (@lem940968 m) (@lem940967 two h1)). Qed.
Lemma lem940970 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem940971 (m : nat) (two : nat) (h1 : term46 = two) : (term119 m) = (term120 m two).
Proof. exact (MK_COMB (@lem940970) (@lem940969 m two h1)). Qed.
Lemma lem940972 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem940973 (m : nat) (n : nat) (two : nat) (h1 : term46 = two) : ((term113 m) = n) = ((Nat.pow m two) = n).
Proof. exact (MK_COMB (@lem940971 m two h1) (@lem940972 n)). Qed.
Lemma lem940974 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem940975 (m : nat) (n : nat) (two : nat) (h1 : term46 = two) : (term121 m n) = (term122 m two n).
Proof. exact (MK_COMB (@lem940974) (@lem940973 m n two h1)). Qed.
Lemma lem940977 (two : nat) (h1 : term46 = two) : term46 = two.
Proof. exact (h1). Qed.
Lemma lem940978 (m : nat) : (term123 m) = (term123 m).
Proof. exact (eq_refl (term123 m)). Qed.
Lemma lem940979 (m : nat) (two : nat) (h1 : term46 = two) : (term124 m) = (term125 m two).
Proof. exact (MK_COMB (@lem940978 m) (@lem940977 two h1)). Qed.
Lemma lem940980 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem940981 (m : nat) (two : nat) (h1 : term46 = two) : (term126 m) = (term127 m two).
Proof. exact (MK_COMB (@lem940980) (@lem940979 m two h1)). Qed.
Lemma lem940982 (m : nat) (n : nat) : (term128 m n) = (term128 m n).
Proof. exact (eq_refl (term128 m n)). Qed.
Lemma lem940983 (m : nat) (n : nat) (two : nat) (h1 : term46 = two) : ((term124 m) = (term128 m n)) = ((term125 m two) = (term128 m n)).
Proof. exact (MK_COMB (@lem940981 m two h1) (@lem940982 m n)). Qed.
Lemma lem940984 (m : nat) (n : nat) (two : nat) (h1 : term46 = two) : (((term113 m) = n) = ((term124 m) = (term128 m n))) = (((Nat.pow m two) = n) = ((term125 m two) = (term128 m n))).
Proof. exact (MK_COMB (@lem940975 m n two h1) (@lem940983 m n two h1)). Qed.
Lemma lem940985 (m : nat) (n : nat) (two : nat) (h1 : term46 = two) : (((Nat.pow m two) = n) = ((term125 m two) = (term128 m n))) = (((term113 m) = n) = ((term124 m) = (term128 m n))).
Proof. exact (SYM (@lem940984 m n two h1)). Qed.
Lemma lem940993 (n : nat) : (BIT1 n) = (term115 n).
Proof. exact (EQ_MP (@lem940949 n) (@lem940948 n)). Qed.
Lemma lem940994 (m : nat) : (BIT1 m) = (term115 m).
Proof. exact (@lem940993 m). Qed.
Lemma lem940995 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem940996 (m : nat) : (term123 m) = (term129 m).
Proof. exact (MK_COMB (@lem940995) (@lem940994 m)). Qed.
Lemma lem940997 (two : nat) : two = two.
Proof. exact (eq_refl two). Qed.
Lemma lem940998 (m : nat) (two : nat) : (term125 m two) = (term130 m two).
Proof. exact (MK_COMB (@lem940996 m) (@lem940997 two)). Qed.
Lemma lem940999 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem941000 (m : nat) (two : nat) : (term127 m two) = (term131 m two).
Proof. exact (MK_COMB (@lem940999) (@lem940998 m two)). Qed.
Lemma lem941002 (n : nat) : (BIT1 n) = (term115 n).
Proof. exact (EQ_MP (@lem940949 n) (@lem940948 n)). Qed.
Lemma lem941003 (m : nat) (n : nat) : (term128 m n) = (term132 m n).
Proof. exact (@lem941002 (term133 m n)). Qed.
Lemma lem941005 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem940952 n) (@lem940951 n)). Qed.
Lemma lem941006 (m : nat) (n : nat) : (term133 m n) = (term134 m n).
Proof. exact (@lem941005 (Nat.add m n)). Qed.
Lemma lem941007 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem941008 (m : nat) (n : nat) : (term135 m n) = (term136 m n).
Proof. exact (MK_COMB (@lem941007) (@lem941006 m n)). Qed.
Lemma lem941010 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem940952 n) (@lem940951 n)). Qed.
Lemma lem941011 (m : nat) (n : nat) : (term133 m n) = (term134 m n).
Proof. exact (@lem941010 (Nat.add m n)). Qed.
Lemma lem941012 (m : nat) (n : nat) : (term137 m n) = (term138 m n).
Proof. exact (MK_COMB (@lem941008 m n) (@lem941011 m n)). Qed.
Lemma lem941013 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem941014 (m : nat) (n : nat) : (term132 m n) = (term139 m n).
Proof. exact (MK_COMB (@lem941013) (@lem941012 m n)). Qed.
Lemma lem941015 (m : nat) (n : nat) : (term128 m n) = (term139 m n).
Proof. exact (TRANS (@lem941003 m n) (@lem941014 m n)). Qed.
Lemma lem941016 (two : nat) (m : nat) (n : nat) : ((term125 m two) = (term128 m n)) = ((term130 m two) = (term139 m n)).
Proof. exact (MK_COMB (@lem941000 m two) (@lem941015 m n)). Qed.
Lemma lem941019 (m : nat) (two : nat) (n : nat) : (term122 m two n) = (term122 m two n).
Proof. exact (eq_refl (term122 m two n)). Qed.
Lemma lem941020 (two : nat) (m : nat) (n : nat) : (((Nat.pow m two) = n) = ((term125 m two) = (term128 m n))) = (((Nat.pow m two) = n) = ((term130 m two) = (term139 m n))).
Proof. exact (MK_COMB (@lem941019 m two n) (@lem941016 two m n)). Qed.
Lemma lem941023 (two : nat) (m : nat) (n : nat) : (((Nat.pow m two) = n) = ((term130 m two) = (term139 m n))) = (((Nat.pow m two) = n) = ((term125 m two) = (term128 m n))).
Proof. exact (SYM (@lem941020 two m n)). Qed.
Lemma lem941024 (two : nat) (h1 : term46 = two) : two = term46.
Proof. exact (SYM (@lem940965 two h1)). Qed.
Lemma lem941025 (m : nat) (n : nat) : (term140 m n) = (term140 m n).
Proof. exact (eq_refl (term140 m n)). Qed.
Lemma lem941026 (m : nat) (n : nat) (two : nat) (h1 : term46 = two) : (term141 m n two) = (term142 m n).
Proof. exact (MK_COMB (@lem941025 m n) (@lem941024 two h1)). Qed.
Lemma lem941027 (m : nat) (n : nat) : (term142 m n) = (((term113 m) = n) = ((term143 m) = (term139 m n))).
Proof. exact (eq_refl (term142 m n)). Qed.
Lemma lem941028 (m : nat) (n : nat) (two : nat) : (term144 m n two) = (term144 m n two).
Proof. exact (eq_refl (term144 m n two)). Qed.
Lemma lem941029 (two : nat) (m : nat) (n : nat) : ((term141 m n two) = (term142 m n)) = ((term141 m n two) = (((term113 m) = n) = ((term143 m) = (term139 m n)))).
Proof. exact (MK_COMB (@lem941028 m n two) (@lem941027 m n)). Qed.
Lemma lem941030 (two : nat) (m : nat) (n : nat) : (term141 m n two) = (((Nat.pow m two) = n) = ((term130 m two) = (term139 m n))).
Proof. exact (eq_refl (term141 m n two)). Qed.
Lemma lem941031 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem941032 (two : nat) (m : nat) (n : nat) : (term144 m n two) = (term145 two m n).
Proof. exact (MK_COMB (@lem941031) (@lem941030 two m n)). Qed.
Lemma lem941033 (m : nat) (n : nat) : (((term113 m) = n) = ((term143 m) = (term139 m n))) = (((term113 m) = n) = ((term143 m) = (term139 m n))).
Proof. exact (eq_refl (((term113 m) = n) = ((term143 m) = (term139 m n)))). Qed.
Lemma lem941034 (two : nat) (m : nat) (n : nat) : ((term141 m n two) = (((term113 m) = n) = ((term143 m) = (term139 m n)))) = ((((Nat.pow m two) = n) = ((term130 m two) = (term139 m n))) = (((term113 m) = n) = ((term143 m) = (term139 m n)))).
Proof. exact (MK_COMB (@lem941032 two m n) (@lem941033 m n)). Qed.
Lemma lem941035 (two : nat) (m : nat) (n : nat) : ((term141 m n two) = (term142 m n)) = ((((Nat.pow m two) = n) = ((term130 m two) = (term139 m n))) = (((term113 m) = n) = ((term143 m) = (term139 m n)))).
Proof. exact (TRANS (@lem941029 two m n) (@lem941034 two m n)). Qed.
Lemma lem941036 (m : nat) (n : nat) (two : nat) (h1 : term46 = two) : (((Nat.pow m two) = n) = ((term130 m two) = (term139 m n))) = (((term113 m) = n) = ((term143 m) = (term139 m n))).
Proof. exact (EQ_MP (@lem941035 two m n) (@lem941026 m n two h1)). Qed.
Lemma lem941037 (m : nat) (n : nat) (two : nat) (h1 : term46 = two) : (((term113 m) = n) = ((term143 m) = (term139 m n))) = (((Nat.pow m two) = n) = ((term130 m two) = (term139 m n))).
Proof. exact (SYM (@lem941036 m n two h1)). Qed.
Lemma lem941047 (n : nat) : (Nat.add n n) = (term44 n).
Proof. exact (EQ_MP (@lem940946 n) (@lem940945 n)). Qed.
Lemma lem941048 (m : nat) : (Nat.add m m) = (term44 m).
Proof. exact (@lem941047 m). Qed.
Lemma lem941049 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem941050 (m : nat) : (term115 m) = (term146 m).
Proof. exact (MK_COMB (@lem941049) (@lem941048 m)). Qed.
Lemma lem941051 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem941052 (m : nat) : (term129 m) = (term147 m).
Proof. exact (MK_COMB (@lem941051) (@lem941050 m)). Qed.
Lemma lem941053 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem941054 (m : nat) : (term143 m) = (term148 m).
Proof. exact (MK_COMB (@lem941052 m) (@lem941053)). Qed.
Lemma lem941055 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem941056 (m : nat) : (term149 m) = (term150 m).
Proof. exact (MK_COMB (@lem941055) (@lem941054 m)). Qed.
Lemma lem941058 (n : nat) : (Nat.add n n) = (term44 n).
Proof. exact (EQ_MP (@lem940946 n) (@lem940945 n)). Qed.
Lemma lem941059 (m : nat) (n : nat) : (term138 m n) = (term151 m n).
Proof. exact (@lem941058 (term134 m n)). Qed.
Lemma lem941061 (n : nat) : (Nat.add n n) = (term44 n).
Proof. exact (EQ_MP (@lem940946 n) (@lem940945 n)). Qed.
Lemma lem941062 (m : nat) (n : nat) : (term134 m n) = (term152 m n).
Proof. exact (@lem941061 (Nat.add m n)). Qed.
Lemma lem941065 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem941066 (m : nat) (n : nat) : (term151 m n) = (term154 m n).
Proof. exact (MK_COMB (@lem941065) (@lem941062 m n)). Qed.
Lemma lem941067 (m : nat) (n : nat) : (term138 m n) = (term154 m n).
Proof. exact (TRANS (@lem941059 m n) (@lem941066 m n)). Qed.
Lemma lem941068 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem941069 (m : nat) (n : nat) : (term139 m n) = (term155 m n).
Proof. exact (MK_COMB (@lem941068) (@lem941067 m n)). Qed.
Lemma lem941070 (m : nat) (n : nat) : ((term143 m) = (term139 m n)) = ((term148 m) = (term155 m n)).
Proof. exact (MK_COMB (@lem941056 m) (@lem941069 m n)). Qed.
Lemma lem941073 (m : nat) (n : nat) : (term121 m n) = (term121 m n).
Proof. exact (eq_refl (term121 m n)). Qed.
Lemma lem941074 (m : nat) (n : nat) : (((term113 m) = n) = ((term143 m) = (term139 m n))) = (((term113 m) = n) = ((term148 m) = (term155 m n))).
Proof. exact (MK_COMB (@lem941073 m n) (@lem941070 m n)). Qed.
Lemma lem941077 (m : nat) (n : nat) : (((term113 m) = n) = ((term148 m) = (term155 m n))) = (((term113 m) = n) = ((term143 m) = (term139 m n))).
Proof. exact (SYM (@lem941074 m n)). Qed.
Lemma lem941083 (n : nat) : (term113 n) = (Nat.mul n n).
Proof. exact (EQ_MP (@lem940933 n) (@lem940932 n)). Qed.
Lemma lem941084 (m : nat) : (term113 m) = (Nat.mul m m).
Proof. exact (@lem941083 m). Qed.
Lemma lem941085 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem941086 (m : nat) : (term119 m) = (term156 m).
Proof. exact (MK_COMB (@lem941085) (@lem941084 m)). Qed.
Lemma lem941087 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem941088 (m : nat) (n : nat) : ((term113 m) = n) = ((Nat.mul m m) = n).
Proof. exact (MK_COMB (@lem941086 m) (@lem941087 n)). Qed.
Lemma lem941091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem941092 (m : nat) (n : nat) : (term121 m n) = (term157 m n).
Proof. exact (MK_COMB (@lem941091) (@lem941088 m n)). Qed.
Lemma lem941096 (n : nat) : (term113 n) = (Nat.mul n n).
Proof. exact (EQ_MP (@lem940933 n) (@lem940932 n)). Qed.
Lemma lem941097 (m : nat) : (term148 m) = (term158 m).
Proof. exact (@lem941096 (term146 m)). Qed.
Lemma lem941099 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (EQ_MP (@lem940914 m n) (@lem940913 m n)). Qed.
Lemma lem941100 (m : nat) : (term158 m) = (term159 m).
Proof. exact (@lem941099 (term44 m) (term146 m)). Qed.
Lemma lem941102 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (EQ_MP (@lem940881 m n) (@lem940880 m n)). Qed.
Lemma lem941103 (m : nat) : (term159 m) = (term160 m).
Proof. exact (@lem941102 (term161 m) (term44 m)). Qed.
Lemma lem941104 (m : nat) : (term158 m) = (term160 m).
Proof. exact (TRANS (@lem941100 m) (@lem941103 m)). Qed.
Lemma lem941105 (m : nat) : (term148 m) = (term160 m).
Proof. exact (TRANS (@lem941097 m) (@lem941104 m)). Qed.
Lemma lem941107 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (EQ_MP (@lem940907 m n) (@lem940906 m n)). Qed.
Lemma lem941108 (m : nat) : (term161 m) = (term162 m).
Proof. exact (@lem941107 (term44 m) (term44 m)). Qed.
Lemma lem941109 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem941110 (m : nat) : (term163 m) = (term164 m).
Proof. exact (MK_COMB (@lem941109) (@lem941108 m)). Qed.
Lemma lem941111 (m : nat) : (term44 m) = (term44 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem941112 (m : nat) : (term165 m) = (term166 m).
Proof. exact (MK_COMB (@lem941110 m) (@lem941111 m)). Qed.
Lemma lem941113 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem941114 (m : nat) : (term160 m) = (term167 m).
Proof. exact (MK_COMB (@lem941113) (@lem941112 m)). Qed.
Lemma lem941115 (m : nat) : (term148 m) = (term167 m).
Proof. exact (TRANS (@lem941105 m) (@lem941114 m)). Qed.
Lemma lem941116 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem941117 (m : nat) : (term150 m) = (term168 m).
Proof. exact (MK_COMB (@lem941116) (@lem941115 m)). Qed.
Lemma lem941118 (m : nat) (n : nat) : (term155 m n) = (term155 m n).
Proof. exact (eq_refl (term155 m n)). Qed.
Lemma lem941119 (m : nat) (n : nat) : ((term148 m) = (term155 m n)) = ((term167 m) = (term155 m n)).
Proof. exact (MK_COMB (@lem941117 m) (@lem941118 m n)). Qed.
Lemma lem941122 (m : nat) (n : nat) : (((term113 m) = n) = ((term148 m) = (term155 m n))) = (((Nat.mul m m) = n) = ((term167 m) = (term155 m n))).
Proof. exact (MK_COMB (@lem941092 m n) (@lem941119 m n)). Qed.
Lemma lem941125 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term167 m) = (term155 m n))) = (((term113 m) = n) = ((term148 m) = (term155 m n))).
Proof. exact (SYM (@lem941122 m n)). Qed.
Lemma lem941131 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem940872 m n) (@lem940871 m n)). Qed.
Lemma lem941132 (m : nat) (n : nat) : ((term167 m) = (term155 m n)) = ((term166 m) = (term154 m n)).
Proof. exact (@lem941131 (term166 m) (term154 m n)). Qed.
Lemma lem941138 (m : nat) (n : nat) (p : nat) : (term69 m n p) = (term51 m n p).
Proof. exact (EQ_MP (@lem940866 m n p) (@lem940865 m n p)). Qed.
Lemma lem941139 (m : nat) : (term169 m) = (term170 m).
Proof. exact (@lem941138 term46 m (term44 m)). Qed.
Lemma lem941140 (m : nat) : (term171 m) = (term171 m).
Proof. exact (eq_refl (term171 m)). Qed.
Lemma lem941141 (m : nat) : (term162 m) = (term172 m).
Proof. exact (MK_COMB (@lem941140 m) (@lem941139 m)). Qed.
Lemma lem941143 (m : nat) (n : nat) (p : nat) : (term26 n m p) = (term25 m n p).
Proof. exact (EQ_MP (@lem940857 m n p) (@lem940856 m n p)). Qed.
Lemma lem941144 (m : nat) : (term172 m) = (term173 m).
Proof. exact (@lem941143 term46 m (term47 m)). Qed.
Lemma lem941145 (m : nat) : (term162 m) = (term173 m).
Proof. exact (TRANS (@lem941141 m) (@lem941144 m)). Qed.
Lemma lem941146 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem941147 (m : nat) : (term164 m) = (term174 m).
Proof. exact (MK_COMB (@lem941146) (@lem941145 m)). Qed.
Lemma lem941148 (m : nat) : (term44 m) = (term44 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem941149 (m : nat) : (term166 m) = (term175 m).
Proof. exact (MK_COMB (@lem941147 m) (@lem941148 m)). Qed.
Lemma lem941151 (m : nat) (n : nat) (p : nat) : (term26 n m p) = (term25 m n p).
Proof. exact (EQ_MP (@lem940857 m n p) (@lem940856 m n p)). Qed.
Lemma lem941152 (m : nat) : (term175 m) = (term176 m).
Proof. exact (@lem941151 term46 (term64 m) m). Qed.
Lemma lem941153 (m : nat) : (term166 m) = (term176 m).
Proof. exact (TRANS (@lem941149 m) (@lem941152 m)). Qed.
Lemma lem941154 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem941155 (m : nat) : (term177 m) = (term178 m).
Proof. exact (MK_COMB (@lem941154) (@lem941153 m)). Qed.
Lemma lem941156 (m : nat) (n : nat) : (term154 m n) = (term154 m n).
Proof. exact (eq_refl (term154 m n)). Qed.
Lemma lem941157 (m : nat) (n : nat) : ((term166 m) = (term154 m n)) = ((term176 m) = (term154 m n)).
Proof. exact (MK_COMB (@lem941155 m) (@lem941156 m n)). Qed.
Lemma lem941160 (m : nat) (n : nat) : ((term167 m) = (term155 m n)) = ((term176 m) = (term154 m n)).
Proof. exact (TRANS (@lem941132 m n) (@lem941157 m n)). Qed.
Lemma lem941161 (m : nat) (n : nat) : (term157 m n) = (term157 m n).
Proof. exact (eq_refl (term157 m n)). Qed.
Lemma lem941162 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term167 m) = (term155 m n))) = (((Nat.mul m m) = n) = ((term176 m) = (term154 m n))).
Proof. exact (MK_COMB (@lem941161 m n) (@lem941160 m n)). Qed.
Lemma lem941165 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term176 m) = (term154 m n))) = (((Nat.mul m m) = n) = ((term167 m) = (term155 m n))).
Proof. exact (SYM (@lem941162 m n)). Qed.
Lemma lem941173 (m : nat) : (term61 m) = (term68 m).
Proof. exact (EQ_MP (@lem940812 m) (@lem0)). Qed.
Lemma lem941174 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem941175 (m : nat) : (term176 m) = (term179 m).
Proof. exact (MK_COMB (@lem941174) (@lem941173 m)). Qed.
Lemma lem941176 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem941177 (m : nat) : (term178 m) = (term180 m).
Proof. exact (MK_COMB (@lem941176) (@lem941175 m)). Qed.
Lemma lem941178 (m : nat) (n : nat) : (term154 m n) = (term154 m n).
Proof. exact (eq_refl (term154 m n)). Qed.
Lemma lem941179 (m : nat) (n : nat) : ((term176 m) = (term154 m n)) = ((term179 m) = (term154 m n)).
Proof. exact (MK_COMB (@lem941177 m) (@lem941178 m n)). Qed.
Lemma lem941182 (m : nat) (n : nat) : (term157 m n) = (term157 m n).
Proof. exact (eq_refl (term157 m n)). Qed.
Lemma lem941183 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term176 m) = (term154 m n))) = (((Nat.mul m m) = n) = ((term179 m) = (term154 m n))).
Proof. exact (MK_COMB (@lem941182 m n) (@lem941179 m n)). Qed.
Lemma lem941186 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term179 m) = (term154 m n))) = (((Nat.mul m m) = n) = ((term176 m) = (term154 m n))).
Proof. exact (SYM (@lem941183 m n)). Qed.
Lemma lem941196 (m : nat) : (term47 m) = (term52 m).
Proof. exact (EQ_MP (@lem940732 m) (@lem0)). Qed.
Lemma lem941197 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem941198 (m : nat) : (term181 m) = (term182 m).
Proof. exact (MK_COMB (@lem941197) (@lem941196 m)). Qed.
Lemma lem941200 (n : nat) : (Nat.add n n) = (term44 n).
Proof. exact (EQ_MP (@lem940745 n) (@lem940744 n)). Qed.
Lemma lem941201 (m : nat) : (Nat.add m m) = (term44 m).
Proof. exact (@lem941200 m). Qed.
Lemma lem941202 (m : nat) : (term68 m) = (term183 m).
Proof. exact (MK_COMB (@lem941198 m) (@lem941201 m)). Qed.
Lemma lem941205 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem941206 (m : nat) : (term179 m) = (term184 m).
Proof. exact (MK_COMB (@lem941205) (@lem941202 m)). Qed.
Lemma lem941207 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem941208 (m : nat) : (term180 m) = (term185 m).
Proof. exact (MK_COMB (@lem941207) (@lem941206 m)). Qed.
Lemma lem941213 (m : nat) (n : nat) : (term154 m n) = (term154 m n).
Proof. exact (eq_refl (term154 m n)). Qed.
Lemma lem941214 (m : nat) (n : nat) : ((term179 m) = (term154 m n)) = ((term184 m) = (term154 m n)).
Proof. exact (MK_COMB (@lem941208 m) (@lem941213 m n)). Qed.
Lemma lem941217 (m : nat) (n : nat) : (term157 m n) = (term157 m n).
Proof. exact (eq_refl (term157 m n)). Qed.
Lemma lem941218 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term179 m) = (term154 m n))) = (((Nat.mul m m) = n) = ((term184 m) = (term154 m n))).
Proof. exact (MK_COMB (@lem941217 m n) (@lem941214 m n)). Qed.
Lemma lem941221 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term184 m) = (term154 m n))) = (((Nat.mul m m) = n) = ((term179 m) = (term154 m n))).
Proof. exact (SYM (@lem941218 m n)). Qed.
Lemma lem941229 (m : nat) (n : nat) (p : nat) : (term26 n m p) = (term25 m n p).
Proof. exact (EQ_MP (@lem940660 m n p) (@lem940659 m n p)). Qed.
Lemma lem941230 (m : nat) : (term183 m) = (term186 m).
Proof. exact (@lem941229 term46 (Nat.mul m m) m). Qed.
Lemma lem941231 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem941232 (m : nat) : (term184 m) = (term187 m).
Proof. exact (MK_COMB (@lem941231) (@lem941230 m)). Qed.
Lemma lem941233 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem941234 (m : nat) : (term185 m) = (term188 m).
Proof. exact (MK_COMB (@lem941233) (@lem941232 m)). Qed.
Lemma lem941235 (m : nat) (n : nat) : (term154 m n) = (term154 m n).
Proof. exact (eq_refl (term154 m n)). Qed.
Lemma lem941236 (m : nat) (n : nat) : ((term184 m) = (term154 m n)) = ((term187 m) = (term154 m n)).
Proof. exact (MK_COMB (@lem941234 m) (@lem941235 m n)). Qed.
Lemma lem941239 (m : nat) (n : nat) : (term157 m n) = (term157 m n).
Proof. exact (eq_refl (term157 m n)). Qed.
Lemma lem941240 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term184 m) = (term154 m n))) = (((Nat.mul m m) = n) = ((term187 m) = (term154 m n))).
Proof. exact (MK_COMB (@lem941239 m n) (@lem941236 m n)). Qed.
Lemma lem941243 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term187 m) = (term154 m n))) = (((Nat.mul m m) = n) = ((term184 m) = (term154 m n))).
Proof. exact (SYM (@lem941240 m n)). Qed.
Lemma lem941249 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term24 m n p).
Proof. exact (EQ_MP (@lem940615 m n p) (@lem940614 m n p)). Qed.
Lemma lem941250 (m : nat) (n : nat) : ((term187 m) = (term154 m n)) = (term189 m n).
Proof. exact (@lem941249 term46 (term186 m) (term152 m n)). Qed.
Lemma lem941254 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem940606 m n) (@lem940605 m n)). Qed.
Lemma lem941255 : (term46 = (NUMERAL 0)) = (term190 = 0).
Proof. exact (@lem941254 term190 0). Qed.
Lemma lem941257 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem940598 n) (@lem940597 n)). Qed.
Lemma lem941258 : (term190 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem941257 (BIT1 0)). Qed.
Lemma lem941260 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem940594 n) (@lem940593 n)). Qed.
Lemma lem941261 : ((BIT1 0) = 0) = False.
Proof. exact (@lem941260 0). Qed.
Lemma lem941262 : (term190 = 0) = False.
Proof. exact (TRANS (@lem941258) (@lem941261)). Qed.
Lemma lem941263 : (term46 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem941255) (@lem941262)). Qed.
Lemma lem941264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem941265 : term191 = (or False).
Proof. exact (MK_COMB (@lem941264) (@lem941263)). Qed.
Lemma lem941267 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term24 m n p).
Proof. exact (EQ_MP (@lem940615 m n p) (@lem940614 m n p)). Qed.
Lemma lem941268 (m : nat) (n : nat) : ((term186 m) = (term152 m n)) = (term192 m n).
Proof. exact (@lem941267 term46 (term193 m) (Nat.add m n)). Qed.
Lemma lem941272 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem940606 m n) (@lem940605 m n)). Qed.
Lemma lem941273 : (term46 = (NUMERAL 0)) = (term190 = 0).
Proof. exact (@lem941272 term190 0). Qed.
Lemma lem941275 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem940598 n) (@lem940597 n)). Qed.
Lemma lem941276 : (term190 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem941275 (BIT1 0)). Qed.
Lemma lem941278 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem940594 n) (@lem940593 n)). Qed.
Lemma lem941279 : ((BIT1 0) = 0) = False.
Proof. exact (@lem941278 0). Qed.
Lemma lem941280 : (term190 = 0) = False.
Proof. exact (TRANS (@lem941276) (@lem941279)). Qed.
Lemma lem941281 : (term46 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem941273) (@lem941280)). Qed.
Lemma lem941282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem941283 : term191 = (or False).
Proof. exact (MK_COMB (@lem941282) (@lem941281)). Qed.
Lemma lem941286 (m : nat) (n : nat) : ((term193 m) = (Nat.add m n)) = ((term193 m) = (Nat.add m n)).
Proof. exact (eq_refl ((term193 m) = (Nat.add m n))). Qed.
Lemma lem941287 (m : nat) (n : nat) : (term192 m n) = (term194 m n).
Proof. exact (MK_COMB (@lem941283) (@lem941286 m n)). Qed.
Lemma lem941289 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem941290 (m : nat) (n : nat) : (term194 m n) = ((term193 m) = (Nat.add m n)).
Proof. exact (@lem941289 ((term193 m) = (Nat.add m n))). Qed.
Lemma lem941293 (m : nat) (n : nat) : (term192 m n) = ((term193 m) = (Nat.add m n)).
Proof. exact (TRANS (@lem941287 m n) (@lem941290 m n)). Qed.
Lemma lem941294 (m : nat) (n : nat) : ((term186 m) = (term152 m n)) = ((term193 m) = (Nat.add m n)).
Proof. exact (TRANS (@lem941268 m n) (@lem941293 m n)). Qed.
Lemma lem941295 (m : nat) (n : nat) : (term189 m n) = (term194 m n).
Proof. exact (MK_COMB (@lem941265) (@lem941294 m n)). Qed.
Lemma lem941297 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem941298 (m : nat) (n : nat) : (term194 m n) = ((term193 m) = (Nat.add m n)).
Proof. exact (@lem941297 ((term193 m) = (Nat.add m n))). Qed.
Lemma lem941301 (m : nat) (n : nat) : (term189 m n) = ((term193 m) = (Nat.add m n)).
Proof. exact (TRANS (@lem941295 m n) (@lem941298 m n)). Qed.
Lemma lem941302 (m : nat) (n : nat) : ((term187 m) = (term154 m n)) = ((term193 m) = (Nat.add m n)).
Proof. exact (TRANS (@lem941250 m n) (@lem941301 m n)). Qed.
Lemma lem941303 (m : nat) (n : nat) : (term157 m n) = (term157 m n).
Proof. exact (eq_refl (term157 m n)). Qed.
Lemma lem941304 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term187 m) = (term154 m n))) = (((Nat.mul m m) = n) = ((term193 m) = (Nat.add m n))).
Proof. exact (MK_COMB (@lem941303 m n) (@lem941302 m n)). Qed.
Lemma lem941307 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term193 m) = (Nat.add m n))) = (((Nat.mul m m) = n) = ((term187 m) = (term154 m n))).
Proof. exact (SYM (@lem941304 m n)). Qed.
Lemma lem941309 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem940546 n m) (@lem940545 m n)). Qed.
Lemma lem941310 (m : nat) : (term195 m) = (term195 m).
Proof. exact (eq_refl (term195 m)). Qed.
Lemma lem941311 (n : nat) (m : nat) : ((term193 m) = (Nat.add m n)) = ((term193 m) = (Nat.add n m)).
Proof. exact (MK_COMB (@lem941310 m) (@lem941309 n m)). Qed.
Lemma lem941312 (m : nat) (n : nat) : (term157 m n) = (term157 m n).
Proof. exact (eq_refl (term157 m n)). Qed.
Lemma lem941313 (n : nat) (m : nat) : (((Nat.mul m m) = n) = ((term193 m) = (Nat.add m n))) = (((Nat.mul m m) = n) = ((term193 m) = (Nat.add n m))).
Proof. exact (MK_COMB (@lem941312 m n) (@lem941311 n m)). Qed.
Lemma lem941314 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term193 m) = (Nat.add n m))) = (((Nat.mul m m) = n) = ((term193 m) = (Nat.add m n))).
Proof. exact (SYM (@lem941313 n m)). Qed.
Lemma lem941320 (p : nat) (m : nat) (n : nat) : ((Nat.add m p) = (Nat.add n p)) = (m = n).
Proof. exact (EQ_MP (@lem940540 p m n) (@lem940539 m n p)). Qed.
Lemma lem941321 (m : nat) (n : nat) : ((term193 m) = (Nat.add n m)) = ((Nat.mul m m) = n).
Proof. exact (@lem941320 m (Nat.mul m m) n). Qed.
Lemma lem941324 (m : nat) (n : nat) : (term157 m n) = (term157 m n).
Proof. exact (eq_refl (term157 m n)). Qed.
Lemma lem941325 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term193 m) = (Nat.add n m))) = (((Nat.mul m m) = n) = ((Nat.mul m m) = n)).
Proof. exact (MK_COMB (@lem941324 m n) (@lem941321 m n)). Qed.
Lemma lem941327 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem941328 (x : Prop) : (x = x) = True.
Proof. exact (@lem941327 Prop x). Qed.
Lemma lem941329 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((Nat.mul m m) = n)) = True.
Proof. exact (@lem941328 ((Nat.mul m m) = n)). Qed.
Lemma lem941330 (n : nat) (m : nat) : (((Nat.mul m m) = n) = ((term193 m) = (Nat.add n m))) = True.
Proof. exact (TRANS (@lem941325 m n) (@lem941329 m n)). Qed.
Lemma lem941331 (n : nat) (m : nat) : True = (((Nat.mul m m) = n) = ((term193 m) = (Nat.add n m))).
Proof. exact (SYM (@lem941330 n m)). Qed.
Lemma lem941332 (n : nat) (m : nat) : ((Nat.mul m m) = n) = ((term193 m) = (Nat.add n m)).
Proof. exact (EQ_MP (@lem941331 n m) (@lem0)). Qed.
Lemma lem941333 (m : nat) (n : nat) : ((Nat.mul m m) = n) = ((term193 m) = (Nat.add m n)).
Proof. exact (EQ_MP (@lem941314 m n) (@lem941332 n m)). Qed.
Lemma lem941334 (m : nat) (n : nat) : ((Nat.mul m m) = n) = ((term187 m) = (term154 m n)).
Proof. exact (EQ_MP (@lem941307 m n) (@lem941333 m n)). Qed.
Lemma lem941335 (m : nat) (n : nat) : ((Nat.mul m m) = n) = ((term184 m) = (term154 m n)).
Proof. exact (EQ_MP (@lem941243 m n) (@lem941334 m n)). Qed.
Lemma lem941336 (m : nat) (n : nat) : ((Nat.mul m m) = n) = ((term179 m) = (term154 m n)).
Proof. exact (EQ_MP (@lem941221 m n) (@lem941335 m n)). Qed.
Lemma lem941337 (m : nat) (n : nat) : ((Nat.mul m m) = n) = ((term176 m) = (term154 m n)).
Proof. exact (EQ_MP (@lem941186 m n) (@lem941336 m n)). Qed.
Lemma lem941338 (m : nat) (n : nat) : ((Nat.mul m m) = n) = ((term167 m) = (term155 m n)).
Proof. exact (EQ_MP (@lem941165 m n) (@lem941337 m n)). Qed.
Lemma lem941339 (m : nat) (n : nat) : ((term113 m) = n) = ((term148 m) = (term155 m n)).
Proof. exact (EQ_MP (@lem941125 m n) (@lem941338 m n)). Qed.
Lemma lem941341 (m : nat) (n : nat) : ((term113 m) = n) = ((term143 m) = (term139 m n)).
Proof. exact (EQ_MP (@lem941077 m n) (@lem941339 m n)). Qed.
Lemma lem941342 (m : nat) (n : nat) (two : nat) (h1 : term46 = two) : ((Nat.pow m two) = n) = ((term130 m two) = (term139 m n)).
Proof. exact (EQ_MP (@lem941037 m n two h1) (@lem941341 m n)). Qed.
Lemma lem941343 (m : nat) (n : nat) (two : nat) (h1 : term46 = two) : ((Nat.pow m two) = n) = ((term125 m two) = (term128 m n)).
Proof. exact (EQ_MP (@lem941023 two m n) (@lem941342 m n two h1)). Qed.
Lemma lem941344 (m : nat) (n : nat) (two : nat) (h1 : term46 = two) : (term46 = two) = (((Nat.pow m two) = n) = ((term125 m two) = (term128 m n))).
Proof. exact (prop_ext (fun h2 : term46 = two => @lem941343 m n two h1) (fun h2 : ((Nat.pow m two) = n) = ((term125 m two) = (term128 m n)) => @lem940965 two h1)). Qed.
Lemma lem941345 (m : nat) (n : nat) (two : nat) (h1 : term46 = two) : ((Nat.pow m two) = n) = ((term125 m two) = (term128 m n)).
Proof. exact (EQ_MP (@lem941344 m n two h1) (@lem940965 two h1)). Qed.
Lemma lem941346 (m : nat) (n : nat) (two : nat) (h1 : term46 = two) : ((term113 m) = n) = ((term124 m) = (term128 m n)).
Proof. exact (EQ_MP (@lem940985 m n two h1) (@lem941345 m n two h1)). Qed.
Lemma lem941349 (m : nat) (n : nat) : ((term113 m) = n) = ((term124 m) = (term128 m n)).
Proof. exact (ex_elim (@lem940964) (fun two : nat => fun h0 : term118 two => @lem941346 m n two h0)). Qed.
