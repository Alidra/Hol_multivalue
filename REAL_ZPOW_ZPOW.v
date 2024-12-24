Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_ZPOW_term_abbrevs.
Require Import FORALL_INT_CASES_spec.
Require Import INT_MUL_LNEG_spec.
Require Import INT_MUL_RNEG_spec.
Require Import INT_NEG_NEG_spec.
Require Import INT_OF_NUM_MUL_spec.
Require Import REAL_INV_INV_spec.
Require Import REAL_INV_POW_spec.
Require Import REAL_POW_POW_spec.
Require Import REAL_ZPOW_POW_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3174522 (x : real) : term0 x.
Proof. exact (@lem1640492 x). Qed.
Lemma lem3174523 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3174524 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem3174523 x) (@lem3174522 x)). Qed.
Lemma lem3174525 (x : real) (m : nat) : term2 x m.
Proof. exact (@lem3174524 x m). Qed.
Lemma lem3174526 (x : real) (m : nat) : (term2 x m) = (term3 x m).
Proof. exact (eq_refl (term2 x m)). Qed.
Lemma lem3174527 (x : real) (m : nat) : term3 x m.
Proof. exact (EQ_MP (@lem3174526 x m) (@lem3174525 x m)). Qed.
Lemma lem3174528 (x : real) (m : nat) (n : nat) : term4 x m n.
Proof. exact (@lem3174527 x m n). Qed.
Lemma lem3174529 (x : real) (m : nat) (n : nat) : (term4 x m n) = ((term5 x m n) = (term6 x m n)).
Proof. exact (eq_refl (term4 x m n)). Qed.
Lemma lem3174531 (x : real) : term7 x.
Proof. exact (@lem1587920 x). Qed.
Lemma lem3174532 (x : real) : (term7 x) = ((term8 x) = x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem3174534 (m : nat) : term9 m.
Proof. exact (@lem2307381 m). Qed.
Lemma lem3174535 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem3174536 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem3174535 m) (@lem3174534 m)). Qed.
Lemma lem3174537 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem3174536 m n). Qed.
Lemma lem3174538 (m : nat) (n : nat) : (term11 m n) = ((term12 m n) = (term13 m n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem3174540 (x : real) : term14 x.
Proof. exact (@lem1595722 x). Qed.
Lemma lem3174541 (x : real) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem3174542 (x : real) : term15 x.
Proof. exact (EQ_MP (@lem3174541 x) (@lem3174540 x)). Qed.
Lemma lem3174543 (x : real) (n : nat) : term16 x n.
Proof. exact (@lem3174542 x n). Qed.
Lemma lem3174544 (x : real) (n : nat) : (term16 x n) = ((term17 x n) = (term18 x n)).
Proof. exact (eq_refl (term16 x n)). Qed.
Lemma lem3174546 : term19.
Proof. exact (proj2 (@lem3174260)). Qed.
Lemma lem3174547 (x : real) : term20 x.
Proof. exact (@lem3174546 x). Qed.
Lemma lem3174548 (x : real) : (term20 x) = (term21 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem3174549 (x : real) : term21 x.
Proof. exact (EQ_MP (@lem3174548 x) (@lem3174547 x)). Qed.
Lemma lem3174550 (x : real) (n : nat) : term22 x n.
Proof. exact (@lem3174549 x n). Qed.
Lemma lem3174551 (x : real) (n : nat) : (term22 x n) = ((term23 x n) = (term17 x n)).
Proof. exact (eq_refl (term22 x n)). Qed.
Lemma lem3174553 : term24.
Proof. exact (proj1 (@lem3174260)). Qed.
Lemma lem3174554 (x : real) : term25 x.
Proof. exact (@lem3174553 x). Qed.
Lemma lem3174555 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem3174556 (x : real) : term26 x.
Proof. exact (EQ_MP (@lem3174555 x) (@lem3174554 x)). Qed.
Lemma lem3174557 (x : real) (n : nat) : term27 x n.
Proof. exact (@lem3174556 x n). Qed.
Lemma lem3174558 (x : real) (n : nat) : (term27 x n) = ((term28 x n) = (real_pow x n)).
Proof. exact (eq_refl (term27 x n)). Qed.
Lemma lem3174560 (x : int) : term29 x.
Proof. exact (@lem2306663 x). Qed.
Lemma lem3174561 (x : int) : (term29 x) = ((term30 x) = x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem3174563 (x : int) : term31 x.
Proof. exact (@lem2306266 x). Qed.
Lemma lem3174564 (x : int) : (term31 x) = (term32 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem3174565 (x : int) : term32 x.
Proof. exact (EQ_MP (@lem3174564 x) (@lem3174563 x)). Qed.
Lemma lem3174566 (x : int) (y : int) : term33 x y.
Proof. exact (@lem3174565 x y). Qed.
Lemma lem3174567 (x : int) (y : int) : (term33 x y) = ((term34 x y) = (term35 x y)).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem3174569 (x : int) : term36 x.
Proof. exact (@lem2306015 x). Qed.
Lemma lem3174570 (x : int) : (term36 x) = (term37 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem3174571 (x : int) : term37 x.
Proof. exact (EQ_MP (@lem3174570 x) (@lem3174569 x)). Qed.
Lemma lem3174572 (x : int) (y : int) : term38 x y.
Proof. exact (@lem3174571 x y). Qed.
Lemma lem3174573 (x : int) (y : int) : (term38 x y) = ((term39 x y) = (term35 x y)).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem3174575 (P : int -> Prop) : term40 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem3174576 (P : int -> Prop) : (term40 P) = ((term41 P) = (term42 P)).
Proof. exact (eq_refl (term40 P)). Qed.
Lemma lem3174589 (P : int -> Prop) : (term41 P) = (term42 P).
Proof. exact (EQ_MP (@lem3174576 P) (@lem3174575 P)). Qed.
Lemma lem3174590 (x : real) : (term43 x) = (term44 x).
Proof. exact (@lem3174589 (term45 x)). Qed.
Lemma lem3174591 (x : real) (m : int) : (term46 x m) = (term47 x m).
Proof. exact (eq_refl (term46 x m)). Qed.
Lemma lem3174592 (x : real) : (term48 x) = (term45 x).
Proof. exact (fun_ext (fun m : int => @lem3174591 x m)). Qed.
Lemma lem3174593 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3174594 (x : real) : (term43 x) = (term49 x).
Proof. exact (MK_COMB (@lem3174593) (@lem3174592 x)). Qed.
Lemma lem3174595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3174596 (x : real) : (term50 x) = (term51 x).
Proof. exact (MK_COMB (@lem3174595) (@lem3174594 x)). Qed.
Lemma lem3174597 (x : real) (n : nat) : (term52 x n) = (term53 x n).
Proof. exact (eq_refl (term52 x n)). Qed.
Lemma lem3174598 (x : real) : (term54 x) = (term55 x).
Proof. exact (fun_ext (fun n : nat => @lem3174597 x n)). Qed.
Lemma lem3174599 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174600 (x : real) : (term56 x) = (term57 x).
Proof. exact (MK_COMB (@lem3174599) (@lem3174598 x)). Qed.
Lemma lem3174601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3174602 (x : real) : (term58 x) = (term59 x).
Proof. exact (MK_COMB (@lem3174601) (@lem3174600 x)). Qed.
Lemma lem3174603 (x : real) (n : nat) : (term60 x n) = (term61 x n).
Proof. exact (eq_refl (term60 x n)). Qed.
Lemma lem3174604 (x : real) : (term62 x) = (term63 x).
Proof. exact (fun_ext (fun n : nat => @lem3174603 x n)). Qed.
Lemma lem3174605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174606 (x : real) : (term64 x) = (term65 x).
Proof. exact (MK_COMB (@lem3174605) (@lem3174604 x)). Qed.
Lemma lem3174607 (x : real) : (term44 x) = (term66 x).
Proof. exact (MK_COMB (@lem3174602 x) (@lem3174606 x)). Qed.
Lemma lem3174608 (x : real) : ((term43 x) = (term44 x)) = ((term49 x) = (term66 x)).
Proof. exact (MK_COMB (@lem3174596 x) (@lem3174607 x)). Qed.
Lemma lem3174609 (x : real) : (term49 x) = (term66 x).
Proof. exact (EQ_MP (@lem3174608 x) (@lem3174590 x)). Qed.
Lemma lem3174623 (P : int -> Prop) : (term41 P) = (term42 P).
Proof. exact (EQ_MP (@lem3174576 P) (@lem3174575 P)). Qed.
Lemma lem3174624 (x : real) (n : nat) : (term67 x n) = (term68 x n).
Proof. exact (@lem3174623 (term69 x n)). Qed.
Lemma lem3174625 (x : real) (n : nat) (n' : int) : (term70 x n n') = ((term71 x n n') = (term72 x n n')).
Proof. exact (eq_refl (term70 x n n')). Qed.
Lemma lem3174626 (x : real) (n : nat) : (term73 x n) = (term69 x n).
Proof. exact (fun_ext (fun n' : int => @lem3174625 x n n')). Qed.
Lemma lem3174627 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3174628 (x : real) (n : nat) : (term67 x n) = (term53 x n).
Proof. exact (MK_COMB (@lem3174627) (@lem3174626 x n)). Qed.
Lemma lem3174629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3174630 (x : real) (n : nat) : (term74 x n) = (term75 x n).
Proof. exact (MK_COMB (@lem3174629) (@lem3174628 x n)). Qed.
Lemma lem3174631 (x : real) (n : nat) (n' : nat) : (term76 x n n') = ((term77 x n n') = (term78 x n n')).
Proof. exact (eq_refl (term76 x n n')). Qed.
Lemma lem3174632 (x : real) (n : nat) : (term79 x n) = (term80 x n).
Proof. exact (fun_ext (fun n' : nat => @lem3174631 x n n')). Qed.
Lemma lem3174633 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174634 (x : real) (n : nat) : (term81 x n) = (term82 x n).
Proof. exact (MK_COMB (@lem3174633) (@lem3174632 x n)). Qed.
Lemma lem3174635 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3174636 (x : real) (n : nat) : (term83 x n) = (term84 x n).
Proof. exact (MK_COMB (@lem3174635) (@lem3174634 x n)). Qed.
Lemma lem3174637 (x : real) (n : nat) (n' : nat) : (term85 x n n') = ((term86 x n n') = (term87 x n n')).
Proof. exact (eq_refl (term85 x n n')). Qed.
Lemma lem3174638 (x : real) (n : nat) : (term88 x n) = (term89 x n).
Proof. exact (fun_ext (fun n' : nat => @lem3174637 x n n')). Qed.
Lemma lem3174639 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174640 (x : real) (n : nat) : (term90 x n) = (term91 x n).
Proof. exact (MK_COMB (@lem3174639) (@lem3174638 x n)). Qed.
Lemma lem3174641 (x : real) (n : nat) : (term68 x n) = (term92 x n).
Proof. exact (MK_COMB (@lem3174636 x n) (@lem3174640 x n)). Qed.
Lemma lem3174642 (x : real) (n : nat) : ((term67 x n) = (term68 x n)) = ((term53 x n) = (term92 x n)).
Proof. exact (MK_COMB (@lem3174630 x n) (@lem3174641 x n)). Qed.
Lemma lem3174643 (x : real) (n : nat) : (term53 x n) = (term92 x n).
Proof. exact (EQ_MP (@lem3174642 x n) (@lem3174624 x n)). Qed.
Lemma lem3174663 (x : int) (y : int) : (term34 x y) = (term35 x y).
Proof. exact (EQ_MP (@lem3174567 x y) (@lem3174566 x y)). Qed.
Lemma lem3174664 (n : nat) (n' : nat) : (term93 n n') = (term94 n n').
Proof. exact (@lem3174663 (int_of_num n) (int_of_num n')). Qed.
Lemma lem3174665 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3174666 (x : real) (n : nat) (n' : nat) : (term87 x n n') = (term95 x n n').
Proof. exact (MK_COMB (@lem3174665 x) (@lem3174664 n n')). Qed.
Lemma lem3174667 (x : real) (n : nat) (n' : nat) : (term96 x n n') = (term96 x n n').
Proof. exact (eq_refl (term96 x n n')). Qed.
Lemma lem3174668 (x : real) (n : nat) (n' : nat) : ((term86 x n n') = (term87 x n n')) = ((term86 x n n') = (term95 x n n')).
Proof. exact (MK_COMB (@lem3174667 x n n') (@lem3174666 x n n')). Qed.
Lemma lem3174671 (x : real) (n : nat) : (term89 x n) = (term97 x n).
Proof. exact (fun_ext (fun n' : nat => @lem3174668 x n n')). Qed.
Lemma lem3174672 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174673 (x : real) (n : nat) : (term91 x n) = (term98 x n).
Proof. exact (MK_COMB (@lem3174672) (@lem3174671 x n)). Qed.
Lemma lem3174680 (x : real) (n : nat) : (term84 x n) = (term84 x n).
Proof. exact (eq_refl (term84 x n)). Qed.
Lemma lem3174681 (x : real) (n : nat) : (term92 x n) = (term99 x n).
Proof. exact (MK_COMB (@lem3174680 x n) (@lem3174673 x n)). Qed.
Lemma lem3174684 (x : real) (n : nat) : (term53 x n) = (term99 x n).
Proof. exact (TRANS (@lem3174643 x n) (@lem3174681 x n)). Qed.
Lemma lem3174685 (x : real) : (term55 x) = (term100 x).
Proof. exact (fun_ext (fun n : nat => @lem3174684 x n)). Qed.
Lemma lem3174686 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174687 (x : real) : (term57 x) = (term101 x).
Proof. exact (MK_COMB (@lem3174686) (@lem3174685 x)). Qed.
Lemma lem3174694 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3174695 (x : real) : (term59 x) = (term102 x).
Proof. exact (MK_COMB (@lem3174694) (@lem3174687 x)). Qed.
Lemma lem3174707 (P : int -> Prop) : (term41 P) = (term42 P).
Proof. exact (EQ_MP (@lem3174576 P) (@lem3174575 P)). Qed.
Lemma lem3174708 (x : real) (n : nat) : (term103 x n) = (term104 x n).
Proof. exact (@lem3174707 (term105 x n)). Qed.
Lemma lem3174709 (x : real) (n : nat) (n' : int) : (term106 x n n') = ((term107 x n n') = (term108 x n n')).
Proof. exact (eq_refl (term106 x n n')). Qed.
Lemma lem3174710 (x : real) (n : nat) : (term109 x n) = (term105 x n).
Proof. exact (fun_ext (fun n' : int => @lem3174709 x n n')). Qed.
Lemma lem3174711 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3174712 (x : real) (n : nat) : (term103 x n) = (term61 x n).
Proof. exact (MK_COMB (@lem3174711) (@lem3174710 x n)). Qed.
Lemma lem3174713 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3174714 (x : real) (n : nat) : (term110 x n) = (term111 x n).
Proof. exact (MK_COMB (@lem3174713) (@lem3174712 x n)). Qed.
Lemma lem3174715 (x : real) (n : nat) (n' : nat) : (term112 x n n') = ((term113 x n n') = (term114 x n n')).
Proof. exact (eq_refl (term112 x n n')). Qed.
Lemma lem3174716 (x : real) (n : nat) : (term115 x n) = (term116 x n).
Proof. exact (fun_ext (fun n' : nat => @lem3174715 x n n')). Qed.
Lemma lem3174717 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174718 (x : real) (n : nat) : (term117 x n) = (term118 x n).
Proof. exact (MK_COMB (@lem3174717) (@lem3174716 x n)). Qed.
Lemma lem3174719 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3174720 (x : real) (n : nat) : (term119 x n) = (term120 x n).
Proof. exact (MK_COMB (@lem3174719) (@lem3174718 x n)). Qed.
Lemma lem3174721 (x : real) (n : nat) (n' : nat) : (term121 x n n') = ((term122 x n n') = (term123 x n n')).
Proof. exact (eq_refl (term121 x n n')). Qed.
Lemma lem3174722 (x : real) (n : nat) : (term124 x n) = (term125 x n).
Proof. exact (fun_ext (fun n' : nat => @lem3174721 x n n')). Qed.
Lemma lem3174723 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174724 (x : real) (n : nat) : (term126 x n) = (term127 x n).
Proof. exact (MK_COMB (@lem3174723) (@lem3174722 x n)). Qed.
Lemma lem3174725 (x : real) (n : nat) : (term104 x n) = (term128 x n).
Proof. exact (MK_COMB (@lem3174720 x n) (@lem3174724 x n)). Qed.
Lemma lem3174726 (x : real) (n : nat) : ((term103 x n) = (term104 x n)) = ((term61 x n) = (term128 x n)).
Proof. exact (MK_COMB (@lem3174714 x n) (@lem3174725 x n)). Qed.
Lemma lem3174727 (x : real) (n : nat) : (term61 x n) = (term128 x n).
Proof. exact (EQ_MP (@lem3174726 x n) (@lem3174708 x n)). Qed.
Lemma lem3174739 (x : int) (y : int) : (term39 x y) = (term35 x y).
Proof. exact (EQ_MP (@lem3174573 x y) (@lem3174572 x y)). Qed.
Lemma lem3174740 (n : nat) (n' : nat) : (term129 n n') = (term94 n n').
Proof. exact (@lem3174739 (int_of_num n) (int_of_num n')). Qed.
Lemma lem3174741 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3174742 (x : real) (n : nat) (n' : nat) : (term114 x n n') = (term95 x n n').
Proof. exact (MK_COMB (@lem3174741 x) (@lem3174740 n n')). Qed.
Lemma lem3174743 (x : real) (n : nat) (n' : nat) : (term130 x n n') = (term130 x n n').
Proof. exact (eq_refl (term130 x n n')). Qed.
Lemma lem3174744 (x : real) (n : nat) (n' : nat) : ((term113 x n n') = (term114 x n n')) = ((term113 x n n') = (term95 x n n')).
Proof. exact (MK_COMB (@lem3174743 x n n') (@lem3174742 x n n')). Qed.
Lemma lem3174747 (x : real) (n : nat) : (term116 x n) = (term131 x n).
Proof. exact (fun_ext (fun n' : nat => @lem3174744 x n n')). Qed.
Lemma lem3174748 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174749 (x : real) (n : nat) : (term118 x n) = (term132 x n).
Proof. exact (MK_COMB (@lem3174748) (@lem3174747 x n)). Qed.
Lemma lem3174756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3174757 (x : real) (n : nat) : (term120 x n) = (term133 x n).
Proof. exact (MK_COMB (@lem3174756) (@lem3174749 x n)). Qed.
Lemma lem3174767 (x : int) (y : int) : (term39 x y) = (term35 x y).
Proof. exact (EQ_MP (@lem3174573 x y) (@lem3174572 x y)). Qed.
Lemma lem3174768 (n : nat) (n' : nat) : (term134 n n') = (term135 n n').
Proof. exact (@lem3174767 (int_of_num n) (term136 n')). Qed.
Lemma lem3174770 (x : int) (y : int) : (term34 x y) = (term35 x y).
Proof. exact (EQ_MP (@lem3174567 x y) (@lem3174566 x y)). Qed.
Lemma lem3174771 (n : nat) (n' : nat) : (term93 n n') = (term94 n n').
Proof. exact (@lem3174770 (int_of_num n) (int_of_num n')). Qed.
Lemma lem3174772 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem3174773 (n : nat) (n' : nat) : (term135 n n') = (term137 n n').
Proof. exact (MK_COMB (@lem3174772) (@lem3174771 n n')). Qed.
Lemma lem3174775 (x : int) : (term30 x) = x.
Proof. exact (EQ_MP (@lem3174561 x) (@lem3174560 x)). Qed.
Lemma lem3174776 (n : nat) (n' : nat) : (term137 n n') = (term12 n n').
Proof. exact (@lem3174775 (term12 n n')). Qed.
Lemma lem3174777 (n : nat) (n' : nat) : (term135 n n') = (term12 n n').
Proof. exact (TRANS (@lem3174773 n n') (@lem3174776 n n')). Qed.
Lemma lem3174778 (n : nat) (n' : nat) : (term134 n n') = (term12 n n').
Proof. exact (TRANS (@lem3174768 n n') (@lem3174777 n n')). Qed.
Lemma lem3174779 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3174780 (x : real) (n : nat) (n' : nat) : (term123 x n n') = (term78 x n n').
Proof. exact (MK_COMB (@lem3174779 x) (@lem3174778 n n')). Qed.
Lemma lem3174781 (x : real) (n : nat) (n' : nat) : (term138 x n n') = (term138 x n n').
Proof. exact (eq_refl (term138 x n n')). Qed.
Lemma lem3174782 (x : real) (n : nat) (n' : nat) : ((term122 x n n') = (term123 x n n')) = ((term122 x n n') = (term78 x n n')).
Proof. exact (MK_COMB (@lem3174781 x n n') (@lem3174780 x n n')). Qed.
Lemma lem3174785 (x : real) (n : nat) : (term125 x n) = (term139 x n).
Proof. exact (fun_ext (fun n' : nat => @lem3174782 x n n')). Qed.
Lemma lem3174786 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174787 (x : real) (n : nat) : (term127 x n) = (term140 x n).
Proof. exact (MK_COMB (@lem3174786) (@lem3174785 x n)). Qed.
Lemma lem3174794 (x : real) (n : nat) : (term128 x n) = (term141 x n).
Proof. exact (MK_COMB (@lem3174757 x n) (@lem3174787 x n)). Qed.
Lemma lem3174797 (x : real) (n : nat) : (term61 x n) = (term141 x n).
Proof. exact (TRANS (@lem3174727 x n) (@lem3174794 x n)). Qed.
Lemma lem3174798 (x : real) : (term63 x) = (term142 x).
Proof. exact (fun_ext (fun n : nat => @lem3174797 x n)). Qed.
Lemma lem3174799 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174800 (x : real) : (term65 x) = (term143 x).
Proof. exact (MK_COMB (@lem3174799) (@lem3174798 x)). Qed.
Lemma lem3174807 (x : real) : (term66 x) = (term144 x).
Proof. exact (MK_COMB (@lem3174695 x) (@lem3174800 x)). Qed.
Lemma lem3174810 (x : real) : (term49 x) = (term144 x).
Proof. exact (TRANS (@lem3174609 x) (@lem3174807 x)). Qed.
Lemma lem3174811 : term145 = term146.
Proof. exact (fun_ext (fun x : real => @lem3174810 x)). Qed.
Lemma lem3174812 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3174813 : term147 = term148.
Proof. exact (MK_COMB (@lem3174812) (@lem3174811)). Qed.
Lemma lem3174820 : term148 = term147.
Proof. exact (SYM (@lem3174813)). Qed.
Lemma lem3174840 (x : real) (n : nat) : (term28 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3174558 x n) (@lem3174557 x n)). Qed.
Lemma lem3174841 (x : real) (n : nat) (n' : nat) : (term77 x n n') = (term149 x n n').
Proof. exact (@lem3174840 (term28 x n) n'). Qed.
Lemma lem3174843 (x : real) (n : nat) : (term28 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3174558 x n) (@lem3174557 x n)). Qed.
Lemma lem3174844 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem3174845 (x : real) (n : nat) : (term150 x n) = (term151 x n).
Proof. exact (MK_COMB (@lem3174844) (@lem3174843 x n)). Qed.
Lemma lem3174846 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem3174847 (x : real) (n : nat) (n' : nat) : (term149 x n n') = (term5 x n n').
Proof. exact (MK_COMB (@lem3174845 x n) (@lem3174846 n')). Qed.
Lemma lem3174848 (x : real) (n : nat) (n' : nat) : (term77 x n n') = (term5 x n n').
Proof. exact (TRANS (@lem3174841 x n n') (@lem3174847 x n n')). Qed.
Lemma lem3174849 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3174850 (x : real) (n : nat) (n' : nat) : (term152 x n n') = (term153 x n n').
Proof. exact (MK_COMB (@lem3174849) (@lem3174848 x n n')). Qed.
Lemma lem3174852 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (EQ_MP (@lem3174538 m n) (@lem3174537 m n)). Qed.
Lemma lem3174853 (n : nat) (n' : nat) : (term12 n n') = (term13 n n').
Proof. exact (@lem3174852 n n'). Qed.
Lemma lem3174854 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3174855 (x : real) (n : nat) (n' : nat) : (term78 x n n') = (term154 x n n').
Proof. exact (MK_COMB (@lem3174854 x) (@lem3174853 n n')). Qed.
Lemma lem3174857 (x : real) (n : nat) : (term28 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3174558 x n) (@lem3174557 x n)). Qed.
Lemma lem3174858 (x : real) (n : nat) (n' : nat) : (term154 x n n') = (term6 x n n').
Proof. exact (@lem3174857 x (Nat.mul n n')). Qed.
Lemma lem3174859 (x : real) (n : nat) (n' : nat) : (term78 x n n') = (term6 x n n').
Proof. exact (TRANS (@lem3174855 x n n') (@lem3174858 x n n')). Qed.
Lemma lem3174860 (x : real) (n : nat) (n' : nat) : ((term77 x n n') = (term78 x n n')) = ((term5 x n n') = (term6 x n n')).
Proof. exact (MK_COMB (@lem3174850 x n n') (@lem3174859 x n n')). Qed.
Lemma lem3174863 (x : real) (n : nat) : (term80 x n) = (term155 x n).
Proof. exact (fun_ext (fun n' : nat => @lem3174860 x n n')). Qed.
Lemma lem3174864 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174865 (x : real) (n : nat) : (term82 x n) = (term3 x n).
Proof. exact (MK_COMB (@lem3174864) (@lem3174863 x n)). Qed.
Lemma lem3174870 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3174871 (x : real) (n : nat) : (term84 x n) = (term156 x n).
Proof. exact (MK_COMB (@lem3174870) (@lem3174865 x n)). Qed.
Lemma lem3174879 (x : real) (n : nat) : (term23 x n) = (term17 x n).
Proof. exact (EQ_MP (@lem3174551 x n) (@lem3174550 x n)). Qed.
Lemma lem3174880 (x : real) (n : nat) (n' : nat) : (term86 x n n') = (term157 x n n').
Proof. exact (@lem3174879 (term28 x n) n'). Qed.
Lemma lem3174882 (x : real) (n : nat) : (term17 x n) = (term18 x n).
Proof. exact (EQ_MP (@lem3174544 x n) (@lem3174543 x n)). Qed.
Lemma lem3174883 (x : real) (n : nat) (n' : nat) : (term157 x n n') = (term158 x n n').
Proof. exact (@lem3174882 (term28 x n) n'). Qed.
Lemma lem3174884 (x : real) (n : nat) (n' : nat) : (term86 x n n') = (term158 x n n').
Proof. exact (TRANS (@lem3174880 x n n') (@lem3174883 x n n')). Qed.
Lemma lem3174886 (x : real) (n : nat) : (term28 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3174558 x n) (@lem3174557 x n)). Qed.
Lemma lem3174887 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3174888 (x : real) (n : nat) : (term159 x n) = (term17 x n).
Proof. exact (MK_COMB (@lem3174887) (@lem3174886 x n)). Qed.
Lemma lem3174890 (x : real) (n : nat) : (term17 x n) = (term18 x n).
Proof. exact (EQ_MP (@lem3174544 x n) (@lem3174543 x n)). Qed.
Lemma lem3174891 (x : real) (n : nat) : (term159 x n) = (term18 x n).
Proof. exact (TRANS (@lem3174888 x n) (@lem3174890 x n)). Qed.
Lemma lem3174892 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem3174893 (x : real) (n : nat) : (term160 x n) = (term161 x n).
Proof. exact (MK_COMB (@lem3174892) (@lem3174891 x n)). Qed.
Lemma lem3174894 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem3174895 (x : real) (n : nat) (n' : nat) : (term158 x n n') = (term162 x n n').
Proof. exact (MK_COMB (@lem3174893 x n) (@lem3174894 n')). Qed.
Lemma lem3174896 (x : real) (n : nat) (n' : nat) : (term86 x n n') = (term162 x n n').
Proof. exact (TRANS (@lem3174884 x n n') (@lem3174895 x n n')). Qed.
Lemma lem3174897 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3174898 (x : real) (n : nat) (n' : nat) : (term96 x n n') = (term163 x n n').
Proof. exact (MK_COMB (@lem3174897) (@lem3174896 x n n')). Qed.
Lemma lem3174900 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (EQ_MP (@lem3174538 m n) (@lem3174537 m n)). Qed.
Lemma lem3174901 (n : nat) (n' : nat) : (term12 n n') = (term13 n n').
Proof. exact (@lem3174900 n n'). Qed.
Lemma lem3174902 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem3174903 (n : nat) (n' : nat) : (term94 n n') = (term164 n n').
Proof. exact (MK_COMB (@lem3174902) (@lem3174901 n n')). Qed.
Lemma lem3174904 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3174905 (x : real) (n : nat) (n' : nat) : (term95 x n n') = (term165 x n n').
Proof. exact (MK_COMB (@lem3174904 x) (@lem3174903 n n')). Qed.
Lemma lem3174907 (x : real) (n : nat) : (term23 x n) = (term17 x n).
Proof. exact (EQ_MP (@lem3174551 x n) (@lem3174550 x n)). Qed.
Lemma lem3174908 (x : real) (n : nat) (n' : nat) : (term165 x n n') = (term166 x n n').
Proof. exact (@lem3174907 x (Nat.mul n n')). Qed.
Lemma lem3174910 (x : real) (n : nat) : (term17 x n) = (term18 x n).
Proof. exact (EQ_MP (@lem3174544 x n) (@lem3174543 x n)). Qed.
Lemma lem3174911 (x : real) (n : nat) (n' : nat) : (term166 x n n') = (term167 x n n').
Proof. exact (@lem3174910 x (Nat.mul n n')). Qed.
Lemma lem3174912 (x : real) (n : nat) (n' : nat) : (term165 x n n') = (term167 x n n').
Proof. exact (TRANS (@lem3174908 x n n') (@lem3174911 x n n')). Qed.
Lemma lem3174913 (x : real) (n : nat) (n' : nat) : (term95 x n n') = (term167 x n n').
Proof. exact (TRANS (@lem3174905 x n n') (@lem3174912 x n n')). Qed.
Lemma lem3174914 (x : real) (n : nat) (n' : nat) : ((term86 x n n') = (term95 x n n')) = ((term162 x n n') = (term167 x n n')).
Proof. exact (MK_COMB (@lem3174898 x n n') (@lem3174913 x n n')). Qed.
Lemma lem3174917 (x : real) (n : nat) : (term97 x n) = (term168 x n).
Proof. exact (fun_ext (fun n' : nat => @lem3174914 x n n')). Qed.
Lemma lem3174918 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174919 (x : real) (n : nat) : (term98 x n) = (term169 x n).
Proof. exact (MK_COMB (@lem3174918) (@lem3174917 x n)). Qed.
Lemma lem3174924 (x : real) (n : nat) : (term99 x n) = (term170 x n).
Proof. exact (MK_COMB (@lem3174871 x n) (@lem3174919 x n)). Qed.
Lemma lem3174927 (x : real) : (term100 x) = (term171 x).
Proof. exact (fun_ext (fun n : nat => @lem3174924 x n)). Qed.
Lemma lem3174928 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174929 (x : real) : (term101 x) = (term172 x).
Proof. exact (MK_COMB (@lem3174928) (@lem3174927 x)). Qed.
Lemma lem3174934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3174935 (x : real) : (term102 x) = (term173 x).
Proof. exact (MK_COMB (@lem3174934) (@lem3174929 x)). Qed.
Lemma lem3174949 (x : real) (n : nat) : (term28 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3174558 x n) (@lem3174557 x n)). Qed.
Lemma lem3174950 (x : real) (n : nat) (n' : nat) : (term113 x n n') = (term174 x n n').
Proof. exact (@lem3174949 (term23 x n) n'). Qed.
Lemma lem3174952 (x : real) (n : nat) : (term23 x n) = (term17 x n).
Proof. exact (EQ_MP (@lem3174551 x n) (@lem3174550 x n)). Qed.
Lemma lem3174954 (x : real) (n : nat) : (term17 x n) = (term18 x n).
Proof. exact (EQ_MP (@lem3174544 x n) (@lem3174543 x n)). Qed.
Lemma lem3174955 (x : real) (n : nat) : (term23 x n) = (term18 x n).
Proof. exact (TRANS (@lem3174952 x n) (@lem3174954 x n)). Qed.
Lemma lem3174956 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem3174957 (x : real) (n : nat) : (term175 x n) = (term161 x n).
Proof. exact (MK_COMB (@lem3174956) (@lem3174955 x n)). Qed.
Lemma lem3174958 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem3174959 (x : real) (n : nat) (n' : nat) : (term174 x n n') = (term162 x n n').
Proof. exact (MK_COMB (@lem3174957 x n) (@lem3174958 n')). Qed.
Lemma lem3174960 (x : real) (n : nat) (n' : nat) : (term113 x n n') = (term162 x n n').
Proof. exact (TRANS (@lem3174950 x n n') (@lem3174959 x n n')). Qed.
Lemma lem3174961 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3174962 (x : real) (n : nat) (n' : nat) : (term130 x n n') = (term163 x n n').
Proof. exact (MK_COMB (@lem3174961) (@lem3174960 x n n')). Qed.
Lemma lem3174964 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (EQ_MP (@lem3174538 m n) (@lem3174537 m n)). Qed.
Lemma lem3174965 (n : nat) (n' : nat) : (term12 n n') = (term13 n n').
Proof. exact (@lem3174964 n n'). Qed.
Lemma lem3174966 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem3174967 (n : nat) (n' : nat) : (term94 n n') = (term164 n n').
Proof. exact (MK_COMB (@lem3174966) (@lem3174965 n n')). Qed.
Lemma lem3174968 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3174969 (x : real) (n : nat) (n' : nat) : (term95 x n n') = (term165 x n n').
Proof. exact (MK_COMB (@lem3174968 x) (@lem3174967 n n')). Qed.
Lemma lem3174971 (x : real) (n : nat) : (term23 x n) = (term17 x n).
Proof. exact (EQ_MP (@lem3174551 x n) (@lem3174550 x n)). Qed.
Lemma lem3174972 (x : real) (n : nat) (n' : nat) : (term165 x n n') = (term166 x n n').
Proof. exact (@lem3174971 x (Nat.mul n n')). Qed.
Lemma lem3174974 (x : real) (n : nat) : (term17 x n) = (term18 x n).
Proof. exact (EQ_MP (@lem3174544 x n) (@lem3174543 x n)). Qed.
Lemma lem3174975 (x : real) (n : nat) (n' : nat) : (term166 x n n') = (term167 x n n').
Proof. exact (@lem3174974 x (Nat.mul n n')). Qed.
Lemma lem3174976 (x : real) (n : nat) (n' : nat) : (term165 x n n') = (term167 x n n').
Proof. exact (TRANS (@lem3174972 x n n') (@lem3174975 x n n')). Qed.
Lemma lem3174977 (x : real) (n : nat) (n' : nat) : (term95 x n n') = (term167 x n n').
Proof. exact (TRANS (@lem3174969 x n n') (@lem3174976 x n n')). Qed.
Lemma lem3174978 (x : real) (n : nat) (n' : nat) : ((term113 x n n') = (term95 x n n')) = ((term162 x n n') = (term167 x n n')).
Proof. exact (MK_COMB (@lem3174962 x n n') (@lem3174977 x n n')). Qed.
Lemma lem3174981 (x : real) (n : nat) : (term131 x n) = (term168 x n).
Proof. exact (fun_ext (fun n' : nat => @lem3174978 x n n')). Qed.
Lemma lem3174982 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174983 (x : real) (n : nat) : (term132 x n) = (term169 x n).
Proof. exact (MK_COMB (@lem3174982) (@lem3174981 x n)). Qed.
Lemma lem3174988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3174989 (x : real) (n : nat) : (term133 x n) = (term176 x n).
Proof. exact (MK_COMB (@lem3174988) (@lem3174983 x n)). Qed.
Lemma lem3174997 (x : real) (n : nat) : (term23 x n) = (term17 x n).
Proof. exact (EQ_MP (@lem3174551 x n) (@lem3174550 x n)). Qed.
Lemma lem3174998 (x : real) (n : nat) (n' : nat) : (term122 x n n') = (term177 x n n').
Proof. exact (@lem3174997 (term23 x n) n'). Qed.
Lemma lem3175000 (x : real) (n : nat) : (term17 x n) = (term18 x n).
Proof. exact (EQ_MP (@lem3174544 x n) (@lem3174543 x n)). Qed.
Lemma lem3175001 (x : real) (n : nat) (n' : nat) : (term177 x n n') = (term178 x n n').
Proof. exact (@lem3175000 (term23 x n) n'). Qed.
Lemma lem3175002 (x : real) (n : nat) (n' : nat) : (term122 x n n') = (term178 x n n').
Proof. exact (TRANS (@lem3174998 x n n') (@lem3175001 x n n')). Qed.
Lemma lem3175004 (x : real) (n : nat) : (term23 x n) = (term17 x n).
Proof. exact (EQ_MP (@lem3174551 x n) (@lem3174550 x n)). Qed.
Lemma lem3175006 (x : real) (n : nat) : (term17 x n) = (term18 x n).
Proof. exact (EQ_MP (@lem3174544 x n) (@lem3174543 x n)). Qed.
Lemma lem3175007 (x : real) (n : nat) : (term23 x n) = (term18 x n).
Proof. exact (TRANS (@lem3175004 x n) (@lem3175006 x n)). Qed.
Lemma lem3175008 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3175009 (x : real) (n : nat) : (term179 x n) = (term180 x n).
Proof. exact (MK_COMB (@lem3175008) (@lem3175007 x n)). Qed.
Lemma lem3175011 (x : real) (n : nat) : (term17 x n) = (term18 x n).
Proof. exact (EQ_MP (@lem3174544 x n) (@lem3174543 x n)). Qed.
Lemma lem3175012 (x : real) (n : nat) : (term180 x n) = (term181 x n).
Proof. exact (@lem3175011 (real_inv x) n). Qed.
Lemma lem3175014 (x : real) : (term8 x) = x.
Proof. exact (EQ_MP (@lem3174532 x) (@lem3174531 x)). Qed.
Lemma lem3175015 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem3175016 (x : real) : (term182 x) = (real_pow x).
Proof. exact (MK_COMB (@lem3175015) (@lem3175014 x)). Qed.
Lemma lem3175017 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3175018 (x : real) (n : nat) : (term181 x n) = (real_pow x n).
Proof. exact (MK_COMB (@lem3175016 x) (@lem3175017 n)). Qed.
Lemma lem3175019 (x : real) (n : nat) : (term180 x n) = (real_pow x n).
Proof. exact (TRANS (@lem3175012 x n) (@lem3175018 x n)). Qed.
Lemma lem3175020 (x : real) (n : nat) : (term179 x n) = (real_pow x n).
Proof. exact (TRANS (@lem3175009 x n) (@lem3175019 x n)). Qed.
Lemma lem3175021 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem3175022 (x : real) (n : nat) : (term183 x n) = (term151 x n).
Proof. exact (MK_COMB (@lem3175021) (@lem3175020 x n)). Qed.
Lemma lem3175023 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem3175024 (x : real) (n : nat) (n' : nat) : (term178 x n n') = (term5 x n n').
Proof. exact (MK_COMB (@lem3175022 x n) (@lem3175023 n')). Qed.
Lemma lem3175025 (x : real) (n : nat) (n' : nat) : (term122 x n n') = (term5 x n n').
Proof. exact (TRANS (@lem3175002 x n n') (@lem3175024 x n n')). Qed.
Lemma lem3175026 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3175027 (x : real) (n : nat) (n' : nat) : (term138 x n n') = (term153 x n n').
Proof. exact (MK_COMB (@lem3175026) (@lem3175025 x n n')). Qed.
Lemma lem3175029 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (EQ_MP (@lem3174538 m n) (@lem3174537 m n)). Qed.
Lemma lem3175030 (n : nat) (n' : nat) : (term12 n n') = (term13 n n').
Proof. exact (@lem3175029 n n'). Qed.
Lemma lem3175031 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3175032 (x : real) (n : nat) (n' : nat) : (term78 x n n') = (term154 x n n').
Proof. exact (MK_COMB (@lem3175031 x) (@lem3175030 n n')). Qed.
Lemma lem3175034 (x : real) (n : nat) : (term28 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3174558 x n) (@lem3174557 x n)). Qed.
Lemma lem3175035 (x : real) (n : nat) (n' : nat) : (term154 x n n') = (term6 x n n').
Proof. exact (@lem3175034 x (Nat.mul n n')). Qed.
Lemma lem3175036 (x : real) (n : nat) (n' : nat) : (term78 x n n') = (term6 x n n').
Proof. exact (TRANS (@lem3175032 x n n') (@lem3175035 x n n')). Qed.
Lemma lem3175037 (x : real) (n : nat) (n' : nat) : ((term122 x n n') = (term78 x n n')) = ((term5 x n n') = (term6 x n n')).
Proof. exact (MK_COMB (@lem3175027 x n n') (@lem3175036 x n n')). Qed.
Lemma lem3175040 (x : real) (n : nat) : (term139 x n) = (term155 x n).
Proof. exact (fun_ext (fun n' : nat => @lem3175037 x n n')). Qed.
Lemma lem3175041 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3175042 (x : real) (n : nat) : (term140 x n) = (term3 x n).
Proof. exact (MK_COMB (@lem3175041) (@lem3175040 x n)). Qed.
Lemma lem3175047 (x : real) (n : nat) : (term141 x n) = (term184 x n).
Proof. exact (MK_COMB (@lem3174989 x n) (@lem3175042 x n)). Qed.
Lemma lem3175050 (x : real) : (term142 x) = (term185 x).
Proof. exact (fun_ext (fun n : nat => @lem3175047 x n)). Qed.
Lemma lem3175051 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3175052 (x : real) : (term143 x) = (term186 x).
Proof. exact (MK_COMB (@lem3175051) (@lem3175050 x)). Qed.
Lemma lem3175057 (x : real) : (term144 x) = (term187 x).
Proof. exact (MK_COMB (@lem3174935 x) (@lem3175052 x)). Qed.
Lemma lem3175060 : term146 = term188.
Proof. exact (fun_ext (fun x : real => @lem3175057 x)). Qed.
Lemma lem3175061 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3175062 : term148 = term189.
Proof. exact (MK_COMB (@lem3175061) (@lem3175060)). Qed.
Lemma lem3175067 : term189 = term148.
Proof. exact (SYM (@lem3175062)). Qed.
Lemma lem3175087 (x : real) (m : nat) (n : nat) : (term5 x m n) = (term6 x m n).
Proof. exact (EQ_MP (@lem3174529 x m n) (@lem3174528 x m n)). Qed.
Lemma lem3175088 (x : real) (n : nat) (n' : nat) : (term5 x n n') = (term6 x n n').
Proof. exact (@lem3175087 x n n'). Qed.
Lemma lem3175089 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3175090 (x : real) (n : nat) (n' : nat) : (term153 x n n') = (term190 x n n').
Proof. exact (MK_COMB (@lem3175089) (@lem3175088 x n n')). Qed.
Lemma lem3175091 (x : real) (n : nat) (n' : nat) : (term6 x n n') = (term6 x n n').
Proof. exact (eq_refl (term6 x n n')). Qed.
Lemma lem3175092 (x : real) (n : nat) (n' : nat) : ((term5 x n n') = (term6 x n n')) = ((term6 x n n') = (term6 x n n')).
Proof. exact (MK_COMB (@lem3175090 x n n') (@lem3175091 x n n')). Qed.
Lemma lem3175094 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3175095 (x : real) : (x = x) = True.
Proof. exact (@lem3175094 real x). Qed.
Lemma lem3175096 (x : real) (n : nat) (n' : nat) : ((term6 x n n') = (term6 x n n')) = True.
Proof. exact (@lem3175095 (term6 x n n')). Qed.
Lemma lem3175097 (x : real) (n : nat) (n' : nat) : ((term5 x n n') = (term6 x n n')) = True.
Proof. exact (TRANS (@lem3175092 x n n') (@lem3175096 x n n')). Qed.
Lemma lem3175098 (x : real) (n : nat) : (term155 x n) = term191.
Proof. exact (fun_ext (fun n' : nat => @lem3175097 x n n')). Qed.
Lemma lem3175099 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3175100 (x : real) (n : nat) : (term3 x n) = term192.
Proof. exact (MK_COMB (@lem3175099) (@lem3175098 x n)). Qed.
Lemma lem3175102 {A : Type'} (t : Prop) : (term193 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3175103 (t : Prop) : (term194 t) = t.
Proof. exact (@lem3175102 nat t). Qed.
Lemma lem3175104 : term192 = True.
Proof. exact (@lem3175103 True). Qed.
Lemma lem3175105 (x : real) (n : nat) : (term3 x n) = True.
Proof. exact (TRANS (@lem3175100 x n) (@lem3175104)). Qed.
Lemma lem3175106 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3175107 (x : real) (n : nat) : (term156 x n) = (and True).
Proof. exact (MK_COMB (@lem3175106) (@lem3175105 x n)). Qed.
Lemma lem3175115 (x : real) (m : nat) (n : nat) : (term5 x m n) = (term6 x m n).
Proof. exact (EQ_MP (@lem3174529 x m n) (@lem3174528 x m n)). Qed.
Lemma lem3175116 (x : real) (n : nat) (n' : nat) : (term162 x n n') = (term167 x n n').
Proof. exact (@lem3175115 (real_inv x) n n'). Qed.
Lemma lem3175117 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3175118 (x : real) (n : nat) (n' : nat) : (term163 x n n') = (term195 x n n').
Proof. exact (MK_COMB (@lem3175117) (@lem3175116 x n n')). Qed.
Lemma lem3175119 (x : real) (n : nat) (n' : nat) : (term167 x n n') = (term167 x n n').
Proof. exact (eq_refl (term167 x n n')). Qed.
Lemma lem3175120 (x : real) (n : nat) (n' : nat) : ((term162 x n n') = (term167 x n n')) = ((term167 x n n') = (term167 x n n')).
Proof. exact (MK_COMB (@lem3175118 x n n') (@lem3175119 x n n')). Qed.
Lemma lem3175122 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3175123 (x : real) : (x = x) = True.
Proof. exact (@lem3175122 real x). Qed.
Lemma lem3175124 (x : real) (n : nat) (n' : nat) : ((term167 x n n') = (term167 x n n')) = True.
Proof. exact (@lem3175123 (term167 x n n')). Qed.
Lemma lem3175125 (x : real) (n : nat) (n' : nat) : ((term162 x n n') = (term167 x n n')) = True.
Proof. exact (TRANS (@lem3175120 x n n') (@lem3175124 x n n')). Qed.
Lemma lem3175126 (x : real) (n : nat) : (term168 x n) = term191.
Proof. exact (fun_ext (fun n' : nat => @lem3175125 x n n')). Qed.
Lemma lem3175127 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3175128 (x : real) (n : nat) : (term169 x n) = term192.
Proof. exact (MK_COMB (@lem3175127) (@lem3175126 x n)). Qed.
Lemma lem3175130 {A : Type'} (t : Prop) : (term193 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3175131 (t : Prop) : (term194 t) = t.
Proof. exact (@lem3175130 nat t). Qed.
Lemma lem3175132 : term192 = True.
Proof. exact (@lem3175131 True). Qed.
Lemma lem3175133 (x : real) (n : nat) : (term169 x n) = True.
Proof. exact (TRANS (@lem3175128 x n) (@lem3175132)). Qed.
Lemma lem3175134 (x : real) (n : nat) : (term170 x n) = (True /\ True).
Proof. exact (MK_COMB (@lem3175107 x n) (@lem3175133 x n)). Qed.
Lemma lem3175136 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3175137 : (True /\ True) = True.
Proof. exact (@lem3175136 True). Qed.
Lemma lem3175138 (x : real) (n : nat) : (term170 x n) = True.
Proof. exact (TRANS (@lem3175134 x n) (@lem3175137)). Qed.
Lemma lem3175139 (x : real) : (term171 x) = term191.
Proof. exact (fun_ext (fun n : nat => @lem3175138 x n)). Qed.
Lemma lem3175140 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3175141 (x : real) : (term172 x) = term192.
Proof. exact (MK_COMB (@lem3175140) (@lem3175139 x)). Qed.
Lemma lem3175143 {A : Type'} (t : Prop) : (term193 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3175144 (t : Prop) : (term194 t) = t.
Proof. exact (@lem3175143 nat t). Qed.
Lemma lem3175145 : term192 = True.
Proof. exact (@lem3175144 True). Qed.
Lemma lem3175146 (x : real) : (term172 x) = True.
Proof. exact (TRANS (@lem3175141 x) (@lem3175145)). Qed.
Lemma lem3175147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3175148 (x : real) : (term173 x) = (and True).
Proof. exact (MK_COMB (@lem3175147) (@lem3175146 x)). Qed.
Lemma lem3175162 (x : real) (m : nat) (n : nat) : (term5 x m n) = (term6 x m n).
Proof. exact (EQ_MP (@lem3174529 x m n) (@lem3174528 x m n)). Qed.
Lemma lem3175163 (x : real) (n : nat) (n' : nat) : (term162 x n n') = (term167 x n n').
Proof. exact (@lem3175162 (real_inv x) n n'). Qed.
Lemma lem3175164 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3175165 (x : real) (n : nat) (n' : nat) : (term163 x n n') = (term195 x n n').
Proof. exact (MK_COMB (@lem3175164) (@lem3175163 x n n')). Qed.
Lemma lem3175166 (x : real) (n : nat) (n' : nat) : (term167 x n n') = (term167 x n n').
Proof. exact (eq_refl (term167 x n n')). Qed.
Lemma lem3175167 (x : real) (n : nat) (n' : nat) : ((term162 x n n') = (term167 x n n')) = ((term167 x n n') = (term167 x n n')).
Proof. exact (MK_COMB (@lem3175165 x n n') (@lem3175166 x n n')). Qed.
Lemma lem3175169 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3175170 (x : real) : (x = x) = True.
Proof. exact (@lem3175169 real x). Qed.
Lemma lem3175171 (x : real) (n : nat) (n' : nat) : ((term167 x n n') = (term167 x n n')) = True.
Proof. exact (@lem3175170 (term167 x n n')). Qed.
Lemma lem3175172 (x : real) (n : nat) (n' : nat) : ((term162 x n n') = (term167 x n n')) = True.
Proof. exact (TRANS (@lem3175167 x n n') (@lem3175171 x n n')). Qed.
Lemma lem3175173 (x : real) (n : nat) : (term168 x n) = term191.
Proof. exact (fun_ext (fun n' : nat => @lem3175172 x n n')). Qed.
Lemma lem3175174 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3175175 (x : real) (n : nat) : (term169 x n) = term192.
Proof. exact (MK_COMB (@lem3175174) (@lem3175173 x n)). Qed.
Lemma lem3175177 {A : Type'} (t : Prop) : (term193 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3175178 (t : Prop) : (term194 t) = t.
Proof. exact (@lem3175177 nat t). Qed.
Lemma lem3175179 : term192 = True.
Proof. exact (@lem3175178 True). Qed.
Lemma lem3175180 (x : real) (n : nat) : (term169 x n) = True.
Proof. exact (TRANS (@lem3175175 x n) (@lem3175179)). Qed.
Lemma lem3175181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3175182 (x : real) (n : nat) : (term176 x n) = (and True).
Proof. exact (MK_COMB (@lem3175181) (@lem3175180 x n)). Qed.
Lemma lem3175190 (x : real) (m : nat) (n : nat) : (term5 x m n) = (term6 x m n).
Proof. exact (EQ_MP (@lem3174529 x m n) (@lem3174528 x m n)). Qed.
Lemma lem3175191 (x : real) (n : nat) (n' : nat) : (term5 x n n') = (term6 x n n').
Proof. exact (@lem3175190 x n n'). Qed.
Lemma lem3175192 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3175193 (x : real) (n : nat) (n' : nat) : (term153 x n n') = (term190 x n n').
Proof. exact (MK_COMB (@lem3175192) (@lem3175191 x n n')). Qed.
Lemma lem3175194 (x : real) (n : nat) (n' : nat) : (term6 x n n') = (term6 x n n').
Proof. exact (eq_refl (term6 x n n')). Qed.
Lemma lem3175195 (x : real) (n : nat) (n' : nat) : ((term5 x n n') = (term6 x n n')) = ((term6 x n n') = (term6 x n n')).
Proof. exact (MK_COMB (@lem3175193 x n n') (@lem3175194 x n n')). Qed.
Lemma lem3175197 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3175198 (x : real) : (x = x) = True.
Proof. exact (@lem3175197 real x). Qed.
Lemma lem3175199 (x : real) (n : nat) (n' : nat) : ((term6 x n n') = (term6 x n n')) = True.
Proof. exact (@lem3175198 (term6 x n n')). Qed.
Lemma lem3175200 (x : real) (n : nat) (n' : nat) : ((term5 x n n') = (term6 x n n')) = True.
Proof. exact (TRANS (@lem3175195 x n n') (@lem3175199 x n n')). Qed.
Lemma lem3175201 (x : real) (n : nat) : (term155 x n) = term191.
Proof. exact (fun_ext (fun n' : nat => @lem3175200 x n n')). Qed.
Lemma lem3175202 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3175203 (x : real) (n : nat) : (term3 x n) = term192.
Proof. exact (MK_COMB (@lem3175202) (@lem3175201 x n)). Qed.
Lemma lem3175205 {A : Type'} (t : Prop) : (term193 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3175206 (t : Prop) : (term194 t) = t.
Proof. exact (@lem3175205 nat t). Qed.
Lemma lem3175207 : term192 = True.
Proof. exact (@lem3175206 True). Qed.
Lemma lem3175208 (x : real) (n : nat) : (term3 x n) = True.
Proof. exact (TRANS (@lem3175203 x n) (@lem3175207)). Qed.
Lemma lem3175209 (x : real) (n : nat) : (term184 x n) = (True /\ True).
Proof. exact (MK_COMB (@lem3175182 x n) (@lem3175208 x n)). Qed.
Lemma lem3175211 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3175212 : (True /\ True) = True.
Proof. exact (@lem3175211 True). Qed.
Lemma lem3175213 (x : real) (n : nat) : (term184 x n) = True.
Proof. exact (TRANS (@lem3175209 x n) (@lem3175212)). Qed.
Lemma lem3175214 (x : real) : (term185 x) = term191.
Proof. exact (fun_ext (fun n : nat => @lem3175213 x n)). Qed.
Lemma lem3175215 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3175216 (x : real) : (term186 x) = term192.
Proof. exact (MK_COMB (@lem3175215) (@lem3175214 x)). Qed.
Lemma lem3175218 {A : Type'} (t : Prop) : (term193 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3175219 (t : Prop) : (term194 t) = t.
Proof. exact (@lem3175218 nat t). Qed.
Lemma lem3175220 : term192 = True.
Proof. exact (@lem3175219 True). Qed.
Lemma lem3175221 (x : real) : (term186 x) = True.
Proof. exact (TRANS (@lem3175216 x) (@lem3175220)). Qed.
Lemma lem3175222 (x : real) : (term187 x) = (True /\ True).
Proof. exact (MK_COMB (@lem3175148 x) (@lem3175221 x)). Qed.
Lemma lem3175224 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3175225 : (True /\ True) = True.
Proof. exact (@lem3175224 True). Qed.
Lemma lem3175226 (x : real) : (term187 x) = True.
Proof. exact (TRANS (@lem3175222 x) (@lem3175225)). Qed.
Lemma lem3175227 : term188 = term196.
Proof. exact (fun_ext (fun x : real => @lem3175226 x)). Qed.
Lemma lem3175228 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3175229 : term189 = term197.
Proof. exact (MK_COMB (@lem3175228) (@lem3175227)). Qed.
Lemma lem3175231 {A : Type'} (t : Prop) : (term193 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3175232 (t : Prop) : (term198 t) = t.
Proof. exact (@lem3175231 real t). Qed.
Lemma lem3175233 : term197 = True.
Proof. exact (@lem3175232 True). Qed.
Lemma lem3175234 : term189 = True.
Proof. exact (TRANS (@lem3175229) (@lem3175233)). Qed.
Lemma lem3175235 : True = term189.
Proof. exact (SYM (@lem3175234)). Qed.
Lemma lem3175236 : term189.
Proof. exact (EQ_MP (@lem3175235) (@lem0)). Qed.
Lemma lem3175237 : term148.
Proof. exact (EQ_MP (@lem3175067) (@lem3175236)). Qed.
Lemma lem3175238 : term147.
Proof. exact (EQ_MP (@lem3174820) (@lem3175237)). Qed.
