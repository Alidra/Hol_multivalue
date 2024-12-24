Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LDISTRIB_term_abbrevs.
Require Import NADD_ADD_spec.
Require Import NADD_ADDITIVE_spec.
Require Import NADD_MUL_spec.
Require Import nadd_eq_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1278628 (x : nadd) : term0 x.
Proof. exact (@lem1266353 x). Qed.
Lemma lem1278629 (x : nadd) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1278630 (x : nadd) : term1 x.
Proof. exact (EQ_MP (@lem1278629 x) (@lem1278628 x)). Qed.
Lemma lem1278631 (x : nadd) (B : nat) (h1 : term2 x B) : term2 x B.
Proof. exact (h1). Qed.
Lemma lem1278632 (x : nadd) : term3 x.
Proof. exact (@lem1277879 x). Qed.
Lemma lem1278633 (x : nadd) : (term3 x) = (term4 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1278634 (x : nadd) : term4 x.
Proof. exact (EQ_MP (@lem1278633 x) (@lem1278632 x)). Qed.
Lemma lem1278635 (x : nadd) (y : nadd) : term5 x y.
Proof. exact (@lem1278634 x y). Qed.
Lemma lem1278636 (x : nadd) (y : nadd) : (term5 x y) = ((term6 x y) = (term7 x y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1278638 (x : nadd) : term8 x.
Proof. exact (@lem1274104 x). Qed.
Lemma lem1278639 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1278640 (x : nadd) : term9 x.
Proof. exact (EQ_MP (@lem1278639 x) (@lem1278638 x)). Qed.
Lemma lem1278641 (x : nadd) (y : nadd) : term10 x y.
Proof. exact (@lem1278640 x y). Qed.
Lemma lem1278642 (x : nadd) (y : nadd) : (term10 x y) = ((term11 x y) = (term12 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1278644 (x : nadd) : term13 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1278645 (x : nadd) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1278646 (x : nadd) : term14 x.
Proof. exact (EQ_MP (@lem1278645 x) (@lem1278644 x)). Qed.
Lemma lem1278647 (x : nadd) (y : nadd) : term15 x y.
Proof. exact (@lem1278646 x y). Qed.
Lemma lem1278648 (x : nadd) (y : nadd) : (term15 x y) = ((nadd_eq x y) = (term16 x y)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1278651 (x : nadd) (y : nadd) : (nadd_eq x y) = (term16 x y).
Proof. exact (EQ_MP (@lem1278648 x y) (@lem1278647 x y)). Qed.
Lemma lem1278652 (y : nadd) (x : nadd) (z : nadd) : (term17 y x z) = (term18 y x z).
Proof. exact (@lem1278651 (term19 x y z) (term20 y x z)). Qed.
Lemma lem1278661 (y : nadd) (x : nadd) (z : nadd) : (term18 y x z) = (term17 y x z).
Proof. exact (SYM (@lem1278652 y x z)). Qed.
Lemma lem1278671 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1278636 x y) (@lem1278635 x y)). Qed.
Lemma lem1278672 (x : nadd) (y : nadd) (z : nadd) : (term21 x y z) = (term22 x y z).
Proof. exact (@lem1278671 x (nadd_add y z)). Qed.
Lemma lem1278674 (x : nadd) (y : nadd) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1278642 x y) (@lem1278641 x y)). Qed.
Lemma lem1278675 (y : nadd) (z : nadd) : (term11 y z) = (term12 y z).
Proof. exact (@lem1278674 y z). Qed.
Lemma lem1278676 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278677 (y : nadd) (z : nadd) (n : nat) : (term23 y z n) = (term24 y z n).
Proof. exact (MK_COMB (@lem1278675 y z) (@lem1278676 n)). Qed.
Lemma lem1278679 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1278680 (f : nat -> nat) (y : nat) : (term26 f y) = (f y).
Proof. exact (@lem1278679 nat nat f y). Qed.
Lemma lem1278681 (y : nadd) (z : nadd) (n : nat) : (term27 y z n) = (term24 y z n).
Proof. exact (@lem1278680 (term12 y z) n). Qed.
Lemma lem1278682 (y : nadd) (z : nadd) (n : nat) : (term24 y z n) = (term28 y z n).
Proof. exact (eq_refl (term24 y z n)). Qed.
Lemma lem1278683 (y : nadd) (z : nadd) : (term29 y z) = (term12 y z).
Proof. exact (fun_ext (fun n : nat => @lem1278682 y z n)). Qed.
Lemma lem1278684 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278685 (y : nadd) (z : nadd) (n : nat) : (term27 y z n) = (term24 y z n).
Proof. exact (MK_COMB (@lem1278683 y z) (@lem1278684 n)). Qed.
Lemma lem1278686 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1278687 (y : nadd) (z : nadd) (n : nat) : (term30 y z n) = (term31 y z n).
Proof. exact (MK_COMB (@lem1278686) (@lem1278685 y z n)). Qed.
Lemma lem1278688 (y : nadd) (z : nadd) (n : nat) : (term24 y z n) = (term28 y z n).
Proof. exact (eq_refl (term24 y z n)). Qed.
Lemma lem1278689 (y : nadd) (z : nadd) (n : nat) : ((term27 y z n) = (term24 y z n)) = ((term24 y z n) = (term28 y z n)).
Proof. exact (MK_COMB (@lem1278687 y z n) (@lem1278688 y z n)). Qed.
Lemma lem1278690 (y : nadd) (z : nadd) (n : nat) : (term24 y z n) = (term28 y z n).
Proof. exact (EQ_MP (@lem1278689 y z n) (@lem1278681 y z n)). Qed.
Lemma lem1278691 (y : nadd) (z : nadd) (n : nat) : (term23 y z n) = (term28 y z n).
Proof. exact (TRANS (@lem1278677 y z n) (@lem1278690 y z n)). Qed.
Lemma lem1278692 (x : nadd) : (dest_nadd x) = (dest_nadd x).
Proof. exact (eq_refl (dest_nadd x)). Qed.
Lemma lem1278693 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term32 x y z n) = (term33 x y z n).
Proof. exact (MK_COMB (@lem1278692 x) (@lem1278691 y z n)). Qed.
Lemma lem1278694 (x : nadd) (y : nadd) (z : nadd) : (term22 x y z) = (term34 x y z).
Proof. exact (fun_ext (fun n : nat => @lem1278693 x y z n)). Qed.
Lemma lem1278695 (x : nadd) (y : nadd) (z : nadd) : (term21 x y z) = (term34 x y z).
Proof. exact (TRANS (@lem1278672 x y z) (@lem1278694 x y z)). Qed.
Lemma lem1278696 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278697 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term35 x y z n) = (term36 x y z n).
Proof. exact (MK_COMB (@lem1278695 x y z) (@lem1278696 n)). Qed.
Lemma lem1278699 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1278700 (f : nat -> nat) (y : nat) : (term26 f y) = (f y).
Proof. exact (@lem1278699 nat nat f y). Qed.
Lemma lem1278701 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term37 x y z n) = (term36 x y z n).
Proof. exact (@lem1278700 (term34 x y z) n). Qed.
Lemma lem1278702 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term36 x y z n) = (term33 x y z n).
Proof. exact (eq_refl (term36 x y z n)). Qed.
Lemma lem1278703 (x : nadd) (y : nadd) (z : nadd) : (term38 x y z) = (term34 x y z).
Proof. exact (fun_ext (fun n : nat => @lem1278702 x y z n)). Qed.
Lemma lem1278704 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278705 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term37 x y z n) = (term36 x y z n).
Proof. exact (MK_COMB (@lem1278703 x y z) (@lem1278704 n)). Qed.
Lemma lem1278706 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1278707 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term39 x y z n) = (term40 x y z n).
Proof. exact (MK_COMB (@lem1278706) (@lem1278705 x y z n)). Qed.
Lemma lem1278708 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term36 x y z n) = (term33 x y z n).
Proof. exact (eq_refl (term36 x y z n)). Qed.
Lemma lem1278709 (x : nadd) (y : nadd) (z : nadd) (n : nat) : ((term37 x y z n) = (term36 x y z n)) = ((term36 x y z n) = (term33 x y z n)).
Proof. exact (MK_COMB (@lem1278707 x y z n) (@lem1278708 x y z n)). Qed.
Lemma lem1278710 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term36 x y z n) = (term33 x y z n).
Proof. exact (EQ_MP (@lem1278709 x y z n) (@lem1278701 x y z n)). Qed.
Lemma lem1278711 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term35 x y z n) = (term33 x y z n).
Proof. exact (TRANS (@lem1278697 x y z n) (@lem1278710 x y z n)). Qed.
Lemma lem1278712 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1278713 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term41 x y z n) = (term42 x y z n).
Proof. exact (MK_COMB (@lem1278712) (@lem1278711 x y z n)). Qed.
Lemma lem1278715 (x : nadd) (y : nadd) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1278642 x y) (@lem1278641 x y)). Qed.
Lemma lem1278716 (y : nadd) (x : nadd) (z : nadd) : (term43 y x z) = (term44 y x z).
Proof. exact (@lem1278715 (nadd_mul x y) (nadd_mul x z)). Qed.
Lemma lem1278718 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1278636 x y) (@lem1278635 x y)). Qed.
Lemma lem1278719 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278720 (x : nadd) (y : nadd) (n : nat) : (term45 x y n) = (term46 x y n).
Proof. exact (MK_COMB (@lem1278718 x y) (@lem1278719 n)). Qed.
Lemma lem1278722 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1278723 (f : nat -> nat) (y : nat) : (term26 f y) = (f y).
Proof. exact (@lem1278722 nat nat f y). Qed.
Lemma lem1278724 (x : nadd) (y : nadd) (n : nat) : (term47 x y n) = (term46 x y n).
Proof. exact (@lem1278723 (term7 x y) n). Qed.
Lemma lem1278725 (x : nadd) (y : nadd) (n : nat) : (term46 x y n) = (term48 x y n).
Proof. exact (eq_refl (term46 x y n)). Qed.
Lemma lem1278726 (x : nadd) (y : nadd) : (term49 x y) = (term7 x y).
Proof. exact (fun_ext (fun n : nat => @lem1278725 x y n)). Qed.
Lemma lem1278727 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278728 (x : nadd) (y : nadd) (n : nat) : (term47 x y n) = (term46 x y n).
Proof. exact (MK_COMB (@lem1278726 x y) (@lem1278727 n)). Qed.
Lemma lem1278729 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1278730 (x : nadd) (y : nadd) (n : nat) : (term50 x y n) = (term51 x y n).
Proof. exact (MK_COMB (@lem1278729) (@lem1278728 x y n)). Qed.
Lemma lem1278731 (x : nadd) (y : nadd) (n : nat) : (term46 x y n) = (term48 x y n).
Proof. exact (eq_refl (term46 x y n)). Qed.
Lemma lem1278732 (x : nadd) (y : nadd) (n : nat) : ((term47 x y n) = (term46 x y n)) = ((term46 x y n) = (term48 x y n)).
Proof. exact (MK_COMB (@lem1278730 x y n) (@lem1278731 x y n)). Qed.
Lemma lem1278733 (x : nadd) (y : nadd) (n : nat) : (term46 x y n) = (term48 x y n).
Proof. exact (EQ_MP (@lem1278732 x y n) (@lem1278724 x y n)). Qed.
Lemma lem1278734 (x : nadd) (y : nadd) (n : nat) : (term45 x y n) = (term48 x y n).
Proof. exact (TRANS (@lem1278720 x y n) (@lem1278733 x y n)). Qed.
Lemma lem1278735 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1278736 (x : nadd) (y : nadd) (n : nat) : (term52 x y n) = (term53 x y n).
Proof. exact (MK_COMB (@lem1278735) (@lem1278734 x y n)). Qed.
Lemma lem1278738 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1278636 x y) (@lem1278635 x y)). Qed.
Lemma lem1278739 (x : nadd) (z : nadd) : (term6 x z) = (term7 x z).
Proof. exact (@lem1278738 x z). Qed.
Lemma lem1278740 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278741 (x : nadd) (z : nadd) (n : nat) : (term45 x z n) = (term46 x z n).
Proof. exact (MK_COMB (@lem1278739 x z) (@lem1278740 n)). Qed.
Lemma lem1278743 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1278744 (f : nat -> nat) (y : nat) : (term26 f y) = (f y).
Proof. exact (@lem1278743 nat nat f y). Qed.
Lemma lem1278745 (x : nadd) (z : nadd) (n : nat) : (term47 x z n) = (term46 x z n).
Proof. exact (@lem1278744 (term7 x z) n). Qed.
Lemma lem1278746 (x : nadd) (z : nadd) (n : nat) : (term46 x z n) = (term48 x z n).
Proof. exact (eq_refl (term46 x z n)). Qed.
Lemma lem1278747 (x : nadd) (z : nadd) : (term49 x z) = (term7 x z).
Proof. exact (fun_ext (fun n : nat => @lem1278746 x z n)). Qed.
Lemma lem1278748 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278749 (x : nadd) (z : nadd) (n : nat) : (term47 x z n) = (term46 x z n).
Proof. exact (MK_COMB (@lem1278747 x z) (@lem1278748 n)). Qed.
Lemma lem1278750 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1278751 (x : nadd) (z : nadd) (n : nat) : (term50 x z n) = (term51 x z n).
Proof. exact (MK_COMB (@lem1278750) (@lem1278749 x z n)). Qed.
Lemma lem1278752 (x : nadd) (z : nadd) (n : nat) : (term46 x z n) = (term48 x z n).
Proof. exact (eq_refl (term46 x z n)). Qed.
Lemma lem1278753 (x : nadd) (z : nadd) (n : nat) : ((term47 x z n) = (term46 x z n)) = ((term46 x z n) = (term48 x z n)).
Proof. exact (MK_COMB (@lem1278751 x z n) (@lem1278752 x z n)). Qed.
Lemma lem1278754 (x : nadd) (z : nadd) (n : nat) : (term46 x z n) = (term48 x z n).
Proof. exact (EQ_MP (@lem1278753 x z n) (@lem1278745 x z n)). Qed.
Lemma lem1278755 (x : nadd) (z : nadd) (n : nat) : (term45 x z n) = (term48 x z n).
Proof. exact (TRANS (@lem1278741 x z n) (@lem1278754 x z n)). Qed.
Lemma lem1278756 (y : nadd) (x : nadd) (z : nadd) (n : nat) : (term54 y x z n) = (term55 y x z n).
Proof. exact (MK_COMB (@lem1278736 x y n) (@lem1278755 x z n)). Qed.
Lemma lem1278757 (y : nadd) (x : nadd) (z : nadd) : (term44 y x z) = (term56 y x z).
Proof. exact (fun_ext (fun n : nat => @lem1278756 y x z n)). Qed.
Lemma lem1278758 (y : nadd) (x : nadd) (z : nadd) : (term43 y x z) = (term56 y x z).
Proof. exact (TRANS (@lem1278716 y x z) (@lem1278757 y x z)). Qed.
Lemma lem1278759 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278760 (y : nadd) (x : nadd) (z : nadd) (n : nat) : (term57 y x z n) = (term58 y x z n).
Proof. exact (MK_COMB (@lem1278758 y x z) (@lem1278759 n)). Qed.
Lemma lem1278762 {A B : Type'} (f : A -> B) (y : A) : (term25 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1278763 (f : nat -> nat) (y : nat) : (term26 f y) = (f y).
Proof. exact (@lem1278762 nat nat f y). Qed.
Lemma lem1278764 (y : nadd) (x : nadd) (z : nadd) (n : nat) : (term59 y x z n) = (term58 y x z n).
Proof. exact (@lem1278763 (term56 y x z) n). Qed.
Lemma lem1278765 (y : nadd) (x : nadd) (z : nadd) (n : nat) : (term58 y x z n) = (term55 y x z n).
Proof. exact (eq_refl (term58 y x z n)). Qed.
Lemma lem1278766 (y : nadd) (x : nadd) (z : nadd) : (term60 y x z) = (term56 y x z).
Proof. exact (fun_ext (fun n : nat => @lem1278765 y x z n)). Qed.
Lemma lem1278767 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278768 (y : nadd) (x : nadd) (z : nadd) (n : nat) : (term59 y x z n) = (term58 y x z n).
Proof. exact (MK_COMB (@lem1278766 y x z) (@lem1278767 n)). Qed.
Lemma lem1278769 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1278770 (y : nadd) (x : nadd) (z : nadd) (n : nat) : (term61 y x z n) = (term62 y x z n).
Proof. exact (MK_COMB (@lem1278769) (@lem1278768 y x z n)). Qed.
Lemma lem1278771 (y : nadd) (x : nadd) (z : nadd) (n : nat) : (term58 y x z n) = (term55 y x z n).
Proof. exact (eq_refl (term58 y x z n)). Qed.
Lemma lem1278772 (y : nadd) (x : nadd) (z : nadd) (n : nat) : ((term59 y x z n) = (term58 y x z n)) = ((term58 y x z n) = (term55 y x z n)).
Proof. exact (MK_COMB (@lem1278770 y x z n) (@lem1278771 y x z n)). Qed.
Lemma lem1278773 (y : nadd) (x : nadd) (z : nadd) (n : nat) : (term58 y x z n) = (term55 y x z n).
Proof. exact (EQ_MP (@lem1278772 y x z n) (@lem1278764 y x z n)). Qed.
Lemma lem1278774 (y : nadd) (x : nadd) (z : nadd) (n : nat) : (term57 y x z n) = (term55 y x z n).
Proof. exact (TRANS (@lem1278760 y x z n) (@lem1278773 y x z n)). Qed.
Lemma lem1278775 (y : nadd) (x : nadd) (z : nadd) (n : nat) : (term63 y x z n) = (term64 y x z n).
Proof. exact (MK_COMB (@lem1278713 x y z n) (@lem1278774 y x z n)). Qed.
Lemma lem1278776 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1278777 (y : nadd) (x : nadd) (z : nadd) (n : nat) : (term65 y x z n) = (term66 y x z n).
Proof. exact (MK_COMB (@lem1278776) (@lem1278775 y x z n)). Qed.
Lemma lem1278778 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1278779 (y : nadd) (x : nadd) (z : nadd) (n : nat) : (term67 y x z n) = (term68 y x z n).
Proof. exact (MK_COMB (@lem1278778) (@lem1278777 y x z n)). Qed.
Lemma lem1278780 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1278781 (y : nadd) (x : nadd) (z : nadd) (n : nat) (B : nat) : (term69 y x z n B) = (term70 y x z n B).
Proof. exact (MK_COMB (@lem1278779 y x z n) (@lem1278780 B)). Qed.
Lemma lem1278782 (y : nadd) (x : nadd) (z : nadd) (B : nat) : (term71 y x z B) = (term72 y x z B).
Proof. exact (fun_ext (fun n : nat => @lem1278781 y x z n B)). Qed.
Lemma lem1278783 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1278784 (y : nadd) (x : nadd) (z : nadd) (B : nat) : (term73 y x z B) = (term74 y x z B).
Proof. exact (MK_COMB (@lem1278783) (@lem1278782 y x z B)). Qed.
Lemma lem1278789 (y : nadd) (x : nadd) (z : nadd) : (term75 y x z) = (term76 y x z).
Proof. exact (fun_ext (fun B : nat => @lem1278784 y x z B)). Qed.
Lemma lem1278790 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1278791 (y : nadd) (x : nadd) (z : nadd) : (term18 y x z) = (term77 y x z).
Proof. exact (MK_COMB (@lem1278790) (@lem1278789 y x z)). Qed.
Lemma lem1278796 (y : nadd) (x : nadd) (z : nadd) : (term77 y x z) = (term18 y x z).
Proof. exact (SYM (@lem1278791 y x z)). Qed.
Lemma lem1278797 (m : nat) (x : nadd) (B : nat) (h1 : term2 x B) : term78 x B m.
Proof. exact (@lem1278631 x B h1 m). Qed.
Lemma lem1278798 (m : nat) (x : nadd) (B : nat) : (term78 x B m) = (term79 m x B).
Proof. exact (eq_refl (term78 x B m)). Qed.
Lemma lem1278799 (m : nat) (x : nadd) (B : nat) (h1 : term2 x B) : term79 m x B.
Proof. exact (EQ_MP (@lem1278798 m x B) (@lem1278797 m x B h1)). Qed.
Lemma lem1278800 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term2 x B) : term80 m x B n.
Proof. exact (@lem1278799 m x B h1 n). Qed.
Lemma lem1278801 (m : nat) (x : nadd) (n : nat) (B : nat) : (term80 m x B n) = (term81 m x n B).
Proof. exact (eq_refl (term80 m x B n)). Qed.
Lemma lem1278802 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term2 x B) : term81 m x n B.
Proof. exact (EQ_MP (@lem1278801 m x n B) (@lem1278800 m n x B h1)). Qed.
Lemma lem1278803 (m : nat) (x : nadd) (n : nat) (B : nat) : (term81 m x n B) = ((term81 m x n B) = True).
Proof. exact (@lem7 (term81 m x n B)). Qed.
Lemma lem1278810 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term2 x B) : (term81 m x n B) = True.
Proof. exact (EQ_MP (@lem1278803 m x n B) (@lem1278802 m n x B h1)). Qed.
Lemma lem1278811 (y : nadd) (z : nadd) (n : nat) (x : nadd) (B : nat) (h1 : term2 x B) : (term70 y x z n B) = True.
Proof. exact (@lem1278810 (dest_nadd y n) (dest_nadd z n) x B h1). Qed.
Lemma lem1278812 (y : nadd) (z : nadd) (x : nadd) (B : nat) (h1 : term2 x B) : (term72 y x z B) = term82.
Proof. exact (fun_ext (fun n : nat => @lem1278811 y z n x B h1)). Qed.
Lemma lem1278813 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1278814 (y : nadd) (z : nadd) (x : nadd) (B : nat) (h1 : term2 x B) : (term74 y x z B) = term83.
Proof. exact (MK_COMB (@lem1278813) (@lem1278812 y z x B h1)). Qed.
Lemma lem1278816 {A : Type'} (t : Prop) : (term84 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1278817 (t : Prop) : (term85 t) = t.
Proof. exact (@lem1278816 nat t). Qed.
Lemma lem1278818 : term83 = True.
Proof. exact (@lem1278817 True). Qed.
Lemma lem1278819 (y : nadd) (z : nadd) (x : nadd) (B : nat) (h1 : term2 x B) : (term74 y x z B) = True.
Proof. exact (TRANS (@lem1278814 y z x B h1) (@lem1278818)). Qed.
Lemma lem1278820 (y : nadd) (z : nadd) (x : nadd) (B : nat) (h1 : term2 x B) : True = (term74 y x z B).
Proof. exact (SYM (@lem1278819 y z x B h1)). Qed.
Lemma lem1278821 (y : nadd) (z : nadd) (x : nadd) (B : nat) (h1 : term2 x B) : term74 y x z B.
Proof. exact (EQ_MP (@lem1278820 y z x B h1) (@lem0)). Qed.
Lemma lem1278822 (y : nadd) (z : nadd) (x : nadd) (B : nat) (h1 : term2 x B) : term77 y x z.
Proof. exact (ex_intro (term76 y x z) B (@lem1278821 y z x B h1)). Qed.
Lemma lem1278823 (y : nadd) (x : nadd) (z : nadd) : term77 y x z.
Proof. exact (ex_elim (@lem1278630 x) (fun B : nat => fun h0 : term86 x B => @lem1278822 y z x B h0)). Qed.
Lemma lem1278824 (y : nadd) (x : nadd) (z : nadd) : term18 y x z.
Proof. exact (EQ_MP (@lem1278796 y x z) (@lem1278823 y x z)). Qed.
Lemma lem1278825 (y : nadd) (x : nadd) (z : nadd) : term17 y x z.
Proof. exact (EQ_MP (@lem1278661 y x z) (@lem1278824 y x z)). Qed.
Lemma lem1278830 (y : nadd) (x : nadd) : term87 y x.
Proof. exact (fun z : nadd => @lem1278825 y x z). Qed.
Lemma lem1278835 (x : nadd) : term88 x.
Proof. exact (fun y : nadd => @lem1278830 y x). Qed.
Lemma lem1278840 : term89.
Proof. exact (fun x : nadd => @lem1278835 x). Qed.
