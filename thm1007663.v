Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1007663_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm75543_spec.
Lemma lem1006582 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1006583 (m : nat) (n : nat) (p : nat) : (((Nat.mul m n) = p) = ((term1 m n) = (NUMERAL p))) = (term2 m n p).
Proof. exact (@lem1006582 (((Nat.mul m n) = p) = ((term1 m n) = (NUMERAL p)))). Qed.
Lemma lem1006584 (m : nat) (n : nat) (p : nat) : (term2 m n p) = (((Nat.mul m n) = p) = ((term1 m n) = (NUMERAL p))).
Proof. exact (SYM (@lem1006583 m n p)). Qed.
Lemma lem1006585 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : term3 m n p.
Proof. exact (h1). Qed.
Lemma lem1006588 (m : nat) (n : nat) (p : nat) (h1 : term4 m n p) : term4 m n p.
Proof. exact (h1). Qed.
Lemma lem1006589 (m : nat) (n : nat) (p : nat) : term5 m n p.
Proof. exact (fun h0 : term4 m n p => @lem1006588 m n p h0). Qed.
Lemma lem1006590 (m : nat) (n : nat) (p : nat) (h1 : term5 m n p) : term5 m n p.
Proof. exact (h1). Qed.
Lemma lem1006591 (m : nat) (n : nat) (p : nat) (h1 : term4 m n p) : term4 m n p.
Proof. exact (h1). Qed.
Lemma lem1006592 (m : nat) (n : nat) (p : nat) (h1 : term4 m n p) (h2 : term5 m n p) : term4 m n p.
Proof. exact (@lem1006590 m n p h2 (@lem1006591 m n p h1)). Qed.
Lemma lem1006593 (m : nat) (n : nat) (p : nat) (h1 : term4 m n p) : term6 m n p.
Proof. exact (fun h0 : term5 m n p => @lem1006592 m n p h1 h0). Qed.
Lemma lem1006594 (m : nat) (n : nat) (p : nat) (h1 : term5 m n p) : term5 m n p.
Proof. exact (h1). Qed.
Lemma lem1006595 (m : nat) (n : nat) (p : nat) (h1 : term4 m n p) (h2 : term5 m n p) : term4 m n p.
Proof. exact (@lem1006593 m n p h1 (@lem1006594 m n p h2)). Qed.
Lemma lem1006596 (m : nat) (n : nat) (p : nat) (h1 : term5 m n p) : term5 m n p.
Proof. exact (fun h0 : term4 m n p => @lem1006595 m n p h0 h1). Qed.
Lemma lem1006597 (m : nat) (n : nat) (p : nat) : term7 m n p.
Proof. exact (fun h0 : term5 m n p => @lem1006596 m n p h0). Qed.
Lemma lem1006600 (m : nat) (n : nat) (p : nat) : term5 m n p.
Proof. exact (@lem1006597 m n p (@lem1006589 m n p)). Qed.
Lemma lem1006616 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1006617 : term8 = term9.
Proof. exact (@lem1006616 term10). Qed.
Lemma lem1006622 (m : nat) (n : nat) (p : nat) : (term11 m n p) = (term11 m n p).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem1006623 (m : nat) (n : nat) (p : nat) : (term4 m n p) = (term12 m n p).
Proof. exact (MK_COMB (@lem1006622 m n p) (@lem1006617)). Qed.
Lemma lem1006626 (n : nat) (p : nat) : (term13 n p) = (term14 n p).
Proof. exact (fun_ext (fun m : nat => @lem1006623 m n p)). Qed.
Lemma lem1006627 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1006628 (n : nat) (p : nat) : (term15 n p) = (term16 n p).
Proof. exact (MK_COMB (@lem1006627) (@lem1006626 n p)). Qed.
Lemma lem1006633 (p : nat) : (term17 p) = (term18 p).
Proof. exact (fun_ext (fun n : nat => @lem1006628 n p)). Qed.
Lemma lem1006634 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1006635 (p : nat) : (term19 p) = (term20 p).
Proof. exact (MK_COMB (@lem1006634) (@lem1006633 p)). Qed.
Lemma lem1006640 : term21 = term22.
Proof. exact (fun_ext (fun p : nat => @lem1006635 p)). Qed.
Lemma lem1006641 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1006650 : term23 = term24.
Proof. exact (MK_COMB (@lem1006641) (@lem1006640)). Qed.
Lemma lem1006651 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1006652 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1006651 n)). Qed.
Lemma lem1006653 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1006654 : term10 = term10.
Proof. exact (MK_COMB (@lem1006653) (@lem1006652)). Qed.
Lemma lem1006655 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1006656 : term9 = term9.
Proof. exact (MK_COMB (@lem1006655) (@lem1006654)). Qed.
Lemma lem1006665 (m : nat) (n : nat) (p : nat) : (term11 m n p) = (term11 m n p).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem1006666 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term12 m n p).
Proof. exact (MK_COMB (@lem1006665 m n p) (@lem1006656)). Qed.
Lemma lem1006667 (n : nat) (p : nat) : (term14 n p) = (term14 n p).
Proof. exact (fun_ext (fun m : nat => @lem1006666 m n p)). Qed.
Lemma lem1006668 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1006669 (n : nat) (p : nat) : (term16 n p) = (term16 n p).
Proof. exact (MK_COMB (@lem1006668) (@lem1006667 n p)). Qed.
Lemma lem1006670 (p : nat) : (term18 p) = (term18 p).
Proof. exact (fun_ext (fun n : nat => @lem1006669 n p)). Qed.
Lemma lem1006671 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1006672 (p : nat) : (term20 p) = (term20 p).
Proof. exact (MK_COMB (@lem1006671) (@lem1006670 p)). Qed.
Lemma lem1006673 : term22 = term22.
Proof. exact (fun_ext (fun p : nat => @lem1006672 p)). Qed.
Lemma lem1006674 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1006675 : term24 = term24.
Proof. exact (MK_COMB (@lem1006674) (@lem1006673)). Qed.
Lemma lem1006704 : term23 = term24.
Proof. exact (TRANS (@lem1006650) (@lem1006675)). Qed.
Lemma lem1006705 : term24 = term23.
Proof. exact (SYM (@lem1006704)). Qed.
Lemma lem1006706 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : term3 m n p.
Proof. exact (h1). Qed.
Lemma lem1006707 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1006726 (m : nat) (n : nat) (p : nat) : (term3 m n p) = (term26 m n p).
Proof. exact (@lem17646 ((Nat.mul m n) = p) ((term1 m n) = (NUMERAL p))). Qed.
Lemma lem1006728 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1006729 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1006728 n)). Qed.
Lemma lem1006730 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1006739 : term10 = term10.
Proof. exact (MK_COMB (@lem1006730) (@lem1006729)). Qed.
Lemma lem1006740 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1006739) (@lem1006707 h1)). Qed.
Lemma lem1006802 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : term26 m n p.
Proof. exact (EQ_MP (@lem1006726 m n p) (@lem1006706 m n p h1)). Qed.
Lemma lem1006809 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1006810 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1006809 n)). Qed.
Lemma lem1006811 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1006812 : term10 = term10.
Proof. exact (MK_COMB (@lem1006811) (@lem1006810)). Qed.
Lemma lem1006813 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1006812) (@lem1006740 h1)). Qed.
Lemma lem1006814 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : term27 m n p.
Proof. exact (h1). Qed.
Lemma lem1006815 (m : nat) (n : nat) (p : nat) (h1 : term28 m n p) : term28 m n p.
Proof. exact (h1). Qed.
Lemma lem1006821 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1006822 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1006821 n)). Qed.
Lemma lem1006823 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1006825 : term10 = term10.
Proof. exact (MK_COMB (@lem1006823) (@lem1006822)). Qed.
Lemma lem1006826 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1006825) (@lem1006813 h1)). Qed.
Lemma lem1006836 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1006837 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1006836 n)). Qed.
Lemma lem1006838 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1006840 : term10 = term10.
Proof. exact (MK_COMB (@lem1006838) (@lem1006837)). Qed.
Lemma lem1006841 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1006840) (@lem1006813 h1)). Qed.
Lemma lem1006850 (_16322 : nat) (h1 : term10) : term29 _16322.
Proof. exact (@lem1006826 h1 _16322). Qed.
Lemma lem1006851 (_16322 : nat) : (term29 _16322) = ((NUMERAL _16322) = _16322).
Proof. exact (eq_refl (term29 _16322)). Qed.
Lemma lem1006853 (_16323 : nat) (h1 : term10) : term29 _16323.
Proof. exact (@lem1006841 h1 _16323). Qed.
Lemma lem1006854 (_16323 : nat) : (term29 _16323) = ((NUMERAL _16323) = _16323).
Proof. exact (eq_refl (term29 _16323)). Qed.
Lemma lem1006859 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : (Nat.mul m n) = p.
Proof. exact (proj1 (@lem1006814 m n p h1)). Qed.
Lemma lem1006861 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : term30 m n p.
Proof. exact (proj2 (@lem1006814 m n p h1)). Qed.
Lemma lem1006865 (m : nat) (n : nat) (p : nat) (h1 : term28 m n p) : term31 m n p.
Proof. exact (proj1 (@lem1006815 m n p h1)). Qed.
Lemma lem1006868 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : p = (Nat.mul m n).
Proof. exact (SYM (@lem1006859 m n p h1)). Qed.
Lemma lem1006897 (m : nat) (n : nat) : (term32 m n) = (term32 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1006898 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : (term33 m n p) = (term34 m n).
Proof. exact (MK_COMB (@lem1006897 m n) (@lem1006868 m n p h1)). Qed.
Lemma lem1006899 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem1006900 (m : nat) (n : nat) (p : nat) : (term36 m n p) = (term36 m n p).
Proof. exact (eq_refl (term36 m n p)). Qed.
Lemma lem1006901 (p : nat) (m : nat) (n : nat) : ((term33 m n p) = (term34 m n)) = ((term33 m n p) = (term35 m n)).
Proof. exact (MK_COMB (@lem1006900 m n p) (@lem1006899 m n)). Qed.
Lemma lem1006902 (m : nat) (n : nat) (p : nat) : (term33 m n p) = (term30 m n p).
Proof. exact (eq_refl (term33 m n p)). Qed.
Lemma lem1006903 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1006904 (m : nat) (n : nat) (p : nat) : (term36 m n p) = (term37 m n p).
Proof. exact (MK_COMB (@lem1006903) (@lem1006902 m n p)). Qed.
Lemma lem1006905 (m : nat) (n : nat) : (term35 m n) = (term35 m n).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem1006906 (p : nat) (m : nat) (n : nat) : ((term33 m n p) = (term35 m n)) = ((term30 m n p) = (term35 m n)).
Proof. exact (MK_COMB (@lem1006904 m n p) (@lem1006905 m n)). Qed.
Lemma lem1006907 (p : nat) (m : nat) (n : nat) : ((term33 m n p) = (term34 m n)) = ((term30 m n p) = (term35 m n)).
Proof. exact (TRANS (@lem1006901 p m n) (@lem1006906 p m n)). Qed.
Lemma lem1006908 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : (term30 m n p) = (term35 m n).
Proof. exact (EQ_MP (@lem1006907 p m n) (@lem1006898 m n p h1)). Qed.
Lemma lem1006909 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : term35 m n.
Proof. exact (EQ_MP (@lem1006908 m n p h1) (@lem1006861 m n p h1)). Qed.
Lemma lem1006910 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1006911 (_16330 : nat) (_16332 : nat) (h1 : _16330 = _16332) : _16330 = _16332.
Proof. exact (h1). Qed.
Lemma lem1006912 (_16331 : nat) (_16333 : nat) (h1 : _16331 = _16333) : _16331 = _16333.
Proof. exact (h1). Qed.
Lemma lem1006913 (_16330 : nat) (_16332 : nat) (h1 : _16330 = _16332) : (Nat.mul _16330) = (Nat.mul _16332).
Proof. exact (MK_COMB (@lem1006910) (@lem1006911 _16330 _16332 h1)). Qed.
Lemma lem1006914 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) (h1 : _16330 = _16332) (h2 : _16331 = _16333) : (Nat.mul _16330 _16331) = (Nat.mul _16332 _16333).
Proof. exact (MK_COMB (@lem1006913 _16330 _16332 h1) (@lem1006912 _16331 _16333 h2)). Qed.
Lemma lem1006915 (_16331 : nat) (_16333 : nat) (_16330 : nat) (_16332 : nat) (h1 : _16330 = _16332) : term38 _16330 _16331 _16332 _16333.
Proof. exact (fun h0 : _16331 = _16333 => @lem1006914 _16330 _16332 _16331 _16333 h1 h0). Qed.
Lemma lem1006917 (a : Prop) (b : Prop) : (a -> b) = (term39 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1006918 (_16330 : nat) (_16331 : nat) (_16332 : nat) (_16333 : nat) : (term38 _16330 _16331 _16332 _16333) = (term40 _16330 _16331 _16332 _16333).
Proof. exact (@lem1006917 (_16331 = _16333) ((Nat.mul _16330 _16331) = (Nat.mul _16332 _16333))). Qed.
Lemma lem1006919 (_16331 : nat) (_16333 : nat) (_16330 : nat) (_16332 : nat) (h1 : _16330 = _16332) : term40 _16330 _16331 _16332 _16333.
Proof. exact (EQ_MP (@lem1006918 _16330 _16331 _16332 _16333) (@lem1006915 _16331 _16333 _16330 _16332 h1)). Qed.
Lemma lem1006920 (_16330 : nat) (_16331 : nat) (_16332 : nat) (_16333 : nat) : term41 _16330 _16331 _16332 _16333.
Proof. exact (fun h0 : _16330 = _16332 => @lem1006919 _16331 _16333 _16330 _16332 h0). Qed.
Lemma lem1006922 (a : Prop) (b : Prop) : (a -> b) = (term39 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1006923 (_16330 : nat) (_16331 : nat) (_16332 : nat) (_16333 : nat) : (term41 _16330 _16331 _16332 _16333) = (term42 _16330 _16331 _16332 _16333).
Proof. exact (@lem1006922 (_16330 = _16332) (term40 _16330 _16331 _16332 _16333)). Qed.
Lemma lem1006924 (_16330 : nat) (_16331 : nat) (_16332 : nat) (_16333 : nat) : term42 _16330 _16331 _16332 _16333.
Proof. exact (EQ_MP (@lem1006923 _16330 _16331 _16332 _16333) (@lem1006920 _16330 _16331 _16332 _16333)). Qed.
Lemma lem1006925 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem1006926 (_16334 : nat) (_16335 : nat) (h1 : _16334 = _16335) : _16334 = _16335.
Proof. exact (h1). Qed.
Lemma lem1006927 (_16334 : nat) (_16335 : nat) (h1 : _16334 = _16335) : (NUMERAL _16334) = (NUMERAL _16335).
Proof. exact (MK_COMB (@lem1006925) (@lem1006926 _16334 _16335 h1)). Qed.
Lemma lem1006928 (_16334 : nat) (_16335 : nat) : term43 _16334 _16335.
Proof. exact (fun h0 : _16334 = _16335 => @lem1006927 _16334 _16335 h0). Qed.
Lemma lem1006930 (a : Prop) (b : Prop) : (a -> b) = (term39 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1006931 (_16334 : nat) (_16335 : nat) : (term43 _16334 _16335) = (term44 _16334 _16335).
Proof. exact (@lem1006930 (_16334 = _16335) ((NUMERAL _16334) = (NUMERAL _16335))). Qed.
Lemma lem1006932 (_16334 : nat) (_16335 : nat) : term44 _16334 _16335.
Proof. exact (EQ_MP (@lem1006931 _16334 _16335) (@lem1006928 _16334 _16335)). Qed.
Lemma lem1006934 (x : nat) (y : nat) (z : nat) : term45 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1006936 (_16322 : nat) (h1 : term10) : (NUMERAL _16322) = _16322.
Proof. exact (EQ_MP (@lem1006851 _16322) (@lem1006850 _16322 h1)). Qed.
Lemma lem1006937 (m : nat) (n : nat) (h1 : term10) : (term46 m n) = (term1 m n).
Proof. exact (@lem1006936 (term1 m n) h1). Qed.
Lemma lem1006938 (m : nat) (n : nat) (h1 : term10) : term47 m n.
Proof. exact (fun h0 : term48 m n => @lem1006937 m n h1). Qed.
Lemma lem1006940 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1006941 (m : nat) (n : nat) : (term47 m n) = ((term46 m n) = (term1 m n)).
Proof. exact (@lem1006940 ((term46 m n) = (term1 m n))). Qed.
Lemma lem1006942 (m : nat) (n : nat) (h1 : term10) : (term46 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem1006941 m n) (@lem1006938 m n h1)). Qed.
Lemma lem1006944 (_16322 : nat) (h1 : term10) : (NUMERAL _16322) = _16322.
Proof. exact (EQ_MP (@lem1006851 _16322) (@lem1006850 _16322 h1)). Qed.
Lemma lem1006945 (m : nat) (h1 : term10) : (NUMERAL m) = m.
Proof. exact (@lem1006944 m h1). Qed.
Lemma lem1006946 (m : nat) (h1 : term10) : term50 m.
Proof. exact (fun h0 : term51 m => @lem1006945 m h1). Qed.
Lemma lem1006948 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1006949 (m : nat) : (term50 m) = ((NUMERAL m) = m).
Proof. exact (@lem1006948 ((NUMERAL m) = m)). Qed.
Lemma lem1006950 (m : nat) (h1 : term10) : (NUMERAL m) = m.
Proof. exact (EQ_MP (@lem1006949 m) (@lem1006946 m h1)). Qed.
Lemma lem1006952 (_16322 : nat) (h1 : term10) : (NUMERAL _16322) = _16322.
Proof. exact (EQ_MP (@lem1006851 _16322) (@lem1006850 _16322 h1)). Qed.
Lemma lem1006953 (n : nat) (h1 : term10) : (NUMERAL n) = n.
Proof. exact (@lem1006952 n h1). Qed.
Lemma lem1006954 (n : nat) (h1 : term10) : term50 n.
Proof. exact (fun h0 : term51 n => @lem1006953 n h1). Qed.
Lemma lem1006956 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1006957 (n : nat) : (term50 n) = ((NUMERAL n) = n).
Proof. exact (@lem1006956 ((NUMERAL n) = n)). Qed.
Lemma lem1006958 (n : nat) (h1 : term10) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1006957 n) (@lem1006954 n h1)). Qed.
Lemma lem1006976 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1006977 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : (term40 _16330 _16331 _16332 _16333) = (term52 _16330 _16332 _16331 _16333).
Proof. exact (@lem1006976 ((Nat.mul _16330 _16331) = (Nat.mul _16332 _16333)) (term53 _16331 _16333)). Qed.
Lemma lem1006987 (_16330 : nat) (_16332 : nat) : (term54 _16330 _16332) = (term54 _16330 _16332).
Proof. exact (eq_refl (term54 _16330 _16332)). Qed.
Lemma lem1006988 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : (term42 _16330 _16331 _16332 _16333) = (term55 _16330 _16332 _16331 _16333).
Proof. exact (MK_COMB (@lem1006987 _16330 _16332) (@lem1006977 _16330 _16332 _16331 _16333)). Qed.
Lemma lem1006992 (q : Prop) (p : Prop) (r : Prop) : (term56 p q r) = (term56 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1006993 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : (term55 _16330 _16332 _16331 _16333) = (term57 _16330 _16332 _16331 _16333).
Proof. exact (@lem1006992 ((Nat.mul _16330 _16331) = (Nat.mul _16332 _16333)) (term53 _16330 _16332) (term53 _16331 _16333)). Qed.
Lemma lem1007015 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : (term42 _16330 _16331 _16332 _16333) = (term57 _16330 _16332 _16331 _16333).
Proof. exact (TRANS (@lem1006988 _16330 _16332 _16331 _16333) (@lem1006993 _16330 _16332 _16331 _16333)). Qed.
Lemma lem1007016 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1007017 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : (term58 _16330 _16331 _16332 _16333) = (term59 _16330 _16332 _16331 _16333).
Proof. exact (MK_COMB (@lem1007016) (@lem1007015 _16330 _16332 _16331 _16333)). Qed.
Lemma lem1007039 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : (term57 _16330 _16332 _16331 _16333) = (term57 _16330 _16332 _16331 _16333).
Proof. exact (eq_refl (term57 _16330 _16332 _16331 _16333)). Qed.
Lemma lem1007040 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : ((term42 _16330 _16331 _16332 _16333) = (term57 _16330 _16332 _16331 _16333)) = ((term57 _16330 _16332 _16331 _16333) = (term57 _16330 _16332 _16331 _16333)).
Proof. exact (MK_COMB (@lem1007017 _16330 _16332 _16331 _16333) (@lem1007039 _16330 _16332 _16331 _16333)). Qed.
Lemma lem1007042 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1007043 (x : Prop) : (x = x) = True.
Proof. exact (@lem1007042 Prop x). Qed.
Lemma lem1007044 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : ((term57 _16330 _16332 _16331 _16333) = (term57 _16330 _16332 _16331 _16333)) = True.
Proof. exact (@lem1007043 (term57 _16330 _16332 _16331 _16333)). Qed.
Lemma lem1007045 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : ((term42 _16330 _16331 _16332 _16333) = (term57 _16330 _16332 _16331 _16333)) = True.
Proof. exact (TRANS (@lem1007040 _16330 _16332 _16331 _16333) (@lem1007044 _16330 _16332 _16331 _16333)). Qed.
Lemma lem1007046 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : True = ((term42 _16330 _16331 _16332 _16333) = (term57 _16330 _16332 _16331 _16333)).
Proof. exact (SYM (@lem1007045 _16330 _16332 _16331 _16333)). Qed.
Lemma lem1007047 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : (term42 _16330 _16331 _16332 _16333) = (term57 _16330 _16332 _16331 _16333).
Proof. exact (EQ_MP (@lem1007046 _16330 _16332 _16331 _16333) (@lem0)). Qed.
Lemma lem1007048 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : term57 _16330 _16332 _16331 _16333.
Proof. exact (EQ_MP (@lem1007047 _16330 _16332 _16331 _16333) (@lem1006924 _16330 _16331 _16332 _16333)). Qed.
Lemma lem1007050 (b : Prop) (a : Prop) : (a \/ b) = (term60 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1007051 (_16330 : nat) (_16331 : nat) (_16332 : nat) (_16333 : nat) : (term57 _16330 _16332 _16331 _16333) = (term61 _16330 _16331 _16332 _16333).
Proof. exact (@lem1007050 (term62 _16330 _16332 _16331 _16333) ((Nat.mul _16330 _16331) = (Nat.mul _16332 _16333))). Qed.
Lemma lem1007053 (a : Prop) (b : Prop) : (term63 a b) = (term64 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1007054 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : (term65 _16330 _16332 _16331 _16333) = (term66 _16330 _16332 _16331 _16333).
Proof. exact (@lem1007053 (term53 _16330 _16332) (term53 _16331 _16333)). Qed.
Lemma lem1007056 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1007057 (_16330 : nat) (_16332 : nat) : (term68 _16330 _16332) = (_16330 = _16332).
Proof. exact (@lem1007056 (_16330 = _16332)). Qed.
Lemma lem1007058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1007059 (_16330 : nat) (_16332 : nat) : (term69 _16330 _16332) = (term70 _16330 _16332).
Proof. exact (MK_COMB (@lem1007058) (@lem1007057 _16330 _16332)). Qed.
Lemma lem1007061 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1007062 (_16331 : nat) (_16333 : nat) : (term68 _16331 _16333) = (_16331 = _16333).
Proof. exact (@lem1007061 (_16331 = _16333)). Qed.
Lemma lem1007063 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : (term66 _16330 _16332 _16331 _16333) = (term71 _16330 _16332 _16331 _16333).
Proof. exact (MK_COMB (@lem1007059 _16330 _16332) (@lem1007062 _16331 _16333)). Qed.
Lemma lem1007064 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : (term65 _16330 _16332 _16331 _16333) = (term71 _16330 _16332 _16331 _16333).
Proof. exact (TRANS (@lem1007054 _16330 _16332 _16331 _16333) (@lem1007063 _16330 _16332 _16331 _16333)). Qed.
Lemma lem1007065 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1007066 (_16330 : nat) (_16332 : nat) (_16331 : nat) (_16333 : nat) : (term72 _16330 _16332 _16331 _16333) = (term73 _16330 _16332 _16331 _16333).
Proof. exact (MK_COMB (@lem1007065) (@lem1007064 _16330 _16332 _16331 _16333)). Qed.
Lemma lem1007067 (_16330 : nat) (_16331 : nat) (_16332 : nat) (_16333 : nat) : ((Nat.mul _16330 _16331) = (Nat.mul _16332 _16333)) = ((Nat.mul _16330 _16331) = (Nat.mul _16332 _16333)).
Proof. exact (eq_refl ((Nat.mul _16330 _16331) = (Nat.mul _16332 _16333))). Qed.
Lemma lem1007068 (_16330 : nat) (_16331 : nat) (_16332 : nat) (_16333 : nat) : (term61 _16330 _16331 _16332 _16333) = (term74 _16330 _16331 _16332 _16333).
Proof. exact (MK_COMB (@lem1007066 _16330 _16332 _16331 _16333) (@lem1007067 _16330 _16331 _16332 _16333)). Qed.
Lemma lem1007069 (_16330 : nat) (_16331 : nat) (_16332 : nat) (_16333 : nat) : (term57 _16330 _16332 _16331 _16333) = (term74 _16330 _16331 _16332 _16333).
Proof. exact (TRANS (@lem1007051 _16330 _16331 _16332 _16333) (@lem1007068 _16330 _16331 _16332 _16333)). Qed.
Lemma lem1007071 (m : nat) (n : nat) (h1 : term10) : term75 m n.
Proof. exact (conj (@lem1006950 m h1) (@lem1006958 n h1)). Qed.
Lemma lem1007073 (_16330 : nat) (_16331 : nat) (_16332 : nat) (_16333 : nat) : term74 _16330 _16331 _16332 _16333.
Proof. exact (EQ_MP (@lem1007069 _16330 _16331 _16332 _16333) (@lem1007048 _16330 _16332 _16331 _16333)). Qed.
Lemma lem1007074 (m : nat) (n : nat) : term76 m n.
Proof. exact (@lem1007073 (NUMERAL m) (NUMERAL n) m n). Qed.
Lemma lem1007077 (m : nat) (n : nat) (h1 : term10) : (term1 m n) = (Nat.mul m n).
Proof. exact (@lem1007074 m n (@lem1007071 m n h1)). Qed.
Lemma lem1007078 (m : nat) (n : nat) (h1 : term10) : term77 m n.
Proof. exact (fun h0 : term78 m n => @lem1007077 m n h1). Qed.
Lemma lem1007080 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1007081 (m : nat) (n : nat) : (term77 m n) = ((term1 m n) = (Nat.mul m n)).
Proof. exact (@lem1007080 ((term1 m n) = (Nat.mul m n))). Qed.
Lemma lem1007082 (m : nat) (n : nat) (h1 : term10) : (term1 m n) = (Nat.mul m n).
Proof. exact (EQ_MP (@lem1007081 m n) (@lem1007078 m n h1)). Qed.
Lemma lem1007088 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1007089 (_16334 : nat) (_16335 : nat) : (term44 _16334 _16335) = (term79 _16334 _16335).
Proof. exact (@lem1007088 ((NUMERAL _16334) = (NUMERAL _16335)) (term53 _16334 _16335)). Qed.
Lemma lem1007099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1007100 (_16334 : nat) (_16335 : nat) : (term80 _16334 _16335) = (term81 _16334 _16335).
Proof. exact (MK_COMB (@lem1007099) (@lem1007089 _16334 _16335)). Qed.
Lemma lem1007110 (_16334 : nat) (_16335 : nat) : (term79 _16334 _16335) = (term79 _16334 _16335).
Proof. exact (eq_refl (term79 _16334 _16335)). Qed.
Lemma lem1007111 (_16334 : nat) (_16335 : nat) : ((term44 _16334 _16335) = (term79 _16334 _16335)) = ((term79 _16334 _16335) = (term79 _16334 _16335)).
Proof. exact (MK_COMB (@lem1007100 _16334 _16335) (@lem1007110 _16334 _16335)). Qed.
Lemma lem1007113 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1007114 (x : Prop) : (x = x) = True.
Proof. exact (@lem1007113 Prop x). Qed.
Lemma lem1007115 (_16334 : nat) (_16335 : nat) : ((term79 _16334 _16335) = (term79 _16334 _16335)) = True.
Proof. exact (@lem1007114 (term79 _16334 _16335)). Qed.
Lemma lem1007116 (_16334 : nat) (_16335 : nat) : ((term44 _16334 _16335) = (term79 _16334 _16335)) = True.
Proof. exact (TRANS (@lem1007111 _16334 _16335) (@lem1007115 _16334 _16335)). Qed.
Lemma lem1007117 (_16334 : nat) (_16335 : nat) : True = ((term44 _16334 _16335) = (term79 _16334 _16335)).
Proof. exact (SYM (@lem1007116 _16334 _16335)). Qed.
Lemma lem1007118 (_16334 : nat) (_16335 : nat) : (term44 _16334 _16335) = (term79 _16334 _16335).
Proof. exact (EQ_MP (@lem1007117 _16334 _16335) (@lem0)). Qed.
Lemma lem1007119 (_16334 : nat) (_16335 : nat) : term79 _16334 _16335.
Proof. exact (EQ_MP (@lem1007118 _16334 _16335) (@lem1006932 _16334 _16335)). Qed.
Lemma lem1007121 (b : Prop) (a : Prop) : (a \/ b) = (term60 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1007122 (_16334 : nat) (_16335 : nat) : (term79 _16334 _16335) = (term82 _16334 _16335).
Proof. exact (@lem1007121 (term53 _16334 _16335) ((NUMERAL _16334) = (NUMERAL _16335))). Qed.
Lemma lem1007124 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1007125 (_16334 : nat) (_16335 : nat) : (term68 _16334 _16335) = (_16334 = _16335).
Proof. exact (@lem1007124 (_16334 = _16335)). Qed.
Lemma lem1007126 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1007127 (_16334 : nat) (_16335 : nat) : (term83 _16334 _16335) = (term84 _16334 _16335).
Proof. exact (MK_COMB (@lem1007126) (@lem1007125 _16334 _16335)). Qed.
Lemma lem1007128 (_16334 : nat) (_16335 : nat) : ((NUMERAL _16334) = (NUMERAL _16335)) = ((NUMERAL _16334) = (NUMERAL _16335)).
Proof. exact (eq_refl ((NUMERAL _16334) = (NUMERAL _16335))). Qed.
Lemma lem1007129 (_16334 : nat) (_16335 : nat) : (term82 _16334 _16335) = (term43 _16334 _16335).
Proof. exact (MK_COMB (@lem1007127 _16334 _16335) (@lem1007128 _16334 _16335)). Qed.
Lemma lem1007130 (_16334 : nat) (_16335 : nat) : (term79 _16334 _16335) = (term43 _16334 _16335).
Proof. exact (TRANS (@lem1007122 _16334 _16335) (@lem1007129 _16334 _16335)). Qed.
Lemma lem1007133 (_16334 : nat) (_16335 : nat) : term43 _16334 _16335.
Proof. exact (EQ_MP (@lem1007130 _16334 _16335) (@lem1007119 _16334 _16335)). Qed.
Lemma lem1007134 (m : nat) (n : nat) : term85 m n.
Proof. exact (@lem1007133 (term1 m n) (Nat.mul m n)). Qed.
Lemma lem1007137 (m : nat) (n : nat) (h1 : term10) : (term46 m n) = (term86 m n).
Proof. exact (@lem1007134 m n (@lem1007082 m n h1)). Qed.
Lemma lem1007138 (m : nat) (n : nat) (h1 : term10) : term87 m n.
Proof. exact (fun h0 : term88 m n => @lem1007137 m n h1). Qed.
Lemma lem1007140 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1007141 (m : nat) (n : nat) : (term87 m n) = ((term46 m n) = (term86 m n)).
Proof. exact (@lem1007140 ((term46 m n) = (term86 m n))). Qed.
Lemma lem1007142 (m : nat) (n : nat) (h1 : term10) : (term46 m n) = (term86 m n).
Proof. exact (EQ_MP (@lem1007141 m n) (@lem1007138 m n h1)). Qed.
Lemma lem1007160 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1007161 (y : nat) (x : nat) (z : nat) : (term89 x y z) = (term90 y x z).
Proof. exact (@lem1007160 (y = z) (term53 x z)). Qed.
Lemma lem1007171 (x : nat) (y : nat) : (term54 x y) = (term54 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1007172 (y : nat) (x : nat) (z : nat) : (term45 x y z) = (term91 y x z).
Proof. exact (MK_COMB (@lem1007171 x y) (@lem1007161 y x z)). Qed.
Lemma lem1007176 (q : Prop) (p : Prop) (r : Prop) : (term56 p q r) = (term56 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1007177 (y : nat) (x : nat) (z : nat) : (term91 y x z) = (term92 y x z).
Proof. exact (@lem1007176 (y = z) (term53 x y) (term53 x z)). Qed.
Lemma lem1007199 (y : nat) (x : nat) (z : nat) : (term45 x y z) = (term92 y x z).
Proof. exact (TRANS (@lem1007172 y x z) (@lem1007177 y x z)). Qed.
Lemma lem1007200 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1007201 (y : nat) (x : nat) (z : nat) : (term93 x y z) = (term94 y x z).
Proof. exact (MK_COMB (@lem1007200) (@lem1007199 y x z)). Qed.
Lemma lem1007223 (y : nat) (x : nat) (z : nat) : (term92 y x z) = (term92 y x z).
Proof. exact (eq_refl (term92 y x z)). Qed.
Lemma lem1007224 (y : nat) (x : nat) (z : nat) : ((term45 x y z) = (term92 y x z)) = ((term92 y x z) = (term92 y x z)).
Proof. exact (MK_COMB (@lem1007201 y x z) (@lem1007223 y x z)). Qed.
Lemma lem1007226 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1007227 (x : Prop) : (x = x) = True.
Proof. exact (@lem1007226 Prop x). Qed.
Lemma lem1007228 (y : nat) (x : nat) (z : nat) : ((term92 y x z) = (term92 y x z)) = True.
Proof. exact (@lem1007227 (term92 y x z)). Qed.
Lemma lem1007229 (y : nat) (x : nat) (z : nat) : ((term45 x y z) = (term92 y x z)) = True.
Proof. exact (TRANS (@lem1007224 y x z) (@lem1007228 y x z)). Qed.
Lemma lem1007230 (y : nat) (x : nat) (z : nat) : True = ((term45 x y z) = (term92 y x z)).
Proof. exact (SYM (@lem1007229 y x z)). Qed.
Lemma lem1007231 (y : nat) (x : nat) (z : nat) : (term45 x y z) = (term92 y x z).
Proof. exact (EQ_MP (@lem1007230 y x z) (@lem0)). Qed.
Lemma lem1007232 (y : nat) (x : nat) (z : nat) : term92 y x z.
Proof. exact (EQ_MP (@lem1007231 y x z) (@lem1006934 x y z)). Qed.
Lemma lem1007234 (b : Prop) (a : Prop) : (a \/ b) = (term60 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1007235 (x : nat) (y : nat) (z : nat) : (term92 y x z) = (term95 x y z).
Proof. exact (@lem1007234 (term96 y x z) (y = z)). Qed.
Lemma lem1007237 (a : Prop) (b : Prop) : (term63 a b) = (term64 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1007238 (y : nat) (x : nat) (z : nat) : (term97 y x z) = (term98 y x z).
Proof. exact (@lem1007237 (term53 x y) (term53 x z)). Qed.
Lemma lem1007240 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1007241 (x : nat) (y : nat) : (term68 x y) = (x = y).
Proof. exact (@lem1007240 (x = y)). Qed.
Lemma lem1007242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1007243 (x : nat) (y : nat) : (term69 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1007242) (@lem1007241 x y)). Qed.
Lemma lem1007245 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1007246 (x : nat) (z : nat) : (term68 x z) = (x = z).
Proof. exact (@lem1007245 (x = z)). Qed.
Lemma lem1007247 (y : nat) (x : nat) (z : nat) : (term98 y x z) = (term99 y x z).
Proof. exact (MK_COMB (@lem1007243 x y) (@lem1007246 x z)). Qed.
Lemma lem1007248 (y : nat) (x : nat) (z : nat) : (term97 y x z) = (term99 y x z).
Proof. exact (TRANS (@lem1007238 y x z) (@lem1007247 y x z)). Qed.
Lemma lem1007249 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1007250 (y : nat) (x : nat) (z : nat) : (term100 y x z) = (term101 y x z).
Proof. exact (MK_COMB (@lem1007249) (@lem1007248 y x z)). Qed.
Lemma lem1007251 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1007252 (x : nat) (y : nat) (z : nat) : (term95 x y z) = (term102 x y z).
Proof. exact (MK_COMB (@lem1007250 y x z) (@lem1007251 y z)). Qed.
Lemma lem1007253 (x : nat) (y : nat) (z : nat) : (term92 y x z) = (term102 x y z).
Proof. exact (TRANS (@lem1007235 x y z) (@lem1007252 x y z)). Qed.
Lemma lem1007255 (m : nat) (n : nat) (h1 : term10) : term103 m n.
Proof. exact (conj (@lem1006942 m n h1) (@lem1007142 m n h1)). Qed.
Lemma lem1007257 (x : nat) (y : nat) (z : nat) : term102 x y z.
Proof. exact (EQ_MP (@lem1007253 x y z) (@lem1007232 y x z)). Qed.
Lemma lem1007258 (m : nat) (n : nat) : term104 m n.
Proof. exact (@lem1007257 (term46 m n) (term1 m n) (term86 m n)). Qed.
Lemma lem1007261 (m : nat) (n : nat) (h1 : term10) : (term1 m n) = (term86 m n).
Proof. exact (@lem1007258 m n (@lem1007255 m n h1)). Qed.
Lemma lem1007262 (m : nat) (n : nat) (h1 : term10) : term105 m n.
Proof. exact (fun h0 : term35 m n => @lem1007261 m n h1). Qed.
Lemma lem1007264 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1007265 (m : nat) (n : nat) : (term105 m n) = ((term1 m n) = (term86 m n)).
Proof. exact (@lem1007264 ((term1 m n) = (term86 m n))). Qed.
Lemma lem1007266 (m : nat) (n : nat) (h1 : term10) : (term1 m n) = (term86 m n).
Proof. exact (EQ_MP (@lem1007265 m n) (@lem1007262 m n h1)). Qed.
Lemma lem1007269 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1007271 (m : nat) (n : nat) : (term35 m n) = (term106 m n).
Proof. exact (@lem1007269 ((term1 m n) = (term86 m n))). Qed.
Lemma lem1007274 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : term106 m n.
Proof. exact (EQ_MP (@lem1007271 m n) (@lem1006909 m n p h1)). Qed.
Lemma lem1007277 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term27 m n p) : False.
Proof. exact (@lem1007274 m n p h2 (@lem1007266 m n h1)). Qed.
Lemma lem1007278 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term27 m n p) : term107.
Proof. exact (fun h0 : ~ False => @lem1007277 m n p h1 h2). Qed.
Lemma lem1007280 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1007281 : term107 = False.
Proof. exact (@lem1007280 False). Qed.
Lemma lem1007283 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1007284 (_16336 : nat) (_16338 : nat) (h1 : _16336 = _16338) : _16336 = _16338.
Proof. exact (h1). Qed.
Lemma lem1007285 (_16337 : nat) (_16339 : nat) (h1 : _16337 = _16339) : _16337 = _16339.
Proof. exact (h1). Qed.
Lemma lem1007286 (_16336 : nat) (_16338 : nat) (h1 : _16336 = _16338) : (Nat.mul _16336) = (Nat.mul _16338).
Proof. exact (MK_COMB (@lem1007283) (@lem1007284 _16336 _16338 h1)). Qed.
Lemma lem1007287 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) (h1 : _16336 = _16338) (h2 : _16337 = _16339) : (Nat.mul _16336 _16337) = (Nat.mul _16338 _16339).
Proof. exact (MK_COMB (@lem1007286 _16336 _16338 h1) (@lem1007285 _16337 _16339 h2)). Qed.
Lemma lem1007288 (_16337 : nat) (_16339 : nat) (_16336 : nat) (_16338 : nat) (h1 : _16336 = _16338) : term38 _16336 _16337 _16338 _16339.
Proof. exact (fun h0 : _16337 = _16339 => @lem1007287 _16336 _16338 _16337 _16339 h1 h0). Qed.
Lemma lem1007290 (a : Prop) (b : Prop) : (a -> b) = (term39 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1007291 (_16336 : nat) (_16337 : nat) (_16338 : nat) (_16339 : nat) : (term38 _16336 _16337 _16338 _16339) = (term40 _16336 _16337 _16338 _16339).
Proof. exact (@lem1007290 (_16337 = _16339) ((Nat.mul _16336 _16337) = (Nat.mul _16338 _16339))). Qed.
Lemma lem1007292 (_16337 : nat) (_16339 : nat) (_16336 : nat) (_16338 : nat) (h1 : _16336 = _16338) : term40 _16336 _16337 _16338 _16339.
Proof. exact (EQ_MP (@lem1007291 _16336 _16337 _16338 _16339) (@lem1007288 _16337 _16339 _16336 _16338 h1)). Qed.
Lemma lem1007293 (_16336 : nat) (_16337 : nat) (_16338 : nat) (_16339 : nat) : term41 _16336 _16337 _16338 _16339.
Proof. exact (fun h0 : _16336 = _16338 => @lem1007292 _16337 _16339 _16336 _16338 h0). Qed.
Lemma lem1007295 (a : Prop) (b : Prop) : (a -> b) = (term39 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1007296 (_16336 : nat) (_16337 : nat) (_16338 : nat) (_16339 : nat) : (term41 _16336 _16337 _16338 _16339) = (term42 _16336 _16337 _16338 _16339).
Proof. exact (@lem1007295 (_16336 = _16338) (term40 _16336 _16337 _16338 _16339)). Qed.
Lemma lem1007297 (_16336 : nat) (_16337 : nat) (_16338 : nat) (_16339 : nat) : term42 _16336 _16337 _16338 _16339.
Proof. exact (EQ_MP (@lem1007296 _16336 _16337 _16338 _16339) (@lem1007293 _16336 _16337 _16338 _16339)). Qed.
Lemma lem1007307 (x : nat) (y : nat) (z : nat) : term45 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1007309 (m : nat) (n : nat) (p : nat) (h1 : term28 m n p) : (term1 m n) = (NUMERAL p).
Proof. exact (proj2 (@lem1006815 m n p h1)). Qed.
Lemma lem1007310 (m : nat) (n : nat) (p : nat) (h1 : term28 m n p) : term108 m n p.
Proof. exact (fun h0 : term30 m n p => @lem1007309 m n p h1). Qed.
Lemma lem1007312 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1007313 (m : nat) (n : nat) (p : nat) : (term108 m n p) = ((term1 m n) = (NUMERAL p)).
Proof. exact (@lem1007312 ((term1 m n) = (NUMERAL p))). Qed.
Lemma lem1007314 (m : nat) (n : nat) (p : nat) (h1 : term28 m n p) : (term1 m n) = (NUMERAL p).
Proof. exact (EQ_MP (@lem1007313 m n p) (@lem1007310 m n p h1)). Qed.
Lemma lem1007316 (_16323 : nat) (h1 : term10) : (NUMERAL _16323) = _16323.
Proof. exact (EQ_MP (@lem1006854 _16323) (@lem1006853 _16323 h1)). Qed.
Lemma lem1007317 (m : nat) (h1 : term10) : (NUMERAL m) = m.
Proof. exact (@lem1007316 m h1). Qed.
Lemma lem1007318 (m : nat) (h1 : term10) : term50 m.
Proof. exact (fun h0 : term51 m => @lem1007317 m h1). Qed.
Lemma lem1007320 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1007321 (m : nat) : (term50 m) = ((NUMERAL m) = m).
Proof. exact (@lem1007320 ((NUMERAL m) = m)). Qed.
Lemma lem1007322 (m : nat) (h1 : term10) : (NUMERAL m) = m.
Proof. exact (EQ_MP (@lem1007321 m) (@lem1007318 m h1)). Qed.
Lemma lem1007324 (_16323 : nat) (h1 : term10) : (NUMERAL _16323) = _16323.
Proof. exact (EQ_MP (@lem1006854 _16323) (@lem1006853 _16323 h1)). Qed.
Lemma lem1007325 (n : nat) (h1 : term10) : (NUMERAL n) = n.
Proof. exact (@lem1007324 n h1). Qed.
Lemma lem1007326 (n : nat) (h1 : term10) : term50 n.
Proof. exact (fun h0 : term51 n => @lem1007325 n h1). Qed.
Lemma lem1007328 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1007329 (n : nat) : (term50 n) = ((NUMERAL n) = n).
Proof. exact (@lem1007328 ((NUMERAL n) = n)). Qed.
Lemma lem1007330 (n : nat) (h1 : term10) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1007329 n) (@lem1007326 n h1)). Qed.
Lemma lem1007348 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1007349 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : (term40 _16336 _16337 _16338 _16339) = (term52 _16336 _16338 _16337 _16339).
Proof. exact (@lem1007348 ((Nat.mul _16336 _16337) = (Nat.mul _16338 _16339)) (term53 _16337 _16339)). Qed.
Lemma lem1007359 (_16336 : nat) (_16338 : nat) : (term54 _16336 _16338) = (term54 _16336 _16338).
Proof. exact (eq_refl (term54 _16336 _16338)). Qed.
Lemma lem1007360 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : (term42 _16336 _16337 _16338 _16339) = (term55 _16336 _16338 _16337 _16339).
Proof. exact (MK_COMB (@lem1007359 _16336 _16338) (@lem1007349 _16336 _16338 _16337 _16339)). Qed.
Lemma lem1007364 (q : Prop) (p : Prop) (r : Prop) : (term56 p q r) = (term56 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1007365 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : (term55 _16336 _16338 _16337 _16339) = (term57 _16336 _16338 _16337 _16339).
Proof. exact (@lem1007364 ((Nat.mul _16336 _16337) = (Nat.mul _16338 _16339)) (term53 _16336 _16338) (term53 _16337 _16339)). Qed.
Lemma lem1007387 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : (term42 _16336 _16337 _16338 _16339) = (term57 _16336 _16338 _16337 _16339).
Proof. exact (TRANS (@lem1007360 _16336 _16338 _16337 _16339) (@lem1007365 _16336 _16338 _16337 _16339)). Qed.
Lemma lem1007388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1007389 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : (term58 _16336 _16337 _16338 _16339) = (term59 _16336 _16338 _16337 _16339).
Proof. exact (MK_COMB (@lem1007388) (@lem1007387 _16336 _16338 _16337 _16339)). Qed.
Lemma lem1007411 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : (term57 _16336 _16338 _16337 _16339) = (term57 _16336 _16338 _16337 _16339).
Proof. exact (eq_refl (term57 _16336 _16338 _16337 _16339)). Qed.
Lemma lem1007412 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : ((term42 _16336 _16337 _16338 _16339) = (term57 _16336 _16338 _16337 _16339)) = ((term57 _16336 _16338 _16337 _16339) = (term57 _16336 _16338 _16337 _16339)).
Proof. exact (MK_COMB (@lem1007389 _16336 _16338 _16337 _16339) (@lem1007411 _16336 _16338 _16337 _16339)). Qed.
Lemma lem1007414 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1007415 (x : Prop) : (x = x) = True.
Proof. exact (@lem1007414 Prop x). Qed.
Lemma lem1007416 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : ((term57 _16336 _16338 _16337 _16339) = (term57 _16336 _16338 _16337 _16339)) = True.
Proof. exact (@lem1007415 (term57 _16336 _16338 _16337 _16339)). Qed.
Lemma lem1007417 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : ((term42 _16336 _16337 _16338 _16339) = (term57 _16336 _16338 _16337 _16339)) = True.
Proof. exact (TRANS (@lem1007412 _16336 _16338 _16337 _16339) (@lem1007416 _16336 _16338 _16337 _16339)). Qed.
Lemma lem1007418 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : True = ((term42 _16336 _16337 _16338 _16339) = (term57 _16336 _16338 _16337 _16339)).
Proof. exact (SYM (@lem1007417 _16336 _16338 _16337 _16339)). Qed.
Lemma lem1007419 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : (term42 _16336 _16337 _16338 _16339) = (term57 _16336 _16338 _16337 _16339).
Proof. exact (EQ_MP (@lem1007418 _16336 _16338 _16337 _16339) (@lem0)). Qed.
Lemma lem1007420 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : term57 _16336 _16338 _16337 _16339.
Proof. exact (EQ_MP (@lem1007419 _16336 _16338 _16337 _16339) (@lem1007297 _16336 _16337 _16338 _16339)). Qed.
Lemma lem1007422 (b : Prop) (a : Prop) : (a \/ b) = (term60 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1007423 (_16336 : nat) (_16337 : nat) (_16338 : nat) (_16339 : nat) : (term57 _16336 _16338 _16337 _16339) = (term61 _16336 _16337 _16338 _16339).
Proof. exact (@lem1007422 (term62 _16336 _16338 _16337 _16339) ((Nat.mul _16336 _16337) = (Nat.mul _16338 _16339))). Qed.
Lemma lem1007425 (a : Prop) (b : Prop) : (term63 a b) = (term64 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1007426 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : (term65 _16336 _16338 _16337 _16339) = (term66 _16336 _16338 _16337 _16339).
Proof. exact (@lem1007425 (term53 _16336 _16338) (term53 _16337 _16339)). Qed.
Lemma lem1007428 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1007429 (_16336 : nat) (_16338 : nat) : (term68 _16336 _16338) = (_16336 = _16338).
Proof. exact (@lem1007428 (_16336 = _16338)). Qed.
Lemma lem1007430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1007431 (_16336 : nat) (_16338 : nat) : (term69 _16336 _16338) = (term70 _16336 _16338).
Proof. exact (MK_COMB (@lem1007430) (@lem1007429 _16336 _16338)). Qed.
Lemma lem1007433 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1007434 (_16337 : nat) (_16339 : nat) : (term68 _16337 _16339) = (_16337 = _16339).
Proof. exact (@lem1007433 (_16337 = _16339)). Qed.
Lemma lem1007435 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : (term66 _16336 _16338 _16337 _16339) = (term71 _16336 _16338 _16337 _16339).
Proof. exact (MK_COMB (@lem1007431 _16336 _16338) (@lem1007434 _16337 _16339)). Qed.
Lemma lem1007436 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : (term65 _16336 _16338 _16337 _16339) = (term71 _16336 _16338 _16337 _16339).
Proof. exact (TRANS (@lem1007426 _16336 _16338 _16337 _16339) (@lem1007435 _16336 _16338 _16337 _16339)). Qed.
Lemma lem1007437 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1007438 (_16336 : nat) (_16338 : nat) (_16337 : nat) (_16339 : nat) : (term72 _16336 _16338 _16337 _16339) = (term73 _16336 _16338 _16337 _16339).
Proof. exact (MK_COMB (@lem1007437) (@lem1007436 _16336 _16338 _16337 _16339)). Qed.
Lemma lem1007439 (_16336 : nat) (_16337 : nat) (_16338 : nat) (_16339 : nat) : ((Nat.mul _16336 _16337) = (Nat.mul _16338 _16339)) = ((Nat.mul _16336 _16337) = (Nat.mul _16338 _16339)).
Proof. exact (eq_refl ((Nat.mul _16336 _16337) = (Nat.mul _16338 _16339))). Qed.
Lemma lem1007440 (_16336 : nat) (_16337 : nat) (_16338 : nat) (_16339 : nat) : (term61 _16336 _16337 _16338 _16339) = (term74 _16336 _16337 _16338 _16339).
Proof. exact (MK_COMB (@lem1007438 _16336 _16338 _16337 _16339) (@lem1007439 _16336 _16337 _16338 _16339)). Qed.
Lemma lem1007441 (_16336 : nat) (_16337 : nat) (_16338 : nat) (_16339 : nat) : (term57 _16336 _16338 _16337 _16339) = (term74 _16336 _16337 _16338 _16339).
Proof. exact (TRANS (@lem1007423 _16336 _16337 _16338 _16339) (@lem1007440 _16336 _16337 _16338 _16339)). Qed.
Lemma lem1007443 (m : nat) (n : nat) (h1 : term10) : term75 m n.
Proof. exact (conj (@lem1007322 m h1) (@lem1007330 n h1)). Qed.
Lemma lem1007445 (_16336 : nat) (_16337 : nat) (_16338 : nat) (_16339 : nat) : term74 _16336 _16337 _16338 _16339.
Proof. exact (EQ_MP (@lem1007441 _16336 _16337 _16338 _16339) (@lem1007420 _16336 _16338 _16337 _16339)). Qed.
Lemma lem1007446 (m : nat) (n : nat) : term76 m n.
Proof. exact (@lem1007445 (NUMERAL m) (NUMERAL n) m n). Qed.
Lemma lem1007449 (m : nat) (n : nat) (h1 : term10) : (term1 m n) = (Nat.mul m n).
Proof. exact (@lem1007446 m n (@lem1007443 m n h1)). Qed.
Lemma lem1007450 (m : nat) (n : nat) (h1 : term10) : term77 m n.
Proof. exact (fun h0 : term78 m n => @lem1007449 m n h1). Qed.
Lemma lem1007452 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1007453 (m : nat) (n : nat) : (term77 m n) = ((term1 m n) = (Nat.mul m n)).
Proof. exact (@lem1007452 ((term1 m n) = (Nat.mul m n))). Qed.
Lemma lem1007454 (m : nat) (n : nat) (h1 : term10) : (term1 m n) = (Nat.mul m n).
Proof. exact (EQ_MP (@lem1007453 m n) (@lem1007450 m n h1)). Qed.
Lemma lem1007472 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1007473 (y : nat) (x : nat) (z : nat) : (term89 x y z) = (term90 y x z).
Proof. exact (@lem1007472 (y = z) (term53 x z)). Qed.
Lemma lem1007483 (x : nat) (y : nat) : (term54 x y) = (term54 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1007484 (y : nat) (x : nat) (z : nat) : (term45 x y z) = (term91 y x z).
Proof. exact (MK_COMB (@lem1007483 x y) (@lem1007473 y x z)). Qed.
Lemma lem1007488 (q : Prop) (p : Prop) (r : Prop) : (term56 p q r) = (term56 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1007489 (y : nat) (x : nat) (z : nat) : (term91 y x z) = (term92 y x z).
Proof. exact (@lem1007488 (y = z) (term53 x y) (term53 x z)). Qed.
Lemma lem1007511 (y : nat) (x : nat) (z : nat) : (term45 x y z) = (term92 y x z).
Proof. exact (TRANS (@lem1007484 y x z) (@lem1007489 y x z)). Qed.
Lemma lem1007512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1007513 (y : nat) (x : nat) (z : nat) : (term93 x y z) = (term94 y x z).
Proof. exact (MK_COMB (@lem1007512) (@lem1007511 y x z)). Qed.
Lemma lem1007535 (y : nat) (x : nat) (z : nat) : (term92 y x z) = (term92 y x z).
Proof. exact (eq_refl (term92 y x z)). Qed.
Lemma lem1007536 (y : nat) (x : nat) (z : nat) : ((term45 x y z) = (term92 y x z)) = ((term92 y x z) = (term92 y x z)).
Proof. exact (MK_COMB (@lem1007513 y x z) (@lem1007535 y x z)). Qed.
Lemma lem1007538 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1007539 (x : Prop) : (x = x) = True.
Proof. exact (@lem1007538 Prop x). Qed.
Lemma lem1007540 (y : nat) (x : nat) (z : nat) : ((term92 y x z) = (term92 y x z)) = True.
Proof. exact (@lem1007539 (term92 y x z)). Qed.
Lemma lem1007541 (y : nat) (x : nat) (z : nat) : ((term45 x y z) = (term92 y x z)) = True.
Proof. exact (TRANS (@lem1007536 y x z) (@lem1007540 y x z)). Qed.
Lemma lem1007542 (y : nat) (x : nat) (z : nat) : True = ((term45 x y z) = (term92 y x z)).
Proof. exact (SYM (@lem1007541 y x z)). Qed.
Lemma lem1007543 (y : nat) (x : nat) (z : nat) : (term45 x y z) = (term92 y x z).
Proof. exact (EQ_MP (@lem1007542 y x z) (@lem0)). Qed.
Lemma lem1007544 (y : nat) (x : nat) (z : nat) : term92 y x z.
Proof. exact (EQ_MP (@lem1007543 y x z) (@lem1007307 x y z)). Qed.
Lemma lem1007546 (b : Prop) (a : Prop) : (a \/ b) = (term60 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1007547 (x : nat) (y : nat) (z : nat) : (term92 y x z) = (term95 x y z).
Proof. exact (@lem1007546 (term96 y x z) (y = z)). Qed.
Lemma lem1007549 (a : Prop) (b : Prop) : (term63 a b) = (term64 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1007550 (y : nat) (x : nat) (z : nat) : (term97 y x z) = (term98 y x z).
Proof. exact (@lem1007549 (term53 x y) (term53 x z)). Qed.
Lemma lem1007552 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1007553 (x : nat) (y : nat) : (term68 x y) = (x = y).
Proof. exact (@lem1007552 (x = y)). Qed.
Lemma lem1007554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1007555 (x : nat) (y : nat) : (term69 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1007554) (@lem1007553 x y)). Qed.
Lemma lem1007557 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1007558 (x : nat) (z : nat) : (term68 x z) = (x = z).
Proof. exact (@lem1007557 (x = z)). Qed.
Lemma lem1007559 (y : nat) (x : nat) (z : nat) : (term98 y x z) = (term99 y x z).
Proof. exact (MK_COMB (@lem1007555 x y) (@lem1007558 x z)). Qed.
Lemma lem1007560 (y : nat) (x : nat) (z : nat) : (term97 y x z) = (term99 y x z).
Proof. exact (TRANS (@lem1007550 y x z) (@lem1007559 y x z)). Qed.
Lemma lem1007561 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1007562 (y : nat) (x : nat) (z : nat) : (term100 y x z) = (term101 y x z).
Proof. exact (MK_COMB (@lem1007561) (@lem1007560 y x z)). Qed.
Lemma lem1007563 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1007564 (x : nat) (y : nat) (z : nat) : (term95 x y z) = (term102 x y z).
Proof. exact (MK_COMB (@lem1007562 y x z) (@lem1007563 y z)). Qed.
Lemma lem1007565 (x : nat) (y : nat) (z : nat) : (term92 y x z) = (term102 x y z).
Proof. exact (TRANS (@lem1007547 x y z) (@lem1007564 x y z)). Qed.
Lemma lem1007567 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : term109 p m n.
Proof. exact (conj (@lem1007314 m n p h2) (@lem1007454 m n h1)). Qed.
Lemma lem1007569 (x : nat) (y : nat) (z : nat) : term102 x y z.
Proof. exact (EQ_MP (@lem1007565 x y z) (@lem1007544 y x z)). Qed.
Lemma lem1007570 (p : nat) (m : nat) (n : nat) : term110 p m n.
Proof. exact (@lem1007569 (term1 m n) (NUMERAL p) (Nat.mul m n)). Qed.
Lemma lem1007573 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : (NUMERAL p) = (Nat.mul m n).
Proof. exact (@lem1007570 p m n (@lem1007567 m n p h1 h2)). Qed.
Lemma lem1007574 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : term111 p m n.
Proof. exact (fun h0 : term112 p m n => @lem1007573 m n p h1 h2). Qed.
Lemma lem1007576 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1007577 (p : nat) (m : nat) (n : nat) : (term111 p m n) = ((NUMERAL p) = (Nat.mul m n)).
Proof. exact (@lem1007576 ((NUMERAL p) = (Nat.mul m n))). Qed.
Lemma lem1007578 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : (NUMERAL p) = (Nat.mul m n).
Proof. exact (EQ_MP (@lem1007577 p m n) (@lem1007574 m n p h1 h2)). Qed.
Lemma lem1007580 (_16323 : nat) (h1 : term10) : (NUMERAL _16323) = _16323.
Proof. exact (EQ_MP (@lem1006854 _16323) (@lem1006853 _16323 h1)). Qed.
Lemma lem1007581 (p : nat) (h1 : term10) : (NUMERAL p) = p.
Proof. exact (@lem1007580 p h1). Qed.
Lemma lem1007582 (p : nat) (h1 : term10) : term50 p.
Proof. exact (fun h0 : term51 p => @lem1007581 p h1). Qed.
Lemma lem1007584 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1007585 (p : nat) : (term50 p) = ((NUMERAL p) = p).
Proof. exact (@lem1007584 ((NUMERAL p) = p)). Qed.
Lemma lem1007586 (p : nat) (h1 : term10) : (NUMERAL p) = p.
Proof. exact (EQ_MP (@lem1007585 p) (@lem1007582 p h1)). Qed.
Lemma lem1007587 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : term113 m n p.
Proof. exact (conj (@lem1007578 m n p h1 h2) (@lem1007586 p h1)). Qed.
Lemma lem1007589 (x : nat) (y : nat) (z : nat) : term102 x y z.
Proof. exact (EQ_MP (@lem1007565 x y z) (@lem1007544 y x z)). Qed.
Lemma lem1007590 (m : nat) (n : nat) (p : nat) : term114 m n p.
Proof. exact (@lem1007589 (NUMERAL p) (Nat.mul m n) p). Qed.
Lemma lem1007593 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : (Nat.mul m n) = p.
Proof. exact (@lem1007590 m n p (@lem1007587 m n p h1 h2)). Qed.
Lemma lem1007594 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : term115 m n p.
Proof. exact (fun h0 : term31 m n p => @lem1007593 m n p h1 h2). Qed.
Lemma lem1007596 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1007597 (m : nat) (n : nat) (p : nat) : (term115 m n p) = ((Nat.mul m n) = p).
Proof. exact (@lem1007596 ((Nat.mul m n) = p)). Qed.
Lemma lem1007598 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : (Nat.mul m n) = p.
Proof. exact (EQ_MP (@lem1007597 m n p) (@lem1007594 m n p h1 h2)). Qed.
Lemma lem1007601 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1007603 (m : nat) (n : nat) (p : nat) : (term31 m n p) = (term116 m n p).
Proof. exact (@lem1007601 ((Nat.mul m n) = p)). Qed.
Lemma lem1007606 (m : nat) (n : nat) (p : nat) (h1 : term28 m n p) : term116 m n p.
Proof. exact (EQ_MP (@lem1007603 m n p) (@lem1006865 m n p h1)). Qed.
Lemma lem1007609 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : False.
Proof. exact (@lem1007606 m n p h2 (@lem1007598 m n p h1 h2)). Qed.
Lemma lem1007610 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : term107.
Proof. exact (fun h0 : ~ False => @lem1007609 m n p h1 h2). Qed.
Lemma lem1007612 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1007613 : term107 = False.
Proof. exact (@lem1007612 False). Qed.
Lemma lem1007614 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : False.
Proof. exact (EQ_MP (@lem1007613) (@lem1007610 m n p h1 h2)). Qed.
Lemma lem1007615 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term27 m n p) : False.
Proof. exact (EQ_MP (@lem1007281) (@lem1007278 m n p h1 h2)). Qed.
Lemma lem1007616 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1007614 m n p h1 h2) (fun h3 : False => @lem1006841 h1)). Qed.
Lemma lem1007617 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : False.
Proof. exact (EQ_MP (@lem1007616 m n p h1 h2) (@lem1006841 h1)). Qed.
Lemma lem1007618 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term27 m n p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1007615 m n p h1 h2) (fun h3 : False => @lem1006826 h1)). Qed.
Lemma lem1007619 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term27 m n p) : False.
Proof. exact (EQ_MP (@lem1007618 m n p h1 h2) (@lem1006826 h1)). Qed.
Lemma lem1007620 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term3 m n p) : False.
Proof. exact (or_elim (@lem1006802 m n p h2) (fun h0 : term27 m n p => @lem1007619 m n p h1 h0) (fun h0 : term28 m n p => @lem1007617 m n p h1 h0)). Qed.
Lemma lem1007621 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term3 m n p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1007620 m n p h1 h2) (fun h3 : False => @lem1006813 h1)). Qed.
Lemma lem1007622 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term3 m n p) : False.
Proof. exact (EQ_MP (@lem1007621 m n p h1 h2) (@lem1006813 h1)). Qed.
Lemma lem1007623 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term3 m n p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1007622 m n p h1 h2) (fun h3 : False => @lem1006740 h1)). Qed.
Lemma lem1007624 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term3 m n p) : False.
Proof. exact (EQ_MP (@lem1007623 m n p h1 h2) (@lem1006740 h1)). Qed.
Lemma lem1007625 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : term8.
Proof. exact (fun h0 : term10 => @lem1007624 m n p h0 h1). Qed.
Lemma lem1007626 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1007627 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : term9.
Proof. exact (EQ_MP (@lem1007626) (@lem1007625 m n p h1)). Qed.
Lemma lem1007628 (m : nat) (n : nat) (p : nat) : term12 m n p.
Proof. exact (fun h0 : term3 m n p => @lem1007627 m n p h0). Qed.
Lemma lem1007633 (n : nat) (p : nat) : term16 n p.
Proof. exact (fun m : nat => @lem1007628 m n p). Qed.
Lemma lem1007638 (p : nat) : term20 p.
Proof. exact (fun n : nat => @lem1007633 n p). Qed.
Lemma lem1007643 : term24.
Proof. exact (fun p : nat => @lem1007638 p). Qed.
Lemma lem1007644 : term23.
Proof. exact (EQ_MP (@lem1006705) (@lem1007643)). Qed.
Lemma lem1007645 (p : nat) : term117 p.
Proof. exact (@lem1007644 p). Qed.
Lemma lem1007646 (p : nat) : (term117 p) = (term19 p).
Proof. exact (eq_refl (term117 p)). Qed.
Lemma lem1007647 (p : nat) : term19 p.
Proof. exact (EQ_MP (@lem1007646 p) (@lem1007645 p)). Qed.
Lemma lem1007648 (p : nat) (n : nat) : term118 p n.
Proof. exact (@lem1007647 p n). Qed.
Lemma lem1007649 (n : nat) (p : nat) : (term118 p n) = (term15 n p).
Proof. exact (eq_refl (term118 p n)). Qed.
Lemma lem1007650 (n : nat) (p : nat) : term15 n p.
Proof. exact (EQ_MP (@lem1007649 n p) (@lem1007648 p n)). Qed.
Lemma lem1007651 (n : nat) (p : nat) (m : nat) : term119 n p m.
Proof. exact (@lem1007650 n p m). Qed.
Lemma lem1007652 (m : nat) (n : nat) (p : nat) : (term119 n p m) = (term4 m n p).
Proof. exact (eq_refl (term119 n p m)). Qed.
Lemma lem1007653 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (EQ_MP (@lem1007652 m n p) (@lem1007651 n p m)). Qed.
Lemma lem1007655 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem1006600 m n p (@lem1007653 m n p)). Qed.
Lemma lem1007656 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : term8.
Proof. exact (@lem1007655 m n p (@lem1006585 m n p h1)). Qed.
Lemma lem1007657 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : False.
Proof. exact (@lem1007656 m n p h1 (@lem75543)). Qed.
Lemma lem1007658 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : (term3 m n p) = False.
Proof. exact (prop_ext (fun h2 : term3 m n p => @lem1007657 m n p h1) (fun h2 : False => @lem1006585 m n p h1)). Qed.
Lemma lem1007659 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : False.
Proof. exact (EQ_MP (@lem1007658 m n p h1) (@lem1006585 m n p h1)). Qed.
Lemma lem1007660 (m : nat) (n : nat) (p : nat) : term2 m n p.
Proof. exact (fun h0 : term3 m n p => @lem1007659 m n p h0). Qed.
Lemma lem1007663 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = p) = ((term1 m n) = (NUMERAL p)).
Proof. exact (EQ_MP (@lem1006584 m n p) (@lem1007660 m n p)). Qed.
