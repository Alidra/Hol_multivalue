Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUB_ELIM_THM_term_abbrevs.
Require Import ADD_SUB2_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import LE_ADD_spec.
Require Import LE_EXISTS_spec.
Require Import LTE_CASES_spec.
Require Import LT_IMP_LE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import NOT_LT_spec.
Require Import SUB_EQ_0_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm1844_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem250621 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem250622 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem250621 n m h1)). Qed.
Lemma lem250623 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem250624 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem250623 m n h1)). Qed.
Lemma lem250625 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem250622 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem250624 m n h1)). Qed.
Lemma lem250626 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem250625 m n)). Qed.
Lemma lem250627 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250628 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem250627) (@lem250626 m)). Qed.
Lemma lem250629 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem250628 m)). Qed.
Lemma lem250630 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250631 : term7 = term8.
Proof. exact (MK_COMB (@lem250630) (@lem250629)). Qed.
Lemma lem250632 : term8.
Proof. exact (EQ_MP (@lem250631) (@lem97961)). Qed.
Lemma lem250633 (m : nat) : term9 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem250634 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem250635 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem250634 m) (@lem250633 m)). Qed.
Lemma lem250636 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem250635 m n). Qed.
Lemma lem250637 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem250638 (m : nat) (n : nat) : term12 m n.
Proof. exact (EQ_MP (@lem250637 m n) (@lem250636 m n)). Qed.
Lemma lem250639 (m : nat) (n : nat) (p : nat) : term13 m n p.
Proof. exact (@lem250638 m n p). Qed.
Lemma lem250640 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term13 m n p)). Qed.
Lemma lem250642 (m : nat) : term14 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem250643 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem250644 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem250643 m) (@lem250642 m)). Qed.
Lemma lem250645 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem250644 m n). Qed.
Lemma lem250646 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem250647 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem250646 m n) (@lem250645 m n)). Qed.
Lemma lem250648 (m : nat) (n : nat) : (term17 m n) = ((term17 m n) = True).
Proof. exact (@lem7 (term17 m n)). Qed.
Lemma lem250650 (m : nat) : term18 m.
Proof. exact (@lem250632 m). Qed.
Lemma lem250651 (m : nat) : (term18 m) = (term4 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem250652 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem250651 m) (@lem250650 m)). Qed.
Lemma lem250653 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem250652 m n). Qed.
Lemma lem250654 (m : nat) (n : nat) : (term19 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem250656 (m : nat) : term20 m.
Proof. exact (@lem135939 m). Qed.
Lemma lem250657 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem250658 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem250657 m) (@lem250656 m)). Qed.
Lemma lem250659 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem250658 m n). Qed.
Lemma lem250660 (m : nat) (n : nat) : (term22 m n) = ((term23 n m) = n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem250662 (m : nat) : term24 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem250663 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem250664 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem250663 m) (@lem250662 m)). Qed.
Lemma lem250665 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem250664 m n). Qed.
Lemma lem250666 (n : nat) (m : nat) : (term26 m n) = ((Peano.le m n) = (term27 n m)).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem250668 (t1 : Prop) : term28 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem250669 (t1 : Prop) : (term28 t1) = (term29 t1).
Proof. exact (eq_refl (term28 t1)). Qed.
Lemma lem250670 (t1 : Prop) : term29 t1.
Proof. exact (EQ_MP (@lem250669 t1) (@lem250668 t1)). Qed.
Lemma lem250671 (t1 : Prop) (t2 : Prop) : term30 t1 t2.
Proof. exact (@lem250670 t1 t2). Qed.
Lemma lem250672 (t1 : Prop) (t2 : Prop) : (term30 t1 t2) = (term31 t1 t2).
Proof. exact (eq_refl (term30 t1 t2)). Qed.
Lemma lem250673 (t1 : Prop) (t2 : Prop) : term31 t1 t2.
Proof. exact (EQ_MP (@lem250672 t1 t2) (@lem250671 t1 t2)). Qed.
Lemma lem250674 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term32 t1 t2 t3.
Proof. exact (@lem250673 t1 t2 t3). Qed.
Lemma lem250675 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term32 t1 t2 t3) = ((term33 t1 t2 t3) = (term34 t1 t2 t3)).
Proof. exact (eq_refl (term32 t1 t2 t3)). Qed.
Lemma lem250676 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term33 t1 t2 t3) = (term34 t1 t2 t3).
Proof. exact (EQ_MP (@lem250675 t1 t2 t3) (@lem250674 t1 t2 t3)). Qed.
Lemma lem250677 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term34 t1 t2 t3) = (term33 t1 t2 t3).
Proof. exact (SYM (@lem250676 t1 t2 t3)). Qed.
Lemma lem250678 (a : nat) : term35 a.
Proof. exact (@lem96963 a). Qed.
Lemma lem250679 (a : nat) : (term35 a) = (term36 a).
Proof. exact (eq_refl (term35 a)). Qed.
Lemma lem250680 (a : nat) : term36 a.
Proof. exact (EQ_MP (@lem250679 a) (@lem250678 a)). Qed.
Lemma lem250681 (a : nat) (b : nat) : term37 a b.
Proof. exact (@lem250680 a b). Qed.
Lemma lem250682 (b : nat) (a : nat) : (term37 a b) = (term38 b a).
Proof. exact (eq_refl (term37 a b)). Qed.
Lemma lem250683 (b : nat) (a : nat) : term38 b a.
Proof. exact (EQ_MP (@lem250682 b a) (@lem250681 a b)). Qed.
Lemma lem250684 (a : nat) (b : nat) (h1 : Peano.lt a b) : Peano.lt a b.
Proof. exact (h1). Qed.
Lemma lem250685 (b : nat) (a : nat) (h1 : Peano.le b a) : Peano.le b a.
Proof. exact (h1). Qed.
Lemma lem250687 (p : Prop) : p = (term39 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem250688 (a : nat) (b : nat) (P : nat -> Prop) : ((term40 P a b) = (term41 a b P)) = (term42 a b P).
Proof. exact (@lem250687 ((term40 P a b) = (term41 a b P))). Qed.
Lemma lem250689 (a : nat) (b : nat) (P : nat -> Prop) : (term42 a b P) = ((term40 P a b) = (term41 a b P)).
Proof. exact (SYM (@lem250688 a b P)). Qed.
Lemma lem250690 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term43 a b P) : term43 a b P.
Proof. exact (h1). Qed.
Lemma lem250693 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term44 a b P) : term44 a b P.
Proof. exact (h1). Qed.
Lemma lem250694 (a : nat) (b : nat) (P : nat -> Prop) : term45 a b P.
Proof. exact (fun h0 : term44 a b P => @lem250693 a b P h0). Qed.
Lemma lem250695 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term45 a b P) : term45 a b P.
Proof. exact (h1). Qed.
Lemma lem250696 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term44 a b P) : term44 a b P.
Proof. exact (h1). Qed.
Lemma lem250697 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term44 a b P) (h2 : term45 a b P) : term44 a b P.
Proof. exact (@lem250695 a b P h2 (@lem250696 a b P h1)). Qed.
Lemma lem250698 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term44 a b P) : term46 a b P.
Proof. exact (fun h0 : term45 a b P => @lem250697 a b P h1 h0). Qed.
Lemma lem250699 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term45 a b P) : term45 a b P.
Proof. exact (h1). Qed.
Lemma lem250700 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term44 a b P) (h2 : term45 a b P) : term44 a b P.
Proof. exact (@lem250698 a b P h1 (@lem250699 a b P h2)). Qed.
Lemma lem250701 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term45 a b P) : term45 a b P.
Proof. exact (fun h0 : term44 a b P => @lem250700 a b P h0 h1). Qed.
Lemma lem250702 (a : nat) (b : nat) (P : nat -> Prop) : term47 a b P.
Proof. exact (fun h0 : term45 a b P => @lem250701 a b P h0). Qed.
Lemma lem250705 (a : nat) (b : nat) (P : nat -> Prop) : term45 a b P.
Proof. exact (@lem250702 a b P (@lem250694 a b P)). Qed.
Lemma lem250765 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem250766 : term48 = term49.
Proof. exact (@lem250765 term50). Qed.
Lemma lem250775 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem250776 : term52 = term53.
Proof. exact (MK_COMB (@lem250775) (@lem250766)). Qed.
Lemma lem250779 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem250780 : term55 = term56.
Proof. exact (MK_COMB (@lem250779) (@lem250776)). Qed.
Lemma lem250783 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem250784 : term58 = term59.
Proof. exact (MK_COMB (@lem250783) (@lem250780)). Qed.
Lemma lem250787 (a : nat) (b : nat) (P : nat -> Prop) : (term60 a b P) = (term60 a b P).
Proof. exact (eq_refl (term60 a b P)). Qed.
Lemma lem250788 (a : nat) (b : nat) (P : nat -> Prop) : (term61 a b P) = (term62 a b P).
Proof. exact (MK_COMB (@lem250787 a b P) (@lem250784)). Qed.
Lemma lem250791 (a : nat) (b : nat) : (term63 a b) = (term63 a b).
Proof. exact (eq_refl (term63 a b)). Qed.
Lemma lem250792 (a : nat) (b : nat) (P : nat -> Prop) : (term44 a b P) = (term64 a b P).
Proof. exact (MK_COMB (@lem250791 a b) (@lem250788 a b P)). Qed.
Lemma lem250795 (b : nat) (P : nat -> Prop) : (term65 b P) = (term66 b P).
Proof. exact (fun_ext (fun a : nat => @lem250792 a b P)). Qed.
Lemma lem250796 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250797 (b : nat) (P : nat -> Prop) : (term67 b P) = (term68 b P).
Proof. exact (MK_COMB (@lem250796) (@lem250795 b P)). Qed.
Lemma lem250802 (P : nat -> Prop) : (term69 P) = (term70 P).
Proof. exact (fun_ext (fun b : nat => @lem250797 b P)). Qed.
Lemma lem250803 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250804 (P : nat -> Prop) : (term71 P) = (term72 P).
Proof. exact (MK_COMB (@lem250803) (@lem250802 P)). Qed.
Lemma lem250809 : term73 = term74.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem250804 P)). Qed.
Lemma lem250810 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem250819 : term75 = term76.
Proof. exact (MK_COMB (@lem250810) (@lem250809)). Qed.
Lemma lem250826 (n : nat) (m : nat) : ((term77 m n) = (Peano.le n m)) = ((term77 m n) = (Peano.le n m)).
Proof. exact (eq_refl ((term77 m n) = (Peano.le n m))). Qed.
Lemma lem250827 (m : nat) : (term78 m) = (term78 m).
Proof. exact (fun_ext (fun n : nat => @lem250826 n m)). Qed.
Lemma lem250828 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250829 (m : nat) : (term79 m) = (term79 m).
Proof. exact (MK_COMB (@lem250828) (@lem250827 m)). Qed.
Lemma lem250830 : term80 = term80.
Proof. exact (fun_ext (fun m : nat => @lem250829 m)). Qed.
Lemma lem250831 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250832 : term50 = term50.
Proof. exact (MK_COMB (@lem250831) (@lem250830)). Qed.
Lemma lem250833 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem250834 : term49 = term49.
Proof. exact (MK_COMB (@lem250833) (@lem250832)). Qed.
Lemma lem250839 (m : nat) (n : nat) : (((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n)) = (((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n)).
Proof. exact (eq_refl (((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n))). Qed.
Lemma lem250840 (m : nat) : (term81 m) = (term81 m).
Proof. exact (fun_ext (fun n : nat => @lem250839 m n)). Qed.
Lemma lem250841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250842 (m : nat) : (term82 m) = (term82 m).
Proof. exact (MK_COMB (@lem250841) (@lem250840 m)). Qed.
Lemma lem250843 : term83 = term83.
Proof. exact (fun_ext (fun m : nat => @lem250842 m)). Qed.
Lemma lem250844 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250845 : term84 = term84.
Proof. exact (MK_COMB (@lem250844) (@lem250843)). Qed.
Lemma lem250846 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem250847 : term51 = term51.
Proof. exact (MK_COMB (@lem250846) (@lem250845)). Qed.
Lemma lem250848 : term53 = term53.
Proof. exact (MK_COMB (@lem250847) (@lem250834)). Qed.
Lemma lem250853 (m : nat) (n : nat) : (term85 m n) = (term85 m n).
Proof. exact (eq_refl (term85 m n)). Qed.
Lemma lem250854 (m : nat) : (term86 m) = (term86 m).
Proof. exact (fun_ext (fun n : nat => @lem250853 m n)). Qed.
Lemma lem250855 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250856 (m : nat) : (term87 m) = (term87 m).
Proof. exact (MK_COMB (@lem250855) (@lem250854 m)). Qed.
Lemma lem250857 : term88 = term88.
Proof. exact (fun_ext (fun m : nat => @lem250856 m)). Qed.
Lemma lem250858 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250859 : term89 = term89.
Proof. exact (MK_COMB (@lem250858) (@lem250857)). Qed.
Lemma lem250860 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem250861 : term54 = term54.
Proof. exact (MK_COMB (@lem250860) (@lem250859)). Qed.
Lemma lem250862 : term56 = term56.
Proof. exact (MK_COMB (@lem250861) (@lem250848)). Qed.
Lemma lem250863 (m : nat) (n : nat) : (term17 m n) = (term17 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem250864 (m : nat) : (term90 m) = (term90 m).
Proof. exact (fun_ext (fun n : nat => @lem250863 m n)). Qed.
Lemma lem250865 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250866 (m : nat) : (term15 m) = (term15 m).
Proof. exact (MK_COMB (@lem250865) (@lem250864 m)). Qed.
Lemma lem250867 : term91 = term91.
Proof. exact (fun_ext (fun m : nat => @lem250866 m)). Qed.
Lemma lem250868 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250869 : term92 = term92.
Proof. exact (MK_COMB (@lem250868) (@lem250867)). Qed.
Lemma lem250870 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem250871 : term57 = term57.
Proof. exact (MK_COMB (@lem250870) (@lem250869)). Qed.
Lemma lem250872 : term59 = term59.
Proof. exact (MK_COMB (@lem250871) (@lem250862)). Qed.
Lemma lem250885 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term93 a b P d) = (term93 a b P d).
Proof. exact (eq_refl (term93 a b P d)). Qed.
Lemma lem250886 (a : nat) (b : nat) (P : nat -> Prop) : (term94 a b P) = (term94 a b P).
Proof. exact (fun_ext (fun d : nat => @lem250885 a b P d)). Qed.
Lemma lem250887 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250888 (a : nat) (b : nat) (P : nat -> Prop) : (term41 a b P) = (term41 a b P).
Proof. exact (MK_COMB (@lem250887) (@lem250886 a b P)). Qed.
Lemma lem250891 (P : nat -> Prop) (a : nat) (b : nat) : (term95 P a b) = (term95 P a b).
Proof. exact (eq_refl (term95 P a b)). Qed.
Lemma lem250892 (a : nat) (b : nat) (P : nat -> Prop) : ((term40 P a b) = (term41 a b P)) = ((term40 P a b) = (term41 a b P)).
Proof. exact (MK_COMB (@lem250891 P a b) (@lem250888 a b P)). Qed.
Lemma lem250893 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem250894 (a : nat) (b : nat) (P : nat -> Prop) : (term43 a b P) = (term43 a b P).
Proof. exact (MK_COMB (@lem250893) (@lem250892 a b P)). Qed.
Lemma lem250895 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem250896 (a : nat) (b : nat) (P : nat -> Prop) : (term60 a b P) = (term60 a b P).
Proof. exact (MK_COMB (@lem250895) (@lem250894 a b P)). Qed.
Lemma lem250897 (a : nat) (b : nat) (P : nat -> Prop) : (term62 a b P) = (term62 a b P).
Proof. exact (MK_COMB (@lem250896 a b P) (@lem250872)). Qed.
Lemma lem250900 (a : nat) (b : nat) : (term63 a b) = (term63 a b).
Proof. exact (eq_refl (term63 a b)). Qed.
Lemma lem250901 (a : nat) (b : nat) (P : nat -> Prop) : (term64 a b P) = (term64 a b P).
Proof. exact (MK_COMB (@lem250900 a b) (@lem250897 a b P)). Qed.
Lemma lem250902 (b : nat) (P : nat -> Prop) : (term66 b P) = (term66 b P).
Proof. exact (fun_ext (fun a : nat => @lem250901 a b P)). Qed.
Lemma lem250903 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250904 (b : nat) (P : nat -> Prop) : (term68 b P) = (term68 b P).
Proof. exact (MK_COMB (@lem250903) (@lem250902 b P)). Qed.
Lemma lem250905 (P : nat -> Prop) : (term70 P) = (term70 P).
Proof. exact (fun_ext (fun b : nat => @lem250904 b P)). Qed.
Lemma lem250906 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem250907 (P : nat -> Prop) : (term72 P) = (term72 P).
Proof. exact (MK_COMB (@lem250906) (@lem250905 P)). Qed.
Lemma lem250908 : term74 = term74.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem250907 P)). Qed.
Lemma lem250909 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem250910 : term76 = term76.
Proof. exact (MK_COMB (@lem250909) (@lem250908)). Qed.
Lemma lem251003 : term75 = term76.
Proof. exact (TRANS (@lem250819) (@lem250910)). Qed.
Lemma lem251004 : term76 = term75.
Proof. exact (SYM (@lem251003)). Qed.
Lemma lem251006 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term43 a b P) : term43 a b P.
Proof. exact (h1). Qed.
Lemma lem251007 (h1 : term92) : term92.
Proof. exact (h1). Qed.
Lemma lem251008 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem251009 (h1 : term84) : term84.
Proof. exact (h1). Qed.
Lemma lem251010 (h1 : term50) : term50.
Proof. exact (h1). Qed.
Lemma lem251016 (a : nat) (b : nat) (h1 : Peano.lt a b) : Peano.lt a b.
Proof. exact (h1). Qed.
Lemma lem251029 (a : nat) (b : nat) (d : nat) : (term96 a b d) = (term97 a b d).
Proof. exact (@lem17045 (Peano.lt a b) (d = (NUMERAL 0))). Qed.
Lemma lem251034 (a : nat) (b : nat) (d : nat) : (term98 a b d) = (term98 a b d).
Proof. exact (eq_refl (term98 a b d)). Qed.
Lemma lem251035 (a : nat) (b : nat) (d : nat) : (term99 a b d) = (term100 a b d).
Proof. exact (MK_COMB (@lem251034 a b d) (@lem251029 a b d)). Qed.
Lemma lem251036 (a : nat) (b : nat) (d : nat) : (term101 a b d) = (term99 a b d).
Proof. exact (@lem17160 (a = (Nat.add b d)) (term102 a b d)). Qed.
Lemma lem251037 (a : nat) (b : nat) (d : nat) : (term101 a b d) = (term100 a b d).
Proof. exact (TRANS (@lem251036 a b d) (@lem251035 a b d)). Qed.
Lemma lem251042 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem251047 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term103 a b P d) = (term104 a b P d).
Proof. exact (@lem17362 (term105 a b d) (P d)). Qed.
Lemma lem251048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem251049 (a : nat) (b : nat) (d : nat) : (term106 a b d) = (term107 a b d).
Proof. exact (MK_COMB (@lem251048) (@lem251037 a b d)). Qed.
Lemma lem251050 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term108 a b P d) = (term109 a b P d).
Proof. exact (MK_COMB (@lem251049 a b d) (@lem251042 P d)). Qed.
Lemma lem251051 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term93 a b P d) = (term108 a b P d).
Proof. exact (@lem17265 (term105 a b d) (P d)). Qed.
Lemma lem251052 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term93 a b P d) = (term109 a b P d).
Proof. exact (TRANS (@lem251051 a b P d) (@lem251050 a b P d)). Qed.
Lemma lem251053 (P : nat -> Prop) : (term110 P) = (term111 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem251054 (a : nat) (b : nat) (P : nat -> Prop) : (term112 a b P) = (term113 a b P).
Proof. exact (@lem251053 (term94 a b P)). Qed.
Lemma lem251055 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term114 a b P d) = (term93 a b P d).
Proof. exact (eq_refl (term114 a b P d)). Qed.
Lemma lem251056 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem251057 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term115 a b P d) = (term103 a b P d).
Proof. exact (MK_COMB (@lem251056) (@lem251055 a b P d)). Qed.
Lemma lem251058 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term115 a b P d) = (term104 a b P d).
Proof. exact (TRANS (@lem251057 a b P d) (@lem251047 a b P d)). Qed.
Lemma lem251059 (a : nat) (b : nat) (P : nat -> Prop) : (term116 a b P) = (term117 a b P).
Proof. exact (fun_ext (fun d : nat => @lem251058 a b P d)). Qed.
Lemma lem251060 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem251061 (a : nat) (b : nat) (P : nat -> Prop) : (term113 a b P) = (term118 a b P).
Proof. exact (MK_COMB (@lem251060) (@lem251059 a b P)). Qed.
Lemma lem251062 (a : nat) (b : nat) (P : nat -> Prop) : (term112 a b P) = (term118 a b P).
Proof. exact (TRANS (@lem251054 a b P) (@lem251061 a b P)). Qed.
Lemma lem251063 (a : nat) (b : nat) (P : nat -> Prop) : (term94 a b P) = (term119 a b P).
Proof. exact (fun_ext (fun d : nat => @lem251052 a b P d)). Qed.
Lemma lem251064 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251065 (a : nat) (b : nat) (P : nat -> Prop) : (term41 a b P) = (term120 a b P).
Proof. exact (MK_COMB (@lem251064) (@lem251063 a b P)). Qed.
Lemma lem251067 (P : nat -> Prop) (a : nat) (b : nat) : (term121 P a b) = (term121 P a b).
Proof. exact (eq_refl (term121 P a b)). Qed.
Lemma lem251068 (a : nat) (b : nat) (P : nat -> Prop) : (term122 a b P) = (term123 a b P).
Proof. exact (MK_COMB (@lem251067 P a b) (@lem251065 a b P)). Qed.
Lemma lem251070 (P : nat -> Prop) (a : nat) (b : nat) : (term124 P a b) = (term124 P a b).
Proof. exact (eq_refl (term124 P a b)). Qed.
Lemma lem251071 (a : nat) (b : nat) (P : nat -> Prop) : (term125 a b P) = (term126 a b P).
Proof. exact (MK_COMB (@lem251070 P a b) (@lem251062 a b P)). Qed.
Lemma lem251072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem251073 (a : nat) (b : nat) (P : nat -> Prop) : (term127 a b P) = (term128 a b P).
Proof. exact (MK_COMB (@lem251072) (@lem251071 a b P)). Qed.
Lemma lem251074 (a : nat) (b : nat) (P : nat -> Prop) : (term129 a b P) = (term130 a b P).
Proof. exact (MK_COMB (@lem251073 a b P) (@lem251068 a b P)). Qed.
Lemma lem251075 (a : nat) (b : nat) (P : nat -> Prop) : (term43 a b P) = (term129 a b P).
Proof. exact (@lem17646 (term40 P a b) (term41 a b P)). Qed.
Lemma lem251076 (a : nat) (b : nat) (P : nat -> Prop) : (term43 a b P) = (term130 a b P).
Proof. exact (TRANS (@lem251075 a b P) (@lem251074 a b P)). Qed.
Lemma lem251159 {A : Type'} (P : Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem251160 (P : Prop) (Q : nat -> Prop) : (term133 P Q) = (term134 P Q).
Proof. exact (@lem251159 nat P Q). Qed.
Lemma lem251161 (a : nat) (b : nat) (P : nat -> Prop) : (term135 a b P) = (term136 a b P).
Proof. exact (@lem251160 (term40 P a b) (term117 a b P)). Qed.
Lemma lem251162 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term137 a b P d) = (term104 a b P d).
Proof. exact (eq_refl (term137 a b P d)). Qed.
Lemma lem251163 (a : nat) (b : nat) (P : nat -> Prop) : (term138 a b P) = (term117 a b P).
Proof. exact (fun_ext (fun d : nat => @lem251162 a b P d)). Qed.
Lemma lem251164 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem251165 (a : nat) (b : nat) (P : nat -> Prop) : (term139 a b P) = (term118 a b P).
Proof. exact (MK_COMB (@lem251164) (@lem251163 a b P)). Qed.
Lemma lem251166 (P : nat -> Prop) (a : nat) (b : nat) : (term124 P a b) = (term124 P a b).
Proof. exact (eq_refl (term124 P a b)). Qed.
Lemma lem251167 (a : nat) (b : nat) (P : nat -> Prop) : (term135 a b P) = (term126 a b P).
Proof. exact (MK_COMB (@lem251166 P a b) (@lem251165 a b P)). Qed.
Lemma lem251168 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem251169 (a : nat) (b : nat) (P : nat -> Prop) : (term140 a b P) = (term141 a b P).
Proof. exact (MK_COMB (@lem251168) (@lem251167 a b P)). Qed.
Lemma lem251170 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term137 a b P d) = (term104 a b P d).
Proof. exact (eq_refl (term137 a b P d)). Qed.
Lemma lem251171 (P : nat -> Prop) (a : nat) (b : nat) : (term124 P a b) = (term124 P a b).
Proof. exact (eq_refl (term124 P a b)). Qed.
Lemma lem251172 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term142 a b P d) = (term143 a b P d).
Proof. exact (MK_COMB (@lem251171 P a b) (@lem251170 a b P d)). Qed.
Lemma lem251173 (a : nat) (b : nat) (P : nat -> Prop) : (term144 a b P) = (term145 a b P).
Proof. exact (fun_ext (fun d : nat => @lem251172 a b P d)). Qed.
Lemma lem251174 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem251175 (a : nat) (b : nat) (P : nat -> Prop) : (term136 a b P) = (term146 a b P).
Proof. exact (MK_COMB (@lem251174) (@lem251173 a b P)). Qed.
Lemma lem251176 (a : nat) (b : nat) (P : nat -> Prop) : ((term135 a b P) = (term136 a b P)) = ((term126 a b P) = (term146 a b P)).
Proof. exact (MK_COMB (@lem251169 a b P) (@lem251175 a b P)). Qed.
Lemma lem251177 (a : nat) (b : nat) (P : nat -> Prop) : (term126 a b P) = (term146 a b P).
Proof. exact (EQ_MP (@lem251176 a b P) (@lem251161 a b P)). Qed.
Lemma lem251178 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem251179 (a : nat) (b : nat) (P : nat -> Prop) : (term128 a b P) = (term147 a b P).
Proof. exact (MK_COMB (@lem251178) (@lem251177 a b P)). Qed.
Lemma lem251180 (a : nat) (b : nat) (P : nat -> Prop) : (term123 a b P) = (term123 a b P).
Proof. exact (eq_refl (term123 a b P)). Qed.
Lemma lem251181 (a : nat) (b : nat) (P : nat -> Prop) : (term130 a b P) = (term148 a b P).
Proof. exact (MK_COMB (@lem251179 a b P) (@lem251180 a b P)). Qed.
Lemma lem251183 {A : Type'} (P : A -> Prop) (Q : Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem251184 (P : nat -> Prop) (Q : Prop) : (term151 P Q) = (term152 P Q).
Proof. exact (@lem251183 nat P Q). Qed.
Lemma lem251185 (a : nat) (b : nat) (P : nat -> Prop) : (term153 a b P) = (term154 a b P).
Proof. exact (@lem251184 (term145 a b P) (term123 a b P)). Qed.
Lemma lem251186 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term155 a b P d) = (term143 a b P d).
Proof. exact (eq_refl (term155 a b P d)). Qed.
Lemma lem251187 (a : nat) (b : nat) (P : nat -> Prop) : (term156 a b P) = (term145 a b P).
Proof. exact (fun_ext (fun d : nat => @lem251186 a b P d)). Qed.
Lemma lem251188 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem251189 (a : nat) (b : nat) (P : nat -> Prop) : (term157 a b P) = (term146 a b P).
Proof. exact (MK_COMB (@lem251188) (@lem251187 a b P)). Qed.
Lemma lem251190 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem251191 (a : nat) (b : nat) (P : nat -> Prop) : (term158 a b P) = (term147 a b P).
Proof. exact (MK_COMB (@lem251190) (@lem251189 a b P)). Qed.
Lemma lem251192 (a : nat) (b : nat) (P : nat -> Prop) : (term123 a b P) = (term123 a b P).
Proof. exact (eq_refl (term123 a b P)). Qed.
Lemma lem251193 (a : nat) (b : nat) (P : nat -> Prop) : (term153 a b P) = (term148 a b P).
Proof. exact (MK_COMB (@lem251191 a b P) (@lem251192 a b P)). Qed.
Lemma lem251194 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem251195 (a : nat) (b : nat) (P : nat -> Prop) : (term159 a b P) = (term160 a b P).
Proof. exact (MK_COMB (@lem251194) (@lem251193 a b P)). Qed.
Lemma lem251196 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term155 a b P d) = (term143 a b P d).
Proof. exact (eq_refl (term155 a b P d)). Qed.
Lemma lem251197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem251198 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term161 a b P d) = (term162 a b P d).
Proof. exact (MK_COMB (@lem251197) (@lem251196 a b P d)). Qed.
Lemma lem251199 (a : nat) (b : nat) (P : nat -> Prop) : (term123 a b P) = (term123 a b P).
Proof. exact (eq_refl (term123 a b P)). Qed.
Lemma lem251200 (d : nat) (a : nat) (b : nat) (P : nat -> Prop) : (term163 d a b P) = (term164 d a b P).
Proof. exact (MK_COMB (@lem251198 a b P d) (@lem251199 a b P)). Qed.
Lemma lem251201 (a : nat) (b : nat) (P : nat -> Prop) : (term165 a b P) = (term166 a b P).
Proof. exact (fun_ext (fun d : nat => @lem251200 d a b P)). Qed.
Lemma lem251202 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem251203 (a : nat) (b : nat) (P : nat -> Prop) : (term154 a b P) = (term167 a b P).
Proof. exact (MK_COMB (@lem251202) (@lem251201 a b P)). Qed.
Lemma lem251204 (a : nat) (b : nat) (P : nat -> Prop) : ((term153 a b P) = (term154 a b P)) = ((term148 a b P) = (term167 a b P)).
Proof. exact (MK_COMB (@lem251195 a b P) (@lem251203 a b P)). Qed.
Lemma lem251205 (a : nat) (b : nat) (P : nat -> Prop) : (term148 a b P) = (term167 a b P).
Proof. exact (EQ_MP (@lem251204 a b P) (@lem251185 a b P)). Qed.
Lemma lem251207 (a : nat) (b : nat) (P : nat -> Prop) : (term130 a b P) = (term167 a b P).
Proof. exact (TRANS (@lem251181 a b P) (@lem251205 a b P)). Qed.
Lemma lem251208 (a : nat) (b : nat) (P : nat -> Prop) : (term43 a b P) = (term167 a b P).
Proof. exact (TRANS (@lem251076 a b P) (@lem251207 a b P)). Qed.
Lemma lem251209 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term43 a b P) : term167 a b P.
Proof. exact (EQ_MP (@lem251208 a b P) (@lem251006 a b P h1)). Qed.
Lemma lem251210 (m : nat) (n : nat) : (term17 m n) = (term17 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem251211 (m : nat) : (term90 m) = (term90 m).
Proof. exact (fun_ext (fun n : nat => @lem251210 m n)). Qed.
Lemma lem251212 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251213 (m : nat) : (term15 m) = (term15 m).
Proof. exact (MK_COMB (@lem251212) (@lem251211 m)). Qed.
Lemma lem251214 : term91 = term91.
Proof. exact (fun_ext (fun m : nat => @lem251213 m)). Qed.
Lemma lem251215 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251228 : term92 = term92.
Proof. exact (MK_COMB (@lem251215) (@lem251214)). Qed.
Lemma lem251229 (h1 : term92) : term92.
Proof. exact (EQ_MP (@lem251228) (@lem251007 h1)). Qed.
Lemma lem251236 (m : nat) (n : nat) : (term85 m n) = (term168 m n).
Proof. exact (@lem17265 (Peano.lt m n) (Peano.le m n)). Qed.
Lemma lem251237 (m : nat) : (term86 m) = (term169 m).
Proof. exact (fun_ext (fun n : nat => @lem251236 m n)). Qed.
Lemma lem251238 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251239 (m : nat) : (term87 m) = (term170 m).
Proof. exact (MK_COMB (@lem251238) (@lem251237 m)). Qed.
Lemma lem251240 : term88 = term171.
Proof. exact (fun_ext (fun m : nat => @lem251239 m)). Qed.
Lemma lem251241 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251298 : term89 = term172.
Proof. exact (MK_COMB (@lem251241) (@lem251240)). Qed.
Lemma lem251299 (h1 : term89) : term172.
Proof. exact (EQ_MP (@lem251298) (@lem251008 h1)). Qed.
Lemma lem251314 (m : nat) (n : nat) : (((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n)) = (term173 m n).
Proof. exact (@lem17784 ((Nat.sub m n) = (NUMERAL 0)) (Peano.le m n)). Qed.
Lemma lem251315 (m : nat) : (term81 m) = (term174 m).
Proof. exact (fun_ext (fun n : nat => @lem251314 m n)). Qed.
Lemma lem251316 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251317 (m : nat) : (term82 m) = (term175 m).
Proof. exact (MK_COMB (@lem251316) (@lem251315 m)). Qed.
Lemma lem251318 : term83 = term176.
Proof. exact (fun_ext (fun m : nat => @lem251317 m)). Qed.
Lemma lem251319 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251320 : term84 = term177.
Proof. exact (MK_COMB (@lem251319) (@lem251318)). Qed.
Lemma lem251326 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem251327 (P : nat -> Prop) (Q : nat -> Prop) : (term180 P Q) = (term181 P Q).
Proof. exact (@lem251326 nat P Q). Qed.
Lemma lem251328 (m : nat) : (term182 m) = (term183 m).
Proof. exact (@lem251327 (term184 m) (term185 m)). Qed.
Lemma lem251329 (m : nat) (n : nat) : (term186 m n) = (term187 m n).
Proof. exact (eq_refl (term186 m n)). Qed.
Lemma lem251330 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem251331 (m : nat) (n : nat) : (term188 m n) = (term189 m n).
Proof. exact (MK_COMB (@lem251330) (@lem251329 m n)). Qed.
Lemma lem251332 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (eq_refl (term190 m n)). Qed.
Lemma lem251333 (m : nat) (n : nat) : (term192 m n) = (term173 m n).
Proof. exact (MK_COMB (@lem251331 m n) (@lem251332 m n)). Qed.
Lemma lem251334 (m : nat) : (term193 m) = (term174 m).
Proof. exact (fun_ext (fun n : nat => @lem251333 m n)). Qed.
Lemma lem251335 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251336 (m : nat) : (term182 m) = (term175 m).
Proof. exact (MK_COMB (@lem251335) (@lem251334 m)). Qed.
Lemma lem251337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem251338 (m : nat) : (term194 m) = (term195 m).
Proof. exact (MK_COMB (@lem251337) (@lem251336 m)). Qed.
Lemma lem251339 (m : nat) (n : nat) : (term186 m n) = (term187 m n).
Proof. exact (eq_refl (term186 m n)). Qed.
Lemma lem251340 (m : nat) : (term196 m) = (term184 m).
Proof. exact (fun_ext (fun n : nat => @lem251339 m n)). Qed.
Lemma lem251341 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251342 (m : nat) : (term197 m) = (term198 m).
Proof. exact (MK_COMB (@lem251341) (@lem251340 m)). Qed.
Lemma lem251343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem251344 (m : nat) : (term199 m) = (term200 m).
Proof. exact (MK_COMB (@lem251343) (@lem251342 m)). Qed.
Lemma lem251345 (m : nat) (n : nat) : (term190 m n) = (term191 m n).
Proof. exact (eq_refl (term190 m n)). Qed.
Lemma lem251346 (m : nat) : (term201 m) = (term185 m).
Proof. exact (fun_ext (fun n : nat => @lem251345 m n)). Qed.
Lemma lem251347 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251348 (m : nat) : (term202 m) = (term203 m).
Proof. exact (MK_COMB (@lem251347) (@lem251346 m)). Qed.
Lemma lem251349 (m : nat) : (term183 m) = (term204 m).
Proof. exact (MK_COMB (@lem251344 m) (@lem251348 m)). Qed.
Lemma lem251350 (m : nat) : ((term182 m) = (term183 m)) = ((term175 m) = (term204 m)).
Proof. exact (MK_COMB (@lem251338 m) (@lem251349 m)). Qed.
Lemma lem251351 (m : nat) : (term175 m) = (term204 m).
Proof. exact (EQ_MP (@lem251350 m) (@lem251328 m)). Qed.
Lemma lem251448 : term176 = term205.
Proof. exact (fun_ext (fun m : nat => @lem251351 m)). Qed.
Lemma lem251449 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251450 : term177 = term206.
Proof. exact (MK_COMB (@lem251449) (@lem251448)). Qed.
Lemma lem251452 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem251453 (P : nat -> Prop) (Q : nat -> Prop) : (term180 P Q) = (term181 P Q).
Proof. exact (@lem251452 nat P Q). Qed.
Lemma lem251454 : term207 = term208.
Proof. exact (@lem251453 term209 term210). Qed.
Lemma lem251455 (m : nat) : (term211 m) = (term198 m).
Proof. exact (eq_refl (term211 m)). Qed.
Lemma lem251456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem251457 (m : nat) : (term212 m) = (term200 m).
Proof. exact (MK_COMB (@lem251456) (@lem251455 m)). Qed.
Lemma lem251458 (m : nat) : (term213 m) = (term203 m).
Proof. exact (eq_refl (term213 m)). Qed.
Lemma lem251459 (m : nat) : (term214 m) = (term204 m).
Proof. exact (MK_COMB (@lem251457 m) (@lem251458 m)). Qed.
Lemma lem251460 : term215 = term205.
Proof. exact (fun_ext (fun m : nat => @lem251459 m)). Qed.
Lemma lem251461 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251462 : term207 = term206.
Proof. exact (MK_COMB (@lem251461) (@lem251460)). Qed.
Lemma lem251463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem251464 : term216 = term217.
Proof. exact (MK_COMB (@lem251463) (@lem251462)). Qed.
Lemma lem251465 (m : nat) : (term211 m) = (term198 m).
Proof. exact (eq_refl (term211 m)). Qed.
Lemma lem251466 : term218 = term209.
Proof. exact (fun_ext (fun m : nat => @lem251465 m)). Qed.
Lemma lem251467 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251468 : term219 = term220.
Proof. exact (MK_COMB (@lem251467) (@lem251466)). Qed.
Lemma lem251469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem251470 : term221 = term222.
Proof. exact (MK_COMB (@lem251469) (@lem251468)). Qed.
Lemma lem251471 (m : nat) : (term213 m) = (term203 m).
Proof. exact (eq_refl (term213 m)). Qed.
Lemma lem251472 : term223 = term210.
Proof. exact (fun_ext (fun m : nat => @lem251471 m)). Qed.
Lemma lem251473 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251474 : term224 = term225.
Proof. exact (MK_COMB (@lem251473) (@lem251472)). Qed.
Lemma lem251475 : term208 = term226.
Proof. exact (MK_COMB (@lem251470) (@lem251474)). Qed.
Lemma lem251476 : (term207 = term208) = (term206 = term226).
Proof. exact (MK_COMB (@lem251464) (@lem251475)). Qed.
Lemma lem251477 : term206 = term226.
Proof. exact (EQ_MP (@lem251476) (@lem251454)). Qed.
Lemma lem251584 : term177 = term226.
Proof. exact (TRANS (@lem251450) (@lem251477)). Qed.
Lemma lem251585 : term84 = term226.
Proof. exact (TRANS (@lem251320) (@lem251584)). Qed.
Lemma lem251586 (h1 : term84) : term226.
Proof. exact (EQ_MP (@lem251585) (@lem251009 h1)). Qed.
Lemma lem251590 (m : nat) (n : nat) : (term227 m n) = (Peano.lt m n).
Proof. exact (@lem16933 (Peano.lt m n)). Qed.
Lemma lem251592 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem251593 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem251594 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (MK_COMB (@lem251593) (@lem251590 m n)). Qed.
Lemma lem251595 (n : nat) (m : nat) : (term230 n m) = (term38 n m).
Proof. exact (MK_COMB (@lem251594 m n) (@lem251592 n m)). Qed.
Lemma lem251600 (n : nat) (m : nat) : (term231 n m) = (term231 n m).
Proof. exact (eq_refl (term231 n m)). Qed.
Lemma lem251601 (n : nat) (m : nat) : (term232 n m) = (term233 n m).
Proof. exact (MK_COMB (@lem251600 n m) (@lem251595 n m)). Qed.
Lemma lem251602 (n : nat) (m : nat) : ((term77 m n) = (Peano.le n m)) = (term232 n m).
Proof. exact (@lem17784 (term77 m n) (Peano.le n m)). Qed.
Lemma lem251603 (n : nat) (m : nat) : ((term77 m n) = (Peano.le n m)) = (term233 n m).
Proof. exact (TRANS (@lem251602 n m) (@lem251601 n m)). Qed.
Lemma lem251604 (m : nat) : (term78 m) = (term234 m).
Proof. exact (fun_ext (fun n : nat => @lem251603 n m)). Qed.
Lemma lem251605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251606 (m : nat) : (term79 m) = (term235 m).
Proof. exact (MK_COMB (@lem251605) (@lem251604 m)). Qed.
Lemma lem251607 : term80 = term236.
Proof. exact (fun_ext (fun m : nat => @lem251606 m)). Qed.
Lemma lem251608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251609 : term50 = term237.
Proof. exact (MK_COMB (@lem251608) (@lem251607)). Qed.
Lemma lem251615 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem251616 (P : nat -> Prop) (Q : nat -> Prop) : (term180 P Q) = (term181 P Q).
Proof. exact (@lem251615 nat P Q). Qed.
Lemma lem251617 (m : nat) : (term238 m) = (term239 m).
Proof. exact (@lem251616 (term240 m) (term241 m)). Qed.
Lemma lem251618 (n : nat) (m : nat) : (term242 m n) = (term243 n m).
Proof. exact (eq_refl (term242 m n)). Qed.
Lemma lem251619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem251620 (n : nat) (m : nat) : (term244 m n) = (term231 n m).
Proof. exact (MK_COMB (@lem251619) (@lem251618 n m)). Qed.
Lemma lem251621 (n : nat) (m : nat) : (term37 m n) = (term38 n m).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem251622 (n : nat) (m : nat) : (term245 m n) = (term233 n m).
Proof. exact (MK_COMB (@lem251620 n m) (@lem251621 n m)). Qed.
Lemma lem251623 (m : nat) : (term246 m) = (term234 m).
Proof. exact (fun_ext (fun n : nat => @lem251622 n m)). Qed.
Lemma lem251624 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251625 (m : nat) : (term238 m) = (term235 m).
Proof. exact (MK_COMB (@lem251624) (@lem251623 m)). Qed.
Lemma lem251626 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem251627 (m : nat) : (term247 m) = (term248 m).
Proof. exact (MK_COMB (@lem251626) (@lem251625 m)). Qed.
Lemma lem251628 (n : nat) (m : nat) : (term242 m n) = (term243 n m).
Proof. exact (eq_refl (term242 m n)). Qed.
Lemma lem251629 (m : nat) : (term249 m) = (term240 m).
Proof. exact (fun_ext (fun n : nat => @lem251628 n m)). Qed.
Lemma lem251630 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251631 (m : nat) : (term250 m) = (term251 m).
Proof. exact (MK_COMB (@lem251630) (@lem251629 m)). Qed.
Lemma lem251632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem251633 (m : nat) : (term252 m) = (term253 m).
Proof. exact (MK_COMB (@lem251632) (@lem251631 m)). Qed.
Lemma lem251634 (n : nat) (m : nat) : (term37 m n) = (term38 n m).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem251635 (m : nat) : (term254 m) = (term241 m).
Proof. exact (fun_ext (fun n : nat => @lem251634 n m)). Qed.
Lemma lem251636 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251637 (m : nat) : (term255 m) = (term36 m).
Proof. exact (MK_COMB (@lem251636) (@lem251635 m)). Qed.
Lemma lem251638 (m : nat) : (term239 m) = (term256 m).
Proof. exact (MK_COMB (@lem251633 m) (@lem251637 m)). Qed.
Lemma lem251639 (m : nat) : ((term238 m) = (term239 m)) = ((term235 m) = (term256 m)).
Proof. exact (MK_COMB (@lem251627 m) (@lem251638 m)). Qed.
Lemma lem251640 (m : nat) : (term235 m) = (term256 m).
Proof. exact (EQ_MP (@lem251639 m) (@lem251617 m)). Qed.
Lemma lem251737 : term236 = term257.
Proof. exact (fun_ext (fun m : nat => @lem251640 m)). Qed.
Lemma lem251738 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251739 : term237 = term258.
Proof. exact (MK_COMB (@lem251738) (@lem251737)). Qed.
Lemma lem251741 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem251742 (P : nat -> Prop) (Q : nat -> Prop) : (term180 P Q) = (term181 P Q).
Proof. exact (@lem251741 nat P Q). Qed.
Lemma lem251743 : term259 = term260.
Proof. exact (@lem251742 term261 term262). Qed.
Lemma lem251744 (m : nat) : (term263 m) = (term251 m).
Proof. exact (eq_refl (term263 m)). Qed.
Lemma lem251745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem251746 (m : nat) : (term264 m) = (term253 m).
Proof. exact (MK_COMB (@lem251745) (@lem251744 m)). Qed.
Lemma lem251747 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem251748 (m : nat) : (term265 m) = (term256 m).
Proof. exact (MK_COMB (@lem251746 m) (@lem251747 m)). Qed.
Lemma lem251749 : term266 = term257.
Proof. exact (fun_ext (fun m : nat => @lem251748 m)). Qed.
Lemma lem251750 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251751 : term259 = term258.
Proof. exact (MK_COMB (@lem251750) (@lem251749)). Qed.
Lemma lem251752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem251753 : term267 = term268.
Proof. exact (MK_COMB (@lem251752) (@lem251751)). Qed.
Lemma lem251754 (m : nat) : (term263 m) = (term251 m).
Proof. exact (eq_refl (term263 m)). Qed.
Lemma lem251755 : term269 = term261.
Proof. exact (fun_ext (fun m : nat => @lem251754 m)). Qed.
Lemma lem251756 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251757 : term270 = term271.
Proof. exact (MK_COMB (@lem251756) (@lem251755)). Qed.
Lemma lem251758 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem251759 : term272 = term273.
Proof. exact (MK_COMB (@lem251758) (@lem251757)). Qed.
Lemma lem251760 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem251761 : term274 = term262.
Proof. exact (fun_ext (fun m : nat => @lem251760 m)). Qed.
Lemma lem251762 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251763 : term275 = term276.
Proof. exact (MK_COMB (@lem251762) (@lem251761)). Qed.
Lemma lem251764 : term260 = term277.
Proof. exact (MK_COMB (@lem251759) (@lem251763)). Qed.
Lemma lem251765 : (term259 = term260) = (term258 = term277).
Proof. exact (MK_COMB (@lem251753) (@lem251764)). Qed.
Lemma lem251766 : term258 = term277.
Proof. exact (EQ_MP (@lem251765) (@lem251743)). Qed.
Lemma lem251873 : term237 = term277.
Proof. exact (TRANS (@lem251739) (@lem251766)). Qed.
Lemma lem251874 : term50 = term277.
Proof. exact (TRANS (@lem251609) (@lem251873)). Qed.
Lemma lem251875 (h1 : term50) : term277.
Proof. exact (EQ_MP (@lem251874) (@lem251010 h1)). Qed.
Lemma lem251876 (d : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term164 d a b P) : term164 d a b P.
Proof. exact (h1). Qed.
Lemma lem251882 (a : nat) (b : nat) (h1 : Peano.lt a b) : Peano.lt a b.
Proof. exact (h1). Qed.
Lemma lem251891 (m : nat) (n : nat) : (term17 m n) = (term17 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem251892 (m : nat) : (term90 m) = (term90 m).
Proof. exact (fun_ext (fun n : nat => @lem251891 m n)). Qed.
Lemma lem251893 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251894 (m : nat) : (term15 m) = (term15 m).
Proof. exact (MK_COMB (@lem251893) (@lem251892 m)). Qed.
Lemma lem251895 : term91 = term91.
Proof. exact (fun_ext (fun m : nat => @lem251894 m)). Qed.
Lemma lem251896 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251897 : term92 = term92.
Proof. exact (MK_COMB (@lem251896) (@lem251895)). Qed.
Lemma lem251898 (h1 : term92) : term92.
Proof. exact (EQ_MP (@lem251897) (@lem251229 h1)). Qed.
Lemma lem251913 (m : nat) (n : nat) : (term168 m n) = (term168 m n).
Proof. exact (eq_refl (term168 m n)). Qed.
Lemma lem251914 (m : nat) : (term169 m) = (term169 m).
Proof. exact (fun_ext (fun n : nat => @lem251913 m n)). Qed.
Lemma lem251915 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251916 (m : nat) : (term170 m) = (term170 m).
Proof. exact (MK_COMB (@lem251915) (@lem251914 m)). Qed.
Lemma lem251917 : term171 = term171.
Proof. exact (fun_ext (fun m : nat => @lem251916 m)). Qed.
Lemma lem251918 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251919 : term172 = term172.
Proof. exact (MK_COMB (@lem251918) (@lem251917)). Qed.
Lemma lem251920 (h1 : term89) : term172.
Proof. exact (EQ_MP (@lem251919) (@lem251299 h1)). Qed.
Lemma lem251941 (m : nat) (n : nat) : (term191 m n) = (term191 m n).
Proof. exact (eq_refl (term191 m n)). Qed.
Lemma lem251942 (m : nat) : (term185 m) = (term185 m).
Proof. exact (fun_ext (fun n : nat => @lem251941 m n)). Qed.
Lemma lem251943 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251944 (m : nat) : (term203 m) = (term203 m).
Proof. exact (MK_COMB (@lem251943) (@lem251942 m)). Qed.
Lemma lem251945 : term210 = term210.
Proof. exact (fun_ext (fun m : nat => @lem251944 m)). Qed.
Lemma lem251946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251947 : term225 = term225.
Proof. exact (MK_COMB (@lem251946) (@lem251945)). Qed.
Lemma lem251968 (m : nat) (n : nat) : (term187 m n) = (term187 m n).
Proof. exact (eq_refl (term187 m n)). Qed.
Lemma lem251969 (m : nat) : (term184 m) = (term184 m).
Proof. exact (fun_ext (fun n : nat => @lem251968 m n)). Qed.
Lemma lem251970 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251971 (m : nat) : (term198 m) = (term198 m).
Proof. exact (MK_COMB (@lem251970) (@lem251969 m)). Qed.
Lemma lem251972 : term209 = term209.
Proof. exact (fun_ext (fun m : nat => @lem251971 m)). Qed.
Lemma lem251973 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251974 : term220 = term220.
Proof. exact (MK_COMB (@lem251973) (@lem251972)). Qed.
Lemma lem251975 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem251976 : term222 = term222.
Proof. exact (MK_COMB (@lem251975) (@lem251974)). Qed.
Lemma lem251977 : term226 = term226.
Proof. exact (MK_COMB (@lem251976) (@lem251947)). Qed.
Lemma lem251978 (h1 : term84) : term226.
Proof. exact (EQ_MP (@lem251977) (@lem251586 h1)). Qed.
Lemma lem251991 (n : nat) (m : nat) : (term38 n m) = (term38 n m).
Proof. exact (eq_refl (term38 n m)). Qed.
Lemma lem251992 (m : nat) : (term241 m) = (term241 m).
Proof. exact (fun_ext (fun n : nat => @lem251991 n m)). Qed.
Lemma lem251993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251994 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem251993) (@lem251992 m)). Qed.
Lemma lem251995 : term262 = term262.
Proof. exact (fun_ext (fun m : nat => @lem251994 m)). Qed.
Lemma lem251996 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem251997 : term276 = term276.
Proof. exact (MK_COMB (@lem251996) (@lem251995)). Qed.
Lemma lem252014 (n : nat) (m : nat) : (term243 n m) = (term243 n m).
Proof. exact (eq_refl (term243 n m)). Qed.
Lemma lem252015 (m : nat) : (term240 m) = (term240 m).
Proof. exact (fun_ext (fun n : nat => @lem252014 n m)). Qed.
Lemma lem252016 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252017 (m : nat) : (term251 m) = (term251 m).
Proof. exact (MK_COMB (@lem252016) (@lem252015 m)). Qed.
Lemma lem252018 : term261 = term261.
Proof. exact (fun_ext (fun m : nat => @lem252017 m)). Qed.
Lemma lem252019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252020 : term271 = term271.
Proof. exact (MK_COMB (@lem252019) (@lem252018)). Qed.
Lemma lem252021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem252022 : term273 = term273.
Proof. exact (MK_COMB (@lem252021) (@lem252020)). Qed.
Lemma lem252023 : term277 = term277.
Proof. exact (MK_COMB (@lem252022) (@lem251997)). Qed.
Lemma lem252024 (h1 : term50) : term277.
Proof. exact (EQ_MP (@lem252023) (@lem251875 h1)). Qed.
Lemma lem252063 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term109 a b P d) = (term109 a b P d).
Proof. exact (eq_refl (term109 a b P d)). Qed.
Lemma lem252064 (a : nat) (b : nat) (P : nat -> Prop) : (term119 a b P) = (term119 a b P).
Proof. exact (fun_ext (fun d : nat => @lem252063 a b P d)). Qed.
Lemma lem252065 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252066 (a : nat) (b : nat) (P : nat -> Prop) : (term120 a b P) = (term120 a b P).
Proof. exact (MK_COMB (@lem252065) (@lem252064 a b P)). Qed.
Lemma lem252077 (P : nat -> Prop) (a : nat) (b : nat) : (term121 P a b) = (term121 P a b).
Proof. exact (eq_refl (term121 P a b)). Qed.
Lemma lem252078 (a : nat) (b : nat) (P : nat -> Prop) : (term123 a b P) = (term123 a b P).
Proof. exact (MK_COMB (@lem252077 P a b) (@lem252066 a b P)). Qed.
Lemma lem252125 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term162 a b P d) = (term162 a b P d).
Proof. exact (eq_refl (term162 a b P d)). Qed.
Lemma lem252126 (d : nat) (a : nat) (b : nat) (P : nat -> Prop) : (term164 d a b P) = (term164 d a b P).
Proof. exact (MK_COMB (@lem252125 a b P d) (@lem252078 a b P)). Qed.
Lemma lem252127 (d : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term164 d a b P) : term164 d a b P.
Proof. exact (EQ_MP (@lem252126 d a b P) (@lem251876 d a b P h1)). Qed.
Lemma lem252129 (h1 : term50) : term271.
Proof. exact (proj1 (@lem252024 h1)). Qed.
Lemma lem252131 (h1 : term84) : term220.
Proof. exact (proj1 (@lem251978 h1)). Qed.
Lemma lem252132 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) (h1 : term143 a b P d) : term143 a b P d.
Proof. exact (h1). Qed.
Lemma lem252133 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term123 a b P) : term123 a b P.
Proof. exact (h1). Qed.
Lemma lem252134 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) (h1 : term143 a b P d) : term104 a b P d.
Proof. exact (proj2 (@lem252132 a b P d h1)). Qed.
Lemma lem252137 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) (h1 : term143 a b P d) : term105 a b d.
Proof. exact (proj1 (@lem252134 a b P d h1)). Qed.
Lemma lem252139 (a : nat) (b : nat) (d : nat) (h1 : term102 a b d) : term102 a b d.
Proof. exact (h1). Qed.
Lemma lem252142 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term123 a b P) : term120 a b P.
Proof. exact (proj2 (@lem252133 a b P h1)). Qed.
Lemma lem252147 (a : nat) (b : nat) (h1 : Peano.lt a b) : Peano.lt a b.
Proof. exact (h1). Qed.
Lemma lem252149 (m : nat) (n : nat) : (term17 m n) = (term17 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem252150 (m : nat) : (term90 m) = (term90 m).
Proof. exact (fun_ext (fun n : nat => @lem252149 m n)). Qed.
Lemma lem252151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252152 (m : nat) : (term15 m) = (term15 m).
Proof. exact (MK_COMB (@lem252151) (@lem252150 m)). Qed.
Lemma lem252153 : term91 = term91.
Proof. exact (fun_ext (fun m : nat => @lem252152 m)). Qed.
Lemma lem252154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252156 : term92 = term92.
Proof. exact (MK_COMB (@lem252154) (@lem252153)). Qed.
Lemma lem252157 (h1 : term92) : term92.
Proof. exact (EQ_MP (@lem252156) (@lem251898 h1)). Qed.
Lemma lem252181 (n : nat) (m : nat) : (term243 n m) = (term243 n m).
Proof. exact (eq_refl (term243 n m)). Qed.
Lemma lem252182 (m : nat) : (term240 m) = (term240 m).
Proof. exact (fun_ext (fun n : nat => @lem252181 n m)). Qed.
Lemma lem252183 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252184 (m : nat) : (term251 m) = (term251 m).
Proof. exact (MK_COMB (@lem252183) (@lem252182 m)). Qed.
Lemma lem252185 : term261 = term261.
Proof. exact (fun_ext (fun m : nat => @lem252184 m)). Qed.
Lemma lem252186 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252188 : term271 = term271.
Proof. exact (MK_COMB (@lem252186) (@lem252185)). Qed.
Lemma lem252189 (h1 : term50) : term271.
Proof. exact (EQ_MP (@lem252188) (@lem252129 h1)). Qed.
Lemma lem252249 (a : nat) (b : nat) (d : nat) (h1 : a = (Nat.add b d)) : a = (Nat.add b d).
Proof. exact (h1). Qed.
Lemma lem252271 (m : nat) (n : nat) : (term168 m n) = (term168 m n).
Proof. exact (eq_refl (term168 m n)). Qed.
Lemma lem252272 (m : nat) : (term169 m) = (term169 m).
Proof. exact (fun_ext (fun n : nat => @lem252271 m n)). Qed.
Lemma lem252273 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252274 (m : nat) : (term170 m) = (term170 m).
Proof. exact (MK_COMB (@lem252273) (@lem252272 m)). Qed.
Lemma lem252275 : term171 = term171.
Proof. exact (fun_ext (fun m : nat => @lem252274 m)). Qed.
Lemma lem252276 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252278 : term172 = term172.
Proof. exact (MK_COMB (@lem252276) (@lem252275)). Qed.
Lemma lem252279 (h1 : term89) : term172.
Proof. exact (EQ_MP (@lem252278) (@lem251920 h1)). Qed.
Lemma lem252319 (m : nat) (n : nat) : (term187 m n) = (term187 m n).
Proof. exact (eq_refl (term187 m n)). Qed.
Lemma lem252320 (m : nat) : (term184 m) = (term184 m).
Proof. exact (fun_ext (fun n : nat => @lem252319 m n)). Qed.
Lemma lem252321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252322 (m : nat) : (term198 m) = (term198 m).
Proof. exact (MK_COMB (@lem252321) (@lem252320 m)). Qed.
Lemma lem252323 : term209 = term209.
Proof. exact (fun_ext (fun m : nat => @lem252322 m)). Qed.
Lemma lem252324 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252326 : term220 = term220.
Proof. exact (MK_COMB (@lem252324) (@lem252323)). Qed.
Lemma lem252327 (h1 : term84) : term220.
Proof. exact (EQ_MP (@lem252326) (@lem252131 h1)). Qed.
Lemma lem252363 (a : nat) (b : nat) (h1 : Peano.lt a b) : Peano.lt a b.
Proof. exact (h1). Qed.
Lemma lem252381 (m : nat) (n : nat) : (term168 m n) = (term168 m n).
Proof. exact (eq_refl (term168 m n)). Qed.
Lemma lem252382 (m : nat) : (term169 m) = (term169 m).
Proof. exact (fun_ext (fun n : nat => @lem252381 m n)). Qed.
Lemma lem252383 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252384 (m : nat) : (term170 m) = (term170 m).
Proof. exact (MK_COMB (@lem252383) (@lem252382 m)). Qed.
Lemma lem252385 : term171 = term171.
Proof. exact (fun_ext (fun m : nat => @lem252384 m)). Qed.
Lemma lem252386 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252388 : term172 = term172.
Proof. exact (MK_COMB (@lem252386) (@lem252385)). Qed.
Lemma lem252389 (h1 : term89) : term172.
Proof. exact (EQ_MP (@lem252388) (@lem251920 h1)). Qed.
Lemma lem252429 (m : nat) (n : nat) : (term187 m n) = (term187 m n).
Proof. exact (eq_refl (term187 m n)). Qed.
Lemma lem252430 (m : nat) : (term184 m) = (term184 m).
Proof. exact (fun_ext (fun n : nat => @lem252429 m n)). Qed.
Lemma lem252431 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252432 (m : nat) : (term198 m) = (term198 m).
Proof. exact (MK_COMB (@lem252431) (@lem252430 m)). Qed.
Lemma lem252433 : term209 = term209.
Proof. exact (fun_ext (fun m : nat => @lem252432 m)). Qed.
Lemma lem252434 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252436 : term220 = term220.
Proof. exact (MK_COMB (@lem252434) (@lem252433)). Qed.
Lemma lem252437 (h1 : term84) : term220.
Proof. exact (EQ_MP (@lem252436) (@lem252131 h1)). Qed.
Lemma lem252481 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term109 a b P d) = (term278 a b P d).
Proof. exact (@lem19699 (term279 a b d) (term97 a b d) (P d)). Qed.
Lemma lem252482 (a : nat) (b : nat) (P : nat -> Prop) : (term119 a b P) = (term280 a b P).
Proof. exact (fun_ext (fun d : nat => @lem252481 a b P d)). Qed.
Lemma lem252483 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem252485 (a : nat) (b : nat) (P : nat -> Prop) : (term120 a b P) = (term281 a b P).
Proof. exact (MK_COMB (@lem252483) (@lem252482 a b P)). Qed.
Lemma lem252486 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term123 a b P) : term281 a b P.
Proof. exact (EQ_MP (@lem252485 a b P) (@lem252142 a b P h1)). Qed.
Lemma lem252487 (_5140 : nat) (h1 : term92) : term14 _5140.
Proof. exact (@lem252157 h1 _5140). Qed.
Lemma lem252488 (_5140 : nat) : (term14 _5140) = (term15 _5140).
Proof. exact (eq_refl (term14 _5140)). Qed.
Lemma lem252489 (_5140 : nat) (h1 : term92) : term15 _5140.
Proof. exact (EQ_MP (@lem252488 _5140) (@lem252487 _5140 h1)). Qed.
Lemma lem252490 (_5140 : nat) (_5141 : nat) (h1 : term92) : term16 _5140 _5141.
Proof. exact (@lem252489 _5140 h1 _5141). Qed.
Lemma lem252491 (_5140 : nat) (_5141 : nat) : (term16 _5140 _5141) = (term17 _5140 _5141).
Proof. exact (eq_refl (term16 _5140 _5141)). Qed.
Lemma lem252499 (_5144 : nat) (h1 : term50) : term263 _5144.
Proof. exact (@lem252189 h1 _5144). Qed.
Lemma lem252500 (_5144 : nat) : (term263 _5144) = (term251 _5144).
Proof. exact (eq_refl (term263 _5144)). Qed.
Lemma lem252501 (_5144 : nat) (h1 : term50) : term251 _5144.
Proof. exact (EQ_MP (@lem252500 _5144) (@lem252499 _5144 h1)). Qed.
Lemma lem252502 (_5144 : nat) (_5145 : nat) (h1 : term50) : term242 _5144 _5145.
Proof. exact (@lem252501 _5144 h1 _5145). Qed.
Lemma lem252503 (_5145 : nat) (_5144 : nat) : (term242 _5144 _5145) = (term243 _5145 _5144).
Proof. exact (eq_refl (term242 _5144 _5145)). Qed.
Lemma lem252529 (_5154 : nat) (h1 : term89) : term282 _5154.
Proof. exact (@lem252279 h1 _5154). Qed.
Lemma lem252530 (_5154 : nat) : (term282 _5154) = (term170 _5154).
Proof. exact (eq_refl (term282 _5154)). Qed.
Lemma lem252531 (_5154 : nat) (h1 : term89) : term170 _5154.
Proof. exact (EQ_MP (@lem252530 _5154) (@lem252529 _5154 h1)). Qed.
Lemma lem252532 (_5154 : nat) (_5155 : nat) (h1 : term89) : term283 _5154 _5155.
Proof. exact (@lem252531 _5154 h1 _5155). Qed.
Lemma lem252533 (_5154 : nat) (_5155 : nat) : (term283 _5154 _5155) = (term168 _5154 _5155).
Proof. exact (eq_refl (term283 _5154 _5155)). Qed.
Lemma lem252547 (_5160 : nat) (h1 : term84) : term211 _5160.
Proof. exact (@lem252327 h1 _5160). Qed.
Lemma lem252548 (_5160 : nat) : (term211 _5160) = (term198 _5160).
Proof. exact (eq_refl (term211 _5160)). Qed.
Lemma lem252549 (_5160 : nat) (h1 : term84) : term198 _5160.
Proof. exact (EQ_MP (@lem252548 _5160) (@lem252547 _5160 h1)). Qed.
Lemma lem252550 (_5160 : nat) (_5161 : nat) (h1 : term84) : term186 _5160 _5161.
Proof. exact (@lem252549 _5160 h1 _5161). Qed.
Lemma lem252551 (_5160 : nat) (_5161 : nat) : (term186 _5160 _5161) = (term187 _5160 _5161).
Proof. exact (eq_refl (term186 _5160 _5161)). Qed.
Lemma lem252565 (_5166 : nat) (h1 : term89) : term282 _5166.
Proof. exact (@lem252389 h1 _5166). Qed.
Lemma lem252566 (_5166 : nat) : (term282 _5166) = (term170 _5166).
Proof. exact (eq_refl (term282 _5166)). Qed.
Lemma lem252567 (_5166 : nat) (h1 : term89) : term170 _5166.
Proof. exact (EQ_MP (@lem252566 _5166) (@lem252565 _5166 h1)). Qed.
Lemma lem252568 (_5166 : nat) (_5167 : nat) (h1 : term89) : term283 _5166 _5167.
Proof. exact (@lem252567 _5166 h1 _5167). Qed.
Lemma lem252569 (_5166 : nat) (_5167 : nat) : (term283 _5166 _5167) = (term168 _5166 _5167).
Proof. exact (eq_refl (term283 _5166 _5167)). Qed.
Lemma lem252583 (_5172 : nat) (h1 : term84) : term211 _5172.
Proof. exact (@lem252437 h1 _5172). Qed.
Lemma lem252584 (_5172 : nat) : (term211 _5172) = (term198 _5172).
Proof. exact (eq_refl (term211 _5172)). Qed.
Lemma lem252585 (_5172 : nat) (h1 : term84) : term198 _5172.
Proof. exact (EQ_MP (@lem252584 _5172) (@lem252583 _5172 h1)). Qed.
Lemma lem252586 (_5172 : nat) (_5173 : nat) (h1 : term84) : term186 _5172 _5173.
Proof. exact (@lem252585 _5172 h1 _5173). Qed.
Lemma lem252587 (_5172 : nat) (_5173 : nat) : (term186 _5172 _5173) = (term187 _5172 _5173).
Proof. exact (eq_refl (term186 _5172 _5173)). Qed.
Lemma lem252595 (_5176 : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term123 a b P) : term284 a b P _5176.
Proof. exact (@lem252486 a b P h1 _5176). Qed.
Lemma lem252596 (a : nat) (b : nat) (P : nat -> Prop) (_5176 : nat) : (term284 a b P _5176) = (term278 a b P _5176).
Proof. exact (eq_refl (term284 a b P _5176)). Qed.
Lemma lem252597 (_5176 : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term123 a b P) : term278 a b P _5176.
Proof. exact (EQ_MP (@lem252596 a b P _5176) (@lem252595 _5176 a b P h1)). Qed.
Lemma lem252598 (_5176 : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term123 a b P) : term285 a b P _5176.
Proof. exact (proj2 (@lem252597 _5176 a b P h1)). Qed.
Lemma lem252601 (a : nat) (b : nat) (h1 : Peano.lt a b) : Peano.lt a b.
Proof. exact (h1). Qed.
Lemma lem252639 (a : nat) (b : nat) (d : nat) (h1 : a = (Nat.add b d)) : a = (Nat.add b d).
Proof. exact (h1). Qed.
Lemma lem252677 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) (h1 : term143 a b P d) : term286 P d.
Proof. exact (proj2 (@lem252134 a b P d h1)). Qed.
Lemma lem252681 (a : nat) (b : nat) (d : nat) (h1 : term102 a b d) : d = (NUMERAL 0).
Proof. exact (proj2 (@lem252139 a b d h1)). Qed.
Lemma lem252683 (a : nat) (b : nat) (h1 : Peano.lt a b) : Peano.lt a b.
Proof. exact (h1). Qed.
Lemma lem252691 (_5166 : nat) (_5167 : nat) (h1 : term89) : term168 _5166 _5167.
Proof. exact (EQ_MP (@lem252569 _5166 _5167) (@lem252568 _5166 _5167 h1)). Qed.
Lemma lem252709 (_5172 : nat) (_5173 : nat) (h1 : term84) : term187 _5172 _5173.
Proof. exact (EQ_MP (@lem252587 _5172 _5173) (@lem252586 _5172 _5173 h1)). Qed.
Lemma lem252717 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term123 a b P) : term287 P a b.
Proof. exact (proj1 (@lem252133 a b P h1)). Qed.
Lemma lem252734 (a : nat) (b : nat) (P : nat -> Prop) (_5176 : nat) : (term285 a b P _5176) = (term288 a b P _5176).
Proof. exact (@lem250677 (term77 a b) (term289 _5176) (P _5176)). Qed.
Lemma lem252735 (_5176 : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term123 a b P) : term288 a b P _5176.
Proof. exact (EQ_MP (@lem252734 a b P _5176) (@lem252598 _5176 a b P h1)). Qed.
Lemma lem252750 (b : nat) : (term290 b) = (term290 b).
Proof. exact (eq_refl (term290 b)). Qed.
Lemma lem252751 (a : nat) (b : nat) (d : nat) (h1 : a = (Nat.add b d)) : (term291 b a) = (term292 b d).
Proof. exact (MK_COMB (@lem252750 b) (@lem252639 a b d h1)). Qed.
Lemma lem252752 (d : nat) (b : nat) : (term292 b d) = (term293 d b).
Proof. exact (eq_refl (term292 b d)). Qed.
Lemma lem252753 (b : nat) (a : nat) : (term294 b a) = (term294 b a).
Proof. exact (eq_refl (term294 b a)). Qed.
Lemma lem252754 (a : nat) (d : nat) (b : nat) : ((term291 b a) = (term292 b d)) = ((term291 b a) = (term293 d b)).
Proof. exact (MK_COMB (@lem252753 b a) (@lem252752 d b)). Qed.
Lemma lem252755 (a : nat) (b : nat) : (term291 b a) = (Peano.lt a b).
Proof. exact (eq_refl (term291 b a)). Qed.
Lemma lem252756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem252757 (a : nat) (b : nat) : (term294 b a) = (term295 a b).
Proof. exact (MK_COMB (@lem252756) (@lem252755 a b)). Qed.
Lemma lem252758 (d : nat) (b : nat) : (term293 d b) = (term293 d b).
Proof. exact (eq_refl (term293 d b)). Qed.
Lemma lem252759 (a : nat) (d : nat) (b : nat) : ((term291 b a) = (term293 d b)) = ((Peano.lt a b) = (term293 d b)).
Proof. exact (MK_COMB (@lem252757 a b) (@lem252758 d b)). Qed.
Lemma lem252760 (a : nat) (d : nat) (b : nat) : ((term291 b a) = (term292 b d)) = ((Peano.lt a b) = (term293 d b)).
Proof. exact (TRANS (@lem252754 a d b) (@lem252759 a d b)). Qed.
Lemma lem252761 (a : nat) (b : nat) (d : nat) (h1 : a = (Nat.add b d)) : (Peano.lt a b) = (term293 d b).
Proof. exact (EQ_MP (@lem252760 a d b) (@lem252751 a b d h1)). Qed.
Lemma lem252804 (_5145 : nat) (_5144 : nat) (h1 : term50) : term243 _5145 _5144.
Proof. exact (EQ_MP (@lem252503 _5145 _5144) (@lem252502 _5144 _5145 h1)). Qed.
Lemma lem252929 (_5154 : nat) (_5155 : nat) (h1 : term89) : term168 _5154 _5155.
Proof. exact (EQ_MP (@lem252533 _5154 _5155) (@lem252532 _5154 _5155 h1)). Qed.
Lemma lem252971 (_5160 : nat) (_5161 : nat) (h1 : term84) : term187 _5160 _5161.
Proof. exact (EQ_MP (@lem252551 _5160 _5161) (@lem252550 _5160 _5161 h1)). Qed.
Lemma lem253000 (P : nat -> Prop) : (term296 P) = (term296 P).
Proof. exact (eq_refl (term296 P)). Qed.
Lemma lem253001 (P : nat -> Prop) (a : nat) (b : nat) (d : nat) (h1 : term102 a b d) : (term297 P d) = (term298 P).
Proof. exact (MK_COMB (@lem253000 P) (@lem252681 a b d h1)). Qed.
Lemma lem253002 (P : nat -> Prop) : (term298 P) = (term299 P).
Proof. exact (eq_refl (term298 P)). Qed.
Lemma lem253003 (P : nat -> Prop) (d : nat) : (term300 P d) = (term300 P d).
Proof. exact (eq_refl (term300 P d)). Qed.
Lemma lem253004 (d : nat) (P : nat -> Prop) : ((term297 P d) = (term298 P)) = ((term297 P d) = (term299 P)).
Proof. exact (MK_COMB (@lem253003 P d) (@lem253002 P)). Qed.
Lemma lem253005 (P : nat -> Prop) (d : nat) : (term297 P d) = (term286 P d).
Proof. exact (eq_refl (term297 P d)). Qed.
Lemma lem253006 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem253007 (P : nat -> Prop) (d : nat) : (term300 P d) = (term301 P d).
Proof. exact (MK_COMB (@lem253006) (@lem253005 P d)). Qed.
Lemma lem253008 (P : nat -> Prop) : (term299 P) = (term299 P).
Proof. exact (eq_refl (term299 P)). Qed.
Lemma lem253009 (d : nat) (P : nat -> Prop) : ((term297 P d) = (term299 P)) = ((term286 P d) = (term299 P)).
Proof. exact (MK_COMB (@lem253007 P d) (@lem253008 P)). Qed.
Lemma lem253010 (d : nat) (P : nat -> Prop) : ((term297 P d) = (term298 P)) = ((term286 P d) = (term299 P)).
Proof. exact (TRANS (@lem253004 d P) (@lem253009 d P)). Qed.
Lemma lem253011 (P : nat -> Prop) (a : nat) (b : nat) (d : nat) (h1 : term102 a b d) : (term286 P d) = (term299 P).
Proof. exact (EQ_MP (@lem253010 d P) (@lem253001 P a b d h1)). Qed.
Lemma lem253012 (P : nat -> Prop) (a : nat) (b : nat) (d : nat) (h1 : term143 a b P d) (h2 : term102 a b d) : term299 P.
Proof. exact (EQ_MP (@lem253011 P a b d h2) (@lem252677 a b P d h1)). Qed.
Lemma lem253118 (a : nat) (b : nat) (d : nat) (h1 : Peano.lt a b) (h2 : a = (Nat.add b d)) : term293 d b.
Proof. exact (EQ_MP (@lem252761 a b d h2) (@lem252601 a b h1)). Qed.
Lemma lem253119 (a : nat) (b : nat) (d : nat) (h1 : Peano.lt a b) (h2 : a = (Nat.add b d)) : term302 d b.
Proof. exact (fun h0 : term303 d b => @lem253118 a b d h1 h2). Qed.
Lemma lem253121 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253122 (d : nat) (b : nat) : (term302 d b) = (term293 d b).
Proof. exact (@lem253121 (term293 d b)). Qed.
Lemma lem253123 (a : nat) (b : nat) (d : nat) (h1 : Peano.lt a b) (h2 : a = (Nat.add b d)) : term293 d b.
Proof. exact (EQ_MP (@lem253122 d b) (@lem253119 a b d h1 h2)). Qed.
Lemma lem253125 (_5140 : nat) (_5141 : nat) (h1 : term92) : term17 _5140 _5141.
Proof. exact (EQ_MP (@lem252491 _5140 _5141) (@lem252490 _5140 _5141 h1)). Qed.
Lemma lem253126 (b : nat) (d : nat) (h1 : term92) : term17 b d.
Proof. exact (@lem253125 b d h1). Qed.
Lemma lem253127 (b : nat) (d : nat) (h1 : term92) : term305 b d.
Proof. exact (fun h0 : term306 b d => @lem253126 b d h1). Qed.
Lemma lem253129 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253130 (b : nat) (d : nat) : (term305 b d) = (term17 b d).
Proof. exact (@lem253129 (term17 b d)). Qed.
Lemma lem253131 (b : nat) (d : nat) (h1 : term92) : term17 b d.
Proof. exact (EQ_MP (@lem253130 b d) (@lem253127 b d h1)). Qed.
Lemma lem253133 (a : Prop) (b : Prop) : (term307 a b) = (term308 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem253134 (_5145 : nat) (_5144 : nat) : (term243 _5145 _5144) = (term309 _5145 _5144).
Proof. exact (@lem253133 (Peano.lt _5144 _5145) (Peano.le _5145 _5144)). Qed.
Lemma lem253136 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem253137 (_5145 : nat) (_5144 : nat) : (term309 _5145 _5144) = (term310 _5145 _5144).
Proof. exact (@lem253136 (term311 _5145 _5144)). Qed.
Lemma lem253138 (_5145 : nat) (_5144 : nat) : (term243 _5145 _5144) = (term310 _5145 _5144).
Proof. exact (TRANS (@lem253134 _5145 _5144) (@lem253137 _5145 _5144)). Qed.
Lemma lem253140 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : Peano.lt a b) (h3 : a = (Nat.add b d)) : term312 b d.
Proof. exact (conj (@lem253123 a b d h2 h3) (@lem253131 b d h1)). Qed.
Lemma lem253142 (_5145 : nat) (_5144 : nat) (h1 : term50) : term310 _5145 _5144.
Proof. exact (EQ_MP (@lem253138 _5145 _5144) (@lem252804 _5145 _5144 h1)). Qed.
Lemma lem253143 (b : nat) (d : nat) (h1 : term50) : term313 b d.
Proof. exact (@lem253142 b (Nat.add b d) h1). Qed.
Lemma lem253146 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : False.
Proof. exact (@lem253143 b d h2 (@lem253140 a b d h1 h3 h4)). Qed.
Lemma lem253147 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : term314.
Proof. exact (fun h0 : ~ False => @lem253146 a b d h1 h2 h3 h4). Qed.
Lemma lem253149 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253150 : term314 = False.
Proof. exact (@lem253149 False). Qed.
Lemma lem253152 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem253153 (_5239 : nat) (_5240 : nat) (h1 : _5239 = _5240) : _5239 = _5240.
Proof. exact (h1). Qed.
Lemma lem253154 (P : nat -> Prop) (_5239 : nat) (_5240 : nat) (h1 : _5239 = _5240) : (P _5239) = (P _5240).
Proof. exact (MK_COMB (@lem253152 P) (@lem253153 _5239 _5240 h1)). Qed.
Lemma lem253156 (b : Prop) (a : Prop) : term315 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem253157 (_5240 : nat) (P : nat -> Prop) (_5239 : nat) : term316 _5240 P _5239.
Proof. exact (@lem253156 (P _5240) (P _5239)). Qed.
Lemma lem253158 (P : nat -> Prop) (_5239 : nat) (_5240 : nat) (h1 : _5239 = _5240) : term317 _5240 P _5239.
Proof. exact (@lem253157 _5240 P _5239 (@lem253154 P _5239 _5240 h1)). Qed.
Lemma lem253159 (_5240 : nat) (P : nat -> Prop) (_5239 : nat) : term318 _5240 P _5239.
Proof. exact (fun h0 : _5239 = _5240 => @lem253158 P _5239 _5240 h0). Qed.
Lemma lem253161 (a : Prop) (b : Prop) : (a -> b) = (term319 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem253162 (_5240 : nat) (P : nat -> Prop) (_5239 : nat) : (term318 _5240 P _5239) = (term320 _5240 P _5239).
Proof. exact (@lem253161 (_5239 = _5240) (term317 _5240 P _5239)). Qed.
Lemma lem253163 (_5240 : nat) (P : nat -> Prop) (_5239 : nat) : term320 _5240 P _5239.
Proof. exact (EQ_MP (@lem253162 _5240 P _5239) (@lem253159 _5240 P _5239)). Qed.
Lemma lem253243 (a : nat) (b : nat) (d : nat) (h1 : term102 a b d) : Peano.lt a b.
Proof. exact (proj1 (@lem252139 a b d h1)). Qed.
Lemma lem253244 (a : nat) (b : nat) (d : nat) (h1 : term102 a b d) : term321 a b.
Proof. exact (fun h0 : term77 a b => @lem253243 a b d h1). Qed.
Lemma lem253246 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253247 (a : nat) (b : nat) : (term321 a b) = (Peano.lt a b).
Proof. exact (@lem253246 (Peano.lt a b)). Qed.
Lemma lem253248 (a : nat) (b : nat) (d : nat) (h1 : term102 a b d) : Peano.lt a b.
Proof. exact (EQ_MP (@lem253247 a b) (@lem253244 a b d h1)). Qed.
Lemma lem253254 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem253255 (_5154 : nat) (_5155 : nat) : (term168 _5154 _5155) = (term322 _5154 _5155).
Proof. exact (@lem253254 (Peano.le _5154 _5155) (term77 _5154 _5155)). Qed.
Lemma lem253261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem253262 (_5154 : nat) (_5155 : nat) : (term323 _5154 _5155) = (term324 _5154 _5155).
Proof. exact (MK_COMB (@lem253261) (@lem253255 _5154 _5155)). Qed.
Lemma lem253268 (_5154 : nat) (_5155 : nat) : (term322 _5154 _5155) = (term322 _5154 _5155).
Proof. exact (eq_refl (term322 _5154 _5155)). Qed.
Lemma lem253269 (_5154 : nat) (_5155 : nat) : ((term168 _5154 _5155) = (term322 _5154 _5155)) = ((term322 _5154 _5155) = (term322 _5154 _5155)).
Proof. exact (MK_COMB (@lem253262 _5154 _5155) (@lem253268 _5154 _5155)). Qed.
Lemma lem253271 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem253272 (x : Prop) : (x = x) = True.
Proof. exact (@lem253271 Prop x). Qed.
Lemma lem253273 (_5154 : nat) (_5155 : nat) : ((term322 _5154 _5155) = (term322 _5154 _5155)) = True.
Proof. exact (@lem253272 (term322 _5154 _5155)). Qed.
Lemma lem253274 (_5154 : nat) (_5155 : nat) : ((term168 _5154 _5155) = (term322 _5154 _5155)) = True.
Proof. exact (TRANS (@lem253269 _5154 _5155) (@lem253273 _5154 _5155)). Qed.
Lemma lem253275 (_5154 : nat) (_5155 : nat) : True = ((term168 _5154 _5155) = (term322 _5154 _5155)).
Proof. exact (SYM (@lem253274 _5154 _5155)). Qed.
Lemma lem253276 (_5154 : nat) (_5155 : nat) : (term168 _5154 _5155) = (term322 _5154 _5155).
Proof. exact (EQ_MP (@lem253275 _5154 _5155) (@lem0)). Qed.
Lemma lem253277 (_5154 : nat) (_5155 : nat) (h1 : term89) : term322 _5154 _5155.
Proof. exact (EQ_MP (@lem253276 _5154 _5155) (@lem252929 _5154 _5155 h1)). Qed.
Lemma lem253279 (b : Prop) (a : Prop) : (a \/ b) = (term325 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem253280 (_5154 : nat) (_5155 : nat) : (term322 _5154 _5155) = (term326 _5154 _5155).
Proof. exact (@lem253279 (term77 _5154 _5155) (Peano.le _5154 _5155)). Qed.
Lemma lem253282 (a : Prop) : (term327 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem253283 (_5154 : nat) (_5155 : nat) : (term227 _5154 _5155) = (Peano.lt _5154 _5155).
Proof. exact (@lem253282 (Peano.lt _5154 _5155)). Qed.
Lemma lem253284 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem253285 (_5154 : nat) (_5155 : nat) : (term328 _5154 _5155) = (term63 _5154 _5155).
Proof. exact (MK_COMB (@lem253284) (@lem253283 _5154 _5155)). Qed.
Lemma lem253286 (_5154 : nat) (_5155 : nat) : (Peano.le _5154 _5155) = (Peano.le _5154 _5155).
Proof. exact (eq_refl (Peano.le _5154 _5155)). Qed.
Lemma lem253287 (_5154 : nat) (_5155 : nat) : (term326 _5154 _5155) = (term85 _5154 _5155).
Proof. exact (MK_COMB (@lem253285 _5154 _5155) (@lem253286 _5154 _5155)). Qed.
Lemma lem253288 (_5154 : nat) (_5155 : nat) : (term322 _5154 _5155) = (term85 _5154 _5155).
Proof. exact (TRANS (@lem253280 _5154 _5155) (@lem253287 _5154 _5155)). Qed.
Lemma lem253291 (_5154 : nat) (_5155 : nat) (h1 : term89) : term85 _5154 _5155.
Proof. exact (EQ_MP (@lem253288 _5154 _5155) (@lem253277 _5154 _5155 h1)). Qed.
Lemma lem253292 (a : nat) (b : nat) (h1 : term89) : term85 a b.
Proof. exact (@lem253291 a b h1). Qed.
Lemma lem253295 (a : nat) (b : nat) (d : nat) (h1 : term89) (h2 : term102 a b d) : Peano.le a b.
Proof. exact (@lem253292 a b h1 (@lem253248 a b d h2)). Qed.
Lemma lem253296 (a : nat) (b : nat) (d : nat) (h1 : term89) (h2 : term102 a b d) : term329 a b.
Proof. exact (fun h0 : term0 a b => @lem253295 a b d h1 h2). Qed.
Lemma lem253298 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253299 (a : nat) (b : nat) : (term329 a b) = (Peano.le a b).
Proof. exact (@lem253298 (Peano.le a b)). Qed.
Lemma lem253300 (a : nat) (b : nat) (d : nat) (h1 : term89) (h2 : term102 a b d) : Peano.le a b.
Proof. exact (EQ_MP (@lem253299 a b) (@lem253296 a b d h1 h2)). Qed.
Lemma lem253302 (b : Prop) (a : Prop) : (a \/ b) = (term325 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem253303 (_5160 : nat) (_5161 : nat) : (term187 _5160 _5161) = (term330 _5160 _5161).
Proof. exact (@lem253302 (term0 _5160 _5161) ((Nat.sub _5160 _5161) = (NUMERAL 0))). Qed.
Lemma lem253305 (a : Prop) : (term327 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem253306 (_5160 : nat) (_5161 : nat) : (term331 _5160 _5161) = (Peano.le _5160 _5161).
Proof. exact (@lem253305 (Peano.le _5160 _5161)). Qed.
Lemma lem253307 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem253308 (_5160 : nat) (_5161 : nat) : (term332 _5160 _5161) = (term333 _5160 _5161).
Proof. exact (MK_COMB (@lem253307) (@lem253306 _5160 _5161)). Qed.
Lemma lem253309 (_5160 : nat) (_5161 : nat) : ((Nat.sub _5160 _5161) = (NUMERAL 0)) = ((Nat.sub _5160 _5161) = (NUMERAL 0)).
Proof. exact (eq_refl ((Nat.sub _5160 _5161) = (NUMERAL 0))). Qed.
Lemma lem253310 (_5160 : nat) (_5161 : nat) : (term330 _5160 _5161) = (term334 _5160 _5161).
Proof. exact (MK_COMB (@lem253308 _5160 _5161) (@lem253309 _5160 _5161)). Qed.
Lemma lem253311 (_5160 : nat) (_5161 : nat) : (term187 _5160 _5161) = (term334 _5160 _5161).
Proof. exact (TRANS (@lem253303 _5160 _5161) (@lem253310 _5160 _5161)). Qed.
Lemma lem253314 (_5160 : nat) (_5161 : nat) (h1 : term84) : term334 _5160 _5161.
Proof. exact (EQ_MP (@lem253311 _5160 _5161) (@lem252971 _5160 _5161 h1)). Qed.
Lemma lem253315 (a : nat) (b : nat) (h1 : term84) : term334 a b.
Proof. exact (@lem253314 a b h1). Qed.
Lemma lem253318 (a : nat) (b : nat) (d : nat) (h1 : term84) (h2 : term89) (h3 : term102 a b d) : (Nat.sub a b) = (NUMERAL 0).
Proof. exact (@lem253315 a b h1 (@lem253300 a b d h2 h3)). Qed.
Lemma lem253319 (a : nat) (b : nat) (d : nat) (h1 : term84) (h2 : term89) (h3 : term102 a b d) : term335 a b.
Proof. exact (fun h0 : term336 a b => @lem253318 a b d h1 h2 h3). Qed.
Lemma lem253321 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253322 (a : nat) (b : nat) : (term335 a b) = ((Nat.sub a b) = (NUMERAL 0)).
Proof. exact (@lem253321 ((Nat.sub a b) = (NUMERAL 0))). Qed.
Lemma lem253323 (a : nat) (b : nat) (d : nat) (h1 : term84) (h2 : term89) (h3 : term102 a b d) : (Nat.sub a b) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem253322 a b) (@lem253319 a b d h1 h2 h3)). Qed.
Lemma lem253325 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) (h1 : term143 a b P d) : term40 P a b.
Proof. exact (proj1 (@lem252132 a b P d h1)). Qed.
Lemma lem253326 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) (h1 : term143 a b P d) : term337 P a b.
Proof. exact (fun h0 : term287 P a b => @lem253325 a b P d h1). Qed.
Lemma lem253328 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253329 (P : nat -> Prop) (a : nat) (b : nat) : (term337 P a b) = (term40 P a b).
Proof. exact (@lem253328 (term40 P a b)). Qed.
Lemma lem253330 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) (h1 : term143 a b P d) : term40 P a b.
Proof. exact (EQ_MP (@lem253329 P a b) (@lem253326 a b P d h1)). Qed.
Lemma lem253336 (q : Prop) (p : Prop) (r : Prop) : (term33 p q r) = (term33 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem253337 (_5240 : nat) (P : nat -> Prop) (_5239 : nat) : (term320 _5240 P _5239) = (term338 _5240 P _5239).
Proof. exact (@lem253336 (P _5240) (term339 _5239 _5240) (term286 P _5239)). Qed.
Lemma lem253351 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem253352 (P : nat -> Prop) (_5239 : nat) (_5240 : nat) : (term340 _5240 P _5239) = (term341 P _5239 _5240).
Proof. exact (@lem253351 (term286 P _5239) (term339 _5239 _5240)). Qed.
Lemma lem253360 (P : nat -> Prop) (_5240 : nat) : (term342 P _5240) = (term342 P _5240).
Proof. exact (eq_refl (term342 P _5240)). Qed.
Lemma lem253361 (P : nat -> Prop) (_5239 : nat) (_5240 : nat) : (term338 _5240 P _5239) = (term343 P _5239 _5240).
Proof. exact (MK_COMB (@lem253360 P _5240) (@lem253352 P _5239 _5240)). Qed.
Lemma lem253372 (P : nat -> Prop) (_5239 : nat) (_5240 : nat) : (term320 _5240 P _5239) = (term343 P _5239 _5240).
Proof. exact (TRANS (@lem253337 _5240 P _5239) (@lem253361 P _5239 _5240)). Qed.
Lemma lem253373 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem253374 (P : nat -> Prop) (_5239 : nat) (_5240 : nat) : (term344 _5240 P _5239) = (term345 P _5239 _5240).
Proof. exact (MK_COMB (@lem253373) (@lem253372 P _5239 _5240)). Qed.
Lemma lem253388 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem253389 (P : nat -> Prop) (_5239 : nat) (_5240 : nat) : (term340 _5240 P _5239) = (term341 P _5239 _5240).
Proof. exact (@lem253388 (term286 P _5239) (term339 _5239 _5240)). Qed.
Lemma lem253397 (P : nat -> Prop) (_5240 : nat) : (term342 P _5240) = (term342 P _5240).
Proof. exact (eq_refl (term342 P _5240)). Qed.
Lemma lem253398 (P : nat -> Prop) (_5239 : nat) (_5240 : nat) : (term338 _5240 P _5239) = (term343 P _5239 _5240).
Proof. exact (MK_COMB (@lem253397 P _5240) (@lem253389 P _5239 _5240)). Qed.
Lemma lem253409 (P : nat -> Prop) (_5239 : nat) (_5240 : nat) : ((term320 _5240 P _5239) = (term338 _5240 P _5239)) = ((term343 P _5239 _5240) = (term343 P _5239 _5240)).
Proof. exact (MK_COMB (@lem253374 P _5239 _5240) (@lem253398 P _5239 _5240)). Qed.
Lemma lem253411 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem253412 (x : Prop) : (x = x) = True.
Proof. exact (@lem253411 Prop x). Qed.
Lemma lem253413 (P : nat -> Prop) (_5239 : nat) (_5240 : nat) : ((term343 P _5239 _5240) = (term343 P _5239 _5240)) = True.
Proof. exact (@lem253412 (term343 P _5239 _5240)). Qed.
Lemma lem253414 (_5240 : nat) (P : nat -> Prop) (_5239 : nat) : ((term320 _5240 P _5239) = (term338 _5240 P _5239)) = True.
Proof. exact (TRANS (@lem253409 P _5239 _5240) (@lem253413 P _5239 _5240)). Qed.
Lemma lem253415 (_5240 : nat) (P : nat -> Prop) (_5239 : nat) : True = ((term320 _5240 P _5239) = (term338 _5240 P _5239)).
Proof. exact (SYM (@lem253414 _5240 P _5239)). Qed.
Lemma lem253416 (_5240 : nat) (P : nat -> Prop) (_5239 : nat) : (term320 _5240 P _5239) = (term338 _5240 P _5239).
Proof. exact (EQ_MP (@lem253415 _5240 P _5239) (@lem0)). Qed.
Lemma lem253417 (_5240 : nat) (P : nat -> Prop) (_5239 : nat) : term338 _5240 P _5239.
Proof. exact (EQ_MP (@lem253416 _5240 P _5239) (@lem253163 _5240 P _5239)). Qed.
Lemma lem253419 (b : Prop) (a : Prop) : (a \/ b) = (term325 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem253420 (_5239 : nat) (P : nat -> Prop) (_5240 : nat) : (term338 _5240 P _5239) = (term346 _5239 P _5240).
Proof. exact (@lem253419 (term340 _5240 P _5239) (P _5240)). Qed.
Lemma lem253422 (a : Prop) (b : Prop) : (term347 a b) = (term348 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem253423 (_5240 : nat) (P : nat -> Prop) (_5239 : nat) : (term349 _5240 P _5239) = (term350 _5240 P _5239).
Proof. exact (@lem253422 (term339 _5239 _5240) (term286 P _5239)). Qed.
Lemma lem253425 (a : Prop) : (term327 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem253426 (_5239 : nat) (_5240 : nat) : (term351 _5239 _5240) = (_5239 = _5240).
Proof. exact (@lem253425 (_5239 = _5240)). Qed.
Lemma lem253427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem253428 (_5239 : nat) (_5240 : nat) : (term352 _5239 _5240) = (term353 _5239 _5240).
Proof. exact (MK_COMB (@lem253427) (@lem253426 _5239 _5240)). Qed.
Lemma lem253430 (a : Prop) : (term327 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem253431 (P : nat -> Prop) (_5239 : nat) : (term354 P _5239) = (P _5239).
Proof. exact (@lem253430 (P _5239)). Qed.
Lemma lem253432 (_5240 : nat) (P : nat -> Prop) (_5239 : nat) : (term350 _5240 P _5239) = (term355 _5240 P _5239).
Proof. exact (MK_COMB (@lem253428 _5239 _5240) (@lem253431 P _5239)). Qed.
Lemma lem253433 (_5240 : nat) (P : nat -> Prop) (_5239 : nat) : (term349 _5240 P _5239) = (term355 _5240 P _5239).
Proof. exact (TRANS (@lem253423 _5240 P _5239) (@lem253432 _5240 P _5239)). Qed.
Lemma lem253434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem253435 (_5240 : nat) (P : nat -> Prop) (_5239 : nat) : (term356 _5240 P _5239) = (term357 _5240 P _5239).
Proof. exact (MK_COMB (@lem253434) (@lem253433 _5240 P _5239)). Qed.
Lemma lem253436 (P : nat -> Prop) (_5240 : nat) : (P _5240) = (P _5240).
Proof. exact (eq_refl (P _5240)). Qed.
Lemma lem253437 (_5239 : nat) (P : nat -> Prop) (_5240 : nat) : (term346 _5239 P _5240) = (term358 _5239 P _5240).
Proof. exact (MK_COMB (@lem253435 _5240 P _5239) (@lem253436 P _5240)). Qed.
Lemma lem253438 (_5239 : nat) (P : nat -> Prop) (_5240 : nat) : (term338 _5240 P _5239) = (term358 _5239 P _5240).
Proof. exact (TRANS (@lem253420 _5239 P _5240) (@lem253437 _5239 P _5240)). Qed.
Lemma lem253440 (P : nat -> Prop) (a : nat) (b : nat) (d : nat) (h1 : term84) (h2 : term89) (h3 : term143 a b P d) (h4 : term102 a b d) : term359 P a b.
Proof. exact (conj (@lem253323 a b d h1 h2 h4) (@lem253330 a b P d h3)). Qed.
Lemma lem253442 (_5239 : nat) (P : nat -> Prop) (_5240 : nat) : term358 _5239 P _5240.
Proof. exact (EQ_MP (@lem253438 _5239 P _5240) (@lem253417 _5240 P _5239)). Qed.
Lemma lem253443 (a : nat) (b : nat) (P : nat -> Prop) : term360 a b P.
Proof. exact (@lem253442 (Nat.sub a b) P (NUMERAL 0)). Qed.
Lemma lem253446 (P : nat -> Prop) (a : nat) (b : nat) (d : nat) (h1 : term84) (h2 : term89) (h3 : term143 a b P d) (h4 : term102 a b d) : term361 P.
Proof. exact (@lem253443 a b P (@lem253440 P a b d h1 h2 h3 h4)). Qed.
Lemma lem253447 (P : nat -> Prop) (a : nat) (b : nat) (d : nat) (h1 : term84) (h2 : term89) (h3 : term143 a b P d) (h4 : term102 a b d) : term362 P.
Proof. exact (fun h0 : term299 P => @lem253446 P a b d h1 h2 h3 h4). Qed.
Lemma lem253449 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253450 (P : nat -> Prop) : (term362 P) = (term361 P).
Proof. exact (@lem253449 (term361 P)). Qed.
Lemma lem253451 (P : nat -> Prop) (a : nat) (b : nat) (d : nat) (h1 : term84) (h2 : term89) (h3 : term143 a b P d) (h4 : term102 a b d) : term361 P.
Proof. exact (EQ_MP (@lem253450 P) (@lem253447 P a b d h1 h2 h3 h4)). Qed.
Lemma lem253454 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem253456 (P : nat -> Prop) : (term299 P) = (term363 P).
Proof. exact (@lem253454 (term361 P)). Qed.
Lemma lem253459 (P : nat -> Prop) (a : nat) (b : nat) (d : nat) (h1 : term143 a b P d) (h2 : term102 a b d) : term363 P.
Proof. exact (EQ_MP (@lem253456 P) (@lem253012 P a b d h1 h2)). Qed.
Lemma lem253462 (P : nat -> Prop) (a : nat) (b : nat) (d : nat) (h1 : term84) (h2 : term89) (h3 : term143 a b P d) (h4 : term102 a b d) : False.
Proof. exact (@lem253459 P a b d h3 h4 (@lem253451 P a b d h1 h2 h3 h4)). Qed.
Lemma lem253463 (P : nat -> Prop) (a : nat) (b : nat) (d : nat) (h1 : term84) (h2 : term89) (h3 : term143 a b P d) (h4 : term102 a b d) : term314.
Proof. exact (fun h0 : ~ False => @lem253462 P a b d h1 h2 h3 h4). Qed.
Lemma lem253465 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253466 : term314 = False.
Proof. exact (@lem253465 False). Qed.
Lemma lem253559 (a : nat) (b : nat) (h1 : Peano.lt a b) : Peano.lt a b.
Proof. exact (h1). Qed.
Lemma lem253560 (a : nat) (b : nat) (h1 : Peano.lt a b) : term321 a b.
Proof. exact (fun h0 : term77 a b => @lem253559 a b h1). Qed.
Lemma lem253562 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253563 (a : nat) (b : nat) : (term321 a b) = (Peano.lt a b).
Proof. exact (@lem253562 (Peano.lt a b)). Qed.
Lemma lem253564 (a : nat) (b : nat) (h1 : Peano.lt a b) : Peano.lt a b.
Proof. exact (EQ_MP (@lem253563 a b) (@lem253560 a b h1)). Qed.
Lemma lem253566 (a : nat) (b : nat) (h1 : Peano.lt a b) : Peano.lt a b.
Proof. exact (h1). Qed.
Lemma lem253567 (a : nat) (b : nat) (h1 : Peano.lt a b) : term321 a b.
Proof. exact (fun h0 : term77 a b => @lem253566 a b h1). Qed.
Lemma lem253569 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253570 (a : nat) (b : nat) : (term321 a b) = (Peano.lt a b).
Proof. exact (@lem253569 (Peano.lt a b)). Qed.
Lemma lem253571 (a : nat) (b : nat) (h1 : Peano.lt a b) : Peano.lt a b.
Proof. exact (EQ_MP (@lem253570 a b) (@lem253567 a b h1)). Qed.
Lemma lem253577 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem253578 (_5166 : nat) (_5167 : nat) : (term168 _5166 _5167) = (term322 _5166 _5167).
Proof. exact (@lem253577 (Peano.le _5166 _5167) (term77 _5166 _5167)). Qed.
Lemma lem253584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem253585 (_5166 : nat) (_5167 : nat) : (term323 _5166 _5167) = (term324 _5166 _5167).
Proof. exact (MK_COMB (@lem253584) (@lem253578 _5166 _5167)). Qed.
Lemma lem253591 (_5166 : nat) (_5167 : nat) : (term322 _5166 _5167) = (term322 _5166 _5167).
Proof. exact (eq_refl (term322 _5166 _5167)). Qed.
Lemma lem253592 (_5166 : nat) (_5167 : nat) : ((term168 _5166 _5167) = (term322 _5166 _5167)) = ((term322 _5166 _5167) = (term322 _5166 _5167)).
Proof. exact (MK_COMB (@lem253585 _5166 _5167) (@lem253591 _5166 _5167)). Qed.
Lemma lem253594 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem253595 (x : Prop) : (x = x) = True.
Proof. exact (@lem253594 Prop x). Qed.
Lemma lem253596 (_5166 : nat) (_5167 : nat) : ((term322 _5166 _5167) = (term322 _5166 _5167)) = True.
Proof. exact (@lem253595 (term322 _5166 _5167)). Qed.
Lemma lem253597 (_5166 : nat) (_5167 : nat) : ((term168 _5166 _5167) = (term322 _5166 _5167)) = True.
Proof. exact (TRANS (@lem253592 _5166 _5167) (@lem253596 _5166 _5167)). Qed.
Lemma lem253598 (_5166 : nat) (_5167 : nat) : True = ((term168 _5166 _5167) = (term322 _5166 _5167)).
Proof. exact (SYM (@lem253597 _5166 _5167)). Qed.
Lemma lem253599 (_5166 : nat) (_5167 : nat) : (term168 _5166 _5167) = (term322 _5166 _5167).
Proof. exact (EQ_MP (@lem253598 _5166 _5167) (@lem0)). Qed.
Lemma lem253600 (_5166 : nat) (_5167 : nat) (h1 : term89) : term322 _5166 _5167.
Proof. exact (EQ_MP (@lem253599 _5166 _5167) (@lem252691 _5166 _5167 h1)). Qed.
Lemma lem253602 (b : Prop) (a : Prop) : (a \/ b) = (term325 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem253603 (_5166 : nat) (_5167 : nat) : (term322 _5166 _5167) = (term326 _5166 _5167).
Proof. exact (@lem253602 (term77 _5166 _5167) (Peano.le _5166 _5167)). Qed.
Lemma lem253605 (a : Prop) : (term327 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem253606 (_5166 : nat) (_5167 : nat) : (term227 _5166 _5167) = (Peano.lt _5166 _5167).
Proof. exact (@lem253605 (Peano.lt _5166 _5167)). Qed.
Lemma lem253607 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem253608 (_5166 : nat) (_5167 : nat) : (term328 _5166 _5167) = (term63 _5166 _5167).
Proof. exact (MK_COMB (@lem253607) (@lem253606 _5166 _5167)). Qed.
Lemma lem253609 (_5166 : nat) (_5167 : nat) : (Peano.le _5166 _5167) = (Peano.le _5166 _5167).
Proof. exact (eq_refl (Peano.le _5166 _5167)). Qed.
Lemma lem253610 (_5166 : nat) (_5167 : nat) : (term326 _5166 _5167) = (term85 _5166 _5167).
Proof. exact (MK_COMB (@lem253608 _5166 _5167) (@lem253609 _5166 _5167)). Qed.
Lemma lem253611 (_5166 : nat) (_5167 : nat) : (term322 _5166 _5167) = (term85 _5166 _5167).
Proof. exact (TRANS (@lem253603 _5166 _5167) (@lem253610 _5166 _5167)). Qed.
Lemma lem253614 (_5166 : nat) (_5167 : nat) (h1 : term89) : term85 _5166 _5167.
Proof. exact (EQ_MP (@lem253611 _5166 _5167) (@lem253600 _5166 _5167 h1)). Qed.
Lemma lem253615 (a : nat) (b : nat) (h1 : term89) : term85 a b.
Proof. exact (@lem253614 a b h1). Qed.
Lemma lem253618 (a : nat) (b : nat) (h1 : term89) (h2 : Peano.lt a b) : Peano.le a b.
Proof. exact (@lem253615 a b h1 (@lem253571 a b h2)). Qed.
Lemma lem253619 (a : nat) (b : nat) (h1 : term89) (h2 : Peano.lt a b) : term329 a b.
Proof. exact (fun h0 : term0 a b => @lem253618 a b h1 h2). Qed.
Lemma lem253621 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253622 (a : nat) (b : nat) : (term329 a b) = (Peano.le a b).
Proof. exact (@lem253621 (Peano.le a b)). Qed.
Lemma lem253623 (a : nat) (b : nat) (h1 : term89) (h2 : Peano.lt a b) : Peano.le a b.
Proof. exact (EQ_MP (@lem253622 a b) (@lem253619 a b h1 h2)). Qed.
Lemma lem253625 (b : Prop) (a : Prop) : (a \/ b) = (term325 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem253626 (_5172 : nat) (_5173 : nat) : (term187 _5172 _5173) = (term330 _5172 _5173).
Proof. exact (@lem253625 (term0 _5172 _5173) ((Nat.sub _5172 _5173) = (NUMERAL 0))). Qed.
Lemma lem253628 (a : Prop) : (term327 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem253629 (_5172 : nat) (_5173 : nat) : (term331 _5172 _5173) = (Peano.le _5172 _5173).
Proof. exact (@lem253628 (Peano.le _5172 _5173)). Qed.
Lemma lem253630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem253631 (_5172 : nat) (_5173 : nat) : (term332 _5172 _5173) = (term333 _5172 _5173).
Proof. exact (MK_COMB (@lem253630) (@lem253629 _5172 _5173)). Qed.
Lemma lem253632 (_5172 : nat) (_5173 : nat) : ((Nat.sub _5172 _5173) = (NUMERAL 0)) = ((Nat.sub _5172 _5173) = (NUMERAL 0)).
Proof. exact (eq_refl ((Nat.sub _5172 _5173) = (NUMERAL 0))). Qed.
Lemma lem253633 (_5172 : nat) (_5173 : nat) : (term330 _5172 _5173) = (term334 _5172 _5173).
Proof. exact (MK_COMB (@lem253631 _5172 _5173) (@lem253632 _5172 _5173)). Qed.
Lemma lem253634 (_5172 : nat) (_5173 : nat) : (term187 _5172 _5173) = (term334 _5172 _5173).
Proof. exact (TRANS (@lem253626 _5172 _5173) (@lem253633 _5172 _5173)). Qed.
Lemma lem253637 (_5172 : nat) (_5173 : nat) (h1 : term84) : term334 _5172 _5173.
Proof. exact (EQ_MP (@lem253634 _5172 _5173) (@lem252709 _5172 _5173 h1)). Qed.
Lemma lem253638 (a : nat) (b : nat) (h1 : term84) : term334 a b.
Proof. exact (@lem253637 a b h1). Qed.
Lemma lem253641 (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : Peano.lt a b) : (Nat.sub a b) = (NUMERAL 0).
Proof. exact (@lem253638 a b h1 (@lem253623 a b h2 h3)). Qed.
Lemma lem253642 (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : Peano.lt a b) : term335 a b.
Proof. exact (fun h0 : term336 a b => @lem253641 a b h1 h2 h3). Qed.
Lemma lem253644 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253645 (a : nat) (b : nat) : (term335 a b) = ((Nat.sub a b) = (NUMERAL 0)).
Proof. exact (@lem253644 ((Nat.sub a b) = (NUMERAL 0))). Qed.
Lemma lem253646 (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : Peano.lt a b) : (Nat.sub a b) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem253645 a b) (@lem253642 a b h1 h2 h3)). Qed.
Lemma lem253662 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem253663 (P : nat -> Prop) (_5176 : nat) : (term364 P _5176) = (term365 P _5176).
Proof. exact (@lem253662 (P _5176) (term289 _5176)). Qed.
Lemma lem253671 (a : nat) (b : nat) : (term366 a b) = (term366 a b).
Proof. exact (eq_refl (term366 a b)). Qed.
Lemma lem253672 (a : nat) (b : nat) (P : nat -> Prop) (_5176 : nat) : (term288 a b P _5176) = (term367 a b P _5176).
Proof. exact (MK_COMB (@lem253671 a b) (@lem253663 P _5176)). Qed.
Lemma lem253676 (q : Prop) (p : Prop) (r : Prop) : (term33 p q r) = (term33 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem253677 (P : nat -> Prop) (a : nat) (b : nat) (_5176 : nat) : (term367 a b P _5176) = (term368 P a b _5176).
Proof. exact (@lem253676 (P _5176) (term77 a b) (term289 _5176)). Qed.
Lemma lem253695 (P : nat -> Prop) (a : nat) (b : nat) (_5176 : nat) : (term288 a b P _5176) = (term368 P a b _5176).
Proof. exact (TRANS (@lem253672 a b P _5176) (@lem253677 P a b _5176)). Qed.
Lemma lem253696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem253697 (P : nat -> Prop) (a : nat) (b : nat) (_5176 : nat) : (term369 a b P _5176) = (term370 P a b _5176).
Proof. exact (MK_COMB (@lem253696) (@lem253695 P a b _5176)). Qed.
Lemma lem253715 (P : nat -> Prop) (a : nat) (b : nat) (_5176 : nat) : (term368 P a b _5176) = (term368 P a b _5176).
Proof. exact (eq_refl (term368 P a b _5176)). Qed.
Lemma lem253716 (P : nat -> Prop) (a : nat) (b : nat) (_5176 : nat) : ((term288 a b P _5176) = (term368 P a b _5176)) = ((term368 P a b _5176) = (term368 P a b _5176)).
Proof. exact (MK_COMB (@lem253697 P a b _5176) (@lem253715 P a b _5176)). Qed.
Lemma lem253718 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem253719 (x : Prop) : (x = x) = True.
Proof. exact (@lem253718 Prop x). Qed.
Lemma lem253720 (P : nat -> Prop) (a : nat) (b : nat) (_5176 : nat) : ((term368 P a b _5176) = (term368 P a b _5176)) = True.
Proof. exact (@lem253719 (term368 P a b _5176)). Qed.
Lemma lem253721 (P : nat -> Prop) (a : nat) (b : nat) (_5176 : nat) : ((term288 a b P _5176) = (term368 P a b _5176)) = True.
Proof. exact (TRANS (@lem253716 P a b _5176) (@lem253720 P a b _5176)). Qed.
Lemma lem253722 (P : nat -> Prop) (a : nat) (b : nat) (_5176 : nat) : True = ((term288 a b P _5176) = (term368 P a b _5176)).
Proof. exact (SYM (@lem253721 P a b _5176)). Qed.
Lemma lem253723 (P : nat -> Prop) (a : nat) (b : nat) (_5176 : nat) : (term288 a b P _5176) = (term368 P a b _5176).
Proof. exact (EQ_MP (@lem253722 P a b _5176) (@lem0)). Qed.
Lemma lem253724 (_5176 : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term123 a b P) : term368 P a b _5176.
Proof. exact (EQ_MP (@lem253723 P a b _5176) (@lem252735 _5176 a b P h1)). Qed.
Lemma lem253726 (b : Prop) (a : Prop) : (a \/ b) = (term325 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem253727 (a : nat) (b : nat) (P : nat -> Prop) (_5176 : nat) : (term368 P a b _5176) = (term371 a b P _5176).
Proof. exact (@lem253726 (term97 a b _5176) (P _5176)). Qed.
Lemma lem253729 (a : Prop) (b : Prop) : (term347 a b) = (term348 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem253730 (a : nat) (b : nat) (_5176 : nat) : (term372 a b _5176) = (term373 a b _5176).
Proof. exact (@lem253729 (term77 a b) (term289 _5176)). Qed.
Lemma lem253732 (a : Prop) : (term327 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem253733 (a : nat) (b : nat) : (term227 a b) = (Peano.lt a b).
Proof. exact (@lem253732 (Peano.lt a b)). Qed.
Lemma lem253734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem253735 (a : nat) (b : nat) : (term374 a b) = (term375 a b).
Proof. exact (MK_COMB (@lem253734) (@lem253733 a b)). Qed.
Lemma lem253737 (a : Prop) : (term327 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem253738 (_5176 : nat) : (term376 _5176) = (_5176 = (NUMERAL 0)).
Proof. exact (@lem253737 (_5176 = (NUMERAL 0))). Qed.
Lemma lem253739 (a : nat) (b : nat) (_5176 : nat) : (term373 a b _5176) = (term102 a b _5176).
Proof. exact (MK_COMB (@lem253735 a b) (@lem253738 _5176)). Qed.
Lemma lem253740 (a : nat) (b : nat) (_5176 : nat) : (term372 a b _5176) = (term102 a b _5176).
Proof. exact (TRANS (@lem253730 a b _5176) (@lem253739 a b _5176)). Qed.
Lemma lem253741 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem253742 (a : nat) (b : nat) (_5176 : nat) : (term377 a b _5176) = (term378 a b _5176).
Proof. exact (MK_COMB (@lem253741) (@lem253740 a b _5176)). Qed.
Lemma lem253743 (P : nat -> Prop) (_5176 : nat) : (P _5176) = (P _5176).
Proof. exact (eq_refl (P _5176)). Qed.
Lemma lem253744 (a : nat) (b : nat) (P : nat -> Prop) (_5176 : nat) : (term371 a b P _5176) = (term379 a b P _5176).
Proof. exact (MK_COMB (@lem253742 a b _5176) (@lem253743 P _5176)). Qed.
Lemma lem253745 (a : nat) (b : nat) (P : nat -> Prop) (_5176 : nat) : (term368 P a b _5176) = (term379 a b P _5176).
Proof. exact (TRANS (@lem253727 a b P _5176) (@lem253744 a b P _5176)). Qed.
Lemma lem253747 (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : Peano.lt a b) : term380 a b.
Proof. exact (conj (@lem253564 a b h3) (@lem253646 a b h1 h2 h3)). Qed.
Lemma lem253749 (_5176 : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term123 a b P) : term379 a b P _5176.
Proof. exact (EQ_MP (@lem253745 a b P _5176) (@lem253724 _5176 a b P h1)). Qed.
Lemma lem253750 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term123 a b P) : term381 P a b.
Proof. exact (@lem253749 (Nat.sub a b) a b P h1). Qed.
Lemma lem253753 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : term123 a b P) (h4 : Peano.lt a b) : term40 P a b.
Proof. exact (@lem253750 a b P h3 (@lem253747 a b h1 h2 h4)). Qed.
Lemma lem253754 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : term123 a b P) (h4 : Peano.lt a b) : term337 P a b.
Proof. exact (fun h0 : term287 P a b => @lem253753 P a b h1 h2 h3 h4). Qed.
Lemma lem253756 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253757 (P : nat -> Prop) (a : nat) (b : nat) : (term337 P a b) = (term40 P a b).
Proof. exact (@lem253756 (term40 P a b)). Qed.
Lemma lem253758 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : term123 a b P) (h4 : Peano.lt a b) : term40 P a b.
Proof. exact (EQ_MP (@lem253757 P a b) (@lem253754 P a b h1 h2 h3 h4)). Qed.
Lemma lem253761 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem253763 (P : nat -> Prop) (a : nat) (b : nat) : (term287 P a b) = (term382 P a b).
Proof. exact (@lem253761 (term40 P a b)). Qed.
Lemma lem253766 (a : nat) (b : nat) (P : nat -> Prop) (h1 : term123 a b P) : term382 P a b.
Proof. exact (EQ_MP (@lem253763 P a b) (@lem252717 a b P h1)). Qed.
Lemma lem253769 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : term123 a b P) (h4 : Peano.lt a b) : False.
Proof. exact (@lem253766 a b P h3 (@lem253758 P a b h1 h2 h3 h4)). Qed.
Lemma lem253770 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : term123 a b P) (h4 : Peano.lt a b) : term314.
Proof. exact (fun h0 : ~ False => @lem253769 P a b h1 h2 h3 h4). Qed.
Lemma lem253772 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem253773 : term314 = False.
Proof. exact (@lem253772 False). Qed.
Lemma lem253774 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : term123 a b P) (h4 : Peano.lt a b) : False.
Proof. exact (EQ_MP (@lem253773) (@lem253770 P a b h1 h2 h3 h4)). Qed.
Lemma lem253775 (P : nat -> Prop) (a : nat) (b : nat) (d : nat) (h1 : term84) (h2 : term89) (h3 : term143 a b P d) (h4 : term102 a b d) : False.
Proof. exact (EQ_MP (@lem253466) (@lem253463 P a b d h1 h2 h3 h4)). Qed.
Lemma lem253776 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : False.
Proof. exact (EQ_MP (@lem253150) (@lem253147 a b d h1 h2 h3 h4)). Qed.
Lemma lem253777 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : term123 a b P) (h4 : Peano.lt a b) : (Peano.lt a b) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt a b => @lem253774 P a b h1 h2 h3 h4) (fun h5 : False => @lem252683 a b h4)). Qed.
Lemma lem253778 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : term123 a b P) (h4 : Peano.lt a b) : False.
Proof. exact (EQ_MP (@lem253777 P a b h1 h2 h3 h4) (@lem252683 a b h4)). Qed.
Lemma lem253779 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : (a = (Nat.add b d)) = False.
Proof. exact (prop_ext (fun h5 : a = (Nat.add b d) => @lem253776 a b d h1 h2 h3 h4) (fun h5 : False => @lem252639 a b d h4)). Qed.
Lemma lem253780 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : False.
Proof. exact (EQ_MP (@lem253779 a b d h1 h2 h3 h4) (@lem252639 a b d h4)). Qed.
Lemma lem253781 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : (Peano.lt a b) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt a b => @lem253780 a b d h1 h2 h3 h4) (fun h5 : False => @lem252601 a b h3)). Qed.
Lemma lem253782 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : False.
Proof. exact (EQ_MP (@lem253781 a b d h1 h2 h3 h4) (@lem252601 a b h3)). Qed.
Lemma lem253783 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : term123 a b P) (h4 : Peano.lt a b) : (Peano.lt a b) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt a b => @lem253778 P a b h1 h2 h3 h4) (fun h5 : False => @lem252363 a b h4)). Qed.
Lemma lem253784 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : term123 a b P) (h4 : Peano.lt a b) : False.
Proof. exact (EQ_MP (@lem253783 P a b h1 h2 h3 h4) (@lem252363 a b h4)). Qed.
Lemma lem253785 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : (a = (Nat.add b d)) = False.
Proof. exact (prop_ext (fun h5 : a = (Nat.add b d) => @lem253782 a b d h1 h2 h3 h4) (fun h5 : False => @lem252249 a b d h4)). Qed.
Lemma lem253786 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : False.
Proof. exact (EQ_MP (@lem253785 a b d h1 h2 h3 h4) (@lem252249 a b d h4)). Qed.
Lemma lem253787 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : (Peano.lt a b) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt a b => @lem253786 a b d h1 h2 h3 h4) (fun h5 : False => @lem252147 a b h3)). Qed.
Lemma lem253788 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : False.
Proof. exact (EQ_MP (@lem253787 a b d h1 h2 h3 h4) (@lem252147 a b h3)). Qed.
Lemma lem253789 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : term123 a b P) (h4 : Peano.lt a b) : (Peano.lt a b) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt a b => @lem253784 P a b h1 h2 h3 h4) (fun h5 : False => @lem252363 a b h4)). Qed.
Lemma lem253790 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term84) (h2 : term89) (h3 : term123 a b P) (h4 : Peano.lt a b) : False.
Proof. exact (EQ_MP (@lem253789 P a b h1 h2 h3 h4) (@lem252363 a b h4)). Qed.
Lemma lem253791 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : (a = (Nat.add b d)) = False.
Proof. exact (prop_ext (fun h5 : a = (Nat.add b d) => @lem253788 a b d h1 h2 h3 h4) (fun h5 : False => @lem252249 a b d h4)). Qed.
Lemma lem253792 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : False.
Proof. exact (EQ_MP (@lem253791 a b d h1 h2 h3 h4) (@lem252249 a b d h4)). Qed.
Lemma lem253793 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : term92 = False.
Proof. exact (prop_ext (fun h5 : term92 => @lem253792 a b d h1 h2 h3 h4) (fun h5 : False => @lem252157 h1)). Qed.
Lemma lem253794 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : False.
Proof. exact (EQ_MP (@lem253793 a b d h1 h2 h3 h4) (@lem252157 h1)). Qed.
Lemma lem253795 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : (Peano.lt a b) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt a b => @lem253794 a b d h1 h2 h3 h4) (fun h5 : False => @lem252147 a b h3)). Qed.
Lemma lem253796 (a : nat) (b : nat) (d : nat) (h1 : term92) (h2 : term50) (h3 : Peano.lt a b) (h4 : a = (Nat.add b d)) : False.
Proof. exact (EQ_MP (@lem253795 a b d h1 h2 h3 h4) (@lem252147 a b h3)). Qed.
Lemma lem253797 (P : nat -> Prop) (d : nat) (a : nat) (b : nat) (h1 : term92) (h2 : term50) (h3 : term84) (h4 : term89) (h5 : term143 a b P d) (h6 : Peano.lt a b) : False.
Proof. exact (or_elim (@lem252137 a b P d h5) (fun h0 : a = (Nat.add b d) => @lem253796 a b d h1 h2 h6 h0) (fun h0 : term102 a b d => @lem253775 P a b d h3 h4 h5 h0)). Qed.
Lemma lem253798 (d : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term92) (h2 : term50) (h3 : term84) (h4 : term89) (h5 : Peano.lt a b) (h6 : term164 d a b P) : False.
Proof. exact (or_elim (@lem252127 d a b P h6) (fun h0 : term143 a b P d => @lem253797 P d a b h1 h2 h3 h4 h0 h5) (fun h0 : term123 a b P => @lem253790 P a b h3 h4 h0 h5)). Qed.
Lemma lem253799 (d : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term92) (h2 : term50) (h3 : term84) (h4 : term89) (h5 : Peano.lt a b) (h6 : term164 d a b P) : (term164 d a b P) = False.
Proof. exact (prop_ext (fun h7 : term164 d a b P => @lem253798 d a b P h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem252127 d a b P h6)). Qed.
Lemma lem253800 (d : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term92) (h2 : term50) (h3 : term84) (h4 : term89) (h5 : Peano.lt a b) (h6 : term164 d a b P) : False.
Proof. exact (EQ_MP (@lem253799 d a b P h1 h2 h3 h4 h5 h6) (@lem252127 d a b P h6)). Qed.
Lemma lem253801 (d : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term92) (h2 : term50) (h3 : term84) (h4 : term89) (h5 : Peano.lt a b) (h6 : term164 d a b P) : term92 = False.
Proof. exact (prop_ext (fun h7 : term92 => @lem253800 d a b P h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem251898 h1)). Qed.
Lemma lem253802 (d : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term92) (h2 : term50) (h3 : term84) (h4 : term89) (h5 : Peano.lt a b) (h6 : term164 d a b P) : False.
Proof. exact (EQ_MP (@lem253801 d a b P h1 h2 h3 h4 h5 h6) (@lem251898 h1)). Qed.
Lemma lem253803 (d : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term92) (h2 : term50) (h3 : term84) (h4 : term89) (h5 : Peano.lt a b) (h6 : term164 d a b P) : (Peano.lt a b) = False.
Proof. exact (prop_ext (fun h7 : Peano.lt a b => @lem253802 d a b P h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem251882 a b h5)). Qed.
Lemma lem253804 (d : nat) (a : nat) (b : nat) (P : nat -> Prop) (h1 : term92) (h2 : term50) (h3 : term84) (h4 : term89) (h5 : Peano.lt a b) (h6 : term164 d a b P) : False.
Proof. exact (EQ_MP (@lem253803 d a b P h1 h2 h3 h4 h5 h6) (@lem251882 a b h5)). Qed.
Lemma lem253805 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term92) (h2 : term50) (h3 : term84) (h4 : term89) (h5 : term43 a b P) (h6 : Peano.lt a b) : False.
Proof. exact (ex_elim (@lem251209 a b P h5) (fun d : nat => fun h0 : term166 a b P d => @lem253804 d a b P h1 h2 h3 h4 h6 h0)). Qed.
Lemma lem253806 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term92) (h2 : term50) (h3 : term84) (h4 : term89) (h5 : term43 a b P) (h6 : Peano.lt a b) : term92 = False.
Proof. exact (prop_ext (fun h7 : term92 => @lem253805 P a b h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem251229 h1)). Qed.
Lemma lem253807 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term92) (h2 : term50) (h3 : term84) (h4 : term89) (h5 : term43 a b P) (h6 : Peano.lt a b) : False.
Proof. exact (EQ_MP (@lem253806 P a b h1 h2 h3 h4 h5 h6) (@lem251229 h1)). Qed.
Lemma lem253808 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term92) (h2 : term50) (h3 : term84) (h4 : term89) (h5 : term43 a b P) (h6 : Peano.lt a b) : (Peano.lt a b) = False.
Proof. exact (prop_ext (fun h7 : Peano.lt a b => @lem253807 P a b h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem251016 a b h6)). Qed.
Lemma lem253809 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term92) (h2 : term50) (h3 : term84) (h4 : term89) (h5 : term43 a b P) (h6 : Peano.lt a b) : False.
Proof. exact (EQ_MP (@lem253808 P a b h1 h2 h3 h4 h5 h6) (@lem251016 a b h6)). Qed.
Lemma lem253810 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term92) (h2 : term84) (h3 : term89) (h4 : term43 a b P) (h5 : Peano.lt a b) : term48.
Proof. exact (fun h0 : term50 => @lem253809 P a b h1 h0 h2 h3 h4 h5). Qed.
Lemma lem253811 : term48 = term49.
Proof. exact (@lem69 term50). Qed.
Lemma lem253812 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term92) (h2 : term84) (h3 : term89) (h4 : term43 a b P) (h5 : Peano.lt a b) : term49.
Proof. exact (EQ_MP (@lem253811) (@lem253810 P a b h1 h2 h3 h4 h5)). Qed.
Lemma lem253813 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term92) (h2 : term89) (h3 : term43 a b P) (h4 : Peano.lt a b) : term53.
Proof. exact (fun h0 : term84 => @lem253812 P a b h1 h0 h2 h3 h4). Qed.
Lemma lem253814 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term92) (h2 : term43 a b P) (h3 : Peano.lt a b) : term56.
Proof. exact (fun h0 : term89 => @lem253813 P a b h1 h0 h2 h3). Qed.
Lemma lem253815 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term43 a b P) (h2 : Peano.lt a b) : term59.
Proof. exact (fun h0 : term92 => @lem253814 P a b h0 h1 h2). Qed.
Lemma lem253816 (P : nat -> Prop) (a : nat) (b : nat) (h1 : Peano.lt a b) : term62 a b P.
Proof. exact (fun h0 : term43 a b P => @lem253815 P a b h0 h1). Qed.
Lemma lem253817 (a : nat) (b : nat) (P : nat -> Prop) : term64 a b P.
Proof. exact (fun h0 : Peano.lt a b => @lem253816 P a b h0). Qed.
Lemma lem253822 (b : nat) (P : nat -> Prop) : term68 b P.
Proof. exact (fun a : nat => @lem253817 a b P). Qed.
Lemma lem253827 (P : nat -> Prop) : term72 P.
Proof. exact (fun b : nat => @lem253822 b P). Qed.
Lemma lem253832 : term76.
Proof. exact (fun P : nat -> Prop => @lem253827 P). Qed.
Lemma lem253833 : term75.
Proof. exact (EQ_MP (@lem251004) (@lem253832)). Qed.
Lemma lem253834 (P : nat -> Prop) : term383 P.
Proof. exact (@lem253833 P). Qed.
Lemma lem253835 (P : nat -> Prop) : (term383 P) = (term71 P).
Proof. exact (eq_refl (term383 P)). Qed.
Lemma lem253836 (P : nat -> Prop) : term71 P.
Proof. exact (EQ_MP (@lem253835 P) (@lem253834 P)). Qed.
Lemma lem253837 (P : nat -> Prop) (b : nat) : term384 P b.
Proof. exact (@lem253836 P b). Qed.
Lemma lem253838 (b : nat) (P : nat -> Prop) : (term384 P b) = (term67 b P).
Proof. exact (eq_refl (term384 P b)). Qed.
Lemma lem253839 (b : nat) (P : nat -> Prop) : term67 b P.
Proof. exact (EQ_MP (@lem253838 b P) (@lem253837 P b)). Qed.
Lemma lem253840 (b : nat) (P : nat -> Prop) (a : nat) : term385 b P a.
Proof. exact (@lem253839 b P a). Qed.
Lemma lem253841 (a : nat) (b : nat) (P : nat -> Prop) : (term385 b P a) = (term44 a b P).
Proof. exact (eq_refl (term385 b P a)). Qed.
Lemma lem253842 (a : nat) (b : nat) (P : nat -> Prop) : term44 a b P.
Proof. exact (EQ_MP (@lem253841 a b P) (@lem253840 b P a)). Qed.
Lemma lem253844 (a : nat) (b : nat) (P : nat -> Prop) : term44 a b P.
Proof. exact (@lem250705 a b P (@lem253842 a b P)). Qed.
Lemma lem253845 (P : nat -> Prop) (a : nat) (b : nat) (h1 : Peano.lt a b) : term61 a b P.
Proof. exact (@lem253844 a b P (@lem250684 a b h1)). Qed.
Lemma lem253846 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term43 a b P) (h2 : Peano.lt a b) : term58.
Proof. exact (@lem253845 P a b h2 (@lem250690 a b P h1)). Qed.
Lemma lem253847 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term43 a b P) (h2 : Peano.lt a b) : term55.
Proof. exact (@lem253846 P a b h1 h2 (@lem100517)). Qed.
Lemma lem253848 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term43 a b P) (h2 : Peano.lt a b) : term52.
Proof. exact (@lem253847 P a b h1 h2 (@lem98439)). Qed.
Lemma lem253849 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term43 a b P) (h2 : Peano.lt a b) : term48.
Proof. exact (@lem253848 P a b h1 h2 (@lem136259)). Qed.
Lemma lem253850 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term43 a b P) (h2 : Peano.lt a b) : False.
Proof. exact (@lem253849 P a b h1 h2 (@lem98377)). Qed.
Lemma lem253851 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term43 a b P) (h2 : Peano.lt a b) : (term43 a b P) = False.
Proof. exact (prop_ext (fun h3 : term43 a b P => @lem253850 P a b h1 h2) (fun h3 : False => @lem250690 a b P h1)). Qed.
Lemma lem253852 (P : nat -> Prop) (a : nat) (b : nat) (h1 : term43 a b P) (h2 : Peano.lt a b) : False.
Proof. exact (EQ_MP (@lem253851 P a b h1 h2) (@lem250690 a b P h1)). Qed.
Lemma lem253853 (P : nat -> Prop) (a : nat) (b : nat) (h1 : Peano.lt a b) : term42 a b P.
Proof. exact (fun h0 : term43 a b P => @lem253852 P a b h0 h1). Qed.
Lemma lem253854 (P : nat -> Prop) (a : nat) (b : nat) (h1 : Peano.lt a b) : (term40 P a b) = (term41 a b P).
Proof. exact (EQ_MP (@lem250689 a b P) (@lem253853 P a b h1)). Qed.
Lemma lem253856 (n : nat) (m : nat) : (Peano.le m n) = (term27 n m).
Proof. exact (EQ_MP (@lem250666 n m) (@lem250665 m n)). Qed.
Lemma lem253857 (a : nat) (b : nat) : (Peano.le b a) = (term27 a b).
Proof. exact (@lem253856 a b). Qed.
Lemma lem253864 (b : nat) (a : nat) (h1 : Peano.le b a) : term27 a b.
Proof. exact (EQ_MP (@lem253857 a b) (@lem250685 b a h1)). Qed.
Lemma lem253865 (a : nat) (b : nat) (e : nat) (h1 : a = (Nat.add b e)) : a = (Nat.add b e).
Proof. exact (h1). Qed.
Lemma lem253866 (b : nat) (P : nat -> Prop) : (term386 b P) = (term386 b P).
Proof. exact (eq_refl (term386 b P)). Qed.
Lemma lem253867 (P : nat -> Prop) (a : nat) (b : nat) (e : nat) (h1 : a = (Nat.add b e)) : (term387 b P a) = (term388 P b e).
Proof. exact (MK_COMB (@lem253866 b P) (@lem253865 a b e h1)). Qed.
Lemma lem253868 (e : nat) (b : nat) (P : nat -> Prop) : (term388 P b e) = ((term389 P e b) = (term390 e b P)).
Proof. exact (eq_refl (term388 P b e)). Qed.
Lemma lem253869 (b : nat) (P : nat -> Prop) (a : nat) : (term391 b P a) = (term391 b P a).
Proof. exact (eq_refl (term391 b P a)). Qed.
Lemma lem253870 (a : nat) (e : nat) (b : nat) (P : nat -> Prop) : ((term387 b P a) = (term388 P b e)) = ((term387 b P a) = ((term389 P e b) = (term390 e b P))).
Proof. exact (MK_COMB (@lem253869 b P a) (@lem253868 e b P)). Qed.
Lemma lem253871 (a : nat) (b : nat) (P : nat -> Prop) : (term387 b P a) = ((term40 P a b) = (term41 a b P)).
Proof. exact (eq_refl (term387 b P a)). Qed.
Lemma lem253872 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem253873 (a : nat) (b : nat) (P : nat -> Prop) : (term391 b P a) = (term392 a b P).
Proof. exact (MK_COMB (@lem253872) (@lem253871 a b P)). Qed.
Lemma lem253874 (e : nat) (b : nat) (P : nat -> Prop) : ((term389 P e b) = (term390 e b P)) = ((term389 P e b) = (term390 e b P)).
Proof. exact (eq_refl ((term389 P e b) = (term390 e b P))). Qed.
Lemma lem253875 (a : nat) (e : nat) (b : nat) (P : nat -> Prop) : ((term387 b P a) = ((term389 P e b) = (term390 e b P))) = (((term40 P a b) = (term41 a b P)) = ((term389 P e b) = (term390 e b P))).
Proof. exact (MK_COMB (@lem253873 a b P) (@lem253874 e b P)). Qed.
Lemma lem253876 (a : nat) (e : nat) (b : nat) (P : nat -> Prop) : ((term387 b P a) = (term388 P b e)) = (((term40 P a b) = (term41 a b P)) = ((term389 P e b) = (term390 e b P))).
Proof. exact (TRANS (@lem253870 a e b P) (@lem253875 a e b P)). Qed.
Lemma lem253877 (P : nat -> Prop) (a : nat) (b : nat) (e : nat) (h1 : a = (Nat.add b e)) : ((term40 P a b) = (term41 a b P)) = ((term389 P e b) = (term390 e b P)).
Proof. exact (EQ_MP (@lem253876 a e b P) (@lem253867 P a b e h1)). Qed.
Lemma lem253878 (P : nat -> Prop) (a : nat) (b : nat) (e : nat) (h1 : a = (Nat.add b e)) : ((term389 P e b) = (term390 e b P)) = ((term40 P a b) = (term41 a b P)).
Proof. exact (SYM (@lem253877 P a b e h1)). Qed.
Lemma lem253882 (m : nat) (n : nat) : (term23 n m) = n.
Proof. exact (EQ_MP (@lem250660 m n) (@lem250659 m n)). Qed.
Lemma lem253883 (b : nat) (e : nat) : (term23 e b) = e.
Proof. exact (@lem253882 b e). Qed.
Lemma lem253884 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem253885 (b : nat) (P : nat -> Prop) (e : nat) : (term389 P e b) = (P e).
Proof. exact (MK_COMB (@lem253884 P) (@lem253883 b e)). Qed.
Lemma lem253886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem253887 (b : nat) (P : nat -> Prop) (e : nat) : (term393 P e b) = (term394 P e).
Proof. exact (MK_COMB (@lem253886) (@lem253885 b P e)). Qed.
Lemma lem253895 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term395 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem253896 (p : Prop) (q : Prop) (p' : Prop) : term396 p q p'.
Proof. exact (fun q' : Prop => @lem253895 p q p' q'). Qed.
Lemma lem253897 (p : Prop) (q : Prop) : term397 p q.
Proof. exact (fun p' : Prop => @lem253896 p q p'). Qed.
Lemma lem253898 (e : nat) (b : nat) (P : nat -> Prop) (d : nat) : term398 e b P d.
Proof. exact (@lem253897 (term399 e b d) (P d)). Qed.
Lemma lem253899 (e : nat) (b : nat) (P : nat -> Prop) (d : nat) (p' : Prop) : term400 e b P d p'.
Proof. exact (@lem253898 e b P d p'). Qed.
Lemma lem253900 (e : nat) (b : nat) (P : nat -> Prop) (d : nat) (p' : Prop) : (term400 e b P d p') = (term401 e b P d p').
Proof. exact (eq_refl (term400 e b P d p')). Qed.
Lemma lem253901 (e : nat) (b : nat) (P : nat -> Prop) (d : nat) (p' : Prop) : term401 e b P d p'.
Proof. exact (EQ_MP (@lem253900 e b P d p') (@lem253899 e b P d p')). Qed.
Lemma lem253902 (e : nat) (b : nat) (P : nat -> Prop) (d : nat) (p' : Prop) (q' : Prop) : term402 e b P d p' q'.
Proof. exact (@lem253901 e b P d p' q'). Qed.
Lemma lem253903 (e : nat) (b : nat) (P : nat -> Prop) (d : nat) (p' : Prop) (q' : Prop) : (term402 e b P d p' q') = (term403 e b P d p' q').
Proof. exact (eq_refl (term402 e b P d p' q')). Qed.
Lemma lem253904 (e : nat) (b : nat) (P : nat -> Prop) (d : nat) (p' : Prop) (q' : Prop) : term403 e b P d p' q'.
Proof. exact (EQ_MP (@lem253903 e b P d p' q') (@lem253902 e b P d p' q')). Qed.
Lemma lem253908 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem250640 m n p) (@lem250639 m n p)). Qed.
Lemma lem253909 (b : nat) (e : nat) (d : nat) : ((Nat.add b e) = (Nat.add b d)) = (e = d).
Proof. exact (@lem253908 b e d). Qed.
Lemma lem253912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem253913 (b : nat) (e : nat) (d : nat) : (term404 e b d) = (term405 e d).
Proof. exact (MK_COMB (@lem253912) (@lem253909 b e d)). Qed.
Lemma lem253919 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem250654 m n) (@lem250653 m n)). Qed.
Lemma lem253920 (b : nat) (e : nat) : (term293 e b) = (term306 b e).
Proof. exact (@lem253919 b (Nat.add b e)). Qed.
Lemma lem253922 (m : nat) (n : nat) : (term17 m n) = True.
Proof. exact (EQ_MP (@lem250648 m n) (@lem250647 m n)). Qed.
Lemma lem253923 (b : nat) (e : nat) : (term17 b e) = True.
Proof. exact (@lem253922 b e). Qed.
Lemma lem253924 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem253925 (b : nat) (e : nat) : (term306 b e) = (~ True).
Proof. exact (MK_COMB (@lem253924) (@lem253923 b e)). Qed.
Lemma lem253927 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem253928 (b : nat) (e : nat) : (term306 b e) = False.
Proof. exact (TRANS (@lem253925 b e) (@lem253927)). Qed.
Lemma lem253929 (e : nat) (b : nat) : (term293 e b) = False.
Proof. exact (TRANS (@lem253920 b e) (@lem253928 b e)). Qed.
Lemma lem253930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem253931 (e : nat) (b : nat) : (term406 e b) = (and False).
Proof. exact (MK_COMB (@lem253930) (@lem253929 e b)). Qed.
Lemma lem253934 (d : nat) : (d = (NUMERAL 0)) = (d = (NUMERAL 0)).
Proof. exact (eq_refl (d = (NUMERAL 0))). Qed.
Lemma lem253935 (e : nat) (b : nat) (d : nat) : (term407 e b d) = (term408 d).
Proof. exact (MK_COMB (@lem253931 e b) (@lem253934 d)). Qed.
Lemma lem253937 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem253938 (d : nat) : (term408 d) = False.
Proof. exact (@lem253937 (d = (NUMERAL 0))). Qed.
Lemma lem253939 (e : nat) (b : nat) (d : nat) : (term407 e b d) = False.
Proof. exact (TRANS (@lem253935 e b d) (@lem253938 d)). Qed.
Lemma lem253940 (b : nat) (e : nat) (d : nat) : (term399 e b d) = (term409 e d).
Proof. exact (MK_COMB (@lem253913 b e d) (@lem253939 e b d)). Qed.
Lemma lem253942 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem253943 (e : nat) (d : nat) : (term409 e d) = (e = d).
Proof. exact (@lem253942 (e = d)). Qed.
Lemma lem253946 (b : nat) (e : nat) (d : nat) : (term399 e b d) = (e = d).
Proof. exact (TRANS (@lem253940 b e d) (@lem253943 e d)). Qed.
Lemma lem253947 (b : nat) (P : nat -> Prop) (e : nat) (d : nat) (q' : Prop) : term410 b P e d q'.
Proof. exact (@lem253904 e b P d (e = d) q'). Qed.
Lemma lem253948 (b : nat) (P : nat -> Prop) (e : nat) (d : nat) (q' : Prop) : term411 b P e d q'.
Proof. exact (@lem253947 b P e d q' (@lem253946 b e d)). Qed.
Lemma lem253950 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem253951 (e : nat) (P : nat -> Prop) (d : nat) : term412 e P d.
Proof. exact (fun h0 : e = d => @lem253950 P d). Qed.
Lemma lem253952 (b : nat) (e : nat) (P : nat -> Prop) (d : nat) : term413 b e P d.
Proof. exact (@lem253948 b P e d (P d)). Qed.
Lemma lem253953 (b : nat) (e : nat) (P : nat -> Prop) (d : nat) : (term414 e b P d) = (term415 e P d).
Proof. exact (@lem253952 b e P d (@lem253951 e P d)). Qed.
Lemma lem253981 (b : nat) (e : nat) (P : nat -> Prop) : (term416 e b P) = (term417 e P).
Proof. exact (fun_ext (fun d : nat => @lem253953 b e P d)). Qed.
Lemma lem254009 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem254010 (b : nat) (e : nat) (P : nat -> Prop) : (term390 e b P) = (term418 e P).
Proof. exact (MK_COMB (@lem254009) (@lem253981 b e P)). Qed.
Lemma lem254042 (b : nat) (e : nat) (P : nat -> Prop) : ((term389 P e b) = (term390 e b P)) = ((P e) = (term418 e P)).
Proof. exact (MK_COMB (@lem253887 b P e) (@lem254010 b e P)). Qed.
Lemma lem254076 (e : nat) (b : nat) (P : nat -> Prop) : ((P e) = (term418 e P)) = ((term389 P e b) = (term390 e b P)).
Proof. exact (SYM (@lem254042 b e P)). Qed.
Lemma lem254078 (p : Prop) : p = (term39 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem254079 (e : nat) (P : nat -> Prop) : ((P e) = (term418 e P)) = (term419 e P).
Proof. exact (@lem254078 ((P e) = (term418 e P))). Qed.
Lemma lem254080 (e : nat) (P : nat -> Prop) : (term419 e P) = ((P e) = (term418 e P)).
Proof. exact (SYM (@lem254079 e P)). Qed.
Lemma lem254081 (e : nat) (P : nat -> Prop) (h1 : term420 e P) : term420 e P.
Proof. exact (h1). Qed.
Lemma lem254084 (e : nat) (P : nat -> Prop) (h1 : term419 e P) : term419 e P.
Proof. exact (h1). Qed.
Lemma lem254085 (e : nat) (P : nat -> Prop) : term421 e P.
Proof. exact (fun h0 : term419 e P => @lem254084 e P h0). Qed.
Lemma lem254086 (e : nat) (P : nat -> Prop) (h1 : term421 e P) : term421 e P.
Proof. exact (h1). Qed.
Lemma lem254087 (e : nat) (P : nat -> Prop) (h1 : term419 e P) : term419 e P.
Proof. exact (h1). Qed.
Lemma lem254088 (e : nat) (P : nat -> Prop) (h1 : term419 e P) (h2 : term421 e P) : term419 e P.
Proof. exact (@lem254086 e P h2 (@lem254087 e P h1)). Qed.
Lemma lem254089 (e : nat) (P : nat -> Prop) (h1 : term419 e P) : term422 e P.
Proof. exact (fun h0 : term421 e P => @lem254088 e P h1 h0). Qed.
Lemma lem254090 (e : nat) (P : nat -> Prop) (h1 : term421 e P) : term421 e P.
Proof. exact (h1). Qed.
Lemma lem254091 (e : nat) (P : nat -> Prop) (h1 : term419 e P) (h2 : term421 e P) : term419 e P.
Proof. exact (@lem254089 e P h1 (@lem254090 e P h2)). Qed.
Lemma lem254092 (e : nat) (P : nat -> Prop) (h1 : term421 e P) : term421 e P.
Proof. exact (fun h0 : term419 e P => @lem254091 e P h0 h1). Qed.
Lemma lem254093 (e : nat) (P : nat -> Prop) : term423 e P.
Proof. exact (fun h0 : term421 e P => @lem254092 e P h0). Qed.
Lemma lem254096 (e : nat) (P : nat -> Prop) : term421 e P.
Proof. exact (@lem254093 e P (@lem254085 e P)). Qed.
Lemma lem254106 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem254107 (e : nat) (P : nat -> Prop) : (term419 e P) = (term424 e P).
Proof. exact (@lem254106 (term420 e P)). Qed.
Lemma lem254109 (t : Prop) : (term327 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem254110 (e : nat) (P : nat -> Prop) : (term424 e P) = ((P e) = (term418 e P)).
Proof. exact (@lem254109 ((P e) = (term418 e P))). Qed.
Lemma lem254111 (e : nat) (P : nat -> Prop) : (term419 e P) = ((P e) = (term418 e P)).
Proof. exact (TRANS (@lem254107 e P) (@lem254110 e P)). Qed.
Lemma lem254118 (P : nat -> Prop) : (term425 P) = (term426 P).
Proof. exact (fun_ext (fun e : nat => @lem254111 e P)). Qed.
Lemma lem254119 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem254120 (P : nat -> Prop) : (term427 P) = (term428 P).
Proof. exact (MK_COMB (@lem254119) (@lem254118 P)). Qed.
Lemma lem254125 : term429 = term430.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem254120 P)). Qed.
Lemma lem254126 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem254135 : term431 = term432.
Proof. exact (MK_COMB (@lem254126) (@lem254125)). Qed.
Lemma lem254140 (e : nat) (P : nat -> Prop) (d : nat) : (term415 e P d) = (term415 e P d).
Proof. exact (eq_refl (term415 e P d)). Qed.
Lemma lem254141 (e : nat) (P : nat -> Prop) : (term417 e P) = (term417 e P).
Proof. exact (fun_ext (fun d : nat => @lem254140 e P d)). Qed.
Lemma lem254142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem254143 (e : nat) (P : nat -> Prop) : (term418 e P) = (term418 e P).
Proof. exact (MK_COMB (@lem254142) (@lem254141 e P)). Qed.
Lemma lem254146 (P : nat -> Prop) (e : nat) : (term394 P e) = (term394 P e).
Proof. exact (eq_refl (term394 P e)). Qed.
Lemma lem254147 (e : nat) (P : nat -> Prop) : ((P e) = (term418 e P)) = ((P e) = (term418 e P)).
Proof. exact (MK_COMB (@lem254146 P e) (@lem254143 e P)). Qed.
Lemma lem254148 (P : nat -> Prop) : (term426 P) = (term426 P).
Proof. exact (fun_ext (fun e : nat => @lem254147 e P)). Qed.
Lemma lem254149 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem254150 (P : nat -> Prop) : (term428 P) = (term428 P).
Proof. exact (MK_COMB (@lem254149) (@lem254148 P)). Qed.
Lemma lem254151 : term430 = term430.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem254150 P)). Qed.
Lemma lem254152 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem254153 : term432 = term432.
Proof. exact (MK_COMB (@lem254152) (@lem254151)). Qed.
Lemma lem254176 : term431 = term432.
Proof. exact (TRANS (@lem254135) (@lem254153)). Qed.
Lemma lem254177 : term432 = term431.
Proof. exact (SYM (@lem254176)). Qed.
Lemma lem254179 (p : Prop) : p = (term39 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem254180 (e : nat) (P : nat -> Prop) : ((P e) = (term418 e P)) = (term419 e P).
Proof. exact (@lem254179 ((P e) = (term418 e P))). Qed.
Lemma lem254181 (e : nat) (P : nat -> Prop) : (term419 e P) = ((P e) = (term418 e P)).
Proof. exact (SYM (@lem254180 e P)). Qed.
Lemma lem254182 (e : nat) (P : nat -> Prop) (h1 : term420 e P) : term420 e P.
Proof. exact (h1). Qed.
Lemma lem254193 (e : nat) (P : nat -> Prop) (d : nat) : (term433 e P d) = (term434 e P d).
Proof. exact (@lem17362 (e = d) (P d)). Qed.
Lemma lem254198 (e : nat) (P : nat -> Prop) (d : nat) : (term415 e P d) = (term435 e P d).
Proof. exact (@lem17265 (e = d) (P d)). Qed.
Lemma lem254199 (P : nat -> Prop) : (term110 P) = (term111 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem254200 (e : nat) (P : nat -> Prop) : (term436 e P) = (term437 e P).
Proof. exact (@lem254199 (term417 e P)). Qed.
Lemma lem254201 (e : nat) (P : nat -> Prop) (d : nat) : (term438 e P d) = (term415 e P d).
Proof. exact (eq_refl (term438 e P d)). Qed.
Lemma lem254202 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem254203 (e : nat) (P : nat -> Prop) (d : nat) : (term439 e P d) = (term433 e P d).
Proof. exact (MK_COMB (@lem254202) (@lem254201 e P d)). Qed.
Lemma lem254204 (e : nat) (P : nat -> Prop) (d : nat) : (term439 e P d) = (term434 e P d).
Proof. exact (TRANS (@lem254203 e P d) (@lem254193 e P d)). Qed.
Lemma lem254205 (e : nat) (P : nat -> Prop) : (term440 e P) = (term441 e P).
Proof. exact (fun_ext (fun d : nat => @lem254204 e P d)). Qed.
Lemma lem254206 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem254207 (e : nat) (P : nat -> Prop) : (term437 e P) = (term442 e P).
Proof. exact (MK_COMB (@lem254206) (@lem254205 e P)). Qed.
Lemma lem254208 (e : nat) (P : nat -> Prop) : (term436 e P) = (term442 e P).
Proof. exact (TRANS (@lem254200 e P) (@lem254207 e P)). Qed.
Lemma lem254209 (e : nat) (P : nat -> Prop) : (term417 e P) = (term443 e P).
Proof. exact (fun_ext (fun d : nat => @lem254198 e P d)). Qed.
Lemma lem254210 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem254211 (e : nat) (P : nat -> Prop) : (term418 e P) = (term444 e P).
Proof. exact (MK_COMB (@lem254210) (@lem254209 e P)). Qed.
Lemma lem254213 (P : nat -> Prop) (e : nat) : (term445 P e) = (term445 P e).
Proof. exact (eq_refl (term445 P e)). Qed.
Lemma lem254214 (e : nat) (P : nat -> Prop) : (term446 e P) = (term447 e P).
Proof. exact (MK_COMB (@lem254213 P e) (@lem254211 e P)). Qed.
Lemma lem254216 (P : nat -> Prop) (e : nat) : (term448 P e) = (term448 P e).
Proof. exact (eq_refl (term448 P e)). Qed.
Lemma lem254217 (e : nat) (P : nat -> Prop) : (term449 e P) = (term450 e P).
Proof. exact (MK_COMB (@lem254216 P e) (@lem254208 e P)). Qed.
Lemma lem254218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem254219 (e : nat) (P : nat -> Prop) : (term451 e P) = (term452 e P).
Proof. exact (MK_COMB (@lem254218) (@lem254217 e P)). Qed.
Lemma lem254220 (e : nat) (P : nat -> Prop) : (term453 e P) = (term454 e P).
Proof. exact (MK_COMB (@lem254219 e P) (@lem254214 e P)). Qed.
Lemma lem254221 (e : nat) (P : nat -> Prop) : (term420 e P) = (term453 e P).
Proof. exact (@lem17646 (P e) (term418 e P)). Qed.
Lemma lem254222 (e : nat) (P : nat -> Prop) : (term420 e P) = (term454 e P).
Proof. exact (TRANS (@lem254221 e P) (@lem254220 e P)). Qed.
Lemma lem254305 {A : Type'} (P : Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem254306 (P : Prop) (Q : nat -> Prop) : (term133 P Q) = (term134 P Q).
Proof. exact (@lem254305 nat P Q). Qed.
Lemma lem254307 (e : nat) (P : nat -> Prop) : (term455 e P) = (term456 e P).
Proof. exact (@lem254306 (P e) (term441 e P)). Qed.
Lemma lem254308 (e : nat) (P : nat -> Prop) (d : nat) : (term457 e P d) = (term434 e P d).
Proof. exact (eq_refl (term457 e P d)). Qed.
Lemma lem254309 (e : nat) (P : nat -> Prop) : (term458 e P) = (term441 e P).
Proof. exact (fun_ext (fun d : nat => @lem254308 e P d)). Qed.
Lemma lem254310 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem254311 (e : nat) (P : nat -> Prop) : (term459 e P) = (term442 e P).
Proof. exact (MK_COMB (@lem254310) (@lem254309 e P)). Qed.
Lemma lem254312 (P : nat -> Prop) (e : nat) : (term448 P e) = (term448 P e).
Proof. exact (eq_refl (term448 P e)). Qed.
Lemma lem254313 (e : nat) (P : nat -> Prop) : (term455 e P) = (term450 e P).
Proof. exact (MK_COMB (@lem254312 P e) (@lem254311 e P)). Qed.
Lemma lem254314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem254315 (e : nat) (P : nat -> Prop) : (term460 e P) = (term461 e P).
Proof. exact (MK_COMB (@lem254314) (@lem254313 e P)). Qed.
Lemma lem254316 (e : nat) (P : nat -> Prop) (d : nat) : (term457 e P d) = (term434 e P d).
Proof. exact (eq_refl (term457 e P d)). Qed.
Lemma lem254317 (P : nat -> Prop) (e : nat) : (term448 P e) = (term448 P e).
Proof. exact (eq_refl (term448 P e)). Qed.
Lemma lem254318 (e : nat) (P : nat -> Prop) (d : nat) : (term462 e P d) = (term463 e P d).
Proof. exact (MK_COMB (@lem254317 P e) (@lem254316 e P d)). Qed.
Lemma lem254319 (e : nat) (P : nat -> Prop) : (term464 e P) = (term465 e P).
Proof. exact (fun_ext (fun d : nat => @lem254318 e P d)). Qed.
Lemma lem254320 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem254321 (e : nat) (P : nat -> Prop) : (term456 e P) = (term466 e P).
Proof. exact (MK_COMB (@lem254320) (@lem254319 e P)). Qed.
Lemma lem254322 (e : nat) (P : nat -> Prop) : ((term455 e P) = (term456 e P)) = ((term450 e P) = (term466 e P)).
Proof. exact (MK_COMB (@lem254315 e P) (@lem254321 e P)). Qed.
Lemma lem254323 (e : nat) (P : nat -> Prop) : (term450 e P) = (term466 e P).
Proof. exact (EQ_MP (@lem254322 e P) (@lem254307 e P)). Qed.
Lemma lem254324 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem254325 (e : nat) (P : nat -> Prop) : (term452 e P) = (term467 e P).
Proof. exact (MK_COMB (@lem254324) (@lem254323 e P)). Qed.
Lemma lem254326 (e : nat) (P : nat -> Prop) : (term447 e P) = (term447 e P).
Proof. exact (eq_refl (term447 e P)). Qed.
Lemma lem254327 (e : nat) (P : nat -> Prop) : (term454 e P) = (term468 e P).
Proof. exact (MK_COMB (@lem254325 e P) (@lem254326 e P)). Qed.
Lemma lem254329 {A : Type'} (P : A -> Prop) (Q : Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem254330 (P : nat -> Prop) (Q : Prop) : (term151 P Q) = (term152 P Q).
Proof. exact (@lem254329 nat P Q). Qed.
Lemma lem254331 (e : nat) (P : nat -> Prop) : (term469 e P) = (term470 e P).
Proof. exact (@lem254330 (term465 e P) (term447 e P)). Qed.
Lemma lem254332 (e : nat) (P : nat -> Prop) (d : nat) : (term471 e P d) = (term463 e P d).
Proof. exact (eq_refl (term471 e P d)). Qed.
Lemma lem254333 (e : nat) (P : nat -> Prop) : (term472 e P) = (term465 e P).
Proof. exact (fun_ext (fun d : nat => @lem254332 e P d)). Qed.
Lemma lem254334 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem254335 (e : nat) (P : nat -> Prop) : (term473 e P) = (term466 e P).
Proof. exact (MK_COMB (@lem254334) (@lem254333 e P)). Qed.
Lemma lem254336 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem254337 (e : nat) (P : nat -> Prop) : (term474 e P) = (term467 e P).
Proof. exact (MK_COMB (@lem254336) (@lem254335 e P)). Qed.
Lemma lem254338 (e : nat) (P : nat -> Prop) : (term447 e P) = (term447 e P).
Proof. exact (eq_refl (term447 e P)). Qed.
Lemma lem254339 (e : nat) (P : nat -> Prop) : (term469 e P) = (term468 e P).
Proof. exact (MK_COMB (@lem254337 e P) (@lem254338 e P)). Qed.
Lemma lem254340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem254341 (e : nat) (P : nat -> Prop) : (term475 e P) = (term476 e P).
Proof. exact (MK_COMB (@lem254340) (@lem254339 e P)). Qed.
Lemma lem254342 (e : nat) (P : nat -> Prop) (d : nat) : (term471 e P d) = (term463 e P d).
Proof. exact (eq_refl (term471 e P d)). Qed.
Lemma lem254343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem254344 (e : nat) (P : nat -> Prop) (d : nat) : (term477 e P d) = (term478 e P d).
Proof. exact (MK_COMB (@lem254343) (@lem254342 e P d)). Qed.
Lemma lem254345 (e : nat) (P : nat -> Prop) : (term447 e P) = (term447 e P).
Proof. exact (eq_refl (term447 e P)). Qed.
Lemma lem254346 (d : nat) (e : nat) (P : nat -> Prop) : (term479 d e P) = (term480 d e P).
Proof. exact (MK_COMB (@lem254344 e P d) (@lem254345 e P)). Qed.
Lemma lem254347 (e : nat) (P : nat -> Prop) : (term481 e P) = (term482 e P).
Proof. exact (fun_ext (fun d : nat => @lem254346 d e P)). Qed.
Lemma lem254348 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem254349 (e : nat) (P : nat -> Prop) : (term470 e P) = (term483 e P).
Proof. exact (MK_COMB (@lem254348) (@lem254347 e P)). Qed.
Lemma lem254350 (e : nat) (P : nat -> Prop) : ((term469 e P) = (term470 e P)) = ((term468 e P) = (term483 e P)).
Proof. exact (MK_COMB (@lem254341 e P) (@lem254349 e P)). Qed.
Lemma lem254351 (e : nat) (P : nat -> Prop) : (term468 e P) = (term483 e P).
Proof. exact (EQ_MP (@lem254350 e P) (@lem254331 e P)). Qed.
Lemma lem254353 (e : nat) (P : nat -> Prop) : (term454 e P) = (term483 e P).
Proof. exact (TRANS (@lem254327 e P) (@lem254351 e P)). Qed.
Lemma lem254354 (e : nat) (P : nat -> Prop) : (term420 e P) = (term483 e P).
Proof. exact (TRANS (@lem254222 e P) (@lem254353 e P)). Qed.
Lemma lem254355 (e : nat) (P : nat -> Prop) (h1 : term420 e P) : term483 e P.
Proof. exact (EQ_MP (@lem254354 e P) (@lem254182 e P h1)). Qed.
Lemma lem254356 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term480 d e P) : term480 d e P.
Proof. exact (h1). Qed.
Lemma lem254369 (e : nat) (P : nat -> Prop) (d : nat) : (term435 e P d) = (term435 e P d).
Proof. exact (eq_refl (term435 e P d)). Qed.
Lemma lem254370 (e : nat) (P : nat -> Prop) : (term443 e P) = (term443 e P).
Proof. exact (fun_ext (fun d : nat => @lem254369 e P d)). Qed.
Lemma lem254371 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem254372 (e : nat) (P : nat -> Prop) : (term444 e P) = (term444 e P).
Proof. exact (MK_COMB (@lem254371) (@lem254370 e P)). Qed.
Lemma lem254379 (P : nat -> Prop) (e : nat) : (term445 P e) = (term445 P e).
Proof. exact (eq_refl (term445 P e)). Qed.
Lemma lem254380 (e : nat) (P : nat -> Prop) : (term447 e P) = (term447 e P).
Proof. exact (MK_COMB (@lem254379 P e) (@lem254372 e P)). Qed.
Lemma lem254401 (e : nat) (P : nat -> Prop) (d : nat) : (term478 e P d) = (term478 e P d).
Proof. exact (eq_refl (term478 e P d)). Qed.
Lemma lem254402 (d : nat) (e : nat) (P : nat -> Prop) : (term480 d e P) = (term480 d e P).
Proof. exact (MK_COMB (@lem254401 e P d) (@lem254380 e P)). Qed.
Lemma lem254403 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term480 d e P) : term480 d e P.
Proof. exact (EQ_MP (@lem254402 d e P) (@lem254356 d e P h1)). Qed.
Lemma lem254404 (e : nat) (P : nat -> Prop) (d : nat) (h1 : term463 e P d) : term463 e P d.
Proof. exact (h1). Qed.
Lemma lem254405 (e : nat) (P : nat -> Prop) (h1 : term447 e P) : term447 e P.
Proof. exact (h1). Qed.
Lemma lem254406 (e : nat) (P : nat -> Prop) (d : nat) (h1 : term463 e P d) : term434 e P d.
Proof. exact (proj2 (@lem254404 e P d h1)). Qed.
Lemma lem254410 (e : nat) (P : nat -> Prop) (h1 : term447 e P) : term444 e P.
Proof. exact (proj2 (@lem254405 e P h1)). Qed.
Lemma lem254435 (e : nat) (P : nat -> Prop) (d : nat) : (term435 e P d) = (term435 e P d).
Proof. exact (eq_refl (term435 e P d)). Qed.
Lemma lem254436 (e : nat) (P : nat -> Prop) : (term443 e P) = (term443 e P).
Proof. exact (fun_ext (fun d : nat => @lem254435 e P d)). Qed.
Lemma lem254437 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem254439 (e : nat) (P : nat -> Prop) : (term444 e P) = (term444 e P).
Proof. exact (MK_COMB (@lem254437) (@lem254436 e P)). Qed.
Lemma lem254440 (e : nat) (P : nat -> Prop) (h1 : term447 e P) : term444 e P.
Proof. exact (EQ_MP (@lem254439 e P) (@lem254410 e P h1)). Qed.
Lemma lem254441 (_5281 : nat) (e : nat) (P : nat -> Prop) (h1 : term447 e P) : term484 e P _5281.
Proof. exact (@lem254440 e P h1 _5281). Qed.
Lemma lem254442 (e : nat) (P : nat -> Prop) (_5281 : nat) : (term484 e P _5281) = (term435 e P _5281).
Proof. exact (eq_refl (term484 e P _5281)). Qed.
Lemma lem254445 (e : nat) (P : nat -> Prop) (d : nat) (h1 : term463 e P d) : P e.
Proof. exact (proj1 (@lem254404 e P d h1)). Qed.
Lemma lem254447 (e : nat) (P : nat -> Prop) (d : nat) (h1 : term463 e P d) : e = d.
Proof. exact (proj1 (@lem254406 e P d h1)). Qed.
Lemma lem254451 (e : nat) (P : nat -> Prop) (h1 : term447 e P) : term286 P e.
Proof. exact (proj1 (@lem254405 e P h1)). Qed.
Lemma lem254457 (_5281 : nat) (e : nat) (P : nat -> Prop) (h1 : term447 e P) : term435 e P _5281.
Proof. exact (EQ_MP (@lem254442 e P _5281) (@lem254441 _5281 e P h1)). Qed.
Lemma lem254472 (P : nat -> Prop) : (term485 P) = (term485 P).
Proof. exact (eq_refl (term485 P)). Qed.
Lemma lem254473 (e : nat) (P : nat -> Prop) (d : nat) (h1 : term463 e P d) : (term486 P e) = (term486 P d).
Proof. exact (MK_COMB (@lem254472 P) (@lem254447 e P d h1)). Qed.
Lemma lem254474 (P : nat -> Prop) (d : nat) : (term486 P d) = (P d).
Proof. exact (eq_refl (term486 P d)). Qed.
Lemma lem254475 (P : nat -> Prop) (e : nat) : (term487 P e) = (term487 P e).
Proof. exact (eq_refl (term487 P e)). Qed.
Lemma lem254476 (e : nat) (P : nat -> Prop) (d : nat) : ((term486 P e) = (term486 P d)) = ((term486 P e) = (P d)).
Proof. exact (MK_COMB (@lem254475 P e) (@lem254474 P d)). Qed.
Lemma lem254477 (P : nat -> Prop) (e : nat) : (term486 P e) = (P e).
Proof. exact (eq_refl (term486 P e)). Qed.
Lemma lem254478 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem254479 (P : nat -> Prop) (e : nat) : (term487 P e) = (term394 P e).
Proof. exact (MK_COMB (@lem254478) (@lem254477 P e)). Qed.
Lemma lem254480 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem254481 (e : nat) (P : nat -> Prop) (d : nat) : ((term486 P e) = (P d)) = ((P e) = (P d)).
Proof. exact (MK_COMB (@lem254479 P e) (@lem254480 P d)). Qed.
Lemma lem254482 (e : nat) (P : nat -> Prop) (d : nat) : ((term486 P e) = (term486 P d)) = ((P e) = (P d)).
Proof. exact (TRANS (@lem254476 e P d) (@lem254481 e P d)). Qed.
Lemma lem254483 (e : nat) (P : nat -> Prop) (d : nat) (h1 : term463 e P d) : (P e) = (P d).
Proof. exact (EQ_MP (@lem254482 e P d) (@lem254473 e P d h1)). Qed.
Lemma lem254498 (e : nat) (P : nat -> Prop) (d : nat) (h1 : term463 e P d) : term286 P d.
Proof. exact (proj2 (@lem254406 e P d h1)). Qed.
Lemma lem254500 (e : nat) (P : nat -> Prop) (d : nat) (h1 : term463 e P d) : P d.
Proof. exact (EQ_MP (@lem254483 e P d h1) (@lem254445 e P d h1)). Qed.
Lemma lem254501 (e : nat) (P : nat -> Prop) (d : nat) (h1 : term463 e P d) : term488 P d.
Proof. exact (fun h0 : term286 P d => @lem254500 e P d h1). Qed.
Lemma lem254503 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem254504 (P : nat -> Prop) (d : nat) : (term488 P d) = (P d).
Proof. exact (@lem254503 (P d)). Qed.
Lemma lem254505 (e : nat) (P : nat -> Prop) (d : nat) (h1 : term463 e P d) : P d.
Proof. exact (EQ_MP (@lem254504 P d) (@lem254501 e P d h1)). Qed.
Lemma lem254508 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem254510 (P : nat -> Prop) (d : nat) : (term286 P d) = (term489 P d).
Proof. exact (@lem254508 (P d)). Qed.
Lemma lem254513 (e : nat) (P : nat -> Prop) (d : nat) (h1 : term463 e P d) : term489 P d.
Proof. exact (EQ_MP (@lem254510 P d) (@lem254498 e P d h1)). Qed.
Lemma lem254516 (e : nat) (P : nat -> Prop) (d : nat) (h1 : term463 e P d) : False.
Proof. exact (@lem254513 e P d h1 (@lem254505 e P d h1)). Qed.
Lemma lem254517 (e : nat) (P : nat -> Prop) (d : nat) (h1 : term463 e P d) : term314.
Proof. exact (fun h0 : ~ False => @lem254516 e P d h1). Qed.
Lemma lem254519 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem254520 : term314 = False.
Proof. exact (@lem254519 False). Qed.
Lemma lem254537 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem254538 (e : nat) : e = e.
Proof. exact (@lem254537 e). Qed.
Lemma lem254539 (e : nat) : term490 e.
Proof. exact (fun h0 : term491 e => @lem254538 e). Qed.
Lemma lem254541 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem254542 (e : nat) : (term490 e) = (e = e).
Proof. exact (@lem254541 (e = e)). Qed.
Lemma lem254543 (e : nat) : e = e.
Proof. exact (EQ_MP (@lem254542 e) (@lem254539 e)). Qed.
Lemma lem254549 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem254550 (P : nat -> Prop) (e : nat) (_5281 : nat) : (term435 e P _5281) = (term492 P e _5281).
Proof. exact (@lem254549 (P _5281) (term339 e _5281)). Qed.
Lemma lem254558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem254559 (P : nat -> Prop) (e : nat) (_5281 : nat) : (term493 e P _5281) = (term494 P e _5281).
Proof. exact (MK_COMB (@lem254558) (@lem254550 P e _5281)). Qed.
Lemma lem254567 (P : nat -> Prop) (e : nat) (_5281 : nat) : (term492 P e _5281) = (term492 P e _5281).
Proof. exact (eq_refl (term492 P e _5281)). Qed.
Lemma lem254568 (P : nat -> Prop) (e : nat) (_5281 : nat) : ((term435 e P _5281) = (term492 P e _5281)) = ((term492 P e _5281) = (term492 P e _5281)).
Proof. exact (MK_COMB (@lem254559 P e _5281) (@lem254567 P e _5281)). Qed.
Lemma lem254570 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem254571 (x : Prop) : (x = x) = True.
Proof. exact (@lem254570 Prop x). Qed.
Lemma lem254572 (P : nat -> Prop) (e : nat) (_5281 : nat) : ((term492 P e _5281) = (term492 P e _5281)) = True.
Proof. exact (@lem254571 (term492 P e _5281)). Qed.
Lemma lem254573 (P : nat -> Prop) (e : nat) (_5281 : nat) : ((term435 e P _5281) = (term492 P e _5281)) = True.
Proof. exact (TRANS (@lem254568 P e _5281) (@lem254572 P e _5281)). Qed.
Lemma lem254574 (P : nat -> Prop) (e : nat) (_5281 : nat) : True = ((term435 e P _5281) = (term492 P e _5281)).
Proof. exact (SYM (@lem254573 P e _5281)). Qed.
Lemma lem254575 (P : nat -> Prop) (e : nat) (_5281 : nat) : (term435 e P _5281) = (term492 P e _5281).
Proof. exact (EQ_MP (@lem254574 P e _5281) (@lem0)). Qed.
Lemma lem254576 (_5281 : nat) (e : nat) (P : nat -> Prop) (h1 : term447 e P) : term492 P e _5281.
Proof. exact (EQ_MP (@lem254575 P e _5281) (@lem254457 _5281 e P h1)). Qed.
Lemma lem254578 (b : Prop) (a : Prop) : (a \/ b) = (term325 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem254579 (e : nat) (P : nat -> Prop) (_5281 : nat) : (term492 P e _5281) = (term495 e P _5281).
Proof. exact (@lem254578 (term339 e _5281) (P _5281)). Qed.
Lemma lem254581 (a : Prop) : (term327 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem254582 (e : nat) (_5281 : nat) : (term351 e _5281) = (e = _5281).
Proof. exact (@lem254581 (e = _5281)). Qed.
Lemma lem254583 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem254584 (e : nat) (_5281 : nat) : (term496 e _5281) = (term497 e _5281).
Proof. exact (MK_COMB (@lem254583) (@lem254582 e _5281)). Qed.
Lemma lem254585 (P : nat -> Prop) (_5281 : nat) : (P _5281) = (P _5281).
Proof. exact (eq_refl (P _5281)). Qed.
Lemma lem254586 (e : nat) (P : nat -> Prop) (_5281 : nat) : (term495 e P _5281) = (term415 e P _5281).
Proof. exact (MK_COMB (@lem254584 e _5281) (@lem254585 P _5281)). Qed.
Lemma lem254587 (e : nat) (P : nat -> Prop) (_5281 : nat) : (term492 P e _5281) = (term415 e P _5281).
Proof. exact (TRANS (@lem254579 e P _5281) (@lem254586 e P _5281)). Qed.
Lemma lem254590 (_5281 : nat) (e : nat) (P : nat -> Prop) (h1 : term447 e P) : term415 e P _5281.
Proof. exact (EQ_MP (@lem254587 e P _5281) (@lem254576 _5281 e P h1)). Qed.
Lemma lem254591 (e : nat) (P : nat -> Prop) (h1 : term447 e P) : term498 P e.
Proof. exact (@lem254590 e e P h1). Qed.
Lemma lem254594 (e : nat) (P : nat -> Prop) (h1 : term447 e P) : P e.
Proof. exact (@lem254591 e P h1 (@lem254543 e)). Qed.
Lemma lem254595 (e : nat) (P : nat -> Prop) (h1 : term447 e P) : term488 P e.
Proof. exact (fun h0 : term286 P e => @lem254594 e P h1). Qed.
Lemma lem254597 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem254598 (P : nat -> Prop) (e : nat) : (term488 P e) = (P e).
Proof. exact (@lem254597 (P e)). Qed.
Lemma lem254599 (e : nat) (P : nat -> Prop) (h1 : term447 e P) : P e.
Proof. exact (EQ_MP (@lem254598 P e) (@lem254595 e P h1)). Qed.
Lemma lem254602 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem254604 (P : nat -> Prop) (e : nat) : (term286 P e) = (term489 P e).
Proof. exact (@lem254602 (P e)). Qed.
Lemma lem254607 (e : nat) (P : nat -> Prop) (h1 : term447 e P) : term489 P e.
Proof. exact (EQ_MP (@lem254604 P e) (@lem254451 e P h1)). Qed.
Lemma lem254610 (e : nat) (P : nat -> Prop) (h1 : term447 e P) : False.
Proof. exact (@lem254607 e P h1 (@lem254599 e P h1)). Qed.
Lemma lem254611 (e : nat) (P : nat -> Prop) (h1 : term447 e P) : term314.
Proof. exact (fun h0 : ~ False => @lem254610 e P h1). Qed.
Lemma lem254613 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem254614 : term314 = False.
Proof. exact (@lem254613 False). Qed.
Lemma lem254615 (e : nat) (P : nat -> Prop) (h1 : term447 e P) : False.
Proof. exact (EQ_MP (@lem254614) (@lem254611 e P h1)). Qed.
Lemma lem254616 (e : nat) (P : nat -> Prop) (d : nat) (h1 : term463 e P d) : False.
Proof. exact (EQ_MP (@lem254520) (@lem254517 e P d h1)). Qed.
Lemma lem254617 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term480 d e P) : False.
Proof. exact (or_elim (@lem254403 d e P h1) (fun h0 : term463 e P d => @lem254616 e P d h0) (fun h0 : term447 e P => @lem254615 e P h0)). Qed.
Lemma lem254618 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term480 d e P) : (term480 d e P) = False.
Proof. exact (prop_ext (fun h2 : term480 d e P => @lem254617 d e P h1) (fun h2 : False => @lem254403 d e P h1)). Qed.
Lemma lem254619 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term480 d e P) : False.
Proof. exact (EQ_MP (@lem254618 d e P h1) (@lem254403 d e P h1)). Qed.
Lemma lem254620 (e : nat) (P : nat -> Prop) (h1 : term420 e P) : False.
Proof. exact (ex_elim (@lem254355 e P h1) (fun d : nat => fun h0 : term482 e P d => @lem254619 d e P h0)). Qed.
Lemma lem254621 (e : nat) (P : nat -> Prop) (h1 : term420 e P) : (term420 e P) = False.
Proof. exact (prop_ext (fun h2 : term420 e P => @lem254620 e P h1) (fun h2 : False => @lem254182 e P h1)). Qed.
Lemma lem254622 (e : nat) (P : nat -> Prop) (h1 : term420 e P) : False.
Proof. exact (EQ_MP (@lem254621 e P h1) (@lem254182 e P h1)). Qed.
Lemma lem254623 (e : nat) (P : nat -> Prop) : term419 e P.
Proof. exact (fun h0 : term420 e P => @lem254622 e P h0). Qed.
Lemma lem254624 (e : nat) (P : nat -> Prop) : (P e) = (term418 e P).
Proof. exact (EQ_MP (@lem254181 e P) (@lem254623 e P)). Qed.
Lemma lem254629 (P : nat -> Prop) : term428 P.
Proof. exact (fun e : nat => @lem254624 e P). Qed.
Lemma lem254634 : term432.
Proof. exact (fun P : nat -> Prop => @lem254629 P). Qed.
Lemma lem254635 : term431.
Proof. exact (EQ_MP (@lem254177) (@lem254634)). Qed.
Lemma lem254636 (P : nat -> Prop) : term499 P.
Proof. exact (@lem254635 P). Qed.
Lemma lem254637 (P : nat -> Prop) : (term499 P) = (term427 P).
Proof. exact (eq_refl (term499 P)). Qed.
Lemma lem254638 (P : nat -> Prop) : term427 P.
Proof. exact (EQ_MP (@lem254637 P) (@lem254636 P)). Qed.
Lemma lem254639 (P : nat -> Prop) (e : nat) : term500 P e.
Proof. exact (@lem254638 P e). Qed.
Lemma lem254640 (e : nat) (P : nat -> Prop) : (term500 P e) = (term419 e P).
Proof. exact (eq_refl (term500 P e)). Qed.
Lemma lem254641 (e : nat) (P : nat -> Prop) : term419 e P.
Proof. exact (EQ_MP (@lem254640 e P) (@lem254639 P e)). Qed.
Lemma lem254643 (e : nat) (P : nat -> Prop) : term419 e P.
Proof. exact (@lem254096 e P (@lem254641 e P)). Qed.
Lemma lem254644 (e : nat) (P : nat -> Prop) (h1 : term420 e P) : False.
Proof. exact (@lem254643 e P (@lem254081 e P h1)). Qed.
Lemma lem254645 (e : nat) (P : nat -> Prop) (h1 : term420 e P) : (term420 e P) = False.
Proof. exact (prop_ext (fun h2 : term420 e P => @lem254644 e P h1) (fun h2 : False => @lem254081 e P h1)). Qed.
Lemma lem254646 (e : nat) (P : nat -> Prop) (h1 : term420 e P) : False.
Proof. exact (EQ_MP (@lem254645 e P h1) (@lem254081 e P h1)). Qed.
Lemma lem254647 (e : nat) (P : nat -> Prop) : term419 e P.
Proof. exact (fun h0 : term420 e P => @lem254646 e P h0). Qed.
Lemma lem254648 (e : nat) (P : nat -> Prop) : (P e) = (term418 e P).
Proof. exact (EQ_MP (@lem254080 e P) (@lem254647 e P)). Qed.
Lemma lem254649 (e : nat) (b : nat) (P : nat -> Prop) : (term389 P e b) = (term390 e b P).
Proof. exact (EQ_MP (@lem254076 e b P) (@lem254648 e P)). Qed.
Lemma lem254650 (P : nat -> Prop) (a : nat) (b : nat) (e : nat) (h1 : a = (Nat.add b e)) : (term40 P a b) = (term41 a b P).
Proof. exact (EQ_MP (@lem253878 P a b e h1) (@lem254649 e b P)). Qed.
Lemma lem254651 (P : nat -> Prop) (b : nat) (a : nat) (h1 : Peano.le b a) : (term40 P a b) = (term41 a b P).
Proof. exact (ex_elim (@lem253864 b a h1) (fun e : nat => fun h0 : term501 a b e => @lem254650 P a b e h0)). Qed.
Lemma lem254652 (a : nat) (b : nat) (P : nat -> Prop) : (term40 P a b) = (term41 a b P).
Proof. exact (or_elim (@lem250683 b a) (fun h0 : Peano.lt a b => @lem253854 P a b h0) (fun h0 : Peano.le b a => @lem254651 P b a h0)). Qed.
