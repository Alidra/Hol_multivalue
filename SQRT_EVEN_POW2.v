Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_EVEN_POW2_term_abbrevs.
Require Import ARITH_EQ_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import DIV_MULT_spec.
Require Import EVEN_EXISTS_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import MULT_SYM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_POS_spec.
Require Import REAL_POW_LE_spec.
Require Import REAL_POW_POW_spec.
Require Import SQRT_UNIQUE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Lemma lem1962564 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1962565 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1962566 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1962565 t1) (@lem1962564 t1)). Qed.
Lemma lem1962567 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1962566 t1 t2). Qed.
Lemma lem1962568 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1962569 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1962568 t1 t2) (@lem1962567 t1 t2)). Qed.
Lemma lem1962570 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1962569 t1 t2 t3). Qed.
Lemma lem1962571 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1962572 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1962571 t1 t2 t3) (@lem1962570 t1 t2 t3)). Qed.
Lemma lem1962573 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1962572 t1 t2 t3)). Qed.
Lemma lem1962574 : term7.
Proof. exact (proj2 (@lem522076)). Qed.
Lemma lem1962575 : term8.
Proof. exact (proj2 (@lem1962574)). Qed.
Lemma lem1962576 : term9.
Proof. exact (proj2 (@lem1962575)). Qed.
Lemma lem1962618 : term10.
Proof. exact (proj1 (@lem1962576)). Qed.
Lemma lem1962619 (n : nat) : term11 n.
Proof. exact (@lem1962618 n). Qed.
Lemma lem1962620 (n : nat) : (term11 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem1962622 : term12.
Proof. exact (proj1 (@lem1962575)). Qed.
Lemma lem1962623 (n : nat) : term13 n.
Proof. exact (@lem1962622 n). Qed.
Lemma lem1962624 (n : nat) : (term13 n) = (((BIT0 n) = 0) = (n = 0)).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem1962627 : term14.
Proof. exact (proj1 (@lem522076)). Qed.
Lemma lem1962628 (m : nat) : term15 m.
Proof. exact (@lem1962627 m). Qed.
Lemma lem1962629 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1962630 (m : nat) : term16 m.
Proof. exact (EQ_MP (@lem1962629 m) (@lem1962628 m)). Qed.
Lemma lem1962631 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem1962630 m n). Qed.
Lemma lem1962632 (m : nat) (n : nat) : (term17 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem1962634 (m : nat) : term18 m.
Proof. exact (@lem170527 m). Qed.
Lemma lem1962635 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1962636 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem1962635 m) (@lem1962634 m)). Qed.
Lemma lem1962637 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem1962636 m n). Qed.
Lemma lem1962638 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem1962639 (m : nat) (n : nat) : term21 m n.
Proof. exact (EQ_MP (@lem1962638 m n) (@lem1962637 m n)). Qed.
Lemma lem1962640 (m : nat) (h1 : term22 m) : term22 m.
Proof. exact (h1). Qed.
Lemma lem1962641 (n : nat) (m : nat) (h1 : term22 m) : (term23 n m) = n.
Proof. exact (@lem1962639 m n (@lem1962640 m h1)). Qed.
Lemma lem1962647 {A : Type'} (P : A -> Prop) : term24 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem1962648 {A : Type'} (P : A -> Prop) : (term24 A P) = (term25 A P).
Proof. exact (eq_refl (term24 A P)). Qed.
Lemma lem1962649 {A : Type'} (P : A -> Prop) : term25 A P.
Proof. exact (EQ_MP (@lem1962648 A P) (@lem1962647 A P)). Qed.
Lemma lem1962650 {A : Type'} (P : A -> Prop) (Q : Prop) : term26 A P Q.
Proof. exact (@lem1962649 A P Q). Qed.
Lemma lem1962651 {A : Type'} (P : A -> Prop) (Q : Prop) : (term26 A P Q) = ((term27 A P Q) = (term28 A P Q)).
Proof. exact (eq_refl (term26 A P Q)). Qed.
Lemma lem1962653 (n : nat) : term29 n.
Proof. exact (@lem128828 n). Qed.
Lemma lem1962654 (n : nat) : (term29 n) = ((Coq.Arith.PeanoNat.Nat.Even n) = (term30 n)).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem1962663 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term31 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1962664 (p : Prop) (q : Prop) (p' : Prop) : term32 p q p'.
Proof. exact (fun q' : Prop => @lem1962663 p q p' q'). Qed.
Lemma lem1962665 (p : Prop) (q : Prop) : term33 p q.
Proof. exact (fun p' : Prop => @lem1962664 p q p'). Qed.
Lemma lem1962666 (n : nat) : term34 n.
Proof. exact (@lem1962665 (Coq.Arith.PeanoNat.Nat.Even n) ((term35 n) = (term36 n))). Qed.
Lemma lem1962667 (n : nat) (p' : Prop) : term37 n p'.
Proof. exact (@lem1962666 n p'). Qed.
Lemma lem1962668 (n : nat) (p' : Prop) : (term37 n p') = (term38 n p').
Proof. exact (eq_refl (term37 n p')). Qed.
Lemma lem1962669 (n : nat) (p' : Prop) : term38 n p'.
Proof. exact (EQ_MP (@lem1962668 n p') (@lem1962667 n p')). Qed.
Lemma lem1962670 (n : nat) (p' : Prop) (q' : Prop) : term39 n p' q'.
Proof. exact (@lem1962669 n p' q'). Qed.
Lemma lem1962671 (n : nat) (p' : Prop) (q' : Prop) : (term39 n p' q') = (term40 n p' q').
Proof. exact (eq_refl (term39 n p' q')). Qed.
Lemma lem1962672 (n : nat) (p' : Prop) (q' : Prop) : term40 n p' q'.
Proof. exact (EQ_MP (@lem1962671 n p' q') (@lem1962670 n p' q')). Qed.
Lemma lem1962674 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (term30 n).
Proof. exact (EQ_MP (@lem1962654 n) (@lem1962653 n)). Qed.
Lemma lem1962681 (n : nat) (q' : Prop) : term41 n q'.
Proof. exact (@lem1962672 n (term30 n) q'). Qed.
Lemma lem1962682 (n : nat) (q' : Prop) : term42 n q'.
Proof. exact (@lem1962681 n q' (@lem1962674 n)). Qed.
Lemma lem1962688 (n : nat) : ((term35 n) = (term36 n)) = ((term35 n) = (term36 n)).
Proof. exact (eq_refl ((term35 n) = (term36 n))). Qed.
Lemma lem1962689 (n : nat) : term43 n.
Proof. exact (fun h0 : term30 n => @lem1962688 n). Qed.
Lemma lem1962690 (n : nat) : term44 n.
Proof. exact (@lem1962682 n ((term35 n) = (term36 n))). Qed.
Lemma lem1962691 (n : nat) : (term45 n) = (term46 n).
Proof. exact (@lem1962690 n (@lem1962689 n)). Qed.
Lemma lem1962693 {A : Type'} (P : A -> Prop) (Q : Prop) : (term27 A P Q) = (term28 A P Q).
Proof. exact (EQ_MP (@lem1962651 A P Q) (@lem1962650 A P Q)). Qed.
Lemma lem1962694 (P : nat -> Prop) (Q : Prop) : (term47 P Q) = (term48 P Q).
Proof. exact (@lem1962693 nat P Q). Qed.
Lemma lem1962695 (n : nat) : (term49 n) = (term50 n).
Proof. exact (@lem1962694 (term51 n) ((term35 n) = (term36 n))). Qed.
Lemma lem1962696 (n : nat) (m : nat) : (term52 n m) = (n = (term53 m)).
Proof. exact (eq_refl (term52 n m)). Qed.
Lemma lem1962697 (n : nat) : (term54 n) = (term51 n).
Proof. exact (fun_ext (fun m : nat => @lem1962696 n m)). Qed.
Lemma lem1962698 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1962699 (n : nat) : (term55 n) = (term30 n).
Proof. exact (MK_COMB (@lem1962698) (@lem1962697 n)). Qed.
Lemma lem1962700 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1962701 (n : nat) : (term56 n) = (term57 n).
Proof. exact (MK_COMB (@lem1962700) (@lem1962699 n)). Qed.
Lemma lem1962702 (n : nat) : ((term35 n) = (term36 n)) = ((term35 n) = (term36 n)).
Proof. exact (eq_refl ((term35 n) = (term36 n))). Qed.
Lemma lem1962703 (n : nat) : (term49 n) = (term46 n).
Proof. exact (MK_COMB (@lem1962701 n) (@lem1962702 n)). Qed.
Lemma lem1962704 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1962705 (n : nat) : (term58 n) = (term59 n).
Proof. exact (MK_COMB (@lem1962704) (@lem1962703 n)). Qed.
Lemma lem1962706 (n : nat) (m : nat) : (term52 n m) = (n = (term53 m)).
Proof. exact (eq_refl (term52 n m)). Qed.
Lemma lem1962707 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1962708 (n : nat) (m : nat) : (term60 n m) = (term61 n m).
Proof. exact (MK_COMB (@lem1962707) (@lem1962706 n m)). Qed.
Lemma lem1962709 (n : nat) : ((term35 n) = (term36 n)) = ((term35 n) = (term36 n)).
Proof. exact (eq_refl ((term35 n) = (term36 n))). Qed.
Lemma lem1962710 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (MK_COMB (@lem1962708 n m) (@lem1962709 n)). Qed.
Lemma lem1962711 (n : nat) : (term64 n) = (term65 n).
Proof. exact (fun_ext (fun m : nat => @lem1962710 m n)). Qed.
Lemma lem1962712 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1962713 (n : nat) : (term50 n) = (term66 n).
Proof. exact (MK_COMB (@lem1962712) (@lem1962711 n)). Qed.
Lemma lem1962714 (n : nat) : ((term49 n) = (term50 n)) = ((term46 n) = (term66 n)).
Proof. exact (MK_COMB (@lem1962705 n) (@lem1962713 n)). Qed.
Lemma lem1962715 (n : nat) : (term46 n) = (term66 n).
Proof. exact (EQ_MP (@lem1962714 n) (@lem1962695 n)). Qed.
Lemma lem1962725 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term31 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1962726 (p : Prop) (q : Prop) (p' : Prop) : term32 p q p'.
Proof. exact (fun q' : Prop => @lem1962725 p q p' q'). Qed.
Lemma lem1962727 (p : Prop) (q : Prop) : term33 p q.
Proof. exact (fun p' : Prop => @lem1962726 p q p'). Qed.
Lemma lem1962728 (m : nat) (n : nat) : term67 m n.
Proof. exact (@lem1962727 (n = (term53 m)) ((term35 n) = (term36 n))). Qed.
Lemma lem1962729 (m : nat) (n : nat) (p' : Prop) : term68 m n p'.
Proof. exact (@lem1962728 m n p'). Qed.
Lemma lem1962730 (m : nat) (n : nat) (p' : Prop) : (term68 m n p') = (term69 m n p').
Proof. exact (eq_refl (term68 m n p')). Qed.
Lemma lem1962731 (m : nat) (n : nat) (p' : Prop) : term69 m n p'.
Proof. exact (EQ_MP (@lem1962730 m n p') (@lem1962729 m n p')). Qed.
Lemma lem1962732 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term70 m n p' q'.
Proof. exact (@lem1962731 m n p' q'). Qed.
Lemma lem1962733 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term70 m n p' q') = (term71 m n p' q').
Proof. exact (eq_refl (term70 m n p' q')). Qed.
Lemma lem1962734 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term71 m n p' q'.
Proof. exact (EQ_MP (@lem1962733 m n p' q') (@lem1962732 m n p' q')). Qed.
Lemma lem1962737 (n : nat) (m : nat) : (n = (term53 m)) = (n = (term53 m)).
Proof. exact (eq_refl (n = (term53 m))). Qed.
Lemma lem1962738 (n : nat) (m : nat) (q' : Prop) : term72 n m q'.
Proof. exact (@lem1962734 m n (n = (term53 m)) q'). Qed.
Lemma lem1962739 (n : nat) (m : nat) (q' : Prop) : term73 n m q'.
Proof. exact (@lem1962738 n m q' (@lem1962737 n m)). Qed.
Lemma lem1962744 (n : nat) (m : nat) (h1 : n = (term53 m)) : n = (term53 m).
Proof. exact (h1). Qed.
Lemma lem1962745 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem1962746 (n : nat) (m : nat) (h1 : n = (term53 m)) : (term75 n) = (term76 m).
Proof. exact (MK_COMB (@lem1962745) (@lem1962744 n m h1)). Qed.
Lemma lem1962747 : sqrt = sqrt.
Proof. exact (eq_refl sqrt). Qed.
Lemma lem1962748 (n : nat) (m : nat) (h1 : n = (term53 m)) : (term35 n) = (term77 m).
Proof. exact (MK_COMB (@lem1962747) (@lem1962746 n m h1)). Qed.
Lemma lem1962749 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1962750 (n : nat) (m : nat) (h1 : n = (term53 m)) : (term78 n) = (term79 m).
Proof. exact (MK_COMB (@lem1962749) (@lem1962748 n m h1)). Qed.
Lemma lem1962752 (n : nat) (m : nat) (h1 : n = (term53 m)) : n = (term53 m).
Proof. exact (h1). Qed.
Lemma lem1962753 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem1962754 (n : nat) (m : nat) (h1 : n = (term53 m)) : (Nat.div n) = (term80 m).
Proof. exact (MK_COMB (@lem1962753) (@lem1962752 n m h1)). Qed.
Lemma lem1962755 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem1962756 (n : nat) (m : nat) (h1 : n = (term53 m)) : (term82 n) = (term83 m).
Proof. exact (MK_COMB (@lem1962754 n m h1) (@lem1962755)). Qed.
Lemma lem1962758 (m : nat) (n : nat) : term21 m n.
Proof. exact (fun h0 : term22 m => @lem1962641 n m h0). Qed.
Lemma lem1962759 (m : nat) : term84 m.
Proof. exact (@lem1962758 term81 m). Qed.
Lemma lem1962761 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1962632 m n) (@lem1962631 m n)). Qed.
Lemma lem1962762 : (term81 = (NUMERAL 0)) = (term85 = 0).
Proof. exact (@lem1962761 term85 0). Qed.
Lemma lem1962764 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem1962624 n) (@lem1962623 n)). Qed.
Lemma lem1962765 : (term85 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem1962764 (BIT1 0)). Qed.
Lemma lem1962767 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem1962620 n) (@lem1962619 n)). Qed.
Lemma lem1962768 : ((BIT1 0) = 0) = False.
Proof. exact (@lem1962767 0). Qed.
Lemma lem1962769 : (term85 = 0) = False.
Proof. exact (TRANS (@lem1962765) (@lem1962768)). Qed.
Lemma lem1962770 : (term81 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1962762) (@lem1962769)). Qed.
Lemma lem1962771 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1962772 : term86 = (~ False).
Proof. exact (MK_COMB (@lem1962771) (@lem1962770)). Qed.
Lemma lem1962774 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1962775 : term86 = True.
Proof. exact (TRANS (@lem1962772) (@lem1962774)). Qed.
Lemma lem1962776 : True = term86.
Proof. exact (SYM (@lem1962775)). Qed.
Lemma lem1962777 : term86.
Proof. exact (EQ_MP (@lem1962776) (@lem0)). Qed.
Lemma lem1962778 (m : nat) : (term83 m) = m.
Proof. exact (@lem1962759 m (@lem1962777)). Qed.
Lemma lem1962779 (n : nat) (m : nat) (h1 : n = (term53 m)) : (term82 n) = m.
Proof. exact (TRANS (@lem1962756 n m h1) (@lem1962778 m)). Qed.
Lemma lem1962780 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem1962781 (n : nat) (m : nat) (h1 : n = (term53 m)) : (term36 n) = (term75 m).
Proof. exact (MK_COMB (@lem1962780) (@lem1962779 n m h1)). Qed.
Lemma lem1962782 (n : nat) (m : nat) (h1 : n = (term53 m)) : ((term35 n) = (term36 n)) = ((term77 m) = (term75 m)).
Proof. exact (MK_COMB (@lem1962750 n m h1) (@lem1962781 n m h1)). Qed.
Lemma lem1962785 (n : nat) (m : nat) : term87 n m.
Proof. exact (fun h0 : n = (term53 m) => @lem1962782 n m h0). Qed.
Lemma lem1962786 (n : nat) (m : nat) : term88 n m.
Proof. exact (@lem1962739 n m ((term77 m) = (term75 m))). Qed.
Lemma lem1962787 (n : nat) (m : nat) : (term63 m n) = (term89 n m).
Proof. exact (@lem1962786 n m (@lem1962785 n m)). Qed.
Lemma lem1962819 (n : nat) : (term65 n) = (term90 n).
Proof. exact (fun_ext (fun m : nat => @lem1962787 n m)). Qed.
Lemma lem1962851 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1962852 (n : nat) : (term66 n) = (term91 n).
Proof. exact (MK_COMB (@lem1962851) (@lem1962819 n)). Qed.
Lemma lem1962888 (n : nat) : (term46 n) = (term91 n).
Proof. exact (TRANS (@lem1962715 n) (@lem1962852 n)). Qed.
Lemma lem1962889 (n : nat) : (term45 n) = (term91 n).
Proof. exact (TRANS (@lem1962691 n) (@lem1962888 n)). Qed.
Lemma lem1962890 : term92 = term93.
Proof. exact (fun_ext (fun n : nat => @lem1962889 n)). Qed.
Lemma lem1962926 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1962927 : term94 = term95.
Proof. exact (MK_COMB (@lem1962926) (@lem1962890)). Qed.
Lemma lem1962967 : term95 = term94.
Proof. exact (SYM (@lem1962927)). Qed.
Lemma lem1962969 (p : Prop) : p = (term96 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1962970 : term95 = term97.
Proof. exact (@lem1962969 term95). Qed.
Lemma lem1962971 : term97 = term95.
Proof. exact (SYM (@lem1962970)). Qed.
Lemma lem1962972 (h1 : term98) : term98.
Proof. exact (h1). Qed.
Lemma lem1962975 (h1 : term99) : term99.
Proof. exact (h1). Qed.
Lemma lem1962976 : term100.
Proof. exact (fun h0 : term99 => @lem1962975 h0). Qed.
Lemma lem1962977 (h1 : term100) : term100.
Proof. exact (h1). Qed.
Lemma lem1962978 (h1 : term99) : term99.
Proof. exact (h1). Qed.
Lemma lem1962979 (h1 : term99) (h2 : term100) : term99.
Proof. exact (@lem1962977 h2 (@lem1962978 h1)). Qed.
Lemma lem1962980 (h1 : term99) : term101.
Proof. exact (fun h0 : term100 => @lem1962979 h1 h0). Qed.
Lemma lem1962981 (h1 : term100) : term100.
Proof. exact (h1). Qed.
Lemma lem1962982 (h1 : term99) (h2 : term100) : term99.
Proof. exact (@lem1962980 h1 (@lem1962981 h2)). Qed.
Lemma lem1962983 (h1 : term100) : term100.
Proof. exact (fun h0 : term99 => @lem1962982 h0 h1). Qed.
Lemma lem1962984 : term102.
Proof. exact (fun h0 : term100 => @lem1962983 h0). Qed.
Lemma lem1962987 : term100.
Proof. exact (@lem1962984 (@lem1962976)). Qed.
Lemma lem1963043 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1963044 : term103 = term104.
Proof. exact (@lem1963043 term105). Qed.
Lemma lem1963057 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem1963058 : term107 = term108.
Proof. exact (MK_COMB (@lem1963057) (@lem1963044)). Qed.
Lemma lem1963061 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem1963062 : term110 = term111.
Proof. exact (MK_COMB (@lem1963061) (@lem1963058)). Qed.
Lemma lem1963065 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem1963066 : term113 = term114.
Proof. exact (MK_COMB (@lem1963065) (@lem1963062)). Qed.
Lemma lem1963069 : term115 = term115.
Proof. exact (eq_refl term115). Qed.
Lemma lem1963070 : term116 = term117.
Proof. exact (MK_COMB (@lem1963069) (@lem1963066)). Qed.
Lemma lem1963073 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem1963080 : term99 = term119.
Proof. exact (MK_COMB (@lem1963073) (@lem1963070)). Qed.
Lemma lem1963089 (x : real) (y : real) : (term120 x y) = (term120 x y).
Proof. exact (eq_refl (term120 x y)). Qed.
Lemma lem1963090 (x : real) : (term121 x) = (term121 x).
Proof. exact (fun_ext (fun y : real => @lem1963089 x y)). Qed.
Lemma lem1963091 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963092 (x : real) : (term122 x) = (term122 x).
Proof. exact (MK_COMB (@lem1963091) (@lem1963090 x)). Qed.
Lemma lem1963093 : term123 = term123.
Proof. exact (fun_ext (fun x : real => @lem1963092 x)). Qed.
Lemma lem1963094 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963095 : term105 = term105.
Proof. exact (MK_COMB (@lem1963094) (@lem1963093)). Qed.
Lemma lem1963096 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1963097 : term104 = term104.
Proof. exact (MK_COMB (@lem1963096) (@lem1963095)). Qed.
Lemma lem1963098 (x : real) (m : nat) (n : nat) : ((term124 x m n) = (term125 x m n)) = ((term124 x m n) = (term125 x m n)).
Proof. exact (eq_refl ((term124 x m n) = (term125 x m n))). Qed.
Lemma lem1963099 (x : real) (m : nat) : (term126 x m) = (term126 x m).
Proof. exact (fun_ext (fun n : nat => @lem1963098 x m n)). Qed.
Lemma lem1963100 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963101 (x : real) (m : nat) : (term127 x m) = (term127 x m).
Proof. exact (MK_COMB (@lem1963100) (@lem1963099 x m)). Qed.
Lemma lem1963102 (x : real) : (term128 x) = (term128 x).
Proof. exact (fun_ext (fun m : nat => @lem1963101 x m)). Qed.
Lemma lem1963103 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963104 (x : real) : (term129 x) = (term129 x).
Proof. exact (MK_COMB (@lem1963103) (@lem1963102 x)). Qed.
Lemma lem1963105 : term130 = term130.
Proof. exact (fun_ext (fun x : real => @lem1963104 x)). Qed.
Lemma lem1963106 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963107 : term131 = term131.
Proof. exact (MK_COMB (@lem1963106) (@lem1963105)). Qed.
Lemma lem1963108 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1963109 : term106 = term106.
Proof. exact (MK_COMB (@lem1963108) (@lem1963107)). Qed.
Lemma lem1963110 : term108 = term108.
Proof. exact (MK_COMB (@lem1963109) (@lem1963097)). Qed.
Lemma lem1963111 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem1963112 (m : nat) : (term132 m) = (term132 m).
Proof. exact (fun_ext (fun n : nat => @lem1963111 n m)). Qed.
Lemma lem1963113 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963114 (m : nat) : (term133 m) = (term133 m).
Proof. exact (MK_COMB (@lem1963113) (@lem1963112 m)). Qed.
Lemma lem1963115 : term134 = term134.
Proof. exact (fun_ext (fun m : nat => @lem1963114 m)). Qed.
Lemma lem1963116 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963117 : term135 = term135.
Proof. exact (MK_COMB (@lem1963116) (@lem1963115)). Qed.
Lemma lem1963118 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1963119 : term109 = term109.
Proof. exact (MK_COMB (@lem1963118) (@lem1963117)). Qed.
Lemma lem1963120 : term111 = term111.
Proof. exact (MK_COMB (@lem1963119) (@lem1963110)). Qed.
Lemma lem1963125 (x : real) (n : nat) : (term136 x n) = (term136 x n).
Proof. exact (eq_refl (term136 x n)). Qed.
Lemma lem1963126 (x : real) : (term137 x) = (term137 x).
Proof. exact (fun_ext (fun n : nat => @lem1963125 x n)). Qed.
Lemma lem1963127 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963128 (x : real) : (term138 x) = (term138 x).
Proof. exact (MK_COMB (@lem1963127) (@lem1963126 x)). Qed.
Lemma lem1963129 : term139 = term139.
Proof. exact (fun_ext (fun x : real => @lem1963128 x)). Qed.
Lemma lem1963130 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963131 : term140 = term140.
Proof. exact (MK_COMB (@lem1963130) (@lem1963129)). Qed.
Lemma lem1963132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1963133 : term112 = term112.
Proof. exact (MK_COMB (@lem1963132) (@lem1963131)). Qed.
Lemma lem1963134 : term114 = term114.
Proof. exact (MK_COMB (@lem1963133) (@lem1963120)). Qed.
Lemma lem1963135 (n : nat) : (term141 n) = (term141 n).
Proof. exact (eq_refl (term141 n)). Qed.
Lemma lem1963136 : term142 = term142.
Proof. exact (fun_ext (fun n : nat => @lem1963135 n)). Qed.
Lemma lem1963137 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963138 : term143 = term143.
Proof. exact (MK_COMB (@lem1963137) (@lem1963136)). Qed.
Lemma lem1963139 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1963140 : term115 = term115.
Proof. exact (MK_COMB (@lem1963139) (@lem1963138)). Qed.
Lemma lem1963141 : term117 = term117.
Proof. exact (MK_COMB (@lem1963140) (@lem1963134)). Qed.
Lemma lem1963146 (n : nat) (m : nat) : (term89 n m) = (term89 n m).
Proof. exact (eq_refl (term89 n m)). Qed.
Lemma lem1963147 (n : nat) : (term90 n) = (term90 n).
Proof. exact (fun_ext (fun m : nat => @lem1963146 n m)). Qed.
Lemma lem1963148 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963149 (n : nat) : (term91 n) = (term91 n).
Proof. exact (MK_COMB (@lem1963148) (@lem1963147 n)). Qed.
Lemma lem1963150 : term93 = term93.
Proof. exact (fun_ext (fun n : nat => @lem1963149 n)). Qed.
Lemma lem1963151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963152 : term95 = term95.
Proof. exact (MK_COMB (@lem1963151) (@lem1963150)). Qed.
Lemma lem1963153 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1963154 : term98 = term98.
Proof. exact (MK_COMB (@lem1963153) (@lem1963152)). Qed.
Lemma lem1963155 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1963156 : term118 = term118.
Proof. exact (MK_COMB (@lem1963155) (@lem1963154)). Qed.
Lemma lem1963157 : term119 = term119.
Proof. exact (MK_COMB (@lem1963156) (@lem1963141)). Qed.
Lemma lem1963250 : term99 = term119.
Proof. exact (TRANS (@lem1963080) (@lem1963157)). Qed.
Lemma lem1963251 : term119 = term99.
Proof. exact (SYM (@lem1963250)). Qed.
Lemma lem1963252 (h1 : term98) : term98.
Proof. exact (h1). Qed.
Lemma lem1963253 (h1 : term143) : term143.
Proof. exact (h1). Qed.
Lemma lem1963254 (h1 : term140) : term140.
Proof. exact (h1). Qed.
Lemma lem1963255 (h1 : term135) : term135.
Proof. exact (h1). Qed.
Lemma lem1963256 (h1 : term131) : term131.
Proof. exact (h1). Qed.
Lemma lem1963257 (h1 : term105) : term105.
Proof. exact (h1). Qed.
Lemma lem1963264 (n : nat) (m : nat) : (term144 n m) = (term145 n m).
Proof. exact (@lem17362 (n = (term53 m)) ((term77 m) = (term75 m))). Qed.
Lemma lem1963265 (P : nat -> Prop) : (term146 P) = (term147 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1963266 (n : nat) : (term148 n) = (term149 n).
Proof. exact (@lem1963265 (term90 n)). Qed.
Lemma lem1963267 (n : nat) (m : nat) : (term150 n m) = (term89 n m).
Proof. exact (eq_refl (term150 n m)). Qed.
Lemma lem1963268 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1963269 (n : nat) (m : nat) : (term151 n m) = (term144 n m).
Proof. exact (MK_COMB (@lem1963268) (@lem1963267 n m)). Qed.
Lemma lem1963270 (n : nat) (m : nat) : (term151 n m) = (term145 n m).
Proof. exact (TRANS (@lem1963269 n m) (@lem1963264 n m)). Qed.
Lemma lem1963271 (n : nat) : (term152 n) = (term153 n).
Proof. exact (fun_ext (fun m : nat => @lem1963270 n m)). Qed.
Lemma lem1963272 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1963273 (n : nat) : (term149 n) = (term154 n).
Proof. exact (MK_COMB (@lem1963272) (@lem1963271 n)). Qed.
Lemma lem1963274 (n : nat) : (term148 n) = (term154 n).
Proof. exact (TRANS (@lem1963266 n) (@lem1963273 n)). Qed.
Lemma lem1963275 (P : nat -> Prop) : (term146 P) = (term147 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1963276 : term98 = term155.
Proof. exact (@lem1963275 term93). Qed.
Lemma lem1963277 (n : nat) : (term156 n) = (term91 n).
Proof. exact (eq_refl (term156 n)). Qed.
Lemma lem1963278 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1963279 (n : nat) : (term157 n) = (term148 n).
Proof. exact (MK_COMB (@lem1963278) (@lem1963277 n)). Qed.
Lemma lem1963280 (n : nat) : (term157 n) = (term154 n).
Proof. exact (TRANS (@lem1963279 n) (@lem1963274 n)). Qed.
Lemma lem1963281 : term158 = term159.
Proof. exact (fun_ext (fun n : nat => @lem1963280 n)). Qed.
Lemma lem1963282 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1963283 : term155 = term160.
Proof. exact (MK_COMB (@lem1963282) (@lem1963281)). Qed.
Lemma lem1963340 : term98 = term160.
Proof. exact (TRANS (@lem1963276) (@lem1963283)). Qed.
Lemma lem1963341 (h1 : term98) : term160.
Proof. exact (EQ_MP (@lem1963340) (@lem1963252 h1)). Qed.
Lemma lem1963342 (n : nat) : (term141 n) = (term141 n).
Proof. exact (eq_refl (term141 n)). Qed.
Lemma lem1963343 : term142 = term142.
Proof. exact (fun_ext (fun n : nat => @lem1963342 n)). Qed.
Lemma lem1963344 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963353 : term143 = term143.
Proof. exact (MK_COMB (@lem1963344) (@lem1963343)). Qed.
Lemma lem1963354 (h1 : term143) : term143.
Proof. exact (EQ_MP (@lem1963353) (@lem1963253 h1)). Qed.
Lemma lem1963361 (x : real) (n : nat) : (term136 x n) = (term161 x n).
Proof. exact (@lem17265 (term162 x) (term163 x n)). Qed.
Lemma lem1963362 (x : real) : (term137 x) = (term164 x).
Proof. exact (fun_ext (fun n : nat => @lem1963361 x n)). Qed.
Lemma lem1963363 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963364 (x : real) : (term138 x) = (term165 x).
Proof. exact (MK_COMB (@lem1963363) (@lem1963362 x)). Qed.
Lemma lem1963365 : term139 = term166.
Proof. exact (fun_ext (fun x : real => @lem1963364 x)). Qed.
Lemma lem1963366 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963367 : term140 = term167.
Proof. exact (MK_COMB (@lem1963366) (@lem1963365)). Qed.
Lemma lem1963373 {A : Type'} (P : Prop) (Q : A -> Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem1963374 (P : Prop) (Q : nat -> Prop) : (term170 P Q) = (term171 P Q).
Proof. exact (@lem1963373 nat P Q). Qed.
Lemma lem1963375 (x : real) : (term172 x) = (term173 x).
Proof. exact (@lem1963374 (term174 x) (term175 x)). Qed.
Lemma lem1963376 (x : real) (n : nat) : (term176 x n) = (term163 x n).
Proof. exact (eq_refl (term176 x n)). Qed.
Lemma lem1963377 (x : real) : (term177 x) = (term177 x).
Proof. exact (eq_refl (term177 x)). Qed.
Lemma lem1963378 (x : real) (n : nat) : (term178 x n) = (term161 x n).
Proof. exact (MK_COMB (@lem1963377 x) (@lem1963376 x n)). Qed.
Lemma lem1963379 (x : real) : (term179 x) = (term164 x).
Proof. exact (fun_ext (fun n : nat => @lem1963378 x n)). Qed.
Lemma lem1963380 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963381 (x : real) : (term172 x) = (term165 x).
Proof. exact (MK_COMB (@lem1963380) (@lem1963379 x)). Qed.
Lemma lem1963382 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1963383 (x : real) : (term180 x) = (term181 x).
Proof. exact (MK_COMB (@lem1963382) (@lem1963381 x)). Qed.
Lemma lem1963384 (x : real) (n : nat) : (term176 x n) = (term163 x n).
Proof. exact (eq_refl (term176 x n)). Qed.
Lemma lem1963385 (x : real) : (term182 x) = (term175 x).
Proof. exact (fun_ext (fun n : nat => @lem1963384 x n)). Qed.
Lemma lem1963386 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963387 (x : real) : (term183 x) = (term184 x).
Proof. exact (MK_COMB (@lem1963386) (@lem1963385 x)). Qed.
Lemma lem1963388 (x : real) : (term177 x) = (term177 x).
Proof. exact (eq_refl (term177 x)). Qed.
Lemma lem1963389 (x : real) : (term173 x) = (term185 x).
Proof. exact (MK_COMB (@lem1963388 x) (@lem1963387 x)). Qed.
Lemma lem1963390 (x : real) : ((term172 x) = (term173 x)) = ((term165 x) = (term185 x)).
Proof. exact (MK_COMB (@lem1963383 x) (@lem1963389 x)). Qed.
Lemma lem1963391 (x : real) : (term165 x) = (term185 x).
Proof. exact (EQ_MP (@lem1963390 x) (@lem1963375 x)). Qed.
Lemma lem1963396 : term166 = term186.
Proof. exact (fun_ext (fun x : real => @lem1963391 x)). Qed.
Lemma lem1963397 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963448 : term167 = term187.
Proof. exact (MK_COMB (@lem1963397) (@lem1963396)). Qed.
Lemma lem1963449 : term140 = term187.
Proof. exact (TRANS (@lem1963367) (@lem1963448)). Qed.
Lemma lem1963450 (h1 : term140) : term187.
Proof. exact (EQ_MP (@lem1963449) (@lem1963254 h1)). Qed.
Lemma lem1963451 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem1963452 (m : nat) : (term132 m) = (term132 m).
Proof. exact (fun_ext (fun n : nat => @lem1963451 n m)). Qed.
Lemma lem1963453 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963454 (m : nat) : (term133 m) = (term133 m).
Proof. exact (MK_COMB (@lem1963453) (@lem1963452 m)). Qed.
Lemma lem1963455 : term134 = term134.
Proof. exact (fun_ext (fun m : nat => @lem1963454 m)). Qed.
Lemma lem1963456 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963469 : term135 = term135.
Proof. exact (MK_COMB (@lem1963456) (@lem1963455)). Qed.
Lemma lem1963470 (h1 : term135) : term135.
Proof. exact (EQ_MP (@lem1963469) (@lem1963255 h1)). Qed.
Lemma lem1963471 (x : real) (m : nat) (n : nat) : ((term124 x m n) = (term125 x m n)) = ((term124 x m n) = (term125 x m n)).
Proof. exact (eq_refl ((term124 x m n) = (term125 x m n))). Qed.
Lemma lem1963472 (x : real) (m : nat) : (term126 x m) = (term126 x m).
Proof. exact (fun_ext (fun n : nat => @lem1963471 x m n)). Qed.
Lemma lem1963473 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963474 (x : real) (m : nat) : (term127 x m) = (term127 x m).
Proof. exact (MK_COMB (@lem1963473) (@lem1963472 x m)). Qed.
Lemma lem1963475 (x : real) : (term128 x) = (term128 x).
Proof. exact (fun_ext (fun m : nat => @lem1963474 x m)). Qed.
Lemma lem1963476 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963477 (x : real) : (term129 x) = (term129 x).
Proof. exact (MK_COMB (@lem1963476) (@lem1963475 x)). Qed.
Lemma lem1963478 : term130 = term130.
Proof. exact (fun_ext (fun x : real => @lem1963477 x)). Qed.
Lemma lem1963479 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963496 : term131 = term131.
Proof. exact (MK_COMB (@lem1963479) (@lem1963478)). Qed.
Lemma lem1963497 (h1 : term131) : term131.
Proof. exact (EQ_MP (@lem1963496) (@lem1963256 h1)). Qed.
Lemma lem1963504 (y : real) (x : real) : (term188 y x) = (term189 y x).
Proof. exact (@lem17045 (term162 y) ((term190 y) = x)). Qed.
Lemma lem1963505 (x : real) (y : real) : ((sqrt x) = y) = ((sqrt x) = y).
Proof. exact (eq_refl ((sqrt x) = y)). Qed.
Lemma lem1963506 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1963507 (y : real) (x : real) : (term191 y x) = (term192 y x).
Proof. exact (MK_COMB (@lem1963506) (@lem1963504 y x)). Qed.
Lemma lem1963508 (x : real) (y : real) : (term193 x y) = (term194 x y).
Proof. exact (MK_COMB (@lem1963507 y x) (@lem1963505 x y)). Qed.
Lemma lem1963509 (x : real) (y : real) : (term120 x y) = (term193 x y).
Proof. exact (@lem17265 (term195 y x) ((sqrt x) = y)). Qed.
Lemma lem1963510 (x : real) (y : real) : (term120 x y) = (term194 x y).
Proof. exact (TRANS (@lem1963509 x y) (@lem1963508 x y)). Qed.
Lemma lem1963511 (x : real) : (term121 x) = (term196 x).
Proof. exact (fun_ext (fun y : real => @lem1963510 x y)). Qed.
Lemma lem1963512 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963513 (x : real) : (term122 x) = (term197 x).
Proof. exact (MK_COMB (@lem1963512) (@lem1963511 x)). Qed.
Lemma lem1963514 : term123 = term198.
Proof. exact (fun_ext (fun x : real => @lem1963513 x)). Qed.
Lemma lem1963515 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963572 : term105 = term199.
Proof. exact (MK_COMB (@lem1963515) (@lem1963514)). Qed.
Lemma lem1963573 (h1 : term105) : term199.
Proof. exact (EQ_MP (@lem1963572) (@lem1963257 h1)). Qed.
Lemma lem1963574 (n : nat) (h1 : term154 n) : term154 n.
Proof. exact (h1). Qed.
Lemma lem1963586 (n : nat) : (term141 n) = (term141 n).
Proof. exact (eq_refl (term141 n)). Qed.
Lemma lem1963587 : term142 = term142.
Proof. exact (fun_ext (fun n : nat => @lem1963586 n)). Qed.
Lemma lem1963588 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963589 : term143 = term143.
Proof. exact (MK_COMB (@lem1963588) (@lem1963587)). Qed.
Lemma lem1963590 (h1 : term143) : term143.
Proof. exact (EQ_MP (@lem1963589) (@lem1963354 h1)). Qed.
Lemma lem1963603 (x : real) (n : nat) : (term163 x n) = (term163 x n).
Proof. exact (eq_refl (term163 x n)). Qed.
Lemma lem1963604 (x : real) : (term175 x) = (term175 x).
Proof. exact (fun_ext (fun n : nat => @lem1963603 x n)). Qed.
Lemma lem1963605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963606 (x : real) : (term184 x) = (term184 x).
Proof. exact (MK_COMB (@lem1963605) (@lem1963604 x)). Qed.
Lemma lem1963619 (x : real) : (term177 x) = (term177 x).
Proof. exact (eq_refl (term177 x)). Qed.
Lemma lem1963620 (x : real) : (term185 x) = (term185 x).
Proof. exact (MK_COMB (@lem1963619 x) (@lem1963606 x)). Qed.
Lemma lem1963621 : term186 = term186.
Proof. exact (fun_ext (fun x : real => @lem1963620 x)). Qed.
Lemma lem1963622 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963623 : term187 = term187.
Proof. exact (MK_COMB (@lem1963622) (@lem1963621)). Qed.
Lemma lem1963624 (h1 : term140) : term187.
Proof. exact (EQ_MP (@lem1963623) (@lem1963450 h1)). Qed.
Lemma lem1963637 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem1963638 (m : nat) : (term132 m) = (term132 m).
Proof. exact (fun_ext (fun n : nat => @lem1963637 n m)). Qed.
Lemma lem1963639 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963640 (m : nat) : (term133 m) = (term133 m).
Proof. exact (MK_COMB (@lem1963639) (@lem1963638 m)). Qed.
Lemma lem1963641 : term134 = term134.
Proof. exact (fun_ext (fun m : nat => @lem1963640 m)). Qed.
Lemma lem1963642 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963643 : term135 = term135.
Proof. exact (MK_COMB (@lem1963642) (@lem1963641)). Qed.
Lemma lem1963644 (h1 : term135) : term135.
Proof. exact (EQ_MP (@lem1963643) (@lem1963470 h1)). Qed.
Lemma lem1963665 (x : real) (m : nat) (n : nat) : ((term124 x m n) = (term125 x m n)) = ((term124 x m n) = (term125 x m n)).
Proof. exact (eq_refl ((term124 x m n) = (term125 x m n))). Qed.
Lemma lem1963666 (x : real) (m : nat) : (term126 x m) = (term126 x m).
Proof. exact (fun_ext (fun n : nat => @lem1963665 x m n)). Qed.
Lemma lem1963667 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963668 (x : real) (m : nat) : (term127 x m) = (term127 x m).
Proof. exact (MK_COMB (@lem1963667) (@lem1963666 x m)). Qed.
Lemma lem1963669 (x : real) : (term128 x) = (term128 x).
Proof. exact (fun_ext (fun m : nat => @lem1963668 x m)). Qed.
Lemma lem1963670 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963671 (x : real) : (term129 x) = (term129 x).
Proof. exact (MK_COMB (@lem1963670) (@lem1963669 x)). Qed.
Lemma lem1963672 : term130 = term130.
Proof. exact (fun_ext (fun x : real => @lem1963671 x)). Qed.
Lemma lem1963673 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963674 : term131 = term131.
Proof. exact (MK_COMB (@lem1963673) (@lem1963672)). Qed.
Lemma lem1963675 (h1 : term131) : term131.
Proof. exact (EQ_MP (@lem1963674) (@lem1963497 h1)). Qed.
Lemma lem1963716 (x : real) (y : real) : (term194 x y) = (term194 x y).
Proof. exact (eq_refl (term194 x y)). Qed.
Lemma lem1963717 (x : real) : (term196 x) = (term196 x).
Proof. exact (fun_ext (fun y : real => @lem1963716 x y)). Qed.
Lemma lem1963718 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963719 (x : real) : (term197 x) = (term197 x).
Proof. exact (MK_COMB (@lem1963718) (@lem1963717 x)). Qed.
Lemma lem1963720 : term198 = term198.
Proof. exact (fun_ext (fun x : real => @lem1963719 x)). Qed.
Lemma lem1963721 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963722 : term199 = term199.
Proof. exact (MK_COMB (@lem1963721) (@lem1963720)). Qed.
Lemma lem1963723 (h1 : term105) : term199.
Proof. exact (EQ_MP (@lem1963722) (@lem1963573 h1)). Qed.
Lemma lem1963785 (n : nat) (m : nat) (h1 : term145 n m) : term145 n m.
Proof. exact (h1). Qed.
Lemma lem1963789 (n : nat) : (term141 n) = (term141 n).
Proof. exact (eq_refl (term141 n)). Qed.
Lemma lem1963790 : term142 = term142.
Proof. exact (fun_ext (fun n : nat => @lem1963789 n)). Qed.
Lemma lem1963791 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963793 : term143 = term143.
Proof. exact (MK_COMB (@lem1963791) (@lem1963790)). Qed.
Lemma lem1963794 (h1 : term143) : term143.
Proof. exact (EQ_MP (@lem1963793) (@lem1963590 h1)). Qed.
Lemma lem1963796 {A : Type'} (P : Prop) (Q : A -> Prop) : (term169 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1963797 (P : Prop) (Q : nat -> Prop) : (term171 P Q) = (term170 P Q).
Proof. exact (@lem1963796 nat P Q). Qed.
Lemma lem1963798 (x : real) : (term173 x) = (term172 x).
Proof. exact (@lem1963797 (term174 x) (term175 x)). Qed.
Lemma lem1963799 (x : real) (n : nat) : (term176 x n) = (term163 x n).
Proof. exact (eq_refl (term176 x n)). Qed.
Lemma lem1963800 (x : real) : (term182 x) = (term175 x).
Proof. exact (fun_ext (fun n : nat => @lem1963799 x n)). Qed.
Lemma lem1963801 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963802 (x : real) : (term183 x) = (term184 x).
Proof. exact (MK_COMB (@lem1963801) (@lem1963800 x)). Qed.
Lemma lem1963803 (x : real) : (term177 x) = (term177 x).
Proof. exact (eq_refl (term177 x)). Qed.
Lemma lem1963804 (x : real) : (term173 x) = (term185 x).
Proof. exact (MK_COMB (@lem1963803 x) (@lem1963802 x)). Qed.
Lemma lem1963805 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1963806 (x : real) : (term200 x) = (term201 x).
Proof. exact (MK_COMB (@lem1963805) (@lem1963804 x)). Qed.
Lemma lem1963807 (x : real) (n : nat) : (term176 x n) = (term163 x n).
Proof. exact (eq_refl (term176 x n)). Qed.
Lemma lem1963808 (x : real) : (term177 x) = (term177 x).
Proof. exact (eq_refl (term177 x)). Qed.
Lemma lem1963809 (x : real) (n : nat) : (term178 x n) = (term161 x n).
Proof. exact (MK_COMB (@lem1963808 x) (@lem1963807 x n)). Qed.
Lemma lem1963810 (x : real) : (term179 x) = (term164 x).
Proof. exact (fun_ext (fun n : nat => @lem1963809 x n)). Qed.
Lemma lem1963811 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963812 (x : real) : (term172 x) = (term165 x).
Proof. exact (MK_COMB (@lem1963811) (@lem1963810 x)). Qed.
Lemma lem1963813 (x : real) : ((term173 x) = (term172 x)) = ((term185 x) = (term165 x)).
Proof. exact (MK_COMB (@lem1963806 x) (@lem1963812 x)). Qed.
Lemma lem1963814 (x : real) : (term185 x) = (term165 x).
Proof. exact (EQ_MP (@lem1963813 x) (@lem1963798 x)). Qed.
Lemma lem1963815 : term186 = term166.
Proof. exact (fun_ext (fun x : real => @lem1963814 x)). Qed.
Lemma lem1963816 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963817 : term187 = term167.
Proof. exact (MK_COMB (@lem1963816) (@lem1963815)). Qed.
Lemma lem1963824 (x : real) (n : nat) : (term161 x n) = (term161 x n).
Proof. exact (eq_refl (term161 x n)). Qed.
Lemma lem1963825 (x : real) : (term164 x) = (term164 x).
Proof. exact (fun_ext (fun n : nat => @lem1963824 x n)). Qed.
Lemma lem1963826 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963827 (x : real) : (term165 x) = (term165 x).
Proof. exact (MK_COMB (@lem1963826) (@lem1963825 x)). Qed.
Lemma lem1963828 : term166 = term166.
Proof. exact (fun_ext (fun x : real => @lem1963827 x)). Qed.
Lemma lem1963829 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963830 : term167 = term167.
Proof. exact (MK_COMB (@lem1963829) (@lem1963828)). Qed.
Lemma lem1963831 : term187 = term167.
Proof. exact (TRANS (@lem1963817) (@lem1963830)). Qed.
Lemma lem1963832 (h1 : term140) : term167.
Proof. exact (EQ_MP (@lem1963831) (@lem1963624 h1)). Qed.
Lemma lem1963834 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem1963835 (m : nat) : (term132 m) = (term132 m).
Proof. exact (fun_ext (fun n : nat => @lem1963834 n m)). Qed.
Lemma lem1963836 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963837 (m : nat) : (term133 m) = (term133 m).
Proof. exact (MK_COMB (@lem1963836) (@lem1963835 m)). Qed.
Lemma lem1963838 : term134 = term134.
Proof. exact (fun_ext (fun m : nat => @lem1963837 m)). Qed.
Lemma lem1963839 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963841 : term135 = term135.
Proof. exact (MK_COMB (@lem1963839) (@lem1963838)). Qed.
Lemma lem1963842 (h1 : term135) : term135.
Proof. exact (EQ_MP (@lem1963841) (@lem1963644 h1)). Qed.
Lemma lem1963844 (x : real) (m : nat) (n : nat) : ((term124 x m n) = (term125 x m n)) = ((term124 x m n) = (term125 x m n)).
Proof. exact (eq_refl ((term124 x m n) = (term125 x m n))). Qed.
Lemma lem1963845 (x : real) (m : nat) : (term126 x m) = (term126 x m).
Proof. exact (fun_ext (fun n : nat => @lem1963844 x m n)). Qed.
Lemma lem1963846 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963847 (x : real) (m : nat) : (term127 x m) = (term127 x m).
Proof. exact (MK_COMB (@lem1963846) (@lem1963845 x m)). Qed.
Lemma lem1963848 (x : real) : (term128 x) = (term128 x).
Proof. exact (fun_ext (fun m : nat => @lem1963847 x m)). Qed.
Lemma lem1963849 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1963850 (x : real) : (term129 x) = (term129 x).
Proof. exact (MK_COMB (@lem1963849) (@lem1963848 x)). Qed.
Lemma lem1963851 : term130 = term130.
Proof. exact (fun_ext (fun x : real => @lem1963850 x)). Qed.
Lemma lem1963852 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963854 : term131 = term131.
Proof. exact (MK_COMB (@lem1963852) (@lem1963851)). Qed.
Lemma lem1963855 (h1 : term131) : term131.
Proof. exact (EQ_MP (@lem1963854) (@lem1963675 h1)). Qed.
Lemma lem1963869 (x : real) (y : real) : (term194 x y) = (term194 x y).
Proof. exact (eq_refl (term194 x y)). Qed.
Lemma lem1963870 (x : real) : (term196 x) = (term196 x).
Proof. exact (fun_ext (fun y : real => @lem1963869 x y)). Qed.
Lemma lem1963871 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963872 (x : real) : (term197 x) = (term197 x).
Proof. exact (MK_COMB (@lem1963871) (@lem1963870 x)). Qed.
Lemma lem1963873 : term198 = term198.
Proof. exact (fun_ext (fun x : real => @lem1963872 x)). Qed.
Lemma lem1963874 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1963876 : term199 = term199.
Proof. exact (MK_COMB (@lem1963874) (@lem1963873)). Qed.
Lemma lem1963877 (h1 : term105) : term199.
Proof. exact (EQ_MP (@lem1963876) (@lem1963723 h1)). Qed.
Lemma lem1963886 (_27564 : nat) (h1 : term143) : term202 _27564.
Proof. exact (@lem1963794 h1 _27564). Qed.
Lemma lem1963887 (_27564 : nat) : (term202 _27564) = (term141 _27564).
Proof. exact (eq_refl (term202 _27564)). Qed.
Lemma lem1963889 (_27565 : real) (h1 : term140) : term203 _27565.
Proof. exact (@lem1963832 h1 _27565). Qed.
Lemma lem1963890 (_27565 : real) : (term203 _27565) = (term165 _27565).
Proof. exact (eq_refl (term203 _27565)). Qed.
Lemma lem1963891 (_27565 : real) (h1 : term140) : term165 _27565.
Proof. exact (EQ_MP (@lem1963890 _27565) (@lem1963889 _27565 h1)). Qed.
Lemma lem1963892 (_27565 : real) (_27566 : nat) (h1 : term140) : term204 _27565 _27566.
Proof. exact (@lem1963891 _27565 h1 _27566). Qed.
Lemma lem1963893 (_27565 : real) (_27566 : nat) : (term204 _27565 _27566) = (term161 _27565 _27566).
Proof. exact (eq_refl (term204 _27565 _27566)). Qed.
Lemma lem1963895 (_27567 : nat) (h1 : term135) : term205 _27567.
Proof. exact (@lem1963842 h1 _27567). Qed.
Lemma lem1963896 (_27567 : nat) : (term205 _27567) = (term133 _27567).
Proof. exact (eq_refl (term205 _27567)). Qed.
Lemma lem1963897 (_27567 : nat) (h1 : term135) : term133 _27567.
Proof. exact (EQ_MP (@lem1963896 _27567) (@lem1963895 _27567 h1)). Qed.
Lemma lem1963898 (_27567 : nat) (_27568 : nat) (h1 : term135) : term206 _27567 _27568.
Proof. exact (@lem1963897 _27567 h1 _27568). Qed.
Lemma lem1963899 (_27568 : nat) (_27567 : nat) : (term206 _27567 _27568) = ((Nat.mul _27567 _27568) = (Nat.mul _27568 _27567)).
Proof. exact (eq_refl (term206 _27567 _27568)). Qed.
Lemma lem1963901 (_27569 : real) (h1 : term131) : term207 _27569.
Proof. exact (@lem1963855 h1 _27569). Qed.
Lemma lem1963902 (_27569 : real) : (term207 _27569) = (term129 _27569).
Proof. exact (eq_refl (term207 _27569)). Qed.
Lemma lem1963903 (_27569 : real) (h1 : term131) : term129 _27569.
Proof. exact (EQ_MP (@lem1963902 _27569) (@lem1963901 _27569 h1)). Qed.
Lemma lem1963904 (_27569 : real) (_27570 : nat) (h1 : term131) : term208 _27569 _27570.
Proof. exact (@lem1963903 _27569 h1 _27570). Qed.
Lemma lem1963905 (_27569 : real) (_27570 : nat) : (term208 _27569 _27570) = (term127 _27569 _27570).
Proof. exact (eq_refl (term208 _27569 _27570)). Qed.
Lemma lem1963906 (_27569 : real) (_27570 : nat) (h1 : term131) : term127 _27569 _27570.
Proof. exact (EQ_MP (@lem1963905 _27569 _27570) (@lem1963904 _27569 _27570 h1)). Qed.
Lemma lem1963907 (_27569 : real) (_27570 : nat) (_27571 : nat) (h1 : term131) : term209 _27569 _27570 _27571.
Proof. exact (@lem1963906 _27569 _27570 h1 _27571). Qed.
Lemma lem1963908 (_27569 : real) (_27570 : nat) (_27571 : nat) : (term209 _27569 _27570 _27571) = ((term124 _27569 _27570 _27571) = (term125 _27569 _27570 _27571)).
Proof. exact (eq_refl (term209 _27569 _27570 _27571)). Qed.
Lemma lem1963910 (_27572 : real) (h1 : term105) : term210 _27572.
Proof. exact (@lem1963877 h1 _27572). Qed.
Lemma lem1963911 (_27572 : real) : (term210 _27572) = (term197 _27572).
Proof. exact (eq_refl (term210 _27572)). Qed.
Lemma lem1963912 (_27572 : real) (h1 : term105) : term197 _27572.
Proof. exact (EQ_MP (@lem1963911 _27572) (@lem1963910 _27572 h1)). Qed.
Lemma lem1963913 (_27572 : real) (_27573 : real) (h1 : term105) : term211 _27572 _27573.
Proof. exact (@lem1963912 _27572 h1 _27573). Qed.
Lemma lem1963914 (_27572 : real) (_27573 : real) : (term211 _27572 _27573) = (term194 _27572 _27573).
Proof. exact (eq_refl (term211 _27572 _27573)). Qed.
Lemma lem1963915 (_27572 : real) (_27573 : real) (h1 : term105) : term194 _27572 _27573.
Proof. exact (EQ_MP (@lem1963914 _27572 _27573) (@lem1963913 _27572 _27573 h1)). Qed.
Lemma lem1963938 (_27572 : real) (_27573 : real) : (term194 _27572 _27573) = (term212 _27572 _27573).
Proof. exact (@lem1962573 (term174 _27573) (term213 _27573 _27572) ((sqrt _27572) = _27573)). Qed.
Lemma lem1963985 (_27565 : real) (_27566 : nat) (h1 : term140) : term161 _27565 _27566.
Proof. exact (EQ_MP (@lem1963893 _27565 _27566) (@lem1963892 _27565 _27566 h1)). Qed.
Lemma lem1964027 (_27572 : real) (_27573 : real) (h1 : term105) : term212 _27572 _27573.
Proof. exact (EQ_MP (@lem1963938 _27572 _27573) (@lem1963915 _27572 _27573 h1)). Qed.
Lemma lem1964041 (n : nat) (m : nat) (h1 : term145 n m) : term214 m.
Proof. exact (proj2 (@lem1963785 n m h1)). Qed.
Lemma lem1964100 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem1964101 (_27602 : real) (_27604 : real) (h1 : _27602 = _27604) : _27602 = _27604.
Proof. exact (h1). Qed.
Lemma lem1964102 (_27603 : nat) (_27605 : nat) (h1 : _27603 = _27605) : _27603 = _27605.
Proof. exact (h1). Qed.
Lemma lem1964103 (_27602 : real) (_27604 : real) (h1 : _27602 = _27604) : (real_pow _27602) = (real_pow _27604).
Proof. exact (MK_COMB (@lem1964100) (@lem1964101 _27602 _27604 h1)). Qed.
Lemma lem1964104 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) (h1 : _27603 = _27605) (h2 : _27602 = _27604) : (real_pow _27602 _27603) = (real_pow _27604 _27605).
Proof. exact (MK_COMB (@lem1964103 _27602 _27604 h2) (@lem1964102 _27603 _27605 h1)). Qed.
Lemma lem1964105 (_27602 : real) (_27604 : real) (_27603 : nat) (_27605 : nat) (h1 : _27603 = _27605) : term215 _27602 _27603 _27604 _27605.
Proof. exact (fun h0 : _27602 = _27604 => @lem1964104 _27603 _27605 _27602 _27604 h1 h0). Qed.
Lemma lem1964107 (a : Prop) (b : Prop) : (a -> b) = (term216 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1964108 (_27602 : real) (_27603 : nat) (_27604 : real) (_27605 : nat) : (term215 _27602 _27603 _27604 _27605) = (term217 _27602 _27603 _27604 _27605).
Proof. exact (@lem1964107 (_27602 = _27604) ((real_pow _27602 _27603) = (real_pow _27604 _27605))). Qed.
Lemma lem1964109 (_27602 : real) (_27604 : real) (_27603 : nat) (_27605 : nat) (h1 : _27603 = _27605) : term217 _27602 _27603 _27604 _27605.
Proof. exact (EQ_MP (@lem1964108 _27602 _27603 _27604 _27605) (@lem1964105 _27602 _27604 _27603 _27605 h1)). Qed.
Lemma lem1964110 (_27602 : real) (_27603 : nat) (_27604 : real) (_27605 : nat) : term218 _27602 _27603 _27604 _27605.
Proof. exact (fun h0 : _27603 = _27605 => @lem1964109 _27602 _27604 _27603 _27605 h0). Qed.
Lemma lem1964112 (a : Prop) (b : Prop) : (a -> b) = (term216 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1964113 (_27602 : real) (_27603 : nat) (_27604 : real) (_27605 : nat) : (term218 _27602 _27603 _27604 _27605) = (term219 _27602 _27603 _27604 _27605).
Proof. exact (@lem1964112 (_27603 = _27605) (term217 _27602 _27603 _27604 _27605)). Qed.
Lemma lem1964114 (_27602 : real) (_27603 : nat) (_27604 : real) (_27605 : nat) : term219 _27602 _27603 _27604 _27605.
Proof. exact (EQ_MP (@lem1964113 _27602 _27603 _27604 _27605) (@lem1964110 _27602 _27603 _27604 _27605)). Qed.
Lemma lem1964132 (x : real) (y : real) (z : real) : term220 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1964136 (_27564 : nat) (h1 : term143) : term141 _27564.
Proof. exact (EQ_MP (@lem1963887 _27564) (@lem1963886 _27564 h1)). Qed.
Lemma lem1964137 (h1 : term143) : term221.
Proof. exact (@lem1964136 term81 h1). Qed.
Lemma lem1964138 (h1 : term143) : term222.
Proof. exact (fun h0 : term223 => @lem1964137 h1). Qed.
Lemma lem1964140 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1964141 : term222 = term221.
Proof. exact (@lem1964140 term221). Qed.
Lemma lem1964142 (h1 : term143) : term221.
Proof. exact (EQ_MP (@lem1964141) (@lem1964138 h1)). Qed.
Lemma lem1964148 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1964149 (_27566 : nat) (_27565 : real) : (term161 _27565 _27566) = (term225 _27566 _27565).
Proof. exact (@lem1964148 (term163 _27565 _27566) (term174 _27565)). Qed.
Lemma lem1964155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1964156 (_27566 : nat) (_27565 : real) : (term226 _27565 _27566) = (term227 _27566 _27565).
Proof. exact (MK_COMB (@lem1964155) (@lem1964149 _27566 _27565)). Qed.
Lemma lem1964162 (_27566 : nat) (_27565 : real) : (term225 _27566 _27565) = (term225 _27566 _27565).
Proof. exact (eq_refl (term225 _27566 _27565)). Qed.
Lemma lem1964163 (_27566 : nat) (_27565 : real) : ((term161 _27565 _27566) = (term225 _27566 _27565)) = ((term225 _27566 _27565) = (term225 _27566 _27565)).
Proof. exact (MK_COMB (@lem1964156 _27566 _27565) (@lem1964162 _27566 _27565)). Qed.
Lemma lem1964165 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1964166 (x : Prop) : (x = x) = True.
Proof. exact (@lem1964165 Prop x). Qed.
Lemma lem1964167 (_27566 : nat) (_27565 : real) : ((term225 _27566 _27565) = (term225 _27566 _27565)) = True.
Proof. exact (@lem1964166 (term225 _27566 _27565)). Qed.
Lemma lem1964168 (_27566 : nat) (_27565 : real) : ((term161 _27565 _27566) = (term225 _27566 _27565)) = True.
Proof. exact (TRANS (@lem1964163 _27566 _27565) (@lem1964167 _27566 _27565)). Qed.
Lemma lem1964169 (_27566 : nat) (_27565 : real) : True = ((term161 _27565 _27566) = (term225 _27566 _27565)).
Proof. exact (SYM (@lem1964168 _27566 _27565)). Qed.
Lemma lem1964170 (_27566 : nat) (_27565 : real) : (term161 _27565 _27566) = (term225 _27566 _27565).
Proof. exact (EQ_MP (@lem1964169 _27566 _27565) (@lem0)). Qed.
Lemma lem1964171 (_27566 : nat) (_27565 : real) (h1 : term140) : term225 _27566 _27565.
Proof. exact (EQ_MP (@lem1964170 _27566 _27565) (@lem1963985 _27565 _27566 h1)). Qed.
Lemma lem1964173 (b : Prop) (a : Prop) : (a \/ b) = (term228 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1964174 (_27565 : real) (_27566 : nat) : (term225 _27566 _27565) = (term229 _27565 _27566).
Proof. exact (@lem1964173 (term174 _27565) (term163 _27565 _27566)). Qed.
Lemma lem1964176 (a : Prop) : (term230 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1964177 (_27565 : real) : (term231 _27565) = (term162 _27565).
Proof. exact (@lem1964176 (term162 _27565)). Qed.
Lemma lem1964178 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1964179 (_27565 : real) : (term232 _27565) = (term233 _27565).
Proof. exact (MK_COMB (@lem1964178) (@lem1964177 _27565)). Qed.
Lemma lem1964180 (_27565 : real) (_27566 : nat) : (term163 _27565 _27566) = (term163 _27565 _27566).
Proof. exact (eq_refl (term163 _27565 _27566)). Qed.
Lemma lem1964181 (_27565 : real) (_27566 : nat) : (term229 _27565 _27566) = (term136 _27565 _27566).
Proof. exact (MK_COMB (@lem1964179 _27565) (@lem1964180 _27565 _27566)). Qed.
Lemma lem1964182 (_27565 : real) (_27566 : nat) : (term225 _27566 _27565) = (term136 _27565 _27566).
Proof. exact (TRANS (@lem1964174 _27565 _27566) (@lem1964181 _27565 _27566)). Qed.
Lemma lem1964185 (_27565 : real) (_27566 : nat) (h1 : term140) : term136 _27565 _27566.
Proof. exact (EQ_MP (@lem1964182 _27565 _27566) (@lem1964171 _27566 _27565 h1)). Qed.
Lemma lem1964186 (_27566 : nat) (h1 : term140) : term234 _27566.
Proof. exact (@lem1964185 term235 _27566 h1). Qed.
Lemma lem1964189 (_27566 : nat) (h1 : term143) (h2 : term140) : term236 _27566.
Proof. exact (@lem1964186 _27566 h2 (@lem1964142 h1)). Qed.
Lemma lem1964190 (m : nat) (h1 : term143) (h2 : term140) : term236 m.
Proof. exact (@lem1964189 m h1 h2). Qed.
Lemma lem1964191 (m : nat) (h1 : term143) (h2 : term140) : term237 m.
Proof. exact (fun h0 : term238 m => @lem1964190 m h1 h2). Qed.
Lemma lem1964193 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1964194 (m : nat) : (term237 m) = (term236 m).
Proof. exact (@lem1964193 (term236 m)). Qed.
Lemma lem1964195 (m : nat) (h1 : term143) (h2 : term140) : term236 m.
Proof. exact (EQ_MP (@lem1964194 m) (@lem1964191 m h1 h2)). Qed.
Lemma lem1964197 (_27569 : real) (_27570 : nat) (_27571 : nat) (h1 : term131) : (term124 _27569 _27570 _27571) = (term125 _27569 _27570 _27571).
Proof. exact (EQ_MP (@lem1963908 _27569 _27570 _27571) (@lem1963907 _27569 _27570 _27571 h1)). Qed.
Lemma lem1964198 (m : nat) (h1 : term131) : (term239 m) = (term240 m).
Proof. exact (@lem1964197 term235 m term81 h1). Qed.
Lemma lem1964199 (m : nat) (h1 : term131) : term241 m.
Proof. exact (fun h0 : term242 m => @lem1964198 m h1). Qed.
Lemma lem1964201 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1964202 (m : nat) : (term241 m) = ((term239 m) = (term240 m)).
Proof. exact (@lem1964201 ((term239 m) = (term240 m))). Qed.
Lemma lem1964203 (m : nat) (h1 : term131) : (term239 m) = (term240 m).
Proof. exact (EQ_MP (@lem1964202 m) (@lem1964199 m h1)). Qed.
Lemma lem1964205 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1964206 (m : nat) : (term239 m) = (term239 m).
Proof. exact (@lem1964205 (term239 m)). Qed.
Lemma lem1964207 (m : nat) : term243 m.
Proof. exact (fun h0 : term244 m => @lem1964206 m). Qed.
Lemma lem1964209 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1964210 (m : nat) : (term243 m) = ((term239 m) = (term239 m)).
Proof. exact (@lem1964209 ((term239 m) = (term239 m))). Qed.
Lemma lem1964211 (m : nat) : (term239 m) = (term239 m).
Proof. exact (EQ_MP (@lem1964210 m) (@lem1964207 m)). Qed.
Lemma lem1964229 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1964230 (y : real) (x : real) (z : real) : (term245 x y z) = (term246 y x z).
Proof. exact (@lem1964229 (y = z) (term247 x z)). Qed.
Lemma lem1964240 (x : real) (y : real) : (term248 x y) = (term248 x y).
Proof. exact (eq_refl (term248 x y)). Qed.
Lemma lem1964241 (y : real) (x : real) (z : real) : (term220 x y z) = (term249 y x z).
Proof. exact (MK_COMB (@lem1964240 x y) (@lem1964230 y x z)). Qed.
Lemma lem1964245 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1964246 (y : real) (x : real) (z : real) : (term249 y x z) = (term250 y x z).
Proof. exact (@lem1964245 (y = z) (term247 x y) (term247 x z)). Qed.
Lemma lem1964268 (y : real) (x : real) (z : real) : (term220 x y z) = (term250 y x z).
Proof. exact (TRANS (@lem1964241 y x z) (@lem1964246 y x z)). Qed.
Lemma lem1964269 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1964270 (y : real) (x : real) (z : real) : (term251 x y z) = (term252 y x z).
Proof. exact (MK_COMB (@lem1964269) (@lem1964268 y x z)). Qed.
Lemma lem1964292 (y : real) (x : real) (z : real) : (term250 y x z) = (term250 y x z).
Proof. exact (eq_refl (term250 y x z)). Qed.
Lemma lem1964293 (y : real) (x : real) (z : real) : ((term220 x y z) = (term250 y x z)) = ((term250 y x z) = (term250 y x z)).
Proof. exact (MK_COMB (@lem1964270 y x z) (@lem1964292 y x z)). Qed.
Lemma lem1964295 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1964296 (x : Prop) : (x = x) = True.
Proof. exact (@lem1964295 Prop x). Qed.
Lemma lem1964297 (y : real) (x : real) (z : real) : ((term250 y x z) = (term250 y x z)) = True.
Proof. exact (@lem1964296 (term250 y x z)). Qed.
Lemma lem1964298 (y : real) (x : real) (z : real) : ((term220 x y z) = (term250 y x z)) = True.
Proof. exact (TRANS (@lem1964293 y x z) (@lem1964297 y x z)). Qed.
Lemma lem1964299 (y : real) (x : real) (z : real) : True = ((term220 x y z) = (term250 y x z)).
Proof. exact (SYM (@lem1964298 y x z)). Qed.
Lemma lem1964300 (y : real) (x : real) (z : real) : (term220 x y z) = (term250 y x z).
Proof. exact (EQ_MP (@lem1964299 y x z) (@lem0)). Qed.
Lemma lem1964301 (y : real) (x : real) (z : real) : term250 y x z.
Proof. exact (EQ_MP (@lem1964300 y x z) (@lem1964132 x y z)). Qed.
Lemma lem1964303 (b : Prop) (a : Prop) : (a \/ b) = (term228 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1964304 (x : real) (y : real) (z : real) : (term250 y x z) = (term253 x y z).
Proof. exact (@lem1964303 (term254 y x z) (y = z)). Qed.
Lemma lem1964306 (a : Prop) (b : Prop) : (term255 a b) = (term256 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1964307 (y : real) (x : real) (z : real) : (term257 y x z) = (term258 y x z).
Proof. exact (@lem1964306 (term247 x y) (term247 x z)). Qed.
Lemma lem1964309 (a : Prop) : (term230 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1964310 (x : real) (y : real) : (term259 x y) = (x = y).
Proof. exact (@lem1964309 (x = y)). Qed.
Lemma lem1964311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1964312 (x : real) (y : real) : (term260 x y) = (term261 x y).
Proof. exact (MK_COMB (@lem1964311) (@lem1964310 x y)). Qed.
Lemma lem1964314 (a : Prop) : (term230 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1964315 (x : real) (z : real) : (term259 x z) = (x = z).
Proof. exact (@lem1964314 (x = z)). Qed.
Lemma lem1964316 (y : real) (x : real) (z : real) : (term258 y x z) = (term262 y x z).
Proof. exact (MK_COMB (@lem1964312 x y) (@lem1964315 x z)). Qed.
Lemma lem1964317 (y : real) (x : real) (z : real) : (term257 y x z) = (term262 y x z).
Proof. exact (TRANS (@lem1964307 y x z) (@lem1964316 y x z)). Qed.
Lemma lem1964318 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1964319 (y : real) (x : real) (z : real) : (term263 y x z) = (term264 y x z).
Proof. exact (MK_COMB (@lem1964318) (@lem1964317 y x z)). Qed.
Lemma lem1964320 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1964321 (x : real) (y : real) (z : real) : (term253 x y z) = (term265 x y z).
Proof. exact (MK_COMB (@lem1964319 y x z) (@lem1964320 y z)). Qed.
Lemma lem1964322 (x : real) (y : real) (z : real) : (term250 y x z) = (term265 x y z).
Proof. exact (TRANS (@lem1964304 x y z) (@lem1964321 x y z)). Qed.
Lemma lem1964324 (m : nat) (h1 : term131) : term266 m.
Proof. exact (conj (@lem1964203 m h1) (@lem1964211 m)). Qed.
Lemma lem1964326 (x : real) (y : real) (z : real) : term265 x y z.
Proof. exact (EQ_MP (@lem1964322 x y z) (@lem1964301 y x z)). Qed.
Lemma lem1964327 (m : nat) : term267 m.
Proof. exact (@lem1964326 (term239 m) (term240 m) (term239 m)). Qed.
Lemma lem1964330 (m : nat) (h1 : term131) : (term240 m) = (term239 m).
Proof. exact (@lem1964327 m (@lem1964324 m h1)). Qed.
Lemma lem1964331 (m : nat) (h1 : term131) : term268 m.
Proof. exact (fun h0 : term269 m => @lem1964330 m h1). Qed.
Lemma lem1964333 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1964334 (m : nat) : (term268 m) = ((term240 m) = (term239 m)).
Proof. exact (@lem1964333 ((term240 m) = (term239 m))). Qed.
Lemma lem1964335 (m : nat) (h1 : term131) : (term240 m) = (term239 m).
Proof. exact (EQ_MP (@lem1964334 m) (@lem1964331 m h1)). Qed.
Lemma lem1964337 (_27568 : nat) (_27567 : nat) (h1 : term135) : (Nat.mul _27567 _27568) = (Nat.mul _27568 _27567).
Proof. exact (EQ_MP (@lem1963899 _27568 _27567) (@lem1963898 _27567 _27568 h1)). Qed.
Lemma lem1964338 (m : nat) (h1 : term135) : (term53 m) = (term270 m).
Proof. exact (@lem1964337 m term81 h1). Qed.
Lemma lem1964339 (m : nat) (h1 : term135) : term271 m.
Proof. exact (fun h0 : term272 m => @lem1964338 m h1). Qed.
Lemma lem1964341 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1964342 (m : nat) : (term271 m) = ((term53 m) = (term270 m)).
Proof. exact (@lem1964341 ((term53 m) = (term270 m))). Qed.
Lemma lem1964343 (m : nat) (h1 : term135) : (term53 m) = (term270 m).
Proof. exact (EQ_MP (@lem1964342 m) (@lem1964339 m h1)). Qed.
Lemma lem1964345 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1964346 : term235 = term235.
Proof. exact (@lem1964345 term235). Qed.
Lemma lem1964347 : term273.
Proof. exact (fun h0 : term274 => @lem1964346). Qed.
Lemma lem1964349 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1964350 : term273 = (term235 = term235).
Proof. exact (@lem1964349 (term235 = term235)). Qed.
Lemma lem1964351 : term235 = term235.
Proof. exact (EQ_MP (@lem1964350) (@lem1964347)). Qed.
Lemma lem1964369 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1964370 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : (term217 _27602 _27603 _27604 _27605) = (term275 _27603 _27605 _27602 _27604).
Proof. exact (@lem1964369 ((real_pow _27602 _27603) = (real_pow _27604 _27605)) (term247 _27602 _27604)). Qed.
Lemma lem1964380 (_27603 : nat) (_27605 : nat) : (term276 _27603 _27605) = (term276 _27603 _27605).
Proof. exact (eq_refl (term276 _27603 _27605)). Qed.
Lemma lem1964381 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : (term219 _27602 _27603 _27604 _27605) = (term277 _27603 _27605 _27602 _27604).
Proof. exact (MK_COMB (@lem1964380 _27603 _27605) (@lem1964370 _27603 _27605 _27602 _27604)). Qed.
Lemma lem1964385 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1964386 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : (term277 _27603 _27605 _27602 _27604) = (term278 _27603 _27605 _27602 _27604).
Proof. exact (@lem1964385 ((real_pow _27602 _27603) = (real_pow _27604 _27605)) (term279 _27603 _27605) (term247 _27602 _27604)). Qed.
Lemma lem1964408 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : (term219 _27602 _27603 _27604 _27605) = (term278 _27603 _27605 _27602 _27604).
Proof. exact (TRANS (@lem1964381 _27603 _27605 _27602 _27604) (@lem1964386 _27603 _27605 _27602 _27604)). Qed.
Lemma lem1964409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1964410 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : (term280 _27602 _27603 _27604 _27605) = (term281 _27603 _27605 _27602 _27604).
Proof. exact (MK_COMB (@lem1964409) (@lem1964408 _27603 _27605 _27602 _27604)). Qed.
Lemma lem1964432 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : (term278 _27603 _27605 _27602 _27604) = (term278 _27603 _27605 _27602 _27604).
Proof. exact (eq_refl (term278 _27603 _27605 _27602 _27604)). Qed.
Lemma lem1964433 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : ((term219 _27602 _27603 _27604 _27605) = (term278 _27603 _27605 _27602 _27604)) = ((term278 _27603 _27605 _27602 _27604) = (term278 _27603 _27605 _27602 _27604)).
Proof. exact (MK_COMB (@lem1964410 _27603 _27605 _27602 _27604) (@lem1964432 _27603 _27605 _27602 _27604)). Qed.
Lemma lem1964435 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1964436 (x : Prop) : (x = x) = True.
Proof. exact (@lem1964435 Prop x). Qed.
Lemma lem1964437 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : ((term278 _27603 _27605 _27602 _27604) = (term278 _27603 _27605 _27602 _27604)) = True.
Proof. exact (@lem1964436 (term278 _27603 _27605 _27602 _27604)). Qed.
Lemma lem1964438 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : ((term219 _27602 _27603 _27604 _27605) = (term278 _27603 _27605 _27602 _27604)) = True.
Proof. exact (TRANS (@lem1964433 _27603 _27605 _27602 _27604) (@lem1964437 _27603 _27605 _27602 _27604)). Qed.
Lemma lem1964439 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : True = ((term219 _27602 _27603 _27604 _27605) = (term278 _27603 _27605 _27602 _27604)).
Proof. exact (SYM (@lem1964438 _27603 _27605 _27602 _27604)). Qed.
Lemma lem1964440 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : (term219 _27602 _27603 _27604 _27605) = (term278 _27603 _27605 _27602 _27604).
Proof. exact (EQ_MP (@lem1964439 _27603 _27605 _27602 _27604) (@lem0)). Qed.
Lemma lem1964441 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : term278 _27603 _27605 _27602 _27604.
Proof. exact (EQ_MP (@lem1964440 _27603 _27605 _27602 _27604) (@lem1964114 _27602 _27603 _27604 _27605)). Qed.
Lemma lem1964443 (b : Prop) (a : Prop) : (a \/ b) = (term228 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1964444 (_27602 : real) (_27603 : nat) (_27604 : real) (_27605 : nat) : (term278 _27603 _27605 _27602 _27604) = (term282 _27602 _27603 _27604 _27605).
Proof. exact (@lem1964443 (term283 _27603 _27605 _27602 _27604) ((real_pow _27602 _27603) = (real_pow _27604 _27605))). Qed.
Lemma lem1964446 (a : Prop) (b : Prop) : (term255 a b) = (term256 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1964447 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : (term284 _27603 _27605 _27602 _27604) = (term285 _27603 _27605 _27602 _27604).
Proof. exact (@lem1964446 (term279 _27603 _27605) (term247 _27602 _27604)). Qed.
Lemma lem1964449 (a : Prop) : (term230 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1964450 (_27603 : nat) (_27605 : nat) : (term286 _27603 _27605) = (_27603 = _27605).
Proof. exact (@lem1964449 (_27603 = _27605)). Qed.
Lemma lem1964451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1964452 (_27603 : nat) (_27605 : nat) : (term287 _27603 _27605) = (term288 _27603 _27605).
Proof. exact (MK_COMB (@lem1964451) (@lem1964450 _27603 _27605)). Qed.
Lemma lem1964454 (a : Prop) : (term230 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1964455 (_27602 : real) (_27604 : real) : (term259 _27602 _27604) = (_27602 = _27604).
Proof. exact (@lem1964454 (_27602 = _27604)). Qed.
Lemma lem1964456 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : (term285 _27603 _27605 _27602 _27604) = (term289 _27603 _27605 _27602 _27604).
Proof. exact (MK_COMB (@lem1964452 _27603 _27605) (@lem1964455 _27602 _27604)). Qed.
Lemma lem1964457 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : (term284 _27603 _27605 _27602 _27604) = (term289 _27603 _27605 _27602 _27604).
Proof. exact (TRANS (@lem1964447 _27603 _27605 _27602 _27604) (@lem1964456 _27603 _27605 _27602 _27604)). Qed.
Lemma lem1964458 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1964459 (_27603 : nat) (_27605 : nat) (_27602 : real) (_27604 : real) : (term290 _27603 _27605 _27602 _27604) = (term291 _27603 _27605 _27602 _27604).
Proof. exact (MK_COMB (@lem1964458) (@lem1964457 _27603 _27605 _27602 _27604)). Qed.
Lemma lem1964460 (_27602 : real) (_27603 : nat) (_27604 : real) (_27605 : nat) : ((real_pow _27602 _27603) = (real_pow _27604 _27605)) = ((real_pow _27602 _27603) = (real_pow _27604 _27605)).
Proof. exact (eq_refl ((real_pow _27602 _27603) = (real_pow _27604 _27605))). Qed.
Lemma lem1964461 (_27602 : real) (_27603 : nat) (_27604 : real) (_27605 : nat) : (term282 _27602 _27603 _27604 _27605) = (term292 _27602 _27603 _27604 _27605).
Proof. exact (MK_COMB (@lem1964459 _27603 _27605 _27602 _27604) (@lem1964460 _27602 _27603 _27604 _27605)). Qed.
Lemma lem1964462 (_27602 : real) (_27603 : nat) (_27604 : real) (_27605 : nat) : (term278 _27603 _27605 _27602 _27604) = (term292 _27602 _27603 _27604 _27605).
Proof. exact (TRANS (@lem1964444 _27602 _27603 _27604 _27605) (@lem1964461 _27602 _27603 _27604 _27605)). Qed.
Lemma lem1964464 (m : nat) (h1 : term135) : term293 m.
Proof. exact (conj (@lem1964343 m h1) (@lem1964351)). Qed.
Lemma lem1964466 (_27602 : real) (_27603 : nat) (_27604 : real) (_27605 : nat) : term292 _27602 _27603 _27604 _27605.
Proof. exact (EQ_MP (@lem1964462 _27602 _27603 _27604 _27605) (@lem1964441 _27603 _27605 _27602 _27604)). Qed.
Lemma lem1964467 (m : nat) : term294 m.
Proof. exact (@lem1964466 term235 (term53 m) term235 (term270 m)). Qed.
Lemma lem1964470 (m : nat) (h1 : term135) : (term76 m) = (term240 m).
Proof. exact (@lem1964467 m (@lem1964464 m h1)). Qed.
Lemma lem1964471 (m : nat) (h1 : term135) : term295 m.
Proof. exact (fun h0 : term296 m => @lem1964470 m h1). Qed.
Lemma lem1964473 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1964474 (m : nat) : (term295 m) = ((term76 m) = (term240 m)).
Proof. exact (@lem1964473 ((term76 m) = (term240 m))). Qed.
Lemma lem1964475 (m : nat) (h1 : term135) : (term76 m) = (term240 m).
Proof. exact (EQ_MP (@lem1964474 m) (@lem1964471 m h1)). Qed.
Lemma lem1964477 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1964478 (m : nat) : (term76 m) = (term76 m).
Proof. exact (@lem1964477 (term76 m)). Qed.
Lemma lem1964479 (m : nat) : term297 m.
Proof. exact (fun h0 : term298 m => @lem1964478 m). Qed.
Lemma lem1964481 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1964482 (m : nat) : (term297 m) = ((term76 m) = (term76 m)).
Proof. exact (@lem1964481 ((term76 m) = (term76 m))). Qed.
Lemma lem1964483 (m : nat) : (term76 m) = (term76 m).
Proof. exact (EQ_MP (@lem1964482 m) (@lem1964479 m)). Qed.
Lemma lem1964484 (m : nat) (h1 : term135) : term299 m.
Proof. exact (conj (@lem1964475 m h1) (@lem1964483 m)). Qed.
Lemma lem1964486 (x : real) (y : real) (z : real) : term265 x y z.
Proof. exact (EQ_MP (@lem1964322 x y z) (@lem1964301 y x z)). Qed.
Lemma lem1964487 (m : nat) : term300 m.
Proof. exact (@lem1964486 (term76 m) (term240 m) (term76 m)). Qed.
Lemma lem1964490 (m : nat) (h1 : term135) : (term240 m) = (term76 m).
Proof. exact (@lem1964487 m (@lem1964484 m h1)). Qed.
Lemma lem1964491 (m : nat) (h1 : term135) : term301 m.
Proof. exact (fun h0 : term302 m => @lem1964490 m h1). Qed.
Lemma lem1964493 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1964494 (m : nat) : (term301 m) = ((term240 m) = (term76 m)).
Proof. exact (@lem1964493 ((term240 m) = (term76 m))). Qed.
Lemma lem1964495 (m : nat) (h1 : term135) : (term240 m) = (term76 m).
Proof. exact (EQ_MP (@lem1964494 m) (@lem1964491 m h1)). Qed.
Lemma lem1964496 (m : nat) (h1 : term135) (h2 : term131) : term303 m.
Proof. exact (conj (@lem1964335 m h2) (@lem1964495 m h1)). Qed.
Lemma lem1964498 (x : real) (y : real) (z : real) : term265 x y z.
Proof. exact (EQ_MP (@lem1964322 x y z) (@lem1964301 y x z)). Qed.
Lemma lem1964499 (m : nat) : term304 m.
Proof. exact (@lem1964498 (term240 m) (term239 m) (term76 m)). Qed.
Lemma lem1964502 (m : nat) (h1 : term135) (h2 : term131) : (term239 m) = (term76 m).
Proof. exact (@lem1964499 m (@lem1964496 m h1 h2)). Qed.
Lemma lem1964503 (m : nat) (h1 : term135) (h2 : term131) : term305 m.
Proof. exact (fun h0 : term306 m => @lem1964502 m h1 h2). Qed.
Lemma lem1964505 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1964506 (m : nat) : (term305 m) = ((term239 m) = (term76 m)).
Proof. exact (@lem1964505 ((term239 m) = (term76 m))). Qed.
Lemma lem1964507 (m : nat) (h1 : term135) (h2 : term131) : (term239 m) = (term76 m).
Proof. exact (EQ_MP (@lem1964506 m) (@lem1964503 m h1 h2)). Qed.
Lemma lem1964513 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1964514 (_27572 : real) (_27573 : real) : (term212 _27572 _27573) = (term307 _27572 _27573).
Proof. exact (@lem1964513 (term213 _27573 _27572) (term174 _27573) ((sqrt _27572) = _27573)). Qed.
Lemma lem1964530 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1964531 (_27572 : real) (_27573 : real) : (term308 _27572 _27573) = (term309 _27572 _27573).
Proof. exact (@lem1964530 ((sqrt _27572) = _27573) (term174 _27573)). Qed.
Lemma lem1964539 (_27573 : real) (_27572 : real) : (term310 _27573 _27572) = (term310 _27573 _27572).
Proof. exact (eq_refl (term310 _27573 _27572)). Qed.
Lemma lem1964540 (_27572 : real) (_27573 : real) : (term307 _27572 _27573) = (term311 _27572 _27573).
Proof. exact (MK_COMB (@lem1964539 _27573 _27572) (@lem1964531 _27572 _27573)). Qed.
Lemma lem1964544 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1964545 (_27572 : real) (_27573 : real) : (term311 _27572 _27573) = (term312 _27572 _27573).
Proof. exact (@lem1964544 ((sqrt _27572) = _27573) (term213 _27573 _27572) (term174 _27573)). Qed.
Lemma lem1964565 (_27572 : real) (_27573 : real) : (term307 _27572 _27573) = (term312 _27572 _27573).
Proof. exact (TRANS (@lem1964540 _27572 _27573) (@lem1964545 _27572 _27573)). Qed.
Lemma lem1964566 (_27572 : real) (_27573 : real) : (term212 _27572 _27573) = (term312 _27572 _27573).
Proof. exact (TRANS (@lem1964514 _27572 _27573) (@lem1964565 _27572 _27573)). Qed.
Lemma lem1964567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1964568 (_27572 : real) (_27573 : real) : (term313 _27572 _27573) = (term314 _27572 _27573).
Proof. exact (MK_COMB (@lem1964567) (@lem1964566 _27572 _27573)). Qed.
Lemma lem1964584 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1964585 (_27572 : real) (_27573 : real) : (term189 _27573 _27572) = (term315 _27572 _27573).
Proof. exact (@lem1964584 (term213 _27573 _27572) (term174 _27573)). Qed.
Lemma lem1964593 (_27572 : real) (_27573 : real) : (term316 _27572 _27573) = (term316 _27572 _27573).
Proof. exact (eq_refl (term316 _27572 _27573)). Qed.
Lemma lem1964594 (_27572 : real) (_27573 : real) : (term317 _27573 _27572) = (term312 _27572 _27573).
Proof. exact (MK_COMB (@lem1964593 _27572 _27573) (@lem1964585 _27572 _27573)). Qed.
Lemma lem1964605 (_27572 : real) (_27573 : real) : ((term212 _27572 _27573) = (term317 _27573 _27572)) = ((term312 _27572 _27573) = (term312 _27572 _27573)).
Proof. exact (MK_COMB (@lem1964568 _27572 _27573) (@lem1964594 _27572 _27573)). Qed.
Lemma lem1964607 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1964608 (x : Prop) : (x = x) = True.
Proof. exact (@lem1964607 Prop x). Qed.
Lemma lem1964609 (_27572 : real) (_27573 : real) : ((term312 _27572 _27573) = (term312 _27572 _27573)) = True.
Proof. exact (@lem1964608 (term312 _27572 _27573)). Qed.
Lemma lem1964610 (_27573 : real) (_27572 : real) : ((term212 _27572 _27573) = (term317 _27573 _27572)) = True.
Proof. exact (TRANS (@lem1964605 _27572 _27573) (@lem1964609 _27572 _27573)). Qed.
Lemma lem1964611 (_27573 : real) (_27572 : real) : True = ((term212 _27572 _27573) = (term317 _27573 _27572)).
Proof. exact (SYM (@lem1964610 _27573 _27572)). Qed.
Lemma lem1964612 (_27573 : real) (_27572 : real) : (term212 _27572 _27573) = (term317 _27573 _27572).
Proof. exact (EQ_MP (@lem1964611 _27573 _27572) (@lem0)). Qed.
Lemma lem1964613 (_27573 : real) (_27572 : real) (h1 : term105) : term317 _27573 _27572.
Proof. exact (EQ_MP (@lem1964612 _27573 _27572) (@lem1964027 _27572 _27573 h1)). Qed.
Lemma lem1964615 (b : Prop) (a : Prop) : (a \/ b) = (term228 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1964616 (_27572 : real) (_27573 : real) : (term317 _27573 _27572) = (term318 _27572 _27573).
Proof. exact (@lem1964615 (term189 _27573 _27572) ((sqrt _27572) = _27573)). Qed.
Lemma lem1964618 (a : Prop) (b : Prop) : (term255 a b) = (term256 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1964619 (_27573 : real) (_27572 : real) : (term319 _27573 _27572) = (term320 _27573 _27572).
Proof. exact (@lem1964618 (term174 _27573) (term213 _27573 _27572)). Qed.
Lemma lem1964621 (a : Prop) : (term230 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1964622 (_27573 : real) : (term231 _27573) = (term162 _27573).
Proof. exact (@lem1964621 (term162 _27573)). Qed.
Lemma lem1964623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1964624 (_27573 : real) : (term321 _27573) = (term322 _27573).
Proof. exact (MK_COMB (@lem1964623) (@lem1964622 _27573)). Qed.
Lemma lem1964626 (a : Prop) : (term230 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1964627 (_27573 : real) (_27572 : real) : (term323 _27573 _27572) = ((term190 _27573) = _27572).
Proof. exact (@lem1964626 ((term190 _27573) = _27572)). Qed.
Lemma lem1964628 (_27573 : real) (_27572 : real) : (term320 _27573 _27572) = (term195 _27573 _27572).
Proof. exact (MK_COMB (@lem1964624 _27573) (@lem1964627 _27573 _27572)). Qed.
Lemma lem1964629 (_27573 : real) (_27572 : real) : (term319 _27573 _27572) = (term195 _27573 _27572).
Proof. exact (TRANS (@lem1964619 _27573 _27572) (@lem1964628 _27573 _27572)). Qed.
Lemma lem1964630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1964631 (_27573 : real) (_27572 : real) : (term324 _27573 _27572) = (term325 _27573 _27572).
Proof. exact (MK_COMB (@lem1964630) (@lem1964629 _27573 _27572)). Qed.
Lemma lem1964632 (_27572 : real) (_27573 : real) : ((sqrt _27572) = _27573) = ((sqrt _27572) = _27573).
Proof. exact (eq_refl ((sqrt _27572) = _27573)). Qed.
Lemma lem1964633 (_27572 : real) (_27573 : real) : (term318 _27572 _27573) = (term120 _27572 _27573).
Proof. exact (MK_COMB (@lem1964631 _27573 _27572) (@lem1964632 _27572 _27573)). Qed.
Lemma lem1964634 (_27572 : real) (_27573 : real) : (term317 _27573 _27572) = (term120 _27572 _27573).
Proof. exact (TRANS (@lem1964616 _27572 _27573) (@lem1964633 _27572 _27573)). Qed.
Lemma lem1964636 (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) : term326 m.
Proof. exact (conj (@lem1964195 m h2 h4) (@lem1964507 m h1 h3)). Qed.
Lemma lem1964638 (_27572 : real) (_27573 : real) (h1 : term105) : term120 _27572 _27573.
Proof. exact (EQ_MP (@lem1964634 _27572 _27573) (@lem1964613 _27573 _27572 h1)). Qed.
Lemma lem1964639 (m : nat) (h1 : term105) : term327 m.
Proof. exact (@lem1964638 (term76 m) (term75 m) h1). Qed.
Lemma lem1964642 (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) : (term77 m) = (term75 m).
Proof. exact (@lem1964639 m h5 (@lem1964636 m h1 h2 h3 h4)). Qed.
Lemma lem1964643 (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) : term328 m.
Proof. exact (fun h0 : term214 m => @lem1964642 m h1 h2 h3 h4 h5). Qed.
Lemma lem1964645 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1964646 (m : nat) : (term328 m) = ((term77 m) = (term75 m)).
Proof. exact (@lem1964645 ((term77 m) = (term75 m))). Qed.
Lemma lem1964647 (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) : (term77 m) = (term75 m).
Proof. exact (EQ_MP (@lem1964646 m) (@lem1964643 m h1 h2 h3 h4 h5)). Qed.
Lemma lem1964650 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1964652 (m : nat) : (term214 m) = (term329 m).
Proof. exact (@lem1964650 ((term77 m) = (term75 m))). Qed.
Lemma lem1964655 (n : nat) (m : nat) (h1 : term145 n m) : term329 m.
Proof. exact (EQ_MP (@lem1964652 m) (@lem1964041 n m h1)). Qed.
Lemma lem1964658 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : False.
Proof. exact (@lem1964655 n m h6 (@lem1964647 m h1 h2 h3 h4 h5)). Qed.
Lemma lem1964659 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : term330.
Proof. exact (fun h0 : ~ False => @lem1964658 n m h1 h2 h3 h4 h5 h6). Qed.
Lemma lem1964661 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1964662 : term330 = False.
Proof. exact (@lem1964661 False). Qed.
Lemma lem1964664 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : False.
Proof. exact (EQ_MP (@lem1964662) (@lem1964659 n m h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1964665 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : term131 = False.
Proof. exact (prop_ext (fun h7 : term131 => @lem1964664 n m h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1963855 h3)). Qed.
Lemma lem1964666 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : False.
Proof. exact (EQ_MP (@lem1964665 n m h1 h2 h3 h4 h5 h6) (@lem1963855 h3)). Qed.
Lemma lem1964667 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : term135 = False.
Proof. exact (prop_ext (fun h7 : term135 => @lem1964666 n m h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1963842 h1)). Qed.
Lemma lem1964668 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : False.
Proof. exact (EQ_MP (@lem1964667 n m h1 h2 h3 h4 h5 h6) (@lem1963842 h1)). Qed.
Lemma lem1964669 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : term143 = False.
Proof. exact (prop_ext (fun h7 : term143 => @lem1964668 n m h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1963794 h2)). Qed.
Lemma lem1964670 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : False.
Proof. exact (EQ_MP (@lem1964669 n m h1 h2 h3 h4 h5 h6) (@lem1963794 h2)). Qed.
Lemma lem1964671 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : (term145 n m) = False.
Proof. exact (prop_ext (fun h7 : term145 n m => @lem1964670 n m h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1963785 n m h6)). Qed.
Lemma lem1964672 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : False.
Proof. exact (EQ_MP (@lem1964671 n m h1 h2 h3 h4 h5 h6) (@lem1963785 n m h6)). Qed.
Lemma lem1964673 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : term131 = False.
Proof. exact (prop_ext (fun h7 : term131 => @lem1964672 n m h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1963675 h3)). Qed.
Lemma lem1964674 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : False.
Proof. exact (EQ_MP (@lem1964673 n m h1 h2 h3 h4 h5 h6) (@lem1963675 h3)). Qed.
Lemma lem1964675 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : term135 = False.
Proof. exact (prop_ext (fun h7 : term135 => @lem1964674 n m h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1963644 h1)). Qed.
Lemma lem1964676 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : False.
Proof. exact (EQ_MP (@lem1964675 n m h1 h2 h3 h4 h5 h6) (@lem1963644 h1)). Qed.
Lemma lem1964677 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : term143 = False.
Proof. exact (prop_ext (fun h7 : term143 => @lem1964676 n m h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1963590 h2)). Qed.
Lemma lem1964678 (n : nat) (m : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term145 n m) : False.
Proof. exact (EQ_MP (@lem1964677 n m h1 h2 h3 h4 h5 h6) (@lem1963590 h2)). Qed.
Lemma lem1964679 (n : nat) (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term154 n) : False.
Proof. exact (ex_elim (@lem1963574 n h6) (fun m : nat => fun h0 : term153 n m => @lem1964678 n m h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem1964680 (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term98) : False.
Proof. exact (ex_elim (@lem1963341 h6) (fun n : nat => fun h0 : term159 n => @lem1964679 n h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem1964681 (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term98) : term131 = False.
Proof. exact (prop_ext (fun h7 : term131 => @lem1964680 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1963497 h3)). Qed.
Lemma lem1964682 (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term98) : False.
Proof. exact (EQ_MP (@lem1964681 h1 h2 h3 h4 h5 h6) (@lem1963497 h3)). Qed.
Lemma lem1964683 (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term98) : term135 = False.
Proof. exact (prop_ext (fun h7 : term135 => @lem1964682 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1963470 h1)). Qed.
Lemma lem1964684 (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term98) : False.
Proof. exact (EQ_MP (@lem1964683 h1 h2 h3 h4 h5 h6) (@lem1963470 h1)). Qed.
Lemma lem1964685 (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term98) : term143 = False.
Proof. exact (prop_ext (fun h7 : term143 => @lem1964684 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1963354 h2)). Qed.
Lemma lem1964686 (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term105) (h6 : term98) : False.
Proof. exact (EQ_MP (@lem1964685 h1 h2 h3 h4 h5 h6) (@lem1963354 h2)). Qed.
Lemma lem1964687 (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term98) : term103.
Proof. exact (fun h0 : term105 => @lem1964686 h1 h2 h3 h4 h0 h5). Qed.
Lemma lem1964688 : term103 = term104.
Proof. exact (@lem69 term105). Qed.
Lemma lem1964689 (h1 : term135) (h2 : term143) (h3 : term131) (h4 : term140) (h5 : term98) : term104.
Proof. exact (EQ_MP (@lem1964688) (@lem1964687 h1 h2 h3 h4 h5)). Qed.
Lemma lem1964690 (h1 : term135) (h2 : term143) (h3 : term140) (h4 : term98) : term108.
Proof. exact (fun h0 : term131 => @lem1964689 h1 h2 h0 h3 h4). Qed.
Lemma lem1964691 (h1 : term143) (h2 : term140) (h3 : term98) : term111.
Proof. exact (fun h0 : term135 => @lem1964690 h0 h1 h2 h3). Qed.
Lemma lem1964692 (h1 : term143) (h2 : term98) : term114.
Proof. exact (fun h0 : term140 => @lem1964691 h1 h0 h2). Qed.
Lemma lem1964693 (h1 : term98) : term117.
Proof. exact (fun h0 : term143 => @lem1964692 h0 h1). Qed.
Lemma lem1964694 : term119.
Proof. exact (fun h0 : term98 => @lem1964693 h0). Qed.
Lemma lem1964695 : term99.
Proof. exact (EQ_MP (@lem1963251) (@lem1964694)). Qed.
Lemma lem1964697 : term99.
Proof. exact (@lem1962987 (@lem1964695)). Qed.
Lemma lem1964698 (h1 : term98) : term116.
Proof. exact (@lem1964697 (@lem1962972 h1)). Qed.
Lemma lem1964699 (h1 : term98) : term113.
Proof. exact (@lem1964698 h1 (@lem1384343)). Qed.
Lemma lem1964700 (h1 : term98) : term110.
Proof. exact (@lem1964699 h1 (@lem1582434)). Qed.
Lemma lem1964701 (h1 : term98) : term107.
Proof. exact (@lem1964700 h1 (@lem81820)). Qed.
Lemma lem1964702 (h1 : term98) : term103.
Proof. exact (@lem1964701 h1 (@lem1640492)). Qed.
Lemma lem1964703 (h1 : term98) : False.
Proof. exact (@lem1964702 h1 (@lem1900060)). Qed.
Lemma lem1964704 (h1 : term98) : term98 = False.
Proof. exact (prop_ext (fun h2 : term98 => @lem1964703 h1) (fun h2 : False => @lem1962972 h1)). Qed.
Lemma lem1964705 (h1 : term98) : False.
Proof. exact (EQ_MP (@lem1964704 h1) (@lem1962972 h1)). Qed.
Lemma lem1964706 : term97.
Proof. exact (fun h0 : term98 => @lem1964705 h0). Qed.
Lemma lem1964707 : term95.
Proof. exact (EQ_MP (@lem1962971) (@lem1964706)). Qed.
Lemma lem1964708 : term94.
Proof. exact (EQ_MP (@lem1962967) (@lem1964707)). Qed.
