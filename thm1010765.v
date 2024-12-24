Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1010765_term_abbrevs.
Require Import LT_REFL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16464_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem1010553 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1010554 (n : nat) : ((term1 n) = False) = (term2 n).
Proof. exact (@lem1010553 ((term1 n) = False)). Qed.
Lemma lem1010555 (n : nat) : (term2 n) = ((term1 n) = False).
Proof. exact (SYM (@lem1010554 n)). Qed.
Lemma lem1010556 (n : nat) (h1 : term3 n) : term3 n.
Proof. exact (h1). Qed.
Lemma lem1010559 (n : nat) (h1 : term4 n) : term4 n.
Proof. exact (h1). Qed.
Lemma lem1010560 (n : nat) : term5 n.
Proof. exact (fun h0 : term4 n => @lem1010559 n h0). Qed.
Lemma lem1010561 (n : nat) (h1 : term5 n) : term5 n.
Proof. exact (h1). Qed.
Lemma lem1010562 (n : nat) (h1 : term4 n) : term4 n.
Proof. exact (h1). Qed.
Lemma lem1010563 (n : nat) (h1 : term4 n) (h2 : term5 n) : term4 n.
Proof. exact (@lem1010561 n h2 (@lem1010562 n h1)). Qed.
Lemma lem1010564 (n : nat) (h1 : term4 n) : term6 n.
Proof. exact (fun h0 : term5 n => @lem1010563 n h1 h0). Qed.
Lemma lem1010565 (n : nat) (h1 : term5 n) : term5 n.
Proof. exact (h1). Qed.
Lemma lem1010566 (n : nat) (h1 : term4 n) (h2 : term5 n) : term4 n.
Proof. exact (@lem1010564 n h1 (@lem1010565 n h2)). Qed.
Lemma lem1010567 (n : nat) (h1 : term5 n) : term5 n.
Proof. exact (fun h0 : term4 n => @lem1010566 n h0 h1). Qed.
Lemma lem1010568 (n : nat) : term7 n.
Proof. exact (fun h0 : term5 n => @lem1010567 n h0). Qed.
Lemma lem1010571 (n : nat) : term5 n.
Proof. exact (@lem1010568 n (@lem1010560 n)). Qed.
Lemma lem1010579 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem1010580 (n : nat) : ((term1 n) = False) = (term8 n).
Proof. exact (@lem1010579 (term1 n)). Qed.
Lemma lem1010581 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1010582 (n : nat) : (term3 n) = (term9 n).
Proof. exact (MK_COMB (@lem1010581) (@lem1010580 n)). Qed.
Lemma lem1010584 (t : Prop) : (term10 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1010585 (n : nat) : (term9 n) = (term1 n).
Proof. exact (@lem1010584 (term1 n)). Qed.
Lemma lem1010586 (n : nat) : (term3 n) = (term1 n).
Proof. exact (TRANS (@lem1010582 n) (@lem1010585 n)). Qed.
Lemma lem1010587 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1010588 (n : nat) : (term11 n) = (term12 n).
Proof. exact (MK_COMB (@lem1010587) (@lem1010586 n)). Qed.
Lemma lem1010590 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1010591 : term13 = term14.
Proof. exact (@lem1010590 term15). Qed.
Lemma lem1010596 (n : nat) : (term4 n) = (term16 n).
Proof. exact (MK_COMB (@lem1010588 n) (@lem1010591)). Qed.
Lemma lem1010599 : term17 = term18.
Proof. exact (fun_ext (fun n : nat => @lem1010596 n)). Qed.
Lemma lem1010600 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010609 : term19 = term20.
Proof. exact (MK_COMB (@lem1010600) (@lem1010599)). Qed.
Lemma lem1010612 (n : nat) : (term21 n) = (term21 n).
Proof. exact (eq_refl (term21 n)). Qed.
Lemma lem1010613 : term22 = term22.
Proof. exact (fun_ext (fun n : nat => @lem1010612 n)). Qed.
Lemma lem1010614 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010615 : term15 = term15.
Proof. exact (MK_COMB (@lem1010614) (@lem1010613)). Qed.
Lemma lem1010616 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1010617 : term14 = term14.
Proof. exact (MK_COMB (@lem1010616) (@lem1010615)). Qed.
Lemma lem1010620 (n : nat) : (term12 n) = (term12 n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem1010621 (n : nat) : (term16 n) = (term16 n).
Proof. exact (MK_COMB (@lem1010620 n) (@lem1010617)). Qed.
Lemma lem1010622 : term18 = term18.
Proof. exact (fun_ext (fun n : nat => @lem1010621 n)). Qed.
Lemma lem1010623 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010624 : term20 = term20.
Proof. exact (MK_COMB (@lem1010623) (@lem1010622)). Qed.
Lemma lem1010641 : term19 = term20.
Proof. exact (TRANS (@lem1010609) (@lem1010624)). Qed.
Lemma lem1010642 : term20 = term19.
Proof. exact (SYM (@lem1010641)). Qed.
Lemma lem1010644 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem1010650 (n : nat) (h1 : term1 n) : term1 n.
Proof. exact (h1). Qed.
Lemma lem1010651 (n : nat) : (term21 n) = (term21 n).
Proof. exact (eq_refl (term21 n)). Qed.
Lemma lem1010652 : term22 = term22.
Proof. exact (fun_ext (fun n : nat => @lem1010651 n)). Qed.
Lemma lem1010653 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010662 : term15 = term15.
Proof. exact (MK_COMB (@lem1010653) (@lem1010652)). Qed.
Lemma lem1010663 (h1 : term15) : term15.
Proof. exact (EQ_MP (@lem1010662) (@lem1010644 h1)). Qed.
Lemma lem1010673 (n : nat) (h1 : term1 n) : term1 n.
Proof. exact (h1). Qed.
Lemma lem1010680 (n : nat) : (term21 n) = (term21 n).
Proof. exact (eq_refl (term21 n)). Qed.
Lemma lem1010681 : term22 = term22.
Proof. exact (fun_ext (fun n : nat => @lem1010680 n)). Qed.
Lemma lem1010682 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010683 : term15 = term15.
Proof. exact (MK_COMB (@lem1010682) (@lem1010681)). Qed.
Lemma lem1010684 (h1 : term15) : term15.
Proof. exact (EQ_MP (@lem1010683) (@lem1010663 h1)). Qed.
Lemma lem1010688 (n : nat) (h1 : term1 n) : term1 n.
Proof. exact (h1). Qed.
Lemma lem1010690 (n : nat) : (term21 n) = (term21 n).
Proof. exact (eq_refl (term21 n)). Qed.
Lemma lem1010691 : term22 = term22.
Proof. exact (fun_ext (fun n : nat => @lem1010690 n)). Qed.
Lemma lem1010692 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1010694 : term15 = term15.
Proof. exact (MK_COMB (@lem1010692) (@lem1010691)). Qed.
Lemma lem1010695 (h1 : term15) : term15.
Proof. exact (EQ_MP (@lem1010694) (@lem1010684 h1)). Qed.
Lemma lem1010696 (_16421 : nat) (h1 : term15) : term23 _16421.
Proof. exact (@lem1010695 h1 _16421). Qed.
Lemma lem1010697 (_16421 : nat) : (term23 _16421) = (term21 _16421).
Proof. exact (eq_refl (term23 _16421)). Qed.
Lemma lem1010700 (n : nat) (h1 : term1 n) : term1 n.
Proof. exact (h1). Qed.
Lemma lem1010702 (_16421 : nat) (h1 : term15) : term21 _16421.
Proof. exact (EQ_MP (@lem1010697 _16421) (@lem1010696 _16421 h1)). Qed.
Lemma lem1010704 (n : nat) (h1 : term1 n) : term1 n.
Proof. exact (h1). Qed.
Lemma lem1010705 (n : nat) (h1 : term1 n) : term24 n.
Proof. exact (fun h0 : term8 n => @lem1010704 n h1). Qed.
Lemma lem1010707 (p : Prop) : (term25 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1010708 (n : nat) : (term24 n) = (term1 n).
Proof. exact (@lem1010707 (term1 n)). Qed.
Lemma lem1010709 (n : nat) (h1 : term1 n) : term1 n.
Proof. exact (EQ_MP (@lem1010708 n) (@lem1010705 n h1)). Qed.
Lemma lem1010712 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1010714 (_16421 : nat) : (term21 _16421) = (term26 _16421).
Proof. exact (@lem1010712 (Peano.lt _16421 _16421)). Qed.
Lemma lem1010717 (_16421 : nat) (h1 : term15) : term26 _16421.
Proof. exact (EQ_MP (@lem1010714 _16421) (@lem1010702 _16421 h1)). Qed.
Lemma lem1010718 (n : nat) (h1 : term15) : term27 n.
Proof. exact (@lem1010717 (NUMERAL n) h1). Qed.
Lemma lem1010721 (n : nat) (h1 : term15) (h2 : term1 n) : False.
Proof. exact (@lem1010718 n h1 (@lem1010709 n h2)). Qed.
Lemma lem1010722 (n : nat) (h1 : term15) (h2 : term1 n) : term28.
Proof. exact (fun h0 : ~ False => @lem1010721 n h1 h2). Qed.
Lemma lem1010724 (p : Prop) : (term25 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1010725 : term28 = False.
Proof. exact (@lem1010724 False). Qed.
Lemma lem1010726 (n : nat) (h1 : term15) (h2 : term1 n) : False.
Proof. exact (EQ_MP (@lem1010725) (@lem1010722 n h1 h2)). Qed.
Lemma lem1010727 (n : nat) (h1 : term15) (h2 : term1 n) : (term1 n) = False.
Proof. exact (prop_ext (fun h3 : term1 n => @lem1010726 n h1 h2) (fun h3 : False => @lem1010700 n h2)). Qed.
Lemma lem1010728 (n : nat) (h1 : term15) (h2 : term1 n) : False.
Proof. exact (EQ_MP (@lem1010727 n h1 h2) (@lem1010700 n h2)). Qed.
Lemma lem1010729 (n : nat) (h1 : term15) (h2 : term1 n) : (term1 n) = False.
Proof. exact (prop_ext (fun h3 : term1 n => @lem1010728 n h1 h2) (fun h3 : False => @lem1010688 n h2)). Qed.
Lemma lem1010730 (n : nat) (h1 : term15) (h2 : term1 n) : False.
Proof. exact (EQ_MP (@lem1010729 n h1 h2) (@lem1010688 n h2)). Qed.
Lemma lem1010731 (n : nat) (h1 : term15) (h2 : term1 n) : term15 = False.
Proof. exact (prop_ext (fun h3 : term15 => @lem1010730 n h1 h2) (fun h3 : False => @lem1010695 h1)). Qed.
Lemma lem1010732 (n : nat) (h1 : term15) (h2 : term1 n) : False.
Proof. exact (EQ_MP (@lem1010731 n h1 h2) (@lem1010695 h1)). Qed.
Lemma lem1010733 (n : nat) (h1 : term15) (h2 : term1 n) : (term1 n) = False.
Proof. exact (prop_ext (fun h3 : term1 n => @lem1010732 n h1 h2) (fun h3 : False => @lem1010688 n h2)). Qed.
Lemma lem1010734 (n : nat) (h1 : term15) (h2 : term1 n) : False.
Proof. exact (EQ_MP (@lem1010733 n h1 h2) (@lem1010688 n h2)). Qed.
Lemma lem1010735 (n : nat) (h1 : term15) (h2 : term1 n) : term15 = False.
Proof. exact (prop_ext (fun h3 : term15 => @lem1010734 n h1 h2) (fun h3 : False => @lem1010684 h1)). Qed.
Lemma lem1010736 (n : nat) (h1 : term15) (h2 : term1 n) : False.
Proof. exact (EQ_MP (@lem1010735 n h1 h2) (@lem1010684 h1)). Qed.
Lemma lem1010737 (n : nat) (h1 : term15) (h2 : term1 n) : (term1 n) = False.
Proof. exact (prop_ext (fun h3 : term1 n => @lem1010736 n h1 h2) (fun h3 : False => @lem1010673 n h2)). Qed.
Lemma lem1010738 (n : nat) (h1 : term15) (h2 : term1 n) : False.
Proof. exact (EQ_MP (@lem1010737 n h1 h2) (@lem1010673 n h2)). Qed.
Lemma lem1010739 (n : nat) (h1 : term15) (h2 : term1 n) : term15 = False.
Proof. exact (prop_ext (fun h3 : term15 => @lem1010738 n h1 h2) (fun h3 : False => @lem1010663 h1)). Qed.
Lemma lem1010740 (n : nat) (h1 : term15) (h2 : term1 n) : False.
Proof. exact (EQ_MP (@lem1010739 n h1 h2) (@lem1010663 h1)). Qed.
Lemma lem1010741 (n : nat) (h1 : term15) (h2 : term1 n) : (term1 n) = False.
Proof. exact (prop_ext (fun h3 : term1 n => @lem1010740 n h1 h2) (fun h3 : False => @lem1010650 n h2)). Qed.
Lemma lem1010742 (n : nat) (h1 : term15) (h2 : term1 n) : False.
Proof. exact (EQ_MP (@lem1010741 n h1 h2) (@lem1010650 n h2)). Qed.
Lemma lem1010743 (n : nat) (h1 : term1 n) : term13.
Proof. exact (fun h0 : term15 => @lem1010742 n h0 h1). Qed.
Lemma lem1010744 : term13 = term14.
Proof. exact (@lem69 term15). Qed.
Lemma lem1010745 (n : nat) (h1 : term1 n) : term14.
Proof. exact (EQ_MP (@lem1010744) (@lem1010743 n h1)). Qed.
Lemma lem1010746 (n : nat) : term16 n.
Proof. exact (fun h0 : term1 n => @lem1010745 n h0). Qed.
Lemma lem1010751 : term20.
Proof. exact (fun n : nat => @lem1010746 n). Qed.
Lemma lem1010752 : term19.
Proof. exact (EQ_MP (@lem1010642) (@lem1010751)). Qed.
Lemma lem1010753 (n : nat) : term29 n.
Proof. exact (@lem1010752 n). Qed.
Lemma lem1010754 (n : nat) : (term29 n) = (term4 n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem1010755 (n : nat) : term4 n.
Proof. exact (EQ_MP (@lem1010754 n) (@lem1010753 n)). Qed.
Lemma lem1010757 (n : nat) : term4 n.
Proof. exact (@lem1010571 n (@lem1010755 n)). Qed.
Lemma lem1010758 (n : nat) (h1 : term3 n) : term13.
Proof. exact (@lem1010757 n (@lem1010556 n h1)). Qed.
Lemma lem1010759 (n : nat) (h1 : term3 n) : False.
Proof. exact (@lem1010758 n h1 (@lem91686)). Qed.
Lemma lem1010760 (n : nat) (h1 : term3 n) : (term3 n) = False.
Proof. exact (prop_ext (fun h2 : term3 n => @lem1010759 n h1) (fun h2 : False => @lem1010556 n h1)). Qed.
Lemma lem1010761 (n : nat) (h1 : term3 n) : False.
Proof. exact (EQ_MP (@lem1010760 n h1) (@lem1010556 n h1)). Qed.
Lemma lem1010762 (n : nat) : term2 n.
Proof. exact (fun h0 : term3 n => @lem1010761 n h0). Qed.
Lemma lem1010765 (n : nat) : (term1 n) = False.
Proof. exact (EQ_MP (@lem1010555 n) (@lem1010762 n)). Qed.
