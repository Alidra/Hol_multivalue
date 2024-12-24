Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ODD_MOD_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DIVISION_spec.
Require Import EVEN_MOD_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EVEN_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
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
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm80360_spec.
Require Import thm80550_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Lemma lem201645 : term0.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem201646 (m : nat) : term1 m.
Proof. exact (@lem201645 m). Qed.
Lemma lem201647 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem201648 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem201647 m) (@lem201646 m)). Qed.
Lemma lem201649 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem201648 m n). Qed.
Lemma lem201650 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem201652 : term6.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem201653 (m : nat) : term7 m.
Proof. exact (@lem201652 m). Qed.
Lemma lem201654 (m : nat) : (term7 m) = ((term8 m) = False).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem201656 (n : nat) : term9 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem201657 (n : nat) : (term9 n) = (term10 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem201658 (n : nat) : term10 n.
Proof. exact (EQ_MP (@lem201657 n) (@lem201656 n)). Qed.
Lemma lem201659 (n : nat) : term11 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem201672 (m : nat) : term12 m.
Proof. exact (@lem157261 m). Qed.
Lemma lem201673 (m : nat) : (term12 m) = (term13 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem201674 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem201673 m) (@lem201672 m)). Qed.
Lemma lem201675 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem201674 m n). Qed.
Lemma lem201676 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem201677 (m : nat) (n : nat) : term15 m n.
Proof. exact (EQ_MP (@lem201676 m n) (@lem201675 m n)). Qed.
Lemma lem201678 (n : nat) (h1 : term16 n) : term16 n.
Proof. exact (h1). Qed.
Lemma lem201679 (m : nat) (n : nat) (h1 : term16 n) : term17 m n.
Proof. exact (@lem201677 m n (@lem201678 n h1)). Qed.
Lemma lem201680 (m : nat) (n : nat) (h1 : term16 n) : term18 m n.
Proof. exact (proj2 (@lem201679 m n h1)). Qed.
Lemma lem201681 (m : nat) (n : nat) : (term18 m n) = ((term18 m n) = True).
Proof. exact (@lem7 (term18 m n)). Qed.
Lemma lem201682 (m : nat) (n : nat) (h1 : term16 n) : (term18 m n) = True.
Proof. exact (EQ_MP (@lem201681 m n) (@lem201680 m n h1)). Qed.
Lemma lem201700 (n : nat) (h1 : (term19 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (term19 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (h1). Qed.
Lemma lem201701 (n : nat) (h1 : (term19 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term19 n).
Proof. exact (SYM (@lem201700 n h1)). Qed.
Lemma lem201702 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term19 n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term19 n).
Proof. exact (h1). Qed.
Lemma lem201703 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term19 n)) : (term19 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (SYM (@lem201702 n h1)). Qed.
Lemma lem201704 (n : nat) : ((term19 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term19 n)).
Proof. exact (prop_ext (fun h1 : (term19 n) = (Coq.Arith.PeanoNat.Nat.Odd n) => @lem201701 n h1) (fun h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term19 n) => @lem201703 n h1)). Qed.
Lemma lem201705 : term20 = term21.
Proof. exact (fun_ext (fun n : nat => @lem201704 n)). Qed.
Lemma lem201706 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem201707 : term22 = term23.
Proof. exact (MK_COMB (@lem201706) (@lem201705)). Qed.
Lemma lem201708 : term23.
Proof. exact (EQ_MP (@lem201707) (@lem124715)). Qed.
Lemma lem201709 (n : nat) : term24 n.
Proof. exact (@lem201634 n). Qed.
Lemma lem201710 (n : nat) : (term24 n) = ((Coq.Arith.PeanoNat.Nat.Even n) = ((term25 n) = (NUMERAL 0))).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem201712 (n : nat) : term26 n.
Proof. exact (@lem201708 n). Qed.
Lemma lem201713 (n : nat) : (term26 n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term19 n)).
Proof. exact (eq_refl (term26 n)). Qed.
Lemma lem201718 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term19 n).
Proof. exact (EQ_MP (@lem201713 n) (@lem201712 n)). Qed.
Lemma lem201720 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = ((term25 n) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem201710 n) (@lem201709 n)). Qed.
Lemma lem201723 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem201724 (n : nat) : (term19 n) = (term27 n).
Proof. exact (MK_COMB (@lem201723) (@lem201720 n)). Qed.
Lemma lem201725 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term27 n).
Proof. exact (TRANS (@lem201718 n) (@lem201724 n)). Qed.
Lemma lem201726 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem201727 (n : nat) : (term28 n) = (term29 n).
Proof. exact (MK_COMB (@lem201726) (@lem201725 n)). Qed.
Lemma lem201730 (n : nat) : ((term25 n) = term30) = ((term25 n) = term30).
Proof. exact (eq_refl ((term25 n) = term30)). Qed.
Lemma lem201731 (n : nat) : ((Coq.Arith.PeanoNat.Nat.Odd n) = ((term25 n) = term30)) = ((term27 n) = ((term25 n) = term30)).
Proof. exact (MK_COMB (@lem201727 n) (@lem201730 n)). Qed.
Lemma lem201734 (n : nat) : ((term27 n) = ((term25 n) = term30)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = ((term25 n) = term30)).
Proof. exact (SYM (@lem201731 n)). Qed.
Lemma lem201735 (n : nat) (h1 : term31 n) : term31 n.
Proof. exact (h1). Qed.
Lemma lem201737 (m : nat) (n : nat) : term32 m n.
Proof. exact (fun h0 : term16 n => @lem201682 m n h0). Qed.
Lemma lem201738 (n : nat) : term33 n.
Proof. exact (@lem201737 n term34). Qed.
Lemma lem201752 : term34 = term35.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem201767 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem201768 : term36 = term37.
Proof. exact (MK_COMB (@lem201767) (@lem201752)). Qed.
Lemma lem201793 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem201794 : (term34 = (NUMERAL 0)) = (term35 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem201768) (@lem201793)). Qed.
Lemma lem201796 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem201659 n (@lem201658 n)). Qed.
Lemma lem201797 : (term35 = (NUMERAL 0)) = False.
Proof. exact (@lem201796 term30). Qed.
Lemma lem201800 : (term34 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem201794) (@lem201797)). Qed.
Lemma lem201801 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem201802 : term38 = (~ False).
Proof. exact (MK_COMB (@lem201801) (@lem201800)). Qed.
Lemma lem201804 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem201807 : term38 = True.
Proof. exact (TRANS (@lem201802) (@lem201804)). Qed.
Lemma lem201808 : True = term38.
Proof. exact (SYM (@lem201807)). Qed.
Lemma lem201809 : term38.
Proof. exact (EQ_MP (@lem201808) (@lem0)). Qed.
Lemma lem201810 (n : nat) : (term31 n) = True.
Proof. exact (@lem201738 n (@lem201809)). Qed.
Lemma lem201813 (n : nat) : True = (term31 n).
Proof. exact (SYM (@lem201810 n)). Qed.
Lemma lem201814 (n : nat) : term31 n.
Proof. exact (EQ_MP (@lem201813 n) (@lem0)). Qed.
Lemma lem201822 : term34 = term35.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem201824 : term30 = term39.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem201825 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem201826 : term35 = term40.
Proof. exact (MK_COMB (@lem201825) (@lem201824)). Qed.
Lemma lem201827 : term34 = term40.
Proof. exact (TRANS (@lem201822) (@lem201826)). Qed.
Lemma lem201828 (n : nat) : (Peano.lt n) = (Peano.lt n).
Proof. exact (eq_refl (Peano.lt n)). Qed.
Lemma lem201829 (n : nat) : (term41 n) = (term42 n).
Proof. exact (MK_COMB (@lem201828 n) (@lem201827)). Qed.
Lemma lem201831 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem201650 m n) (@lem201649 m n)). Qed.
Lemma lem201832 (n : nat) : (term42 n) = (term43 n).
Proof. exact (@lem201831 n term39). Qed.
Lemma lem201838 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem201650 m n) (@lem201649 m n)). Qed.
Lemma lem201839 (n : nat) : (term44 n) = (term45 n).
Proof. exact (@lem201838 n (NUMERAL 0)). Qed.
Lemma lem201845 (m : nat) : (term8 m) = False.
Proof. exact (EQ_MP (@lem201654 m) (@lem201653 m)). Qed.
Lemma lem201846 (n : nat) : (term8 n) = False.
Proof. exact (@lem201845 n). Qed.
Lemma lem201847 (n : nat) : (term46 n) = (term46 n).
Proof. exact (eq_refl (term46 n)). Qed.
Lemma lem201848 (n : nat) : (term45 n) = (term47 n).
Proof. exact (MK_COMB (@lem201847 n) (@lem201846 n)). Qed.
Lemma lem201850 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem201851 (n : nat) : (term47 n) = (n = (NUMERAL 0)).
Proof. exact (@lem201850 (n = (NUMERAL 0))). Qed.
Lemma lem201854 (n : nat) : (term45 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem201848 n) (@lem201851 n)). Qed.
Lemma lem201855 (n : nat) : (term44 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem201839 n) (@lem201854 n)). Qed.
Lemma lem201856 (n : nat) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem201857 (n : nat) : (term43 n) = (term49 n).
Proof. exact (MK_COMB (@lem201856 n) (@lem201855 n)). Qed.
Lemma lem201860 (n : nat) : (term42 n) = (term49 n).
Proof. exact (TRANS (@lem201832 n) (@lem201857 n)). Qed.
Lemma lem201861 (n : nat) : (term41 n) = (term49 n).
Proof. exact (TRANS (@lem201829 n) (@lem201860 n)). Qed.
Lemma lem201862 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem201863 (n : nat) : (term50 n) = (term51 n).
Proof. exact (MK_COMB (@lem201862) (@lem201861 n)). Qed.
Lemma lem201871 : term30 = term39.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem201872 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem201873 (n : nat) : (n = term30) = (n = term39).
Proof. exact (MK_COMB (@lem201872 n) (@lem201871)). Qed.
Lemma lem201876 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem201877 (n : nat) : ((term16 n) = (n = term30)) = ((term16 n) = (n = term39)).
Proof. exact (MK_COMB (@lem201876 n) (@lem201873 n)). Qed.
Lemma lem201880 (n : nat) : (term53 n) = (term54 n).
Proof. exact (MK_COMB (@lem201863 n) (@lem201877 n)). Qed.
Lemma lem201883 : term55 = term56.
Proof. exact (fun_ext (fun n : nat => @lem201880 n)). Qed.
Lemma lem201884 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem201885 : term57 = term58.
Proof. exact (MK_COMB (@lem201884) (@lem201883)). Qed.
Lemma lem201890 : term58 = term57.
Proof. exact (SYM (@lem201885)). Qed.
Lemma lem201892 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem201893 : term58 = term60.
Proof. exact (@lem201892 term58). Qed.
Lemma lem201894 : term60 = term58.
Proof. exact (SYM (@lem201893)). Qed.
Lemma lem201895 (h1 : term61) : term61.
Proof. exact (h1). Qed.
Lemma lem201898 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem201899 : term63.
Proof. exact (fun h0 : term62 => @lem201898 h0). Qed.
Lemma lem201900 (h1 : term63) : term63.
Proof. exact (h1). Qed.
Lemma lem201901 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem201902 (h1 : term62) (h2 : term63) : term62.
Proof. exact (@lem201900 h2 (@lem201901 h1)). Qed.
Lemma lem201903 (h1 : term62) : term64.
Proof. exact (fun h0 : term63 => @lem201902 h1 h0). Qed.
Lemma lem201904 (h1 : term63) : term63.
Proof. exact (h1). Qed.
Lemma lem201905 (h1 : term62) (h2 : term63) : term62.
Proof. exact (@lem201903 h1 (@lem201904 h2)). Qed.
Lemma lem201906 (h1 : term63) : term63.
Proof. exact (fun h0 : term62 => @lem201905 h0 h1). Qed.
Lemma lem201907 : term65.
Proof. exact (fun h0 : term63 => @lem201906 h0). Qed.
Lemma lem201910 : term63.
Proof. exact (@lem201907 (@lem201899)). Qed.
Lemma lem201922 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem201923 : term66 = term67.
Proof. exact (@lem201922 term68). Qed.
Lemma lem201928 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem201935 : term62 = term70.
Proof. exact (MK_COMB (@lem201928) (@lem201923)). Qed.
Lemma lem201938 (n : nat) : (term10 n) = (term10 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem201939 : term71 = term71.
Proof. exact (fun_ext (fun n : nat => @lem201938 n)). Qed.
Lemma lem201940 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem201941 : term68 = term68.
Proof. exact (MK_COMB (@lem201940) (@lem201939)). Qed.
Lemma lem201942 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem201943 : term67 = term67.
Proof. exact (MK_COMB (@lem201942) (@lem201941)). Qed.
Lemma lem201958 (n : nat) : (term54 n) = (term54 n).
Proof. exact (eq_refl (term54 n)). Qed.
Lemma lem201959 : term56 = term56.
Proof. exact (fun_ext (fun n : nat => @lem201958 n)). Qed.
Lemma lem201960 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem201961 : term58 = term58.
Proof. exact (MK_COMB (@lem201960) (@lem201959)). Qed.
Lemma lem201962 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem201963 : term61 = term61.
Proof. exact (MK_COMB (@lem201962) (@lem201961)). Qed.
Lemma lem201964 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem201965 : term69 = term69.
Proof. exact (MK_COMB (@lem201964) (@lem201963)). Qed.
Lemma lem201966 : term70 = term70.
Proof. exact (MK_COMB (@lem201965) (@lem201943)). Qed.
Lemma lem201987 : term62 = term70.
Proof. exact (TRANS (@lem201935) (@lem201966)). Qed.
Lemma lem201988 : term70 = term62.
Proof. exact (SYM (@lem201987)). Qed.
Lemma lem201989 (h1 : term61) : term61.
Proof. exact (h1). Qed.
Lemma lem201990 (h1 : term68) : term68.
Proof. exact (h1). Qed.
Lemma lem201999 (n : nat) : (term72 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem202001 (n : nat) : (n = term39) = (n = term39).
Proof. exact (eq_refl (n = term39)). Qed.
Lemma lem202002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem202003 (n : nat) : (term73 n) = (term74 n).
Proof. exact (MK_COMB (@lem202002) (@lem201999 n)). Qed.
Lemma lem202004 (n : nat) : (term75 n) = (term76 n).
Proof. exact (MK_COMB (@lem202003 n) (@lem202001 n)). Qed.
Lemma lem202009 (n : nat) : (term77 n) = (term77 n).
Proof. exact (eq_refl (term77 n)). Qed.
Lemma lem202010 (n : nat) : (term78 n) = (term79 n).
Proof. exact (MK_COMB (@lem202009 n) (@lem202004 n)). Qed.
Lemma lem202011 (n : nat) : (term80 n) = (term78 n).
Proof. exact (@lem17646 (term16 n) (n = term39)). Qed.
Lemma lem202012 (n : nat) : (term80 n) = (term79 n).
Proof. exact (TRANS (@lem202011 n) (@lem202010 n)). Qed.
Lemma lem202014 (n : nat) : (term81 n) = (term81 n).
Proof. exact (eq_refl (term81 n)). Qed.
Lemma lem202015 (n : nat) : (term82 n) = (term83 n).
Proof. exact (MK_COMB (@lem202014 n) (@lem202012 n)). Qed.
Lemma lem202016 (n : nat) : (term84 n) = (term82 n).
Proof. exact (@lem17362 (term49 n) ((term16 n) = (n = term39))). Qed.
Lemma lem202017 (n : nat) : (term84 n) = (term83 n).
Proof. exact (TRANS (@lem202016 n) (@lem202015 n)). Qed.
Lemma lem202018 (P : nat -> Prop) : (term85 P) = (term86 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem202019 : term61 = term87.
Proof. exact (@lem202018 term56). Qed.
Lemma lem202020 (n : nat) : (term88 n) = (term54 n).
Proof. exact (eq_refl (term88 n)). Qed.
Lemma lem202021 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem202022 (n : nat) : (term89 n) = (term84 n).
Proof. exact (MK_COMB (@lem202021) (@lem202020 n)). Qed.
Lemma lem202023 (n : nat) : (term89 n) = (term83 n).
Proof. exact (TRANS (@lem202022 n) (@lem202017 n)). Qed.
Lemma lem202024 : term90 = term91.
Proof. exact (fun_ext (fun n : nat => @lem202023 n)). Qed.
Lemma lem202025 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem202026 : term87 = term92.
Proof. exact (MK_COMB (@lem202025) (@lem202024)). Qed.
Lemma lem202079 : term61 = term92.
Proof. exact (TRANS (@lem202019) (@lem202026)). Qed.
Lemma lem202080 (h1 : term61) : term92.
Proof. exact (EQ_MP (@lem202079) (@lem201989 h1)). Qed.
Lemma lem202081 (n : nat) : (term10 n) = (term10 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem202082 : term71 = term71.
Proof. exact (fun_ext (fun n : nat => @lem202081 n)). Qed.
Lemma lem202083 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem202092 : term68 = term68.
Proof. exact (MK_COMB (@lem202083) (@lem202082)). Qed.
Lemma lem202093 (h1 : term68) : term68.
Proof. exact (EQ_MP (@lem202092) (@lem201990 h1)). Qed.
Lemma lem202105 (n : nat) : (term10 n) = (term10 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem202106 : term71 = term71.
Proof. exact (fun_ext (fun n : nat => @lem202105 n)). Qed.
Lemma lem202107 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem202108 : term68 = term68.
Proof. exact (MK_COMB (@lem202107) (@lem202106)). Qed.
Lemma lem202109 (h1 : term68) : term68.
Proof. exact (EQ_MP (@lem202108) (@lem202093 h1)). Qed.
Lemma lem202177 (n : nat) (h1 : term83 n) : term83 n.
Proof. exact (h1). Qed.
Lemma lem202178 (n : nat) (h1 : term83 n) : term79 n.
Proof. exact (proj2 (@lem202177 n h1)). Qed.
Lemma lem202179 (n : nat) (h1 : term83 n) : term49 n.
Proof. exact (proj1 (@lem202177 n h1)). Qed.
Lemma lem202180 (n : nat) (h1 : term93 n) : term93 n.
Proof. exact (h1). Qed.
Lemma lem202181 (n : nat) (h1 : term76 n) : term76 n.
Proof. exact (h1). Qed.
Lemma lem202208 (n : nat) (h1 : n = term39) : n = term39.
Proof. exact (h1). Qed.
Lemma lem202227 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem202229 (n : nat) : (term10 n) = (term10 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem202230 : term71 = term71.
Proof. exact (fun_ext (fun n : nat => @lem202229 n)). Qed.
Lemma lem202231 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem202233 : term68 = term68.
Proof. exact (MK_COMB (@lem202231) (@lem202230)). Qed.
Lemma lem202234 (h1 : term68) : term68.
Proof. exact (EQ_MP (@lem202233) (@lem202109 h1)). Qed.
Lemma lem202248 (n : nat) : (term10 n) = (term10 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem202249 : term71 = term71.
Proof. exact (fun_ext (fun n : nat => @lem202248 n)). Qed.
Lemma lem202250 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem202252 : term68 = term68.
Proof. exact (MK_COMB (@lem202250) (@lem202249)). Qed.
Lemma lem202253 (h1 : term68) : term68.
Proof. exact (EQ_MP (@lem202252) (@lem202109 h1)). Qed.
Lemma lem202272 (_4093 : nat) (h1 : term68) : term9 _4093.
Proof. exact (@lem202234 h1 _4093). Qed.
Lemma lem202273 (_4093 : nat) : (term9 _4093) = (term10 _4093).
Proof. exact (eq_refl (term9 _4093)). Qed.
Lemma lem202275 (_4094 : nat) (h1 : term68) : term9 _4094.
Proof. exact (@lem202253 h1 _4094). Qed.
Lemma lem202276 (_4094 : nat) : (term9 _4094) = (term10 _4094).
Proof. exact (eq_refl (term9 _4094)). Qed.
Lemma lem202283 (n : nat) (h1 : term93 n) : term94 n.
Proof. exact (proj2 (@lem202180 n h1)). Qed.
Lemma lem202285 (n : nat) (h1 : n = term39) : n = term39.
Proof. exact (h1). Qed.
Lemma lem202289 (n : nat) (h1 : term93 n) : term16 n.
Proof. exact (proj1 (@lem202180 n h1)). Qed.
Lemma lem202293 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem202297 (n : nat) (h1 : term76 n) : n = (NUMERAL 0).
Proof. exact (proj1 (@lem202181 n h1)). Qed.
Lemma lem202299 (n : nat) (h1 : term76 n) : n = term39.
Proof. exact (proj2 (@lem202181 n h1)). Qed.
Lemma lem202301 (n : nat) (h1 : n = term39) : n = term39.
Proof. exact (h1). Qed.
Lemma lem202305 (n : nat) (h1 : term76 n) : n = (NUMERAL 0).
Proof. exact (proj1 (@lem202181 n h1)). Qed.
Lemma lem202307 (n : nat) (h1 : term76 n) : n = term39.
Proof. exact (proj2 (@lem202181 n h1)). Qed.
Lemma lem202309 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem202351 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem202352 (n : nat) (h1 : n = term39) : (term96 n) = term97.
Proof. exact (MK_COMB (@lem202351) (@lem202285 n h1)). Qed.
Lemma lem202353 : term97 = term98.
Proof. exact (eq_refl term97). Qed.
Lemma lem202354 (n : nat) : (term99 n) = (term99 n).
Proof. exact (eq_refl (term99 n)). Qed.
Lemma lem202355 (n : nat) : ((term96 n) = term97) = ((term96 n) = term98).
Proof. exact (MK_COMB (@lem202354 n) (@lem202353)). Qed.
Lemma lem202356 (n : nat) : (term96 n) = (term94 n).
Proof. exact (eq_refl (term96 n)). Qed.
Lemma lem202357 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem202358 (n : nat) : (term99 n) = (term100 n).
Proof. exact (MK_COMB (@lem202357) (@lem202356 n)). Qed.
Lemma lem202359 : term98 = term98.
Proof. exact (eq_refl term98). Qed.
Lemma lem202360 (n : nat) : ((term96 n) = term98) = ((term94 n) = term98).
Proof. exact (MK_COMB (@lem202358 n) (@lem202359)). Qed.
Lemma lem202361 (n : nat) : ((term96 n) = term97) = ((term94 n) = term98).
Proof. exact (TRANS (@lem202355 n) (@lem202360 n)). Qed.
Lemma lem202362 (n : nat) (h1 : n = term39) : (term94 n) = term98.
Proof. exact (EQ_MP (@lem202361 n) (@lem202352 n h1)). Qed.
Lemma lem202363 (n : nat) (h1 : term93 n) (h2 : n = term39) : term98.
Proof. exact (EQ_MP (@lem202362 n h2) (@lem202283 n h1)). Qed.
Lemma lem202392 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem202393 (n : nat) (h1 : n = (NUMERAL 0)) : (term102 n) = term103.
Proof. exact (MK_COMB (@lem202392) (@lem202293 n h1)). Qed.
Lemma lem202394 : term103 = term104.
Proof. exact (eq_refl term103). Qed.
Lemma lem202395 (n : nat) : (term105 n) = (term105 n).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem202396 (n : nat) : ((term102 n) = term103) = ((term102 n) = term104).
Proof. exact (MK_COMB (@lem202395 n) (@lem202394)). Qed.
Lemma lem202397 (n : nat) : (term102 n) = (term16 n).
Proof. exact (eq_refl (term102 n)). Qed.
Lemma lem202398 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem202399 (n : nat) : (term105 n) = (term52 n).
Proof. exact (MK_COMB (@lem202398) (@lem202397 n)). Qed.
Lemma lem202400 : term104 = term104.
Proof. exact (eq_refl term104). Qed.
Lemma lem202401 (n : nat) : ((term102 n) = term104) = ((term16 n) = term104).
Proof. exact (MK_COMB (@lem202399 n) (@lem202400)). Qed.
Lemma lem202402 (n : nat) : ((term102 n) = term103) = ((term16 n) = term104).
Proof. exact (TRANS (@lem202396 n) (@lem202401 n)). Qed.
Lemma lem202403 (n : nat) (h1 : n = (NUMERAL 0)) : (term16 n) = term104.
Proof. exact (EQ_MP (@lem202402 n) (@lem202393 n h1)). Qed.
Lemma lem202404 (n : nat) (h1 : term93 n) (h2 : n = (NUMERAL 0)) : term104.
Proof. exact (EQ_MP (@lem202403 n h2) (@lem202289 n h1)). Qed.
Lemma lem202445 (_4093 : nat) (h1 : term68) : term10 _4093.
Proof. exact (EQ_MP (@lem202273 _4093) (@lem202272 _4093 h1)). Qed.
Lemma lem202446 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem202447 (n : nat) (h1 : n = term39) : (term107 n) = term108.
Proof. exact (MK_COMB (@lem202446) (@lem202301 n h1)). Qed.
Lemma lem202448 : term108 = (term39 = (NUMERAL 0)).
Proof. exact (eq_refl term108). Qed.
Lemma lem202449 (n : nat) : (term109 n) = (term109 n).
Proof. exact (eq_refl (term109 n)). Qed.
Lemma lem202450 (n : nat) : ((term107 n) = term108) = ((term107 n) = (term39 = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem202449 n) (@lem202448)). Qed.
Lemma lem202451 (n : nat) : (term107 n) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (term107 n)). Qed.
Lemma lem202452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem202453 (n : nat) : (term109 n) = (term110 n).
Proof. exact (MK_COMB (@lem202452) (@lem202451 n)). Qed.
Lemma lem202454 : (term39 = (NUMERAL 0)) = (term39 = (NUMERAL 0)).
Proof. exact (eq_refl (term39 = (NUMERAL 0))). Qed.
Lemma lem202455 (n : nat) : ((term107 n) = (term39 = (NUMERAL 0))) = ((n = (NUMERAL 0)) = (term39 = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem202453 n) (@lem202454)). Qed.
Lemma lem202456 (n : nat) : ((term107 n) = term108) = ((n = (NUMERAL 0)) = (term39 = (NUMERAL 0))).
Proof. exact (TRANS (@lem202450 n) (@lem202455 n)). Qed.
Lemma lem202457 (n : nat) (h1 : n = term39) : (n = (NUMERAL 0)) = (term39 = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem202456 n) (@lem202447 n h1)). Qed.
Lemma lem202499 (_4094 : nat) (h1 : term68) : term10 _4094.
Proof. exact (EQ_MP (@lem202276 _4094) (@lem202275 _4094 h1)). Qed.
Lemma lem202513 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem202514 (n : nat) (h1 : n = (NUMERAL 0)) : (term112 n) = term113.
Proof. exact (MK_COMB (@lem202513) (@lem202309 n h1)). Qed.
Lemma lem202515 : term113 = ((NUMERAL 0) = term39).
Proof. exact (eq_refl term113). Qed.
Lemma lem202516 (n : nat) : (term114 n) = (term114 n).
Proof. exact (eq_refl (term114 n)). Qed.
Lemma lem202517 (n : nat) : ((term112 n) = term113) = ((term112 n) = ((NUMERAL 0) = term39)).
Proof. exact (MK_COMB (@lem202516 n) (@lem202515)). Qed.
Lemma lem202518 (n : nat) : (term112 n) = (n = term39).
Proof. exact (eq_refl (term112 n)). Qed.
Lemma lem202519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem202520 (n : nat) : (term114 n) = (term115 n).
Proof. exact (MK_COMB (@lem202519) (@lem202518 n)). Qed.
Lemma lem202521 : ((NUMERAL 0) = term39) = ((NUMERAL 0) = term39).
Proof. exact (eq_refl ((NUMERAL 0) = term39)). Qed.
Lemma lem202522 (n : nat) : ((term112 n) = ((NUMERAL 0) = term39)) = ((n = term39) = ((NUMERAL 0) = term39)).
Proof. exact (MK_COMB (@lem202520 n) (@lem202521)). Qed.
Lemma lem202523 (n : nat) : ((term112 n) = term113) = ((n = term39) = ((NUMERAL 0) = term39)).
Proof. exact (TRANS (@lem202517 n) (@lem202522 n)). Qed.
Lemma lem202524 (n : nat) (h1 : n = (NUMERAL 0)) : (n = term39) = ((NUMERAL 0) = term39).
Proof. exact (EQ_MP (@lem202523 n) (@lem202514 n h1)). Qed.
Lemma lem202545 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem202546 : term39 = term39.
Proof. exact (@lem202545 term39). Qed.
Lemma lem202547 : term116.
Proof. exact (fun h0 : term98 => @lem202546). Qed.
Lemma lem202549 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem202550 : term116 = (term39 = term39).
Proof. exact (@lem202549 (term39 = term39)). Qed.
Lemma lem202551 : term39 = term39.
Proof. exact (EQ_MP (@lem202550) (@lem202547)). Qed.
Lemma lem202554 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem202556 : term98 = term118.
Proof. exact (@lem202554 (term39 = term39)). Qed.
Lemma lem202559 (n : nat) (h1 : term93 n) (h2 : n = term39) : term118.
Proof. exact (EQ_MP (@lem202556) (@lem202363 n h1 h2)). Qed.
Lemma lem202562 (n : nat) (h1 : term93 n) (h2 : n = term39) : False.
Proof. exact (@lem202559 n h1 h2 (@lem202551)). Qed.
Lemma lem202563 (n : nat) (h1 : term93 n) (h2 : n = term39) : term119.
Proof. exact (fun h0 : ~ False => @lem202562 n h1 h2). Qed.
Lemma lem202565 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem202566 : term119 = False.
Proof. exact (@lem202565 False). Qed.
Lemma lem202587 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem202588 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (@lem202587 (NUMERAL 0)). Qed.
Lemma lem202589 : term120.
Proof. exact (fun h0 : term104 => @lem202588). Qed.
Lemma lem202591 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem202592 : term120 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem202591 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem202593 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem202592) (@lem202589)). Qed.
Lemma lem202596 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem202598 : term104 = term121.
Proof. exact (@lem202596 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem202601 (n : nat) (h1 : term93 n) (h2 : n = (NUMERAL 0)) : term121.
Proof. exact (EQ_MP (@lem202598) (@lem202404 n h1 h2)). Qed.
Lemma lem202604 (n : nat) (h1 : term93 n) (h2 : n = (NUMERAL 0)) : False.
Proof. exact (@lem202601 n h1 h2 (@lem202593)). Qed.
Lemma lem202605 (n : nat) (h1 : term93 n) (h2 : n = (NUMERAL 0)) : term119.
Proof. exact (fun h0 : ~ False => @lem202604 n h1 h2). Qed.
Lemma lem202607 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem202608 : term119 = False.
Proof. exact (@lem202607 False). Qed.
Lemma lem202629 (n : nat) (h1 : term76 n) (h2 : n = term39) : term39 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem202457 n h2) (@lem202297 n h1)). Qed.
Lemma lem202630 (n : nat) (h1 : term76 n) (h2 : n = term39) : term122.
Proof. exact (fun h0 : term123 => @lem202629 n h1 h2). Qed.
Lemma lem202632 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem202633 : term122 = (term39 = (NUMERAL 0)).
Proof. exact (@lem202632 (term39 = (NUMERAL 0))). Qed.
Lemma lem202634 (n : nat) (h1 : term76 n) (h2 : n = term39) : term39 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem202633) (@lem202630 n h1 h2)). Qed.
Lemma lem202637 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem202639 (_4093 : nat) : (term10 _4093) = (term124 _4093).
Proof. exact (@lem202637 ((S _4093) = (NUMERAL 0))). Qed.
Lemma lem202642 (_4093 : nat) (h1 : term68) : term124 _4093.
Proof. exact (EQ_MP (@lem202639 _4093) (@lem202445 _4093 h1)). Qed.
Lemma lem202643 (h1 : term68) : term125.
Proof. exact (@lem202642 (NUMERAL 0) h1). Qed.
Lemma lem202646 (n : nat) (h1 : term68) (h2 : term76 n) (h3 : n = term39) : False.
Proof. exact (@lem202643 h1 (@lem202634 n h2 h3)). Qed.
Lemma lem202647 (n : nat) (h1 : term68) (h2 : term76 n) (h3 : n = term39) : term119.
Proof. exact (fun h0 : ~ False => @lem202646 n h1 h2 h3). Qed.
Lemma lem202649 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem202650 : term119 = False.
Proof. exact (@lem202649 False). Qed.
Lemma lem202669 (x : nat) (y : nat) (z : nat) : term126 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem202671 (n : nat) (h1 : term76 n) (h2 : n = (NUMERAL 0)) : (NUMERAL 0) = term39.
Proof. exact (EQ_MP (@lem202524 n h2) (@lem202307 n h1)). Qed.
Lemma lem202672 (n : nat) (h1 : term76 n) (h2 : n = (NUMERAL 0)) : term127.
Proof. exact (fun h0 : term128 => @lem202671 n h1 h2). Qed.
Lemma lem202674 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem202675 : term127 = ((NUMERAL 0) = term39).
Proof. exact (@lem202674 ((NUMERAL 0) = term39)). Qed.
Lemma lem202676 (n : nat) (h1 : term76 n) (h2 : n = (NUMERAL 0)) : (NUMERAL 0) = term39.
Proof. exact (EQ_MP (@lem202675) (@lem202672 n h1 h2)). Qed.
Lemma lem202678 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem202679 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (@lem202678 (NUMERAL 0)). Qed.
Lemma lem202680 : term120.
Proof. exact (fun h0 : term104 => @lem202679). Qed.
Lemma lem202682 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem202683 : term120 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem202682 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem202684 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem202683) (@lem202680)). Qed.
Lemma lem202702 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem202703 (y : nat) (x : nat) (z : nat) : (term129 x y z) = (term130 y x z).
Proof. exact (@lem202702 (y = z) (term131 x z)). Qed.
Lemma lem202713 (x : nat) (y : nat) : (term132 x y) = (term132 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem202714 (y : nat) (x : nat) (z : nat) : (term126 x y z) = (term133 y x z).
Proof. exact (MK_COMB (@lem202713 x y) (@lem202703 y x z)). Qed.
Lemma lem202718 (q : Prop) (p : Prop) (r : Prop) : (term134 p q r) = (term134 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem202719 (y : nat) (x : nat) (z : nat) : (term133 y x z) = (term135 y x z).
Proof. exact (@lem202718 (y = z) (term131 x y) (term131 x z)). Qed.
Lemma lem202741 (y : nat) (x : nat) (z : nat) : (term126 x y z) = (term135 y x z).
Proof. exact (TRANS (@lem202714 y x z) (@lem202719 y x z)). Qed.
Lemma lem202742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem202743 (y : nat) (x : nat) (z : nat) : (term136 x y z) = (term137 y x z).
Proof. exact (MK_COMB (@lem202742) (@lem202741 y x z)). Qed.
Lemma lem202765 (y : nat) (x : nat) (z : nat) : (term135 y x z) = (term135 y x z).
Proof. exact (eq_refl (term135 y x z)). Qed.
Lemma lem202766 (y : nat) (x : nat) (z : nat) : ((term126 x y z) = (term135 y x z)) = ((term135 y x z) = (term135 y x z)).
Proof. exact (MK_COMB (@lem202743 y x z) (@lem202765 y x z)). Qed.
Lemma lem202768 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem202769 (x : Prop) : (x = x) = True.
Proof. exact (@lem202768 Prop x). Qed.
Lemma lem202770 (y : nat) (x : nat) (z : nat) : ((term135 y x z) = (term135 y x z)) = True.
Proof. exact (@lem202769 (term135 y x z)). Qed.
Lemma lem202771 (y : nat) (x : nat) (z : nat) : ((term126 x y z) = (term135 y x z)) = True.
Proof. exact (TRANS (@lem202766 y x z) (@lem202770 y x z)). Qed.
Lemma lem202772 (y : nat) (x : nat) (z : nat) : True = ((term126 x y z) = (term135 y x z)).
Proof. exact (SYM (@lem202771 y x z)). Qed.
Lemma lem202773 (y : nat) (x : nat) (z : nat) : (term126 x y z) = (term135 y x z).
Proof. exact (EQ_MP (@lem202772 y x z) (@lem0)). Qed.
Lemma lem202774 (y : nat) (x : nat) (z : nat) : term135 y x z.
Proof. exact (EQ_MP (@lem202773 y x z) (@lem202669 x y z)). Qed.
Lemma lem202776 (b : Prop) (a : Prop) : (a \/ b) = (term138 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem202777 (x : nat) (y : nat) (z : nat) : (term135 y x z) = (term139 x y z).
Proof. exact (@lem202776 (term140 y x z) (y = z)). Qed.
Lemma lem202779 (a : Prop) (b : Prop) : (term141 a b) = (term142 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem202780 (y : nat) (x : nat) (z : nat) : (term143 y x z) = (term144 y x z).
Proof. exact (@lem202779 (term131 x y) (term131 x z)). Qed.
Lemma lem202782 (a : Prop) : (term145 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem202783 (x : nat) (y : nat) : (term146 x y) = (x = y).
Proof. exact (@lem202782 (x = y)). Qed.
Lemma lem202784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem202785 (x : nat) (y : nat) : (term147 x y) = (term148 x y).
Proof. exact (MK_COMB (@lem202784) (@lem202783 x y)). Qed.
Lemma lem202787 (a : Prop) : (term145 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem202788 (x : nat) (z : nat) : (term146 x z) = (x = z).
Proof. exact (@lem202787 (x = z)). Qed.
Lemma lem202789 (y : nat) (x : nat) (z : nat) : (term144 y x z) = (term149 y x z).
Proof. exact (MK_COMB (@lem202785 x y) (@lem202788 x z)). Qed.
Lemma lem202790 (y : nat) (x : nat) (z : nat) : (term143 y x z) = (term149 y x z).
Proof. exact (TRANS (@lem202780 y x z) (@lem202789 y x z)). Qed.
Lemma lem202791 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem202792 (y : nat) (x : nat) (z : nat) : (term150 y x z) = (term151 y x z).
Proof. exact (MK_COMB (@lem202791) (@lem202790 y x z)). Qed.
Lemma lem202793 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem202794 (x : nat) (y : nat) (z : nat) : (term139 x y z) = (term152 x y z).
Proof. exact (MK_COMB (@lem202792 y x z) (@lem202793 y z)). Qed.
Lemma lem202795 (x : nat) (y : nat) (z : nat) : (term135 y x z) = (term152 x y z).
Proof. exact (TRANS (@lem202777 x y z) (@lem202794 x y z)). Qed.
Lemma lem202797 (n : nat) (h1 : term76 n) (h2 : n = (NUMERAL 0)) : term153.
Proof. exact (conj (@lem202676 n h1 h2) (@lem202684)). Qed.
Lemma lem202799 (x : nat) (y : nat) (z : nat) : term152 x y z.
Proof. exact (EQ_MP (@lem202795 x y z) (@lem202774 y x z)). Qed.
Lemma lem202800 : term154.
Proof. exact (@lem202799 (NUMERAL 0) term39 (NUMERAL 0)). Qed.
Lemma lem202803 (n : nat) (h1 : term76 n) (h2 : n = (NUMERAL 0)) : term39 = (NUMERAL 0).
Proof. exact (@lem202800 (@lem202797 n h1 h2)). Qed.
Lemma lem202804 (n : nat) (h1 : term76 n) (h2 : n = (NUMERAL 0)) : term122.
Proof. exact (fun h0 : term123 => @lem202803 n h1 h2). Qed.
Lemma lem202806 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem202807 : term122 = (term39 = (NUMERAL 0)).
Proof. exact (@lem202806 (term39 = (NUMERAL 0))). Qed.
Lemma lem202808 (n : nat) (h1 : term76 n) (h2 : n = (NUMERAL 0)) : term39 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem202807) (@lem202804 n h1 h2)). Qed.
Lemma lem202811 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem202813 (_4094 : nat) : (term10 _4094) = (term124 _4094).
Proof. exact (@lem202811 ((S _4094) = (NUMERAL 0))). Qed.
Lemma lem202816 (_4094 : nat) (h1 : term68) : term124 _4094.
Proof. exact (EQ_MP (@lem202813 _4094) (@lem202499 _4094 h1)). Qed.
Lemma lem202817 (h1 : term68) : term125.
Proof. exact (@lem202816 (NUMERAL 0) h1). Qed.
Lemma lem202820 (n : nat) (h1 : term68) (h2 : term76 n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (@lem202817 h1 (@lem202808 n h2 h3)). Qed.
Lemma lem202821 (n : nat) (h1 : term68) (h2 : term76 n) (h3 : n = (NUMERAL 0)) : term119.
Proof. exact (fun h0 : ~ False => @lem202820 n h1 h2 h3). Qed.
Lemma lem202823 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem202824 : term119 = False.
Proof. exact (@lem202823 False). Qed.
Lemma lem202826 (n : nat) (h1 : term68) (h2 : term76 n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem202824) (@lem202821 n h1 h2 h3)). Qed.
Lemma lem202827 (n : nat) (h1 : term68) (h2 : term76 n) (h3 : n = term39) : False.
Proof. exact (EQ_MP (@lem202650) (@lem202647 n h1 h2 h3)). Qed.
Lemma lem202828 (n : nat) (h1 : term93 n) (h2 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem202608) (@lem202605 n h1 h2)). Qed.
Lemma lem202829 (n : nat) (h1 : term93 n) (h2 : n = term39) : False.
Proof. exact (EQ_MP (@lem202566) (@lem202563 n h1 h2)). Qed.
Lemma lem202830 (n : nat) (h1 : term68) (h2 : term76 n) (h3 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : n = (NUMERAL 0) => @lem202826 n h1 h2 h3) (fun h4 : False => @lem202309 n h3)). Qed.
Lemma lem202831 (n : nat) (h1 : term68) (h2 : term76 n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem202830 n h1 h2 h3) (@lem202309 n h3)). Qed.
Lemma lem202832 (n : nat) (h1 : term68) (h2 : term76 n) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h3 : n = (NUMERAL 0) => @lem202831 n h1 h2 h3) (fun h3 : False => @lem202305 n h2)). Qed.
Lemma lem202833 (n : nat) (h1 : term68) (h2 : term76 n) : False.
Proof. exact (EQ_MP (@lem202832 n h1 h2) (@lem202305 n h2)). Qed.
Lemma lem202834 (n : nat) (h1 : term68) (h2 : term76 n) (h3 : n = term39) : (n = term39) = False.
Proof. exact (prop_ext (fun h4 : n = term39 => @lem202827 n h1 h2 h3) (fun h4 : False => @lem202301 n h3)). Qed.
Lemma lem202835 (n : nat) (h1 : term68) (h2 : term76 n) (h3 : n = term39) : False.
Proof. exact (EQ_MP (@lem202834 n h1 h2 h3) (@lem202301 n h3)). Qed.
Lemma lem202836 (n : nat) (h1 : term68) (h2 : term76 n) : (n = term39) = False.
Proof. exact (prop_ext (fun h3 : n = term39 => @lem202835 n h1 h2 h3) (fun h3 : False => @lem202299 n h2)). Qed.
Lemma lem202837 (n : nat) (h1 : term68) (h2 : term76 n) : False.
Proof. exact (EQ_MP (@lem202836 n h1 h2) (@lem202299 n h2)). Qed.
Lemma lem202838 (n : nat) (h1 : term93 n) (h2 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h3 : n = (NUMERAL 0) => @lem202828 n h1 h2) (fun h3 : False => @lem202293 n h2)). Qed.
Lemma lem202839 (n : nat) (h1 : term93 n) (h2 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem202838 n h1 h2) (@lem202293 n h2)). Qed.
Lemma lem202840 (n : nat) (h1 : term93 n) (h2 : n = term39) : (n = term39) = False.
Proof. exact (prop_ext (fun h3 : n = term39 => @lem202829 n h1 h2) (fun h3 : False => @lem202285 n h2)). Qed.
Lemma lem202841 (n : nat) (h1 : term93 n) (h2 : n = term39) : False.
Proof. exact (EQ_MP (@lem202840 n h1 h2) (@lem202285 n h2)). Qed.
Lemma lem202842 (n : nat) (h1 : term93 n) (h2 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h3 : n = (NUMERAL 0) => @lem202839 n h1 h2) (fun h3 : False => @lem202227 n h2)). Qed.
Lemma lem202843 (n : nat) (h1 : term93 n) (h2 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem202842 n h1 h2) (@lem202227 n h2)). Qed.
Lemma lem202844 (n : nat) (h1 : term93 n) (h2 : n = term39) : (n = term39) = False.
Proof. exact (prop_ext (fun h3 : n = term39 => @lem202841 n h1 h2) (fun h3 : False => @lem202208 n h2)). Qed.
Lemma lem202845 (n : nat) (h1 : term93 n) (h2 : n = term39) : False.
Proof. exact (EQ_MP (@lem202844 n h1 h2) (@lem202208 n h2)). Qed.
Lemma lem202846 (n : nat) (h1 : term68) (h2 : term76 n) : term68 = False.
Proof. exact (prop_ext (fun h3 : term68 => @lem202833 n h1 h2) (fun h3 : False => @lem202253 h1)). Qed.
Lemma lem202847 (n : nat) (h1 : term68) (h2 : term76 n) : False.
Proof. exact (EQ_MP (@lem202846 n h1 h2) (@lem202253 h1)). Qed.
Lemma lem202848 (n : nat) (h1 : term68) (h2 : term76 n) : term68 = False.
Proof. exact (prop_ext (fun h3 : term68 => @lem202837 n h1 h2) (fun h3 : False => @lem202234 h1)). Qed.
Lemma lem202849 (n : nat) (h1 : term68) (h2 : term76 n) : False.
Proof. exact (EQ_MP (@lem202848 n h1 h2) (@lem202234 h1)). Qed.
Lemma lem202850 (n : nat) (h1 : term93 n) (h2 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h3 : n = (NUMERAL 0) => @lem202843 n h1 h2) (fun h3 : False => @lem202227 n h2)). Qed.
Lemma lem202851 (n : nat) (h1 : term93 n) (h2 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem202850 n h1 h2) (@lem202227 n h2)). Qed.
Lemma lem202852 (n : nat) (h1 : term93 n) (h2 : n = term39) : (n = term39) = False.
Proof. exact (prop_ext (fun h3 : n = term39 => @lem202845 n h1 h2) (fun h3 : False => @lem202208 n h2)). Qed.
Lemma lem202853 (n : nat) (h1 : term93 n) (h2 : n = term39) : False.
Proof. exact (EQ_MP (@lem202852 n h1 h2) (@lem202208 n h2)). Qed.
Lemma lem202854 (n : nat) (h1 : term68) (h2 : term76 n) (h3 : term83 n) : False.
Proof. exact (or_elim (@lem202179 n h3) (fun h0 : n = term39 => @lem202849 n h1 h2) (fun h0 : n = (NUMERAL 0) => @lem202847 n h1 h2)). Qed.
Lemma lem202855 (n : nat) (h1 : term93 n) (h2 : term83 n) : False.
Proof. exact (or_elim (@lem202179 n h2) (fun h0 : n = term39 => @lem202853 n h1 h0) (fun h0 : n = (NUMERAL 0) => @lem202851 n h1 h0)). Qed.
Lemma lem202856 (n : nat) (h1 : term68) (h2 : term83 n) : False.
Proof. exact (or_elim (@lem202178 n h2) (fun h0 : term93 n => @lem202855 n h0 h2) (fun h0 : term76 n => @lem202854 n h1 h0 h2)). Qed.
Lemma lem202857 (n : nat) (h1 : term68) (h2 : term83 n) : (term83 n) = False.
Proof. exact (prop_ext (fun h3 : term83 n => @lem202856 n h1 h2) (fun h3 : False => @lem202177 n h2)). Qed.
Lemma lem202858 (n : nat) (h1 : term68) (h2 : term83 n) : False.
Proof. exact (EQ_MP (@lem202857 n h1 h2) (@lem202177 n h2)). Qed.
Lemma lem202859 (n : nat) (h1 : term68) (h2 : term83 n) : term68 = False.
Proof. exact (prop_ext (fun h3 : term68 => @lem202858 n h1 h2) (fun h3 : False => @lem202109 h1)). Qed.
Lemma lem202860 (n : nat) (h1 : term68) (h2 : term83 n) : False.
Proof. exact (EQ_MP (@lem202859 n h1 h2) (@lem202109 h1)). Qed.
Lemma lem202861 (h1 : term68) (h2 : term61) : False.
Proof. exact (ex_elim (@lem202080 h2) (fun n : nat => fun h0 : term91 n => @lem202860 n h1 h0)). Qed.
Lemma lem202862 (h1 : term68) (h2 : term61) : term68 = False.
Proof. exact (prop_ext (fun h3 : term68 => @lem202861 h1 h2) (fun h3 : False => @lem202093 h1)). Qed.
Lemma lem202863 (h1 : term68) (h2 : term61) : False.
Proof. exact (EQ_MP (@lem202862 h1 h2) (@lem202093 h1)). Qed.
Lemma lem202864 (h1 : term61) : term66.
Proof. exact (fun h0 : term68 => @lem202863 h0 h1). Qed.
Lemma lem202865 : term66 = term67.
Proof. exact (@lem69 term68). Qed.
Lemma lem202866 (h1 : term61) : term67.
Proof. exact (EQ_MP (@lem202865) (@lem202864 h1)). Qed.
Lemma lem202867 : term70.
Proof. exact (fun h0 : term61 => @lem202866 h0). Qed.
Lemma lem202868 : term62.
Proof. exact (EQ_MP (@lem201988) (@lem202867)). Qed.
Lemma lem202870 : term62.
Proof. exact (@lem201910 (@lem202868)). Qed.
Lemma lem202871 (h1 : term61) : term66.
Proof. exact (@lem202870 (@lem201895 h1)). Qed.
Lemma lem202872 (h1 : term61) : False.
Proof. exact (@lem202871 h1 (@lem75570)). Qed.
Lemma lem202873 (h1 : term61) : term61 = False.
Proof. exact (prop_ext (fun h2 : term61 => @lem202872 h1) (fun h2 : False => @lem201895 h1)). Qed.
Lemma lem202874 (h1 : term61) : False.
Proof. exact (EQ_MP (@lem202873 h1) (@lem201895 h1)). Qed.
Lemma lem202875 : term60.
Proof. exact (fun h0 : term61 => @lem202874 h0). Qed.
Lemma lem202876 : term58.
Proof. exact (EQ_MP (@lem201894) (@lem202875)). Qed.
Lemma lem202877 : term57.
Proof. exact (EQ_MP (@lem201890) (@lem202876)). Qed.
Lemma lem202878 (n : nat) : term155 n.
Proof. exact (@lem202877 (term25 n)). Qed.
Lemma lem202879 (n : nat) : (term155 n) = (term156 n).
Proof. exact (eq_refl (term155 n)). Qed.
Lemma lem202880 (n : nat) : term156 n.
Proof. exact (EQ_MP (@lem202879 n) (@lem202878 n)). Qed.
Lemma lem202881 (n : nat) (h1 : term31 n) : (term27 n) = ((term25 n) = term30).
Proof. exact (@lem202880 n (@lem201735 n h1)). Qed.
Lemma lem202882 (n : nat) : (term31 n) = ((term27 n) = ((term25 n) = term30)).
Proof. exact (prop_ext (fun h1 : term31 n => @lem202881 n h1) (fun h1 : (term27 n) = ((term25 n) = term30) => @lem201814 n)). Qed.
Lemma lem202883 (n : nat) : (term27 n) = ((term25 n) = term30).
Proof. exact (EQ_MP (@lem202882 n) (@lem201814 n)). Qed.
Lemma lem202884 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = ((term25 n) = term30).
Proof. exact (EQ_MP (@lem201734 n) (@lem202883 n)). Qed.
Lemma lem202889 : term157.
Proof. exact (fun n : nat => @lem202884 n). Qed.
