Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_LT2_ODD_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_ODD_spec.
Require Import REAL_LE_NEGTOTAL_spec.
Require Import REAL_POW_LE_spec.
Require Import REAL_POW_LT_spec.
Require Import REAL_POW_LT2_spec.
Require Import REAL_POW_NEG_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm12653_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483490_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483523_spec.
Require Import thm1483531_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1845_spec.
Require Import thm516555_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1657727 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Even n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (h1). Qed.
Lemma lem1657728 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Even n)) : (Coq.Arith.PeanoNat.Nat.Even n) = (term0 n).
Proof. exact (SYM (@lem1657727 n h1)). Qed.
Lemma lem1657729 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = (term0 n)) : (Coq.Arith.PeanoNat.Nat.Even n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem1657730 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = (term0 n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (SYM (@lem1657729 n h1)). Qed.
Lemma lem1657731 (n : nat) : ((term0 n) = (Coq.Arith.PeanoNat.Nat.Even n)) = ((Coq.Arith.PeanoNat.Nat.Even n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Even n) => @lem1657728 n h1) (fun h1 : (Coq.Arith.PeanoNat.Nat.Even n) = (term0 n) => @lem1657730 n h1)). Qed.
Lemma lem1657732 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem1657731 n)). Qed.
Lemma lem1657733 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1657734 : term3 = term4.
Proof. exact (MK_COMB (@lem1657733) (@lem1657732)). Qed.
Lemma lem1657735 : term4.
Proof. exact (EQ_MP (@lem1657734) (@lem124808)). Qed.
Lemma lem1657736 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1657737 (n : nat) (h1 : term5) : term6 n.
Proof. exact (@lem1657736 h1 n). Qed.
Lemma lem1657738 (n : nat) : (term6 n) = (term7 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem1657739 (n : nat) (h1 : term5) : term7 n.
Proof. exact (EQ_MP (@lem1657738 n) (@lem1657737 n h1)). Qed.
Lemma lem1657740 (n : nat) (x : real) (h1 : term5) : term8 n x.
Proof. exact (@lem1657739 n h1 x). Qed.
Lemma lem1657741 (x : real) (n : nat) : (term8 n x) = (term9 x n).
Proof. exact (eq_refl (term8 n x)). Qed.
Lemma lem1657742 (x : real) (n : nat) (h1 : term5) : term9 x n.
Proof. exact (EQ_MP (@lem1657741 x n) (@lem1657740 n x h1)). Qed.
Lemma lem1657743 (x : real) (n : nat) (y : real) (h1 : term5) : term10 x n y.
Proof. exact (@lem1657742 x n h1 y). Qed.
Lemma lem1657744 (x : real) (y : real) (n : nat) : (term10 x n y) = (term11 x y n).
Proof. exact (eq_refl (term10 x n y)). Qed.
Lemma lem1657745 (x : real) (y : real) (n : nat) (h1 : term5) : term11 x y n.
Proof. exact (EQ_MP (@lem1657744 x y n) (@lem1657743 x n y h1)). Qed.
Lemma lem1657746 (n : nat) (x : real) (y : real) (h1 : term12 n x y) : term12 n x y.
Proof. exact (h1). Qed.
Lemma lem1657747 (n : nat) (x : real) (y : real) (h1 : term5) (h2 : term12 n x y) : term13 x y n.
Proof. exact (@lem1657745 x y n h1 (@lem1657746 n x y h2)). Qed.
Lemma lem1657748 (n : nat) (x : real) (y : real) (h1 : term12 n x y) : term14 x y n.
Proof. exact (fun h0 : term5 => @lem1657747 n x y h0 h1). Qed.
Lemma lem1657749 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1657750 (n : nat) (x : real) (y : real) (h1 : term5) (h2 : term12 n x y) : term13 x y n.
Proof. exact (@lem1657748 n x y h2 (@lem1657749 h1)). Qed.
Lemma lem1657751 (x : real) (y : real) (n : nat) (h1 : term5) : term11 x y n.
Proof. exact (fun h0 : term12 n x y => @lem1657750 n x y h1 h0). Qed.
Lemma lem1657752 (x : real) (y : real) (h1 : term5) : term15 x y.
Proof. exact (fun n : nat => @lem1657751 x y n h1). Qed.
Lemma lem1657753 (x : real) (h1 : term5) : term16 x.
Proof. exact (fun y : real => @lem1657752 x y h1). Qed.
Lemma lem1657754 (h1 : term5) : term17.
Proof. exact (fun x : real => @lem1657753 x h1). Qed.
Lemma lem1657755 : term18.
Proof. exact (fun h0 : term5 => @lem1657754 h0). Qed.
Lemma lem1657756 : term17.
Proof. exact (@lem1657755 (@lem1638321)). Qed.
Lemma lem1657757 (x : real) : term19 x.
Proof. exact (@lem1657756 x). Qed.
Lemma lem1657758 (x : real) : (term19 x) = (term16 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1657759 (x : real) : term16 x.
Proof. exact (EQ_MP (@lem1657758 x) (@lem1657757 x)). Qed.
Lemma lem1657760 (x : real) (y : real) : term20 x y.
Proof. exact (@lem1657759 x y). Qed.
Lemma lem1657761 (x : real) (y : real) : (term20 x y) = (term15 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1657762 (x : real) (y : real) : term15 x y.
Proof. exact (EQ_MP (@lem1657761 x y) (@lem1657760 x y)). Qed.
Lemma lem1657763 (x : real) (y : real) (n : nat) : term21 x y n.
Proof. exact (@lem1657762 x y n). Qed.
Lemma lem1657764 (x : real) (y : real) (n : nat) : (term21 x y n) = (term11 x y n).
Proof. exact (eq_refl (term21 x y n)). Qed.
Lemma lem1657767 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Even n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (h1). Qed.
Lemma lem1657768 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Even n)) : (Coq.Arith.PeanoNat.Nat.Even n) = (term0 n).
Proof. exact (SYM (@lem1657767 n h1)). Qed.
Lemma lem1657769 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = (term0 n)) : (Coq.Arith.PeanoNat.Nat.Even n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem1657770 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = (term0 n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (SYM (@lem1657769 n h1)). Qed.
Lemma lem1657771 (n : nat) : ((term0 n) = (Coq.Arith.PeanoNat.Nat.Even n)) = ((Coq.Arith.PeanoNat.Nat.Even n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Even n) => @lem1657768 n h1) (fun h1 : (Coq.Arith.PeanoNat.Nat.Even n) = (term0 n) => @lem1657770 n h1)). Qed.
Lemma lem1657772 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem1657771 n)). Qed.
Lemma lem1657773 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1657774 : term3 = term4.
Proof. exact (MK_COMB (@lem1657773) (@lem1657772)). Qed.
Lemma lem1657775 : term4.
Proof. exact (EQ_MP (@lem1657774) (@lem124808)). Qed.
Lemma lem1657798 (x : real) : (term22 x) = (term23 x).
Proof. exact (@lem17160 (term24 x) (term25 x)). Qed.
Lemma lem1657799 (x : real) : (term26 x) = (term27 x).
Proof. exact (@lem1483533 term28 x). Qed.
Lemma lem1657805 (x : real) : (term29 x) = (term30 x).
Proof. exact (@lem1483519 term28 x). Qed.
Lemma lem1657810 (x : real) : (term30 x) = (term31 x).
Proof. exact (@lem1483448 (term31 x)). Qed.
Lemma lem1657812 (x : real) : (term29 x) = (term31 x).
Proof. exact (TRANS (@lem1657805 x) (@lem1657810 x)). Qed.
Lemma lem1657813 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1657814 (x : real) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem1657813) (@lem1657812 x)). Qed.
Lemma lem1657815 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1657816 (x : real) : (term27 x) = (term34 x).
Proof. exact (MK_COMB (@lem1657814 x) (@lem1657815)). Qed.
Lemma lem1657817 (x : real) : (term26 x) = (term34 x).
Proof. exact (TRANS (@lem1657799 x) (@lem1657816 x)). Qed.
Lemma lem1657818 (x : real) : (term35 x) = (term36 x).
Proof. exact (@lem1483531 term28 (real_neg x)). Qed.
Lemma lem1657825 (x : real) : (real_neg x) = (term31 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1657828 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1657829 (x : real) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem1657828) (@lem1657825 x)). Qed.
Lemma lem1657830 (x : real) : (term39 x) = (term40 x).
Proof. exact (@lem1483519 term28 (term31 x)). Qed.
Lemma lem1657831 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1483476 term43 term43 x). Qed.
Lemma lem1657833 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1657834 : term46 = term47.
Proof. exact (@lem1657833 term48 term48). Qed.
Lemma lem1657835 : (term49 = (BIT1 0)) = (term50 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1657836 : term50 = term48.
Proof. exact (EQ_MP (@lem1657835) (@lem940073)). Qed.
Lemma lem1657837 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1657838 : term47 = term51.
Proof. exact (MK_COMB (@lem1657837) (@lem1657836)). Qed.
Lemma lem1657839 : term46 = term51.
Proof. exact (TRANS (@lem1657834) (@lem1657838)). Qed.
Lemma lem1657840 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1657841 : term52 = term53.
Proof. exact (MK_COMB (@lem1657840) (@lem1657839)). Qed.
Lemma lem1657842 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1657843 (x : real) : (term42 x) = (term54 x).
Proof. exact (MK_COMB (@lem1657841) (@lem1657842 x)). Qed.
Lemma lem1657844 (x : real) : (term41 x) = (term54 x).
Proof. exact (TRANS (@lem1657831 x) (@lem1657843 x)). Qed.
Lemma lem1657845 (x : real) : (term54 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1657846 (x : real) : (term41 x) = x.
Proof. exact (TRANS (@lem1657844 x) (@lem1657845 x)). Qed.
Lemma lem1657847 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem1657848 (x : real) : (term40 x) = (term56 x).
Proof. exact (MK_COMB (@lem1657847) (@lem1657846 x)). Qed.
Lemma lem1657849 (x : real) : (term56 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1657850 (x : real) : (term40 x) = x.
Proof. exact (TRANS (@lem1657848 x) (@lem1657849 x)). Qed.
Lemma lem1657851 (x : real) : (term39 x) = x.
Proof. exact (TRANS (@lem1657830 x) (@lem1657850 x)). Qed.
Lemma lem1657852 (x : real) : (term38 x) = x.
Proof. exact (TRANS (@lem1657829 x) (@lem1657851 x)). Qed.
Lemma lem1657853 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1657854 (x : real) : (term57 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1657853) (@lem1657852 x)). Qed.
Lemma lem1657855 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1657856 (x : real) : (term36 x) = (term58 x).
Proof. exact (MK_COMB (@lem1657854 x) (@lem1657855)). Qed.
Lemma lem1657857 (x : real) : (term35 x) = (term58 x).
Proof. exact (TRANS (@lem1657818 x) (@lem1657856 x)). Qed.
Lemma lem1657858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1657859 (x : real) : (term59 x) = (term60 x).
Proof. exact (MK_COMB (@lem1657858) (@lem1657817 x)). Qed.
Lemma lem1657860 (x : real) : (term23 x) = (term61 x).
Proof. exact (MK_COMB (@lem1657859 x) (@lem1657857 x)). Qed.
Lemma lem1657875 (x : real) : (term22 x) = (term61 x).
Proof. exact (TRANS (@lem1657798 x) (@lem1657860 x)). Qed.
Lemma lem1657879 (x : real) (h1 : term61 x) : term61 x.
Proof. exact (h1). Qed.
Lemma lem1657880 (x : real) (h1 : term61 x) : term58 x.
Proof. exact (proj2 (@lem1657879 x h1)). Qed.
Lemma lem1657881 (x : real) (h1 : term61 x) : term34 x.
Proof. exact (proj1 (@lem1657879 x h1)). Qed.
Lemma lem1657883 (n : nat) (m : nat) : (term62 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1657884 : term63 = term64.
Proof. exact (@lem1657883 (NUMERAL 0) term48). Qed.
Lemma lem1657885 : term65 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1657886 (h1 : term65 = (BIT1 0)) : term64 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1657887 : (term65 = (BIT1 0)) = (term64 = True).
Proof. exact (prop_ext (fun h1 : term65 = (BIT1 0) => @lem1657886 h1) (fun h1 : term64 = True => @lem1657885)). Qed.
Lemma lem1657888 : term64 = True.
Proof. exact (EQ_MP (@lem1657887) (@lem1657885)). Qed.
Lemma lem1657889 : term63 = True.
Proof. exact (TRANS (@lem1657884) (@lem1657888)). Qed.
Lemma lem1657890 : True = term63.
Proof. exact (SYM (@lem1657889)). Qed.
Lemma lem1657891 : term63.
Proof. exact (EQ_MP (@lem1657890) (@lem0)). Qed.
Lemma lem1657892 (x : real) (h1 : term61 x) : term66 x.
Proof. exact (conj (@lem1657891) (@lem1657880 x h1)). Qed.
Lemma lem1657894 (x : real) (y : real) : term67 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1657895 (x : real) : term68 x.
Proof. exact (@lem1657894 term51 x). Qed.
Lemma lem1657896 (x : real) (h1 : term61 x) : term69 x.
Proof. exact (@lem1657895 x (@lem1657892 x h1)). Qed.
Lemma lem1657897 (x : real) : (term54 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1657898 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1657899 (x : real) : (term70 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1657898) (@lem1657897 x)). Qed.
Lemma lem1657900 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1657901 (x : real) : (term69 x) = (term58 x).
Proof. exact (MK_COMB (@lem1657899 x) (@lem1657900)). Qed.
Lemma lem1657902 (x : real) (h1 : term61 x) : term58 x.
Proof. exact (EQ_MP (@lem1657901 x) (@lem1657896 x h1)). Qed.
Lemma lem1657904 (n : nat) (m : nat) : (term62 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1657905 : term63 = term64.
Proof. exact (@lem1657904 (NUMERAL 0) term48). Qed.
Lemma lem1657906 : term65 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1657907 (h1 : term65 = (BIT1 0)) : term64 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1657908 : (term65 = (BIT1 0)) = (term64 = True).
Proof. exact (prop_ext (fun h1 : term65 = (BIT1 0) => @lem1657907 h1) (fun h1 : term64 = True => @lem1657906)). Qed.
Lemma lem1657909 : term64 = True.
Proof. exact (EQ_MP (@lem1657908) (@lem1657906)). Qed.
Lemma lem1657910 : term63 = True.
Proof. exact (TRANS (@lem1657905) (@lem1657909)). Qed.
Lemma lem1657911 : True = term63.
Proof. exact (SYM (@lem1657910)). Qed.
Lemma lem1657912 : term63.
Proof. exact (EQ_MP (@lem1657911) (@lem0)). Qed.
Lemma lem1657913 (x : real) (h1 : term61 x) : term71 x.
Proof. exact (conj (@lem1657912) (@lem1657881 x h1)). Qed.
Lemma lem1657915 (x : real) (y : real) : term72 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1657916 (x : real) : term73 x.
Proof. exact (@lem1657915 term51 (term31 x)). Qed.
Lemma lem1657917 (x : real) (h1 : term61 x) : term74 x.
Proof. exact (@lem1657916 x (@lem1657913 x h1)). Qed.
Lemma lem1657918 (x : real) : (term75 x) = (term31 x).
Proof. exact (@lem1483460 (term31 x)). Qed.
Lemma lem1657919 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1657920 (x : real) : (term76 x) = (term33 x).
Proof. exact (MK_COMB (@lem1657919) (@lem1657918 x)). Qed.
Lemma lem1657921 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1657922 (x : real) : (term74 x) = (term34 x).
Proof. exact (MK_COMB (@lem1657920 x) (@lem1657921)). Qed.
Lemma lem1657923 (x : real) (h1 : term61 x) : term34 x.
Proof. exact (EQ_MP (@lem1657922 x) (@lem1657917 x h1)). Qed.
Lemma lem1657924 (x : real) (h1 : term61 x) : term61 x.
Proof. exact (conj (@lem1657923 x h1) (@lem1657902 x h1)). Qed.
Lemma lem1657926 (x : real) (y : real) : term77 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1657927 (x : real) : term78 x.
Proof. exact (@lem1657926 (term31 x) x). Qed.
Lemma lem1657928 (x : real) (h1 : term61 x) : term79 x.
Proof. exact (@lem1657927 x (@lem1657924 x h1)). Qed.
Lemma lem1657929 (x : real) : (term80 x) = (term81 x).
Proof. exact (@lem1483440 term43 x). Qed.
Lemma lem1657931 (m : nat) : (term82 m) = term28.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1657932 : term83 = term28.
Proof. exact (@lem1657931 term48). Qed.
Lemma lem1657933 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1657934 : term84 = term85.
Proof. exact (MK_COMB (@lem1657933) (@lem1657932)). Qed.
Lemma lem1657935 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1657936 (x : real) : (term81 x) = (term86 x).
Proof. exact (MK_COMB (@lem1657934) (@lem1657935 x)). Qed.
Lemma lem1657937 (x : real) : (term80 x) = (term86 x).
Proof. exact (TRANS (@lem1657929 x) (@lem1657936 x)). Qed.
Lemma lem1657938 (x : real) : (term86 x) = term28.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1657939 (x : real) : (term80 x) = term28.
Proof. exact (TRANS (@lem1657937 x) (@lem1657938 x)). Qed.
Lemma lem1657940 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1657941 (x : real) : (term87 x) = term88.
Proof. exact (MK_COMB (@lem1657940) (@lem1657939 x)). Qed.
Lemma lem1657942 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1657943 (x : real) : (term79 x) = term89.
Proof. exact (MK_COMB (@lem1657941 x) (@lem1657942)). Qed.
Lemma lem1657944 (x : real) (h1 : term61 x) : term89.
Proof. exact (EQ_MP (@lem1657943 x) (@lem1657928 x h1)). Qed.
Lemma lem1657946 (n : nat) (m : nat) : (term62 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1657947 : term89 = term90.
Proof. exact (@lem1657946 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1657948 : term90 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1657949 : term89 = False.
Proof. exact (TRANS (@lem1657947) (@lem1657948)). Qed.
Lemma lem1657950 (x : real) (h1 : term61 x) : False.
Proof. exact (EQ_MP (@lem1657949) (@lem1657944 x h1)). Qed.
Lemma lem1657952 (x : real) (h1 : term61 x) : term61 x.
Proof. exact (h1). Qed.
Lemma lem1657953 (x : real) (h1 : term61 x) : (term61 x) = False.
Proof. exact (prop_ext (fun h2 : term61 x => @lem1657950 x h1) (fun h2 : False => @lem1657952 x h1)). Qed.
Lemma lem1657954 (x : real) (h1 : term61 x) : False.
Proof. exact (EQ_MP (@lem1657953 x h1) (@lem1657952 x h1)). Qed.
Lemma lem1657955 (x : real) (h1 : term22 x) : term22 x.
Proof. exact (h1). Qed.
Lemma lem1657956 (x : real) (h1 : term22 x) : term61 x.
Proof. exact (EQ_MP (@lem1657875 x) (@lem1657955 x h1)). Qed.
Lemma lem1657957 (x : real) (h1 : term22 x) : (term61 x) = False.
Proof. exact (prop_ext (fun h2 : term61 x => @lem1657954 x h2) (fun h2 : False => @lem1657956 x h1)). Qed.
Lemma lem1657958 (x : real) (h1 : term22 x) : False.
Proof. exact (EQ_MP (@lem1657957 x h1) (@lem1657956 x h1)). Qed.
Lemma lem1657959 (x : real) : term91 x.
Proof. exact (fun h0 : term22 x => @lem1657958 x h0). Qed.
Lemma lem1657960 (x : real) : term92 x.
Proof. exact (@lem1386578 (term93 x)). Qed.
Lemma lem1657961 (x : real) : term93 x.
Proof. exact (@lem1657960 x (@lem1657959 x)). Qed.
Lemma lem1657962 (x : real) (h1 : term24 x) : term24 x.
Proof. exact (h1). Qed.
Lemma lem1657963 (x : real) (h1 : term25 x) : term25 x.
Proof. exact (h1). Qed.
Lemma lem1657964 (y : real) : term94 y.
Proof. exact (@lem1382820 y). Qed.
Lemma lem1657965 (y : real) : (term94 y) = (term95 y).
Proof. exact (eq_refl (term94 y)). Qed.
Lemma lem1657966 (y : real) : term95 y.
Proof. exact (EQ_MP (@lem1657965 y) (@lem1657964 y)). Qed.
Lemma lem1657967 (y : real) (h1 : term24 y) : term24 y.
Proof. exact (h1). Qed.
Lemma lem1657968 (y : real) (h1 : term96 y) : term96 y.
Proof. exact (h1). Qed.
Lemma lem1657969 (n : nat) : term97 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem1657970 (n : nat) : (term97 n) = (term98 n).
Proof. exact (eq_refl (term97 n)). Qed.
Lemma lem1657971 (n : nat) : term98 n.
Proof. exact (EQ_MP (@lem1657970 n) (@lem1657969 n)). Qed.
Lemma lem1657973 (n : nat) (h1 : term99 n) : term99 n.
Proof. exact (h1). Qed.
Lemma lem1658368 : term100.
Proof. exact (EQ_MP (@lem516555) (@lem0)). Qed.
Lemma lem1658369 : term101.
Proof. exact (proj2 (@lem1658368)). Qed.
Lemma lem1658380 : term102.
Proof. exact (proj1 (@lem1658368)). Qed.
Lemma lem1658381 (n : nat) : term103 n.
Proof. exact (@lem1658380 n). Qed.
Lemma lem1658382 (n : nat) : (term103 n) = ((term104 n) = (Coq.Arith.PeanoNat.Nat.Odd n)).
Proof. exact (eq_refl (term103 n)). Qed.
Lemma lem1658623 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1658624 : Coq.Arith.PeanoNat.Nat.Odd = Coq.Arith.PeanoNat.Nat.Odd.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Odd). Qed.
Lemma lem1658625 (n : nat) (h1 : n = (NUMERAL 0)) : (Coq.Arith.PeanoNat.Nat.Odd n) = term105.
Proof. exact (MK_COMB (@lem1658624) (@lem1658623 n h1)). Qed.
Lemma lem1658627 (n : nat) : (term104 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (EQ_MP (@lem1658382 n) (@lem1658381 n)). Qed.
Lemma lem1658628 : term105 = (Coq.Arith.PeanoNat.Nat.Odd 0).
Proof. exact (@lem1658627 0). Qed.
Lemma lem1658630 : (Coq.Arith.PeanoNat.Nat.Odd 0) = False.
Proof. exact (proj1 (@lem1658369)). Qed.
Lemma lem1658631 : term105 = False.
Proof. exact (TRANS (@lem1658628) (@lem1658630)). Qed.
Lemma lem1658632 (n : nat) (h1 : n = (NUMERAL 0)) : (Coq.Arith.PeanoNat.Nat.Odd n) = False.
Proof. exact (TRANS (@lem1658625 n h1) (@lem1658631)). Qed.
Lemma lem1658633 (x : real) (y : real) : (term106 x y) = (term106 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1658634 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term107 x y n) = (term108 x y).
Proof. exact (MK_COMB (@lem1658633 x y) (@lem1658632 n h1)). Qed.
Lemma lem1658636 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1658637 (x : real) (y : real) : (term108 x y) = False.
Proof. exact (@lem1658636 (real_lt x y)). Qed.
Lemma lem1658638 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term107 x y n) = False.
Proof. exact (TRANS (@lem1658634 x y n h1) (@lem1658637 x y)). Qed.
Lemma lem1658639 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1658640 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term109 x y n) = (imp False).
Proof. exact (MK_COMB (@lem1658639) (@lem1658638 x y n h1)). Qed.
Lemma lem1658642 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1658643 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem1658644 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (real_pow x n) = (term110 x).
Proof. exact (MK_COMB (@lem1658643 x) (@lem1658642 n h1)). Qed.
Lemma lem1658645 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1658646 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term111 x n) = (term112 x).
Proof. exact (MK_COMB (@lem1658645) (@lem1658644 x n h1)). Qed.
Lemma lem1658648 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1658649 (y : real) : (real_pow y) = (real_pow y).
Proof. exact (eq_refl (real_pow y)). Qed.
Lemma lem1658650 (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (real_pow y n) = (term110 y).
Proof. exact (MK_COMB (@lem1658649 y) (@lem1658648 n h1)). Qed.
Lemma lem1658651 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term13 x y n) = (term113 x y).
Proof. exact (MK_COMB (@lem1658646 x n h1) (@lem1658650 y n h1)). Qed.
Lemma lem1658652 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term114 x y n) = (term115 x y).
Proof. exact (MK_COMB (@lem1658640 x y n h1) (@lem1658651 x y n h1)). Qed.
Lemma lem1658654 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1658655 (x : real) (y : real) : (term115 x y) = True.
Proof. exact (@lem1658654 (term113 x y)). Qed.
Lemma lem1658656 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term114 x y n) = True.
Proof. exact (TRANS (@lem1658652 x y n h1) (@lem1658655 x y)). Qed.
Lemma lem1658657 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : True = (term114 x y n).
Proof. exact (SYM (@lem1658656 x y n h1)). Qed.
Lemma lem1658658 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : term114 x y n.
Proof. exact (EQ_MP (@lem1658657 x y n h1) (@lem0)). Qed.
Lemma lem1659322 (x : real) (y : real) (n : nat) (h1 : term107 x y n) : term107 x y n.
Proof. exact (h1). Qed.
Lemma lem1659323 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem1659324 (x : real) (y : real) (h1 : real_lt x y) : real_lt x y.
Proof. exact (h1). Qed.
Lemma lem1659325 (n : nat) : term6 n.
Proof. exact (@lem1638321 n). Qed.
Lemma lem1659326 (n : nat) : (term6 n) = (term7 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem1659327 (n : nat) : term7 n.
Proof. exact (EQ_MP (@lem1659326 n) (@lem1659325 n)). Qed.
Lemma lem1659328 (n : nat) (x : real) : term8 n x.
Proof. exact (@lem1659327 n x). Qed.
Lemma lem1659329 (x : real) (n : nat) : (term8 n x) = (term9 x n).
Proof. exact (eq_refl (term8 n x)). Qed.
Lemma lem1659330 (x : real) (n : nat) : term9 x n.
Proof. exact (EQ_MP (@lem1659329 x n) (@lem1659328 n x)). Qed.
Lemma lem1659331 (x : real) (n : nat) (y : real) : term10 x n y.
Proof. exact (@lem1659330 x n y). Qed.
Lemma lem1659332 (x : real) (y : real) (n : nat) : (term10 x n y) = (term11 x y n).
Proof. exact (eq_refl (term10 x n y)). Qed.
Lemma lem1659333 (x : real) (y : real) (n : nat) : term11 x y n.
Proof. exact (EQ_MP (@lem1659332 x y n) (@lem1659331 x n y)). Qed.
Lemma lem1659334 (n : nat) (x : real) (y : real) (h1 : term12 n x y) : term12 n x y.
Proof. exact (h1). Qed.
Lemma lem1659335 (n : nat) (x : real) (y : real) (h1 : term12 n x y) : term13 x y n.
Proof. exact (@lem1659333 x y n (@lem1659334 n x y h1)). Qed.
Lemma lem1659336 (x : real) (y : real) (n : nat) : (term13 x y n) = ((term13 x y n) = True).
Proof. exact (@lem7 (term13 x y n)). Qed.
Lemma lem1659337 (n : nat) (x : real) (y : real) (h1 : term12 n x y) : (term13 x y n) = True.
Proof. exact (EQ_MP (@lem1659336 x y n) (@lem1659335 n x y h1)). Qed.
Lemma lem1659343 (n : nat) : term116 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem1659356 (x : real) (y : real) : (real_lt x y) = ((real_lt x y) = True).
Proof. exact (@lem7 (real_lt x y)). Qed.
Lemma lem1659362 (x : real) : (term24 x) = ((term24 x) = True).
Proof. exact (@lem7 (term24 x)). Qed.
Lemma lem1659365 (x : real) (y : real) (n : nat) : term117 x y n.
Proof. exact (fun h0 : term12 n x y => @lem1659337 n x y h0). Qed.
Lemma lem1659369 (n : nat) (h1 : term99 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1659343 n (@lem1657973 n h1)). Qed.
Lemma lem1659370 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1659371 (n : nat) (h1 : term99 n) : (term99 n) = (~ False).
Proof. exact (MK_COMB (@lem1659370) (@lem1659369 n h1)). Qed.
Lemma lem1659373 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1659374 (n : nat) (h1 : term99 n) : (term99 n) = True.
Proof. exact (TRANS (@lem1659371 n h1) (@lem1659373)). Qed.
Lemma lem1659375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1659376 (n : nat) (h1 : term99 n) : (term118 n) = (and True).
Proof. exact (MK_COMB (@lem1659375) (@lem1659374 n h1)). Qed.
Lemma lem1659380 (x : real) (h1 : term24 x) : (term24 x) = True.
Proof. exact (EQ_MP (@lem1659362 x) (@lem1657962 x h1)). Qed.
Lemma lem1659381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1659382 (x : real) (h1 : term24 x) : (term119 x) = (and True).
Proof. exact (MK_COMB (@lem1659381) (@lem1659380 x h1)). Qed.
Lemma lem1659384 (x : real) (y : real) (h1 : real_lt x y) : (real_lt x y) = True.
Proof. exact (EQ_MP (@lem1659356 x y) (@lem1659324 x y h1)). Qed.
Lemma lem1659385 (x : real) (y : real) (h1 : term24 x) (h2 : real_lt x y) : (term120 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1659382 x h1) (@lem1659384 x y h2)). Qed.
Lemma lem1659387 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1659388 : (True /\ True) = True.
Proof. exact (@lem1659387 True). Qed.
Lemma lem1659389 (x : real) (y : real) (h1 : term24 x) (h2 : real_lt x y) : (term120 x y) = True.
Proof. exact (TRANS (@lem1659385 x y h1 h2) (@lem1659388)). Qed.
Lemma lem1659390 (n : nat) (x : real) (y : real) (h1 : term99 n) (h2 : term24 x) (h3 : real_lt x y) : (term12 n x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1659376 n h1) (@lem1659389 x y h2 h3)). Qed.
Lemma lem1659392 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1659393 : (True /\ True) = True.
Proof. exact (@lem1659392 True). Qed.
Lemma lem1659394 (n : nat) (x : real) (y : real) (h1 : term99 n) (h2 : term24 x) (h3 : real_lt x y) : (term12 n x y) = True.
Proof. exact (TRANS (@lem1659390 n x y h1 h2 h3) (@lem1659393)). Qed.
Lemma lem1659395 (n : nat) (x : real) (y : real) (h1 : term99 n) (h2 : term24 x) (h3 : real_lt x y) : True = (term12 n x y).
Proof. exact (SYM (@lem1659394 n x y h1 h2 h3)). Qed.
Lemma lem1659396 (n : nat) (x : real) (y : real) (h1 : term99 n) (h2 : term24 x) (h3 : real_lt x y) : term12 n x y.
Proof. exact (EQ_MP (@lem1659395 n x y h1 h2 h3) (@lem0)). Qed.
Lemma lem1659397 (n : nat) (x : real) (y : real) (h1 : term99 n) (h2 : term24 x) (h3 : real_lt x y) : (term13 x y n) = True.
Proof. exact (@lem1659365 x y n (@lem1659396 n x y h1 h2 h3)). Qed.
Lemma lem1659398 (n : nat) (x : real) (y : real) (h1 : term99 n) (h2 : term24 x) (h3 : real_lt x y) : True = (term13 x y n).
Proof. exact (SYM (@lem1659397 n x y h1 h2 h3)). Qed.
Lemma lem1659399 (n : nat) (x : real) (y : real) (h1 : term99 n) (h2 : term24 x) (h3 : real_lt x y) : term13 x y n.
Proof. exact (EQ_MP (@lem1659398 n x y h1 h2 h3) (@lem0)). Qed.
Lemma lem1659470 (x : real) (y : real) (n : nat) (h1 : term121 x y n) : term121 x y n.
Proof. exact (h1). Qed.
Lemma lem1659471 (x : real) : term122 x.
Proof. exact (@lem1582551 x). Qed.
Lemma lem1659472 (x : real) : (term122 x) = (term123 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1659473 (x : real) : term123 x.
Proof. exact (EQ_MP (@lem1659472 x) (@lem1659471 x)). Qed.
Lemma lem1659474 (x : real) (n : nat) : term124 x n.
Proof. exact (@lem1659473 x n). Qed.
Lemma lem1659475 (x : real) (n : nat) : (term124 x n) = (term125 x n).
Proof. exact (eq_refl (term124 x n)). Qed.
Lemma lem1659476 (x : real) (n : nat) : term125 x n.
Proof. exact (EQ_MP (@lem1659475 x n) (@lem1659474 x n)). Qed.
Lemma lem1659477 (x : real) (h1 : term126 x) : term126 x.
Proof. exact (h1). Qed.
Lemma lem1659478 (n : nat) (x : real) (h1 : term126 x) : term127 x n.
Proof. exact (@lem1659476 x n (@lem1659477 x h1)). Qed.
Lemma lem1659479 (x : real) (n : nat) : (term127 x n) = ((term127 x n) = True).
Proof. exact (@lem7 (term127 x n)). Qed.
Lemma lem1659480 (n : nat) (x : real) (h1 : term126 x) : (term127 x n) = True.
Proof. exact (EQ_MP (@lem1659479 x n) (@lem1659478 n x h1)). Qed.
Lemma lem1659486 (x : real) : term128 x.
Proof. exact (@lem1582434 x). Qed.
Lemma lem1659487 (x : real) : (term128 x) = (term129 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1659488 (x : real) : term129 x.
Proof. exact (EQ_MP (@lem1659487 x) (@lem1659486 x)). Qed.
Lemma lem1659489 (x : real) (n : nat) : term130 x n.
Proof. exact (@lem1659488 x n). Qed.
Lemma lem1659490 (x : real) (n : nat) : (term130 x n) = (term131 x n).
Proof. exact (eq_refl (term130 x n)). Qed.
Lemma lem1659491 (x : real) (n : nat) : term131 x n.
Proof. exact (EQ_MP (@lem1659490 x n) (@lem1659489 x n)). Qed.
Lemma lem1659492 (x : real) (h1 : term24 x) : term24 x.
Proof. exact (h1). Qed.
Lemma lem1659493 (n : nat) (x : real) (h1 : term24 x) : term132 x n.
Proof. exact (@lem1659491 x n (@lem1659492 x h1)). Qed.
Lemma lem1659494 (x : real) (n : nat) : (term132 x n) = ((term132 x n) = True).
Proof. exact (@lem7 (term132 x n)). Qed.
Lemma lem1659495 (n : nat) (x : real) (h1 : term24 x) : (term132 x n) = True.
Proof. exact (EQ_MP (@lem1659494 x n) (@lem1659493 n x h1)). Qed.
Lemma lem1659518 (y : real) : (term24 y) = ((term24 y) = True).
Proof. exact (@lem7 (term24 y)). Qed.
Lemma lem1659520 (x : real) : (term25 x) = ((term25 x) = True).
Proof. exact (@lem7 (term25 x)). Qed.
Lemma lem1659525 (x : real) (n : nat) : term133 x n.
Proof. exact (fun h0 : term126 x => @lem1659480 n x h0). Qed.
Lemma lem1659526 (x : real) (n : nat) : term134 x n.
Proof. exact (@lem1659525 (real_neg x) n). Qed.
Lemma lem1659528 (x : real) (h1 : term25 x) : (term25 x) = True.
Proof. exact (EQ_MP (@lem1659520 x) (@lem1657963 x h1)). Qed.
Lemma lem1659529 (x : real) (h1 : term25 x) : True = (term25 x).
Proof. exact (SYM (@lem1659528 x h1)). Qed.
Lemma lem1659530 (x : real) (h1 : term25 x) : term25 x.
Proof. exact (EQ_MP (@lem1659529 x h1) (@lem0)). Qed.
Lemma lem1659531 (n : nat) (x : real) (h1 : term25 x) : (term135 x n) = True.
Proof. exact (@lem1659526 x n (@lem1659530 x h1)). Qed.
Lemma lem1659532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1659533 (n : nat) (x : real) (h1 : term25 x) : (term136 x n) = (and True).
Proof. exact (MK_COMB (@lem1659532) (@lem1659531 n x h1)). Qed.
Lemma lem1659535 (x : real) (n : nat) : term137 x n.
Proof. exact (fun h0 : term24 x => @lem1659495 n x h0). Qed.
Lemma lem1659536 (y : real) (n : nat) : term137 y n.
Proof. exact (@lem1659535 y n). Qed.
Lemma lem1659538 (y : real) (h1 : term24 y) : (term24 y) = True.
Proof. exact (EQ_MP (@lem1659518 y) (@lem1657967 y h1)). Qed.
Lemma lem1659539 (y : real) (h1 : term24 y) : True = (term24 y).
Proof. exact (SYM (@lem1659538 y h1)). Qed.
Lemma lem1659540 (y : real) (h1 : term24 y) : term24 y.
Proof. exact (EQ_MP (@lem1659539 y h1) (@lem0)). Qed.
Lemma lem1659541 (n : nat) (y : real) (h1 : term24 y) : (term132 y n) = True.
Proof. exact (@lem1659536 y n (@lem1659540 y h1)). Qed.
Lemma lem1659542 (n : nat) (y : real) (x : real) (h1 : term24 y) (h2 : term25 x) : (term121 x y n) = (True /\ True).
Proof. exact (MK_COMB (@lem1659533 n x h2) (@lem1659541 n y h1)). Qed.
Lemma lem1659544 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1659545 : (True /\ True) = True.
Proof. exact (@lem1659544 True). Qed.
Lemma lem1659546 (n : nat) (y : real) (x : real) (h1 : term24 y) (h2 : term25 x) : (term121 x y n) = True.
Proof. exact (TRANS (@lem1659542 n y x h1 h2) (@lem1659545)). Qed.
Lemma lem1659547 (n : nat) (y : real) (x : real) (h1 : term24 y) (h2 : term25 x) : True = (term121 x y n).
Proof. exact (SYM (@lem1659546 n y x h1 h2)). Qed.
Lemma lem1659548 (n : nat) (y : real) (x : real) (h1 : term24 y) (h2 : term25 x) : term121 x y n.
Proof. exact (EQ_MP (@lem1659547 n y x h1 h2) (@lem0)). Qed.
Lemma lem1659549 (n : nat) : term138 n.
Proof. exact (@lem1657775 n). Qed.
Lemma lem1659550 (n : nat) : (term138 n) = ((Coq.Arith.PeanoNat.Nat.Even n) = (term0 n)).
Proof. exact (eq_refl (term138 n)). Qed.
Lemma lem1659552 (x : real) : term139 x.
Proof. exact (@lem1362863 x). Qed.
Lemma lem1659553 (x : real) : (term139 x) = (term140 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1659554 (x : real) : term140 x.
Proof. exact (EQ_MP (@lem1659553 x) (@lem1659552 x)). Qed.
Lemma lem1659555 (x : real) (n : nat) : term141 x n.
Proof. exact (@lem1659554 x n). Qed.
Lemma lem1659556 (x : real) (n : nat) : (term141 x n) = ((term142 x n) = (term143 x n)).
Proof. exact (eq_refl (term141 x n)). Qed.
Lemma lem1659573 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem1659584 (x : real) (n : nat) : (term142 x n) = (term143 x n).
Proof. exact (EQ_MP (@lem1659556 x n) (@lem1659555 x n)). Qed.
Lemma lem1659586 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (term0 n).
Proof. exact (EQ_MP (@lem1659550 n) (@lem1659549 n)). Qed.
Lemma lem1659588 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (Coq.Arith.PeanoNat.Nat.Odd n) = True.
Proof. exact (EQ_MP (@lem1659573 n) (@lem1659323 n h1)). Qed.
Lemma lem1659589 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1659590 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term0 n) = (~ True).
Proof. exact (MK_COMB (@lem1659589) (@lem1659588 n h1)). Qed.
Lemma lem1659592 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1659593 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term0 n) = False.
Proof. exact (TRANS (@lem1659590 n h1) (@lem1659592)). Qed.
Lemma lem1659594 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (Coq.Arith.PeanoNat.Nat.Even n) = False.
Proof. exact (TRANS (@lem1659586 n) (@lem1659593 n h1)). Qed.
Lemma lem1659595 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1659596 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term144 n) = (@COND real False).
Proof. exact (MK_COMB (@lem1659595) (@lem1659594 n h1)). Qed.
Lemma lem1659597 (x : real) (n : nat) : (real_pow x n) = (real_pow x n).
Proof. exact (eq_refl (real_pow x n)). Qed.
Lemma lem1659598 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term145 x n) = (term146 x n).
Proof. exact (MK_COMB (@lem1659596 n h1) (@lem1659597 x n)). Qed.
Lemma lem1659599 (x : real) (n : nat) : (term147 x n) = (term147 x n).
Proof. exact (eq_refl (term147 x n)). Qed.
Lemma lem1659600 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term143 x n) = (term148 x n).
Proof. exact (MK_COMB (@lem1659598 x n h1) (@lem1659599 x n)). Qed.
Lemma lem1659602 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1659603 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1659602 real t1 t2). Qed.
Lemma lem1659604 (x : real) (n : nat) : (term148 x n) = (term147 x n).
Proof. exact (@lem1659603 (real_pow x n) (term147 x n)). Qed.
Lemma lem1659605 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term143 x n) = (term147 x n).
Proof. exact (TRANS (@lem1659600 x n h1) (@lem1659604 x n)). Qed.
Lemma lem1659606 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term142 x n) = (term147 x n).
Proof. exact (TRANS (@lem1659584 x n) (@lem1659605 x n h1)). Qed.
Lemma lem1659607 : term149 = term149.
Proof. exact (eq_refl term149). Qed.
Lemma lem1659608 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term135 x n) = (term150 x n).
Proof. exact (MK_COMB (@lem1659607) (@lem1659606 x n h1)). Qed.
Lemma lem1659609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1659610 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term136 x n) = (term151 x n).
Proof. exact (MK_COMB (@lem1659609) (@lem1659608 x n h1)). Qed.
Lemma lem1659611 (y : real) (n : nat) : (term132 y n) = (term132 y n).
Proof. exact (eq_refl (term132 y n)). Qed.
Lemma lem1659612 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term121 x y n) = (term152 x y n).
Proof. exact (MK_COMB (@lem1659610 x n h1) (@lem1659611 y n)). Qed.
Lemma lem1659615 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1659616 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term153 x y n) = (term154 x y n).
Proof. exact (MK_COMB (@lem1659615) (@lem1659612 x y n h1)). Qed.
Lemma lem1659617 (x : real) (y : real) (n : nat) : (term13 x y n) = (term13 x y n).
Proof. exact (eq_refl (term13 x y n)). Qed.
Lemma lem1659618 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term155 x y n) = (term156 x y n).
Proof. exact (MK_COMB (@lem1659616 x y n h1) (@lem1659617 x y n)). Qed.
Lemma lem1659621 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term156 x y n) = (term155 x y n).
Proof. exact (SYM (@lem1659618 x y n h1)). Qed.
Lemma lem1659652 (x : real) (y : real) (n : nat) : (term157 x y n) = (term158 x y n).
Proof. exact (@lem17362 (term152 x y n) (term13 x y n)). Qed.
Lemma lem1659653 (x : real) (n : nat) : (term150 x n) = (term159 x n).
Proof. exact (@lem1483521 (term147 x n) term28). Qed.
Lemma lem1659654 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1659661 (x : real) (n : nat) : (term147 x n) = (term160 x n).
Proof. exact (@lem1483512 (real_pow x n)). Qed.
Lemma lem1659662 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1659663 (x : real) (n : nat) : (term161 x n) = (term162 x n).
Proof. exact (MK_COMB (@lem1659662) (@lem1659661 x n)). Qed.
Lemma lem1659664 (x : real) (n : nat) : (term163 x n) = (term164 x n).
Proof. exact (MK_COMB (@lem1659663 x n) (@lem1659654)). Qed.
Lemma lem1659665 (x : real) (n : nat) : (term164 x n) = (term165 x n).
Proof. exact (@lem1483519 (term160 x n) term28). Qed.
Lemma lem1659667 (x : nat) : (term166 x) = term28.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1659668 : term167 = term28.
Proof. exact (@lem1659667 term48). Qed.
Lemma lem1659669 (x : real) (n : nat) : (term168 x n) = (term168 x n).
Proof. exact (eq_refl (term168 x n)). Qed.
Lemma lem1659670 (x : real) (n : nat) : (term165 x n) = (term169 x n).
Proof. exact (MK_COMB (@lem1659669 x n) (@lem1659668)). Qed.
Lemma lem1659671 (x : real) (n : nat) : (term169 x n) = (term160 x n).
Proof. exact (@lem1483450 (term160 x n)). Qed.
Lemma lem1659672 (x : real) (n : nat) : (term165 x n) = (term160 x n).
Proof. exact (TRANS (@lem1659670 x n) (@lem1659671 x n)). Qed.
Lemma lem1659673 (x : real) (n : nat) : (term164 x n) = (term160 x n).
Proof. exact (TRANS (@lem1659665 x n) (@lem1659672 x n)). Qed.
Lemma lem1659674 (x : real) (n : nat) : (term163 x n) = (term160 x n).
Proof. exact (TRANS (@lem1659664 x n) (@lem1659673 x n)). Qed.
Lemma lem1659675 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1659676 (x : real) (n : nat) : (term170 x n) = (term171 x n).
Proof. exact (MK_COMB (@lem1659675) (@lem1659674 x n)). Qed.
Lemma lem1659677 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1659678 (x : real) (n : nat) : (term159 x n) = (term172 x n).
Proof. exact (MK_COMB (@lem1659676 x n) (@lem1659677)). Qed.
Lemma lem1659679 (x : real) (n : nat) : (term150 x n) = (term172 x n).
Proof. exact (TRANS (@lem1659653 x n) (@lem1659678 x n)). Qed.
Lemma lem1659680 (y : real) (n : nat) : (term132 y n) = (term173 y n).
Proof. exact (@lem1483523 (real_pow y n) term28). Qed.
Lemma lem1659686 (y : real) (n : nat) : (term174 y n) = (term175 y n).
Proof. exact (@lem1483519 (real_pow y n) term28). Qed.
Lemma lem1659688 (x : nat) : (term166 x) = term28.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1659689 : term167 = term28.
Proof. exact (@lem1659688 term48). Qed.
Lemma lem1659690 (y : real) (n : nat) : (term176 y n) = (term176 y n).
Proof. exact (eq_refl (term176 y n)). Qed.
Lemma lem1659691 (y : real) (n : nat) : (term175 y n) = (term177 y n).
Proof. exact (MK_COMB (@lem1659690 y n) (@lem1659689)). Qed.
Lemma lem1659692 (y : real) (n : nat) : (term177 y n) = (real_pow y n).
Proof. exact (@lem1483450 (real_pow y n)). Qed.
Lemma lem1659693 (y : real) (n : nat) : (term175 y n) = (real_pow y n).
Proof. exact (TRANS (@lem1659691 y n) (@lem1659692 y n)). Qed.
Lemma lem1659695 (y : real) (n : nat) : (term174 y n) = (real_pow y n).
Proof. exact (TRANS (@lem1659686 y n) (@lem1659693 y n)). Qed.
Lemma lem1659696 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1659697 (y : real) (n : nat) : (term178 y n) = (term179 y n).
Proof. exact (MK_COMB (@lem1659696) (@lem1659695 y n)). Qed.
Lemma lem1659698 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1659699 (y : real) (n : nat) : (term173 y n) = (term180 y n).
Proof. exact (MK_COMB (@lem1659697 y n) (@lem1659698)). Qed.
Lemma lem1659700 (y : real) (n : nat) : (term132 y n) = (term180 y n).
Proof. exact (TRANS (@lem1659680 y n) (@lem1659699 y n)). Qed.
Lemma lem1659701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1659702 (x : real) (n : nat) : (term151 x n) = (term181 x n).
Proof. exact (MK_COMB (@lem1659701) (@lem1659679 x n)). Qed.
Lemma lem1659703 (x : real) (y : real) (n : nat) : (term152 x y n) = (term182 x y n).
Proof. exact (MK_COMB (@lem1659702 x n) (@lem1659700 y n)). Qed.
Lemma lem1659704 (x : real) (y : real) (n : nat) : (term183 x y n) = (term184 x y n).
Proof. exact (@lem1483531 (real_pow x n) (real_pow y n)). Qed.
Lemma lem1659717 (x : real) (y : real) (n : nat) : (term185 x y n) = (term186 x y n).
Proof. exact (@lem1483519 (real_pow x n) (real_pow y n)). Qed.
Lemma lem1659718 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1659719 (x : real) (y : real) (n : nat) : (term187 x y n) = (term188 x y n).
Proof. exact (MK_COMB (@lem1659718) (@lem1659717 x y n)). Qed.
Lemma lem1659720 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1659721 (x : real) (y : real) (n : nat) : (term184 x y n) = (term189 x y n).
Proof. exact (MK_COMB (@lem1659719 x y n) (@lem1659720)). Qed.
Lemma lem1659722 (x : real) (y : real) (n : nat) : (term183 x y n) = (term189 x y n).
Proof. exact (TRANS (@lem1659704 x y n) (@lem1659721 x y n)). Qed.
Lemma lem1659723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1659724 (x : real) (y : real) (n : nat) : (term190 x y n) = (term191 x y n).
Proof. exact (MK_COMB (@lem1659723) (@lem1659703 x y n)). Qed.
Lemma lem1659725 (x : real) (y : real) (n : nat) : (term158 x y n) = (term192 x y n).
Proof. exact (MK_COMB (@lem1659724 x y n) (@lem1659722 x y n)). Qed.
Lemma lem1659746 (x : real) (y : real) (n : nat) : (term157 x y n) = (term192 x y n).
Proof. exact (TRANS (@lem1659652 x y n) (@lem1659725 x y n)). Qed.
Lemma lem1659750 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term192 x y n.
Proof. exact (h1). Qed.
Lemma lem1659751 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term189 x y n.
Proof. exact (proj2 (@lem1659750 x y n h1)). Qed.
Lemma lem1659752 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term182 x y n.
Proof. exact (proj1 (@lem1659750 x y n h1)). Qed.
Lemma lem1659753 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term180 y n.
Proof. exact (proj2 (@lem1659752 x y n h1)). Qed.
Lemma lem1659754 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term172 x n.
Proof. exact (proj1 (@lem1659752 x y n h1)). Qed.
Lemma lem1659756 (n : nat) (m : nat) : (term62 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1659757 : term63 = term64.
Proof. exact (@lem1659756 (NUMERAL 0) term48). Qed.
Lemma lem1659758 : term65 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1659759 (h1 : term65 = (BIT1 0)) : term64 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1659760 : (term65 = (BIT1 0)) = (term64 = True).
Proof. exact (prop_ext (fun h1 : term65 = (BIT1 0) => @lem1659759 h1) (fun h1 : term64 = True => @lem1659758)). Qed.
Lemma lem1659761 : term64 = True.
Proof. exact (EQ_MP (@lem1659760) (@lem1659758)). Qed.
Lemma lem1659762 : term63 = True.
Proof. exact (TRANS (@lem1659757) (@lem1659761)). Qed.
Lemma lem1659763 : True = term63.
Proof. exact (SYM (@lem1659762)). Qed.
Lemma lem1659764 : term63.
Proof. exact (EQ_MP (@lem1659763) (@lem0)). Qed.
Lemma lem1659765 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term193 y n.
Proof. exact (conj (@lem1659764) (@lem1659753 x y n h1)). Qed.
Lemma lem1659767 (x : real) (y : real) : term67 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1659768 (y : real) (n : nat) : term194 y n.
Proof. exact (@lem1659767 term51 (real_pow y n)). Qed.
Lemma lem1659769 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term195 y n.
Proof. exact (@lem1659768 y n (@lem1659765 x y n h1)). Qed.
Lemma lem1659770 (y : real) (n : nat) : (term196 y n) = (real_pow y n).
Proof. exact (@lem1483460 (real_pow y n)). Qed.
Lemma lem1659771 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1659772 (y : real) (n : nat) : (term197 y n) = (term179 y n).
Proof. exact (MK_COMB (@lem1659771) (@lem1659770 y n)). Qed.
Lemma lem1659773 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1659774 (y : real) (n : nat) : (term195 y n) = (term180 y n).
Proof. exact (MK_COMB (@lem1659772 y n) (@lem1659773)). Qed.
Lemma lem1659775 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term180 y n.
Proof. exact (EQ_MP (@lem1659774 y n) (@lem1659769 x y n h1)). Qed.
Lemma lem1659777 (n : nat) (m : nat) : (term62 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1659778 : term63 = term64.
Proof. exact (@lem1659777 (NUMERAL 0) term48). Qed.
Lemma lem1659779 : term65 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1659780 (h1 : term65 = (BIT1 0)) : term64 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1659781 : (term65 = (BIT1 0)) = (term64 = True).
Proof. exact (prop_ext (fun h1 : term65 = (BIT1 0) => @lem1659780 h1) (fun h1 : term64 = True => @lem1659779)). Qed.
Lemma lem1659782 : term64 = True.
Proof. exact (EQ_MP (@lem1659781) (@lem1659779)). Qed.
Lemma lem1659783 : term63 = True.
Proof. exact (TRANS (@lem1659778) (@lem1659782)). Qed.
Lemma lem1659784 : True = term63.
Proof. exact (SYM (@lem1659783)). Qed.
Lemma lem1659785 : term63.
Proof. exact (EQ_MP (@lem1659784) (@lem0)). Qed.
Lemma lem1659786 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term198 x y n.
Proof. exact (conj (@lem1659785) (@lem1659751 x y n h1)). Qed.
Lemma lem1659788 (x : real) (y : real) : term67 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1659789 (x : real) (y : real) (n : nat) : term199 x y n.
Proof. exact (@lem1659788 term51 (term186 x y n)). Qed.
Lemma lem1659790 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term200 x y n.
Proof. exact (@lem1659789 x y n (@lem1659786 x y n h1)). Qed.
Lemma lem1659791 (x : real) (y : real) (n : nat) : (term201 x y n) = (term186 x y n).
Proof. exact (@lem1483460 (term186 x y n)). Qed.
Lemma lem1659792 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1659793 (x : real) (y : real) (n : nat) : (term202 x y n) = (term188 x y n).
Proof. exact (MK_COMB (@lem1659792) (@lem1659791 x y n)). Qed.
Lemma lem1659794 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1659795 (x : real) (y : real) (n : nat) : (term200 x y n) = (term189 x y n).
Proof. exact (MK_COMB (@lem1659793 x y n) (@lem1659794)). Qed.
Lemma lem1659796 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term189 x y n.
Proof. exact (EQ_MP (@lem1659795 x y n) (@lem1659790 x y n h1)). Qed.
Lemma lem1659798 (n : nat) (m : nat) : (term62 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1659799 : term63 = term64.
Proof. exact (@lem1659798 (NUMERAL 0) term48). Qed.
Lemma lem1659800 : term65 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1659801 (h1 : term65 = (BIT1 0)) : term64 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1659802 : (term65 = (BIT1 0)) = (term64 = True).
Proof. exact (prop_ext (fun h1 : term65 = (BIT1 0) => @lem1659801 h1) (fun h1 : term64 = True => @lem1659800)). Qed.
Lemma lem1659803 : term64 = True.
Proof. exact (EQ_MP (@lem1659802) (@lem1659800)). Qed.
Lemma lem1659804 : term63 = True.
Proof. exact (TRANS (@lem1659799) (@lem1659803)). Qed.
Lemma lem1659805 : True = term63.
Proof. exact (SYM (@lem1659804)). Qed.
Lemma lem1659806 : term63.
Proof. exact (EQ_MP (@lem1659805) (@lem0)). Qed.
Lemma lem1659807 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term203 x n.
Proof. exact (conj (@lem1659806) (@lem1659754 x y n h1)). Qed.
Lemma lem1659809 (x : real) (y : real) : term72 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1659810 (x : real) (n : nat) : term204 x n.
Proof. exact (@lem1659809 term51 (term160 x n)). Qed.
Lemma lem1659811 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term205 x n.
Proof. exact (@lem1659810 x n (@lem1659807 x y n h1)). Qed.
Lemma lem1659812 (x : real) (n : nat) : (term206 x n) = (term160 x n).
Proof. exact (@lem1483460 (term160 x n)). Qed.
Lemma lem1659813 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1659814 (x : real) (n : nat) : (term207 x n) = (term171 x n).
Proof. exact (MK_COMB (@lem1659813) (@lem1659812 x n)). Qed.
Lemma lem1659815 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1659816 (x : real) (n : nat) : (term205 x n) = (term172 x n).
Proof. exact (MK_COMB (@lem1659814 x n) (@lem1659815)). Qed.
Lemma lem1659817 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term172 x n.
Proof. exact (EQ_MP (@lem1659816 x n) (@lem1659811 x y n h1)). Qed.
Lemma lem1659818 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term208 x y n.
Proof. exact (conj (@lem1659817 x y n h1) (@lem1659796 x y n h1)). Qed.
Lemma lem1659820 (x : real) (y : real) : term77 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1659821 (x : real) (y : real) (n : nat) : term209 x y n.
Proof. exact (@lem1659820 (term160 x n) (term186 x y n)). Qed.
Lemma lem1659822 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term210 x y n.
Proof. exact (@lem1659821 x y n (@lem1659818 x y n h1)). Qed.
Lemma lem1659823 (x : real) (y : real) (n : nat) : (term211 x y n) = (term212 x y n).
Proof. exact (@lem1483490 (term160 x n) (real_pow x n) (term160 y n)). Qed.
Lemma lem1659824 (x : real) (n : nat) : (term213 x n) = (term214 x n).
Proof. exact (@lem1483440 term43 (real_pow x n)). Qed.
Lemma lem1659826 (m : nat) : (term82 m) = term28.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1659827 : term83 = term28.
Proof. exact (@lem1659826 term48). Qed.
Lemma lem1659828 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1659829 : term84 = term85.
Proof. exact (MK_COMB (@lem1659828) (@lem1659827)). Qed.
Lemma lem1659830 (x : real) (n : nat) : (real_pow x n) = (real_pow x n).
Proof. exact (eq_refl (real_pow x n)). Qed.
Lemma lem1659831 (x : real) (n : nat) : (term214 x n) = (term215 x n).
Proof. exact (MK_COMB (@lem1659829) (@lem1659830 x n)). Qed.
Lemma lem1659832 (x : real) (n : nat) : (term213 x n) = (term215 x n).
Proof. exact (TRANS (@lem1659824 x n) (@lem1659831 x n)). Qed.
Lemma lem1659833 (x : real) (n : nat) : (term215 x n) = term28.
Proof. exact (@lem1483446 (real_pow x n)). Qed.
Lemma lem1659834 (x : real) (n : nat) : (term213 x n) = term28.
Proof. exact (TRANS (@lem1659832 x n) (@lem1659833 x n)). Qed.
Lemma lem1659835 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1659836 (x : real) (n : nat) : (term216 x n) = term55.
Proof. exact (MK_COMB (@lem1659835) (@lem1659834 x n)). Qed.
Lemma lem1659837 (y : real) (n : nat) : (term160 y n) = (term160 y n).
Proof. exact (eq_refl (term160 y n)). Qed.
Lemma lem1659838 (x : real) (y : real) (n : nat) : (term212 x y n) = (term217 y n).
Proof. exact (MK_COMB (@lem1659836 x n) (@lem1659837 y n)). Qed.
Lemma lem1659839 (x : real) (y : real) (n : nat) : (term211 x y n) = (term217 y n).
Proof. exact (TRANS (@lem1659823 x y n) (@lem1659838 x y n)). Qed.
Lemma lem1659840 (y : real) (n : nat) : (term217 y n) = (term160 y n).
Proof. exact (@lem1483448 (term160 y n)). Qed.
Lemma lem1659841 (x : real) (y : real) (n : nat) : (term211 x y n) = (term160 y n).
Proof. exact (TRANS (@lem1659839 x y n) (@lem1659840 y n)). Qed.
Lemma lem1659842 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1659843 (x : real) (y : real) (n : nat) : (term218 x y n) = (term171 y n).
Proof. exact (MK_COMB (@lem1659842) (@lem1659841 x y n)). Qed.
Lemma lem1659844 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1659845 (x : real) (y : real) (n : nat) : (term210 x y n) = (term172 y n).
Proof. exact (MK_COMB (@lem1659843 x y n) (@lem1659844)). Qed.
Lemma lem1659846 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term172 y n.
Proof. exact (EQ_MP (@lem1659845 x y n) (@lem1659822 x y n h1)). Qed.
Lemma lem1659848 (n : nat) (m : nat) : (term62 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1659849 : term63 = term64.
Proof. exact (@lem1659848 (NUMERAL 0) term48). Qed.
Lemma lem1659850 : term65 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1659851 (h1 : term65 = (BIT1 0)) : term64 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1659852 : (term65 = (BIT1 0)) = (term64 = True).
Proof. exact (prop_ext (fun h1 : term65 = (BIT1 0) => @lem1659851 h1) (fun h1 : term64 = True => @lem1659850)). Qed.
Lemma lem1659853 : term64 = True.
Proof. exact (EQ_MP (@lem1659852) (@lem1659850)). Qed.
Lemma lem1659854 : term63 = True.
Proof. exact (TRANS (@lem1659849) (@lem1659853)). Qed.
Lemma lem1659855 : True = term63.
Proof. exact (SYM (@lem1659854)). Qed.
Lemma lem1659856 : term63.
Proof. exact (EQ_MP (@lem1659855) (@lem0)). Qed.
Lemma lem1659857 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term203 y n.
Proof. exact (conj (@lem1659856) (@lem1659846 x y n h1)). Qed.
Lemma lem1659859 (x : real) (y : real) : term72 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1659860 (y : real) (n : nat) : term204 y n.
Proof. exact (@lem1659859 term51 (term160 y n)). Qed.
Lemma lem1659861 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term205 y n.
Proof. exact (@lem1659860 y n (@lem1659857 x y n h1)). Qed.
Lemma lem1659862 (y : real) (n : nat) : (term206 y n) = (term160 y n).
Proof. exact (@lem1483460 (term160 y n)). Qed.
Lemma lem1659863 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1659864 (y : real) (n : nat) : (term207 y n) = (term171 y n).
Proof. exact (MK_COMB (@lem1659863) (@lem1659862 y n)). Qed.
Lemma lem1659865 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1659866 (y : real) (n : nat) : (term205 y n) = (term172 y n).
Proof. exact (MK_COMB (@lem1659864 y n) (@lem1659865)). Qed.
Lemma lem1659867 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term172 y n.
Proof. exact (EQ_MP (@lem1659866 y n) (@lem1659861 x y n h1)). Qed.
Lemma lem1659868 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term219 y n.
Proof. exact (conj (@lem1659867 x y n h1) (@lem1659775 x y n h1)). Qed.
Lemma lem1659870 (x : real) (y : real) : term77 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1659871 (y : real) (n : nat) : term220 y n.
Proof. exact (@lem1659870 (term160 y n) (real_pow y n)). Qed.
Lemma lem1659872 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term221 y n.
Proof. exact (@lem1659871 y n (@lem1659868 x y n h1)). Qed.
Lemma lem1659873 (y : real) (n : nat) : (term213 y n) = (term214 y n).
Proof. exact (@lem1483440 term43 (real_pow y n)). Qed.
Lemma lem1659875 (m : nat) : (term82 m) = term28.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1659876 : term83 = term28.
Proof. exact (@lem1659875 term48). Qed.
Lemma lem1659877 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1659878 : term84 = term85.
Proof. exact (MK_COMB (@lem1659877) (@lem1659876)). Qed.
Lemma lem1659879 (y : real) (n : nat) : (real_pow y n) = (real_pow y n).
Proof. exact (eq_refl (real_pow y n)). Qed.
Lemma lem1659880 (y : real) (n : nat) : (term214 y n) = (term215 y n).
Proof. exact (MK_COMB (@lem1659878) (@lem1659879 y n)). Qed.
Lemma lem1659881 (y : real) (n : nat) : (term213 y n) = (term215 y n).
Proof. exact (TRANS (@lem1659873 y n) (@lem1659880 y n)). Qed.
Lemma lem1659882 (y : real) (n : nat) : (term215 y n) = term28.
Proof. exact (@lem1483446 (real_pow y n)). Qed.
Lemma lem1659883 (y : real) (n : nat) : (term213 y n) = term28.
Proof. exact (TRANS (@lem1659881 y n) (@lem1659882 y n)). Qed.
Lemma lem1659884 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1659885 (y : real) (n : nat) : (term222 y n) = term88.
Proof. exact (MK_COMB (@lem1659884) (@lem1659883 y n)). Qed.
Lemma lem1659886 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1659887 (y : real) (n : nat) : (term221 y n) = term89.
Proof. exact (MK_COMB (@lem1659885 y n) (@lem1659886)). Qed.
Lemma lem1659888 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term89.
Proof. exact (EQ_MP (@lem1659887 y n) (@lem1659872 x y n h1)). Qed.
Lemma lem1659890 (n : nat) (m : nat) : (term62 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1659891 : term89 = term90.
Proof. exact (@lem1659890 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1659892 : term90 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1659893 : term89 = False.
Proof. exact (TRANS (@lem1659891) (@lem1659892)). Qed.
Lemma lem1659894 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : False.
Proof. exact (EQ_MP (@lem1659893) (@lem1659888 x y n h1)). Qed.
Lemma lem1659896 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : term192 x y n.
Proof. exact (h1). Qed.
Lemma lem1659897 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : (term192 x y n) = False.
Proof. exact (prop_ext (fun h2 : term192 x y n => @lem1659894 x y n h1) (fun h2 : False => @lem1659896 x y n h1)). Qed.
Lemma lem1659898 (x : real) (y : real) (n : nat) (h1 : term192 x y n) : False.
Proof. exact (EQ_MP (@lem1659897 x y n h1) (@lem1659896 x y n h1)). Qed.
Lemma lem1659899 (x : real) (y : real) (n : nat) (h1 : term157 x y n) : term157 x y n.
Proof. exact (h1). Qed.
Lemma lem1659900 (x : real) (y : real) (n : nat) (h1 : term157 x y n) : term192 x y n.
Proof. exact (EQ_MP (@lem1659746 x y n) (@lem1659899 x y n h1)). Qed.
Lemma lem1659901 (x : real) (y : real) (n : nat) (h1 : term157 x y n) : (term192 x y n) = False.
Proof. exact (prop_ext (fun h2 : term192 x y n => @lem1659898 x y n h2) (fun h2 : False => @lem1659900 x y n h1)). Qed.
Lemma lem1659902 (x : real) (y : real) (n : nat) (h1 : term157 x y n) : False.
Proof. exact (EQ_MP (@lem1659901 x y n h1) (@lem1659900 x y n h1)). Qed.
Lemma lem1659903 (x : real) (y : real) (n : nat) : term223 x y n.
Proof. exact (fun h0 : term157 x y n => @lem1659902 x y n h0). Qed.
Lemma lem1659904 (x : real) (y : real) (n : nat) : term224 x y n.
Proof. exact (@lem1386578 (term156 x y n)). Qed.
Lemma lem1659905 (x : real) (y : real) (n : nat) : term156 x y n.
Proof. exact (@lem1659904 x y n (@lem1659903 x y n)). Qed.
Lemma lem1659906 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : term155 x y n.
Proof. exact (EQ_MP (@lem1659621 x y n h1) (@lem1659905 x y n)). Qed.
Lemma lem1659907 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term121 x y n) : term13 x y n.
Proof. exact (@lem1659906 x y n h1 (@lem1659470 x y n h2)). Qed.
Lemma lem1659908 (n : nat) (y : real) (x : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term24 y) (h3 : term25 x) : (term121 x y n) = (term13 x y n).
Proof. exact (prop_ext (fun h4 : term121 x y n => @lem1659907 x y n h1 h4) (fun h4 : term13 x y n => @lem1659548 n y x h2 h3)). Qed.
Lemma lem1659910 (n : nat) (y : real) (x : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term24 y) (h3 : term25 x) : term13 x y n.
Proof. exact (EQ_MP (@lem1659908 n y x h1 h2 h3) (@lem1659548 n y x h2 h3)). Qed.
Lemma lem1659911 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : term24 y) (h4 : real_lt x y) : term13 x y n.
Proof. exact (or_elim (@lem1657961 x) (fun h0 : term24 x => @lem1659399 n x y h2 h0 h4) (fun h0 : term25 x => @lem1659910 n y x h1 h3 h0)). Qed.
Lemma lem1659912 (y : real) (x : real) (n : nat) (h1 : term225 y x n) : term225 y x n.
Proof. exact (h1). Qed.
Lemma lem1659914 (x : real) (y : real) (n : nat) : term11 x y n.
Proof. exact (EQ_MP (@lem1657764 x y n) (@lem1657763 x y n)). Qed.
Lemma lem1659915 (y : real) (x : real) (n : nat) : term226 y x n.
Proof. exact (@lem1659914 (real_neg y) (real_neg x) n). Qed.
Lemma lem1659916 (n : nat) : term116 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem1659933 (y : real) : (term96 y) = ((term96 y) = True).
Proof. exact (@lem7 (term96 y)). Qed.
Lemma lem1659938 (n : nat) (h1 : term99 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1659916 n (@lem1657973 n h1)). Qed.
Lemma lem1659939 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1659940 (n : nat) (h1 : term99 n) : (term99 n) = (~ False).
Proof. exact (MK_COMB (@lem1659939) (@lem1659938 n h1)). Qed.
Lemma lem1659942 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1659943 (n : nat) (h1 : term99 n) : (term99 n) = True.
Proof. exact (TRANS (@lem1659940 n h1) (@lem1659942)). Qed.
Lemma lem1659944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1659945 (n : nat) (h1 : term99 n) : (term118 n) = (and True).
Proof. exact (MK_COMB (@lem1659944) (@lem1659943 n h1)). Qed.
Lemma lem1659949 (y : real) (h1 : term96 y) : (term96 y) = True.
Proof. exact (EQ_MP (@lem1659933 y) (@lem1657968 y h1)). Qed.
Lemma lem1659950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1659951 (y : real) (h1 : term96 y) : (term227 y) = (and True).
Proof. exact (MK_COMB (@lem1659950) (@lem1659949 y h1)). Qed.
Lemma lem1659952 (y : real) (x : real) : (term228 y x) = (term228 y x).
Proof. exact (eq_refl (term228 y x)). Qed.
Lemma lem1659953 (x : real) (y : real) (h1 : term96 y) : (term229 y x) = (term230 y x).
Proof. exact (MK_COMB (@lem1659951 y h1) (@lem1659952 y x)). Qed.
Lemma lem1659955 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1659956 (y : real) (x : real) : (term230 y x) = (term228 y x).
Proof. exact (@lem1659955 (term228 y x)). Qed.
Lemma lem1659957 (x : real) (y : real) (h1 : term96 y) : (term229 y x) = (term228 y x).
Proof. exact (TRANS (@lem1659953 x y h1) (@lem1659956 y x)). Qed.
Lemma lem1659958 (x : real) (n : nat) (y : real) (h1 : term99 n) (h2 : term96 y) : (term231 n y x) = (term230 y x).
Proof. exact (MK_COMB (@lem1659945 n h1) (@lem1659957 x y h2)). Qed.
Lemma lem1659960 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1659961 (y : real) (x : real) : (term230 y x) = (term228 y x).
Proof. exact (@lem1659960 (term228 y x)). Qed.
Lemma lem1659962 (x : real) (n : nat) (y : real) (h1 : term99 n) (h2 : term96 y) : (term231 n y x) = (term228 y x).
Proof. exact (TRANS (@lem1659958 x n y h1 h2) (@lem1659961 y x)). Qed.
Lemma lem1659963 (x : real) (n : nat) (y : real) (h1 : term99 n) (h2 : term96 y) : (term228 y x) = (term231 n y x).
Proof. exact (SYM (@lem1659962 x n y h1 h2)). Qed.
Lemma lem1659964 (n : nat) : term138 n.
Proof. exact (@lem1657735 n). Qed.
Lemma lem1659965 (n : nat) : (term138 n) = ((Coq.Arith.PeanoNat.Nat.Even n) = (term0 n)).
Proof. exact (eq_refl (term138 n)). Qed.
Lemma lem1659967 (x : real) : term139 x.
Proof. exact (@lem1362863 x). Qed.
Lemma lem1659968 (x : real) : (term139 x) = (term140 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1659969 (x : real) : term140 x.
Proof. exact (EQ_MP (@lem1659968 x) (@lem1659967 x)). Qed.
Lemma lem1659970 (x : real) (n : nat) : term141 x n.
Proof. exact (@lem1659969 x n). Qed.
Lemma lem1659971 (x : real) (n : nat) : (term141 x n) = ((term142 x n) = (term143 x n)).
Proof. exact (eq_refl (term141 x n)). Qed.
Lemma lem1659988 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem1659995 (x : real) (n : nat) : (term142 x n) = (term143 x n).
Proof. exact (EQ_MP (@lem1659971 x n) (@lem1659970 x n)). Qed.
Lemma lem1659996 (y : real) (n : nat) : (term142 y n) = (term143 y n).
Proof. exact (@lem1659995 y n). Qed.
Lemma lem1659998 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (term0 n).
Proof. exact (EQ_MP (@lem1659965 n) (@lem1659964 n)). Qed.
Lemma lem1660000 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (Coq.Arith.PeanoNat.Nat.Odd n) = True.
Proof. exact (EQ_MP (@lem1659988 n) (@lem1659323 n h1)). Qed.
Lemma lem1660001 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1660002 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term0 n) = (~ True).
Proof. exact (MK_COMB (@lem1660001) (@lem1660000 n h1)). Qed.
Lemma lem1660004 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1660005 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term0 n) = False.
Proof. exact (TRANS (@lem1660002 n h1) (@lem1660004)). Qed.
Lemma lem1660006 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (Coq.Arith.PeanoNat.Nat.Even n) = False.
Proof. exact (TRANS (@lem1659998 n) (@lem1660005 n h1)). Qed.
Lemma lem1660007 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1660008 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term144 n) = (@COND real False).
Proof. exact (MK_COMB (@lem1660007) (@lem1660006 n h1)). Qed.
Lemma lem1660009 (y : real) (n : nat) : (real_pow y n) = (real_pow y n).
Proof. exact (eq_refl (real_pow y n)). Qed.
Lemma lem1660010 (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term145 y n) = (term146 y n).
Proof. exact (MK_COMB (@lem1660008 n h1) (@lem1660009 y n)). Qed.
Lemma lem1660011 (y : real) (n : nat) : (term147 y n) = (term147 y n).
Proof. exact (eq_refl (term147 y n)). Qed.
Lemma lem1660012 (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term143 y n) = (term148 y n).
Proof. exact (MK_COMB (@lem1660010 y n h1) (@lem1660011 y n)). Qed.
Lemma lem1660014 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1660015 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1660014 real t1 t2). Qed.
Lemma lem1660016 (y : real) (n : nat) : (term148 y n) = (term147 y n).
Proof. exact (@lem1660015 (real_pow y n) (term147 y n)). Qed.
Lemma lem1660017 (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term143 y n) = (term147 y n).
Proof. exact (TRANS (@lem1660012 y n h1) (@lem1660016 y n)). Qed.
Lemma lem1660018 (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term142 y n) = (term147 y n).
Proof. exact (TRANS (@lem1659996 y n) (@lem1660017 y n h1)). Qed.
Lemma lem1660019 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1660020 (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term232 y n) = (term233 y n).
Proof. exact (MK_COMB (@lem1660019) (@lem1660018 y n h1)). Qed.
Lemma lem1660022 (x : real) (n : nat) : (term142 x n) = (term143 x n).
Proof. exact (EQ_MP (@lem1659971 x n) (@lem1659970 x n)). Qed.
Lemma lem1660024 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (term0 n).
Proof. exact (EQ_MP (@lem1659965 n) (@lem1659964 n)). Qed.
Lemma lem1660026 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (Coq.Arith.PeanoNat.Nat.Odd n) = True.
Proof. exact (EQ_MP (@lem1659988 n) (@lem1659323 n h1)). Qed.
Lemma lem1660027 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1660028 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term0 n) = (~ True).
Proof. exact (MK_COMB (@lem1660027) (@lem1660026 n h1)). Qed.
Lemma lem1660030 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1660031 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term0 n) = False.
Proof. exact (TRANS (@lem1660028 n h1) (@lem1660030)). Qed.
Lemma lem1660032 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (Coq.Arith.PeanoNat.Nat.Even n) = False.
Proof. exact (TRANS (@lem1660024 n) (@lem1660031 n h1)). Qed.
Lemma lem1660033 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1660034 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term144 n) = (@COND real False).
Proof. exact (MK_COMB (@lem1660033) (@lem1660032 n h1)). Qed.
Lemma lem1660035 (x : real) (n : nat) : (real_pow x n) = (real_pow x n).
Proof. exact (eq_refl (real_pow x n)). Qed.
Lemma lem1660036 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term145 x n) = (term146 x n).
Proof. exact (MK_COMB (@lem1660034 n h1) (@lem1660035 x n)). Qed.
Lemma lem1660037 (x : real) (n : nat) : (term147 x n) = (term147 x n).
Proof. exact (eq_refl (term147 x n)). Qed.
Lemma lem1660038 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term143 x n) = (term148 x n).
Proof. exact (MK_COMB (@lem1660036 x n h1) (@lem1660037 x n)). Qed.
Lemma lem1660040 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1660041 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1660040 real t1 t2). Qed.
Lemma lem1660042 (x : real) (n : nat) : (term148 x n) = (term147 x n).
Proof. exact (@lem1660041 (real_pow x n) (term147 x n)). Qed.
Lemma lem1660043 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term143 x n) = (term147 x n).
Proof. exact (TRANS (@lem1660038 x n h1) (@lem1660042 x n)). Qed.
Lemma lem1660044 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term142 x n) = (term147 x n).
Proof. exact (TRANS (@lem1660022 x n) (@lem1660043 x n h1)). Qed.
Lemma lem1660045 (y : real) (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term225 y x n) = (term234 y x n).
Proof. exact (MK_COMB (@lem1660020 y n h1) (@lem1660044 x n h1)). Qed.
Lemma lem1660046 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1660047 (y : real) (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term235 y x n) = (term236 y x n).
Proof. exact (MK_COMB (@lem1660046) (@lem1660045 y x n h1)). Qed.
Lemma lem1660048 (x : real) (y : real) (n : nat) : (term13 x y n) = (term13 x y n).
Proof. exact (eq_refl (term13 x y n)). Qed.
Lemma lem1660049 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term237 x y n) = (term238 x y n).
Proof. exact (MK_COMB (@lem1660047 y x n h1) (@lem1660048 x y n)). Qed.
Lemma lem1660052 (x : real) (y : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term238 x y n) = (term237 x y n).
Proof. exact (SYM (@lem1660049 x y n h1)). Qed.
Lemma lem1660073 (y : real) (x : real) : (term239 y x) = (term240 y x).
Proof. exact (@lem17362 (term96 y) (term228 y x)). Qed.
Lemma lem1660075 (n : nat) : (term241 n) = (term241 n).
Proof. exact (eq_refl (term241 n)). Qed.
Lemma lem1660076 (n : nat) (y : real) (x : real) : (term242 n y x) = (term243 n y x).
Proof. exact (MK_COMB (@lem1660075 n) (@lem1660073 y x)). Qed.
Lemma lem1660077 (n : nat) (y : real) (x : real) : (term244 n y x) = (term242 n y x).
Proof. exact (@lem17362 (Coq.Arith.PeanoNat.Nat.Odd n) (term245 y x)). Qed.
Lemma lem1660078 (n : nat) (y : real) (x : real) : (term244 n y x) = (term243 n y x).
Proof. exact (TRANS (@lem1660077 n y x) (@lem1660076 n y x)). Qed.
Lemma lem1660080 (x : real) (y : real) : (term106 x y) = (term106 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1660081 (n : nat) (y : real) (x : real) : (term246 n y x) = (term247 n y x).
Proof. exact (MK_COMB (@lem1660080 x y) (@lem1660078 n y x)). Qed.
Lemma lem1660082 (n : nat) (y : real) (x : real) : (term248 n y x) = (term246 n y x).
Proof. exact (@lem17362 (real_lt x y) (term249 n y x)). Qed.
Lemma lem1660083 (n : nat) (y : real) (x : real) : (term248 n y x) = (term247 n y x).
Proof. exact (TRANS (@lem1660082 n y x) (@lem1660081 n y x)). Qed.
Lemma lem1660085 (n : nat) : (term118 n) = (term118 n).
Proof. exact (eq_refl (term118 n)). Qed.
Lemma lem1660086 (n : nat) (y : real) (x : real) : (term250 n y x) = (term251 n y x).
Proof. exact (MK_COMB (@lem1660085 n) (@lem1660083 n y x)). Qed.
Lemma lem1660087 (n : nat) (y : real) (x : real) : (term252 n y x) = (term250 n y x).
Proof. exact (@lem17362 (term99 n) (term253 n y x)). Qed.
Lemma lem1660111 (n : nat) (y : real) (x : real) : (term252 n y x) = (term251 n y x).
Proof. exact (TRANS (@lem1660087 n y x) (@lem1660086 n y x)). Qed.
Lemma lem1660113 (y : real) (x : real) : (real_lt x y) = (term254 y x).
Proof. exact (@lem1483521 y x). Qed.
Lemma lem1660119 (y : real) (x : real) : (real_sub y x) = (term255 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1660124 (x : real) (y : real) : (term255 y x) = (term256 x y).
Proof. exact (@lem1483488 (term31 x) y). Qed.
Lemma lem1660126 (x : real) (y : real) : (real_sub y x) = (term256 x y).
Proof. exact (TRANS (@lem1660119 y x) (@lem1660124 x y)). Qed.
Lemma lem1660127 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1660128 (x : real) (y : real) : (term257 y x) = (term258 x y).
Proof. exact (MK_COMB (@lem1660127) (@lem1660126 x y)). Qed.
Lemma lem1660129 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660130 (x : real) (y : real) : (term254 y x) = (term259 x y).
Proof. exact (MK_COMB (@lem1660128 x y) (@lem1660129)). Qed.
Lemma lem1660131 (x : real) (y : real) : (real_lt x y) = (term259 x y).
Proof. exact (TRANS (@lem1660113 y x) (@lem1660130 x y)). Qed.
Lemma lem1660133 (y : real) : (term96 y) = (term260 y).
Proof. exact (@lem1483523 (real_neg y) term28). Qed.
Lemma lem1660134 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660141 (y : real) : (real_neg y) = (term31 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1660142 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1660143 (y : real) : (term261 y) = (term262 y).
Proof. exact (MK_COMB (@lem1660142) (@lem1660141 y)). Qed.
Lemma lem1660144 (y : real) : (term263 y) = (term264 y).
Proof. exact (MK_COMB (@lem1660143 y) (@lem1660134)). Qed.
Lemma lem1660145 (y : real) : (term264 y) = (term265 y).
Proof. exact (@lem1483519 (term31 y) term28). Qed.
Lemma lem1660147 (x : nat) : (term166 x) = term28.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1660148 : term167 = term28.
Proof. exact (@lem1660147 term48). Qed.
Lemma lem1660149 (y : real) : (term266 y) = (term266 y).
Proof. exact (eq_refl (term266 y)). Qed.
Lemma lem1660150 (y : real) : (term265 y) = (term267 y).
Proof. exact (MK_COMB (@lem1660149 y) (@lem1660148)). Qed.
Lemma lem1660151 (y : real) : (term267 y) = (term31 y).
Proof. exact (@lem1483450 (term31 y)). Qed.
Lemma lem1660152 (y : real) : (term265 y) = (term31 y).
Proof. exact (TRANS (@lem1660150 y) (@lem1660151 y)). Qed.
Lemma lem1660153 (y : real) : (term264 y) = (term31 y).
Proof. exact (TRANS (@lem1660145 y) (@lem1660152 y)). Qed.
Lemma lem1660154 (y : real) : (term263 y) = (term31 y).
Proof. exact (TRANS (@lem1660144 y) (@lem1660153 y)). Qed.
Lemma lem1660155 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1660156 (y : real) : (term268 y) = (term269 y).
Proof. exact (MK_COMB (@lem1660155) (@lem1660154 y)). Qed.
Lemma lem1660157 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660158 (y : real) : (term260 y) = (term270 y).
Proof. exact (MK_COMB (@lem1660156 y) (@lem1660157)). Qed.
Lemma lem1660159 (y : real) : (term96 y) = (term270 y).
Proof. exact (TRANS (@lem1660133 y) (@lem1660158 y)). Qed.
Lemma lem1660160 (y : real) (x : real) : (term271 y x) = (term272 y x).
Proof. exact (@lem1483531 (real_neg y) (real_neg x)). Qed.
Lemma lem1660167 (x : real) : (real_neg x) = (term31 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1660174 (y : real) : (real_neg y) = (term31 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1660175 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1660176 (y : real) : (term261 y) = (term262 y).
Proof. exact (MK_COMB (@lem1660175) (@lem1660174 y)). Qed.
Lemma lem1660177 (y : real) (x : real) : (term273 y x) = (term274 y x).
Proof. exact (MK_COMB (@lem1660176 y) (@lem1660167 x)). Qed.
Lemma lem1660178 (y : real) (x : real) : (term274 y x) = (term275 y x).
Proof. exact (@lem1483519 (term31 y) (term31 x)). Qed.
Lemma lem1660179 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1483476 term43 term43 x). Qed.
Lemma lem1660181 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1660182 : term46 = term47.
Proof. exact (@lem1660181 term48 term48). Qed.
Lemma lem1660183 : (term49 = (BIT1 0)) = (term50 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1660184 : term50 = term48.
Proof. exact (EQ_MP (@lem1660183) (@lem940073)). Qed.
Lemma lem1660185 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1660186 : term47 = term51.
Proof. exact (MK_COMB (@lem1660185) (@lem1660184)). Qed.
Lemma lem1660187 : term46 = term51.
Proof. exact (TRANS (@lem1660182) (@lem1660186)). Qed.
Lemma lem1660188 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1660189 : term52 = term53.
Proof. exact (MK_COMB (@lem1660188) (@lem1660187)). Qed.
Lemma lem1660190 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1660191 (x : real) : (term42 x) = (term54 x).
Proof. exact (MK_COMB (@lem1660189) (@lem1660190 x)). Qed.
Lemma lem1660192 (x : real) : (term41 x) = (term54 x).
Proof. exact (TRANS (@lem1660179 x) (@lem1660191 x)). Qed.
Lemma lem1660193 (x : real) : (term54 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1660194 (x : real) : (term41 x) = x.
Proof. exact (TRANS (@lem1660192 x) (@lem1660193 x)). Qed.
Lemma lem1660195 (y : real) : (term266 y) = (term266 y).
Proof. exact (eq_refl (term266 y)). Qed.
Lemma lem1660196 (y : real) (x : real) : (term275 y x) = (term256 y x).
Proof. exact (MK_COMB (@lem1660195 y) (@lem1660194 x)). Qed.
Lemma lem1660197 (x : real) (y : real) : (term256 y x) = (term255 x y).
Proof. exact (@lem1483488 x (term31 y)). Qed.
Lemma lem1660198 (x : real) (y : real) : (term275 y x) = (term255 x y).
Proof. exact (TRANS (@lem1660196 y x) (@lem1660197 x y)). Qed.
Lemma lem1660199 (x : real) (y : real) : (term274 y x) = (term255 x y).
Proof. exact (TRANS (@lem1660178 y x) (@lem1660198 x y)). Qed.
Lemma lem1660200 (x : real) (y : real) : (term273 y x) = (term255 x y).
Proof. exact (TRANS (@lem1660177 y x) (@lem1660199 x y)). Qed.
Lemma lem1660201 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1660202 (x : real) (y : real) : (term276 y x) = (term277 x y).
Proof. exact (MK_COMB (@lem1660201) (@lem1660200 x y)). Qed.
Lemma lem1660203 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660204 (x : real) (y : real) : (term272 y x) = (term278 x y).
Proof. exact (MK_COMB (@lem1660202 x y) (@lem1660203)). Qed.
Lemma lem1660205 (x : real) (y : real) : (term271 y x) = (term278 x y).
Proof. exact (TRANS (@lem1660160 y x) (@lem1660204 x y)). Qed.
Lemma lem1660206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1660207 (y : real) : (term227 y) = (term279 y).
Proof. exact (MK_COMB (@lem1660206) (@lem1660159 y)). Qed.
Lemma lem1660208 (x : real) (y : real) : (term240 y x) = (term280 x y).
Proof. exact (MK_COMB (@lem1660207 y) (@lem1660205 x y)). Qed.
Lemma lem1660210 (n : nat) : (term241 n) = (term241 n).
Proof. exact (eq_refl (term241 n)). Qed.
Lemma lem1660211 (n : nat) (x : real) (y : real) : (term243 n y x) = (term281 n x y).
Proof. exact (MK_COMB (@lem1660210 n) (@lem1660208 x y)). Qed.
Lemma lem1660212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1660213 (x : real) (y : real) : (term106 x y) = (term282 x y).
Proof. exact (MK_COMB (@lem1660212) (@lem1660131 x y)). Qed.
Lemma lem1660214 (n : nat) (x : real) (y : real) : (term247 n y x) = (term283 n x y).
Proof. exact (MK_COMB (@lem1660213 x y) (@lem1660211 n x y)). Qed.
Lemma lem1660216 (n : nat) : (term118 n) = (term118 n).
Proof. exact (eq_refl (term118 n)). Qed.
Lemma lem1660217 (n : nat) (x : real) (y : real) : (term251 n y x) = (term284 n x y).
Proof. exact (MK_COMB (@lem1660216 n) (@lem1660214 n x y)). Qed.
Lemma lem1660250 (n : nat) (x : real) (y : real) : (term252 n y x) = (term284 n x y).
Proof. exact (TRANS (@lem1660111 n y x) (@lem1660217 n x y)). Qed.
Lemma lem1660254 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term284 n x y.
Proof. exact (h1). Qed.
Lemma lem1660255 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term283 n x y.
Proof. exact (proj2 (@lem1660254 n x y h1)). Qed.
Lemma lem1660257 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term281 n x y.
Proof. exact (proj2 (@lem1660255 n x y h1)). Qed.
Lemma lem1660258 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term259 x y.
Proof. exact (proj1 (@lem1660255 n x y h1)). Qed.
Lemma lem1660259 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term280 x y.
Proof. exact (proj2 (@lem1660257 n x y h1)). Qed.
Lemma lem1660261 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term278 x y.
Proof. exact (proj2 (@lem1660259 n x y h1)). Qed.
Lemma lem1660264 (n : nat) (m : nat) : (term62 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1660265 : term63 = term64.
Proof. exact (@lem1660264 (NUMERAL 0) term48). Qed.
Lemma lem1660266 : term65 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1660267 (h1 : term65 = (BIT1 0)) : term64 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1660268 : (term65 = (BIT1 0)) = (term64 = True).
Proof. exact (prop_ext (fun h1 : term65 = (BIT1 0) => @lem1660267 h1) (fun h1 : term64 = True => @lem1660266)). Qed.
Lemma lem1660269 : term64 = True.
Proof. exact (EQ_MP (@lem1660268) (@lem1660266)). Qed.
Lemma lem1660270 : term63 = True.
Proof. exact (TRANS (@lem1660265) (@lem1660269)). Qed.
Lemma lem1660271 : True = term63.
Proof. exact (SYM (@lem1660270)). Qed.
Lemma lem1660272 : term63.
Proof. exact (EQ_MP (@lem1660271) (@lem0)). Qed.
Lemma lem1660273 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term285 x y.
Proof. exact (conj (@lem1660272) (@lem1660261 n x y h1)). Qed.
Lemma lem1660275 (x : real) (y : real) : term67 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1660276 (x : real) (y : real) : term286 x y.
Proof. exact (@lem1660275 term51 (term255 x y)). Qed.
Lemma lem1660277 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term287 x y.
Proof. exact (@lem1660276 x y (@lem1660273 n x y h1)). Qed.
Lemma lem1660278 (x : real) (y : real) : (term288 x y) = (term255 x y).
Proof. exact (@lem1483460 (term255 x y)). Qed.
Lemma lem1660279 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1660280 (x : real) (y : real) : (term289 x y) = (term277 x y).
Proof. exact (MK_COMB (@lem1660279) (@lem1660278 x y)). Qed.
Lemma lem1660281 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660282 (x : real) (y : real) : (term287 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem1660280 x y) (@lem1660281)). Qed.
Lemma lem1660283 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term278 x y.
Proof. exact (EQ_MP (@lem1660282 x y) (@lem1660277 n x y h1)). Qed.
Lemma lem1660285 (n : nat) (m : nat) : (term62 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1660286 : term63 = term64.
Proof. exact (@lem1660285 (NUMERAL 0) term48). Qed.
Lemma lem1660287 : term65 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1660288 (h1 : term65 = (BIT1 0)) : term64 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1660289 : (term65 = (BIT1 0)) = (term64 = True).
Proof. exact (prop_ext (fun h1 : term65 = (BIT1 0) => @lem1660288 h1) (fun h1 : term64 = True => @lem1660287)). Qed.
Lemma lem1660290 : term64 = True.
Proof. exact (EQ_MP (@lem1660289) (@lem1660287)). Qed.
Lemma lem1660291 : term63 = True.
Proof. exact (TRANS (@lem1660286) (@lem1660290)). Qed.
Lemma lem1660292 : True = term63.
Proof. exact (SYM (@lem1660291)). Qed.
Lemma lem1660293 : term63.
Proof. exact (EQ_MP (@lem1660292) (@lem0)). Qed.
Lemma lem1660294 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term290 x y.
Proof. exact (conj (@lem1660293) (@lem1660258 n x y h1)). Qed.
Lemma lem1660296 (x : real) (y : real) : term72 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1660297 (x : real) (y : real) : term291 x y.
Proof. exact (@lem1660296 term51 (term256 x y)). Qed.
Lemma lem1660298 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term292 x y.
Proof. exact (@lem1660297 x y (@lem1660294 n x y h1)). Qed.
Lemma lem1660299 (x : real) (y : real) : (term293 x y) = (term256 x y).
Proof. exact (@lem1483460 (term256 x y)). Qed.
Lemma lem1660300 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1660301 (x : real) (y : real) : (term294 x y) = (term258 x y).
Proof. exact (MK_COMB (@lem1660300) (@lem1660299 x y)). Qed.
Lemma lem1660302 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660303 (x : real) (y : real) : (term292 x y) = (term259 x y).
Proof. exact (MK_COMB (@lem1660301 x y) (@lem1660302)). Qed.
Lemma lem1660304 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term259 x y.
Proof. exact (EQ_MP (@lem1660303 x y) (@lem1660298 n x y h1)). Qed.
Lemma lem1660305 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term295 x y.
Proof. exact (conj (@lem1660304 n x y h1) (@lem1660283 n x y h1)). Qed.
Lemma lem1660307 (x : real) (y : real) : term77 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1660308 (x : real) (y : real) : term296 x y.
Proof. exact (@lem1660307 (term256 x y) (term255 x y)). Qed.
Lemma lem1660309 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term297 x y.
Proof. exact (@lem1660308 x y (@lem1660305 n x y h1)). Qed.
Lemma lem1660310 (x : real) (y : real) : (term298 x y) = (term299 x y).
Proof. exact (@lem1483480 (term31 x) x y (term31 y)). Qed.
Lemma lem1660311 (x : real) : (term80 x) = (term81 x).
Proof. exact (@lem1483440 term43 x). Qed.
Lemma lem1660313 (m : nat) : (term82 m) = term28.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1660314 : term83 = term28.
Proof. exact (@lem1660313 term48). Qed.
Lemma lem1660315 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1660316 : term84 = term85.
Proof. exact (MK_COMB (@lem1660315) (@lem1660314)). Qed.
Lemma lem1660317 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1660318 (x : real) : (term81 x) = (term86 x).
Proof. exact (MK_COMB (@lem1660316) (@lem1660317 x)). Qed.
Lemma lem1660319 (x : real) : (term80 x) = (term86 x).
Proof. exact (TRANS (@lem1660311 x) (@lem1660318 x)). Qed.
Lemma lem1660320 (x : real) : (term86 x) = term28.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1660321 (x : real) : (term80 x) = term28.
Proof. exact (TRANS (@lem1660319 x) (@lem1660320 x)). Qed.
Lemma lem1660322 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1660323 (x : real) : (term300 x) = term55.
Proof. exact (MK_COMB (@lem1660322) (@lem1660321 x)). Qed.
Lemma lem1660324 (y : real) : (term301 y) = (term81 y).
Proof. exact (@lem1483442 term43 y). Qed.
Lemma lem1660326 (m : nat) : (term82 m) = term28.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1660327 : term83 = term28.
Proof. exact (@lem1660326 term48). Qed.
Lemma lem1660328 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1660329 : term84 = term85.
Proof. exact (MK_COMB (@lem1660328) (@lem1660327)). Qed.
Lemma lem1660330 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1660331 (y : real) : (term81 y) = (term86 y).
Proof. exact (MK_COMB (@lem1660329) (@lem1660330 y)). Qed.
Lemma lem1660332 (y : real) : (term301 y) = (term86 y).
Proof. exact (TRANS (@lem1660324 y) (@lem1660331 y)). Qed.
Lemma lem1660333 (y : real) : (term86 y) = term28.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1660334 (y : real) : (term301 y) = term28.
Proof. exact (TRANS (@lem1660332 y) (@lem1660333 y)). Qed.
Lemma lem1660335 (x : real) (y : real) : (term299 x y) = term302.
Proof. exact (MK_COMB (@lem1660323 x) (@lem1660334 y)). Qed.
Lemma lem1660336 (x : real) (y : real) : (term298 x y) = term302.
Proof. exact (TRANS (@lem1660310 x y) (@lem1660335 x y)). Qed.
Lemma lem1660337 : term302 = term28.
Proof. exact (@lem1483448 term28). Qed.
Lemma lem1660338 (x : real) (y : real) : (term298 x y) = term28.
Proof. exact (TRANS (@lem1660336 x y) (@lem1660337)). Qed.
Lemma lem1660339 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1660340 (x : real) (y : real) : (term303 x y) = term88.
Proof. exact (MK_COMB (@lem1660339) (@lem1660338 x y)). Qed.
Lemma lem1660341 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660342 (x : real) (y : real) : (term297 x y) = term89.
Proof. exact (MK_COMB (@lem1660340 x y) (@lem1660341)). Qed.
Lemma lem1660343 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term89.
Proof. exact (EQ_MP (@lem1660342 x y) (@lem1660309 n x y h1)). Qed.
Lemma lem1660345 (n : nat) (m : nat) : (term62 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1660346 : term89 = term90.
Proof. exact (@lem1660345 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1660347 : term90 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1660348 : term89 = False.
Proof. exact (TRANS (@lem1660346) (@lem1660347)). Qed.
Lemma lem1660349 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : False.
Proof. exact (EQ_MP (@lem1660348) (@lem1660343 n x y h1)). Qed.
Lemma lem1660351 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : term284 n x y.
Proof. exact (h1). Qed.
Lemma lem1660352 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : (term284 n x y) = False.
Proof. exact (prop_ext (fun h2 : term284 n x y => @lem1660349 n x y h1) (fun h2 : False => @lem1660351 n x y h1)). Qed.
Lemma lem1660353 (n : nat) (x : real) (y : real) (h1 : term284 n x y) : False.
Proof. exact (EQ_MP (@lem1660352 n x y h1) (@lem1660351 n x y h1)). Qed.
Lemma lem1660354 (n : nat) (y : real) (x : real) (h1 : term252 n y x) : term252 n y x.
Proof. exact (h1). Qed.
Lemma lem1660355 (n : nat) (y : real) (x : real) (h1 : term252 n y x) : term284 n x y.
Proof. exact (EQ_MP (@lem1660250 n x y) (@lem1660354 n y x h1)). Qed.
Lemma lem1660356 (n : nat) (y : real) (x : real) (h1 : term252 n y x) : (term284 n x y) = False.
Proof. exact (prop_ext (fun h2 : term284 n x y => @lem1660353 n x y h2) (fun h2 : False => @lem1660355 n y x h1)). Qed.
Lemma lem1660357 (n : nat) (y : real) (x : real) (h1 : term252 n y x) : False.
Proof. exact (EQ_MP (@lem1660356 n y x h1) (@lem1660355 n y x h1)). Qed.
Lemma lem1660358 (n : nat) (y : real) (x : real) : term304 n y x.
Proof. exact (fun h0 : term252 n y x => @lem1660357 n y x h0). Qed.
Lemma lem1660359 (n : nat) (y : real) (x : real) : term305 n y x.
Proof. exact (@lem1386578 (term306 n y x)). Qed.
Lemma lem1660360 (n : nat) (y : real) (x : real) : term306 n y x.
Proof. exact (@lem1660359 n y x (@lem1660358 n y x)). Qed.
Lemma lem1660384 (x : real) (y : real) (n : nat) : (term307 x y n) = (term308 x y n).
Proof. exact (@lem17362 (term234 y x n) (term13 x y n)). Qed.
Lemma lem1660386 (y : real) : (term227 y) = (term227 y).
Proof. exact (eq_refl (term227 y)). Qed.
Lemma lem1660387 (x : real) (y : real) (n : nat) : (term309 x y n) = (term310 x y n).
Proof. exact (MK_COMB (@lem1660386 y) (@lem1660384 x y n)). Qed.
Lemma lem1660388 (x : real) (y : real) (n : nat) : (term311 x y n) = (term309 x y n).
Proof. exact (@lem17362 (term96 y) (term238 x y n)). Qed.
Lemma lem1660389 (x : real) (y : real) (n : nat) : (term311 x y n) = (term310 x y n).
Proof. exact (TRANS (@lem1660388 x y n) (@lem1660387 x y n)). Qed.
Lemma lem1660391 (n : nat) : (term241 n) = (term241 n).
Proof. exact (eq_refl (term241 n)). Qed.
Lemma lem1660392 (x : real) (y : real) (n : nat) : (term312 x y n) = (term313 x y n).
Proof. exact (MK_COMB (@lem1660391 n) (@lem1660389 x y n)). Qed.
Lemma lem1660393 (x : real) (y : real) (n : nat) : (term314 x y n) = (term312 x y n).
Proof. exact (@lem17362 (Coq.Arith.PeanoNat.Nat.Odd n) (term315 x y n)). Qed.
Lemma lem1660394 (x : real) (y : real) (n : nat) : (term314 x y n) = (term313 x y n).
Proof. exact (TRANS (@lem1660393 x y n) (@lem1660392 x y n)). Qed.
Lemma lem1660396 (x : real) (y : real) : (term106 x y) = (term106 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1660397 (x : real) (y : real) (n : nat) : (term316 x y n) = (term317 x y n).
Proof. exact (MK_COMB (@lem1660396 x y) (@lem1660394 x y n)). Qed.
Lemma lem1660398 (x : real) (y : real) (n : nat) : (term318 x y n) = (term316 x y n).
Proof. exact (@lem17362 (real_lt x y) (term319 x y n)). Qed.
Lemma lem1660399 (x : real) (y : real) (n : nat) : (term318 x y n) = (term317 x y n).
Proof. exact (TRANS (@lem1660398 x y n) (@lem1660397 x y n)). Qed.
Lemma lem1660401 (n : nat) : (term118 n) = (term118 n).
Proof. exact (eq_refl (term118 n)). Qed.
Lemma lem1660402 (x : real) (y : real) (n : nat) : (term320 x y n) = (term321 x y n).
Proof. exact (MK_COMB (@lem1660401 n) (@lem1660399 x y n)). Qed.
Lemma lem1660403 (x : real) (y : real) (n : nat) : (term322 x y n) = (term320 x y n).
Proof. exact (@lem17362 (term99 n) (term323 x y n)). Qed.
Lemma lem1660431 (x : real) (y : real) (n : nat) : (term322 x y n) = (term321 x y n).
Proof. exact (TRANS (@lem1660403 x y n) (@lem1660402 x y n)). Qed.
Lemma lem1660433 (y : real) (x : real) : (real_lt x y) = (term254 y x).
Proof. exact (@lem1483521 y x). Qed.
Lemma lem1660439 (y : real) (x : real) : (real_sub y x) = (term255 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1660444 (x : real) (y : real) : (term255 y x) = (term256 x y).
Proof. exact (@lem1483488 (term31 x) y). Qed.
Lemma lem1660446 (x : real) (y : real) : (real_sub y x) = (term256 x y).
Proof. exact (TRANS (@lem1660439 y x) (@lem1660444 x y)). Qed.
Lemma lem1660447 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1660448 (x : real) (y : real) : (term257 y x) = (term258 x y).
Proof. exact (MK_COMB (@lem1660447) (@lem1660446 x y)). Qed.
Lemma lem1660449 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660450 (x : real) (y : real) : (term254 y x) = (term259 x y).
Proof. exact (MK_COMB (@lem1660448 x y) (@lem1660449)). Qed.
Lemma lem1660451 (x : real) (y : real) : (real_lt x y) = (term259 x y).
Proof. exact (TRANS (@lem1660433 y x) (@lem1660450 x y)). Qed.
Lemma lem1660453 (y : real) : (term96 y) = (term260 y).
Proof. exact (@lem1483523 (real_neg y) term28). Qed.
Lemma lem1660454 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660461 (y : real) : (real_neg y) = (term31 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1660462 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1660463 (y : real) : (term261 y) = (term262 y).
Proof. exact (MK_COMB (@lem1660462) (@lem1660461 y)). Qed.
Lemma lem1660464 (y : real) : (term263 y) = (term264 y).
Proof. exact (MK_COMB (@lem1660463 y) (@lem1660454)). Qed.
Lemma lem1660465 (y : real) : (term264 y) = (term265 y).
Proof. exact (@lem1483519 (term31 y) term28). Qed.
Lemma lem1660467 (x : nat) : (term166 x) = term28.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1660468 : term167 = term28.
Proof. exact (@lem1660467 term48). Qed.
Lemma lem1660469 (y : real) : (term266 y) = (term266 y).
Proof. exact (eq_refl (term266 y)). Qed.
Lemma lem1660470 (y : real) : (term265 y) = (term267 y).
Proof. exact (MK_COMB (@lem1660469 y) (@lem1660468)). Qed.
Lemma lem1660471 (y : real) : (term267 y) = (term31 y).
Proof. exact (@lem1483450 (term31 y)). Qed.
Lemma lem1660472 (y : real) : (term265 y) = (term31 y).
Proof. exact (TRANS (@lem1660470 y) (@lem1660471 y)). Qed.
Lemma lem1660473 (y : real) : (term264 y) = (term31 y).
Proof. exact (TRANS (@lem1660465 y) (@lem1660472 y)). Qed.
Lemma lem1660474 (y : real) : (term263 y) = (term31 y).
Proof. exact (TRANS (@lem1660464 y) (@lem1660473 y)). Qed.
Lemma lem1660475 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1660476 (y : real) : (term268 y) = (term269 y).
Proof. exact (MK_COMB (@lem1660475) (@lem1660474 y)). Qed.
Lemma lem1660477 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660478 (y : real) : (term260 y) = (term270 y).
Proof. exact (MK_COMB (@lem1660476 y) (@lem1660477)). Qed.
Lemma lem1660479 (y : real) : (term96 y) = (term270 y).
Proof. exact (TRANS (@lem1660453 y) (@lem1660478 y)). Qed.
Lemma lem1660480 (x : real) (y : real) (n : nat) : (term234 y x n) = (term324 x y n).
Proof. exact (@lem1483521 (term147 x n) (term147 y n)). Qed.
Lemma lem1660487 (y : real) (n : nat) : (term147 y n) = (term160 y n).
Proof. exact (@lem1483512 (real_pow y n)). Qed.
Lemma lem1660494 (x : real) (n : nat) : (term147 x n) = (term160 x n).
Proof. exact (@lem1483512 (real_pow x n)). Qed.
Lemma lem1660495 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1660496 (x : real) (n : nat) : (term161 x n) = (term162 x n).
Proof. exact (MK_COMB (@lem1660495) (@lem1660494 x n)). Qed.
Lemma lem1660497 (x : real) (y : real) (n : nat) : (term325 x y n) = (term326 x y n).
Proof. exact (MK_COMB (@lem1660496 x n) (@lem1660487 y n)). Qed.
Lemma lem1660498 (x : real) (y : real) (n : nat) : (term326 x y n) = (term327 x y n).
Proof. exact (@lem1483519 (term160 x n) (term160 y n)). Qed.
Lemma lem1660499 (y : real) (n : nat) : (term328 y n) = (term329 y n).
Proof. exact (@lem1483476 term43 term43 (real_pow y n)). Qed.
Lemma lem1660501 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1660502 : term46 = term47.
Proof. exact (@lem1660501 term48 term48). Qed.
Lemma lem1660503 : (term49 = (BIT1 0)) = (term50 = term48).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1660504 : term50 = term48.
Proof. exact (EQ_MP (@lem1660503) (@lem940073)). Qed.
Lemma lem1660505 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1660506 : term47 = term51.
Proof. exact (MK_COMB (@lem1660505) (@lem1660504)). Qed.
Lemma lem1660507 : term46 = term51.
Proof. exact (TRANS (@lem1660502) (@lem1660506)). Qed.
Lemma lem1660508 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1660509 : term52 = term53.
Proof. exact (MK_COMB (@lem1660508) (@lem1660507)). Qed.
Lemma lem1660510 (y : real) (n : nat) : (real_pow y n) = (real_pow y n).
Proof. exact (eq_refl (real_pow y n)). Qed.
Lemma lem1660511 (y : real) (n : nat) : (term329 y n) = (term196 y n).
Proof. exact (MK_COMB (@lem1660509) (@lem1660510 y n)). Qed.
Lemma lem1660512 (y : real) (n : nat) : (term328 y n) = (term196 y n).
Proof. exact (TRANS (@lem1660499 y n) (@lem1660511 y n)). Qed.
Lemma lem1660513 (y : real) (n : nat) : (term196 y n) = (real_pow y n).
Proof. exact (@lem1483436 (real_pow y n)). Qed.
Lemma lem1660514 (y : real) (n : nat) : (term328 y n) = (real_pow y n).
Proof. exact (TRANS (@lem1660512 y n) (@lem1660513 y n)). Qed.
Lemma lem1660515 (x : real) (n : nat) : (term168 x n) = (term168 x n).
Proof. exact (eq_refl (term168 x n)). Qed.
Lemma lem1660518 (x : real) (y : real) (n : nat) : (term327 x y n) = (term330 x y n).
Proof. exact (MK_COMB (@lem1660515 x n) (@lem1660514 y n)). Qed.
Lemma lem1660519 (x : real) (y : real) (n : nat) : (term326 x y n) = (term330 x y n).
Proof. exact (TRANS (@lem1660498 x y n) (@lem1660518 x y n)). Qed.
Lemma lem1660520 (x : real) (y : real) (n : nat) : (term325 x y n) = (term330 x y n).
Proof. exact (TRANS (@lem1660497 x y n) (@lem1660519 x y n)). Qed.
Lemma lem1660521 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1660522 (x : real) (y : real) (n : nat) : (term331 x y n) = (term332 x y n).
Proof. exact (MK_COMB (@lem1660521) (@lem1660520 x y n)). Qed.
Lemma lem1660523 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660524 (x : real) (y : real) (n : nat) : (term324 x y n) = (term333 x y n).
Proof. exact (MK_COMB (@lem1660522 x y n) (@lem1660523)). Qed.
Lemma lem1660525 (x : real) (y : real) (n : nat) : (term234 y x n) = (term333 x y n).
Proof. exact (TRANS (@lem1660480 x y n) (@lem1660524 x y n)). Qed.
Lemma lem1660526 (x : real) (y : real) (n : nat) : (term183 x y n) = (term184 x y n).
Proof. exact (@lem1483531 (real_pow x n) (real_pow y n)). Qed.
Lemma lem1660539 (x : real) (y : real) (n : nat) : (term185 x y n) = (term186 x y n).
Proof. exact (@lem1483519 (real_pow x n) (real_pow y n)). Qed.
Lemma lem1660540 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1660541 (x : real) (y : real) (n : nat) : (term187 x y n) = (term188 x y n).
Proof. exact (MK_COMB (@lem1660540) (@lem1660539 x y n)). Qed.
Lemma lem1660542 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660543 (x : real) (y : real) (n : nat) : (term184 x y n) = (term189 x y n).
Proof. exact (MK_COMB (@lem1660541 x y n) (@lem1660542)). Qed.
Lemma lem1660544 (x : real) (y : real) (n : nat) : (term183 x y n) = (term189 x y n).
Proof. exact (TRANS (@lem1660526 x y n) (@lem1660543 x y n)). Qed.
Lemma lem1660545 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1660546 (x : real) (y : real) (n : nat) : (term334 y x n) = (term335 x y n).
Proof. exact (MK_COMB (@lem1660545) (@lem1660525 x y n)). Qed.
Lemma lem1660547 (x : real) (y : real) (n : nat) : (term308 x y n) = (term336 x y n).
Proof. exact (MK_COMB (@lem1660546 x y n) (@lem1660544 x y n)). Qed.
Lemma lem1660548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1660549 (y : real) : (term227 y) = (term279 y).
Proof. exact (MK_COMB (@lem1660548) (@lem1660479 y)). Qed.
Lemma lem1660550 (x : real) (y : real) (n : nat) : (term310 x y n) = (term337 x y n).
Proof. exact (MK_COMB (@lem1660549 y) (@lem1660547 x y n)). Qed.
Lemma lem1660552 (n : nat) : (term241 n) = (term241 n).
Proof. exact (eq_refl (term241 n)). Qed.
Lemma lem1660553 (x : real) (y : real) (n : nat) : (term313 x y n) = (term338 x y n).
Proof. exact (MK_COMB (@lem1660552 n) (@lem1660550 x y n)). Qed.
Lemma lem1660554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1660555 (x : real) (y : real) : (term106 x y) = (term282 x y).
Proof. exact (MK_COMB (@lem1660554) (@lem1660451 x y)). Qed.
Lemma lem1660556 (x : real) (y : real) (n : nat) : (term317 x y n) = (term339 x y n).
Proof. exact (MK_COMB (@lem1660555 x y) (@lem1660553 x y n)). Qed.
Lemma lem1660558 (n : nat) : (term118 n) = (term118 n).
Proof. exact (eq_refl (term118 n)). Qed.
Lemma lem1660559 (x : real) (y : real) (n : nat) : (term321 x y n) = (term340 x y n).
Proof. exact (MK_COMB (@lem1660558 n) (@lem1660556 x y n)). Qed.
Lemma lem1660598 (x : real) (y : real) (n : nat) : (term322 x y n) = (term340 x y n).
Proof. exact (TRANS (@lem1660431 x y n) (@lem1660559 x y n)). Qed.
Lemma lem1660602 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term340 x y n.
Proof. exact (h1). Qed.
Lemma lem1660603 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term339 x y n.
Proof. exact (proj2 (@lem1660602 x y n h1)). Qed.
Lemma lem1660605 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term338 x y n.
Proof. exact (proj2 (@lem1660603 x y n h1)). Qed.
Lemma lem1660607 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term337 x y n.
Proof. exact (proj2 (@lem1660605 x y n h1)). Qed.
Lemma lem1660609 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term336 x y n.
Proof. exact (proj2 (@lem1660607 x y n h1)). Qed.
Lemma lem1660611 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term189 x y n.
Proof. exact (proj2 (@lem1660609 x y n h1)). Qed.
Lemma lem1660612 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term333 x y n.
Proof. exact (proj1 (@lem1660609 x y n h1)). Qed.
Lemma lem1660614 (n : nat) (m : nat) : (term62 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1660615 : term63 = term64.
Proof. exact (@lem1660614 (NUMERAL 0) term48). Qed.
Lemma lem1660616 : term65 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1660617 (h1 : term65 = (BIT1 0)) : term64 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1660618 : (term65 = (BIT1 0)) = (term64 = True).
Proof. exact (prop_ext (fun h1 : term65 = (BIT1 0) => @lem1660617 h1) (fun h1 : term64 = True => @lem1660616)). Qed.
Lemma lem1660619 : term64 = True.
Proof. exact (EQ_MP (@lem1660618) (@lem1660616)). Qed.
Lemma lem1660620 : term63 = True.
Proof. exact (TRANS (@lem1660615) (@lem1660619)). Qed.
Lemma lem1660621 : True = term63.
Proof. exact (SYM (@lem1660620)). Qed.
Lemma lem1660622 : term63.
Proof. exact (EQ_MP (@lem1660621) (@lem0)). Qed.
Lemma lem1660623 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term198 x y n.
Proof. exact (conj (@lem1660622) (@lem1660611 x y n h1)). Qed.
Lemma lem1660625 (x : real) (y : real) : term67 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1660626 (x : real) (y : real) (n : nat) : term199 x y n.
Proof. exact (@lem1660625 term51 (term186 x y n)). Qed.
Lemma lem1660627 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term200 x y n.
Proof. exact (@lem1660626 x y n (@lem1660623 x y n h1)). Qed.
Lemma lem1660628 (x : real) (y : real) (n : nat) : (term201 x y n) = (term186 x y n).
Proof. exact (@lem1483460 (term186 x y n)). Qed.
Lemma lem1660629 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1660630 (x : real) (y : real) (n : nat) : (term202 x y n) = (term188 x y n).
Proof. exact (MK_COMB (@lem1660629) (@lem1660628 x y n)). Qed.
Lemma lem1660631 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660632 (x : real) (y : real) (n : nat) : (term200 x y n) = (term189 x y n).
Proof. exact (MK_COMB (@lem1660630 x y n) (@lem1660631)). Qed.
Lemma lem1660633 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term189 x y n.
Proof. exact (EQ_MP (@lem1660632 x y n) (@lem1660627 x y n h1)). Qed.
Lemma lem1660635 (n : nat) (m : nat) : (term62 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1660636 : term63 = term64.
Proof. exact (@lem1660635 (NUMERAL 0) term48). Qed.
Lemma lem1660637 : term65 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1660638 (h1 : term65 = (BIT1 0)) : term64 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1660639 : (term65 = (BIT1 0)) = (term64 = True).
Proof. exact (prop_ext (fun h1 : term65 = (BIT1 0) => @lem1660638 h1) (fun h1 : term64 = True => @lem1660637)). Qed.
Lemma lem1660640 : term64 = True.
Proof. exact (EQ_MP (@lem1660639) (@lem1660637)). Qed.
Lemma lem1660641 : term63 = True.
Proof. exact (TRANS (@lem1660636) (@lem1660640)). Qed.
Lemma lem1660642 : True = term63.
Proof. exact (SYM (@lem1660641)). Qed.
Lemma lem1660643 : term63.
Proof. exact (EQ_MP (@lem1660642) (@lem0)). Qed.
Lemma lem1660644 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term341 x y n.
Proof. exact (conj (@lem1660643) (@lem1660612 x y n h1)). Qed.
Lemma lem1660646 (x : real) (y : real) : term72 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1660647 (x : real) (y : real) (n : nat) : term342 x y n.
Proof. exact (@lem1660646 term51 (term330 x y n)). Qed.
Lemma lem1660648 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term343 x y n.
Proof. exact (@lem1660647 x y n (@lem1660644 x y n h1)). Qed.
Lemma lem1660649 (x : real) (y : real) (n : nat) : (term344 x y n) = (term330 x y n).
Proof. exact (@lem1483460 (term330 x y n)). Qed.
Lemma lem1660650 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1660651 (x : real) (y : real) (n : nat) : (term345 x y n) = (term332 x y n).
Proof. exact (MK_COMB (@lem1660650) (@lem1660649 x y n)). Qed.
Lemma lem1660652 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660653 (x : real) (y : real) (n : nat) : (term343 x y n) = (term333 x y n).
Proof. exact (MK_COMB (@lem1660651 x y n) (@lem1660652)). Qed.
Lemma lem1660654 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term333 x y n.
Proof. exact (EQ_MP (@lem1660653 x y n) (@lem1660648 x y n h1)). Qed.
Lemma lem1660655 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term336 x y n.
Proof. exact (conj (@lem1660654 x y n h1) (@lem1660633 x y n h1)). Qed.
Lemma lem1660657 (x : real) (y : real) : term77 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1660658 (x : real) (y : real) (n : nat) : term346 x y n.
Proof. exact (@lem1660657 (term330 x y n) (term186 x y n)). Qed.
Lemma lem1660659 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term347 x y n.
Proof. exact (@lem1660658 x y n (@lem1660655 x y n h1)). Qed.
Lemma lem1660660 (x : real) (y : real) (n : nat) : (term348 x y n) = (term349 x y n).
Proof. exact (@lem1483480 (term160 x n) (real_pow x n) (real_pow y n) (term160 y n)). Qed.
Lemma lem1660661 (x : real) (n : nat) : (term213 x n) = (term214 x n).
Proof. exact (@lem1483440 term43 (real_pow x n)). Qed.
Lemma lem1660663 (m : nat) : (term82 m) = term28.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1660664 : term83 = term28.
Proof. exact (@lem1660663 term48). Qed.
Lemma lem1660665 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1660666 : term84 = term85.
Proof. exact (MK_COMB (@lem1660665) (@lem1660664)). Qed.
Lemma lem1660667 (x : real) (n : nat) : (real_pow x n) = (real_pow x n).
Proof. exact (eq_refl (real_pow x n)). Qed.
Lemma lem1660668 (x : real) (n : nat) : (term214 x n) = (term215 x n).
Proof. exact (MK_COMB (@lem1660666) (@lem1660667 x n)). Qed.
Lemma lem1660669 (x : real) (n : nat) : (term213 x n) = (term215 x n).
Proof. exact (TRANS (@lem1660661 x n) (@lem1660668 x n)). Qed.
Lemma lem1660670 (x : real) (n : nat) : (term215 x n) = term28.
Proof. exact (@lem1483446 (real_pow x n)). Qed.
Lemma lem1660671 (x : real) (n : nat) : (term213 x n) = term28.
Proof. exact (TRANS (@lem1660669 x n) (@lem1660670 x n)). Qed.
Lemma lem1660672 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1660673 (x : real) (n : nat) : (term216 x n) = term55.
Proof. exact (MK_COMB (@lem1660672) (@lem1660671 x n)). Qed.
Lemma lem1660674 (y : real) (n : nat) : (term350 y n) = (term214 y n).
Proof. exact (@lem1483442 term43 (real_pow y n)). Qed.
Lemma lem1660676 (m : nat) : (term82 m) = term28.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1660677 : term83 = term28.
Proof. exact (@lem1660676 term48). Qed.
Lemma lem1660678 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1660679 : term84 = term85.
Proof. exact (MK_COMB (@lem1660678) (@lem1660677)). Qed.
Lemma lem1660680 (y : real) (n : nat) : (real_pow y n) = (real_pow y n).
Proof. exact (eq_refl (real_pow y n)). Qed.
Lemma lem1660681 (y : real) (n : nat) : (term214 y n) = (term215 y n).
Proof. exact (MK_COMB (@lem1660679) (@lem1660680 y n)). Qed.
Lemma lem1660682 (y : real) (n : nat) : (term350 y n) = (term215 y n).
Proof. exact (TRANS (@lem1660674 y n) (@lem1660681 y n)). Qed.
Lemma lem1660683 (y : real) (n : nat) : (term215 y n) = term28.
Proof. exact (@lem1483446 (real_pow y n)). Qed.
Lemma lem1660684 (y : real) (n : nat) : (term350 y n) = term28.
Proof. exact (TRANS (@lem1660682 y n) (@lem1660683 y n)). Qed.
Lemma lem1660685 (x : real) (y : real) (n : nat) : (term349 x y n) = term302.
Proof. exact (MK_COMB (@lem1660673 x n) (@lem1660684 y n)). Qed.
Lemma lem1660686 (x : real) (y : real) (n : nat) : (term348 x y n) = term302.
Proof. exact (TRANS (@lem1660660 x y n) (@lem1660685 x y n)). Qed.
Lemma lem1660687 : term302 = term28.
Proof. exact (@lem1483448 term28). Qed.
Lemma lem1660688 (x : real) (y : real) (n : nat) : (term348 x y n) = term28.
Proof. exact (TRANS (@lem1660686 x y n) (@lem1660687)). Qed.
Lemma lem1660689 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1660690 (x : real) (y : real) (n : nat) : (term351 x y n) = term88.
Proof. exact (MK_COMB (@lem1660689) (@lem1660688 x y n)). Qed.
Lemma lem1660691 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1660692 (x : real) (y : real) (n : nat) : (term347 x y n) = term89.
Proof. exact (MK_COMB (@lem1660690 x y n) (@lem1660691)). Qed.
Lemma lem1660693 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term89.
Proof. exact (EQ_MP (@lem1660692 x y n) (@lem1660659 x y n h1)). Qed.
Lemma lem1660695 (n : nat) (m : nat) : (term62 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1660696 : term89 = term90.
Proof. exact (@lem1660695 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1660697 : term90 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1660698 : term89 = False.
Proof. exact (TRANS (@lem1660696) (@lem1660697)). Qed.
Lemma lem1660699 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : False.
Proof. exact (EQ_MP (@lem1660698) (@lem1660693 x y n h1)). Qed.
Lemma lem1660701 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : term340 x y n.
Proof. exact (h1). Qed.
Lemma lem1660702 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : (term340 x y n) = False.
Proof. exact (prop_ext (fun h2 : term340 x y n => @lem1660699 x y n h1) (fun h2 : False => @lem1660701 x y n h1)). Qed.
Lemma lem1660703 (x : real) (y : real) (n : nat) (h1 : term340 x y n) : False.
Proof. exact (EQ_MP (@lem1660702 x y n h1) (@lem1660701 x y n h1)). Qed.
Lemma lem1660704 (x : real) (y : real) (n : nat) (h1 : term322 x y n) : term322 x y n.
Proof. exact (h1). Qed.
Lemma lem1660705 (x : real) (y : real) (n : nat) (h1 : term322 x y n) : term340 x y n.
Proof. exact (EQ_MP (@lem1660598 x y n) (@lem1660704 x y n h1)). Qed.
Lemma lem1660706 (x : real) (y : real) (n : nat) (h1 : term322 x y n) : (term340 x y n) = False.
Proof. exact (prop_ext (fun h2 : term340 x y n => @lem1660703 x y n h2) (fun h2 : False => @lem1660705 x y n h1)). Qed.
Lemma lem1660707 (x : real) (y : real) (n : nat) (h1 : term322 x y n) : False.
Proof. exact (EQ_MP (@lem1660706 x y n h1) (@lem1660705 x y n h1)). Qed.
Lemma lem1660708 (x : real) (y : real) (n : nat) : term352 x y n.
Proof. exact (fun h0 : term322 x y n => @lem1660707 x y n h0). Qed.
Lemma lem1660709 (x : real) (y : real) (n : nat) : term353 x y n.
Proof. exact (@lem1386578 (term354 x y n)). Qed.
Lemma lem1660710 (x : real) (y : real) (n : nat) : term354 x y n.
Proof. exact (@lem1660709 x y n (@lem1660708 x y n)). Qed.
Lemma lem1660711 (x : real) (y : real) (n : nat) (h1 : term99 n) : term323 x y n.
Proof. exact (@lem1660710 x y n (@lem1657973 n h1)). Qed.
Lemma lem1660712 (n : nat) (x : real) (y : real) (h1 : term99 n) (h2 : real_lt x y) : term319 x y n.
Proof. exact (@lem1660711 x y n h1 (@lem1659324 x y h2)). Qed.
Lemma lem1660713 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : real_lt x y) : term315 x y n.
Proof. exact (@lem1660712 n x y h2 h3 (@lem1659323 n h1)). Qed.
Lemma lem1660714 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : term96 y) (h4 : real_lt x y) : term238 x y n.
Proof. exact (@lem1660713 n x y h1 h2 h4 (@lem1657968 y h3)). Qed.
Lemma lem1660715 (y : real) (x : real) (n : nat) (h1 : term99 n) : term253 n y x.
Proof. exact (@lem1660360 n y x (@lem1657973 n h1)). Qed.
Lemma lem1660716 (n : nat) (x : real) (y : real) (h1 : term99 n) (h2 : real_lt x y) : term249 n y x.
Proof. exact (@lem1660715 y x n h1 (@lem1659324 x y h2)). Qed.
Lemma lem1660717 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : real_lt x y) : term245 y x.
Proof. exact (@lem1660716 n x y h2 h3 (@lem1659323 n h1)). Qed.
Lemma lem1660718 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : term96 y) (h4 : real_lt x y) : term228 y x.
Proof. exact (@lem1660717 n x y h1 h2 h4 (@lem1657968 y h3)). Qed.
Lemma lem1660719 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : term96 y) (h4 : real_lt x y) : term237 x y n.
Proof. exact (EQ_MP (@lem1660052 x y n h1) (@lem1660714 n x y h1 h2 h3 h4)). Qed.
Lemma lem1660720 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : term96 y) (h4 : real_lt x y) : term231 n y x.
Proof. exact (EQ_MP (@lem1659963 x n y h2 h3) (@lem1660718 n x y h1 h2 h3 h4)). Qed.
Lemma lem1660721 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : term96 y) (h4 : real_lt x y) : term225 y x n.
Proof. exact (@lem1659915 y x n (@lem1660720 n x y h1 h2 h3 h4)). Qed.
Lemma lem1660722 (y : real) (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : term96 y) (h4 : real_lt x y) (h5 : term225 y x n) : term13 x y n.
Proof. exact (@lem1660719 n x y h1 h2 h3 h4 (@lem1659912 y x n h5)). Qed.
Lemma lem1660723 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : term96 y) (h4 : real_lt x y) : (term225 y x n) = (term13 x y n).
Proof. exact (prop_ext (fun h5 : term225 y x n => @lem1660722 y x n h1 h2 h3 h4 h5) (fun h5 : term13 x y n => @lem1660721 n x y h1 h2 h3 h4)). Qed.
Lemma lem1660724 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : term96 y) (h4 : real_lt x y) : term13 x y n.
Proof. exact (EQ_MP (@lem1660723 n x y h1 h2 h3 h4) (@lem1660721 n x y h1 h2 h3 h4)). Qed.
Lemma lem1660725 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : real_lt x y) : term13 x y n.
Proof. exact (or_elim (@lem1657966 y) (fun h0 : term24 y => @lem1659911 n x y h1 h2 h0 h3) (fun h0 : term96 y => @lem1660724 n x y h1 h2 h0 h3)). Qed.
Lemma lem1660726 (x : real) (y : real) (n : nat) (h1 : term107 x y n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (proj2 (@lem1659322 x y n h1)). Qed.
Lemma lem1660727 (x : real) (y : real) (n : nat) (h1 : term107 x y n) : real_lt x y.
Proof. exact (proj1 (@lem1659322 x y n h1)). Qed.
Lemma lem1660728 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : real_lt x y) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term13 x y n).
Proof. exact (prop_ext (fun h4 : Coq.Arith.PeanoNat.Nat.Odd n => @lem1660725 n x y h1 h2 h3) (fun h4 : term13 x y n => @lem1659323 n h1)). Qed.
Lemma lem1660729 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : real_lt x y) : term13 x y n.
Proof. exact (EQ_MP (@lem1660728 n x y h1 h2 h3) (@lem1659323 n h1)). Qed.
Lemma lem1660730 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : real_lt x y) : (real_lt x y) = (term13 x y n).
Proof. exact (prop_ext (fun h4 : real_lt x y => @lem1660729 n x y h1 h2 h3) (fun h4 : term13 x y n => @lem1659324 x y h3)). Qed.
Lemma lem1660731 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term99 n) (h3 : real_lt x y) : term13 x y n.
Proof. exact (EQ_MP (@lem1660730 n x y h1 h2 h3) (@lem1659324 x y h3)). Qed.
Lemma lem1660732 (n : nat) (x : real) (y : real) (h1 : term99 n) (h2 : term107 x y n) (h3 : real_lt x y) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term13 x y n).
Proof. exact (prop_ext (fun h4 : Coq.Arith.PeanoNat.Nat.Odd n => @lem1660731 n x y h4 h1 h3) (fun h4 : term13 x y n => @lem1660726 x y n h2)). Qed.
Lemma lem1660733 (n : nat) (x : real) (y : real) (h1 : term99 n) (h2 : term107 x y n) (h3 : real_lt x y) : term13 x y n.
Proof. exact (EQ_MP (@lem1660732 n x y h1 h2 h3) (@lem1660726 x y n h2)). Qed.
Lemma lem1660734 (x : real) (y : real) (n : nat) (h1 : term99 n) (h2 : term107 x y n) : (real_lt x y) = (term13 x y n).
Proof. exact (prop_ext (fun h3 : real_lt x y => @lem1660733 n x y h1 h2 h3) (fun h3 : term13 x y n => @lem1660727 x y n h2)). Qed.
Lemma lem1660735 (x : real) (y : real) (n : nat) (h1 : term99 n) (h2 : term107 x y n) : term13 x y n.
Proof. exact (EQ_MP (@lem1660734 x y n h1 h2) (@lem1660727 x y n h2)). Qed.
Lemma lem1660737 (x : real) (y : real) (n : nat) (h1 : term99 n) : term114 x y n.
Proof. exact (fun h0 : term107 x y n => @lem1660735 x y n h1 h0). Qed.
Lemma lem1660738 (x : real) (y : real) (n : nat) : term114 x y n.
Proof. exact (or_elim (@lem1657971 n) (fun h0 : n = (NUMERAL 0) => @lem1658658 x y n h0) (fun h0 : term99 n => @lem1660737 x y n h0)). Qed.
Lemma lem1660743 (x : real) (n : nat) : term355 x n.
Proof. exact (fun y : real => @lem1660738 x y n). Qed.
Lemma lem1660748 (n : nat) : term356 n.
Proof. exact (fun x : real => @lem1660743 x n). Qed.
Lemma lem1660753 : term357.
Proof. exact (fun n : nat => @lem1660748 n). Qed.
