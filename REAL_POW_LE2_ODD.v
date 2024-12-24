Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_LE2_ODD_term_abbrevs.
Require Import REAL_LE_LT_spec.
Require Import REAL_POW_LT2_ODD_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem1660754 (x : real) : term0 x.
Proof. exact (@lem1376325 x). Qed.
Lemma lem1660755 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1660756 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1660755 x) (@lem1660754 x)). Qed.
Lemma lem1660757 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1660756 x y). Qed.
Lemma lem1660758 (x : real) (y : real) : (term2 x y) = ((real_le x y) = (term3 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1660777 (x : real) (y : real) : (real_le x y) = (term3 x y).
Proof. exact (EQ_MP (@lem1660758 x y) (@lem1660757 x y)). Qed.
Lemma lem1660782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1660783 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1660782) (@lem1660777 x y)). Qed.
Lemma lem1660784 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem1660785 (x : real) (y : real) (n : nat) : (term6 x y n) = (term7 x y n).
Proof. exact (MK_COMB (@lem1660783 x y) (@lem1660784 n)). Qed.
Lemma lem1660788 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1660789 (x : real) (y : real) (n : nat) : (term8 x y n) = (term9 x y n).
Proof. exact (MK_COMB (@lem1660788) (@lem1660785 x y n)). Qed.
Lemma lem1660791 (x : real) (y : real) : (real_le x y) = (term3 x y).
Proof. exact (EQ_MP (@lem1660758 x y) (@lem1660757 x y)). Qed.
Lemma lem1660792 (x : real) (y : real) (n : nat) : (term10 x y n) = (term11 x y n).
Proof. exact (@lem1660791 (real_pow x n) (real_pow y n)). Qed.
Lemma lem1660797 (x : real) (y : real) (n : nat) : (term12 x y n) = (term13 x y n).
Proof. exact (MK_COMB (@lem1660789 x y n) (@lem1660792 x y n)). Qed.
Lemma lem1660800 (x : real) (n : nat) : (term14 x n) = (term15 x n).
Proof. exact (fun_ext (fun y : real => @lem1660797 x y n)). Qed.
Lemma lem1660801 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1660802 (x : real) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (MK_COMB (@lem1660801) (@lem1660800 x n)). Qed.
Lemma lem1660807 (n : nat) : (term18 n) = (term19 n).
Proof. exact (fun_ext (fun x : real => @lem1660802 x n)). Qed.
Lemma lem1660808 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1660809 (n : nat) : (term20 n) = (term21 n).
Proof. exact (MK_COMB (@lem1660808) (@lem1660807 n)). Qed.
Lemma lem1660814 : term22 = term23.
Proof. exact (fun_ext (fun n : nat => @lem1660809 n)). Qed.
Lemma lem1660815 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1660816 : term24 = term25.
Proof. exact (MK_COMB (@lem1660815) (@lem1660814)). Qed.
Lemma lem1660821 : term25 = term24.
Proof. exact (SYM (@lem1660816)). Qed.
Lemma lem1660822 (x : real) (y : real) (n : nat) (h1 : term7 x y n) : term7 x y n.
Proof. exact (h1). Qed.
Lemma lem1660823 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem1660824 (x : real) (y : real) (h1 : term3 x y) : term3 x y.
Proof. exact (h1). Qed.
Lemma lem1660825 (x : real) (y : real) (h1 : real_lt x y) : real_lt x y.
Proof. exact (h1). Qed.
Lemma lem1660826 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1660827 (n : nat) : term26 n.
Proof. exact (@lem1660753 n). Qed.
Lemma lem1660828 (n : nat) : (term26 n) = (term27 n).
Proof. exact (eq_refl (term26 n)). Qed.
Lemma lem1660829 (n : nat) : term27 n.
Proof. exact (EQ_MP (@lem1660828 n) (@lem1660827 n)). Qed.
Lemma lem1660830 (n : nat) (x : real) : term28 n x.
Proof. exact (@lem1660829 n x). Qed.
Lemma lem1660831 (x : real) (n : nat) : (term28 n x) = (term29 x n).
Proof. exact (eq_refl (term28 n x)). Qed.
Lemma lem1660832 (x : real) (n : nat) : term29 x n.
Proof. exact (EQ_MP (@lem1660831 x n) (@lem1660830 n x)). Qed.
Lemma lem1660833 (x : real) (n : nat) (y : real) : term30 x n y.
Proof. exact (@lem1660832 x n y). Qed.
Lemma lem1660834 (x : real) (y : real) (n : nat) : (term30 x n y) = (term31 x y n).
Proof. exact (eq_refl (term30 x n y)). Qed.
Lemma lem1660835 (x : real) (y : real) (n : nat) : term31 x y n.
Proof. exact (EQ_MP (@lem1660834 x y n) (@lem1660833 x n y)). Qed.
Lemma lem1660836 (x : real) (y : real) (n : nat) (h1 : term32 x y n) : term32 x y n.
Proof. exact (h1). Qed.
Lemma lem1660837 (x : real) (y : real) (n : nat) (h1 : term32 x y n) : term33 x y n.
Proof. exact (@lem1660835 x y n (@lem1660836 x y n h1)). Qed.
Lemma lem1660838 (x : real) (y : real) (n : nat) : (term33 x y n) = ((term33 x y n) = True).
Proof. exact (@lem7 (term33 x y n)). Qed.
Lemma lem1660839 (x : real) (y : real) (n : nat) (h1 : term32 x y n) : (term33 x y n) = True.
Proof. exact (EQ_MP (@lem1660838 x y n) (@lem1660837 x y n h1)). Qed.
Lemma lem1660845 (x : real) (y : real) : (real_lt x y) = ((real_lt x y) = True).
Proof. exact (@lem7 (real_lt x y)). Qed.
Lemma lem1660847 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem1660852 (x : real) (y : real) (n : nat) : term34 x y n.
Proof. exact (fun h0 : term32 x y n => @lem1660839 x y n h0). Qed.
Lemma lem1660856 (x : real) (y : real) (h1 : real_lt x y) : (real_lt x y) = True.
Proof. exact (EQ_MP (@lem1660845 x y) (@lem1660825 x y h1)). Qed.
Lemma lem1660857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1660858 (x : real) (y : real) (h1 : real_lt x y) : (term35 x y) = (and True).
Proof. exact (MK_COMB (@lem1660857) (@lem1660856 x y h1)). Qed.
Lemma lem1660860 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (Coq.Arith.PeanoNat.Nat.Odd n) = True.
Proof. exact (EQ_MP (@lem1660847 n) (@lem1660823 n h1)). Qed.
Lemma lem1660861 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : real_lt x y) : (term32 x y n) = (True /\ True).
Proof. exact (MK_COMB (@lem1660858 x y h2) (@lem1660860 n h1)). Qed.
Lemma lem1660863 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1660864 : (True /\ True) = True.
Proof. exact (@lem1660863 True). Qed.
Lemma lem1660865 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : real_lt x y) : (term32 x y n) = True.
Proof. exact (TRANS (@lem1660861 n x y h1 h2) (@lem1660864)). Qed.
Lemma lem1660866 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : real_lt x y) : True = (term32 x y n).
Proof. exact (SYM (@lem1660865 n x y h1 h2)). Qed.
Lemma lem1660867 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : real_lt x y) : term32 x y n.
Proof. exact (EQ_MP (@lem1660866 n x y h1 h2) (@lem0)). Qed.
Lemma lem1660868 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : real_lt x y) : (term33 x y n) = True.
Proof. exact (@lem1660852 x y n (@lem1660867 n x y h1 h2)). Qed.
Lemma lem1660869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1660870 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : real_lt x y) : (term36 x y n) = (or True).
Proof. exact (MK_COMB (@lem1660869) (@lem1660868 n x y h1 h2)). Qed.
Lemma lem1660873 (x : real) (y : real) (n : nat) : ((real_pow x n) = (real_pow y n)) = ((real_pow x n) = (real_pow y n)).
Proof. exact (eq_refl ((real_pow x n) = (real_pow y n))). Qed.
Lemma lem1660874 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : real_lt x y) : (term11 x y n) = (term37 x y n).
Proof. exact (MK_COMB (@lem1660870 n x y h1 h2) (@lem1660873 x y n)). Qed.
Lemma lem1660876 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1660877 (x : real) (y : real) (n : nat) : (term37 x y n) = True.
Proof. exact (@lem1660876 ((real_pow x n) = (real_pow y n))). Qed.
Lemma lem1660878 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : real_lt x y) : (term11 x y n) = True.
Proof. exact (TRANS (@lem1660874 n x y h1 h2) (@lem1660877 x y n)). Qed.
Lemma lem1660879 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : real_lt x y) : True = (term11 x y n).
Proof. exact (SYM (@lem1660878 n x y h1 h2)). Qed.
Lemma lem1660880 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : real_lt x y) : term11 x y n.
Proof. exact (EQ_MP (@lem1660879 n x y h1 h2) (@lem0)). Qed.
Lemma lem1660924 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1660925 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem1660926 (x : real) (y : real) (h1 : x = y) : (real_pow x) = (real_pow y).
Proof. exact (MK_COMB (@lem1660925) (@lem1660924 x y h1)). Qed.
Lemma lem1660927 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1660928 (n : nat) (x : real) (y : real) (h1 : x = y) : (real_pow x n) = (real_pow y n).
Proof. exact (MK_COMB (@lem1660926 x y h1) (@lem1660927 n)). Qed.
Lemma lem1660929 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1660930 (n : nat) (x : real) (y : real) (h1 : x = y) : (term38 x n) = (term38 y n).
Proof. exact (MK_COMB (@lem1660929) (@lem1660928 n x y h1)). Qed.
Lemma lem1660931 (y : real) (n : nat) : (real_pow y n) = (real_pow y n).
Proof. exact (eq_refl (real_pow y n)). Qed.
Lemma lem1660932 (n : nat) (x : real) (y : real) (h1 : x = y) : (term33 x y n) = (term39 y n).
Proof. exact (MK_COMB (@lem1660930 n x y h1) (@lem1660931 y n)). Qed.
Lemma lem1660947 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1660948 (n : nat) (x : real) (y : real) (h1 : x = y) : (term36 x y n) = (term40 y n).
Proof. exact (MK_COMB (@lem1660947) (@lem1660932 n x y h1)). Qed.
Lemma lem1660966 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1660967 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem1660968 (x : real) (y : real) (h1 : x = y) : (real_pow x) = (real_pow y).
Proof. exact (MK_COMB (@lem1660967) (@lem1660966 x y h1)). Qed.
Lemma lem1660969 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1660970 (n : nat) (x : real) (y : real) (h1 : x = y) : (real_pow x n) = (real_pow y n).
Proof. exact (MK_COMB (@lem1660968 x y h1) (@lem1660969 n)). Qed.
Lemma lem1660971 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1660972 (n : nat) (x : real) (y : real) (h1 : x = y) : (term41 x n) = (term41 y n).
Proof. exact (MK_COMB (@lem1660971) (@lem1660970 n x y h1)). Qed.
Lemma lem1660973 (y : real) (n : nat) : (real_pow y n) = (real_pow y n).
Proof. exact (eq_refl (real_pow y n)). Qed.
Lemma lem1660974 (n : nat) (x : real) (y : real) (h1 : x = y) : ((real_pow x n) = (real_pow y n)) = ((real_pow y n) = (real_pow y n)).
Proof. exact (MK_COMB (@lem1660972 n x y h1) (@lem1660973 y n)). Qed.
Lemma lem1660976 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1660977 (x : real) : (x = x) = True.
Proof. exact (@lem1660976 real x). Qed.
Lemma lem1660978 (y : real) (n : nat) : ((real_pow y n) = (real_pow y n)) = True.
Proof. exact (@lem1660977 (real_pow y n)). Qed.
Lemma lem1660979 (n : nat) (x : real) (y : real) (h1 : x = y) : ((real_pow x n) = (real_pow y n)) = True.
Proof. exact (TRANS (@lem1660974 n x y h1) (@lem1660978 y n)). Qed.
Lemma lem1660980 (n : nat) (x : real) (y : real) (h1 : x = y) : (term11 x y n) = (term42 y n).
Proof. exact (MK_COMB (@lem1660948 n x y h1) (@lem1660979 n x y h1)). Qed.
Lemma lem1660982 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1660983 (y : real) (n : nat) : (term42 y n) = True.
Proof. exact (@lem1660982 (term39 y n)). Qed.
Lemma lem1660984 (n : nat) (x : real) (y : real) (h1 : x = y) : (term11 x y n) = True.
Proof. exact (TRANS (@lem1660980 n x y h1) (@lem1660983 y n)). Qed.
Lemma lem1660985 (n : nat) (x : real) (y : real) (h1 : x = y) : True = (term11 x y n).
Proof. exact (SYM (@lem1660984 n x y h1)). Qed.
Lemma lem1660986 (n : nat) (x : real) (y : real) (h1 : x = y) : term11 x y n.
Proof. exact (EQ_MP (@lem1660985 n x y h1) (@lem0)). Qed.
Lemma lem1660987 (x : real) (y : real) (n : nat) (h1 : term7 x y n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (proj2 (@lem1660822 x y n h1)). Qed.
Lemma lem1660988 (x : real) (y : real) (n : nat) (h1 : term7 x y n) : term3 x y.
Proof. exact (proj1 (@lem1660822 x y n h1)). Qed.
Lemma lem1660989 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : real_lt x y) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term11 x y n).
Proof. exact (prop_ext (fun h3 : Coq.Arith.PeanoNat.Nat.Odd n => @lem1660880 n x y h1 h2) (fun h3 : term11 x y n => @lem1660823 n h1)). Qed.
Lemma lem1660990 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : real_lt x y) : term11 x y n.
Proof. exact (EQ_MP (@lem1660989 n x y h1 h2) (@lem1660823 n h1)). Qed.
Lemma lem1660991 (n : nat) (x : real) (y : real) (h1 : x = y) : (x = y) = (term11 x y n).
Proof. exact (prop_ext (fun h2 : x = y => @lem1660986 n x y h1) (fun h2 : term11 x y n => @lem1660826 x y h1)). Qed.
Lemma lem1660992 (n : nat) (x : real) (y : real) (h1 : x = y) : term11 x y n.
Proof. exact (EQ_MP (@lem1660991 n x y h1) (@lem1660826 x y h1)). Qed.
Lemma lem1660993 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : real_lt x y) : (real_lt x y) = (term11 x y n).
Proof. exact (prop_ext (fun h3 : real_lt x y => @lem1660990 n x y h1 h2) (fun h3 : term11 x y n => @lem1660825 x y h2)). Qed.
Lemma lem1660994 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : real_lt x y) : term11 x y n.
Proof. exact (EQ_MP (@lem1660993 n x y h1 h2) (@lem1660825 x y h2)). Qed.
Lemma lem1660995 (n : nat) (x : real) (y : real) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) (h2 : term3 x y) : term11 x y n.
Proof. exact (or_elim (@lem1660824 x y h2) (fun h0 : real_lt x y => @lem1660994 n x y h1 h0) (fun h0 : x = y => @lem1660992 n x y h0)). Qed.
Lemma lem1660996 (n : nat) (x : real) (y : real) (h1 : term7 x y n) (h2 : term3 x y) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term11 x y n).
Proof. exact (prop_ext (fun h3 : Coq.Arith.PeanoNat.Nat.Odd n => @lem1660995 n x y h3 h2) (fun h3 : term11 x y n => @lem1660987 x y n h1)). Qed.
Lemma lem1660997 (n : nat) (x : real) (y : real) (h1 : term7 x y n) (h2 : term3 x y) : term11 x y n.
Proof. exact (EQ_MP (@lem1660996 n x y h1 h2) (@lem1660987 x y n h1)). Qed.
Lemma lem1660998 (x : real) (y : real) (n : nat) (h1 : term7 x y n) : (term3 x y) = (term11 x y n).
Proof. exact (prop_ext (fun h2 : term3 x y => @lem1660997 n x y h1 h2) (fun h2 : term11 x y n => @lem1660988 x y n h1)). Qed.
Lemma lem1660999 (x : real) (y : real) (n : nat) (h1 : term7 x y n) : term11 x y n.
Proof. exact (EQ_MP (@lem1660998 x y n h1) (@lem1660988 x y n h1)). Qed.
Lemma lem1661000 (x : real) (y : real) (n : nat) : term13 x y n.
Proof. exact (fun h0 : term7 x y n => @lem1660999 x y n h0). Qed.
Lemma lem1661005 (x : real) (n : nat) : term17 x n.
Proof. exact (fun y : real => @lem1661000 x y n). Qed.
Lemma lem1661010 (n : nat) : term21 n.
Proof. exact (fun x : real => @lem1661005 x n). Qed.
Lemma lem1661015 : term25.
Proof. exact (fun n : nat => @lem1661010 n). Qed.
Lemma lem1661016 : term24.
Proof. exact (EQ_MP (@lem1660821) (@lem1661015)). Qed.
