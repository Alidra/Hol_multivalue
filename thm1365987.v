Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1365987_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import real_ge_spec.
Require Import thm0_spec.
Require Import thm1365403_spec.
Require Import thm1365404_spec.
Require Import thm1365406_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1365727 (y : real) : term0 y.
Proof. exact (@lem1342163 y). Qed.
Lemma lem1365728 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem1365729 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem1365728 y) (@lem1365727 y)). Qed.
Lemma lem1365730 (y : real) (x : real) : term2 y x.
Proof. exact (@lem1365729 y x). Qed.
Lemma lem1365731 (y : real) (x : real) : (term2 y x) = ((real_ge x y) = (real_le y x)).
Proof. exact (eq_refl (term2 y x)). Qed.
Lemma lem1365736 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1365737 (m : nat) (n : nat) : ((term3 m n) = True) = (term3 m n).
Proof. exact (@lem1365736 (term3 m n)). Qed.
Lemma lem1365739 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1365731 y x) (@lem1365730 y x)). Qed.
Lemma lem1365740 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (@lem1365739 (term5 n) (real_of_num m)). Qed.
Lemma lem1365742 (m : nat) (n : nat) : (term4 m n) = True.
Proof. exact (proj1 (@lem1365403 m n)). Qed.
Lemma lem1365743 (n : nat) (m : nat) : (term4 n m) = True.
Proof. exact (@lem1365742 n m). Qed.
Lemma lem1365744 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (TRANS (@lem1365740 n m) (@lem1365743 n m)). Qed.
Lemma lem1365745 (m : nat) (n : nat) : ((term3 m n) = True) = True.
Proof. exact (TRANS (@lem1365737 m n) (@lem1365744 m n)). Qed.
Lemma lem1365746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1365747 (m : nat) (n : nat) : (term6 m n) = (and True).
Proof. exact (MK_COMB (@lem1365746) (@lem1365745 m n)). Qed.
Lemma lem1365753 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1365731 y x) (@lem1365730 y x)). Qed.
Lemma lem1365754 (n : nat) (m : nat) : (term7 m n) = (term8 n m).
Proof. exact (@lem1365753 (real_of_num n) (real_of_num m)). Qed.
Lemma lem1365756 (m : nat) (n : nat) : (term8 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem1365404 m n)). Qed.
Lemma lem1365757 (n : nat) (m : nat) : (term8 n m) = (Peano.le n m).
Proof. exact (@lem1365756 n m). Qed.
Lemma lem1365758 (n : nat) (m : nat) : (term7 m n) = (Peano.le n m).
Proof. exact (TRANS (@lem1365754 n m) (@lem1365757 n m)). Qed.
Lemma lem1365759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365760 (n : nat) (m : nat) : (term9 m n) = (term10 n m).
Proof. exact (MK_COMB (@lem1365759) (@lem1365758 n m)). Qed.
Lemma lem1365761 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem1365762 (n : nat) (m : nat) : ((term7 m n) = (Peano.le n m)) = ((Peano.le n m) = (Peano.le n m)).
Proof. exact (MK_COMB (@lem1365760 n m) (@lem1365761 n m)). Qed.
Lemma lem1365764 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1365765 (x : Prop) : (x = x) = True.
Proof. exact (@lem1365764 Prop x). Qed.
Lemma lem1365766 (n : nat) (m : nat) : ((Peano.le n m) = (Peano.le n m)) = True.
Proof. exact (@lem1365765 (Peano.le n m)). Qed.
Lemma lem1365767 (n : nat) (m : nat) : ((term7 m n) = (Peano.le n m)) = True.
Proof. exact (TRANS (@lem1365762 n m) (@lem1365766 n m)). Qed.
Lemma lem1365768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1365769 (n : nat) (m : nat) : (term11 n m) = (and True).
Proof. exact (MK_COMB (@lem1365768) (@lem1365767 n m)). Qed.
Lemma lem1365775 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1365731 y x) (@lem1365730 y x)). Qed.
Lemma lem1365776 (n : nat) (m : nat) : (term12 m n) = (term13 n m).
Proof. exact (@lem1365775 (term5 n) (term5 m)). Qed.
Lemma lem1365778 (n : nat) (m : nat) : (term13 m n) = (Peano.le n m).
Proof. exact (proj1 (@lem1365406 m n)). Qed.
Lemma lem1365779 (m : nat) (n : nat) : (term13 n m) = (Peano.le m n).
Proof. exact (@lem1365778 m n). Qed.
Lemma lem1365780 (m : nat) (n : nat) : (term12 m n) = (Peano.le m n).
Proof. exact (TRANS (@lem1365776 n m) (@lem1365779 m n)). Qed.
Lemma lem1365781 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365782 (m : nat) (n : nat) : (term14 m n) = (term10 m n).
Proof. exact (MK_COMB (@lem1365781) (@lem1365780 m n)). Qed.
Lemma lem1365783 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem1365784 (m : nat) (n : nat) : ((term12 m n) = (Peano.le m n)) = ((Peano.le m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem1365782 m n) (@lem1365783 m n)). Qed.
Lemma lem1365786 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1365787 (x : Prop) : (x = x) = True.
Proof. exact (@lem1365786 Prop x). Qed.
Lemma lem1365788 (m : nat) (n : nat) : ((Peano.le m n) = (Peano.le m n)) = True.
Proof. exact (@lem1365787 (Peano.le m n)). Qed.
Lemma lem1365789 (m : nat) (n : nat) : ((term12 m n) = (Peano.le m n)) = True.
Proof. exact (TRANS (@lem1365784 m n) (@lem1365788 m n)). Qed.
Lemma lem1365790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1365791 (m : nat) (n : nat) : (term15 m n) = (and True).
Proof. exact (MK_COMB (@lem1365790) (@lem1365789 m n)). Qed.
Lemma lem1365795 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1365731 y x) (@lem1365730 y x)). Qed.
Lemma lem1365796 (n : nat) (m : nat) : (term16 m n) = (term17 n m).
Proof. exact (@lem1365795 (real_of_num n) (term5 m)). Qed.
Lemma lem1365798 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem1365799 (n : nat) (m : nat) : (term17 n m) = (term18 n m).
Proof. exact (@lem1365798 n m). Qed.
Lemma lem1365802 (n : nat) (m : nat) : (term16 m n) = (term18 n m).
Proof. exact (TRANS (@lem1365796 n m) (@lem1365799 n m)). Qed.
Lemma lem1365807 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365808 (n : nat) (m : nat) : (term19 m n) = (term20 n m).
Proof. exact (MK_COMB (@lem1365807) (@lem1365802 n m)). Qed.
Lemma lem1365815 (m : nat) (n : nat) : (term18 m n) = (term18 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem1365816 (m : nat) (n : nat) : ((term16 m n) = (term18 m n)) = ((term18 n m) = (term18 m n)).
Proof. exact (MK_COMB (@lem1365808 n m) (@lem1365815 m n)). Qed.
Lemma lem1365819 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem1365791 m n) (@lem1365816 m n)). Qed.
Lemma lem1365821 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1365822 (m : nat) (n : nat) : (term22 m n) = ((term18 n m) = (term18 m n)).
Proof. exact (@lem1365821 ((term18 n m) = (term18 m n))). Qed.
Lemma lem1365837 (m : nat) (n : nat) : (term21 m n) = ((term18 n m) = (term18 m n)).
Proof. exact (TRANS (@lem1365819 m n) (@lem1365822 m n)). Qed.
Lemma lem1365838 (m : nat) (n : nat) : (term23 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem1365769 n m) (@lem1365837 m n)). Qed.
Lemma lem1365840 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1365841 (m : nat) (n : nat) : (term22 m n) = ((term18 n m) = (term18 m n)).
Proof. exact (@lem1365840 ((term18 n m) = (term18 m n))). Qed.
Lemma lem1365856 (m : nat) (n : nat) : (term23 m n) = ((term18 n m) = (term18 m n)).
Proof. exact (TRANS (@lem1365838 m n) (@lem1365841 m n)). Qed.
Lemma lem1365857 (m : nat) (n : nat) : (term24 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem1365747 m n) (@lem1365856 m n)). Qed.
Lemma lem1365859 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1365860 (m : nat) (n : nat) : (term22 m n) = ((term18 n m) = (term18 m n)).
Proof. exact (@lem1365859 ((term18 n m) = (term18 m n))). Qed.
Lemma lem1365875 (m : nat) (n : nat) : (term24 m n) = ((term18 n m) = (term18 m n)).
Proof. exact (TRANS (@lem1365857 m n) (@lem1365860 m n)). Qed.
Lemma lem1365876 (m : nat) (n : nat) : ((term18 n m) = (term18 m n)) = (term24 m n).
Proof. exact (SYM (@lem1365875 m n)). Qed.
Lemma lem1365893 (n : nat) : term25 n.
Proof. exact (@lem9851 (n = (NUMERAL 0))). Qed.
Lemma lem1365894 (n : nat) : (term25 n) = (term26 n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem1365895 (n : nat) : term26 n.
Proof. exact (EQ_MP (@lem1365894 n) (@lem1365893 n)). Qed.
Lemma lem1365896 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (n = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem1365897 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (n = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem1365914 (m : nat) : (term27 m) = (term27 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem1365915 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term28 m n) = (term29 m).
Proof. exact (MK_COMB (@lem1365914 m) (@lem1365896 n h1)). Qed.
Lemma lem1365916 (m : nat) : (term29 m) = ((term30 m) = (term31 m)).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem1365917 (m : nat) (n : nat) : (term32 m n) = (term32 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1365918 (n : nat) (m : nat) : ((term28 m n) = (term29 m)) = ((term28 m n) = ((term30 m) = (term31 m))).
Proof. exact (MK_COMB (@lem1365917 m n) (@lem1365916 m)). Qed.
Lemma lem1365919 (m : nat) (n : nat) : (term28 m n) = ((term18 n m) = (term18 m n)).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem1365920 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365921 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (MK_COMB (@lem1365920) (@lem1365919 m n)). Qed.
Lemma lem1365922 (m : nat) : ((term30 m) = (term31 m)) = ((term30 m) = (term31 m)).
Proof. exact (eq_refl ((term30 m) = (term31 m))). Qed.
Lemma lem1365923 (n : nat) (m : nat) : ((term28 m n) = ((term30 m) = (term31 m))) = (((term18 n m) = (term18 m n)) = ((term30 m) = (term31 m))).
Proof. exact (MK_COMB (@lem1365921 m n) (@lem1365922 m)). Qed.
Lemma lem1365924 (n : nat) (m : nat) : ((term28 m n) = (term29 m)) = (((term18 n m) = (term18 m n)) = ((term30 m) = (term31 m))).
Proof. exact (TRANS (@lem1365918 n m) (@lem1365923 n m)). Qed.
Lemma lem1365925 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term18 n m) = (term18 m n)) = ((term30 m) = (term31 m)).
Proof. exact (EQ_MP (@lem1365924 n m) (@lem1365915 m n h1)). Qed.
Lemma lem1365926 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term30 m) = (term31 m)) = ((term18 n m) = (term18 m n)).
Proof. exact (SYM (@lem1365925 m n h1)). Qed.
Lemma lem1365927 (m : nat) : (term27 m) = (term27 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem1365928 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term28 m n) = (term34 m).
Proof. exact (MK_COMB (@lem1365927 m) (@lem1365897 n h1)). Qed.
Lemma lem1365929 (m : nat) : (term34 m) = ((term35 m) = (term36 m)).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem1365930 (m : nat) (n : nat) : (term32 m n) = (term32 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1365931 (n : nat) (m : nat) : ((term28 m n) = (term34 m)) = ((term28 m n) = ((term35 m) = (term36 m))).
Proof. exact (MK_COMB (@lem1365930 m n) (@lem1365929 m)). Qed.
Lemma lem1365932 (m : nat) (n : nat) : (term28 m n) = ((term18 n m) = (term18 m n)).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem1365933 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365934 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (MK_COMB (@lem1365933) (@lem1365932 m n)). Qed.
Lemma lem1365935 (m : nat) : ((term35 m) = (term36 m)) = ((term35 m) = (term36 m)).
Proof. exact (eq_refl ((term35 m) = (term36 m))). Qed.
Lemma lem1365936 (n : nat) (m : nat) : ((term28 m n) = ((term35 m) = (term36 m))) = (((term18 n m) = (term18 m n)) = ((term35 m) = (term36 m))).
Proof. exact (MK_COMB (@lem1365934 m n) (@lem1365935 m)). Qed.
Lemma lem1365937 (n : nat) (m : nat) : ((term28 m n) = (term34 m)) = (((term18 n m) = (term18 m n)) = ((term35 m) = (term36 m))).
Proof. exact (TRANS (@lem1365931 n m) (@lem1365936 n m)). Qed.
Lemma lem1365938 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term18 n m) = (term18 m n)) = ((term35 m) = (term36 m)).
Proof. exact (EQ_MP (@lem1365937 n m) (@lem1365928 m n h1)). Qed.
Lemma lem1365939 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term35 m) = (term36 m)) = ((term18 n m) = (term18 m n)).
Proof. exact (SYM (@lem1365938 m n h1)). Qed.
Lemma lem1365943 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1365944 (m : nat) : (term30 m) = (m = (NUMERAL 0)).
Proof. exact (@lem1365943 (m = (NUMERAL 0))). Qed.
Lemma lem1365947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365948 (m : nat) : (term37 m) = (term38 m).
Proof. exact (MK_COMB (@lem1365947) (@lem1365944 m)). Qed.
Lemma lem1365950 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1365951 (m : nat) : (term31 m) = (m = (NUMERAL 0)).
Proof. exact (@lem1365950 (m = (NUMERAL 0))). Qed.
Lemma lem1365954 (m : nat) : ((term30 m) = (term31 m)) = ((m = (NUMERAL 0)) = (m = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1365948 m) (@lem1365951 m)). Qed.
Lemma lem1365956 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1365957 (x : Prop) : (x = x) = True.
Proof. exact (@lem1365956 Prop x). Qed.
Lemma lem1365958 (m : nat) : ((m = (NUMERAL 0)) = (m = (NUMERAL 0))) = True.
Proof. exact (@lem1365957 (m = (NUMERAL 0))). Qed.
Lemma lem1365959 (m : nat) : ((term30 m) = (term31 m)) = True.
Proof. exact (TRANS (@lem1365954 m) (@lem1365958 m)). Qed.
Lemma lem1365960 (m : nat) : True = ((term30 m) = (term31 m)).
Proof. exact (SYM (@lem1365959 m)). Qed.
Lemma lem1365961 (m : nat) : (term30 m) = (term31 m).
Proof. exact (EQ_MP (@lem1365960 m) (@lem0)). Qed.
Lemma lem1365965 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1365966 (m : nat) : (term35 m) = False.
Proof. exact (@lem1365965 (m = (NUMERAL 0))). Qed.
Lemma lem1365967 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1365968 (m : nat) : (term39 m) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1365967) (@lem1365966 m)). Qed.
Lemma lem1365970 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1365971 (m : nat) : (term36 m) = False.
Proof. exact (@lem1365970 (m = (NUMERAL 0))). Qed.
Lemma lem1365972 (m : nat) : ((term35 m) = (term36 m)) = (False = False).
Proof. exact (MK_COMB (@lem1365968 m) (@lem1365971 m)). Qed.
Lemma lem1365974 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1365975 : (False = False) = (~ False).
Proof. exact (@lem1365974 False). Qed.
Lemma lem1365977 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1365978 : (False = False) = True.
Proof. exact (TRANS (@lem1365975) (@lem1365977)). Qed.
Lemma lem1365979 (m : nat) : ((term35 m) = (term36 m)) = True.
Proof. exact (TRANS (@lem1365972 m) (@lem1365978)). Qed.
Lemma lem1365980 (m : nat) : True = ((term35 m) = (term36 m)).
Proof. exact (SYM (@lem1365979 m)). Qed.
Lemma lem1365981 (m : nat) : (term35 m) = (term36 m).
Proof. exact (EQ_MP (@lem1365980 m) (@lem0)). Qed.
Lemma lem1365982 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term18 n m) = (term18 m n).
Proof. exact (EQ_MP (@lem1365939 m n h1) (@lem1365981 m)). Qed.
Lemma lem1365983 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term18 n m) = (term18 m n).
Proof. exact (EQ_MP (@lem1365926 m n h1) (@lem1365961 m)). Qed.
Lemma lem1365986 (m : nat) (n : nat) : (term18 n m) = (term18 m n).
Proof. exact (or_elim (@lem1365895 n) (fun h0 : (n = (NUMERAL 0)) = True => @lem1365983 m n h0) (fun h0 : (n = (NUMERAL 0)) = False => @lem1365982 m n h0)). Qed.
Lemma lem1365987 (m : nat) (n : nat) : term24 m n.
Proof. exact (EQ_MP (@lem1365876 m n) (@lem1365986 m n)). Qed.
