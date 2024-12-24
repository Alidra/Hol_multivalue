Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_LT2_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import REAL_LT_MUL2_spec.
Require Import REAL_MUL_RID_spec.
Require Import REAL_POW_LE_spec.
Require Import thm0_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem1637790 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1637791 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1637790 h1 x). Qed.
Lemma lem1637792 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1637793 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1637792 x) (@lem1637791 x h1)). Qed.
Lemma lem1637794 (x : real) (n : nat) (h1 : term0) : term3 x n.
Proof. exact (@lem1637793 x h1 n). Qed.
Lemma lem1637795 (x : real) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (eq_refl (term3 x n)). Qed.
Lemma lem1637796 (x : real) (n : nat) (h1 : term0) : term4 x n.
Proof. exact (EQ_MP (@lem1637795 x n) (@lem1637794 x n h1)). Qed.
Lemma lem1637797 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (h1). Qed.
Lemma lem1637798 (n : nat) (x : real) (h1 : term0) (h2 : term5 x) : term6 x n.
Proof. exact (@lem1637796 x n h1 (@lem1637797 x h2)). Qed.
Lemma lem1637799 (n : nat) (x : real) (h1 : term5 x) : term7 x n.
Proof. exact (fun h0 : term0 => @lem1637798 n x h0 h1). Qed.
Lemma lem1637800 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1637801 (n : nat) (x : real) (h1 : term0) (h2 : term5 x) : term6 x n.
Proof. exact (@lem1637799 n x h2 (@lem1637800 h1)). Qed.
Lemma lem1637802 (x : real) (n : nat) (h1 : term0) : term4 x n.
Proof. exact (fun h0 : term5 x => @lem1637801 n x h1 h0). Qed.
Lemma lem1637803 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun n : nat => @lem1637802 x n h1). Qed.
Lemma lem1637804 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1637803 x h1). Qed.
Lemma lem1637805 : term8.
Proof. exact (fun h0 : term0 => @lem1637804 h0). Qed.
Lemma lem1637806 : term0.
Proof. exact (@lem1637805 (@lem1582434)). Qed.
Lemma lem1637807 (x : real) : term1 x.
Proof. exact (@lem1637806 x). Qed.
Lemma lem1637808 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1637809 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1637808 x) (@lem1637807 x)). Qed.
Lemma lem1637810 (x : real) (n : nat) : term3 x n.
Proof. exact (@lem1637809 x n). Qed.
Lemma lem1637811 (x : real) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (eq_refl (term3 x n)). Qed.
Lemma lem1637813 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem1637814 (w : real) (h1 : term9) : term10 w.
Proof. exact (@lem1637813 h1 w). Qed.
Lemma lem1637815 (w : real) : (term10 w) = (term11 w).
Proof. exact (eq_refl (term10 w)). Qed.
Lemma lem1637816 (w : real) (h1 : term9) : term11 w.
Proof. exact (EQ_MP (@lem1637815 w) (@lem1637814 w h1)). Qed.
Lemma lem1637817 (w : real) (x : real) (h1 : term9) : term12 w x.
Proof. exact (@lem1637816 w h1 x). Qed.
Lemma lem1637818 (w : real) (x : real) : (term12 w x) = (term13 w x).
Proof. exact (eq_refl (term12 w x)). Qed.
Lemma lem1637819 (w : real) (x : real) (h1 : term9) : term13 w x.
Proof. exact (EQ_MP (@lem1637818 w x) (@lem1637817 w x h1)). Qed.
Lemma lem1637820 (w : real) (x : real) (y : real) (h1 : term9) : term14 w x y.
Proof. exact (@lem1637819 w x h1 y). Qed.
Lemma lem1637821 (w : real) (y : real) (x : real) : (term14 w x y) = (term15 w y x).
Proof. exact (eq_refl (term14 w x y)). Qed.
Lemma lem1637822 (w : real) (y : real) (x : real) (h1 : term9) : term15 w y x.
Proof. exact (EQ_MP (@lem1637821 w y x) (@lem1637820 w x y h1)). Qed.
Lemma lem1637823 (w : real) (y : real) (x : real) (z : real) (h1 : term9) : term16 w y x z.
Proof. exact (@lem1637822 w y x h1 z). Qed.
Lemma lem1637824 (w : real) (y : real) (x : real) (z : real) : (term16 w y x z) = (term17 w y x z).
Proof. exact (eq_refl (term16 w y x z)). Qed.
Lemma lem1637825 (w : real) (y : real) (x : real) (z : real) (h1 : term9) : term17 w y x z.
Proof. exact (EQ_MP (@lem1637824 w y x z) (@lem1637823 w y x z h1)). Qed.
Lemma lem1637826 (w : real) (x : real) (y : real) (z : real) (h1 : term18 w x y z) : term18 w x y z.
Proof. exact (h1). Qed.
Lemma lem1637827 (w : real) (x : real) (y : real) (z : real) (h1 : term9) (h2 : term18 w x y z) : term19 w y x z.
Proof. exact (@lem1637825 w y x z h1 (@lem1637826 w x y z h2)). Qed.
Lemma lem1637828 (w : real) (x : real) (y : real) (z : real) (h1 : term18 w x y z) : term20 w y x z.
Proof. exact (fun h0 : term9 => @lem1637827 w x y z h0 h1). Qed.
Lemma lem1637829 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem1637830 (w : real) (x : real) (y : real) (z : real) (h1 : term9) (h2 : term18 w x y z) : term19 w y x z.
Proof. exact (@lem1637828 w x y z h2 (@lem1637829 h1)). Qed.
Lemma lem1637831 (w : real) (y : real) (x : real) (z : real) (h1 : term9) : term17 w y x z.
Proof. exact (fun h0 : term18 w x y z => @lem1637830 w x y z h1 h0). Qed.
Lemma lem1637832 (w : real) (y : real) (x : real) (h1 : term9) : term15 w y x.
Proof. exact (fun z : real => @lem1637831 w y x z h1). Qed.
Lemma lem1637833 (w : real) (y : real) (h1 : term9) : term21 w y.
Proof. exact (fun x : real => @lem1637832 w y x h1). Qed.
Lemma lem1637834 (w : real) (h1 : term9) : term22 w.
Proof. exact (fun y : real => @lem1637833 w y h1). Qed.
Lemma lem1637835 (h1 : term9) : term23.
Proof. exact (fun w : real => @lem1637834 w h1). Qed.
Lemma lem1637836 : term24.
Proof. exact (fun h0 : term9 => @lem1637835 h0). Qed.
Lemma lem1637837 : term23.
Proof. exact (@lem1637836 (@lem1630835)). Qed.
Lemma lem1637838 (w : real) : term25 w.
Proof. exact (@lem1637837 w). Qed.
Lemma lem1637839 (w : real) : (term25 w) = (term22 w).
Proof. exact (eq_refl (term25 w)). Qed.
Lemma lem1637840 (w : real) : term22 w.
Proof. exact (EQ_MP (@lem1637839 w) (@lem1637838 w)). Qed.
Lemma lem1637841 (w : real) (y : real) : term26 w y.
Proof. exact (@lem1637840 w y). Qed.
Lemma lem1637842 (w : real) (y : real) : (term26 w y) = (term21 w y).
Proof. exact (eq_refl (term26 w y)). Qed.
Lemma lem1637843 (w : real) (y : real) : term21 w y.
Proof. exact (EQ_MP (@lem1637842 w y) (@lem1637841 w y)). Qed.
Lemma lem1637844 (w : real) (y : real) (x : real) : term27 w y x.
Proof. exact (@lem1637843 w y x). Qed.
Lemma lem1637845 (w : real) (y : real) (x : real) : (term27 w y x) = (term15 w y x).
Proof. exact (eq_refl (term27 w y x)). Qed.
Lemma lem1637846 (w : real) (y : real) (x : real) : term15 w y x.
Proof. exact (EQ_MP (@lem1637845 w y x) (@lem1637844 w y x)). Qed.
Lemma lem1637847 (w : real) (y : real) (x : real) (z : real) : term16 w y x z.
Proof. exact (@lem1637846 w y x z). Qed.
Lemma lem1637848 (w : real) (y : real) (x : real) (z : real) : (term16 w y x z) = (term17 w y x z).
Proof. exact (eq_refl (term16 w y x z)). Qed.
Lemma lem1637850 (n : nat) : term28 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem1637851 (n : nat) : (term28 n) = (term29 n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem1637852 (n : nat) : term29 n.
Proof. exact (EQ_MP (@lem1637851 n) (@lem1637850 n)). Qed.
Lemma lem1637854 (n : nat) (h1 : term30 n) : term30 n.
Proof. exact (h1). Qed.
Lemma lem1637855 (x : real) : term31 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1637856 (x : real) (n : nat) : term32 x n.
Proof. exact (@lem1637855 x n). Qed.
Lemma lem1637857 (x : real) (n : nat) : (term32 x n) = ((term33 x n) = (term34 x n)).
Proof. exact (eq_refl (term32 x n)). Qed.
Lemma lem1637860 (n : nat) : term35 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1637861 (n : nat) : (term35 n) = (term36 n).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem1637862 (n : nat) : term36 n.
Proof. exact (EQ_MP (@lem1637861 n) (@lem1637860 n)). Qed.
Lemma lem1637863 (n : nat) : term37 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem1637877 (P : nat -> Prop) : term38 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1637878 : term39.
Proof. exact (@lem1637877 term40). Qed.
Lemma lem1637879 : term41 = term42.
Proof. exact (eq_refl term41). Qed.
Lemma lem1637880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1637881 : term43 = term44.
Proof. exact (MK_COMB (@lem1637880) (@lem1637879)). Qed.
Lemma lem1637882 (n : nat) : (term45 n) = (term46 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem1637883 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1637884 (n : nat) : (term47 n) = (term48 n).
Proof. exact (MK_COMB (@lem1637883) (@lem1637882 n)). Qed.
Lemma lem1637885 (n : nat) : (term49 n) = (term50 n).
Proof. exact (eq_refl (term49 n)). Qed.
Lemma lem1637886 (n : nat) : (term51 n) = (term52 n).
Proof. exact (MK_COMB (@lem1637884 n) (@lem1637885 n)). Qed.
Lemma lem1637887 : term53 = term54.
Proof. exact (fun_ext (fun n : nat => @lem1637886 n)). Qed.
Lemma lem1637888 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1637889 : term55 = term56.
Proof. exact (MK_COMB (@lem1637888) (@lem1637887)). Qed.
Lemma lem1637890 : term57 = term58.
Proof. exact (MK_COMB (@lem1637881) (@lem1637889)). Qed.
Lemma lem1637891 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1637892 : term59 = term60.
Proof. exact (MK_COMB (@lem1637891) (@lem1637890)). Qed.
Lemma lem1637893 (n : nat) : (term45 n) = (term46 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem1637894 : term61 = term40.
Proof. exact (fun_ext (fun n : nat => @lem1637893 n)). Qed.
Lemma lem1637895 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1637896 : term62 = term63.
Proof. exact (MK_COMB (@lem1637895) (@lem1637894)). Qed.
Lemma lem1637897 : term39 = term64.
Proof. exact (MK_COMB (@lem1637892) (@lem1637896)). Qed.
Lemma lem1637898 : term64.
Proof. exact (EQ_MP (@lem1637897) (@lem1637878)). Qed.
Lemma lem1637899 (n : nat) (h1 : term46 n) : term46 n.
Proof. exact (h1). Qed.
Lemma lem1637913 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1637914 (x : nat) : (x = x) = True.
Proof. exact (@lem1637913 nat x). Qed.
Lemma lem1637915 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1637914 (NUMERAL 0)). Qed.
Lemma lem1637916 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1637917 : term65 = (~ True).
Proof. exact (MK_COMB (@lem1637916) (@lem1637915)). Qed.
Lemma lem1637919 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1637920 : term65 = False.
Proof. exact (TRANS (@lem1637917) (@lem1637919)). Qed.
Lemma lem1637921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1637922 : term66 = (and False).
Proof. exact (MK_COMB (@lem1637921) (@lem1637920)). Qed.
Lemma lem1637925 (x : real) (y : real) : (term67 x y) = (term67 x y).
Proof. exact (eq_refl (term67 x y)). Qed.
Lemma lem1637926 (x : real) (y : real) : (term68 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1637922) (@lem1637925 x y)). Qed.
Lemma lem1637928 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1637929 (x : real) (y : real) : (term69 x y) = False.
Proof. exact (@lem1637928 (term67 x y)). Qed.
Lemma lem1637930 (x : real) (y : real) : (term68 x y) = False.
Proof. exact (TRANS (@lem1637926 x y) (@lem1637929 x y)). Qed.
Lemma lem1637931 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1637932 (x : real) (y : real) : (term70 x y) = (imp False).
Proof. exact (MK_COMB (@lem1637931) (@lem1637930 x y)). Qed.
Lemma lem1637934 (x : real) : (term71 x) = term72.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1637935 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1637936 (x : real) : (term73 x) = term74.
Proof. exact (MK_COMB (@lem1637935) (@lem1637934 x)). Qed.
Lemma lem1637938 (x : real) : (term71 x) = term72.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1637939 (y : real) : (term71 y) = term72.
Proof. exact (@lem1637938 y). Qed.
Lemma lem1637940 (x : real) (y : real) : (term75 x y) = term76.
Proof. exact (MK_COMB (@lem1637936 x) (@lem1637939 y)). Qed.
Lemma lem1637941 (x : real) (y : real) : (term77 x y) = term78.
Proof. exact (MK_COMB (@lem1637932 x y) (@lem1637940 x y)). Qed.
Lemma lem1637943 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1637944 : term78 = True.
Proof. exact (@lem1637943 term76). Qed.
Lemma lem1637945 (x : real) (y : real) : (term77 x y) = True.
Proof. exact (TRANS (@lem1637941 x y) (@lem1637944)). Qed.
Lemma lem1637946 (x : real) : (term79 x) = term80.
Proof. exact (fun_ext (fun y : real => @lem1637945 x y)). Qed.
Lemma lem1637947 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1637948 (x : real) : (term81 x) = term82.
Proof. exact (MK_COMB (@lem1637947) (@lem1637946 x)). Qed.
Lemma lem1637950 {A : Type'} (t : Prop) : (term83 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1637951 (t : Prop) : (term84 t) = t.
Proof. exact (@lem1637950 real t). Qed.
Lemma lem1637952 : term82 = True.
Proof. exact (@lem1637951 True). Qed.
Lemma lem1637953 (x : real) : (term81 x) = True.
Proof. exact (TRANS (@lem1637948 x) (@lem1637952)). Qed.
Lemma lem1637954 : term85 = term80.
Proof. exact (fun_ext (fun x : real => @lem1637953 x)). Qed.
Lemma lem1637955 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1637956 : term42 = term82.
Proof. exact (MK_COMB (@lem1637955) (@lem1637954)). Qed.
Lemma lem1637958 {A : Type'} (t : Prop) : (term83 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1637959 (t : Prop) : (term84 t) = t.
Proof. exact (@lem1637958 real t). Qed.
Lemma lem1637960 : term82 = True.
Proof. exact (@lem1637959 True). Qed.
Lemma lem1637961 : term42 = True.
Proof. exact (TRANS (@lem1637956) (@lem1637960)). Qed.
Lemma lem1637962 : True = term42.
Proof. exact (SYM (@lem1637961)). Qed.
Lemma lem1637963 : term42.
Proof. exact (EQ_MP (@lem1637962) (@lem0)). Qed.
Lemma lem1637977 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1637863 n (@lem1637862 n)). Qed.
Lemma lem1637978 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1637979 (n : nat) : (term36 n) = (~ False).
Proof. exact (MK_COMB (@lem1637978) (@lem1637977 n)). Qed.
Lemma lem1637981 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1637982 (n : nat) : (term36 n) = True.
Proof. exact (TRANS (@lem1637979 n) (@lem1637981)). Qed.
Lemma lem1637983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1637984 (n : nat) : (term86 n) = (and True).
Proof. exact (MK_COMB (@lem1637983) (@lem1637982 n)). Qed.
Lemma lem1637987 (x : real) (y : real) : (term67 x y) = (term67 x y).
Proof. exact (eq_refl (term67 x y)). Qed.
Lemma lem1637988 (n : nat) (x : real) (y : real) : (term87 n x y) = (term88 x y).
Proof. exact (MK_COMB (@lem1637984 n) (@lem1637987 x y)). Qed.
Lemma lem1637990 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1637991 (x : real) (y : real) : (term88 x y) = (term67 x y).
Proof. exact (@lem1637990 (term67 x y)). Qed.
Lemma lem1637994 (n : nat) (x : real) (y : real) : (term87 n x y) = (term67 x y).
Proof. exact (TRANS (@lem1637988 n x y) (@lem1637991 x y)). Qed.
Lemma lem1637995 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1637996 (n : nat) (x : real) (y : real) : (term89 n x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1637995) (@lem1637994 n x y)). Qed.
Lemma lem1637998 (x : real) (n : nat) : (term33 x n) = (term34 x n).
Proof. exact (EQ_MP (@lem1637857 x n) (@lem1637856 x n)). Qed.
Lemma lem1637999 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1638000 (x : real) (n : nat) : (term91 x n) = (term92 x n).
Proof. exact (MK_COMB (@lem1637999) (@lem1637998 x n)). Qed.
Lemma lem1638002 (x : real) (n : nat) : (term33 x n) = (term34 x n).
Proof. exact (EQ_MP (@lem1637857 x n) (@lem1637856 x n)). Qed.
Lemma lem1638003 (y : real) (n : nat) : (term33 y n) = (term34 y n).
Proof. exact (@lem1638002 y n). Qed.
Lemma lem1638004 (x : real) (y : real) (n : nat) : (term93 x y n) = (term94 x y n).
Proof. exact (MK_COMB (@lem1638000 x n) (@lem1638003 y n)). Qed.
Lemma lem1638005 (x : real) (y : real) (n : nat) : (term95 x y n) = (term96 x y n).
Proof. exact (MK_COMB (@lem1637996 n x y) (@lem1638004 x y n)). Qed.
Lemma lem1638008 (x : real) (n : nat) : (term97 x n) = (term98 x n).
Proof. exact (fun_ext (fun y : real => @lem1638005 x y n)). Qed.
Lemma lem1638009 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1638010 (x : real) (n : nat) : (term99 x n) = (term100 x n).
Proof. exact (MK_COMB (@lem1638009) (@lem1638008 x n)). Qed.
Lemma lem1638015 (n : nat) : (term101 n) = (term102 n).
Proof. exact (fun_ext (fun x : real => @lem1638010 x n)). Qed.
Lemma lem1638016 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1638017 (n : nat) : (term50 n) = (term103 n).
Proof. exact (MK_COMB (@lem1638016) (@lem1638015 n)). Qed.
Lemma lem1638022 (n : nat) : (term103 n) = (term50 n).
Proof. exact (SYM (@lem1638017 n)). Qed.
Lemma lem1638023 (x : real) (y : real) (h1 : term67 x y) : term67 x y.
Proof. exact (h1). Qed.
Lemma lem1638024 (x : real) (y : real) (h1 : real_lt x y) : real_lt x y.
Proof. exact (h1). Qed.
Lemma lem1638025 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (h1). Qed.
Lemma lem1638026 (x : real) : term104 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem1638027 (x : real) : (term104 x) = ((term105 x) = x).
Proof. exact (eq_refl (term104 x)). Qed.
Lemma lem1638044 (x : real) (y : real) : (real_lt x y) = ((real_lt x y) = True).
Proof. exact (@lem7 (real_lt x y)). Qed.
Lemma lem1638047 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1638048 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem1638049 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (real_pow x n) = (term71 x).
Proof. exact (MK_COMB (@lem1638048 x) (@lem1638047 n h1)). Qed.
Lemma lem1638051 (x : real) : (term71 x) = term72.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1638052 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (real_pow x n) = term72.
Proof. exact (TRANS (@lem1638049 x n h1) (@lem1638051 x)). Qed.
Lemma lem1638053 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1638054 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term34 x n) = (term105 x).
Proof. exact (MK_COMB (@lem1638053 x) (@lem1638052 x n h1)). Qed.
Lemma lem1638056 (x : real) : (term105 x) = x.
Proof. exact (EQ_MP (@lem1638027 x) (@lem1638026 x)). Qed.
Lemma lem1638057 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term34 x n) = x.
Proof. exact (TRANS (@lem1638054 x n h1) (@lem1638056 x)). Qed.
Lemma lem1638058 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1638059 (x : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term92 x n) = (real_lt x).
Proof. exact (MK_COMB (@lem1638058) (@lem1638057 x n h1)). Qed.
Lemma lem1638061 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1638062 (y : real) : (real_pow y) = (real_pow y).
Proof. exact (eq_refl (real_pow y)). Qed.
Lemma lem1638063 (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (real_pow y n) = (term71 y).
Proof. exact (MK_COMB (@lem1638062 y) (@lem1638061 n h1)). Qed.
Lemma lem1638065 (x : real) : (term71 x) = term72.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1638066 (y : real) : (term71 y) = term72.
Proof. exact (@lem1638065 y). Qed.
Lemma lem1638067 (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (real_pow y n) = term72.
Proof. exact (TRANS (@lem1638063 y n h1) (@lem1638066 y)). Qed.
Lemma lem1638068 (y : real) : (real_mul y) = (real_mul y).
Proof. exact (eq_refl (real_mul y)). Qed.
Lemma lem1638069 (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term34 y n) = (term105 y).
Proof. exact (MK_COMB (@lem1638068 y) (@lem1638067 y n h1)). Qed.
Lemma lem1638071 (x : real) : (term105 x) = x.
Proof. exact (EQ_MP (@lem1638027 x) (@lem1638026 x)). Qed.
Lemma lem1638072 (y : real) : (term105 y) = y.
Proof. exact (@lem1638071 y). Qed.
Lemma lem1638073 (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term34 y n) = y.
Proof. exact (TRANS (@lem1638069 y n h1) (@lem1638072 y)). Qed.
Lemma lem1638074 (x : real) (y : real) (n : nat) (h1 : n = (NUMERAL 0)) : (term94 x y n) = (real_lt x y).
Proof. exact (MK_COMB (@lem1638059 x n h1) (@lem1638073 y n h1)). Qed.
Lemma lem1638076 (x : real) (y : real) (h1 : real_lt x y) : (real_lt x y) = True.
Proof. exact (EQ_MP (@lem1638044 x y) (@lem1638024 x y h1)). Qed.
Lemma lem1638077 (n : nat) (x : real) (y : real) (h1 : n = (NUMERAL 0)) (h2 : real_lt x y) : (term94 x y n) = True.
Proof. exact (TRANS (@lem1638074 x y n h1) (@lem1638076 x y h2)). Qed.
Lemma lem1638078 (n : nat) (x : real) (y : real) (h1 : n = (NUMERAL 0)) (h2 : real_lt x y) : True = (term94 x y n).
Proof. exact (SYM (@lem1638077 n x y h1 h2)). Qed.
Lemma lem1638079 (n : nat) (x : real) (y : real) (h1 : n = (NUMERAL 0)) (h2 : real_lt x y) : term94 x y n.
Proof. exact (EQ_MP (@lem1638078 n x y h1 h2) (@lem0)). Qed.
Lemma lem1638116 (w : real) (y : real) (x : real) (z : real) : term17 w y x z.
Proof. exact (EQ_MP (@lem1637848 w y x z) (@lem1637847 w y x z)). Qed.
Lemma lem1638117 (x : real) (y : real) (n : nat) : term106 x y n.
Proof. exact (@lem1638116 x (real_pow x n) y (real_pow y n)). Qed.
Lemma lem1638126 (x : real) : (term5 x) = ((term5 x) = True).
Proof. exact (@lem7 (term5 x)). Qed.
Lemma lem1638128 (x : real) (y : real) : (real_lt x y) = ((real_lt x y) = True).
Proof. exact (@lem7 (real_lt x y)). Qed.
Lemma lem1638146 (x : real) (h1 : term5 x) : (term5 x) = True.
Proof. exact (EQ_MP (@lem1638126 x) (@lem1638025 x h1)). Qed.
Lemma lem1638147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1638148 (x : real) (h1 : term5 x) : (term107 x) = (and True).
Proof. exact (MK_COMB (@lem1638147) (@lem1638146 x h1)). Qed.
Lemma lem1638152 (x : real) (y : real) (h1 : real_lt x y) : (real_lt x y) = True.
Proof. exact (EQ_MP (@lem1638128 x y) (@lem1638024 x y h1)). Qed.
Lemma lem1638153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1638154 (x : real) (y : real) (h1 : real_lt x y) : (term108 x y) = (and True).
Proof. exact (MK_COMB (@lem1638153) (@lem1638152 x y h1)). Qed.
Lemma lem1638157 (x : real) (y : real) (n : nat) : (term109 x y n) = (term109 x y n).
Proof. exact (eq_refl (term109 x y n)). Qed.
Lemma lem1638158 (n : nat) (x : real) (y : real) (h1 : real_lt x y) : (term110 x y n) = (term111 x y n).
Proof. exact (MK_COMB (@lem1638154 x y h1) (@lem1638157 x y n)). Qed.
Lemma lem1638160 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1638161 (x : real) (y : real) (n : nat) : (term111 x y n) = (term109 x y n).
Proof. exact (@lem1638160 (term109 x y n)). Qed.
Lemma lem1638164 (n : nat) (x : real) (y : real) (h1 : real_lt x y) : (term110 x y n) = (term109 x y n).
Proof. exact (TRANS (@lem1638158 n x y h1) (@lem1638161 x y n)). Qed.
Lemma lem1638165 (n : nat) (x : real) (y : real) (h1 : term5 x) (h2 : real_lt x y) : (term112 x y n) = (term111 x y n).
Proof. exact (MK_COMB (@lem1638148 x h1) (@lem1638164 n x y h2)). Qed.
Lemma lem1638167 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1638168 (x : real) (y : real) (n : nat) : (term111 x y n) = (term109 x y n).
Proof. exact (@lem1638167 (term109 x y n)). Qed.
Lemma lem1638171 (n : nat) (x : real) (y : real) (h1 : term5 x) (h2 : real_lt x y) : (term112 x y n) = (term109 x y n).
Proof. exact (TRANS (@lem1638165 n x y h1 h2) (@lem1638168 x y n)). Qed.
Lemma lem1638172 (n : nat) (x : real) (y : real) (h1 : term5 x) (h2 : real_lt x y) : (term109 x y n) = (term112 x y n).
Proof. exact (SYM (@lem1638171 n x y h1 h2)). Qed.
Lemma lem1638174 (x : real) (n : nat) : term4 x n.
Proof. exact (EQ_MP (@lem1637811 x n) (@lem1637810 x n)). Qed.
Lemma lem1638183 (x : real) : (term5 x) = ((term5 x) = True).
Proof. exact (@lem7 (term5 x)). Qed.
Lemma lem1638201 (x : real) (h1 : term5 x) : (term5 x) = True.
Proof. exact (EQ_MP (@lem1638183 x) (@lem1638025 x h1)). Qed.
Lemma lem1638202 (x : real) (h1 : term5 x) : True = (term5 x).
Proof. exact (SYM (@lem1638201 x h1)). Qed.
Lemma lem1638203 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (EQ_MP (@lem1638202 x h1) (@lem0)). Qed.
Lemma lem1638204 (n : nat) (x : real) (h1 : term5 x) : term6 x n.
Proof. exact (@lem1638174 x n (@lem1638203 x h1)). Qed.
Lemma lem1638205 (n : nat) (h1 : term46 n) : term46 n.
Proof. exact (h1). Qed.
Lemma lem1638206 (x : real) (n : nat) (h1 : term46 n) : term113 n x.
Proof. exact (@lem1638205 n h1 x). Qed.
Lemma lem1638207 (x : real) (n : nat) : (term113 n x) = (term114 x n).
Proof. exact (eq_refl (term113 n x)). Qed.
Lemma lem1638208 (x : real) (n : nat) (h1 : term46 n) : term114 x n.
Proof. exact (EQ_MP (@lem1638207 x n) (@lem1638206 x n h1)). Qed.
Lemma lem1638209 (x : real) (y : real) (n : nat) (h1 : term46 n) : term115 x n y.
Proof. exact (@lem1638208 x n h1 y). Qed.
Lemma lem1638210 (x : real) (y : real) (n : nat) : (term115 x n y) = (term116 x y n).
Proof. exact (eq_refl (term115 x n y)). Qed.
Lemma lem1638211 (x : real) (y : real) (n : nat) (h1 : term46 n) : term116 x y n.
Proof. exact (EQ_MP (@lem1638210 x y n) (@lem1638209 x y n h1)). Qed.
Lemma lem1638212 (n : nat) (x : real) (y : real) (h1 : term117 n x y) : term117 n x y.
Proof. exact (h1). Qed.
Lemma lem1638213 (n : nat) (x : real) (y : real) (h1 : term46 n) (h2 : term117 n x y) : term118 x y n.
Proof. exact (@lem1638211 x y n h1 (@lem1638212 n x y h2)). Qed.
Lemma lem1638214 (n : nat) (x : real) (y : real) (h1 : term117 n x y) : term119 x y n.
Proof. exact (fun h0 : term46 n => @lem1638213 n x y h0 h1). Qed.
Lemma lem1638215 (n : nat) (h1 : term46 n) : term46 n.
Proof. exact (h1). Qed.
Lemma lem1638216 (n : nat) (x : real) (y : real) (h1 : term46 n) (h2 : term117 n x y) : term118 x y n.
Proof. exact (@lem1638214 n x y h2 (@lem1638215 n h1)). Qed.
Lemma lem1638217 (x : real) (y : real) (n : nat) (h1 : term46 n) : term116 x y n.
Proof. exact (fun h0 : term117 n x y => @lem1638216 n x y h1 h0). Qed.
Lemma lem1638218 (x : real) (n : nat) (h1 : term46 n) : term114 x n.
Proof. exact (fun y : real => @lem1638217 x y n h1). Qed.
Lemma lem1638219 (n : nat) (h1 : term46 n) : term46 n.
Proof. exact (fun x : real => @lem1638218 x n h1). Qed.
Lemma lem1638220 (n : nat) : term120 n.
Proof. exact (fun h0 : term46 n => @lem1638219 n h0). Qed.
Lemma lem1638221 (n : nat) (h1 : term46 n) : term46 n.
Proof. exact (@lem1638220 n (@lem1637899 n h1)). Qed.
Lemma lem1638222 (x : real) (n : nat) (h1 : term46 n) : term113 n x.
Proof. exact (@lem1638221 n h1 x). Qed.
Lemma lem1638223 (x : real) (n : nat) : (term113 n x) = (term114 x n).
Proof. exact (eq_refl (term113 n x)). Qed.
Lemma lem1638224 (x : real) (n : nat) (h1 : term46 n) : term114 x n.
Proof. exact (EQ_MP (@lem1638223 x n) (@lem1638222 x n h1)). Qed.
Lemma lem1638225 (x : real) (y : real) (n : nat) (h1 : term46 n) : term115 x n y.
Proof. exact (@lem1638224 x n h1 y). Qed.
Lemma lem1638226 (x : real) (y : real) (n : nat) : (term115 x n y) = (term116 x y n).
Proof. exact (eq_refl (term115 x n y)). Qed.
Lemma lem1638229 (x : real) (y : real) (n : nat) (h1 : term46 n) : term116 x y n.
Proof. exact (EQ_MP (@lem1638226 x y n) (@lem1638225 x y n h1)). Qed.
Lemma lem1638238 (x : real) : (term5 x) = ((term5 x) = True).
Proof. exact (@lem7 (term5 x)). Qed.
Lemma lem1638240 (x : real) (y : real) : (real_lt x y) = ((real_lt x y) = True).
Proof. exact (@lem7 (real_lt x y)). Qed.
Lemma lem1638242 (n : nat) : term121 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem1638258 (n : nat) (h1 : term30 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1638242 n (@lem1637854 n h1)). Qed.
Lemma lem1638259 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1638260 (n : nat) (h1 : term30 n) : (term30 n) = (~ False).
Proof. exact (MK_COMB (@lem1638259) (@lem1638258 n h1)). Qed.
Lemma lem1638262 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1638263 (n : nat) (h1 : term30 n) : (term30 n) = True.
Proof. exact (TRANS (@lem1638260 n h1) (@lem1638262)). Qed.
Lemma lem1638264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1638265 (n : nat) (h1 : term30 n) : (term122 n) = (and True).
Proof. exact (MK_COMB (@lem1638264) (@lem1638263 n h1)). Qed.
Lemma lem1638269 (x : real) (h1 : term5 x) : (term5 x) = True.
Proof. exact (EQ_MP (@lem1638238 x) (@lem1638025 x h1)). Qed.
Lemma lem1638270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1638271 (x : real) (h1 : term5 x) : (term107 x) = (and True).
Proof. exact (MK_COMB (@lem1638270) (@lem1638269 x h1)). Qed.
Lemma lem1638273 (x : real) (y : real) (h1 : real_lt x y) : (real_lt x y) = True.
Proof. exact (EQ_MP (@lem1638240 x y) (@lem1638024 x y h1)). Qed.
Lemma lem1638274 (x : real) (y : real) (h1 : term5 x) (h2 : real_lt x y) : (term67 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1638271 x h1) (@lem1638273 x y h2)). Qed.
Lemma lem1638276 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1638277 : (True /\ True) = True.
Proof. exact (@lem1638276 True). Qed.
Lemma lem1638278 (x : real) (y : real) (h1 : term5 x) (h2 : real_lt x y) : (term67 x y) = True.
Proof. exact (TRANS (@lem1638274 x y h1 h2) (@lem1638277)). Qed.
Lemma lem1638279 (n : nat) (x : real) (y : real) (h1 : term30 n) (h2 : term5 x) (h3 : real_lt x y) : (term117 n x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1638265 n h1) (@lem1638278 x y h2 h3)). Qed.
Lemma lem1638281 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1638282 : (True /\ True) = True.
Proof. exact (@lem1638281 True). Qed.
Lemma lem1638283 (n : nat) (x : real) (y : real) (h1 : term30 n) (h2 : term5 x) (h3 : real_lt x y) : (term117 n x y) = True.
Proof. exact (TRANS (@lem1638279 n x y h1 h2 h3) (@lem1638282)). Qed.
Lemma lem1638284 (n : nat) (x : real) (y : real) (h1 : term30 n) (h2 : term5 x) (h3 : real_lt x y) : True = (term117 n x y).
Proof. exact (SYM (@lem1638283 n x y h1 h2 h3)). Qed.
Lemma lem1638285 (n : nat) (x : real) (y : real) (h1 : term30 n) (h2 : term5 x) (h3 : real_lt x y) : term117 n x y.
Proof. exact (EQ_MP (@lem1638284 n x y h1 h2 h3) (@lem0)). Qed.
Lemma lem1638286 (n : nat) (x : real) (y : real) (h1 : term46 n) (h2 : term30 n) (h3 : term5 x) (h4 : real_lt x y) : term118 x y n.
Proof. exact (@lem1638229 x y n h1 (@lem1638285 n x y h2 h3 h4)). Qed.
Lemma lem1638287 (n : nat) (x : real) (y : real) (h1 : term46 n) (h2 : term30 n) (h3 : term5 x) (h4 : real_lt x y) : term109 x y n.
Proof. exact (conj (@lem1638204 n x h3) (@lem1638286 n x y h1 h2 h3 h4)). Qed.
Lemma lem1638288 (n : nat) (x : real) (y : real) (h1 : term46 n) (h2 : term30 n) (h3 : term5 x) (h4 : real_lt x y) : term112 x y n.
Proof. exact (EQ_MP (@lem1638172 n x y h3 h4) (@lem1638287 n x y h1 h2 h3 h4)). Qed.
Lemma lem1638290 (n : nat) (x : real) (y : real) (h1 : term46 n) (h2 : term30 n) (h3 : term5 x) (h4 : real_lt x y) : term94 x y n.
Proof. exact (@lem1638117 x y n (@lem1638288 n x y h1 h2 h3 h4)). Qed.
Lemma lem1638291 (n : nat) (x : real) (y : real) (h1 : term46 n) (h2 : term5 x) (h3 : real_lt x y) : term94 x y n.
Proof. exact (or_elim (@lem1637852 n) (fun h0 : n = (NUMERAL 0) => @lem1638079 n x y h0 h3) (fun h0 : term30 n => @lem1638290 n x y h1 h0 h2 h3)). Qed.
Lemma lem1638292 (x : real) (y : real) (h1 : term67 x y) : real_lt x y.
Proof. exact (proj2 (@lem1638023 x y h1)). Qed.
Lemma lem1638293 (x : real) (y : real) (h1 : term67 x y) : term5 x.
Proof. exact (proj1 (@lem1638023 x y h1)). Qed.
Lemma lem1638294 (n : nat) (x : real) (y : real) (h1 : term46 n) (h2 : term5 x) (h3 : real_lt x y) : (real_lt x y) = (term94 x y n).
Proof. exact (prop_ext (fun h4 : real_lt x y => @lem1638291 n x y h1 h2 h3) (fun h4 : term94 x y n => @lem1638024 x y h3)). Qed.
Lemma lem1638295 (n : nat) (x : real) (y : real) (h1 : term46 n) (h2 : term5 x) (h3 : real_lt x y) : term94 x y n.
Proof. exact (EQ_MP (@lem1638294 n x y h1 h2 h3) (@lem1638024 x y h3)). Qed.
Lemma lem1638296 (n : nat) (x : real) (y : real) (h1 : term46 n) (h2 : term5 x) (h3 : real_lt x y) : (term5 x) = (term94 x y n).
Proof. exact (prop_ext (fun h4 : term5 x => @lem1638295 n x y h1 h2 h3) (fun h4 : term94 x y n => @lem1638025 x h2)). Qed.
Lemma lem1638297 (n : nat) (x : real) (y : real) (h1 : term46 n) (h2 : term5 x) (h3 : real_lt x y) : term94 x y n.
Proof. exact (EQ_MP (@lem1638296 n x y h1 h2 h3) (@lem1638025 x h2)). Qed.
Lemma lem1638298 (n : nat) (y : real) (x : real) (h1 : term46 n) (h2 : term67 x y) (h3 : term5 x) : (real_lt x y) = (term94 x y n).
Proof. exact (prop_ext (fun h4 : real_lt x y => @lem1638297 n x y h1 h3 h4) (fun h4 : term94 x y n => @lem1638292 x y h2)). Qed.
Lemma lem1638299 (n : nat) (y : real) (x : real) (h1 : term46 n) (h2 : term67 x y) (h3 : term5 x) : term94 x y n.
Proof. exact (EQ_MP (@lem1638298 n y x h1 h2 h3) (@lem1638292 x y h2)). Qed.
Lemma lem1638300 (n : nat) (x : real) (y : real) (h1 : term46 n) (h2 : term67 x y) : (term5 x) = (term94 x y n).
Proof. exact (prop_ext (fun h3 : term5 x => @lem1638299 n y x h1 h2 h3) (fun h3 : term94 x y n => @lem1638293 x y h2)). Qed.
Lemma lem1638301 (n : nat) (x : real) (y : real) (h1 : term46 n) (h2 : term67 x y) : term94 x y n.
Proof. exact (EQ_MP (@lem1638300 n x y h1 h2) (@lem1638293 x y h2)). Qed.
Lemma lem1638302 (x : real) (y : real) (n : nat) (h1 : term46 n) : term96 x y n.
Proof. exact (fun h0 : term67 x y => @lem1638301 n x y h1 h0). Qed.
Lemma lem1638307 (x : real) (n : nat) (h1 : term46 n) : term100 x n.
Proof. exact (fun y : real => @lem1638302 x y n h1). Qed.
Lemma lem1638312 (n : nat) (h1 : term46 n) : term103 n.
Proof. exact (fun x : real => @lem1638307 x n h1). Qed.
Lemma lem1638313 (n : nat) (h1 : term46 n) : term50 n.
Proof. exact (EQ_MP (@lem1638022 n) (@lem1638312 n h1)). Qed.
Lemma lem1638314 (n : nat) : term52 n.
Proof. exact (fun h0 : term46 n => @lem1638313 n h0). Qed.
Lemma lem1638319 : term56.
Proof. exact (fun n : nat => @lem1638314 n). Qed.
Lemma lem1638320 : term58.
Proof. exact (conj (@lem1637963) (@lem1638319)). Qed.
Lemma lem1638321 : term63.
Proof. exact (@lem1637898 (@lem1638320)). Qed.
