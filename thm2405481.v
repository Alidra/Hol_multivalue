Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2405481_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import INT_LE_ANTISYM_spec.
Require Import LE_0_spec.
Require Import LE_ANTISYM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2403913_spec.
Require Import thm2403914_spec.
Require Import thm2403916_spec.
Require Import thm7_spec.
Require Import thm89498_spec.
Lemma lem2404787 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem2404788 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2404789 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2404788 n) (@lem2404787 n)). Qed.
Lemma lem2404790 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem2404799 : term2.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem2404800 (m : nat) : term3 m.
Proof. exact (@lem2404799 m). Qed.
Lemma lem2404801 (m : nat) : (term3 m) = ((term4 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem2404805 (m : nat) (n : nat) (h1 : (term5 n m) = (m = n)) : (term5 n m) = (m = n).
Proof. exact (h1). Qed.
Lemma lem2404806 (m : nat) (n : nat) (h1 : (term5 n m) = (m = n)) : (m = n) = (term5 n m).
Proof. exact (SYM (@lem2404805 m n h1)). Qed.
Lemma lem2404807 (n : nat) (m : nat) (h1 : (m = n) = (term5 n m)) : (m = n) = (term5 n m).
Proof. exact (h1). Qed.
Lemma lem2404808 (n : nat) (m : nat) (h1 : (m = n) = (term5 n m)) : (term5 n m) = (m = n).
Proof. exact (SYM (@lem2404807 n m h1)). Qed.
Lemma lem2404809 (n : nat) (m : nat) : ((term5 n m) = (m = n)) = ((m = n) = (term5 n m)).
Proof. exact (prop_ext (fun h1 : (term5 n m) = (m = n) => @lem2404806 m n h1) (fun h1 : (m = n) = (term5 n m) => @lem2404808 n m h1)). Qed.
Lemma lem2404810 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem2404809 n m)). Qed.
Lemma lem2404811 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2404812 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem2404811) (@lem2404810 m)). Qed.
Lemma lem2404813 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem2404812 m)). Qed.
Lemma lem2404814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2404815 : term12 = term13.
Proof. exact (MK_COMB (@lem2404814) (@lem2404813)). Qed.
Lemma lem2404816 : term13.
Proof. exact (EQ_MP (@lem2404815) (@lem92426)). Qed.
Lemma lem2404819 (x : int) (y : int) (h1 : (term14 y x) = (x = y)) : (term14 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem2404820 (x : int) (y : int) (h1 : (term14 y x) = (x = y)) : (x = y) = (term14 y x).
Proof. exact (SYM (@lem2404819 x y h1)). Qed.
Lemma lem2404821 (y : int) (x : int) (h1 : (x = y) = (term14 y x)) : (x = y) = (term14 y x).
Proof. exact (h1). Qed.
Lemma lem2404822 (y : int) (x : int) (h1 : (x = y) = (term14 y x)) : (term14 y x) = (x = y).
Proof. exact (SYM (@lem2404821 y x h1)). Qed.
Lemma lem2404823 (y : int) (x : int) : ((term14 y x) = (x = y)) = ((x = y) = (term14 y x)).
Proof. exact (prop_ext (fun h1 : (term14 y x) = (x = y) => @lem2404820 x y h1) (fun h1 : (x = y) = (term14 y x) => @lem2404822 y x h1)). Qed.
Lemma lem2404824 (x : int) : (term15 x) = (term16 x).
Proof. exact (fun_ext (fun y : int => @lem2404823 y x)). Qed.
Lemma lem2404825 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2404826 (x : int) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem2404825) (@lem2404824 x)). Qed.
Lemma lem2404827 : term19 = term20.
Proof. exact (fun_ext (fun x : int => @lem2404826 x)). Qed.
Lemma lem2404828 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2404829 : term21 = term22.
Proof. exact (MK_COMB (@lem2404828) (@lem2404827)). Qed.
Lemma lem2404830 : term22.
Proof. exact (EQ_MP (@lem2404829) (@lem2302347)). Qed.
Lemma lem2404831 (m : nat) : term23 m.
Proof. exact (@lem2404816 m). Qed.
Lemma lem2404832 (m : nat) : (term23 m) = (term9 m).
Proof. exact (eq_refl (term23 m)). Qed.
Lemma lem2404833 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem2404832 m) (@lem2404831 m)). Qed.
Lemma lem2404834 (m : nat) (n : nat) : term24 m n.
Proof. exact (@lem2404833 m n). Qed.
Lemma lem2404835 (n : nat) (m : nat) : (term24 m n) = ((m = n) = (term5 n m)).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem2404837 (x : int) : term25 x.
Proof. exact (@lem2404830 x). Qed.
Lemma lem2404838 (x : int) : (term25 x) = (term18 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem2404839 (x : int) : term18 x.
Proof. exact (EQ_MP (@lem2404838 x) (@lem2404837 x)). Qed.
Lemma lem2404840 (x : int) (y : int) : term26 x y.
Proof. exact (@lem2404839 x y). Qed.
Lemma lem2404841 (y : int) (x : int) : (term26 x y) = ((x = y) = (term14 y x)).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem2404856 (y : int) (x : int) : (x = y) = (term14 y x).
Proof. exact (EQ_MP (@lem2404841 y x) (@lem2404840 x y)). Qed.
Lemma lem2404857 (n : nat) (m : nat) : ((int_of_num m) = (int_of_num n)) = (term27 n m).
Proof. exact (@lem2404856 (int_of_num n) (int_of_num m)). Qed.
Lemma lem2404860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2404861 (n : nat) (m : nat) : (term28 m n) = (term29 n m).
Proof. exact (MK_COMB (@lem2404860) (@lem2404857 n m)). Qed.
Lemma lem2404865 (n : nat) (m : nat) : (m = n) = (term5 n m).
Proof. exact (EQ_MP (@lem2404835 n m) (@lem2404834 m n)). Qed.
Lemma lem2404868 (n : nat) (m : nat) : (((int_of_num m) = (int_of_num n)) = (m = n)) = ((term27 n m) = (term5 n m)).
Proof. exact (MK_COMB (@lem2404861 n m) (@lem2404865 n m)). Qed.
Lemma lem2404875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2404876 (n : nat) (m : nat) : (term30 m n) = (term31 n m).
Proof. exact (MK_COMB (@lem2404875) (@lem2404868 n m)). Qed.
Lemma lem2404890 (y : int) (x : int) : (x = y) = (term14 y x).
Proof. exact (EQ_MP (@lem2404841 y x) (@lem2404840 x y)). Qed.
Lemma lem2404891 (n : nat) (m : nat) : ((term32 m) = (term32 n)) = (term33 n m).
Proof. exact (@lem2404890 (term32 n) (term32 m)). Qed.
Lemma lem2404894 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2404895 (n : nat) (m : nat) : (term34 m n) = (term35 n m).
Proof. exact (MK_COMB (@lem2404894) (@lem2404891 n m)). Qed.
Lemma lem2404899 (n : nat) (m : nat) : (m = n) = (term5 n m).
Proof. exact (EQ_MP (@lem2404835 n m) (@lem2404834 m n)). Qed.
Lemma lem2404902 (n : nat) (m : nat) : (((term32 m) = (term32 n)) = (m = n)) = ((term33 n m) = (term5 n m)).
Proof. exact (MK_COMB (@lem2404895 n m) (@lem2404899 n m)). Qed.
Lemma lem2404909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2404910 (n : nat) (m : nat) : (term36 m n) = (term37 n m).
Proof. exact (MK_COMB (@lem2404909) (@lem2404902 n m)). Qed.
Lemma lem2404924 (y : int) (x : int) : (x = y) = (term14 y x).
Proof. exact (EQ_MP (@lem2404841 y x) (@lem2404840 x y)). Qed.
Lemma lem2404925 (n : nat) (m : nat) : ((term32 m) = (int_of_num n)) = (term38 n m).
Proof. exact (@lem2404924 (int_of_num n) (term32 m)). Qed.
Lemma lem2404928 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2404929 (n : nat) (m : nat) : (term39 m n) = (term40 n m).
Proof. exact (MK_COMB (@lem2404928) (@lem2404925 n m)). Qed.
Lemma lem2404935 (n : nat) (m : nat) : (m = n) = (term5 n m).
Proof. exact (EQ_MP (@lem2404835 n m) (@lem2404834 m n)). Qed.
Lemma lem2404936 (m : nat) : (m = (NUMERAL 0)) = (term41 m).
Proof. exact (@lem2404935 (NUMERAL 0) m). Qed.
Lemma lem2404939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2404940 (m : nat) : (term42 m) = (term43 m).
Proof. exact (MK_COMB (@lem2404939) (@lem2404936 m)). Qed.
Lemma lem2404944 (n : nat) (m : nat) : (m = n) = (term5 n m).
Proof. exact (EQ_MP (@lem2404835 n m) (@lem2404834 m n)). Qed.
Lemma lem2404945 (n : nat) : (n = (NUMERAL 0)) = (term41 n).
Proof. exact (@lem2404944 (NUMERAL 0) n). Qed.
Lemma lem2404948 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem2404940 m) (@lem2404945 n)). Qed.
Lemma lem2404951 (m : nat) (n : nat) : (((term32 m) = (int_of_num n)) = (term44 m n)) = ((term38 n m) = (term45 m n)).
Proof. exact (MK_COMB (@lem2404929 n m) (@lem2404948 m n)). Qed.
Lemma lem2404958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2404959 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem2404958) (@lem2404951 m n)). Qed.
Lemma lem2404971 (y : int) (x : int) : (x = y) = (term14 y x).
Proof. exact (EQ_MP (@lem2404841 y x) (@lem2404840 x y)). Qed.
Lemma lem2404972 (n : nat) (m : nat) : ((int_of_num m) = (term32 n)) = (term48 n m).
Proof. exact (@lem2404971 (term32 n) (int_of_num m)). Qed.
Lemma lem2404975 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2404976 (n : nat) (m : nat) : (term49 m n) = (term50 n m).
Proof. exact (MK_COMB (@lem2404975) (@lem2404972 n m)). Qed.
Lemma lem2404982 (n : nat) (m : nat) : (m = n) = (term5 n m).
Proof. exact (EQ_MP (@lem2404835 n m) (@lem2404834 m n)). Qed.
Lemma lem2404983 (m : nat) : (m = (NUMERAL 0)) = (term41 m).
Proof. exact (@lem2404982 (NUMERAL 0) m). Qed.
Lemma lem2404986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2404987 (m : nat) : (term42 m) = (term43 m).
Proof. exact (MK_COMB (@lem2404986) (@lem2404983 m)). Qed.
Lemma lem2404991 (n : nat) (m : nat) : (m = n) = (term5 n m).
Proof. exact (EQ_MP (@lem2404835 n m) (@lem2404834 m n)). Qed.
Lemma lem2404992 (n : nat) : (n = (NUMERAL 0)) = (term41 n).
Proof. exact (@lem2404991 (NUMERAL 0) n). Qed.
Lemma lem2404995 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem2404987 m) (@lem2404992 n)). Qed.
Lemma lem2404998 (m : nat) (n : nat) : (((int_of_num m) = (term32 n)) = (term44 m n)) = ((term48 n m) = (term45 m n)).
Proof. exact (MK_COMB (@lem2404976 n m) (@lem2404995 m n)). Qed.
Lemma lem2405005 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (MK_COMB (@lem2404959 m n) (@lem2404998 m n)). Qed.
Lemma lem2405008 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (MK_COMB (@lem2404910 n m) (@lem2405005 m n)). Qed.
Lemma lem2405011 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem2404876 n m) (@lem2405008 m n)). Qed.
Lemma lem2405014 (m : nat) (n : nat) : (term56 m n) = (term55 m n).
Proof. exact (SYM (@lem2405011 m n)). Qed.
Lemma lem2405022 (m : nat) (n : nat) : (term57 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2405023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405024 (m : nat) (n : nat) : (term58 m n) = (term59 m n).
Proof. exact (MK_COMB (@lem2405023) (@lem2405022 m n)). Qed.
Lemma lem2405026 (m : nat) (n : nat) : (term57 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2405027 (n : nat) (m : nat) : (term57 n m) = (Peano.le n m).
Proof. exact (@lem2405026 n m). Qed.
Lemma lem2405028 (n : nat) (m : nat) : (term27 n m) = (term5 n m).
Proof. exact (MK_COMB (@lem2405024 m n) (@lem2405027 n m)). Qed.
Lemma lem2405031 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2405032 (n : nat) (m : nat) : (term29 n m) = (term60 n m).
Proof. exact (MK_COMB (@lem2405031) (@lem2405028 n m)). Qed.
Lemma lem2405035 (n : nat) (m : nat) : (term5 n m) = (term5 n m).
Proof. exact (eq_refl (term5 n m)). Qed.
Lemma lem2405036 (n : nat) (m : nat) : ((term27 n m) = (term5 n m)) = ((term5 n m) = (term5 n m)).
Proof. exact (MK_COMB (@lem2405032 n m) (@lem2405035 n m)). Qed.
Lemma lem2405038 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405039 (x : Prop) : (x = x) = True.
Proof. exact (@lem2405038 Prop x). Qed.
Lemma lem2405040 (n : nat) (m : nat) : ((term5 n m) = (term5 n m)) = True.
Proof. exact (@lem2405039 (term5 n m)). Qed.
Lemma lem2405041 (n : nat) (m : nat) : ((term27 n m) = (term5 n m)) = True.
Proof. exact (TRANS (@lem2405036 n m) (@lem2405040 n m)). Qed.
Lemma lem2405042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405043 (n : nat) (m : nat) : (term31 n m) = (and True).
Proof. exact (MK_COMB (@lem2405042) (@lem2405041 n m)). Qed.
Lemma lem2405051 (n : nat) (m : nat) : (term61 m n) = (Peano.le n m).
Proof. exact (proj1 (@lem2403916 m n)). Qed.
Lemma lem2405052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405053 (n : nat) (m : nat) : (term62 m n) = (term59 n m).
Proof. exact (MK_COMB (@lem2405052) (@lem2405051 n m)). Qed.
Lemma lem2405055 (n : nat) (m : nat) : (term61 m n) = (Peano.le n m).
Proof. exact (proj1 (@lem2403916 m n)). Qed.
Lemma lem2405056 (m : nat) (n : nat) : (term61 n m) = (Peano.le m n).
Proof. exact (@lem2405055 m n). Qed.
Lemma lem2405057 (m : nat) (n : nat) : (term33 n m) = (term5 m n).
Proof. exact (MK_COMB (@lem2405053 n m) (@lem2405056 m n)). Qed.
Lemma lem2405060 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2405061 (m : nat) (n : nat) : (term35 n m) = (term60 m n).
Proof. exact (MK_COMB (@lem2405060) (@lem2405057 m n)). Qed.
Lemma lem2405064 (n : nat) (m : nat) : (term5 n m) = (term5 n m).
Proof. exact (eq_refl (term5 n m)). Qed.
Lemma lem2405065 (n : nat) (m : nat) : ((term33 n m) = (term5 n m)) = ((term5 m n) = (term5 n m)).
Proof. exact (MK_COMB (@lem2405061 m n) (@lem2405064 n m)). Qed.
Lemma lem2405068 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405069 (n : nat) (m : nat) : (term37 n m) = (term63 n m).
Proof. exact (MK_COMB (@lem2405068) (@lem2405065 n m)). Qed.
Lemma lem2405077 (m : nat) (n : nat) : (term64 m n) = True.
Proof. exact (proj1 (@lem2403913 m n)). Qed.
Lemma lem2405078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405079 (m : nat) (n : nat) : (term65 m n) = (and True).
Proof. exact (MK_COMB (@lem2405078) (@lem2405077 m n)). Qed.
Lemma lem2405081 (m : nat) (n : nat) : (term66 m n) = (term44 m n).
Proof. exact (proj2 (@lem2403916 m n)). Qed.
Lemma lem2405082 (n : nat) (m : nat) : (term66 n m) = (term44 n m).
Proof. exact (@lem2405081 n m). Qed.
Lemma lem2405089 (n : nat) (m : nat) : (term38 n m) = (term67 n m).
Proof. exact (MK_COMB (@lem2405079 m n) (@lem2405082 n m)). Qed.
Lemma lem2405091 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2405092 (n : nat) (m : nat) : (term67 n m) = (term44 n m).
Proof. exact (@lem2405091 (term44 n m)). Qed.
Lemma lem2405099 (n : nat) (m : nat) : (term38 n m) = (term44 n m).
Proof. exact (TRANS (@lem2405089 n m) (@lem2405092 n m)). Qed.
Lemma lem2405100 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2405101 (n : nat) (m : nat) : (term40 n m) = (term68 n m).
Proof. exact (MK_COMB (@lem2405100) (@lem2405099 n m)). Qed.
Lemma lem2405107 (m : nat) : (term4 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem2404801 m) (@lem2404800 m)). Qed.
Lemma lem2405110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405111 (m : nat) : (term69 m) = (term42 m).
Proof. exact (MK_COMB (@lem2405110) (@lem2405107 m)). Qed.
Lemma lem2405113 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem2404790 n) (@lem2404789 n)). Qed.
Lemma lem2405114 (m : nat) : (term1 m) = True.
Proof. exact (@lem2405113 m). Qed.
Lemma lem2405115 (m : nat) : (term41 m) = (term70 m).
Proof. exact (MK_COMB (@lem2405111 m) (@lem2405114 m)). Qed.
Lemma lem2405117 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2405118 (m : nat) : (term70 m) = (m = (NUMERAL 0)).
Proof. exact (@lem2405117 (m = (NUMERAL 0))). Qed.
Lemma lem2405121 (m : nat) : (term41 m) = (m = (NUMERAL 0)).
Proof. exact (TRANS (@lem2405115 m) (@lem2405118 m)). Qed.
Lemma lem2405122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405123 (m : nat) : (term43 m) = (term42 m).
Proof. exact (MK_COMB (@lem2405122) (@lem2405121 m)). Qed.
Lemma lem2405127 (m : nat) : (term4 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem2404801 m) (@lem2404800 m)). Qed.
Lemma lem2405128 (n : nat) : (term4 n) = (n = (NUMERAL 0)).
Proof. exact (@lem2405127 n). Qed.
Lemma lem2405131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405132 (n : nat) : (term69 n) = (term42 n).
Proof. exact (MK_COMB (@lem2405131) (@lem2405128 n)). Qed.
Lemma lem2405134 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem2404790 n) (@lem2404789 n)). Qed.
Lemma lem2405135 (n : nat) : (term41 n) = (term70 n).
Proof. exact (MK_COMB (@lem2405132 n) (@lem2405134 n)). Qed.
Lemma lem2405137 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2405138 (n : nat) : (term70 n) = (n = (NUMERAL 0)).
Proof. exact (@lem2405137 (n = (NUMERAL 0))). Qed.
Lemma lem2405141 (n : nat) : (term41 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem2405135 n) (@lem2405138 n)). Qed.
Lemma lem2405142 (m : nat) (n : nat) : (term45 m n) = (term44 m n).
Proof. exact (MK_COMB (@lem2405123 m) (@lem2405141 n)). Qed.
Lemma lem2405145 (m : nat) (n : nat) : ((term38 n m) = (term45 m n)) = ((term44 n m) = (term44 m n)).
Proof. exact (MK_COMB (@lem2405101 n m) (@lem2405142 m n)). Qed.
Lemma lem2405148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405149 (m : nat) (n : nat) : (term47 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem2405148) (@lem2405145 m n)). Qed.
Lemma lem2405155 (m : nat) (n : nat) : (term66 m n) = (term44 m n).
Proof. exact (proj2 (@lem2403916 m n)). Qed.
Lemma lem2405162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405163 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (MK_COMB (@lem2405162) (@lem2405155 m n)). Qed.
Lemma lem2405165 (m : nat) (n : nat) : (term64 m n) = True.
Proof. exact (proj1 (@lem2403913 m n)). Qed.
Lemma lem2405166 (n : nat) (m : nat) : (term64 n m) = True.
Proof. exact (@lem2405165 n m). Qed.
Lemma lem2405167 (m : nat) (n : nat) : (term48 n m) = (term74 m n).
Proof. exact (MK_COMB (@lem2405163 m n) (@lem2405166 n m)). Qed.
Lemma lem2405169 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2405170 (m : nat) (n : nat) : (term74 m n) = (term44 m n).
Proof. exact (@lem2405169 (term44 m n)). Qed.
Lemma lem2405177 (m : nat) (n : nat) : (term48 n m) = (term44 m n).
Proof. exact (TRANS (@lem2405167 m n) (@lem2405170 m n)). Qed.
Lemma lem2405178 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2405179 (m : nat) (n : nat) : (term50 n m) = (term68 m n).
Proof. exact (MK_COMB (@lem2405178) (@lem2405177 m n)). Qed.
Lemma lem2405185 (m : nat) : (term4 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem2404801 m) (@lem2404800 m)). Qed.
Lemma lem2405188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405189 (m : nat) : (term69 m) = (term42 m).
Proof. exact (MK_COMB (@lem2405188) (@lem2405185 m)). Qed.
Lemma lem2405191 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem2404790 n) (@lem2404789 n)). Qed.
Lemma lem2405192 (m : nat) : (term1 m) = True.
Proof. exact (@lem2405191 m). Qed.
Lemma lem2405193 (m : nat) : (term41 m) = (term70 m).
Proof. exact (MK_COMB (@lem2405189 m) (@lem2405192 m)). Qed.
Lemma lem2405195 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2405196 (m : nat) : (term70 m) = (m = (NUMERAL 0)).
Proof. exact (@lem2405195 (m = (NUMERAL 0))). Qed.
Lemma lem2405199 (m : nat) : (term41 m) = (m = (NUMERAL 0)).
Proof. exact (TRANS (@lem2405193 m) (@lem2405196 m)). Qed.
Lemma lem2405200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405201 (m : nat) : (term43 m) = (term42 m).
Proof. exact (MK_COMB (@lem2405200) (@lem2405199 m)). Qed.
Lemma lem2405205 (m : nat) : (term4 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem2404801 m) (@lem2404800 m)). Qed.
Lemma lem2405206 (n : nat) : (term4 n) = (n = (NUMERAL 0)).
Proof. exact (@lem2405205 n). Qed.
Lemma lem2405209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405210 (n : nat) : (term69 n) = (term42 n).
Proof. exact (MK_COMB (@lem2405209) (@lem2405206 n)). Qed.
Lemma lem2405212 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem2404790 n) (@lem2404789 n)). Qed.
Lemma lem2405213 (n : nat) : (term41 n) = (term70 n).
Proof. exact (MK_COMB (@lem2405210 n) (@lem2405212 n)). Qed.
Lemma lem2405215 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2405216 (n : nat) : (term70 n) = (n = (NUMERAL 0)).
Proof. exact (@lem2405215 (n = (NUMERAL 0))). Qed.
Lemma lem2405219 (n : nat) : (term41 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem2405213 n) (@lem2405216 n)). Qed.
Lemma lem2405220 (m : nat) (n : nat) : (term45 m n) = (term44 m n).
Proof. exact (MK_COMB (@lem2405201 m) (@lem2405219 n)). Qed.
Lemma lem2405223 (m : nat) (n : nat) : ((term48 n m) = (term45 m n)) = ((term44 m n) = (term44 m n)).
Proof. exact (MK_COMB (@lem2405179 m n) (@lem2405220 m n)). Qed.
Lemma lem2405225 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405226 (x : Prop) : (x = x) = True.
Proof. exact (@lem2405225 Prop x). Qed.
Lemma lem2405227 (m : nat) (n : nat) : ((term44 m n) = (term44 m n)) = True.
Proof. exact (@lem2405226 (term44 m n)). Qed.
Lemma lem2405228 (m : nat) (n : nat) : ((term48 n m) = (term45 m n)) = True.
Proof. exact (TRANS (@lem2405223 m n) (@lem2405227 m n)). Qed.
Lemma lem2405229 (m : nat) (n : nat) : (term52 m n) = (term75 m n).
Proof. exact (MK_COMB (@lem2405149 m n) (@lem2405228 m n)). Qed.
Lemma lem2405231 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2405232 (m : nat) (n : nat) : (term75 m n) = ((term44 n m) = (term44 m n)).
Proof. exact (@lem2405231 ((term44 n m) = (term44 m n))). Qed.
Lemma lem2405247 (m : nat) (n : nat) : (term52 m n) = ((term44 n m) = (term44 m n)).
Proof. exact (TRANS (@lem2405229 m n) (@lem2405232 m n)). Qed.
Lemma lem2405248 (m : nat) (n : nat) : (term54 m n) = (term76 m n).
Proof. exact (MK_COMB (@lem2405069 n m) (@lem2405247 m n)). Qed.
Lemma lem2405251 (m : nat) (n : nat) : (term56 m n) = (term77 m n).
Proof. exact (MK_COMB (@lem2405043 n m) (@lem2405248 m n)). Qed.
Lemma lem2405253 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2405254 (m : nat) (n : nat) : (term77 m n) = (term76 m n).
Proof. exact (@lem2405253 (term76 m n)). Qed.
Lemma lem2405277 (m : nat) (n : nat) : (term56 m n) = (term76 m n).
Proof. exact (TRANS (@lem2405251 m n) (@lem2405254 m n)). Qed.
Lemma lem2405278 (m : nat) (n : nat) : (term76 m n) = (term56 m n).
Proof. exact (SYM (@lem2405277 m n)). Qed.
Lemma lem2405287 (n : nat) (m : nat) : term78 n m.
Proof. exact (@lem9851 (Peano.le n m)). Qed.
Lemma lem2405288 (n : nat) (m : nat) : (term78 n m) = (term79 n m).
Proof. exact (eq_refl (term78 n m)). Qed.
Lemma lem2405289 (n : nat) (m : nat) : term79 n m.
Proof. exact (EQ_MP (@lem2405288 n m) (@lem2405287 n m)). Qed.
Lemma lem2405290 (n : nat) (m : nat) (h1 : (Peano.le n m) = True) : (Peano.le n m) = True.
Proof. exact (h1). Qed.
Lemma lem2405291 (n : nat) (m : nat) (h1 : (Peano.le n m) = False) : (Peano.le n m) = False.
Proof. exact (h1). Qed.
Lemma lem2405300 (m : nat) (n : nat) : (term80 m n) = (term80 m n).
Proof. exact (eq_refl (term80 m n)). Qed.
Lemma lem2405301 (n : nat) (m : nat) (h1 : (Peano.le n m) = True) : (term81 n m) = (term82 m n).
Proof. exact (MK_COMB (@lem2405300 m n) (@lem2405290 n m h1)). Qed.
Lemma lem2405302 (m : nat) (n : nat) : (term82 m n) = ((term83 m n) = (term84 m n)).
Proof. exact (eq_refl (term82 m n)). Qed.
Lemma lem2405303 (n : nat) (m : nat) : (term85 n m) = (term85 n m).
Proof. exact (eq_refl (term85 n m)). Qed.
Lemma lem2405304 (m : nat) (n : nat) : ((term81 n m) = (term82 m n)) = ((term81 n m) = ((term83 m n) = (term84 m n))).
Proof. exact (MK_COMB (@lem2405303 n m) (@lem2405302 m n)). Qed.
Lemma lem2405305 (n : nat) (m : nat) : (term81 n m) = ((term5 m n) = (term5 n m)).
Proof. exact (eq_refl (term81 n m)). Qed.
Lemma lem2405306 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2405307 (n : nat) (m : nat) : (term85 n m) = (term86 n m).
Proof. exact (MK_COMB (@lem2405306) (@lem2405305 n m)). Qed.
Lemma lem2405308 (m : nat) (n : nat) : ((term83 m n) = (term84 m n)) = ((term83 m n) = (term84 m n)).
Proof. exact (eq_refl ((term83 m n) = (term84 m n))). Qed.
Lemma lem2405309 (m : nat) (n : nat) : ((term81 n m) = ((term83 m n) = (term84 m n))) = (((term5 m n) = (term5 n m)) = ((term83 m n) = (term84 m n))).
Proof. exact (MK_COMB (@lem2405307 n m) (@lem2405308 m n)). Qed.
Lemma lem2405310 (m : nat) (n : nat) : ((term81 n m) = (term82 m n)) = (((term5 m n) = (term5 n m)) = ((term83 m n) = (term84 m n))).
Proof. exact (TRANS (@lem2405304 m n) (@lem2405309 m n)). Qed.
Lemma lem2405311 (n : nat) (m : nat) (h1 : (Peano.le n m) = True) : ((term5 m n) = (term5 n m)) = ((term83 m n) = (term84 m n)).
Proof. exact (EQ_MP (@lem2405310 m n) (@lem2405301 n m h1)). Qed.
Lemma lem2405312 (n : nat) (m : nat) (h1 : (Peano.le n m) = True) : ((term83 m n) = (term84 m n)) = ((term5 m n) = (term5 n m)).
Proof. exact (SYM (@lem2405311 n m h1)). Qed.
Lemma lem2405313 (m : nat) (n : nat) : (term80 m n) = (term80 m n).
Proof. exact (eq_refl (term80 m n)). Qed.
Lemma lem2405314 (n : nat) (m : nat) (h1 : (Peano.le n m) = False) : (term81 n m) = (term87 m n).
Proof. exact (MK_COMB (@lem2405313 m n) (@lem2405291 n m h1)). Qed.
Lemma lem2405315 (m : nat) (n : nat) : (term87 m n) = ((term88 m n) = (term89 m n)).
Proof. exact (eq_refl (term87 m n)). Qed.
Lemma lem2405316 (n : nat) (m : nat) : (term85 n m) = (term85 n m).
Proof. exact (eq_refl (term85 n m)). Qed.
Lemma lem2405317 (m : nat) (n : nat) : ((term81 n m) = (term87 m n)) = ((term81 n m) = ((term88 m n) = (term89 m n))).
Proof. exact (MK_COMB (@lem2405316 n m) (@lem2405315 m n)). Qed.
Lemma lem2405318 (n : nat) (m : nat) : (term81 n m) = ((term5 m n) = (term5 n m)).
Proof. exact (eq_refl (term81 n m)). Qed.
Lemma lem2405319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2405320 (n : nat) (m : nat) : (term85 n m) = (term86 n m).
Proof. exact (MK_COMB (@lem2405319) (@lem2405318 n m)). Qed.
Lemma lem2405321 (m : nat) (n : nat) : ((term88 m n) = (term89 m n)) = ((term88 m n) = (term89 m n)).
Proof. exact (eq_refl ((term88 m n) = (term89 m n))). Qed.
Lemma lem2405322 (m : nat) (n : nat) : ((term81 n m) = ((term88 m n) = (term89 m n))) = (((term5 m n) = (term5 n m)) = ((term88 m n) = (term89 m n))).
Proof. exact (MK_COMB (@lem2405320 n m) (@lem2405321 m n)). Qed.
Lemma lem2405323 (m : nat) (n : nat) : ((term81 n m) = (term87 m n)) = (((term5 m n) = (term5 n m)) = ((term88 m n) = (term89 m n))).
Proof. exact (TRANS (@lem2405317 m n) (@lem2405322 m n)). Qed.
Lemma lem2405324 (n : nat) (m : nat) (h1 : (Peano.le n m) = False) : ((term5 m n) = (term5 n m)) = ((term88 m n) = (term89 m n)).
Proof. exact (EQ_MP (@lem2405323 m n) (@lem2405314 n m h1)). Qed.
Lemma lem2405325 (n : nat) (m : nat) (h1 : (Peano.le n m) = False) : ((term88 m n) = (term89 m n)) = ((term5 m n) = (term5 n m)).
Proof. exact (SYM (@lem2405324 n m h1)). Qed.
Lemma lem2405329 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2405330 (m : nat) (n : nat) : (term83 m n) = (Peano.le m n).
Proof. exact (@lem2405329 (Peano.le m n)). Qed.
Lemma lem2405331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2405332 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem2405331) (@lem2405330 m n)). Qed.
Lemma lem2405334 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2405335 (m : nat) (n : nat) : (term84 m n) = (Peano.le m n).
Proof. exact (@lem2405334 (Peano.le m n)). Qed.
Lemma lem2405336 (m : nat) (n : nat) : ((term83 m n) = (term84 m n)) = ((Peano.le m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem2405332 m n) (@lem2405335 m n)). Qed.
Lemma lem2405338 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405339 (x : Prop) : (x = x) = True.
Proof. exact (@lem2405338 Prop x). Qed.
Lemma lem2405340 (m : nat) (n : nat) : ((Peano.le m n) = (Peano.le m n)) = True.
Proof. exact (@lem2405339 (Peano.le m n)). Qed.
Lemma lem2405341 (m : nat) (n : nat) : ((term83 m n) = (term84 m n)) = True.
Proof. exact (TRANS (@lem2405336 m n) (@lem2405340 m n)). Qed.
Lemma lem2405342 (m : nat) (n : nat) : True = ((term83 m n) = (term84 m n)).
Proof. exact (SYM (@lem2405341 m n)). Qed.
Lemma lem2405343 (m : nat) (n : nat) : (term83 m n) = (term84 m n).
Proof. exact (EQ_MP (@lem2405342 m n) (@lem0)). Qed.
Lemma lem2405347 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem2405348 (m : nat) (n : nat) : (term88 m n) = False.
Proof. exact (@lem2405347 (Peano.le m n)). Qed.
Lemma lem2405349 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2405350 (m : nat) (n : nat) : (term92 m n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem2405349) (@lem2405348 m n)). Qed.
Lemma lem2405352 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem2405353 (m : nat) (n : nat) : (term89 m n) = False.
Proof. exact (@lem2405352 (Peano.le m n)). Qed.
Lemma lem2405354 (m : nat) (n : nat) : ((term88 m n) = (term89 m n)) = (False = False).
Proof. exact (MK_COMB (@lem2405350 m n) (@lem2405353 m n)). Qed.
Lemma lem2405356 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem2405357 : (False = False) = (~ False).
Proof. exact (@lem2405356 False). Qed.
Lemma lem2405359 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2405360 : (False = False) = True.
Proof. exact (TRANS (@lem2405357) (@lem2405359)). Qed.
Lemma lem2405361 (m : nat) (n : nat) : ((term88 m n) = (term89 m n)) = True.
Proof. exact (TRANS (@lem2405354 m n) (@lem2405360)). Qed.
Lemma lem2405362 (m : nat) (n : nat) : True = ((term88 m n) = (term89 m n)).
Proof. exact (SYM (@lem2405361 m n)). Qed.
Lemma lem2405363 (m : nat) (n : nat) : (term88 m n) = (term89 m n).
Proof. exact (EQ_MP (@lem2405362 m n) (@lem0)). Qed.
Lemma lem2405364 (n : nat) (m : nat) (h1 : (Peano.le n m) = False) : (term5 m n) = (term5 n m).
Proof. exact (EQ_MP (@lem2405325 n m h1) (@lem2405363 m n)). Qed.
Lemma lem2405365 (n : nat) (m : nat) (h1 : (Peano.le n m) = True) : (term5 m n) = (term5 n m).
Proof. exact (EQ_MP (@lem2405312 n m h1) (@lem2405343 m n)). Qed.
Lemma lem2405368 (n : nat) (m : nat) : (term5 m n) = (term5 n m).
Proof. exact (or_elim (@lem2405289 n m) (fun h0 : (Peano.le n m) = True => @lem2405365 n m h0) (fun h0 : (Peano.le n m) = False => @lem2405364 n m h0)). Qed.
Lemma lem2405385 (n : nat) : term93 n.
Proof. exact (@lem9851 (n = (NUMERAL 0))). Qed.
Lemma lem2405386 (n : nat) : (term93 n) = (term94 n).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem2405387 (n : nat) : term94 n.
Proof. exact (EQ_MP (@lem2405386 n) (@lem2405385 n)). Qed.
Lemma lem2405388 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (n = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem2405389 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (n = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem2405406 (m : nat) : (term95 m) = (term95 m).
Proof. exact (eq_refl (term95 m)). Qed.
Lemma lem2405407 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term96 m n) = (term97 m).
Proof. exact (MK_COMB (@lem2405406 m) (@lem2405388 n h1)). Qed.
Lemma lem2405408 (m : nat) : (term97 m) = ((term98 m) = (term70 m)).
Proof. exact (eq_refl (term97 m)). Qed.
Lemma lem2405409 (m : nat) (n : nat) : (term99 m n) = (term99 m n).
Proof. exact (eq_refl (term99 m n)). Qed.
Lemma lem2405410 (n : nat) (m : nat) : ((term96 m n) = (term97 m)) = ((term96 m n) = ((term98 m) = (term70 m))).
Proof. exact (MK_COMB (@lem2405409 m n) (@lem2405408 m)). Qed.
Lemma lem2405411 (m : nat) (n : nat) : (term96 m n) = ((term44 n m) = (term44 m n)).
Proof. exact (eq_refl (term96 m n)). Qed.
Lemma lem2405412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2405413 (m : nat) (n : nat) : (term99 m n) = (term100 m n).
Proof. exact (MK_COMB (@lem2405412) (@lem2405411 m n)). Qed.
Lemma lem2405414 (m : nat) : ((term98 m) = (term70 m)) = ((term98 m) = (term70 m)).
Proof. exact (eq_refl ((term98 m) = (term70 m))). Qed.
Lemma lem2405415 (n : nat) (m : nat) : ((term96 m n) = ((term98 m) = (term70 m))) = (((term44 n m) = (term44 m n)) = ((term98 m) = (term70 m))).
Proof. exact (MK_COMB (@lem2405413 m n) (@lem2405414 m)). Qed.
Lemma lem2405416 (n : nat) (m : nat) : ((term96 m n) = (term97 m)) = (((term44 n m) = (term44 m n)) = ((term98 m) = (term70 m))).
Proof. exact (TRANS (@lem2405410 n m) (@lem2405415 n m)). Qed.
Lemma lem2405417 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term44 n m) = (term44 m n)) = ((term98 m) = (term70 m)).
Proof. exact (EQ_MP (@lem2405416 n m) (@lem2405407 m n h1)). Qed.
Lemma lem2405418 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term98 m) = (term70 m)) = ((term44 n m) = (term44 m n)).
Proof. exact (SYM (@lem2405417 m n h1)). Qed.
Lemma lem2405419 (m : nat) : (term95 m) = (term95 m).
Proof. exact (eq_refl (term95 m)). Qed.
Lemma lem2405420 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term96 m n) = (term101 m).
Proof. exact (MK_COMB (@lem2405419 m) (@lem2405389 n h1)). Qed.
Lemma lem2405421 (m : nat) : (term101 m) = ((term102 m) = (term103 m)).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem2405422 (m : nat) (n : nat) : (term99 m n) = (term99 m n).
Proof. exact (eq_refl (term99 m n)). Qed.
Lemma lem2405423 (n : nat) (m : nat) : ((term96 m n) = (term101 m)) = ((term96 m n) = ((term102 m) = (term103 m))).
Proof. exact (MK_COMB (@lem2405422 m n) (@lem2405421 m)). Qed.
Lemma lem2405424 (m : nat) (n : nat) : (term96 m n) = ((term44 n m) = (term44 m n)).
Proof. exact (eq_refl (term96 m n)). Qed.
Lemma lem2405425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2405426 (m : nat) (n : nat) : (term99 m n) = (term100 m n).
Proof. exact (MK_COMB (@lem2405425) (@lem2405424 m n)). Qed.
Lemma lem2405427 (m : nat) : ((term102 m) = (term103 m)) = ((term102 m) = (term103 m)).
Proof. exact (eq_refl ((term102 m) = (term103 m))). Qed.
Lemma lem2405428 (n : nat) (m : nat) : ((term96 m n) = ((term102 m) = (term103 m))) = (((term44 n m) = (term44 m n)) = ((term102 m) = (term103 m))).
Proof. exact (MK_COMB (@lem2405426 m n) (@lem2405427 m)). Qed.
Lemma lem2405429 (n : nat) (m : nat) : ((term96 m n) = (term101 m)) = (((term44 n m) = (term44 m n)) = ((term102 m) = (term103 m))).
Proof. exact (TRANS (@lem2405423 n m) (@lem2405428 n m)). Qed.
Lemma lem2405430 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term44 n m) = (term44 m n)) = ((term102 m) = (term103 m)).
Proof. exact (EQ_MP (@lem2405429 n m) (@lem2405420 m n h1)). Qed.
Lemma lem2405431 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term102 m) = (term103 m)) = ((term44 n m) = (term44 m n)).
Proof. exact (SYM (@lem2405430 m n h1)). Qed.
Lemma lem2405435 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2405436 (m : nat) : (term98 m) = (m = (NUMERAL 0)).
Proof. exact (@lem2405435 (m = (NUMERAL 0))). Qed.
Lemma lem2405439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2405440 (m : nat) : (term104 m) = (term105 m).
Proof. exact (MK_COMB (@lem2405439) (@lem2405436 m)). Qed.
Lemma lem2405442 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2405443 (m : nat) : (term70 m) = (m = (NUMERAL 0)).
Proof. exact (@lem2405442 (m = (NUMERAL 0))). Qed.
Lemma lem2405446 (m : nat) : ((term98 m) = (term70 m)) = ((m = (NUMERAL 0)) = (m = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem2405440 m) (@lem2405443 m)). Qed.
Lemma lem2405448 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405449 (x : Prop) : (x = x) = True.
Proof. exact (@lem2405448 Prop x). Qed.
Lemma lem2405450 (m : nat) : ((m = (NUMERAL 0)) = (m = (NUMERAL 0))) = True.
Proof. exact (@lem2405449 (m = (NUMERAL 0))). Qed.
Lemma lem2405451 (m : nat) : ((term98 m) = (term70 m)) = True.
Proof. exact (TRANS (@lem2405446 m) (@lem2405450 m)). Qed.
Lemma lem2405452 (m : nat) : True = ((term98 m) = (term70 m)).
Proof. exact (SYM (@lem2405451 m)). Qed.
Lemma lem2405453 (m : nat) : (term98 m) = (term70 m).
Proof. exact (EQ_MP (@lem2405452 m) (@lem0)). Qed.
Lemma lem2405457 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem2405458 (m : nat) : (term102 m) = False.
Proof. exact (@lem2405457 (m = (NUMERAL 0))). Qed.
Lemma lem2405459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2405460 (m : nat) : (term106 m) = (@eq Prop False).
Proof. exact (MK_COMB (@lem2405459) (@lem2405458 m)). Qed.
Lemma lem2405462 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem2405463 (m : nat) : (term103 m) = False.
Proof. exact (@lem2405462 (m = (NUMERAL 0))). Qed.
Lemma lem2405464 (m : nat) : ((term102 m) = (term103 m)) = (False = False).
Proof. exact (MK_COMB (@lem2405460 m) (@lem2405463 m)). Qed.
Lemma lem2405466 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem2405467 : (False = False) = (~ False).
Proof. exact (@lem2405466 False). Qed.
Lemma lem2405469 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2405470 : (False = False) = True.
Proof. exact (TRANS (@lem2405467) (@lem2405469)). Qed.
Lemma lem2405471 (m : nat) : ((term102 m) = (term103 m)) = True.
Proof. exact (TRANS (@lem2405464 m) (@lem2405470)). Qed.
Lemma lem2405472 (m : nat) : True = ((term102 m) = (term103 m)).
Proof. exact (SYM (@lem2405471 m)). Qed.
Lemma lem2405473 (m : nat) : (term102 m) = (term103 m).
Proof. exact (EQ_MP (@lem2405472 m) (@lem0)). Qed.
Lemma lem2405474 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term44 n m) = (term44 m n).
Proof. exact (EQ_MP (@lem2405431 m n h1) (@lem2405473 m)). Qed.
Lemma lem2405475 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term44 n m) = (term44 m n).
Proof. exact (EQ_MP (@lem2405418 m n h1) (@lem2405453 m)). Qed.
Lemma lem2405478 (m : nat) (n : nat) : (term44 n m) = (term44 m n).
Proof. exact (or_elim (@lem2405387 n) (fun h0 : (n = (NUMERAL 0)) = True => @lem2405475 m n h0) (fun h0 : (n = (NUMERAL 0)) = False => @lem2405474 m n h0)). Qed.
Lemma lem2405479 (m : nat) (n : nat) : term76 m n.
Proof. exact (conj (@lem2405368 n m) (@lem2405478 m n)). Qed.
Lemma lem2405480 (m : nat) (n : nat) : term56 m n.
Proof. exact (EQ_MP (@lem2405278 m n) (@lem2405479 m n)). Qed.
Lemma lem2405481 (m : nat) (n : nat) : term55 m n.
Proof. exact (EQ_MP (@lem2405014 m n) (@lem2405480 m n)). Qed.
