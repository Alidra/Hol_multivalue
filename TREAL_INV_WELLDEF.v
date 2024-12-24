Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_INV_WELLDEF_term_abbrevs.
Require Import EQ_SYM_EQ_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import HREAL_ADD_RID_spec.
Require Import HREAL_EQ_ADD_LCANCEL_spec.
Require Import HREAL_EQ_ADD_RCANCEL_spec.
Require Import HREAL_LE_ADD_LCANCEL_spec.
Require Import NADD_INV_0_spec.
Require Import SELECT_UNIQUE_spec.
Require Import TREAL_EQ_REFL_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1319042_spec.
Require Import thm1319377_spec.
Require Import thm1319496_spec.
Require Import thm1319607_spec.
Require Import thm1319802_spec.
Require Import thm1320004_spec.
Require Import thm1320203_spec.
Require Import thm1320277_spec.
Require Import thm1321215_spec.
Require Import thm13473_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm9396_spec.
Require Import treal_eq_spec.
Require Import treal_inv_spec.
Lemma lem1334748 (m : hreal) : term0 m.
Proof. exact (@lem1321346 m). Qed.
Lemma lem1334749 (m : hreal) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1334750 (m : hreal) : term1 m.
Proof. exact (EQ_MP (@lem1334749 m) (@lem1334748 m)). Qed.
Lemma lem1334751 (m : hreal) (n : hreal) : term2 m n.
Proof. exact (@lem1334750 m n). Qed.
Lemma lem1334752 (m : hreal) (n : hreal) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1334753 (m : hreal) (n : hreal) : term3 m n.
Proof. exact (EQ_MP (@lem1334752 m n) (@lem1334751 m n)). Qed.
Lemma lem1334754 (m : hreal) (n : hreal) (p : hreal) : term4 m n p.
Proof. exact (@lem1334753 m n p). Qed.
Lemma lem1334755 (m : hreal) (n : hreal) (p : hreal) : (term4 m n p) = (((hreal_add m n) = (hreal_add m p)) = (n = p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1334758 (n : hreal) (h1 : (term5 n) = n) : (term5 n) = n.
Proof. exact (h1). Qed.
Lemma lem1334759 (n : hreal) (h1 : (term5 n) = n) : n = (term5 n).
Proof. exact (SYM (@lem1334758 n h1)). Qed.
Lemma lem1334760 (n : hreal) (h1 : n = (term5 n)) : n = (term5 n).
Proof. exact (h1). Qed.
Lemma lem1334761 (n : hreal) (h1 : n = (term5 n)) : (term5 n) = n.
Proof. exact (SYM (@lem1334760 n h1)). Qed.
Lemma lem1334762 (n : hreal) : ((term5 n) = n) = (n = (term5 n)).
Proof. exact (prop_ext (fun h1 : (term5 n) = n => @lem1334759 n h1) (fun h1 : n = (term5 n) => @lem1334761 n h1)). Qed.
Lemma lem1334763 : term6 = term7.
Proof. exact (fun_ext (fun n : hreal => @lem1334762 n)). Qed.
Lemma lem1334764 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334765 : term8 = term9.
Proof. exact (MK_COMB (@lem1334764) (@lem1334763)). Qed.
Lemma lem1334766 : term9.
Proof. exact (EQ_MP (@lem1334765) (@lem1321694)). Qed.
Lemma lem1334767 (n : hreal) : term10 n.
Proof. exact (@lem1334766 n). Qed.
Lemma lem1334768 (n : hreal) : (term10 n) = (n = (term5 n)).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem1334770 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem1334771 {A : Type'} (P : A -> Prop) (h1 : term11 A) : term12 A P.
Proof. exact (@lem1334770 A h1 P). Qed.
Lemma lem1334772 {A : Type'} (P : A -> Prop) : (term12 A P) = (term13 A P).
Proof. exact (eq_refl (term12 A P)). Qed.
Lemma lem1334773 {A : Type'} (P : A -> Prop) (h1 : term11 A) : term13 A P.
Proof. exact (EQ_MP (@lem1334772 A P) (@lem1334771 A P h1)). Qed.
Lemma lem1334774 {A : Type'} (P : A -> Prop) (x : A) (h1 : term11 A) : term14 A P x.
Proof. exact (@lem1334773 A P h1 x). Qed.
Lemma lem1334775 {A : Type'} (P : A -> Prop) (x : A) : (term14 A P x) = (term15 A P x).
Proof. exact (eq_refl (term14 A P x)). Qed.
Lemma lem1334776 {A : Type'} (P : A -> Prop) (x : A) (h1 : term11 A) : term15 A P x.
Proof. exact (EQ_MP (@lem1334775 A P x) (@lem1334774 A P x h1)). Qed.
Lemma lem1334777 {A : Type'} (P : A -> Prop) (x : A) (h1 : term16 A P x) : term16 A P x.
Proof. exact (h1). Qed.
Lemma lem1334778 {A : Type'} (P : A -> Prop) (x : A) (h1 : term16 A P x) (h2 : term11 A) : (@ε A P) = x.
Proof. exact (@lem1334776 A P x h2 (@lem1334777 A P x h1)). Qed.
Lemma lem1334779 {A : Type'} (P : A -> Prop) (x : A) (h1 : term16 A P x) : term17 A P x.
Proof. exact (fun h0 : term11 A => @lem1334778 A P x h1 h0). Qed.
Lemma lem1334780 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem1334781 {A : Type'} (P : A -> Prop) (x : A) (h1 : term16 A P x) (h2 : term11 A) : (@ε A P) = x.
Proof. exact (@lem1334779 A P x h1 (@lem1334780 A h2)). Qed.
Lemma lem1334782 {A : Type'} (P : A -> Prop) (x : A) (h1 : term11 A) : term15 A P x.
Proof. exact (fun h0 : term16 A P x => @lem1334781 A P x h0 h1). Qed.
Lemma lem1334783 {A : Type'} (P : A -> Prop) (h1 : term11 A) : term13 A P.
Proof. exact (fun x : A => @lem1334782 A P x h1). Qed.
Lemma lem1334784 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (fun P : A -> Prop => @lem1334783 A P h1). Qed.
Lemma lem1334785 {A : Type'} : term18 A.
Proof. exact (fun h0 : term11 A => @lem1334784 A h0). Qed.
Lemma lem1334786 {A : Type'} : term11 A.
Proof. exact (@lem1334785 A (@lem9522 A)). Qed.
Lemma lem1334787 {A : Type'} (P : A -> Prop) : term12 A P.
Proof. exact (@lem1334786 A P). Qed.
Lemma lem1334788 {A : Type'} (P : A -> Prop) : (term12 A P) = (term13 A P).
Proof. exact (eq_refl (term12 A P)). Qed.
Lemma lem1334789 {A : Type'} (P : A -> Prop) : term13 A P.
Proof. exact (EQ_MP (@lem1334788 A P) (@lem1334787 A P)). Qed.
Lemma lem1334790 {A : Type'} (P : A -> Prop) (x : A) : term14 A P x.
Proof. exact (@lem1334789 A P x). Qed.
Lemma lem1334791 {A : Type'} (P : A -> Prop) (x : A) : (term14 A P x) = (term15 A P x).
Proof. exact (eq_refl (term14 A P x)). Qed.
Lemma lem1334794 {A : Type'} (P : A -> Prop) (x : A) : term15 A P x.
Proof. exact (EQ_MP (@lem1334791 A P x) (@lem1334790 A P x)). Qed.
Lemma lem1334795 (P : hreal -> Prop) (x : hreal) : term19 P x.
Proof. exact (@lem1334794 hreal P x). Qed.
Lemma lem1334796 (x : hreal) : term20 x.
Proof. exact (@lem1334795 (term21 x) term22). Qed.
Lemma lem1334797 (x : hreal) (y : hreal) : (term23 x y) = (x = (hreal_add x y)).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1334798 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1334799 (x : hreal) (y : hreal) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1334798) (@lem1334797 x y)). Qed.
Lemma lem1334800 (y : hreal) : (y = term22) = (y = term22).
Proof. exact (eq_refl (y = term22)). Qed.
Lemma lem1334801 (x : hreal) (y : hreal) : ((term23 x y) = (y = term22)) = ((x = (hreal_add x y)) = (y = term22)).
Proof. exact (MK_COMB (@lem1334799 x y) (@lem1334800 y)). Qed.
Lemma lem1334802 (x : hreal) : (term26 x) = (term27 x).
Proof. exact (fun_ext (fun y : hreal => @lem1334801 x y)). Qed.
Lemma lem1334803 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334804 (x : hreal) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem1334803) (@lem1334802 x)). Qed.
Lemma lem1334805 (x : hreal) : (term29 x) = (term28 x).
Proof. exact (SYM (@lem1334804 x)). Qed.
Lemma lem1334807 (n : hreal) : n = (term5 n).
Proof. exact (EQ_MP (@lem1334768 n) (@lem1334767 n)). Qed.
Lemma lem1334808 (x : hreal) : x = (term5 x).
Proof. exact (@lem1334807 x). Qed.
Lemma lem1334809 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1334810 (x : hreal) : (@eq hreal x) = (term30 x).
Proof. exact (MK_COMB (@lem1334809) (@lem1334808 x)). Qed.
Lemma lem1334811 (x : hreal) (y : hreal) : (hreal_add x y) = (hreal_add x y).
Proof. exact (eq_refl (hreal_add x y)). Qed.
Lemma lem1334812 (x : hreal) (y : hreal) : (x = (hreal_add x y)) = ((term5 x) = (hreal_add x y)).
Proof. exact (MK_COMB (@lem1334810 x) (@lem1334811 x y)). Qed.
Lemma lem1334813 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1334814 (x : hreal) (y : hreal) : (term25 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1334813) (@lem1334812 x y)). Qed.
Lemma lem1334815 (y : hreal) : (y = term22) = (y = term22).
Proof. exact (eq_refl (y = term22)). Qed.
Lemma lem1334816 (x : hreal) (y : hreal) : ((x = (hreal_add x y)) = (y = term22)) = (((term5 x) = (hreal_add x y)) = (y = term22)).
Proof. exact (MK_COMB (@lem1334814 x y) (@lem1334815 y)). Qed.
Lemma lem1334817 (x : hreal) (y : hreal) : (((term5 x) = (hreal_add x y)) = (y = term22)) = ((x = (hreal_add x y)) = (y = term22)).
Proof. exact (SYM (@lem1334816 x y)). Qed.
Lemma lem1334821 (m : hreal) (n : hreal) (p : hreal) : ((hreal_add m n) = (hreal_add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1334755 m n p) (@lem1334754 m n p)). Qed.
Lemma lem1334822 (x : hreal) (y : hreal) : ((term5 x) = (hreal_add x y)) = (term22 = y).
Proof. exact (@lem1334821 x term22 y). Qed.
Lemma lem1334825 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1334826 (x : hreal) (y : hreal) : (term31 x y) = (term32 y).
Proof. exact (MK_COMB (@lem1334825) (@lem1334822 x y)). Qed.
Lemma lem1334829 (y : hreal) : (y = term22) = (y = term22).
Proof. exact (eq_refl (y = term22)). Qed.
Lemma lem1334830 (x : hreal) (y : hreal) : (((term5 x) = (hreal_add x y)) = (y = term22)) = ((term22 = y) = (y = term22)).
Proof. exact (MK_COMB (@lem1334826 x y) (@lem1334829 y)). Qed.
Lemma lem1334833 (x : hreal) (y : hreal) : ((term22 = y) = (y = term22)) = (((term5 x) = (hreal_add x y)) = (y = term22)).
Proof. exact (SYM (@lem1334830 x y)). Qed.
Lemma lem1334834 {A : Type'} (x : A) : term33 A x.
Proof. exact (@lem362 A x). Qed.
Lemma lem1334835 {A : Type'} (x : A) : (term33 A x) = (term34 A x).
Proof. exact (eq_refl (term33 A x)). Qed.
Lemma lem1334836 {A : Type'} (x : A) : term34 A x.
Proof. exact (EQ_MP (@lem1334835 A x) (@lem1334834 A x)). Qed.
Lemma lem1334837 {A : Type'} (x : A) (y : A) : term35 A x y.
Proof. exact (@lem1334836 A x y). Qed.
Lemma lem1334838 {A : Type'} (y : A) (x : A) : (term35 A x y) = ((x = y) = (y = x)).
Proof. exact (eq_refl (term35 A x y)). Qed.
Lemma lem1334841 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem1334838 A y x) (@lem1334837 A x y)). Qed.
Lemma lem1334842 (y : hreal) (x : hreal) : (x = y) = (y = x).
Proof. exact (@lem1334841 hreal y x). Qed.
Lemma lem1334843 (y : hreal) : (term22 = y) = (y = term22).
Proof. exact (@lem1334842 y term22). Qed.
Lemma lem1334844 (x : hreal) (y : hreal) : ((term5 x) = (hreal_add x y)) = (y = term22).
Proof. exact (EQ_MP (@lem1334833 x y) (@lem1334843 y)). Qed.
Lemma lem1334845 (x : hreal) (y : hreal) : (x = (hreal_add x y)) = (y = term22).
Proof. exact (EQ_MP (@lem1334817 x y) (@lem1334844 x y)). Qed.
Lemma lem1334850 (x : hreal) : term29 x.
Proof. exact (fun y : hreal => @lem1334845 x y). Qed.
Lemma lem1334851 (x : hreal) : term28 x.
Proof. exact (EQ_MP (@lem1334805 x) (@lem1334850 x)). Qed.
Lemma lem1334853 (x : prod hreal hreal) : term36 x.
Proof. exact (@lem1326193 x). Qed.
Lemma lem1334854 (x : prod hreal hreal) : (term36 x) = (treal_eq x x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1334855 (x : prod hreal hreal) : treal_eq x x.
Proof. exact (EQ_MP (@lem1334854 x) (@lem1334853 x)). Qed.
Lemma lem1334856 (x : prod hreal hreal) : (treal_eq x x) = ((treal_eq x x) = True).
Proof. exact (@lem7 (treal_eq x x)). Qed.
Lemma lem1334858 (m : hreal) : term0 m.
Proof. exact (@lem1321346 m). Qed.
Lemma lem1334859 (m : hreal) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1334860 (m : hreal) : term1 m.
Proof. exact (EQ_MP (@lem1334859 m) (@lem1334858 m)). Qed.
Lemma lem1334861 (m : hreal) (n : hreal) : term2 m n.
Proof. exact (@lem1334860 m n). Qed.
Lemma lem1334862 (m : hreal) (n : hreal) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1334863 (m : hreal) (n : hreal) : term3 m n.
Proof. exact (EQ_MP (@lem1334862 m n) (@lem1334861 m n)). Qed.
Lemma lem1334864 (m : hreal) (n : hreal) (p : hreal) : term4 m n p.
Proof. exact (@lem1334863 m n p). Qed.
Lemma lem1334865 (m : hreal) (n : hreal) (p : hreal) : (term4 m n p) = (((hreal_add m n) = (hreal_add m p)) = (n = p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1334867 (x : hreal) : term37 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1334868 (x : hreal) : (term37 x) = (term38 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1334869 (x : hreal) : term38 x.
Proof. exact (EQ_MP (@lem1334868 x) (@lem1334867 x)). Qed.
Lemma lem1334870 (x : hreal) (y : hreal) : term39 x y.
Proof. exact (@lem1334869 x y). Qed.
Lemma lem1334871 (y : hreal) (x : hreal) : (term39 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term39 x y)). Qed.
Lemma lem1334873 (x : hreal) : term40 x.
Proof. exact (@lem1319607 x). Qed.
Lemma lem1334874 (x : hreal) : (term40 x) = (term41 x).
Proof. exact (eq_refl (term40 x)). Qed.
Lemma lem1334875 (x : hreal) : term41 x.
Proof. exact (EQ_MP (@lem1334874 x) (@lem1334873 x)). Qed.
Lemma lem1334876 (x : hreal) (y : hreal) : term42 x y.
Proof. exact (@lem1334875 x y). Qed.
Lemma lem1334877 (x : hreal) (y : hreal) : (term42 x y) = (term43 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1334878 (x : hreal) (y : hreal) : term43 x y.
Proof. exact (EQ_MP (@lem1334877 x y) (@lem1334876 x y)). Qed.
Lemma lem1334879 (x : hreal) (y : hreal) : (term43 x y) = ((term43 x y) = True).
Proof. exact (@lem7 (term43 x y)). Qed.
Lemma lem1334882 (x : hreal) (h1 : (term44 x) = x) : (term44 x) = x.
Proof. exact (h1). Qed.
Lemma lem1334883 (x : hreal) (h1 : (term44 x) = x) : x = (term44 x).
Proof. exact (SYM (@lem1334882 x h1)). Qed.
Lemma lem1334884 (x : hreal) (h1 : x = (term44 x)) : x = (term44 x).
Proof. exact (h1). Qed.
Lemma lem1334885 (x : hreal) (h1 : x = (term44 x)) : (term44 x) = x.
Proof. exact (SYM (@lem1334884 x h1)). Qed.
Lemma lem1334886 (x : hreal) : ((term44 x) = x) = (x = (term44 x)).
Proof. exact (prop_ext (fun h1 : (term44 x) = x => @lem1334883 x h1) (fun h1 : x = (term44 x) => @lem1334885 x h1)). Qed.
Lemma lem1334887 : term45 = term46.
Proof. exact (fun_ext (fun x : hreal => @lem1334886 x)). Qed.
Lemma lem1334888 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334889 : term47 = term48.
Proof. exact (MK_COMB (@lem1334888) (@lem1334887)). Qed.
Lemma lem1334890 : term48.
Proof. exact (EQ_MP (@lem1334889) (@lem1320277)). Qed.
Lemma lem1334891 (x : hreal) : term49 x.
Proof. exact (@lem1334890 x). Qed.
Lemma lem1334892 (x : hreal) : (term49 x) = (x = (term44 x)).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1334896 (x : hreal) (y : hreal) (h1 : (term50 y x) = (x = y)) : (term50 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1334897 (x : hreal) (y : hreal) (h1 : (term50 y x) = (x = y)) : (x = y) = (term50 y x).
Proof. exact (SYM (@lem1334896 x y h1)). Qed.
Lemma lem1334898 (y : hreal) (x : hreal) (h1 : (x = y) = (term50 y x)) : (x = y) = (term50 y x).
Proof. exact (h1). Qed.
Lemma lem1334899 (y : hreal) (x : hreal) (h1 : (x = y) = (term50 y x)) : (term50 y x) = (x = y).
Proof. exact (SYM (@lem1334898 y x h1)). Qed.
Lemma lem1334900 (y : hreal) (x : hreal) : ((term50 y x) = (x = y)) = ((x = y) = (term50 y x)).
Proof. exact (prop_ext (fun h1 : (term50 y x) = (x = y) => @lem1334897 x y h1) (fun h1 : (x = y) = (term50 y x) => @lem1334899 y x h1)). Qed.
Lemma lem1334901 (x : hreal) : (term51 x) = (term52 x).
Proof. exact (fun_ext (fun y : hreal => @lem1334900 y x)). Qed.
Lemma lem1334902 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334903 (x : hreal) : (term53 x) = (term54 x).
Proof. exact (MK_COMB (@lem1334902) (@lem1334901 x)). Qed.
Lemma lem1334904 : term55 = term56.
Proof. exact (fun_ext (fun x : hreal => @lem1334903 x)). Qed.
Lemma lem1334905 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334906 : term57 = term58.
Proof. exact (MK_COMB (@lem1334905) (@lem1334904)). Qed.
Lemma lem1334907 : term58.
Proof. exact (EQ_MP (@lem1334906) (@lem1319377)). Qed.
Lemma lem1334908 (x : hreal) : term37 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1334909 (x : hreal) : (term37 x) = (term38 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1334910 (x : hreal) : term38 x.
Proof. exact (EQ_MP (@lem1334909 x) (@lem1334908 x)). Qed.
Lemma lem1334911 (x : hreal) (y : hreal) : term39 x y.
Proof. exact (@lem1334910 x y). Qed.
Lemma lem1334912 (y : hreal) (x : hreal) : (term39 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term39 x y)). Qed.
Lemma lem1334929 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1334912 y x) (@lem1334911 x y)). Qed.
Lemma lem1334930 (n : hreal) (m : hreal) : (hreal_add m n) = (hreal_add n m).
Proof. exact (@lem1334929 n m). Qed.
Lemma lem1334931 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1334932 (n : hreal) (m : hreal) : (term59 m n) = (term59 n m).
Proof. exact (MK_COMB (@lem1334931) (@lem1334930 n m)). Qed.
Lemma lem1334934 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1334912 y x) (@lem1334911 x y)). Qed.
Lemma lem1334935 (p : hreal) (m : hreal) : (hreal_add m p) = (hreal_add p m).
Proof. exact (@lem1334934 p m). Qed.
Lemma lem1334936 (n : hreal) (p : hreal) (m : hreal) : (term60 n m p) = (term61 n p m).
Proof. exact (MK_COMB (@lem1334932 n m) (@lem1334935 p m)). Qed.
Lemma lem1334937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1334938 (n : hreal) (p : hreal) (m : hreal) : (term62 n m p) = (term63 n p m).
Proof. exact (MK_COMB (@lem1334937) (@lem1334936 n p m)). Qed.
Lemma lem1334939 (n : hreal) (p : hreal) : (hreal_le n p) = (hreal_le n p).
Proof. exact (eq_refl (hreal_le n p)). Qed.
Lemma lem1334940 (m : hreal) (n : hreal) (p : hreal) : ((term60 n m p) = (hreal_le n p)) = ((term61 n p m) = (hreal_le n p)).
Proof. exact (MK_COMB (@lem1334938 n p m) (@lem1334939 n p)). Qed.
Lemma lem1334941 (m : hreal) (n : hreal) : (term64 m n) = (term65 m n).
Proof. exact (fun_ext (fun p : hreal => @lem1334940 m n p)). Qed.
Lemma lem1334942 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334943 (m : hreal) (n : hreal) : (term66 m n) = (term67 m n).
Proof. exact (MK_COMB (@lem1334942) (@lem1334941 m n)). Qed.
Lemma lem1334944 (m : hreal) : (term68 m) = (term69 m).
Proof. exact (fun_ext (fun n : hreal => @lem1334943 m n)). Qed.
Lemma lem1334945 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334946 (m : hreal) : (term70 m) = (term71 m).
Proof. exact (MK_COMB (@lem1334945) (@lem1334944 m)). Qed.
Lemma lem1334947 : term72 = term73.
Proof. exact (fun_ext (fun m : hreal => @lem1334946 m)). Qed.
Lemma lem1334948 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334949 : term74 = term75.
Proof. exact (MK_COMB (@lem1334948) (@lem1334947)). Qed.
Lemma lem1334950 : term75.
Proof. exact (EQ_MP (@lem1334949) (@lem1321588)). Qed.
Lemma lem1334951 (m : hreal) : term76 m.
Proof. exact (@lem1334950 m). Qed.
Lemma lem1334952 (m : hreal) : (term76 m) = (term71 m).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem1334953 (m : hreal) : term71 m.
Proof. exact (EQ_MP (@lem1334952 m) (@lem1334951 m)). Qed.
Lemma lem1334954 (m : hreal) (n : hreal) : term77 m n.
Proof. exact (@lem1334953 m n). Qed.
Lemma lem1334955 (m : hreal) (n : hreal) : (term77 m n) = (term67 m n).
Proof. exact (eq_refl (term77 m n)). Qed.
Lemma lem1334956 (m : hreal) (n : hreal) : term67 m n.
Proof. exact (EQ_MP (@lem1334955 m n) (@lem1334954 m n)). Qed.
Lemma lem1334957 (m : hreal) (n : hreal) (p : hreal) : term78 m n p.
Proof. exact (@lem1334956 m n p). Qed.
Lemma lem1334958 (m : hreal) (n : hreal) (p : hreal) : (term78 m n p) = ((term61 n p m) = (hreal_le n p)).
Proof. exact (eq_refl (term78 m n p)). Qed.
Lemma lem1334961 (x : hreal) (h1 : (term44 x) = x) : (term44 x) = x.
Proof. exact (h1). Qed.
Lemma lem1334962 (x : hreal) (h1 : (term44 x) = x) : x = (term44 x).
Proof. exact (SYM (@lem1334961 x h1)). Qed.
Lemma lem1334963 (x : hreal) (h1 : x = (term44 x)) : x = (term44 x).
Proof. exact (h1). Qed.
Lemma lem1334964 (x : hreal) (h1 : x = (term44 x)) : (term44 x) = x.
Proof. exact (SYM (@lem1334963 x h1)). Qed.
Lemma lem1334965 (x : hreal) : ((term44 x) = x) = (x = (term44 x)).
Proof. exact (prop_ext (fun h1 : (term44 x) = x => @lem1334962 x h1) (fun h1 : x = (term44 x) => @lem1334964 x h1)). Qed.
Lemma lem1334966 : term45 = term46.
Proof. exact (fun_ext (fun x : hreal => @lem1334965 x)). Qed.
Lemma lem1334967 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334968 : term47 = term48.
Proof. exact (MK_COMB (@lem1334967) (@lem1334966)). Qed.
Lemma lem1334969 : term48.
Proof. exact (EQ_MP (@lem1334968) (@lem1320277)). Qed.
Lemma lem1334970 (x : hreal) : term49 x.
Proof. exact (@lem1334969 x). Qed.
Lemma lem1334971 (x : hreal) : (term49 x) = (x = (term44 x)).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1335009 (x : hreal) (y : hreal) (z : hreal) (h1 : (term79 x y z) = (term80 x y z)) : (term79 x y z) = (term80 x y z).
Proof. exact (h1). Qed.
Lemma lem1335010 (x : hreal) (y : hreal) (z : hreal) (h1 : (term79 x y z) = (term80 x y z)) : (term80 x y z) = (term79 x y z).
Proof. exact (SYM (@lem1335009 x y z h1)). Qed.
Lemma lem1335011 (x : hreal) (y : hreal) (z : hreal) (h1 : (term80 x y z) = (term79 x y z)) : (term80 x y z) = (term79 x y z).
Proof. exact (h1). Qed.
Lemma lem1335012 (x : hreal) (y : hreal) (z : hreal) (h1 : (term80 x y z) = (term79 x y z)) : (term79 x y z) = (term80 x y z).
Proof. exact (SYM (@lem1335011 x y z h1)). Qed.
Lemma lem1335013 (x : hreal) (y : hreal) (z : hreal) : ((term79 x y z) = (term80 x y z)) = ((term80 x y z) = (term79 x y z)).
Proof. exact (prop_ext (fun h1 : (term79 x y z) = (term80 x y z) => @lem1335010 x y z h1) (fun h1 : (term80 x y z) = (term79 x y z) => @lem1335012 x y z h1)). Qed.
Lemma lem1335014 (x : hreal) (y : hreal) : (term81 x y) = (term82 x y).
Proof. exact (fun_ext (fun z : hreal => @lem1335013 x y z)). Qed.
Lemma lem1335015 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1335016 (x : hreal) (y : hreal) : (term83 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1335015) (@lem1335014 x y)). Qed.
Lemma lem1335017 (x : hreal) : (term85 x) = (term86 x).
Proof. exact (fun_ext (fun y : hreal => @lem1335016 x y)). Qed.
Lemma lem1335018 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1335019 (x : hreal) : (term87 x) = (term88 x).
Proof. exact (MK_COMB (@lem1335018) (@lem1335017 x)). Qed.
Lemma lem1335020 : term89 = term90.
Proof. exact (fun_ext (fun x : hreal => @lem1335019 x)). Qed.
Lemma lem1335021 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1335022 : term91 = term92.
Proof. exact (MK_COMB (@lem1335021) (@lem1335020)). Qed.
Lemma lem1335023 : term92.
Proof. exact (EQ_MP (@lem1335022) (@lem1320203)). Qed.
Lemma lem1335024 (x : hreal) : term93 x.
Proof. exact (@lem1335023 x). Qed.
Lemma lem1335025 (x : hreal) : (term93 x) = (term88 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem1335026 (x : hreal) : term88 x.
Proof. exact (EQ_MP (@lem1335025 x) (@lem1335024 x)). Qed.
Lemma lem1335027 (x : hreal) (y : hreal) : term94 x y.
Proof. exact (@lem1335026 x y). Qed.
Lemma lem1335028 (x : hreal) (y : hreal) : (term94 x y) = (term84 x y).
Proof. exact (eq_refl (term94 x y)). Qed.
Lemma lem1335029 (x : hreal) (y : hreal) : term84 x y.
Proof. exact (EQ_MP (@lem1335028 x y) (@lem1335027 x y)). Qed.
Lemma lem1335030 (x : hreal) (y : hreal) (z : hreal) : term95 x y z.
Proof. exact (@lem1335029 x y z). Qed.
Lemma lem1335031 (x : hreal) (y : hreal) (z : hreal) : (term95 x y z) = ((term80 x y z) = (term79 x y z)).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1335033 (m : hreal) : term0 m.
Proof. exact (@lem1321346 m). Qed.
Lemma lem1335034 (m : hreal) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1335035 (m : hreal) : term1 m.
Proof. exact (EQ_MP (@lem1335034 m) (@lem1335033 m)). Qed.
Lemma lem1335036 (m : hreal) (n : hreal) : term2 m n.
Proof. exact (@lem1335035 m n). Qed.
Lemma lem1335037 (m : hreal) (n : hreal) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1335038 (m : hreal) (n : hreal) : term3 m n.
Proof. exact (EQ_MP (@lem1335037 m n) (@lem1335036 m n)). Qed.
Lemma lem1335039 (m : hreal) (n : hreal) (p : hreal) : term4 m n p.
Proof. exact (@lem1335038 m n p). Qed.
Lemma lem1335040 (m : hreal) (n : hreal) (p : hreal) : (term4 m n p) = (((hreal_add m n) = (hreal_add m p)) = (n = p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1335042 (x : hreal) : term96 x.
Proof. exact (@lem1319802 x). Qed.
Lemma lem1335043 (x : hreal) : (term96 x) = (term97 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem1335044 (x : hreal) : term97 x.
Proof. exact (EQ_MP (@lem1335043 x) (@lem1335042 x)). Qed.
Lemma lem1335045 (x : hreal) (y : hreal) : term98 x y.
Proof. exact (@lem1335044 x y). Qed.
Lemma lem1335046 (y : hreal) (x : hreal) : (term98 x y) = (term99 y x).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem1335048 (x1 : hreal) : term100 x1.
Proof. exact (@lem1319496 x1). Qed.
Lemma lem1335049 (x1 : hreal) : (term100 x1) = (term101 x1).
Proof. exact (eq_refl (term100 x1)). Qed.
Lemma lem1335050 (x1 : hreal) : term101 x1.
Proof. exact (EQ_MP (@lem1335049 x1) (@lem1335048 x1)). Qed.
Lemma lem1335051 (x1 : hreal) (x2 : hreal) : term102 x1 x2.
Proof. exact (@lem1335050 x1 x2). Qed.
Lemma lem1335052 (x2 : hreal) (x1 : hreal) : (term102 x1 x2) = (term103 x2 x1).
Proof. exact (eq_refl (term102 x1 x2)). Qed.
Lemma lem1335053 (x2 : hreal) (x1 : hreal) : term103 x2 x1.
Proof. exact (EQ_MP (@lem1335052 x2 x1) (@lem1335051 x1 x2)). Qed.
Lemma lem1335054 (x1 : hreal) (x2 : hreal) (h1 : hreal_le x1 x2) : hreal_le x1 x2.
Proof. exact (h1). Qed.
Lemma lem1335055 (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : hreal_le x2 x1.
Proof. exact (h1). Qed.
Lemma lem1335056 (x : prod hreal hreal) : term36 x.
Proof. exact (@lem1326193 x). Qed.
Lemma lem1335057 (x : prod hreal hreal) : (term36 x) = (treal_eq x x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1335058 (x : prod hreal hreal) : treal_eq x x.
Proof. exact (EQ_MP (@lem1335057 x) (@lem1335056 x)). Qed.
Lemma lem1335059 (x : prod hreal hreal) : (treal_eq x x) = ((treal_eq x x) = True).
Proof. exact (@lem7 (treal_eq x x)). Qed.
Lemma lem1335061 (m : hreal) : term0 m.
Proof. exact (@lem1321346 m). Qed.
Lemma lem1335062 (m : hreal) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1335063 (m : hreal) : term1 m.
Proof. exact (EQ_MP (@lem1335062 m) (@lem1335061 m)). Qed.
Lemma lem1335064 (m : hreal) (n : hreal) : term2 m n.
Proof. exact (@lem1335063 m n). Qed.
Lemma lem1335065 (m : hreal) (n : hreal) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1335066 (m : hreal) (n : hreal) : term3 m n.
Proof. exact (EQ_MP (@lem1335065 m n) (@lem1335064 m n)). Qed.
Lemma lem1335067 (m : hreal) (n : hreal) (p : hreal) : term4 m n p.
Proof. exact (@lem1335066 m n p). Qed.
Lemma lem1335068 (m : hreal) (n : hreal) (p : hreal) : (term4 m n p) = (((hreal_add m n) = (hreal_add m p)) = (n = p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1335070 (x : hreal) : term37 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1335071 (x : hreal) : (term37 x) = (term38 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1335072 (x : hreal) : term38 x.
Proof. exact (EQ_MP (@lem1335071 x) (@lem1335070 x)). Qed.
Lemma lem1335073 (x : hreal) (y : hreal) : term39 x y.
Proof. exact (@lem1335072 x y). Qed.
Lemma lem1335074 (y : hreal) (x : hreal) : (term39 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term39 x y)). Qed.
Lemma lem1335076 (x : hreal) : term37 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1335077 (x : hreal) : (term37 x) = (term38 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1335078 (x : hreal) : term38 x.
Proof. exact (EQ_MP (@lem1335077 x) (@lem1335076 x)). Qed.
Lemma lem1335079 (x : hreal) (y : hreal) : term39 x y.
Proof. exact (@lem1335078 x y). Qed.
Lemma lem1335080 (y : hreal) (x : hreal) : (term39 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term39 x y)). Qed.
Lemma lem1335091 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1335080 y x) (@lem1335079 x y)). Qed.
Lemma lem1335092 (x : hreal) : (hreal_le x) = (hreal_le x).
Proof. exact (eq_refl (hreal_le x)). Qed.
Lemma lem1335093 (y : hreal) (x : hreal) : (term43 x y) = (term104 y x).
Proof. exact (MK_COMB (@lem1335092 x) (@lem1335091 y x)). Qed.
Lemma lem1335094 (x : hreal) : (term105 x) = (term106 x).
Proof. exact (fun_ext (fun y : hreal => @lem1335093 y x)). Qed.
Lemma lem1335095 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1335096 (x : hreal) : (term41 x) = (term107 x).
Proof. exact (MK_COMB (@lem1335095) (@lem1335094 x)). Qed.
Lemma lem1335097 : term108 = term109.
Proof. exact (fun_ext (fun x : hreal => @lem1335096 x)). Qed.
Lemma lem1335098 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1335099 : term110 = term111.
Proof. exact (MK_COMB (@lem1335098) (@lem1335097)). Qed.
Lemma lem1335100 : term111.
Proof. exact (EQ_MP (@lem1335099) (@lem1319607)). Qed.
Lemma lem1335101 (x : hreal) : term112 x.
Proof. exact (@lem1335100 x). Qed.
Lemma lem1335102 (x : hreal) : (term112 x) = (term107 x).
Proof. exact (eq_refl (term112 x)). Qed.
Lemma lem1335103 (x : hreal) : term107 x.
Proof. exact (EQ_MP (@lem1335102 x) (@lem1335101 x)). Qed.
Lemma lem1335104 (x : hreal) (y : hreal) : term113 x y.
Proof. exact (@lem1335103 x y). Qed.
Lemma lem1335105 (y : hreal) (x : hreal) : (term113 x y) = (term104 y x).
Proof. exact (eq_refl (term113 x y)). Qed.
Lemma lem1335106 (y : hreal) (x : hreal) : term104 y x.
Proof. exact (EQ_MP (@lem1335105 y x) (@lem1335104 x y)). Qed.
Lemma lem1335107 (y : hreal) (x : hreal) : (term104 y x) = ((term104 y x) = True).
Proof. exact (@lem7 (term104 y x)). Qed.
Lemma lem1335112 (x : hreal) (y : hreal) (z : hreal) (h1 : (term79 x y z) = (term80 x y z)) : (term79 x y z) = (term80 x y z).
Proof. exact (h1). Qed.
Lemma lem1335113 (x : hreal) (y : hreal) (z : hreal) (h1 : (term79 x y z) = (term80 x y z)) : (term80 x y z) = (term79 x y z).
Proof. exact (SYM (@lem1335112 x y z h1)). Qed.
Lemma lem1335114 (x : hreal) (y : hreal) (z : hreal) (h1 : (term80 x y z) = (term79 x y z)) : (term80 x y z) = (term79 x y z).
Proof. exact (h1). Qed.
Lemma lem1335115 (x : hreal) (y : hreal) (z : hreal) (h1 : (term80 x y z) = (term79 x y z)) : (term79 x y z) = (term80 x y z).
Proof. exact (SYM (@lem1335114 x y z h1)). Qed.
Lemma lem1335116 (x : hreal) (y : hreal) (z : hreal) : ((term79 x y z) = (term80 x y z)) = ((term80 x y z) = (term79 x y z)).
Proof. exact (prop_ext (fun h1 : (term79 x y z) = (term80 x y z) => @lem1335113 x y z h1) (fun h1 : (term80 x y z) = (term79 x y z) => @lem1335115 x y z h1)). Qed.
Lemma lem1335117 (x : hreal) (y : hreal) : (term81 x y) = (term82 x y).
Proof. exact (fun_ext (fun z : hreal => @lem1335116 x y z)). Qed.
Lemma lem1335118 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1335119 (x : hreal) (y : hreal) : (term83 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1335118) (@lem1335117 x y)). Qed.
Lemma lem1335120 (x : hreal) : (term85 x) = (term86 x).
Proof. exact (fun_ext (fun y : hreal => @lem1335119 x y)). Qed.
Lemma lem1335121 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1335122 (x : hreal) : (term87 x) = (term88 x).
Proof. exact (MK_COMB (@lem1335121) (@lem1335120 x)). Qed.
Lemma lem1335123 : term89 = term90.
Proof. exact (fun_ext (fun x : hreal => @lem1335122 x)). Qed.
Lemma lem1335124 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1335125 : term91 = term92.
Proof. exact (MK_COMB (@lem1335124) (@lem1335123)). Qed.
Lemma lem1335126 : term92.
Proof. exact (EQ_MP (@lem1335125) (@lem1320203)). Qed.
Lemma lem1335127 (x : hreal) : term93 x.
Proof. exact (@lem1335126 x). Qed.
Lemma lem1335128 (x : hreal) : (term93 x) = (term88 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem1335129 (x : hreal) : term88 x.
Proof. exact (EQ_MP (@lem1335128 x) (@lem1335127 x)). Qed.
Lemma lem1335130 (x : hreal) (y : hreal) : term94 x y.
Proof. exact (@lem1335129 x y). Qed.
Lemma lem1335131 (x : hreal) (y : hreal) : (term94 x y) = (term84 x y).
Proof. exact (eq_refl (term94 x y)). Qed.
Lemma lem1335132 (x : hreal) (y : hreal) : term84 x y.
Proof. exact (EQ_MP (@lem1335131 x y) (@lem1335130 x y)). Qed.
Lemma lem1335133 (x : hreal) (y : hreal) (z : hreal) : term95 x y z.
Proof. exact (@lem1335132 x y z). Qed.
Lemma lem1335134 (x : hreal) (y : hreal) (z : hreal) : (term95 x y z) = ((term80 x y z) = (term79 x y z)).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1335136 (m : hreal) : term0 m.
Proof. exact (@lem1321346 m). Qed.
Lemma lem1335137 (m : hreal) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1335138 (m : hreal) : term1 m.
Proof. exact (EQ_MP (@lem1335137 m) (@lem1335136 m)). Qed.
Lemma lem1335139 (m : hreal) (n : hreal) : term2 m n.
Proof. exact (@lem1335138 m n). Qed.
Lemma lem1335140 (m : hreal) (n : hreal) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1335141 (m : hreal) (n : hreal) : term3 m n.
Proof. exact (EQ_MP (@lem1335140 m n) (@lem1335139 m n)). Qed.
Lemma lem1335142 (m : hreal) (n : hreal) (p : hreal) : term4 m n p.
Proof. exact (@lem1335141 m n p). Qed.
Lemma lem1335143 (m : hreal) (n : hreal) (p : hreal) : (term4 m n p) = (((hreal_add m n) = (hreal_add m p)) = (n = p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1335145 (x : hreal) : term96 x.
Proof. exact (@lem1319802 x). Qed.
Lemma lem1335146 (x : hreal) : (term96 x) = (term97 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem1335147 (x : hreal) : term97 x.
Proof. exact (EQ_MP (@lem1335146 x) (@lem1335145 x)). Qed.
Lemma lem1335148 (x : hreal) (y : hreal) : term98 x y.
Proof. exact (@lem1335147 x y). Qed.
Lemma lem1335149 (y : hreal) (x : hreal) : (term98 x y) = (term99 y x).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem1335151 (x2 : hreal) (x1 : hreal) : term114 x2 x1.
Proof. exact (@lem9784 (hreal_le x2 x1)). Qed.
Lemma lem1335152 (x2 : hreal) (x1 : hreal) : (term114 x2 x1) = (term115 x2 x1).
Proof. exact (eq_refl (term114 x2 x1)). Qed.
Lemma lem1335153 (x2 : hreal) (x1 : hreal) : term115 x2 x1.
Proof. exact (EQ_MP (@lem1335152 x2 x1) (@lem1335151 x2 x1)). Qed.
Lemma lem1335154 (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : hreal_le x2 x1.
Proof. exact (h1). Qed.
Lemma lem1335155 (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : term116 x2 x1.
Proof. exact (h1). Qed.
Lemma lem1335156 (m : hreal) : term117 m.
Proof. exact (@lem1321459 m). Qed.
Lemma lem1335157 (m : hreal) : (term117 m) = (term118 m).
Proof. exact (eq_refl (term117 m)). Qed.
Lemma lem1335158 (m : hreal) : term118 m.
Proof. exact (EQ_MP (@lem1335157 m) (@lem1335156 m)). Qed.
Lemma lem1335159 (m : hreal) (n : hreal) : term119 m n.
Proof. exact (@lem1335158 m n). Qed.
Lemma lem1335160 (m : hreal) (n : hreal) : (term119 m n) = (term120 m n).
Proof. exact (eq_refl (term119 m n)). Qed.
Lemma lem1335161 (m : hreal) (n : hreal) : term120 m n.
Proof. exact (EQ_MP (@lem1335160 m n) (@lem1335159 m n)). Qed.
Lemma lem1335162 (m : hreal) (n : hreal) (p : hreal) : term121 m n p.
Proof. exact (@lem1335161 m n p). Qed.
Lemma lem1335163 (p : hreal) (m : hreal) (n : hreal) : (term121 m n p) = (((hreal_add m p) = (hreal_add n p)) = (m = n)).
Proof. exact (eq_refl (term121 m n p)). Qed.
Lemma lem1335165 (m : hreal) : term0 m.
Proof. exact (@lem1321346 m). Qed.
Lemma lem1335166 (m : hreal) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1335167 (m : hreal) : term1 m.
Proof. exact (EQ_MP (@lem1335166 m) (@lem1335165 m)). Qed.
Lemma lem1335168 (m : hreal) (n : hreal) : term2 m n.
Proof. exact (@lem1335167 m n). Qed.
Lemma lem1335169 (m : hreal) (n : hreal) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1335170 (m : hreal) (n : hreal) : term3 m n.
Proof. exact (EQ_MP (@lem1335169 m n) (@lem1335168 m n)). Qed.
Lemma lem1335171 (m : hreal) (n : hreal) (p : hreal) : term4 m n p.
Proof. exact (@lem1335170 m n p). Qed.
Lemma lem1335172 (m : hreal) (n : hreal) (p : hreal) : (term4 m n p) = (((hreal_add m n) = (hreal_add m p)) = (n = p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1335174 (x : hreal) : term37 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1335175 (x : hreal) : (term37 x) = (term38 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1335176 (x : hreal) : term38 x.
Proof. exact (EQ_MP (@lem1335175 x) (@lem1335174 x)). Qed.
Lemma lem1335177 (x : hreal) (y : hreal) : term39 x y.
Proof. exact (@lem1335176 x y). Qed.
Lemma lem1335178 (y : hreal) (x : hreal) : (term39 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term39 x y)). Qed.
Lemma lem1335180 (x : prod hreal hreal) : term36 x.
Proof. exact (@lem1326193 x). Qed.
Lemma lem1335181 (x : prod hreal hreal) : (term36 x) = (treal_eq x x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1335182 (x : prod hreal hreal) : treal_eq x x.
Proof. exact (EQ_MP (@lem1335181 x) (@lem1335180 x)). Qed.
Lemma lem1335183 (x : prod hreal hreal) : (treal_eq x x) = ((treal_eq x x) = True).
Proof. exact (@lem7 (treal_eq x x)). Qed.
Lemma lem1335185 (y1 : hreal) (y2 : hreal) : term122 y1 y2.
Proof. exact (@lem9784 (y1 = y2)). Qed.
Lemma lem1335186 (y1 : hreal) (y2 : hreal) : (term122 y1 y2) = (term123 y1 y2).
Proof. exact (eq_refl (term122 y1 y2)). Qed.
Lemma lem1335187 (y1 : hreal) (y2 : hreal) : term123 y1 y2.
Proof. exact (EQ_MP (@lem1335186 y1 y2) (@lem1335185 y1 y2)). Qed.
Lemma lem1335189 (y1 : hreal) (y2 : hreal) (h1 : term124 y1 y2) : term124 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1335190 (x1 : hreal) (x2 : hreal) : term122 x1 x2.
Proof. exact (@lem9784 (x1 = x2)). Qed.
Lemma lem1335191 (x1 : hreal) (x2 : hreal) : (term122 x1 x2) = (term123 x1 x2).
Proof. exact (eq_refl (term122 x1 x2)). Qed.
Lemma lem1335192 (x1 : hreal) (x2 : hreal) : term123 x1 x2.
Proof. exact (EQ_MP (@lem1335191 x1 x2) (@lem1335190 x1 x2)). Qed.
Lemma lem1335194 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : term124 x1 x2.
Proof. exact (h1). Qed.
Lemma lem1335195 (y : hreal) : term125 y.
Proof. exact (@lem1325510 y). Qed.
Lemma lem1335196 (y : hreal) : (term125 y) = (term126 y).
Proof. exact (eq_refl (term125 y)). Qed.
Lemma lem1335197 (y : hreal) : term126 y.
Proof. exact (EQ_MP (@lem1335196 y) (@lem1335195 y)). Qed.
Lemma lem1335198 (y : hreal) (x : hreal) : term127 y x.
Proof. exact (@lem1335197 y x). Qed.
Lemma lem1335199 (y : hreal) (x : hreal) : (term127 y x) = ((term128 x y) = (term129 y x)).
Proof. exact (eq_refl (term127 y x)). Qed.
Lemma lem1335201 (x1 : hreal) : term130 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1335202 (x1 : hreal) : (term130 x1) = (term131 x1).
Proof. exact (eq_refl (term130 x1)). Qed.
Lemma lem1335203 (x1 : hreal) : term131 x1.
Proof. exact (EQ_MP (@lem1335202 x1) (@lem1335201 x1)). Qed.
Lemma lem1335204 (x1 : hreal) (y2 : hreal) : term132 x1 y2.
Proof. exact (@lem1335203 x1 y2). Qed.
Lemma lem1335205 (x1 : hreal) (y2 : hreal) : (term132 x1 y2) = (term133 x1 y2).
Proof. exact (eq_refl (term132 x1 y2)). Qed.
Lemma lem1335206 (x1 : hreal) (y2 : hreal) : term133 x1 y2.
Proof. exact (EQ_MP (@lem1335205 x1 y2) (@lem1335204 x1 y2)). Qed.
Lemma lem1335207 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term134 x1 y2 x2.
Proof. exact (@lem1335206 x1 y2 x2). Qed.
Lemma lem1335208 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term134 x1 y2 x2) = (term135 x1 y2 x2).
Proof. exact (eq_refl (term134 x1 y2 x2)). Qed.
Lemma lem1335209 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term135 x1 y2 x2.
Proof. exact (EQ_MP (@lem1335208 x1 y2 x2) (@lem1335207 x1 y2 x2)). Qed.
Lemma lem1335210 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term136 x1 y2 x2 y1.
Proof. exact (@lem1335209 x1 y2 x2 y1). Qed.
Lemma lem1335211 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term136 x1 y2 x2 y1) = ((term137 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term136 x1 y2 x2 y1)). Qed.
Lemma lem1335213 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term138 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1335214 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term138 _5106 _5107 P) = ((term139 _5106 _5107 P) = (term140 _5106 _5107 P)).
Proof. exact (eq_refl (term138 _5106 _5107 P)). Qed.
Lemma lem1335221 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term139 _5106 _5107 P) = (term140 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1335214 _5106 _5107 P) (@lem1335213 _5106 _5107 P)). Qed.
Lemma lem1335222 (P : type1233) : (term141 P) = (term142 P).
Proof. exact (@lem1335221 hreal hreal P). Qed.
Lemma lem1335223 : term143 = term144.
Proof. exact (@lem1335222 term145). Qed.
Lemma lem1335224 (x : prod hreal hreal) : (term146 x) = (term147 x).
Proof. exact (eq_refl (term146 x)). Qed.
Lemma lem1335225 : term148 = term145.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1335224 x)). Qed.
Lemma lem1335226 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1335227 : term143 = term149.
Proof. exact (MK_COMB (@lem1335226) (@lem1335225)). Qed.
Lemma lem1335228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1335229 : term150 = term151.
Proof. exact (MK_COMB (@lem1335228) (@lem1335227)). Qed.
Lemma lem1335230 (p1 : hreal) (p2 : hreal) : (term152 p1 p2) = (term153 p1 p2).
Proof. exact (eq_refl (term152 p1 p2)). Qed.
Lemma lem1335231 (p1 : hreal) : (term154 p1) = (term155 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1335230 p1 p2)). Qed.
Lemma lem1335232 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1335233 (p1 : hreal) : (term156 p1) = (term157 p1).
Proof. exact (MK_COMB (@lem1335232) (@lem1335231 p1)). Qed.
Lemma lem1335234 : term158 = term159.
Proof. exact (fun_ext (fun p1 : hreal => @lem1335233 p1)). Qed.
Lemma lem1335235 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1335236 : term144 = term160.
Proof. exact (MK_COMB (@lem1335235) (@lem1335234)). Qed.
Lemma lem1335237 : (term143 = term144) = (term149 = term160).
Proof. exact (MK_COMB (@lem1335229) (@lem1335236)). Qed.
Lemma lem1335238 : term149 = term160.
Proof. exact (EQ_MP (@lem1335237) (@lem1335223)). Qed.
Lemma lem1335256 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term139 _5106 _5107 P) = (term140 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1335214 _5106 _5107 P) (@lem1335213 _5106 _5107 P)). Qed.
Lemma lem1335257 (P : type1233) : (term141 P) = (term142 P).
Proof. exact (@lem1335256 hreal hreal P). Qed.
Lemma lem1335258 (p1 : hreal) (p2 : hreal) : (term161 p1 p2) = (term162 p1 p2).
Proof. exact (@lem1335257 (term163 p1 p2)). Qed.
Lemma lem1335259 (p1 : hreal) (p2 : hreal) (y : prod hreal hreal) : (term164 p1 p2 y) = (term165 p1 p2 y).
Proof. exact (eq_refl (term164 p1 p2 y)). Qed.
Lemma lem1335260 (p1 : hreal) (p2 : hreal) : (term166 p1 p2) = (term163 p1 p2).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1335259 p1 p2 y)). Qed.
Lemma lem1335261 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1335262 (p1 : hreal) (p2 : hreal) : (term161 p1 p2) = (term153 p1 p2).
Proof. exact (MK_COMB (@lem1335261) (@lem1335260 p1 p2)). Qed.
Lemma lem1335263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1335264 (p1 : hreal) (p2 : hreal) : (term167 p1 p2) = (term168 p1 p2).
Proof. exact (MK_COMB (@lem1335263) (@lem1335262 p1 p2)). Qed.
Lemma lem1335265 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term169 p1 p2 p1' p2') = (term170 p1 p2 p1' p2').
Proof. exact (eq_refl (term169 p1 p2 p1' p2')). Qed.
Lemma lem1335266 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term171 p1 p2 p1') = (term172 p1 p2 p1').
Proof. exact (fun_ext (fun p2' : hreal => @lem1335265 p1 p2 p1' p2')). Qed.
Lemma lem1335267 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1335268 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term173 p1 p2 p1') = (term174 p1 p2 p1').
Proof. exact (MK_COMB (@lem1335267) (@lem1335266 p1 p2 p1')). Qed.
Lemma lem1335269 (p1 : hreal) (p2 : hreal) : (term175 p1 p2) = (term176 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1335268 p1 p2 p1')). Qed.
Lemma lem1335270 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1335271 (p1 : hreal) (p2 : hreal) : (term162 p1 p2) = (term177 p1 p2).
Proof. exact (MK_COMB (@lem1335270) (@lem1335269 p1 p2)). Qed.
Lemma lem1335272 (p1 : hreal) (p2 : hreal) : ((term161 p1 p2) = (term162 p1 p2)) = ((term153 p1 p2) = (term177 p1 p2)).
Proof. exact (MK_COMB (@lem1335264 p1 p2) (@lem1335271 p1 p2)). Qed.
Lemma lem1335273 (p1 : hreal) (p2 : hreal) : (term153 p1 p2) = (term177 p1 p2).
Proof. exact (EQ_MP (@lem1335272 p1 p2) (@lem1335258 p1 p2)). Qed.
Lemma lem1335288 (p1 : hreal) : (term155 p1) = (term178 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1335273 p1 p2)). Qed.
Lemma lem1335289 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1335290 (p1 : hreal) : (term157 p1) = (term179 p1).
Proof. exact (MK_COMB (@lem1335289) (@lem1335288 p1)). Qed.
Lemma lem1335297 : term159 = term180.
Proof. exact (fun_ext (fun p1 : hreal => @lem1335290 p1)). Qed.
Lemma lem1335298 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1335299 : term160 = term181.
Proof. exact (MK_COMB (@lem1335298) (@lem1335297)). Qed.
Lemma lem1335306 : term149 = term181.
Proof. exact (TRANS (@lem1335238) (@lem1335299)). Qed.
Lemma lem1335307 : term181 = term149.
Proof. exact (SYM (@lem1335306)). Qed.
Lemma lem1335309 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term137 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1335211 x1 y2 x2 y1) (@lem1335210 x1 y2 x2 y1)). Qed.
Lemma lem1335310 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term137 x1 x2 y1 y2) = ((hreal_add x1 y2) = (hreal_add y1 x2)).
Proof. exact (@lem1335309 x1 y2 y1 x2). Qed.
Lemma lem1335311 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1335312 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term182 x1 x2 y1 y2) = (term183 x1 y2 y1 x2).
Proof. exact (MK_COMB (@lem1335311) (@lem1335310 x1 y2 y1 x2)). Qed.
Lemma lem1335314 (y : hreal) (x : hreal) : (term128 x y) = (term129 y x).
Proof. exact (EQ_MP (@lem1335199 y x) (@lem1335198 y x)). Qed.
Lemma lem1335315 (x2 : hreal) (x1 : hreal) : (term128 x1 x2) = (term129 x2 x1).
Proof. exact (@lem1335314 x2 x1). Qed.
Lemma lem1335316 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1335317 (x2 : hreal) (x1 : hreal) : (term184 x1 x2) = (term185 x2 x1).
Proof. exact (MK_COMB (@lem1335316) (@lem1335315 x2 x1)). Qed.
Lemma lem1335319 (y : hreal) (x : hreal) : (term128 x y) = (term129 y x).
Proof. exact (EQ_MP (@lem1335199 y x) (@lem1335198 y x)). Qed.
Lemma lem1335320 (y2 : hreal) (y1 : hreal) : (term128 y1 y2) = (term129 y2 y1).
Proof. exact (@lem1335319 y2 y1). Qed.
Lemma lem1335321 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term186 x1 x2 y1 y2) = (term187 x2 x1 y2 y1).
Proof. exact (MK_COMB (@lem1335317 x2 x1) (@lem1335320 y2 y1)). Qed.
Lemma lem1335322 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term170 x1 x2 y1 y2) = (term188 x2 x1 y2 y1).
Proof. exact (MK_COMB (@lem1335312 x1 y2 y1 x2) (@lem1335321 x2 x1 y2 y1)). Qed.
Lemma lem1335323 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term188 x2 x1 y2 y1) = (term170 x1 x2 y1 y2).
Proof. exact (SYM (@lem1335322 x2 x1 y2 y1)). Qed.
Lemma lem1335331 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : x1 = x2.
Proof. exact (h1). Qed.
Lemma lem1335332 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1335333 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (hreal_add x1) = (hreal_add x2).
Proof. exact (MK_COMB (@lem1335332) (@lem1335331 x1 x2 h1)). Qed.
Lemma lem1335334 (y2 : hreal) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem1335335 (y2 : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (hreal_add x1 y2) = (hreal_add x2 y2).
Proof. exact (MK_COMB (@lem1335333 x1 x2 h1) (@lem1335334 y2)). Qed.
Lemma lem1335336 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1335337 (y2 : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term189 x1 y2) = (term189 x2 y2).
Proof. exact (MK_COMB (@lem1335336) (@lem1335335 y2 x1 x2 h1)). Qed.
Lemma lem1335339 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : y1 = y2.
Proof. exact (h1). Qed.
Lemma lem1335340 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1335341 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (hreal_add y1) = (hreal_add y2).
Proof. exact (MK_COMB (@lem1335340) (@lem1335339 y1 y2 h1)). Qed.
Lemma lem1335342 (x2 : hreal) : x2 = x2.
Proof. exact (eq_refl x2). Qed.
Lemma lem1335343 (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (hreal_add y1 x2) = (hreal_add y2 x2).
Proof. exact (MK_COMB (@lem1335341 y1 y2 h1) (@lem1335342 x2)). Qed.
Lemma lem1335344 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : x1 = x2) (h2 : y1 = y2) : ((hreal_add x1 y2) = (hreal_add y1 x2)) = ((hreal_add x2 y2) = (hreal_add y2 x2)).
Proof. exact (MK_COMB (@lem1335337 y2 x1 x2 h1) (@lem1335343 x2 y1 y2 h2)). Qed.
Lemma lem1335347 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1335348 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : x1 = x2) (h2 : y1 = y2) : (term183 x1 y2 y1 x2) = (term190 y2 x2).
Proof. exact (MK_COMB (@lem1335347) (@lem1335344 x1 x2 y1 y2 h1 h2)). Qed.
Lemma lem1335354 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : x1 = x2.
Proof. exact (h1). Qed.
Lemma lem1335355 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1335356 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (@eq hreal x1) = (@eq hreal x2).
Proof. exact (MK_COMB (@lem1335355) (@lem1335354 x1 x2 h1)). Qed.
Lemma lem1335357 (x2 : hreal) : x2 = x2.
Proof. exact (eq_refl x2). Qed.
Lemma lem1335358 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (x1 = x2) = (x2 = x2).
Proof. exact (MK_COMB (@lem1335356 x1 x2 h1) (@lem1335357 x2)). Qed.
Lemma lem1335360 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1335361 (x : hreal) : (x = x) = True.
Proof. exact (@lem1335360 hreal x). Qed.
Lemma lem1335362 (x2 : hreal) : (x2 = x2) = True.
Proof. exact (@lem1335361 x2). Qed.
Lemma lem1335363 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (x1 = x2) = True.
Proof. exact (TRANS (@lem1335358 x1 x2 h1) (@lem1335362 x2)). Qed.
Lemma lem1335364 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1335365 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term191 x1 x2) = (@COND (prod hreal hreal) True).
Proof. exact (MK_COMB (@lem1335364) (@lem1335363 x1 x2 h1)). Qed.
Lemma lem1335366 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem1335367 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term193 x1 x2) = term194.
Proof. exact (MK_COMB (@lem1335365 x1 x2 h1) (@lem1335366)). Qed.
Lemma lem1335369 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : x1 = x2.
Proof. exact (h1). Qed.
Lemma lem1335370 (x2 : hreal) : (hreal_le x2) = (hreal_le x2).
Proof. exact (eq_refl (hreal_le x2)). Qed.
Lemma lem1335371 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (hreal_le x2 x1) = (hreal_le x2 x2).
Proof. exact (MK_COMB (@lem1335370 x2) (@lem1335369 x1 x2 h1)). Qed.
Lemma lem1335372 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1335373 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term195 x2 x1) = (term196 x2).
Proof. exact (MK_COMB (@lem1335372) (@lem1335371 x1 x2 h1)). Qed.
Lemma lem1335379 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : x1 = x2.
Proof. exact (h1). Qed.
Lemma lem1335380 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1335381 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (@eq hreal x1) = (@eq hreal x2).
Proof. exact (MK_COMB (@lem1335380) (@lem1335379 x1 x2 h1)). Qed.
Lemma lem1335382 (x2 : hreal) (d : hreal) : (hreal_add x2 d) = (hreal_add x2 d).
Proof. exact (eq_refl (hreal_add x2 d)). Qed.
Lemma lem1335383 (d : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (x1 = (hreal_add x2 d)) = (x2 = (hreal_add x2 d)).
Proof. exact (MK_COMB (@lem1335381 x1 x2 h1) (@lem1335382 x2 d)). Qed.
Lemma lem1335386 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term197 x1 x2) = (term21 x2).
Proof. exact (fun_ext (fun d : hreal => @lem1335383 d x1 x2 h1)). Qed.
Lemma lem1335387 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1335388 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term198 x1 x2) = (term199 x2).
Proof. exact (MK_COMB (@lem1335387) (@lem1335386 x1 x2 h1)). Qed.
Lemma lem1335391 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1335392 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term200 x1 x2) = (term201 x2).
Proof. exact (MK_COMB (@lem1335391) (@lem1335388 x1 x2 h1)). Qed.
Lemma lem1335393 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1335394 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term202 x1 x2) = (term203 x2).
Proof. exact (MK_COMB (@lem1335393) (@lem1335392 x1 x2 h1)). Qed.
Lemma lem1335395 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1335396 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term204 x1 x2) = (term205 x2).
Proof. exact (MK_COMB (@lem1335394 x1 x2 h1) (@lem1335395)). Qed.
Lemma lem1335397 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term206 x1 x2) = (term207 x2).
Proof. exact (MK_COMB (@lem1335373 x1 x2 h1) (@lem1335396 x1 x2 h1)). Qed.
Lemma lem1335403 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : x1 = x2.
Proof. exact (h1). Qed.
Lemma lem1335404 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1335405 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (hreal_add x1) = (hreal_add x2).
Proof. exact (MK_COMB (@lem1335404) (@lem1335403 x1 x2 h1)). Qed.
Lemma lem1335406 (d : hreal) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1335407 (d : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (hreal_add x1 d) = (hreal_add x2 d).
Proof. exact (MK_COMB (@lem1335405 x1 x2 h1) (@lem1335406 d)). Qed.
Lemma lem1335408 (x2 : hreal) : (@eq hreal x2) = (@eq hreal x2).
Proof. exact (eq_refl (@eq hreal x2)). Qed.
Lemma lem1335409 (d : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (x2 = (hreal_add x1 d)) = (x2 = (hreal_add x2 d)).
Proof. exact (MK_COMB (@lem1335408 x2) (@lem1335407 d x1 x2 h1)). Qed.
Lemma lem1335412 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term197 x2 x1) = (term21 x2).
Proof. exact (fun_ext (fun d : hreal => @lem1335409 d x1 x2 h1)). Qed.
Lemma lem1335413 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1335414 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term198 x2 x1) = (term199 x2).
Proof. exact (MK_COMB (@lem1335413) (@lem1335412 x1 x2 h1)). Qed.
Lemma lem1335417 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1335418 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term200 x2 x1) = (term201 x2).
Proof. exact (MK_COMB (@lem1335417) (@lem1335414 x1 x2 h1)). Qed.
Lemma lem1335419 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem1335420 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term209 x2 x1) = (term210 x2).
Proof. exact (MK_COMB (@lem1335419) (@lem1335418 x1 x2 h1)). Qed.
Lemma lem1335421 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term211 x2 x1) = (term212 x2).
Proof. exact (MK_COMB (@lem1335397 x1 x2 h1) (@lem1335420 x1 x2 h1)). Qed.
Lemma lem1335422 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term129 x2 x1) = (term213 x2).
Proof. exact (MK_COMB (@lem1335367 x1 x2 h1) (@lem1335421 x1 x2 h1)). Qed.
Lemma lem1335424 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1335425 (t2 : prod hreal hreal) (t1 : prod hreal hreal) : (@COND (prod hreal hreal) True t1 t2) = t1.
Proof. exact (@lem1335424 (prod hreal hreal) t2 t1). Qed.
Lemma lem1335426 (x2 : hreal) : (term213 x2) = term192.
Proof. exact (@lem1335425 (term212 x2) term192). Qed.
Lemma lem1335427 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term129 x2 x1) = term192.
Proof. exact (TRANS (@lem1335422 x1 x2 h1) (@lem1335426 x2)). Qed.
Lemma lem1335428 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1335429 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term185 x2 x1) = term214.
Proof. exact (MK_COMB (@lem1335428) (@lem1335427 x1 x2 h1)). Qed.
Lemma lem1335435 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : y1 = y2.
Proof. exact (h1). Qed.
Lemma lem1335436 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1335437 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (@eq hreal y1) = (@eq hreal y2).
Proof. exact (MK_COMB (@lem1335436) (@lem1335435 y1 y2 h1)). Qed.
Lemma lem1335438 (y2 : hreal) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem1335439 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (y1 = y2) = (y2 = y2).
Proof. exact (MK_COMB (@lem1335437 y1 y2 h1) (@lem1335438 y2)). Qed.
Lemma lem1335441 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1335442 (x : hreal) : (x = x) = True.
Proof. exact (@lem1335441 hreal x). Qed.
Lemma lem1335443 (y2 : hreal) : (y2 = y2) = True.
Proof. exact (@lem1335442 y2). Qed.
Lemma lem1335444 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (y1 = y2) = True.
Proof. exact (TRANS (@lem1335439 y1 y2 h1) (@lem1335443 y2)). Qed.
Lemma lem1335445 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1335446 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term191 y1 y2) = (@COND (prod hreal hreal) True).
Proof. exact (MK_COMB (@lem1335445) (@lem1335444 y1 y2 h1)). Qed.
Lemma lem1335447 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem1335448 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term193 y1 y2) = term194.
Proof. exact (MK_COMB (@lem1335446 y1 y2 h1) (@lem1335447)). Qed.
Lemma lem1335450 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : y1 = y2.
Proof. exact (h1). Qed.
Lemma lem1335451 (y2 : hreal) : (hreal_le y2) = (hreal_le y2).
Proof. exact (eq_refl (hreal_le y2)). Qed.
Lemma lem1335452 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (hreal_le y2 y1) = (hreal_le y2 y2).
Proof. exact (MK_COMB (@lem1335451 y2) (@lem1335450 y1 y2 h1)). Qed.
Lemma lem1335453 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1335454 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term195 y2 y1) = (term196 y2).
Proof. exact (MK_COMB (@lem1335453) (@lem1335452 y1 y2 h1)). Qed.
Lemma lem1335460 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : y1 = y2.
Proof. exact (h1). Qed.
Lemma lem1335461 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1335462 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (@eq hreal y1) = (@eq hreal y2).
Proof. exact (MK_COMB (@lem1335461) (@lem1335460 y1 y2 h1)). Qed.
Lemma lem1335463 (y2 : hreal) (d : hreal) : (hreal_add y2 d) = (hreal_add y2 d).
Proof. exact (eq_refl (hreal_add y2 d)). Qed.
Lemma lem1335464 (d : hreal) (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (y1 = (hreal_add y2 d)) = (y2 = (hreal_add y2 d)).
Proof. exact (MK_COMB (@lem1335462 y1 y2 h1) (@lem1335463 y2 d)). Qed.
Lemma lem1335467 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term197 y1 y2) = (term21 y2).
Proof. exact (fun_ext (fun d : hreal => @lem1335464 d y1 y2 h1)). Qed.
Lemma lem1335468 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1335469 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term198 y1 y2) = (term199 y2).
Proof. exact (MK_COMB (@lem1335468) (@lem1335467 y1 y2 h1)). Qed.
Lemma lem1335472 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1335473 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term200 y1 y2) = (term201 y2).
Proof. exact (MK_COMB (@lem1335472) (@lem1335469 y1 y2 h1)). Qed.
Lemma lem1335474 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1335475 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term202 y1 y2) = (term203 y2).
Proof. exact (MK_COMB (@lem1335474) (@lem1335473 y1 y2 h1)). Qed.
Lemma lem1335476 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1335477 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term204 y1 y2) = (term205 y2).
Proof. exact (MK_COMB (@lem1335475 y1 y2 h1) (@lem1335476)). Qed.
Lemma lem1335478 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term206 y1 y2) = (term207 y2).
Proof. exact (MK_COMB (@lem1335454 y1 y2 h1) (@lem1335477 y1 y2 h1)). Qed.
Lemma lem1335484 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : y1 = y2.
Proof. exact (h1). Qed.
Lemma lem1335485 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1335486 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (hreal_add y1) = (hreal_add y2).
Proof. exact (MK_COMB (@lem1335485) (@lem1335484 y1 y2 h1)). Qed.
Lemma lem1335487 (d : hreal) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1335488 (d : hreal) (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (hreal_add y1 d) = (hreal_add y2 d).
Proof. exact (MK_COMB (@lem1335486 y1 y2 h1) (@lem1335487 d)). Qed.
Lemma lem1335489 (y2 : hreal) : (@eq hreal y2) = (@eq hreal y2).
Proof. exact (eq_refl (@eq hreal y2)). Qed.
Lemma lem1335490 (d : hreal) (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (y2 = (hreal_add y1 d)) = (y2 = (hreal_add y2 d)).
Proof. exact (MK_COMB (@lem1335489 y2) (@lem1335488 d y1 y2 h1)). Qed.
Lemma lem1335493 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term197 y2 y1) = (term21 y2).
Proof. exact (fun_ext (fun d : hreal => @lem1335490 d y1 y2 h1)). Qed.
Lemma lem1335494 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1335495 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term198 y2 y1) = (term199 y2).
Proof. exact (MK_COMB (@lem1335494) (@lem1335493 y1 y2 h1)). Qed.
Lemma lem1335498 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1335499 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term200 y2 y1) = (term201 y2).
Proof. exact (MK_COMB (@lem1335498) (@lem1335495 y1 y2 h1)). Qed.
Lemma lem1335500 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem1335501 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term209 y2 y1) = (term210 y2).
Proof. exact (MK_COMB (@lem1335500) (@lem1335499 y1 y2 h1)). Qed.
Lemma lem1335502 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term211 y2 y1) = (term212 y2).
Proof. exact (MK_COMB (@lem1335478 y1 y2 h1) (@lem1335501 y1 y2 h1)). Qed.
Lemma lem1335503 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term129 y2 y1) = (term213 y2).
Proof. exact (MK_COMB (@lem1335448 y1 y2 h1) (@lem1335502 y1 y2 h1)). Qed.
Lemma lem1335505 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1335506 (t2 : prod hreal hreal) (t1 : prod hreal hreal) : (@COND (prod hreal hreal) True t1 t2) = t1.
Proof. exact (@lem1335505 (prod hreal hreal) t2 t1). Qed.
Lemma lem1335507 (y2 : hreal) : (term213 y2) = term192.
Proof. exact (@lem1335506 (term212 y2) term192). Qed.
Lemma lem1335508 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term129 y2 y1) = term192.
Proof. exact (TRANS (@lem1335503 y1 y2 h1) (@lem1335507 y2)). Qed.
Lemma lem1335509 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : x1 = x2) (h2 : y1 = y2) : (term187 x2 x1 y2 y1) = term215.
Proof. exact (MK_COMB (@lem1335429 x1 x2 h1) (@lem1335508 y1 y2 h2)). Qed.
Lemma lem1335510 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : x1 = x2) (h2 : y1 = y2) : (term188 x2 x1 y2 y1) = (term216 y2 x2).
Proof. exact (MK_COMB (@lem1335348 x1 x2 y1 y2 h1 h2) (@lem1335509 x1 x2 y1 y2 h1 h2)). Qed.
Lemma lem1335515 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : x1 = x2) (h2 : y1 = y2) : (term216 y2 x2) = (term188 x2 x1 y2 y1).
Proof. exact (SYM (@lem1335510 x1 x2 y1 y2 h1 h2)). Qed.
Lemma lem1335516 (y1 : hreal) (y2 : hreal) : term217 y1 y2.
Proof. exact (@lem82 (y1 = y2)). Qed.
Lemma lem1335536 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : x1 = x2.
Proof. exact (h1). Qed.
Lemma lem1335537 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1335538 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (hreal_add x1) = (hreal_add x2).
Proof. exact (MK_COMB (@lem1335537) (@lem1335536 x1 x2 h1)). Qed.
Lemma lem1335539 (y2 : hreal) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem1335540 (y2 : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (hreal_add x1 y2) = (hreal_add x2 y2).
Proof. exact (MK_COMB (@lem1335538 x1 x2 h1) (@lem1335539 y2)). Qed.
Lemma lem1335541 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1335542 (y2 : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term189 x1 y2) = (term189 x2 y2).
Proof. exact (MK_COMB (@lem1335541) (@lem1335540 y2 x1 x2 h1)). Qed.
Lemma lem1335543 (y1 : hreal) (x2 : hreal) : (hreal_add y1 x2) = (hreal_add y1 x2).
Proof. exact (eq_refl (hreal_add y1 x2)). Qed.
Lemma lem1335544 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : ((hreal_add x1 y2) = (hreal_add y1 x2)) = ((hreal_add x2 y2) = (hreal_add y1 x2)).
Proof. exact (MK_COMB (@lem1335542 y2 x1 x2 h1) (@lem1335543 y1 x2)). Qed.
Lemma lem1335547 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1335548 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term183 x1 y2 y1 x2) = (term218 y2 y1 x2).
Proof. exact (MK_COMB (@lem1335547) (@lem1335544 y2 y1 x1 x2 h1)). Qed.
Lemma lem1335554 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : x1 = x2.
Proof. exact (h1). Qed.
Lemma lem1335555 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1335556 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (@eq hreal x1) = (@eq hreal x2).
Proof. exact (MK_COMB (@lem1335555) (@lem1335554 x1 x2 h1)). Qed.
Lemma lem1335557 (x2 : hreal) : x2 = x2.
Proof. exact (eq_refl x2). Qed.
Lemma lem1335558 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (x1 = x2) = (x2 = x2).
Proof. exact (MK_COMB (@lem1335556 x1 x2 h1) (@lem1335557 x2)). Qed.
Lemma lem1335560 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1335561 (x : hreal) : (x = x) = True.
Proof. exact (@lem1335560 hreal x). Qed.
Lemma lem1335562 (x2 : hreal) : (x2 = x2) = True.
Proof. exact (@lem1335561 x2). Qed.
Lemma lem1335563 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (x1 = x2) = True.
Proof. exact (TRANS (@lem1335558 x1 x2 h1) (@lem1335562 x2)). Qed.
Lemma lem1335564 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1335565 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term191 x1 x2) = (@COND (prod hreal hreal) True).
Proof. exact (MK_COMB (@lem1335564) (@lem1335563 x1 x2 h1)). Qed.
Lemma lem1335566 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem1335567 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term193 x1 x2) = term194.
Proof. exact (MK_COMB (@lem1335565 x1 x2 h1) (@lem1335566)). Qed.
Lemma lem1335569 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : x1 = x2.
Proof. exact (h1). Qed.
Lemma lem1335570 (x2 : hreal) : (hreal_le x2) = (hreal_le x2).
Proof. exact (eq_refl (hreal_le x2)). Qed.
Lemma lem1335571 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (hreal_le x2 x1) = (hreal_le x2 x2).
Proof. exact (MK_COMB (@lem1335570 x2) (@lem1335569 x1 x2 h1)). Qed.
Lemma lem1335572 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1335573 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term195 x2 x1) = (term196 x2).
Proof. exact (MK_COMB (@lem1335572) (@lem1335571 x1 x2 h1)). Qed.
Lemma lem1335579 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : x1 = x2.
Proof. exact (h1). Qed.
Lemma lem1335580 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1335581 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (@eq hreal x1) = (@eq hreal x2).
Proof. exact (MK_COMB (@lem1335580) (@lem1335579 x1 x2 h1)). Qed.
Lemma lem1335582 (x2 : hreal) (d : hreal) : (hreal_add x2 d) = (hreal_add x2 d).
Proof. exact (eq_refl (hreal_add x2 d)). Qed.
Lemma lem1335583 (d : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (x1 = (hreal_add x2 d)) = (x2 = (hreal_add x2 d)).
Proof. exact (MK_COMB (@lem1335581 x1 x2 h1) (@lem1335582 x2 d)). Qed.
Lemma lem1335586 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term197 x1 x2) = (term21 x2).
Proof. exact (fun_ext (fun d : hreal => @lem1335583 d x1 x2 h1)). Qed.
Lemma lem1335587 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1335588 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term198 x1 x2) = (term199 x2).
Proof. exact (MK_COMB (@lem1335587) (@lem1335586 x1 x2 h1)). Qed.
Lemma lem1335591 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1335592 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term200 x1 x2) = (term201 x2).
Proof. exact (MK_COMB (@lem1335591) (@lem1335588 x1 x2 h1)). Qed.
Lemma lem1335593 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1335594 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term202 x1 x2) = (term203 x2).
Proof. exact (MK_COMB (@lem1335593) (@lem1335592 x1 x2 h1)). Qed.
Lemma lem1335595 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1335596 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term204 x1 x2) = (term205 x2).
Proof. exact (MK_COMB (@lem1335594 x1 x2 h1) (@lem1335595)). Qed.
Lemma lem1335597 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term206 x1 x2) = (term207 x2).
Proof. exact (MK_COMB (@lem1335573 x1 x2 h1) (@lem1335596 x1 x2 h1)). Qed.
Lemma lem1335603 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : x1 = x2.
Proof. exact (h1). Qed.
Lemma lem1335604 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1335605 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (hreal_add x1) = (hreal_add x2).
Proof. exact (MK_COMB (@lem1335604) (@lem1335603 x1 x2 h1)). Qed.
Lemma lem1335606 (d : hreal) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1335607 (d : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (hreal_add x1 d) = (hreal_add x2 d).
Proof. exact (MK_COMB (@lem1335605 x1 x2 h1) (@lem1335606 d)). Qed.
Lemma lem1335608 (x2 : hreal) : (@eq hreal x2) = (@eq hreal x2).
Proof. exact (eq_refl (@eq hreal x2)). Qed.
Lemma lem1335609 (d : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (x2 = (hreal_add x1 d)) = (x2 = (hreal_add x2 d)).
Proof. exact (MK_COMB (@lem1335608 x2) (@lem1335607 d x1 x2 h1)). Qed.
Lemma lem1335612 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term197 x2 x1) = (term21 x2).
Proof. exact (fun_ext (fun d : hreal => @lem1335609 d x1 x2 h1)). Qed.
Lemma lem1335613 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1335614 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term198 x2 x1) = (term199 x2).
Proof. exact (MK_COMB (@lem1335613) (@lem1335612 x1 x2 h1)). Qed.
Lemma lem1335617 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1335618 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term200 x2 x1) = (term201 x2).
Proof. exact (MK_COMB (@lem1335617) (@lem1335614 x1 x2 h1)). Qed.
Lemma lem1335619 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem1335620 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term209 x2 x1) = (term210 x2).
Proof. exact (MK_COMB (@lem1335619) (@lem1335618 x1 x2 h1)). Qed.
Lemma lem1335621 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term211 x2 x1) = (term212 x2).
Proof. exact (MK_COMB (@lem1335597 x1 x2 h1) (@lem1335620 x1 x2 h1)). Qed.
Lemma lem1335622 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term129 x2 x1) = (term213 x2).
Proof. exact (MK_COMB (@lem1335567 x1 x2 h1) (@lem1335621 x1 x2 h1)). Qed.
Lemma lem1335624 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1335625 (t2 : prod hreal hreal) (t1 : prod hreal hreal) : (@COND (prod hreal hreal) True t1 t2) = t1.
Proof. exact (@lem1335624 (prod hreal hreal) t2 t1). Qed.
Lemma lem1335626 (x2 : hreal) : (term213 x2) = term192.
Proof. exact (@lem1335625 (term212 x2) term192). Qed.
Lemma lem1335627 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term129 x2 x1) = term192.
Proof. exact (TRANS (@lem1335622 x1 x2 h1) (@lem1335626 x2)). Qed.
Lemma lem1335628 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1335629 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term185 x2 x1) = term214.
Proof. exact (MK_COMB (@lem1335628) (@lem1335627 x1 x2 h1)). Qed.
Lemma lem1335633 (y1 : hreal) (y2 : hreal) (h1 : term124 y1 y2) : (y1 = y2) = False.
Proof. exact (@lem1335516 y1 y2 (@lem1335189 y1 y2 h1)). Qed.
Lemma lem1335634 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1335635 (y1 : hreal) (y2 : hreal) (h1 : term124 y1 y2) : (term191 y1 y2) = (@COND (prod hreal hreal) False).
Proof. exact (MK_COMB (@lem1335634) (@lem1335633 y1 y2 h1)). Qed.
Lemma lem1335636 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem1335637 (y1 : hreal) (y2 : hreal) (h1 : term124 y1 y2) : (term193 y1 y2) = term219.
Proof. exact (MK_COMB (@lem1335635 y1 y2 h1) (@lem1335636)). Qed.
Lemma lem1335646 (y2 : hreal) (y1 : hreal) : (term211 y2 y1) = (term211 y2 y1).
Proof. exact (eq_refl (term211 y2 y1)). Qed.
Lemma lem1335647 (y1 : hreal) (y2 : hreal) (h1 : term124 y1 y2) : (term129 y2 y1) = (term220 y2 y1).
Proof. exact (MK_COMB (@lem1335637 y1 y2 h1) (@lem1335646 y2 y1)). Qed.
Lemma lem1335649 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1335650 (t1 : prod hreal hreal) (t2 : prod hreal hreal) : (@COND (prod hreal hreal) False t1 t2) = t2.
Proof. exact (@lem1335649 (prod hreal hreal) t1 t2). Qed.
Lemma lem1335651 (y2 : hreal) (y1 : hreal) : (term220 y2 y1) = (term211 y2 y1).
Proof. exact (@lem1335650 term192 (term211 y2 y1)). Qed.
Lemma lem1335660 (y1 : hreal) (y2 : hreal) (h1 : term124 y1 y2) : (term129 y2 y1) = (term211 y2 y1).
Proof. exact (TRANS (@lem1335647 y1 y2 h1) (@lem1335651 y2 y1)). Qed.
Lemma lem1335661 (y1 : hreal) (y2 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 y1 y2) (h2 : x1 = x2) : (term187 x2 x1 y2 y1) = (term221 y2 y1).
Proof. exact (MK_COMB (@lem1335629 x1 x2 h2) (@lem1335660 y1 y2 h1)). Qed.
Lemma lem1335662 (y1 : hreal) (y2 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 y1 y2) (h2 : x1 = x2) : (term188 x2 x1 y2 y1) = (term222 x2 y2 y1).
Proof. exact (MK_COMB (@lem1335548 y2 y1 x1 x2 h2) (@lem1335661 y1 y2 x1 x2 h1 h2)). Qed.
Lemma lem1335667 (y1 : hreal) (y2 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 y1 y2) (h2 : x1 = x2) : (term222 x2 y2 y1) = (term188 x2 x1 y2 y1).
Proof. exact (SYM (@lem1335662 y1 y2 x1 x2 h1 h2)). Qed.
Lemma lem1335668 (x1 : hreal) (x2 : hreal) : term217 x1 x2.
Proof. exact (@lem82 (x1 = x2)). Qed.
Lemma lem1335688 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : y1 = y2.
Proof. exact (h1). Qed.
Lemma lem1335689 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1335690 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (hreal_add y1) = (hreal_add y2).
Proof. exact (MK_COMB (@lem1335689) (@lem1335688 y1 y2 h1)). Qed.
Lemma lem1335691 (x2 : hreal) : x2 = x2.
Proof. exact (eq_refl x2). Qed.
Lemma lem1335692 (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (hreal_add y1 x2) = (hreal_add y2 x2).
Proof. exact (MK_COMB (@lem1335690 y1 y2 h1) (@lem1335691 x2)). Qed.
Lemma lem1335693 (x1 : hreal) (y2 : hreal) : (term189 x1 y2) = (term189 x1 y2).
Proof. exact (eq_refl (term189 x1 y2)). Qed.
Lemma lem1335694 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : ((hreal_add x1 y2) = (hreal_add y1 x2)) = ((hreal_add x1 y2) = (hreal_add y2 x2)).
Proof. exact (MK_COMB (@lem1335693 x1 y2) (@lem1335692 x2 y1 y2 h1)). Qed.
Lemma lem1335697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1335698 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term183 x1 y2 y1 x2) = (term223 x1 y2 x2).
Proof. exact (MK_COMB (@lem1335697) (@lem1335694 x1 x2 y1 y2 h1)). Qed.
Lemma lem1335702 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (x1 = x2) = False.
Proof. exact (@lem1335668 x1 x2 (@lem1335194 x1 x2 h1)). Qed.
Lemma lem1335703 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1335704 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (term191 x1 x2) = (@COND (prod hreal hreal) False).
Proof. exact (MK_COMB (@lem1335703) (@lem1335702 x1 x2 h1)). Qed.
Lemma lem1335705 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem1335706 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (term193 x1 x2) = term219.
Proof. exact (MK_COMB (@lem1335704 x1 x2 h1) (@lem1335705)). Qed.
Lemma lem1335715 (x2 : hreal) (x1 : hreal) : (term211 x2 x1) = (term211 x2 x1).
Proof. exact (eq_refl (term211 x2 x1)). Qed.
Lemma lem1335716 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (term129 x2 x1) = (term220 x2 x1).
Proof. exact (MK_COMB (@lem1335706 x1 x2 h1) (@lem1335715 x2 x1)). Qed.
Lemma lem1335718 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1335719 (t1 : prod hreal hreal) (t2 : prod hreal hreal) : (@COND (prod hreal hreal) False t1 t2) = t2.
Proof. exact (@lem1335718 (prod hreal hreal) t1 t2). Qed.
Lemma lem1335720 (x2 : hreal) (x1 : hreal) : (term220 x2 x1) = (term211 x2 x1).
Proof. exact (@lem1335719 term192 (term211 x2 x1)). Qed.
Lemma lem1335729 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (term129 x2 x1) = (term211 x2 x1).
Proof. exact (TRANS (@lem1335716 x1 x2 h1) (@lem1335720 x2 x1)). Qed.
Lemma lem1335730 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1335731 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (term185 x2 x1) = (term224 x2 x1).
Proof. exact (MK_COMB (@lem1335730) (@lem1335729 x1 x2 h1)). Qed.
Lemma lem1335737 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : y1 = y2.
Proof. exact (h1). Qed.
Lemma lem1335738 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1335739 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (@eq hreal y1) = (@eq hreal y2).
Proof. exact (MK_COMB (@lem1335738) (@lem1335737 y1 y2 h1)). Qed.
Lemma lem1335740 (y2 : hreal) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem1335741 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (y1 = y2) = (y2 = y2).
Proof. exact (MK_COMB (@lem1335739 y1 y2 h1) (@lem1335740 y2)). Qed.
Lemma lem1335743 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1335744 (x : hreal) : (x = x) = True.
Proof. exact (@lem1335743 hreal x). Qed.
Lemma lem1335745 (y2 : hreal) : (y2 = y2) = True.
Proof. exact (@lem1335744 y2). Qed.
Lemma lem1335746 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (y1 = y2) = True.
Proof. exact (TRANS (@lem1335741 y1 y2 h1) (@lem1335745 y2)). Qed.
Lemma lem1335747 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1335748 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term191 y1 y2) = (@COND (prod hreal hreal) True).
Proof. exact (MK_COMB (@lem1335747) (@lem1335746 y1 y2 h1)). Qed.
Lemma lem1335749 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem1335750 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term193 y1 y2) = term194.
Proof. exact (MK_COMB (@lem1335748 y1 y2 h1) (@lem1335749)). Qed.
Lemma lem1335752 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : y1 = y2.
Proof. exact (h1). Qed.
Lemma lem1335753 (y2 : hreal) : (hreal_le y2) = (hreal_le y2).
Proof. exact (eq_refl (hreal_le y2)). Qed.
Lemma lem1335754 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (hreal_le y2 y1) = (hreal_le y2 y2).
Proof. exact (MK_COMB (@lem1335753 y2) (@lem1335752 y1 y2 h1)). Qed.
Lemma lem1335755 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1335756 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term195 y2 y1) = (term196 y2).
Proof. exact (MK_COMB (@lem1335755) (@lem1335754 y1 y2 h1)). Qed.
Lemma lem1335762 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : y1 = y2.
Proof. exact (h1). Qed.
Lemma lem1335763 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1335764 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (@eq hreal y1) = (@eq hreal y2).
Proof. exact (MK_COMB (@lem1335763) (@lem1335762 y1 y2 h1)). Qed.
Lemma lem1335765 (y2 : hreal) (d : hreal) : (hreal_add y2 d) = (hreal_add y2 d).
Proof. exact (eq_refl (hreal_add y2 d)). Qed.
Lemma lem1335766 (d : hreal) (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (y1 = (hreal_add y2 d)) = (y2 = (hreal_add y2 d)).
Proof. exact (MK_COMB (@lem1335764 y1 y2 h1) (@lem1335765 y2 d)). Qed.
Lemma lem1335769 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term197 y1 y2) = (term21 y2).
Proof. exact (fun_ext (fun d : hreal => @lem1335766 d y1 y2 h1)). Qed.
Lemma lem1335770 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1335771 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term198 y1 y2) = (term199 y2).
Proof. exact (MK_COMB (@lem1335770) (@lem1335769 y1 y2 h1)). Qed.
Lemma lem1335774 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1335775 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term200 y1 y2) = (term201 y2).
Proof. exact (MK_COMB (@lem1335774) (@lem1335771 y1 y2 h1)). Qed.
Lemma lem1335776 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1335777 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term202 y1 y2) = (term203 y2).
Proof. exact (MK_COMB (@lem1335776) (@lem1335775 y1 y2 h1)). Qed.
Lemma lem1335778 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1335779 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term204 y1 y2) = (term205 y2).
Proof. exact (MK_COMB (@lem1335777 y1 y2 h1) (@lem1335778)). Qed.
Lemma lem1335780 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term206 y1 y2) = (term207 y2).
Proof. exact (MK_COMB (@lem1335756 y1 y2 h1) (@lem1335779 y1 y2 h1)). Qed.
Lemma lem1335786 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : y1 = y2.
Proof. exact (h1). Qed.
Lemma lem1335787 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1335788 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (hreal_add y1) = (hreal_add y2).
Proof. exact (MK_COMB (@lem1335787) (@lem1335786 y1 y2 h1)). Qed.
Lemma lem1335789 (d : hreal) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1335790 (d : hreal) (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (hreal_add y1 d) = (hreal_add y2 d).
Proof. exact (MK_COMB (@lem1335788 y1 y2 h1) (@lem1335789 d)). Qed.
Lemma lem1335791 (y2 : hreal) : (@eq hreal y2) = (@eq hreal y2).
Proof. exact (eq_refl (@eq hreal y2)). Qed.
Lemma lem1335792 (d : hreal) (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (y2 = (hreal_add y1 d)) = (y2 = (hreal_add y2 d)).
Proof. exact (MK_COMB (@lem1335791 y2) (@lem1335790 d y1 y2 h1)). Qed.
Lemma lem1335795 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term197 y2 y1) = (term21 y2).
Proof. exact (fun_ext (fun d : hreal => @lem1335792 d y1 y2 h1)). Qed.
Lemma lem1335796 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1335797 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term198 y2 y1) = (term199 y2).
Proof. exact (MK_COMB (@lem1335796) (@lem1335795 y1 y2 h1)). Qed.
Lemma lem1335800 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1335801 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term200 y2 y1) = (term201 y2).
Proof. exact (MK_COMB (@lem1335800) (@lem1335797 y1 y2 h1)). Qed.
Lemma lem1335802 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem1335803 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term209 y2 y1) = (term210 y2).
Proof. exact (MK_COMB (@lem1335802) (@lem1335801 y1 y2 h1)). Qed.
Lemma lem1335804 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term211 y2 y1) = (term212 y2).
Proof. exact (MK_COMB (@lem1335780 y1 y2 h1) (@lem1335803 y1 y2 h1)). Qed.
Lemma lem1335805 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term129 y2 y1) = (term213 y2).
Proof. exact (MK_COMB (@lem1335750 y1 y2 h1) (@lem1335804 y1 y2 h1)). Qed.
Lemma lem1335807 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1335808 (t2 : prod hreal hreal) (t1 : prod hreal hreal) : (@COND (prod hreal hreal) True t1 t2) = t1.
Proof. exact (@lem1335807 (prod hreal hreal) t2 t1). Qed.
Lemma lem1335809 (y2 : hreal) : (term213 y2) = term192.
Proof. exact (@lem1335808 (term212 y2) term192). Qed.
Lemma lem1335810 (y1 : hreal) (y2 : hreal) (h1 : y1 = y2) : (term129 y2 y1) = term192.
Proof. exact (TRANS (@lem1335805 y1 y2 h1) (@lem1335809 y2)). Qed.
Lemma lem1335811 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : term124 x1 x2) (h2 : y1 = y2) : (term187 x2 x1 y2 y1) = (term225 x2 x1).
Proof. exact (MK_COMB (@lem1335731 x1 x2 h1) (@lem1335810 y1 y2 h2)). Qed.
Lemma lem1335812 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : term124 x1 x2) (h2 : y1 = y2) : (term188 x2 x1 y2 y1) = (term226 y2 x2 x1).
Proof. exact (MK_COMB (@lem1335698 x1 x2 y1 y2 h2) (@lem1335811 x1 x2 y1 y2 h1 h2)). Qed.
Lemma lem1335817 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : term124 x1 x2) (h2 : y1 = y2) : (term226 y2 x2 x1) = (term188 x2 x1 y2 y1).
Proof. exact (SYM (@lem1335812 x1 x2 y1 y2 h1 h2)). Qed.
Lemma lem1335818 (x1 : hreal) (x2 : hreal) : term217 x1 x2.
Proof. exact (@lem82 (x1 = x2)). Qed.
Lemma lem1335831 (y1 : hreal) (y2 : hreal) : term217 y1 y2.
Proof. exact (@lem82 (y1 = y2)). Qed.
Lemma lem1335853 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (x1 = x2) = False.
Proof. exact (@lem1335818 x1 x2 (@lem1335194 x1 x2 h1)). Qed.
Lemma lem1335854 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1335855 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (term191 x1 x2) = (@COND (prod hreal hreal) False).
Proof. exact (MK_COMB (@lem1335854) (@lem1335853 x1 x2 h1)). Qed.
Lemma lem1335856 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem1335857 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (term193 x1 x2) = term219.
Proof. exact (MK_COMB (@lem1335855 x1 x2 h1) (@lem1335856)). Qed.
Lemma lem1335866 (x2 : hreal) (x1 : hreal) : (term211 x2 x1) = (term211 x2 x1).
Proof. exact (eq_refl (term211 x2 x1)). Qed.
Lemma lem1335867 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (term129 x2 x1) = (term220 x2 x1).
Proof. exact (MK_COMB (@lem1335857 x1 x2 h1) (@lem1335866 x2 x1)). Qed.
Lemma lem1335869 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1335870 (t1 : prod hreal hreal) (t2 : prod hreal hreal) : (@COND (prod hreal hreal) False t1 t2) = t2.
Proof. exact (@lem1335869 (prod hreal hreal) t1 t2). Qed.
Lemma lem1335871 (x2 : hreal) (x1 : hreal) : (term220 x2 x1) = (term211 x2 x1).
Proof. exact (@lem1335870 term192 (term211 x2 x1)). Qed.
Lemma lem1335880 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (term129 x2 x1) = (term211 x2 x1).
Proof. exact (TRANS (@lem1335867 x1 x2 h1) (@lem1335871 x2 x1)). Qed.
Lemma lem1335881 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1335882 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (term185 x2 x1) = (term224 x2 x1).
Proof. exact (MK_COMB (@lem1335881) (@lem1335880 x1 x2 h1)). Qed.
Lemma lem1335886 (y1 : hreal) (y2 : hreal) (h1 : term124 y1 y2) : (y1 = y2) = False.
Proof. exact (@lem1335831 y1 y2 (@lem1335189 y1 y2 h1)). Qed.
Lemma lem1335887 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1335888 (y1 : hreal) (y2 : hreal) (h1 : term124 y1 y2) : (term191 y1 y2) = (@COND (prod hreal hreal) False).
Proof. exact (MK_COMB (@lem1335887) (@lem1335886 y1 y2 h1)). Qed.
Lemma lem1335889 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem1335890 (y1 : hreal) (y2 : hreal) (h1 : term124 y1 y2) : (term193 y1 y2) = term219.
Proof. exact (MK_COMB (@lem1335888 y1 y2 h1) (@lem1335889)). Qed.
Lemma lem1335899 (y2 : hreal) (y1 : hreal) : (term211 y2 y1) = (term211 y2 y1).
Proof. exact (eq_refl (term211 y2 y1)). Qed.
Lemma lem1335900 (y1 : hreal) (y2 : hreal) (h1 : term124 y1 y2) : (term129 y2 y1) = (term220 y2 y1).
Proof. exact (MK_COMB (@lem1335890 y1 y2 h1) (@lem1335899 y2 y1)). Qed.
Lemma lem1335902 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1335903 (t1 : prod hreal hreal) (t2 : prod hreal hreal) : (@COND (prod hreal hreal) False t1 t2) = t2.
Proof. exact (@lem1335902 (prod hreal hreal) t1 t2). Qed.
Lemma lem1335904 (y2 : hreal) (y1 : hreal) : (term220 y2 y1) = (term211 y2 y1).
Proof. exact (@lem1335903 term192 (term211 y2 y1)). Qed.
Lemma lem1335913 (y1 : hreal) (y2 : hreal) (h1 : term124 y1 y2) : (term129 y2 y1) = (term211 y2 y1).
Proof. exact (TRANS (@lem1335900 y1 y2 h1) (@lem1335904 y2 y1)). Qed.
Lemma lem1335914 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : term124 x1 x2) (h2 : term124 y1 y2) : (term187 x2 x1 y2 y1) = (term227 x2 x1 y2 y1).
Proof. exact (MK_COMB (@lem1335882 x1 x2 h1) (@lem1335913 y1 y2 h2)). Qed.
Lemma lem1335915 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term183 x1 y2 y1 x2) = (term183 x1 y2 y1 x2).
Proof. exact (eq_refl (term183 x1 y2 y1 x2)). Qed.
Lemma lem1335916 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : term124 x1 x2) (h2 : term124 y1 y2) : (term188 x2 x1 y2 y1) = (term228 x2 x1 y2 y1).
Proof. exact (MK_COMB (@lem1335915 x1 y2 y1 x2) (@lem1335914 x1 x2 y1 y2 h1 h2)). Qed.
Lemma lem1335921 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : term124 x1 x2) (h2 : term124 y1 y2) : (term228 x2 x1 y2 y1) = (term188 x2 x1 y2 y1).
Proof. exact (SYM (@lem1335916 x1 x2 y1 y2 h1 h2)). Qed.
Lemma lem1335929 (x : prod hreal hreal) : (treal_eq x x) = True.
Proof. exact (EQ_MP (@lem1335183 x) (@lem1335182 x)). Qed.
Lemma lem1335930 : term215 = True.
Proof. exact (@lem1335929 term192). Qed.
Lemma lem1335931 (y2 : hreal) (x2 : hreal) : (term190 y2 x2) = (term190 y2 x2).
Proof. exact (eq_refl (term190 y2 x2)). Qed.
Lemma lem1335932 (y2 : hreal) (x2 : hreal) : (term216 y2 x2) = (term229 y2 x2).
Proof. exact (MK_COMB (@lem1335931 y2 x2) (@lem1335930)). Qed.
Lemma lem1335936 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1335937 (y2 : hreal) (x2 : hreal) : (term229 y2 x2) = True.
Proof. exact (@lem1335936 ((hreal_add x2 y2) = (hreal_add y2 x2))). Qed.
Lemma lem1335938 (y2 : hreal) (x2 : hreal) : (term216 y2 x2) = True.
Proof. exact (TRANS (@lem1335932 y2 x2) (@lem1335937 y2 x2)). Qed.
Lemma lem1335939 (y2 : hreal) (x2 : hreal) : True = (term216 y2 x2).
Proof. exact (SYM (@lem1335938 y2 x2)). Qed.
Lemma lem1335940 (y2 : hreal) (x2 : hreal) : term216 y2 x2.
Proof. exact (EQ_MP (@lem1335939 y2 x2) (@lem0)). Qed.
Lemma lem1336003 (y2 : hreal) (y1 : hreal) (x2 : hreal) (h1 : (hreal_add x2 y2) = (hreal_add y1 x2)) : (hreal_add x2 y2) = (hreal_add y1 x2).
Proof. exact (h1). Qed.
Lemma lem1336005 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1335178 y x) (@lem1335177 x y)). Qed.
Lemma lem1336006 (x2 : hreal) (y1 : hreal) : (hreal_add y1 x2) = (hreal_add x2 y1).
Proof. exact (@lem1336005 x2 y1). Qed.
Lemma lem1336007 (x2 : hreal) (y2 : hreal) : (term189 x2 y2) = (term189 x2 y2).
Proof. exact (eq_refl (term189 x2 y2)). Qed.
Lemma lem1336008 (y2 : hreal) (x2 : hreal) (y1 : hreal) : ((hreal_add x2 y2) = (hreal_add y1 x2)) = ((hreal_add x2 y2) = (hreal_add x2 y1)).
Proof. exact (MK_COMB (@lem1336007 x2 y2) (@lem1336006 x2 y1)). Qed.
Lemma lem1336009 (y2 : hreal) (y1 : hreal) (x2 : hreal) (h1 : (hreal_add x2 y2) = (hreal_add y1 x2)) : (hreal_add x2 y2) = (hreal_add x2 y1).
Proof. exact (EQ_MP (@lem1336008 y2 x2 y1) (@lem1336003 y2 y1 x2 h1)). Qed.
Lemma lem1336010 (x1 : hreal) (y2 : hreal) (x2 : hreal) (h1 : (hreal_add x1 y2) = (hreal_add y2 x2)) : (hreal_add x1 y2) = (hreal_add y2 x2).
Proof. exact (h1). Qed.
Lemma lem1336012 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1335178 y x) (@lem1335177 x y)). Qed.
Lemma lem1336013 (x2 : hreal) (y2 : hreal) : (hreal_add y2 x2) = (hreal_add x2 y2).
Proof. exact (@lem1336012 x2 y2). Qed.
Lemma lem1336014 (x1 : hreal) (y2 : hreal) : (term189 x1 y2) = (term189 x1 y2).
Proof. exact (eq_refl (term189 x1 y2)). Qed.
Lemma lem1336015 (x1 : hreal) (x2 : hreal) (y2 : hreal) : ((hreal_add x1 y2) = (hreal_add y2 x2)) = ((hreal_add x1 y2) = (hreal_add x2 y2)).
Proof. exact (MK_COMB (@lem1336014 x1 y2) (@lem1336013 x2 y2)). Qed.
Lemma lem1336016 (x1 : hreal) (y2 : hreal) (x2 : hreal) (h1 : (hreal_add x1 y2) = (hreal_add y2 x2)) : (hreal_add x1 y2) = (hreal_add x2 y2).
Proof. exact (EQ_MP (@lem1336015 x1 x2 y2) (@lem1336010 x1 y2 x2 h1)). Qed.
Lemma lem1336017 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) (h1 : (hreal_add x1 y2) = (hreal_add y1 x2)) : (hreal_add x1 y2) = (hreal_add y1 x2).
Proof. exact (h1). Qed.
Lemma lem1336019 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1335178 y x) (@lem1335177 x y)). Qed.
Lemma lem1336020 (x2 : hreal) (y1 : hreal) : (hreal_add y1 x2) = (hreal_add x2 y1).
Proof. exact (@lem1336019 x2 y1). Qed.
Lemma lem1336021 (x1 : hreal) (y2 : hreal) : (term189 x1 y2) = (term189 x1 y2).
Proof. exact (eq_refl (term189 x1 y2)). Qed.
Lemma lem1336022 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : ((hreal_add x1 y2) = (hreal_add y1 x2)) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (MK_COMB (@lem1336021 x1 y2) (@lem1336020 x2 y1)). Qed.
Lemma lem1336023 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) (h1 : (hreal_add x1 y2) = (hreal_add y1 x2)) : (hreal_add x1 y2) = (hreal_add x2 y1).
Proof. exact (EQ_MP (@lem1336022 x1 y2 x2 y1) (@lem1336017 x1 y2 y1 x2 h1)). Qed.
Lemma lem1336031 (m : hreal) (n : hreal) (p : hreal) : ((hreal_add m n) = (hreal_add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1335172 m n p) (@lem1335171 m n p)). Qed.
Lemma lem1336032 (x2 : hreal) (y2 : hreal) (y1 : hreal) : ((hreal_add x2 y2) = (hreal_add x2 y1)) = (y2 = y1).
Proof. exact (@lem1336031 x2 y2 y1). Qed.
Lemma lem1336035 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1336036 (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term230 y2 x2 y1) = (term231 y2 y1).
Proof. exact (MK_COMB (@lem1336035) (@lem1336032 x2 y2 y1)). Qed.
Lemma lem1336045 (y2 : hreal) (y1 : hreal) : (term221 y2 y1) = (term221 y2 y1).
Proof. exact (eq_refl (term221 y2 y1)). Qed.
Lemma lem1336046 (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term232 x2 y2 y1) = (term233 y2 y1).
Proof. exact (MK_COMB (@lem1336036 x2 y2 y1) (@lem1336045 y2 y1)). Qed.
Lemma lem1336051 (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term233 y2 y1) = (term232 x2 y2 y1).
Proof. exact (SYM (@lem1336046 x2 y2 y1)). Qed.
Lemma lem1336057 (p : hreal) (m : hreal) (n : hreal) : ((hreal_add m p) = (hreal_add n p)) = (m = n).
Proof. exact (EQ_MP (@lem1335163 p m n) (@lem1335162 m n p)). Qed.
Lemma lem1336058 (y2 : hreal) (x1 : hreal) (x2 : hreal) : ((hreal_add x1 y2) = (hreal_add x2 y2)) = (x1 = x2).
Proof. exact (@lem1336057 y2 x1 x2). Qed.
Lemma lem1336061 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1336062 (y2 : hreal) (x1 : hreal) (x2 : hreal) : (term234 x1 x2 y2) = (term231 x1 x2).
Proof. exact (MK_COMB (@lem1336061) (@lem1336058 y2 x1 x2)). Qed.
Lemma lem1336071 (x2 : hreal) (x1 : hreal) : (term225 x2 x1) = (term225 x2 x1).
Proof. exact (eq_refl (term225 x2 x1)). Qed.
Lemma lem1336072 (y2 : hreal) (x2 : hreal) (x1 : hreal) : (term235 y2 x2 x1) = (term236 x2 x1).
Proof. exact (MK_COMB (@lem1336062 y2 x1 x2) (@lem1336071 x2 x1)). Qed.
Lemma lem1336077 (y2 : hreal) (x2 : hreal) (x1 : hreal) : (term236 x2 x1) = (term235 y2 x2 x1).
Proof. exact (SYM (@lem1336072 y2 x2 x1)). Qed.
Lemma lem1336108 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) (h1 : (hreal_add x1 y2) = (hreal_add x2 y1)) : (hreal_add x1 y2) = (hreal_add x2 y1).
Proof. exact (h1). Qed.
Lemma lem1336109 (x : prod hreal hreal) : term36 x.
Proof. exact (@lem1326193 x). Qed.
Lemma lem1336110 (x : prod hreal hreal) : (term36 x) = (treal_eq x x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1336111 (x : prod hreal hreal) : treal_eq x x.
Proof. exact (EQ_MP (@lem1336110 x) (@lem1336109 x)). Qed.
Lemma lem1336112 (x : prod hreal hreal) : (treal_eq x x) = ((treal_eq x x) = True).
Proof. exact (@lem7 (treal_eq x x)). Qed.
Lemma lem1336114 (x : hreal) : term237 x.
Proof. exact (@lem1319042 x). Qed.
Lemma lem1336115 (x : hreal) : (term237 x) = (hreal_le x x).
Proof. exact (eq_refl (term237 x)). Qed.
Lemma lem1336116 (x : hreal) : hreal_le x x.
Proof. exact (EQ_MP (@lem1336115 x) (@lem1336114 x)). Qed.
Lemma lem1336117 (x : hreal) : (hreal_le x x) = ((hreal_le x x) = True).
Proof. exact (@lem7 (hreal_le x x)). Qed.
Lemma lem1336137 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : y2 = y1.
Proof. exact (h1). Qed.
Lemma lem1336138 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1336139 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (hreal_le y2) = (hreal_le y1).
Proof. exact (MK_COMB (@lem1336138) (@lem1336137 y2 y1 h1)). Qed.
Lemma lem1336140 (y1 : hreal) : y1 = y1.
Proof. exact (eq_refl y1). Qed.
Lemma lem1336141 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (hreal_le y2 y1) = (hreal_le y1 y1).
Proof. exact (MK_COMB (@lem1336139 y2 y1 h1) (@lem1336140 y1)). Qed.
Lemma lem1336143 (x : hreal) : (hreal_le x x) = True.
Proof. exact (EQ_MP (@lem1336117 x) (@lem1336116 x)). Qed.
Lemma lem1336144 (y1 : hreal) : (hreal_le y1 y1) = True.
Proof. exact (@lem1336143 y1). Qed.
Lemma lem1336145 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (hreal_le y2 y1) = True.
Proof. exact (TRANS (@lem1336141 y2 y1 h1) (@lem1336144 y1)). Qed.
Lemma lem1336146 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1336147 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term195 y2 y1) = (@COND (prod hreal hreal) True).
Proof. exact (MK_COMB (@lem1336146) (@lem1336145 y2 y1 h1)). Qed.
Lemma lem1336155 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : y2 = y1.
Proof. exact (h1). Qed.
Lemma lem1336156 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1336157 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (hreal_add y2) = (hreal_add y1).
Proof. exact (MK_COMB (@lem1336156) (@lem1336155 y2 y1 h1)). Qed.
Lemma lem1336158 (d : hreal) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1336159 (d : hreal) (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (hreal_add y2 d) = (hreal_add y1 d).
Proof. exact (MK_COMB (@lem1336157 y2 y1 h1) (@lem1336158 d)). Qed.
Lemma lem1336160 (y1 : hreal) : (@eq hreal y1) = (@eq hreal y1).
Proof. exact (eq_refl (@eq hreal y1)). Qed.
Lemma lem1336161 (d : hreal) (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (y1 = (hreal_add y2 d)) = (y1 = (hreal_add y1 d)).
Proof. exact (MK_COMB (@lem1336160 y1) (@lem1336159 d y2 y1 h1)). Qed.
Lemma lem1336164 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term197 y1 y2) = (term21 y1).
Proof. exact (fun_ext (fun d : hreal => @lem1336161 d y2 y1 h1)). Qed.
Lemma lem1336165 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1336166 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term198 y1 y2) = (term199 y1).
Proof. exact (MK_COMB (@lem1336165) (@lem1336164 y2 y1 h1)). Qed.
Lemma lem1336168 (x : hreal) : (term199 x) = term22.
Proof. exact (@lem1334796 x (@lem1334851 x)). Qed.
Lemma lem1336169 (y1 : hreal) : (term199 y1) = term22.
Proof. exact (@lem1336168 y1). Qed.
Lemma lem1336170 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term198 y1 y2) = term22.
Proof. exact (TRANS (@lem1336166 y2 y1 h1) (@lem1336169 y1)). Qed.
Lemma lem1336171 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1336172 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term200 y1 y2) = term238.
Proof. exact (MK_COMB (@lem1336171) (@lem1336170 y2 y1 h1)). Qed.
Lemma lem1336174 : term238 = term22.
Proof. exact (EQ_MP (@lem1321215) (@lem1309022)). Qed.
Lemma lem1336175 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term200 y1 y2) = term22.
Proof. exact (TRANS (@lem1336172 y2 y1 h1) (@lem1336174)). Qed.
Lemma lem1336176 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1336177 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term202 y1 y2) = term208.
Proof. exact (MK_COMB (@lem1336176) (@lem1336175 y2 y1 h1)). Qed.
Lemma lem1336178 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1336179 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term204 y1 y2) = term192.
Proof. exact (MK_COMB (@lem1336177 y2 y1 h1) (@lem1336178)). Qed.
Lemma lem1336180 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term206 y1 y2) = term194.
Proof. exact (MK_COMB (@lem1336147 y2 y1 h1) (@lem1336179 y2 y1 h1)). Qed.
Lemma lem1336188 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : y2 = y1.
Proof. exact (h1). Qed.
Lemma lem1336189 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1336190 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (@eq hreal y2) = (@eq hreal y1).
Proof. exact (MK_COMB (@lem1336189) (@lem1336188 y2 y1 h1)). Qed.
Lemma lem1336191 (y1 : hreal) (d : hreal) : (hreal_add y1 d) = (hreal_add y1 d).
Proof. exact (eq_refl (hreal_add y1 d)). Qed.
Lemma lem1336192 (d : hreal) (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (y2 = (hreal_add y1 d)) = (y1 = (hreal_add y1 d)).
Proof. exact (MK_COMB (@lem1336190 y2 y1 h1) (@lem1336191 y1 d)). Qed.
Lemma lem1336195 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term197 y2 y1) = (term21 y1).
Proof. exact (fun_ext (fun d : hreal => @lem1336192 d y2 y1 h1)). Qed.
Lemma lem1336196 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1336197 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term198 y2 y1) = (term199 y1).
Proof. exact (MK_COMB (@lem1336196) (@lem1336195 y2 y1 h1)). Qed.
Lemma lem1336199 (x : hreal) : (term199 x) = term22.
Proof. exact (@lem1334796 x (@lem1334851 x)). Qed.
Lemma lem1336200 (y1 : hreal) : (term199 y1) = term22.
Proof. exact (@lem1336199 y1). Qed.
Lemma lem1336201 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term198 y2 y1) = term22.
Proof. exact (TRANS (@lem1336197 y2 y1 h1) (@lem1336200 y1)). Qed.
Lemma lem1336202 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1336203 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term200 y2 y1) = term238.
Proof. exact (MK_COMB (@lem1336202) (@lem1336201 y2 y1 h1)). Qed.
Lemma lem1336205 : term238 = term22.
Proof. exact (EQ_MP (@lem1321215) (@lem1309022)). Qed.
Lemma lem1336206 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term200 y2 y1) = term22.
Proof. exact (TRANS (@lem1336203 y2 y1 h1) (@lem1336205)). Qed.
Lemma lem1336207 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem1336208 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term209 y2 y1) = term192.
Proof. exact (MK_COMB (@lem1336207) (@lem1336206 y2 y1 h1)). Qed.
Lemma lem1336209 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term211 y2 y1) = term239.
Proof. exact (MK_COMB (@lem1336180 y2 y1 h1) (@lem1336208 y2 y1 h1)). Qed.
Lemma lem1336211 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1336212 (t2 : prod hreal hreal) (t1 : prod hreal hreal) : (@COND (prod hreal hreal) True t1 t2) = t1.
Proof. exact (@lem1336211 (prod hreal hreal) t2 t1). Qed.
Lemma lem1336213 : term239 = term192.
Proof. exact (@lem1336212 term192 term192). Qed.
Lemma lem1336214 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term211 y2 y1) = term192.
Proof. exact (TRANS (@lem1336209 y2 y1 h1) (@lem1336213)). Qed.
Lemma lem1336215 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem1336216 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term221 y2 y1) = term215.
Proof. exact (MK_COMB (@lem1336215) (@lem1336214 y2 y1 h1)). Qed.
Lemma lem1336218 (x : prod hreal hreal) : (treal_eq x x) = True.
Proof. exact (EQ_MP (@lem1336112 x) (@lem1336111 x)). Qed.
Lemma lem1336219 : term215 = True.
Proof. exact (@lem1336218 term192). Qed.
Lemma lem1336220 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : (term221 y2 y1) = True.
Proof. exact (TRANS (@lem1336216 y2 y1 h1) (@lem1336219)). Qed.
Lemma lem1336221 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : True = (term221 y2 y1).
Proof. exact (SYM (@lem1336220 y2 y1 h1)). Qed.
Lemma lem1336222 (y2 : hreal) (y1 : hreal) (h1 : y2 = y1) : term221 y2 y1.
Proof. exact (EQ_MP (@lem1336221 y2 y1 h1) (@lem0)). Qed.
Lemma lem1336223 (x : prod hreal hreal) : term36 x.
Proof. exact (@lem1326193 x). Qed.
Lemma lem1336224 (x : prod hreal hreal) : (term36 x) = (treal_eq x x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1336225 (x : prod hreal hreal) : treal_eq x x.
Proof. exact (EQ_MP (@lem1336224 x) (@lem1336223 x)). Qed.
Lemma lem1336226 (x : prod hreal hreal) : (treal_eq x x) = ((treal_eq x x) = True).
Proof. exact (@lem7 (treal_eq x x)). Qed.
Lemma lem1336228 (x : hreal) : term237 x.
Proof. exact (@lem1319042 x). Qed.
Lemma lem1336229 (x : hreal) : (term237 x) = (hreal_le x x).
Proof. exact (eq_refl (term237 x)). Qed.
Lemma lem1336230 (x : hreal) : hreal_le x x.
Proof. exact (EQ_MP (@lem1336229 x) (@lem1336228 x)). Qed.
Lemma lem1336231 (x : hreal) : (hreal_le x x) = ((hreal_le x x) = True).
Proof. exact (@lem7 (hreal_le x x)). Qed.
Lemma lem1336251 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : x1 = x2.
Proof. exact (h1). Qed.
Lemma lem1336252 (x2 : hreal) : (hreal_le x2) = (hreal_le x2).
Proof. exact (eq_refl (hreal_le x2)). Qed.
Lemma lem1336253 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (hreal_le x2 x1) = (hreal_le x2 x2).
Proof. exact (MK_COMB (@lem1336252 x2) (@lem1336251 x1 x2 h1)). Qed.
Lemma lem1336255 (x : hreal) : (hreal_le x x) = True.
Proof. exact (EQ_MP (@lem1336231 x) (@lem1336230 x)). Qed.
Lemma lem1336256 (x2 : hreal) : (hreal_le x2 x2) = True.
Proof. exact (@lem1336255 x2). Qed.
Lemma lem1336257 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (hreal_le x2 x1) = True.
Proof. exact (TRANS (@lem1336253 x1 x2 h1) (@lem1336256 x2)). Qed.
Lemma lem1336258 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1336259 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term195 x2 x1) = (@COND (prod hreal hreal) True).
Proof. exact (MK_COMB (@lem1336258) (@lem1336257 x1 x2 h1)). Qed.
Lemma lem1336267 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : x1 = x2.
Proof. exact (h1). Qed.
Lemma lem1336268 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1336269 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (@eq hreal x1) = (@eq hreal x2).
Proof. exact (MK_COMB (@lem1336268) (@lem1336267 x1 x2 h1)). Qed.
Lemma lem1336270 (x2 : hreal) (d : hreal) : (hreal_add x2 d) = (hreal_add x2 d).
Proof. exact (eq_refl (hreal_add x2 d)). Qed.
Lemma lem1336271 (d : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (x1 = (hreal_add x2 d)) = (x2 = (hreal_add x2 d)).
Proof. exact (MK_COMB (@lem1336269 x1 x2 h1) (@lem1336270 x2 d)). Qed.
Lemma lem1336274 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term197 x1 x2) = (term21 x2).
Proof. exact (fun_ext (fun d : hreal => @lem1336271 d x1 x2 h1)). Qed.
Lemma lem1336275 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1336276 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term198 x1 x2) = (term199 x2).
Proof. exact (MK_COMB (@lem1336275) (@lem1336274 x1 x2 h1)). Qed.
Lemma lem1336278 (x : hreal) : (term199 x) = term22.
Proof. exact (@lem1334796 x (@lem1334851 x)). Qed.
Lemma lem1336279 (x2 : hreal) : (term199 x2) = term22.
Proof. exact (@lem1336278 x2). Qed.
Lemma lem1336280 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term198 x1 x2) = term22.
Proof. exact (TRANS (@lem1336276 x1 x2 h1) (@lem1336279 x2)). Qed.
Lemma lem1336281 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1336282 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term200 x1 x2) = term238.
Proof. exact (MK_COMB (@lem1336281) (@lem1336280 x1 x2 h1)). Qed.
Lemma lem1336284 : term238 = term22.
Proof. exact (EQ_MP (@lem1321215) (@lem1309022)). Qed.
Lemma lem1336285 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term200 x1 x2) = term22.
Proof. exact (TRANS (@lem1336282 x1 x2 h1) (@lem1336284)). Qed.
Lemma lem1336286 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1336287 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term202 x1 x2) = term208.
Proof. exact (MK_COMB (@lem1336286) (@lem1336285 x1 x2 h1)). Qed.
Lemma lem1336288 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1336289 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term204 x1 x2) = term192.
Proof. exact (MK_COMB (@lem1336287 x1 x2 h1) (@lem1336288)). Qed.
Lemma lem1336290 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term206 x1 x2) = term194.
Proof. exact (MK_COMB (@lem1336259 x1 x2 h1) (@lem1336289 x1 x2 h1)). Qed.
Lemma lem1336298 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : x1 = x2.
Proof. exact (h1). Qed.
Lemma lem1336299 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1336300 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (hreal_add x1) = (hreal_add x2).
Proof. exact (MK_COMB (@lem1336299) (@lem1336298 x1 x2 h1)). Qed.
Lemma lem1336301 (d : hreal) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1336302 (d : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (hreal_add x1 d) = (hreal_add x2 d).
Proof. exact (MK_COMB (@lem1336300 x1 x2 h1) (@lem1336301 d)). Qed.
Lemma lem1336303 (x2 : hreal) : (@eq hreal x2) = (@eq hreal x2).
Proof. exact (eq_refl (@eq hreal x2)). Qed.
Lemma lem1336304 (d : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (x2 = (hreal_add x1 d)) = (x2 = (hreal_add x2 d)).
Proof. exact (MK_COMB (@lem1336303 x2) (@lem1336302 d x1 x2 h1)). Qed.
Lemma lem1336307 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term197 x2 x1) = (term21 x2).
Proof. exact (fun_ext (fun d : hreal => @lem1336304 d x1 x2 h1)). Qed.
Lemma lem1336308 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1336309 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term198 x2 x1) = (term199 x2).
Proof. exact (MK_COMB (@lem1336308) (@lem1336307 x1 x2 h1)). Qed.
Lemma lem1336311 (x : hreal) : (term199 x) = term22.
Proof. exact (@lem1334796 x (@lem1334851 x)). Qed.
Lemma lem1336312 (x2 : hreal) : (term199 x2) = term22.
Proof. exact (@lem1336311 x2). Qed.
Lemma lem1336313 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term198 x2 x1) = term22.
Proof. exact (TRANS (@lem1336309 x1 x2 h1) (@lem1336312 x2)). Qed.
Lemma lem1336314 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1336315 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term200 x2 x1) = term238.
Proof. exact (MK_COMB (@lem1336314) (@lem1336313 x1 x2 h1)). Qed.
Lemma lem1336317 : term238 = term22.
Proof. exact (EQ_MP (@lem1321215) (@lem1309022)). Qed.
Lemma lem1336318 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term200 x2 x1) = term22.
Proof. exact (TRANS (@lem1336315 x1 x2 h1) (@lem1336317)). Qed.
Lemma lem1336319 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem1336320 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term209 x2 x1) = term192.
Proof. exact (MK_COMB (@lem1336319) (@lem1336318 x1 x2 h1)). Qed.
Lemma lem1336321 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term211 x2 x1) = term239.
Proof. exact (MK_COMB (@lem1336290 x1 x2 h1) (@lem1336320 x1 x2 h1)). Qed.
Lemma lem1336323 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1336324 (t2 : prod hreal hreal) (t1 : prod hreal hreal) : (@COND (prod hreal hreal) True t1 t2) = t1.
Proof. exact (@lem1336323 (prod hreal hreal) t2 t1). Qed.
Lemma lem1336325 : term239 = term192.
Proof. exact (@lem1336324 term192 term192). Qed.
Lemma lem1336326 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term211 x2 x1) = term192.
Proof. exact (TRANS (@lem1336321 x1 x2 h1) (@lem1336325)). Qed.
Lemma lem1336327 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1336328 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term224 x2 x1) = term214.
Proof. exact (MK_COMB (@lem1336327) (@lem1336326 x1 x2 h1)). Qed.
Lemma lem1336329 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem1336330 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term225 x2 x1) = term215.
Proof. exact (MK_COMB (@lem1336328 x1 x2 h1) (@lem1336329)). Qed.
Lemma lem1336332 (x : prod hreal hreal) : (treal_eq x x) = True.
Proof. exact (EQ_MP (@lem1336226 x) (@lem1336225 x)). Qed.
Lemma lem1336333 : term215 = True.
Proof. exact (@lem1336332 term192). Qed.
Lemma lem1336334 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : (term225 x2 x1) = True.
Proof. exact (TRANS (@lem1336330 x1 x2 h1) (@lem1336333)). Qed.
Lemma lem1336335 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : True = (term225 x2 x1).
Proof. exact (SYM (@lem1336334 x1 x2 h1)). Qed.
Lemma lem1336336 (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : term225 x2 x1.
Proof. exact (EQ_MP (@lem1336335 x1 x2 h1) (@lem0)). Qed.
Lemma lem1336431 (x2 : hreal) (x1 : hreal) : (hreal_le x2 x1) = ((hreal_le x2 x1) = True).
Proof. exact (@lem7 (hreal_le x2 x1)). Qed.
Lemma lem1336434 (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : (hreal_le x2 x1) = True.
Proof. exact (EQ_MP (@lem1336431 x2 x1) (@lem1335154 x2 x1 h1)). Qed.
Lemma lem1336435 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1336436 (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : (term195 x2 x1) = (@COND (prod hreal hreal) True).
Proof. exact (MK_COMB (@lem1336435) (@lem1336434 x2 x1 h1)). Qed.
Lemma lem1336441 (x1 : hreal) (x2 : hreal) : (term204 x1 x2) = (term204 x1 x2).
Proof. exact (eq_refl (term204 x1 x2)). Qed.
Lemma lem1336442 (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : (term206 x1 x2) = (term240 x1 x2).
Proof. exact (MK_COMB (@lem1336436 x2 x1 h1) (@lem1336441 x1 x2)). Qed.
Lemma lem1336447 (x2 : hreal) (x1 : hreal) : (term209 x2 x1) = (term209 x2 x1).
Proof. exact (eq_refl (term209 x2 x1)). Qed.
Lemma lem1336448 (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : (term211 x2 x1) = (term241 x2 x1).
Proof. exact (MK_COMB (@lem1336442 x2 x1 h1) (@lem1336447 x2 x1)). Qed.
Lemma lem1336450 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1336451 (t2 : prod hreal hreal) (t1 : prod hreal hreal) : (@COND (prod hreal hreal) True t1 t2) = t1.
Proof. exact (@lem1336450 (prod hreal hreal) t2 t1). Qed.
Lemma lem1336452 (x1 : hreal) (x2 : hreal) : (term241 x2 x1) = (term204 x1 x2).
Proof. exact (@lem1336451 (term209 x2 x1) (term204 x1 x2)). Qed.
Lemma lem1336457 (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : (term211 x2 x1) = (term204 x1 x2).
Proof. exact (TRANS (@lem1336448 x2 x1 h1) (@lem1336452 x1 x2)). Qed.
Lemma lem1336458 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1336459 (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : (term224 x2 x1) = (term242 x1 x2).
Proof. exact (MK_COMB (@lem1336458) (@lem1336457 x2 x1 h1)). Qed.
Lemma lem1336468 (y2 : hreal) (y1 : hreal) : (term211 y2 y1) = (term211 y2 y1).
Proof. exact (eq_refl (term211 y2 y1)). Qed.
Lemma lem1336469 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : (term227 x2 x1 y2 y1) = (term243 x1 x2 y2 y1).
Proof. exact (MK_COMB (@lem1336459 x2 x1 h1) (@lem1336468 y2 y1)). Qed.
Lemma lem1336470 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : (term243 x1 x2 y2 y1) = (term227 x2 x1 y2 y1).
Proof. exact (SYM (@lem1336469 y2 y1 x2 x1 h1)). Qed.
Lemma lem1336497 (x2 : hreal) (x1 : hreal) : term244 x2 x1.
Proof. exact (@lem82 (hreal_le x2 x1)). Qed.
Lemma lem1336500 (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : (hreal_le x2 x1) = False.
Proof. exact (@lem1336497 x2 x1 (@lem1335155 x2 x1 h1)). Qed.
Lemma lem1336501 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1336502 (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : (term195 x2 x1) = (@COND (prod hreal hreal) False).
Proof. exact (MK_COMB (@lem1336501) (@lem1336500 x2 x1 h1)). Qed.
Lemma lem1336507 (x1 : hreal) (x2 : hreal) : (term204 x1 x2) = (term204 x1 x2).
Proof. exact (eq_refl (term204 x1 x2)). Qed.
Lemma lem1336508 (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : (term206 x1 x2) = (term245 x1 x2).
Proof. exact (MK_COMB (@lem1336502 x2 x1 h1) (@lem1336507 x1 x2)). Qed.
Lemma lem1336513 (x2 : hreal) (x1 : hreal) : (term209 x2 x1) = (term209 x2 x1).
Proof. exact (eq_refl (term209 x2 x1)). Qed.
Lemma lem1336514 (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : (term211 x2 x1) = (term246 x2 x1).
Proof. exact (MK_COMB (@lem1336508 x2 x1 h1) (@lem1336513 x2 x1)). Qed.
Lemma lem1336516 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1336517 (t1 : prod hreal hreal) (t2 : prod hreal hreal) : (@COND (prod hreal hreal) False t1 t2) = t2.
Proof. exact (@lem1336516 (prod hreal hreal) t1 t2). Qed.
Lemma lem1336518 (x2 : hreal) (x1 : hreal) : (term246 x2 x1) = (term209 x2 x1).
Proof. exact (@lem1336517 (term204 x1 x2) (term209 x2 x1)). Qed.
Lemma lem1336523 (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : (term211 x2 x1) = (term209 x2 x1).
Proof. exact (TRANS (@lem1336514 x2 x1 h1) (@lem1336518 x2 x1)). Qed.
Lemma lem1336524 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1336525 (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : (term224 x2 x1) = (term247 x2 x1).
Proof. exact (MK_COMB (@lem1336524) (@lem1336523 x2 x1 h1)). Qed.
Lemma lem1336534 (y2 : hreal) (y1 : hreal) : (term211 y2 y1) = (term211 y2 y1).
Proof. exact (eq_refl (term211 y2 y1)). Qed.
Lemma lem1336535 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : (term227 x2 x1 y2 y1) = (term248 x2 x1 y2 y1).
Proof. exact (MK_COMB (@lem1336525 x2 x1 h1) (@lem1336534 y2 y1)). Qed.
Lemma lem1336536 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : (term248 x2 x1 y2 y1) = (term227 x2 x1 y2 y1).
Proof. exact (SYM (@lem1336535 y2 y1 x2 x1 h1)). Qed.
Lemma lem1336538 (y : hreal) (x : hreal) : term99 y x.
Proof. exact (EQ_MP (@lem1335149 y x) (@lem1335148 x y)). Qed.
Lemma lem1336539 (x1 : hreal) (x2 : hreal) : term99 x1 x2.
Proof. exact (@lem1336538 x1 x2). Qed.
Lemma lem1336540 (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : term249 x1 x2.
Proof. exact (@lem1336539 x1 x2 (@lem1335154 x2 x1 h1)). Qed.
Lemma lem1336541 (P : hreal -> Prop) : term250 P.
Proof. exact (@lem9396 hreal P). Qed.
Lemma lem1336542 (x1 : hreal) (x2 : hreal) : term251 x1 x2.
Proof. exact (@lem1336541 (term197 x1 x2)). Qed.
Lemma lem1336543 (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : term252 x1 x2.
Proof. exact (@lem1336542 x1 x2 (@lem1336540 x2 x1 h1)). Qed.
Lemma lem1336544 (x1 : hreal) (x2 : hreal) : (term252 x1 x2) = (x1 = (term253 x1 x2)).
Proof. exact (eq_refl (term252 x1 x2)). Qed.
Lemma lem1336547 (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : x1 = (term253 x1 x2).
Proof. exact (EQ_MP (@lem1336544 x1 x2) (@lem1336543 x2 x1 h1)). Qed.
Lemma lem1336548 (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term254 x2 y2 y1) = (term254 x2 y2 y1).
Proof. exact (eq_refl (term254 x2 y2 y1)). Qed.
Lemma lem1336549 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : (term255 x2 y2 y1 x1) = (term256 y2 y1 x1 x2).
Proof. exact (MK_COMB (@lem1336548 x2 y2 y1) (@lem1336547 x2 x1 h1)). Qed.
Lemma lem1336550 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term256 y2 y1 x1 x2) = (term257 x1 x2 y2 y1).
Proof. exact (eq_refl (term256 y2 y1 x1 x2)). Qed.
Lemma lem1336551 (x2 : hreal) (y2 : hreal) (y1 : hreal) (x1 : hreal) : (term258 x2 y2 y1 x1) = (term258 x2 y2 y1 x1).
Proof. exact (eq_refl (term258 x2 y2 y1 x1)). Qed.
Lemma lem1336552 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : ((term255 x2 y2 y1 x1) = (term256 y2 y1 x1 x2)) = ((term255 x2 y2 y1 x1) = (term257 x1 x2 y2 y1)).
Proof. exact (MK_COMB (@lem1336551 x2 y2 y1 x1) (@lem1336550 x1 x2 y2 y1)). Qed.
Lemma lem1336553 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term255 x2 y2 y1 x1) = (term259 x1 x2 y2 y1).
Proof. exact (eq_refl (term255 x2 y2 y1 x1)). Qed.
Lemma lem1336554 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1336555 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term258 x2 y2 y1 x1) = (term260 x1 x2 y2 y1).
Proof. exact (MK_COMB (@lem1336554) (@lem1336553 x1 x2 y2 y1)). Qed.
Lemma lem1336556 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term257 x1 x2 y2 y1) = (term257 x1 x2 y2 y1).
Proof. exact (eq_refl (term257 x1 x2 y2 y1)). Qed.
Lemma lem1336557 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : ((term255 x2 y2 y1 x1) = (term257 x1 x2 y2 y1)) = ((term259 x1 x2 y2 y1) = (term257 x1 x2 y2 y1)).
Proof. exact (MK_COMB (@lem1336555 x1 x2 y2 y1) (@lem1336556 x1 x2 y2 y1)). Qed.
Lemma lem1336558 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : ((term255 x2 y2 y1 x1) = (term256 y2 y1 x1 x2)) = ((term259 x1 x2 y2 y1) = (term257 x1 x2 y2 y1)).
Proof. exact (TRANS (@lem1336552 x1 x2 y2 y1) (@lem1336557 x1 x2 y2 y1)). Qed.
Lemma lem1336559 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : (term259 x1 x2 y2 y1) = (term257 x1 x2 y2 y1).
Proof. exact (EQ_MP (@lem1336558 x1 x2 y2 y1) (@lem1336549 y2 y1 x2 x1 h1)). Qed.
Lemma lem1336560 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : (term257 x1 x2 y2 y1) = (term259 x1 x2 y2 y1).
Proof. exact (SYM (@lem1336559 y2 y1 x2 x1 h1)). Qed.
Lemma lem1336570 (x : hreal) (y : hreal) (z : hreal) : (term80 x y z) = (term79 x y z).
Proof. exact (EQ_MP (@lem1335134 x y z) (@lem1335133 x y z)). Qed.
Lemma lem1336571 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term261 x1 x2 y2) = (term262 x1 x2 y2).
Proof. exact (@lem1336570 x2 (term198 x1 x2) y2). Qed.
Lemma lem1336576 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1336577 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term263 x1 x2 y2) = (term264 x1 x2 y2).
Proof. exact (MK_COMB (@lem1336576) (@lem1336571 x1 x2 y2)). Qed.
Lemma lem1336578 (x2 : hreal) (y1 : hreal) : (hreal_add x2 y1) = (hreal_add x2 y1).
Proof. exact (eq_refl (hreal_add x2 y1)). Qed.
Lemma lem1336579 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : ((term261 x1 x2 y2) = (hreal_add x2 y1)) = ((term262 x1 x2 y2) = (hreal_add x2 y1)).
Proof. exact (MK_COMB (@lem1336577 x1 x2 y2) (@lem1336578 x2 y1)). Qed.
Lemma lem1336581 (m : hreal) (n : hreal) (p : hreal) : ((hreal_add m n) = (hreal_add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1335143 m n p) (@lem1335142 m n p)). Qed.
Lemma lem1336582 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : ((term262 x1 x2 y2) = (hreal_add x2 y1)) = ((term265 x1 x2 y2) = y1).
Proof. exact (@lem1336581 x2 (term265 x1 x2 y2) y1). Qed.
Lemma lem1336589 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : ((term261 x1 x2 y2) = (hreal_add x2 y1)) = ((term265 x1 x2 y2) = y1).
Proof. exact (TRANS (@lem1336579 x1 y2 x2 y1) (@lem1336582 x1 x2 y2 y1)). Qed.
Lemma lem1336590 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1336591 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term266 x1 y2 x2 y1) = (term267 x1 x2 y2 y1).
Proof. exact (MK_COMB (@lem1336590) (@lem1336589 x1 x2 y2 y1)). Qed.
Lemma lem1336595 (m : hreal) (n : hreal) (p : hreal) : ((hreal_add m n) = (hreal_add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1335143 m n p) (@lem1335142 m n p)). Qed.
Lemma lem1336596 (x1 : hreal) (x2 : hreal) (d : hreal) : ((term253 x1 x2) = (hreal_add x2 d)) = ((term198 x1 x2) = d).
Proof. exact (@lem1336595 x2 (term198 x1 x2) d). Qed.
Lemma lem1336603 (x1 : hreal) (x2 : hreal) : (term268 x1 x2) = (term269 x1 x2).
Proof. exact (fun_ext (fun d : hreal => @lem1336596 x1 x2 d)). Qed.
Lemma lem1336604 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1336605 (x1 : hreal) (x2 : hreal) : (term270 x1 x2) = (term271 x1 x2).
Proof. exact (MK_COMB (@lem1336604) (@lem1336603 x1 x2)). Qed.
Lemma lem1336608 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1336609 (x1 : hreal) (x2 : hreal) : (term272 x1 x2) = (term273 x1 x2).
Proof. exact (MK_COMB (@lem1336608) (@lem1336605 x1 x2)). Qed.
Lemma lem1336610 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1336611 (x1 : hreal) (x2 : hreal) : (term274 x1 x2) = (term275 x1 x2).
Proof. exact (MK_COMB (@lem1336610) (@lem1336609 x1 x2)). Qed.
Lemma lem1336612 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1336613 (x1 : hreal) (x2 : hreal) : (term276 x1 x2) = (term277 x1 x2).
Proof. exact (MK_COMB (@lem1336611 x1 x2) (@lem1336612)). Qed.
Lemma lem1336614 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1336615 (x1 : hreal) (x2 : hreal) : (term278 x1 x2) = (term279 x1 x2).
Proof. exact (MK_COMB (@lem1336614) (@lem1336613 x1 x2)). Qed.
Lemma lem1336624 (y2 : hreal) (y1 : hreal) : (term211 y2 y1) = (term211 y2 y1).
Proof. exact (eq_refl (term211 y2 y1)). Qed.
Lemma lem1336625 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term280 x1 x2 y2 y1) = (term281 x1 x2 y2 y1).
Proof. exact (MK_COMB (@lem1336615 x1 x2) (@lem1336624 y2 y1)). Qed.
Lemma lem1336626 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term257 x1 x2 y2 y1) = (term282 x1 x2 y2 y1).
Proof. exact (MK_COMB (@lem1336591 x1 x2 y2 y1) (@lem1336625 x1 x2 y2 y1)). Qed.
Lemma lem1336631 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term282 x1 x2 y2 y1) = (term257 x1 x2 y2 y1).
Proof. exact (SYM (@lem1336626 x1 x2 y2 y1)). Qed.
Lemma lem1336632 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) (h1 : (term265 x1 x2 y2) = y1) : (term265 x1 x2 y2) = y1.
Proof. exact (h1). Qed.
Lemma lem1336633 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) (h1 : (term265 x1 x2 y2) = y1) : y1 = (term265 x1 x2 y2).
Proof. exact (SYM (@lem1336632 x1 x2 y2 y1 h1)). Qed.
Lemma lem1336634 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term283 x1 x2 y2) = (term283 x1 x2 y2).
Proof. exact (eq_refl (term283 x1 x2 y2)). Qed.
Lemma lem1336635 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) (h1 : (term265 x1 x2 y2) = y1) : (term284 x1 x2 y2 y1) = (term285 x1 x2 y2).
Proof. exact (MK_COMB (@lem1336634 x1 x2 y2) (@lem1336633 x1 x2 y2 y1 h1)). Qed.
Lemma lem1336636 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term285 x1 x2 y2) = (term286 x1 x2 y2).
Proof. exact (eq_refl (term285 x1 x2 y2)). Qed.
Lemma lem1336637 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term287 x1 x2 y2 y1) = (term287 x1 x2 y2 y1).
Proof. exact (eq_refl (term287 x1 x2 y2 y1)). Qed.
Lemma lem1336638 (y1 : hreal) (x1 : hreal) (x2 : hreal) (y2 : hreal) : ((term284 x1 x2 y2 y1) = (term285 x1 x2 y2)) = ((term284 x1 x2 y2 y1) = (term286 x1 x2 y2)).
Proof. exact (MK_COMB (@lem1336637 x1 x2 y2 y1) (@lem1336636 x1 x2 y2)). Qed.
Lemma lem1336639 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term284 x1 x2 y2 y1) = (term281 x1 x2 y2 y1).
Proof. exact (eq_refl (term284 x1 x2 y2 y1)). Qed.
Lemma lem1336640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1336641 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : (term287 x1 x2 y2 y1) = (term288 x1 x2 y2 y1).
Proof. exact (MK_COMB (@lem1336640) (@lem1336639 x1 x2 y2 y1)). Qed.
Lemma lem1336642 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term286 x1 x2 y2) = (term286 x1 x2 y2).
Proof. exact (eq_refl (term286 x1 x2 y2)). Qed.
Lemma lem1336643 (y1 : hreal) (x1 : hreal) (x2 : hreal) (y2 : hreal) : ((term284 x1 x2 y2 y1) = (term286 x1 x2 y2)) = ((term281 x1 x2 y2 y1) = (term286 x1 x2 y2)).
Proof. exact (MK_COMB (@lem1336641 x1 x2 y2 y1) (@lem1336642 x1 x2 y2)). Qed.
Lemma lem1336644 (y1 : hreal) (x1 : hreal) (x2 : hreal) (y2 : hreal) : ((term284 x1 x2 y2 y1) = (term285 x1 x2 y2)) = ((term281 x1 x2 y2 y1) = (term286 x1 x2 y2)).
Proof. exact (TRANS (@lem1336638 y1 x1 x2 y2) (@lem1336643 y1 x1 x2 y2)). Qed.
Lemma lem1336645 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) (h1 : (term265 x1 x2 y2) = y1) : (term281 x1 x2 y2 y1) = (term286 x1 x2 y2).
Proof. exact (EQ_MP (@lem1336644 y1 x1 x2 y2) (@lem1336635 x1 x2 y2 y1 h1)). Qed.
Lemma lem1336646 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) (h1 : (term265 x1 x2 y2) = y1) : (term286 x1 x2 y2) = (term281 x1 x2 y2 y1).
Proof. exact (SYM (@lem1336645 x1 x2 y2 y1 h1)). Qed.
Lemma lem1336656 (y : hreal) (x : hreal) : (term104 y x) = True.
Proof. exact (EQ_MP (@lem1335107 y x) (@lem1335106 y x)). Qed.
Lemma lem1336657 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term289 x1 x2 y2) = True.
Proof. exact (@lem1336656 (term198 x1 x2) y2). Qed.
Lemma lem1336658 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1336659 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term290 x1 x2 y2) = (@COND (prod hreal hreal) True).
Proof. exact (MK_COMB (@lem1336658) (@lem1336657 x1 x2 y2)). Qed.
Lemma lem1336668 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term291 x1 x2 y2) = (term291 x1 x2 y2).
Proof. exact (eq_refl (term291 x1 x2 y2)). Qed.
Lemma lem1336669 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term292 x1 x2 y2) = (term293 x1 x2 y2).
Proof. exact (MK_COMB (@lem1336659 x1 x2 y2) (@lem1336668 x1 x2 y2)). Qed.
Lemma lem1336678 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term294 x1 x2 y2) = (term294 x1 x2 y2).
Proof. exact (eq_refl (term294 x1 x2 y2)). Qed.
Lemma lem1336679 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term295 x1 x2 y2) = (term296 x1 x2 y2).
Proof. exact (MK_COMB (@lem1336669 x1 x2 y2) (@lem1336678 x1 x2 y2)). Qed.
Lemma lem1336681 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1336682 (t2 : prod hreal hreal) (t1 : prod hreal hreal) : (@COND (prod hreal hreal) True t1 t2) = t1.
Proof. exact (@lem1336681 (prod hreal hreal) t2 t1). Qed.
Lemma lem1336683 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term296 x1 x2 y2) = (term291 x1 x2 y2).
Proof. exact (@lem1336682 (term294 x1 x2 y2) (term291 x1 x2 y2)). Qed.
Lemma lem1336692 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term295 x1 x2 y2) = (term291 x1 x2 y2).
Proof. exact (TRANS (@lem1336679 x1 x2 y2) (@lem1336683 x1 x2 y2)). Qed.
Lemma lem1336693 (x1 : hreal) (x2 : hreal) : (term279 x1 x2) = (term279 x1 x2).
Proof. exact (eq_refl (term279 x1 x2)). Qed.
Lemma lem1336694 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term286 x1 x2 y2) = (term297 x1 x2 y2).
Proof. exact (MK_COMB (@lem1336693 x1 x2) (@lem1336692 x1 x2 y2)). Qed.
Lemma lem1336695 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term297 x1 x2 y2) = (term286 x1 x2 y2).
Proof. exact (SYM (@lem1336694 x1 x2 y2)). Qed.
Lemma lem1336697 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1335074 y x) (@lem1335073 x y)). Qed.
Lemma lem1336698 (y2 : hreal) (x1 : hreal) (x2 : hreal) : (term265 x1 x2 y2) = (term298 y2 x1 x2).
Proof. exact (@lem1336697 y2 (term198 x1 x2)). Qed.
Lemma lem1336699 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1336700 (y2 : hreal) (x1 : hreal) (x2 : hreal) : (term299 x1 x2 y2) = (term300 y2 x1 x2).
Proof. exact (MK_COMB (@lem1336699) (@lem1336698 y2 x1 x2)). Qed.
Lemma lem1336701 (y2 : hreal) (d : hreal) : (hreal_add y2 d) = (hreal_add y2 d).
Proof. exact (eq_refl (hreal_add y2 d)). Qed.
Lemma lem1336702 (x1 : hreal) (x2 : hreal) (y2 : hreal) (d : hreal) : ((term265 x1 x2 y2) = (hreal_add y2 d)) = ((term298 y2 x1 x2) = (hreal_add y2 d)).
Proof. exact (MK_COMB (@lem1336700 y2 x1 x2) (@lem1336701 y2 d)). Qed.
Lemma lem1336703 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term301 x1 x2 y2) = (term302 x1 x2 y2).
Proof. exact (fun_ext (fun d : hreal => @lem1336702 x1 x2 y2 d)). Qed.
Lemma lem1336704 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1336705 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term303 x1 x2 y2) = (term304 x1 x2 y2).
Proof. exact (MK_COMB (@lem1336704) (@lem1336703 x1 x2 y2)). Qed.
Lemma lem1336706 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1336707 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term305 x1 x2 y2) = (term306 x1 x2 y2).
Proof. exact (MK_COMB (@lem1336706) (@lem1336705 x1 x2 y2)). Qed.
Lemma lem1336708 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1336709 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term307 x1 x2 y2) = (term308 x1 x2 y2).
Proof. exact (MK_COMB (@lem1336708) (@lem1336707 x1 x2 y2)). Qed.
Lemma lem1336710 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1336711 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term291 x1 x2 y2) = (term309 x1 x2 y2).
Proof. exact (MK_COMB (@lem1336709 x1 x2 y2) (@lem1336710)). Qed.
Lemma lem1336712 (x1 : hreal) (x2 : hreal) : (term279 x1 x2) = (term279 x1 x2).
Proof. exact (eq_refl (term279 x1 x2)). Qed.
Lemma lem1336713 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term297 x1 x2 y2) = (term310 x1 x2 y2).
Proof. exact (MK_COMB (@lem1336712 x1 x2) (@lem1336711 x1 x2 y2)). Qed.
Lemma lem1336714 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term310 x1 x2 y2) = (term297 x1 x2 y2).
Proof. exact (SYM (@lem1336713 x1 x2 y2)). Qed.
Lemma lem1336728 (m : hreal) (n : hreal) (p : hreal) : ((hreal_add m n) = (hreal_add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1335068 m n p) (@lem1335067 m n p)). Qed.
Lemma lem1336729 (y2 : hreal) (x1 : hreal) (x2 : hreal) (d : hreal) : ((term298 y2 x1 x2) = (hreal_add y2 d)) = ((term198 x1 x2) = d).
Proof. exact (@lem1336728 y2 (term198 x1 x2) d). Qed.
Lemma lem1336736 (y2 : hreal) (x1 : hreal) (x2 : hreal) : (term302 x1 x2 y2) = (term269 x1 x2).
Proof. exact (fun_ext (fun d : hreal => @lem1336729 y2 x1 x2 d)). Qed.
Lemma lem1336737 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1336738 (y2 : hreal) (x1 : hreal) (x2 : hreal) : (term304 x1 x2 y2) = (term271 x1 x2).
Proof. exact (MK_COMB (@lem1336737) (@lem1336736 y2 x1 x2)). Qed.
Lemma lem1336741 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1336742 (y2 : hreal) (x1 : hreal) (x2 : hreal) : (term306 x1 x2 y2) = (term273 x1 x2).
Proof. exact (MK_COMB (@lem1336741) (@lem1336738 y2 x1 x2)). Qed.
Lemma lem1336743 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1336744 (y2 : hreal) (x1 : hreal) (x2 : hreal) : (term308 x1 x2 y2) = (term275 x1 x2).
Proof. exact (MK_COMB (@lem1336743) (@lem1336742 y2 x1 x2)). Qed.
Lemma lem1336745 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1336746 (y2 : hreal) (x1 : hreal) (x2 : hreal) : (term309 x1 x2 y2) = (term277 x1 x2).
Proof. exact (MK_COMB (@lem1336744 y2 x1 x2) (@lem1336745)). Qed.
Lemma lem1336747 (x1 : hreal) (x2 : hreal) : (term279 x1 x2) = (term279 x1 x2).
Proof. exact (eq_refl (term279 x1 x2)). Qed.
Lemma lem1336748 (y2 : hreal) (x1 : hreal) (x2 : hreal) : (term310 x1 x2 y2) = (term311 x1 x2).
Proof. exact (MK_COMB (@lem1336747 x1 x2) (@lem1336746 y2 x1 x2)). Qed.
Lemma lem1336750 (x : prod hreal hreal) : (treal_eq x x) = True.
Proof. exact (EQ_MP (@lem1335059 x) (@lem1335058 x)). Qed.
Lemma lem1336751 (x1 : hreal) (x2 : hreal) : (term311 x1 x2) = True.
Proof. exact (@lem1336750 (term277 x1 x2)). Qed.
Lemma lem1336752 (x1 : hreal) (x2 : hreal) (y2 : hreal) : (term310 x1 x2 y2) = True.
Proof. exact (TRANS (@lem1336748 y2 x1 x2) (@lem1336751 x1 x2)). Qed.
Lemma lem1336753 (x1 : hreal) (x2 : hreal) (y2 : hreal) : True = (term310 x1 x2 y2).
Proof. exact (SYM (@lem1336752 x1 x2 y2)). Qed.
Lemma lem1336754 (x1 : hreal) (x2 : hreal) (y2 : hreal) : term310 x1 x2 y2.
Proof. exact (EQ_MP (@lem1336753 x1 x2 y2) (@lem0)). Qed.
Lemma lem1336755 (x1 : hreal) (x2 : hreal) (y2 : hreal) : term297 x1 x2 y2.
Proof. exact (EQ_MP (@lem1336714 x1 x2 y2) (@lem1336754 x1 x2 y2)). Qed.
Lemma lem1336756 (x1 : hreal) (x2 : hreal) (y2 : hreal) : term286 x1 x2 y2.
Proof. exact (EQ_MP (@lem1336695 x1 x2 y2) (@lem1336755 x1 x2 y2)). Qed.
Lemma lem1336757 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) (h1 : (term265 x1 x2 y2) = y1) : term281 x1 x2 y2 y1.
Proof. exact (EQ_MP (@lem1336646 x1 x2 y2 y1 h1) (@lem1336756 x1 x2 y2)). Qed.
Lemma lem1336758 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : term282 x1 x2 y2 y1.
Proof. exact (fun h0 : (term265 x1 x2 y2) = y1 => @lem1336757 x1 x2 y2 y1 h0). Qed.
Lemma lem1336759 (x1 : hreal) (x2 : hreal) (y2 : hreal) (y1 : hreal) : term257 x1 x2 y2 y1.
Proof. exact (EQ_MP (@lem1336631 x1 x2 y2 y1) (@lem1336758 x1 x2 y2 y1)). Qed.
Lemma lem1336760 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : hreal_le x2 x1) : term259 x1 x2 y2 y1.
Proof. exact (EQ_MP (@lem1336560 y2 y1 x2 x1 h1) (@lem1336759 x1 x2 y2 y1)). Qed.
Lemma lem1336761 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : (hreal_add x1 y2) = (hreal_add x2 y1)) (h2 : hreal_le x2 x1) : term243 x1 x2 y2 y1.
Proof. exact (@lem1336760 y2 y1 x2 x1 h2 (@lem1336108 x1 y2 x2 y1 h1)). Qed.
Lemma lem1336832 (x2 : hreal) (x1 : hreal) : term244 x2 x1.
Proof. exact (@lem82 (hreal_le x2 x1)). Qed.
Lemma lem1336837 (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : (hreal_le x2 x1) = False.
Proof. exact (@lem1336832 x2 x1 (@lem1335155 x2 x1 h1)). Qed.
Lemma lem1336838 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1336839 (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : (term312 x2 x1) = (imp False).
Proof. exact (MK_COMB (@lem1336838) (@lem1336837 x2 x1 h1)). Qed.
Lemma lem1336852 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term248 x2 x1 y2 y1) = (term248 x2 x1 y2 y1).
Proof. exact (eq_refl (term248 x2 x1 y2 y1)). Qed.
Lemma lem1336853 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : (term313 x2 x1 y2 y1) = (term314 x2 x1 y2 y1).
Proof. exact (MK_COMB (@lem1336839 x2 x1 h1) (@lem1336852 x2 x1 y2 y1)). Qed.
Lemma lem1336855 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1336856 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term314 x2 x1 y2 y1) = True.
Proof. exact (@lem1336855 (term248 x2 x1 y2 y1)). Qed.
Lemma lem1336857 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : (term313 x2 x1 y2 y1) = True.
Proof. exact (TRANS (@lem1336853 y2 y1 x2 x1 h1) (@lem1336856 x2 x1 y2 y1)). Qed.
Lemma lem1336858 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : True = (term313 x2 x1 y2 y1).
Proof. exact (SYM (@lem1336857 y2 y1 x2 x1 h1)). Qed.
Lemma lem1336859 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) : term313 x2 x1 y2 y1.
Proof. exact (EQ_MP (@lem1336858 y2 y1 x2 x1 h1) (@lem0)). Qed.
Lemma lem1336860 (x1 : hreal) (x2 : hreal) (h1 : hreal_le x1 x2) : hreal_le x1 x2.
Proof. exact (h1). Qed.
Lemma lem1336862 (y : hreal) (x : hreal) : term99 y x.
Proof. exact (EQ_MP (@lem1335046 y x) (@lem1335045 x y)). Qed.
Lemma lem1336863 (x2 : hreal) (x1 : hreal) : term99 x2 x1.
Proof. exact (@lem1336862 x2 x1). Qed.
Lemma lem1336864 (x1 : hreal) (x2 : hreal) (h1 : hreal_le x1 x2) : term249 x2 x1.
Proof. exact (@lem1336863 x2 x1 (@lem1336860 x1 x2 h1)). Qed.
Lemma lem1336865 (P : hreal -> Prop) : term250 P.
Proof. exact (@lem9396 hreal P). Qed.
Lemma lem1336866 (x2 : hreal) (x1 : hreal) : term251 x2 x1.
Proof. exact (@lem1336865 (term197 x2 x1)). Qed.
Lemma lem1336867 (x1 : hreal) (x2 : hreal) (h1 : hreal_le x1 x2) : term252 x2 x1.
Proof. exact (@lem1336866 x2 x1 (@lem1336864 x1 x2 h1)). Qed.
Lemma lem1336868 (x2 : hreal) (x1 : hreal) : (term252 x2 x1) = (x2 = (term253 x2 x1)).
Proof. exact (eq_refl (term252 x2 x1)). Qed.
Lemma lem1336869 (x1 : hreal) (x2 : hreal) (h1 : hreal_le x1 x2) : x2 = (term253 x2 x1).
Proof. exact (EQ_MP (@lem1336868 x2 x1) (@lem1336867 x1 x2 h1)). Qed.
Lemma lem1336870 (x1 : hreal) (x2 : hreal) (h1 : hreal_le x1 x2) : (term253 x2 x1) = x2.
Proof. exact (SYM (@lem1336869 x1 x2 h1)). Qed.
Lemma lem1336871 (x1 : hreal) (x2 : hreal) (h1 : hreal_le x1 x2) : x2 = (term253 x2 x1).
Proof. exact (EQ_MP (@lem1336868 x2 x1) (@lem1336867 x1 x2 h1)). Qed.
Lemma lem1336872 (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term315 x1 y2 y1) = (term315 x1 y2 y1).
Proof. exact (eq_refl (term315 x1 y2 y1)). Qed.
Lemma lem1336873 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : hreal_le x1 x2) : (term316 x1 y2 y1 x2) = (term317 y2 y1 x2 x1).
Proof. exact (MK_COMB (@lem1336872 x1 y2 y1) (@lem1336871 x1 x2 h1)). Qed.
Lemma lem1336874 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term317 y2 y1 x2 x1) = (term318 x2 x1 y2 y1).
Proof. exact (eq_refl (term317 y2 y1 x2 x1)). Qed.
Lemma lem1336875 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term319 x1 y2 y1 x2) = (term319 x1 y2 y1 x2).
Proof. exact (eq_refl (term319 x1 y2 y1 x2)). Qed.
Lemma lem1336876 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : ((term316 x1 y2 y1 x2) = (term317 y2 y1 x2 x1)) = ((term316 x1 y2 y1 x2) = (term318 x2 x1 y2 y1)).
Proof. exact (MK_COMB (@lem1336875 x1 y2 y1 x2) (@lem1336874 x2 x1 y2 y1)). Qed.
Lemma lem1336877 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term316 x1 y2 y1 x2) = (term320 x2 x1 y2 y1).
Proof. exact (eq_refl (term316 x1 y2 y1 x2)). Qed.
Lemma lem1336878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1336879 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term319 x1 y2 y1 x2) = (term321 x2 x1 y2 y1).
Proof. exact (MK_COMB (@lem1336878) (@lem1336877 x2 x1 y2 y1)). Qed.
Lemma lem1336880 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term318 x2 x1 y2 y1) = (term318 x2 x1 y2 y1).
Proof. exact (eq_refl (term318 x2 x1 y2 y1)). Qed.
Lemma lem1336881 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : ((term316 x1 y2 y1 x2) = (term318 x2 x1 y2 y1)) = ((term320 x2 x1 y2 y1) = (term318 x2 x1 y2 y1)).
Proof. exact (MK_COMB (@lem1336879 x2 x1 y2 y1) (@lem1336880 x2 x1 y2 y1)). Qed.
Lemma lem1336882 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : ((term316 x1 y2 y1 x2) = (term317 y2 y1 x2 x1)) = ((term320 x2 x1 y2 y1) = (term318 x2 x1 y2 y1)).
Proof. exact (TRANS (@lem1336876 x2 x1 y2 y1) (@lem1336881 x2 x1 y2 y1)). Qed.
Lemma lem1336883 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : hreal_le x1 x2) : (term320 x2 x1 y2 y1) = (term318 x2 x1 y2 y1).
Proof. exact (EQ_MP (@lem1336882 x2 x1 y2 y1) (@lem1336873 y2 y1 x1 x2 h1)). Qed.
Lemma lem1336884 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : hreal_le x1 x2) : (term318 x2 x1 y2 y1) = (term320 x2 x1 y2 y1).
Proof. exact (SYM (@lem1336883 y2 y1 x1 x2 h1)). Qed.
Lemma lem1336894 (x : hreal) (y : hreal) (z : hreal) : (term80 x y z) = (term79 x y z).
Proof. exact (EQ_MP (@lem1335031 x y z) (@lem1335030 x y z)). Qed.
Lemma lem1336895 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term261 x2 x1 y1) = (term262 x2 x1 y1).
Proof. exact (@lem1336894 x1 (term198 x2 x1) y1). Qed.
Lemma lem1336900 (x1 : hreal) (y2 : hreal) : (term189 x1 y2) = (term189 x1 y2).
Proof. exact (eq_refl (term189 x1 y2)). Qed.
Lemma lem1336901 (y2 : hreal) (x2 : hreal) (x1 : hreal) (y1 : hreal) : ((hreal_add x1 y2) = (term261 x2 x1 y1)) = ((hreal_add x1 y2) = (term262 x2 x1 y1)).
Proof. exact (MK_COMB (@lem1336900 x1 y2) (@lem1336895 x2 x1 y1)). Qed.
Lemma lem1336903 (m : hreal) (n : hreal) (p : hreal) : ((hreal_add m n) = (hreal_add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1335040 m n p) (@lem1335039 m n p)). Qed.
Lemma lem1336904 (y2 : hreal) (x2 : hreal) (x1 : hreal) (y1 : hreal) : ((hreal_add x1 y2) = (term262 x2 x1 y1)) = (y2 = (term265 x2 x1 y1)).
Proof. exact (@lem1336903 x1 y2 (term265 x2 x1 y1)). Qed.
Lemma lem1336911 (y2 : hreal) (x2 : hreal) (x1 : hreal) (y1 : hreal) : ((hreal_add x1 y2) = (term261 x2 x1 y1)) = (y2 = (term265 x2 x1 y1)).
Proof. exact (TRANS (@lem1336901 y2 x2 x1 y1) (@lem1336904 y2 x2 x1 y1)). Qed.
Lemma lem1336912 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1336913 (y2 : hreal) (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term322 y2 x2 x1 y1) = (term323 y2 x2 x1 y1).
Proof. exact (MK_COMB (@lem1336912) (@lem1336911 y2 x2 x1 y1)). Qed.
Lemma lem1336917 (m : hreal) (n : hreal) (p : hreal) : ((hreal_add m n) = (hreal_add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1335040 m n p) (@lem1335039 m n p)). Qed.
Lemma lem1336918 (x2 : hreal) (x1 : hreal) (d : hreal) : ((term253 x2 x1) = (hreal_add x1 d)) = ((term198 x2 x1) = d).
Proof. exact (@lem1336917 x1 (term198 x2 x1) d). Qed.
Lemma lem1336925 (x2 : hreal) (x1 : hreal) : (term268 x2 x1) = (term269 x2 x1).
Proof. exact (fun_ext (fun d : hreal => @lem1336918 x2 x1 d)). Qed.
Lemma lem1336926 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1336927 (x2 : hreal) (x1 : hreal) : (term270 x2 x1) = (term271 x2 x1).
Proof. exact (MK_COMB (@lem1336926) (@lem1336925 x2 x1)). Qed.
Lemma lem1336930 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1336931 (x2 : hreal) (x1 : hreal) : (term272 x2 x1) = (term273 x2 x1).
Proof. exact (MK_COMB (@lem1336930) (@lem1336927 x2 x1)). Qed.
Lemma lem1336932 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem1336933 (x2 : hreal) (x1 : hreal) : (term324 x2 x1) = (term325 x2 x1).
Proof. exact (MK_COMB (@lem1336932) (@lem1336931 x2 x1)). Qed.
Lemma lem1336934 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1336935 (x2 : hreal) (x1 : hreal) : (term326 x2 x1) = (term327 x2 x1).
Proof. exact (MK_COMB (@lem1336934) (@lem1336933 x2 x1)). Qed.
Lemma lem1336944 (y2 : hreal) (y1 : hreal) : (term211 y2 y1) = (term211 y2 y1).
Proof. exact (eq_refl (term211 y2 y1)). Qed.
Lemma lem1336945 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term328 x2 x1 y2 y1) = (term329 x2 x1 y2 y1).
Proof. exact (MK_COMB (@lem1336935 x2 x1) (@lem1336944 y2 y1)). Qed.
Lemma lem1336946 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term318 x2 x1 y2 y1) = (term330 x2 x1 y2 y1).
Proof. exact (MK_COMB (@lem1336913 y2 x2 x1 y1) (@lem1336945 x2 x1 y2 y1)). Qed.
Lemma lem1336951 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term330 x2 x1 y2 y1) = (term318 x2 x1 y2 y1).
Proof. exact (SYM (@lem1336946 x2 x1 y2 y1)). Qed.
Lemma lem1336952 (y2 : hreal) (x2 : hreal) (x1 : hreal) (y1 : hreal) (h1 : y2 = (term265 x2 x1 y1)) : y2 = (term265 x2 x1 y1).
Proof. exact (h1). Qed.
Lemma lem1336953 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term331 x2 x1 y1) = (term331 x2 x1 y1).
Proof. exact (eq_refl (term331 x2 x1 y1)). Qed.
Lemma lem1336954 (y2 : hreal) (x2 : hreal) (x1 : hreal) (y1 : hreal) (h1 : y2 = (term265 x2 x1 y1)) : (term332 x2 x1 y1 y2) = (term333 x2 x1 y1).
Proof. exact (MK_COMB (@lem1336953 x2 x1 y1) (@lem1336952 y2 x2 x1 y1 h1)). Qed.
Lemma lem1336955 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term333 x2 x1 y1) = (term334 x2 x1 y1).
Proof. exact (eq_refl (term333 x2 x1 y1)). Qed.
Lemma lem1336956 (x2 : hreal) (x1 : hreal) (y1 : hreal) (y2 : hreal) : (term335 x2 x1 y1 y2) = (term335 x2 x1 y1 y2).
Proof. exact (eq_refl (term335 x2 x1 y1 y2)). Qed.
Lemma lem1336957 (y2 : hreal) (x2 : hreal) (x1 : hreal) (y1 : hreal) : ((term332 x2 x1 y1 y2) = (term333 x2 x1 y1)) = ((term332 x2 x1 y1 y2) = (term334 x2 x1 y1)).
Proof. exact (MK_COMB (@lem1336956 x2 x1 y1 y2) (@lem1336955 x2 x1 y1)). Qed.
Lemma lem1336958 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term332 x2 x1 y1 y2) = (term329 x2 x1 y2 y1).
Proof. exact (eq_refl (term332 x2 x1 y1 y2)). Qed.
Lemma lem1336959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1336960 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term335 x2 x1 y1 y2) = (term336 x2 x1 y2 y1).
Proof. exact (MK_COMB (@lem1336959) (@lem1336958 x2 x1 y2 y1)). Qed.
Lemma lem1336961 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term334 x2 x1 y1) = (term334 x2 x1 y1).
Proof. exact (eq_refl (term334 x2 x1 y1)). Qed.
Lemma lem1336962 (y2 : hreal) (x2 : hreal) (x1 : hreal) (y1 : hreal) : ((term332 x2 x1 y1 y2) = (term334 x2 x1 y1)) = ((term329 x2 x1 y2 y1) = (term334 x2 x1 y1)).
Proof. exact (MK_COMB (@lem1336960 x2 x1 y2 y1) (@lem1336961 x2 x1 y1)). Qed.
Lemma lem1336963 (y2 : hreal) (x2 : hreal) (x1 : hreal) (y1 : hreal) : ((term332 x2 x1 y1 y2) = (term333 x2 x1 y1)) = ((term329 x2 x1 y2 y1) = (term334 x2 x1 y1)).
Proof. exact (TRANS (@lem1336957 y2 x2 x1 y1) (@lem1336962 y2 x2 x1 y1)). Qed.
Lemma lem1336964 (y2 : hreal) (x2 : hreal) (x1 : hreal) (y1 : hreal) (h1 : y2 = (term265 x2 x1 y1)) : (term329 x2 x1 y2 y1) = (term334 x2 x1 y1).
Proof. exact (EQ_MP (@lem1336963 y2 x2 x1 y1) (@lem1336954 y2 x2 x1 y1 h1)). Qed.
Lemma lem1336965 (y2 : hreal) (x2 : hreal) (x1 : hreal) (y1 : hreal) (h1 : y2 = (term265 x2 x1 y1)) : (term334 x2 x1 y1) = (term329 x2 x1 y2 y1).
Proof. exact (SYM (@lem1336964 y2 x2 x1 y1 h1)). Qed.
Lemma lem1336996 (_474 : prod hreal hreal) (_475 : Prop) (_476 : type1233) (_477 : prod hreal hreal) : (term337 _476 _475 _474 _477) = (term338 _474 _475 _476 _477).
Proof. exact (@lem13473 (prod hreal hreal) _474 _475 _476 _477). Qed.
Lemma lem1336997 (_474 : prod hreal hreal) (_475 : Prop) (x2 : hreal) (x1 : hreal) (_477 : prod hreal hreal) : (term339 x2 x1 _475 _474 _477) = (term340 _474 _475 x2 x1 _477).
Proof. exact (@lem1336996 _474 _475 (term341 x2 x1) _477). Qed.
Lemma lem1336998 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term342 x2 x1 y1) = (term343 x2 x1 y1).
Proof. exact (@lem1336997 (term344 x2 x1 y1) (term345 x2 x1 y1) x2 x1 (term346 x2 x1 y1)). Qed.
Lemma lem1336999 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term347 x2 x1 y1) = (term348 x2 x1 y1).
Proof. exact (eq_refl (term347 x2 x1 y1)). Qed.
Lemma lem1337000 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term349 x2 x1 y1) = (term349 x2 x1 y1).
Proof. exact (eq_refl (term349 x2 x1 y1)). Qed.
Lemma lem1337001 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term350 x2 x1 y1) = (term351 x2 x1 y1).
Proof. exact (MK_COMB (@lem1337000 x2 x1 y1) (@lem1336999 x2 x1 y1)). Qed.
Lemma lem1337002 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term352 x2 x1 y1) = (term353 x2 x1 y1).
Proof. exact (eq_refl (term352 x2 x1 y1)). Qed.
Lemma lem1337003 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term354 x2 x1 y1) = (term354 x2 x1 y1).
Proof. exact (eq_refl (term354 x2 x1 y1)). Qed.
Lemma lem1337004 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term355 x2 x1 y1) = (term356 x2 x1 y1).
Proof. exact (MK_COMB (@lem1337003 x2 x1 y1) (@lem1337002 x2 x1 y1)). Qed.
Lemma lem1337005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1337006 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term357 x2 x1 y1) = (term358 x2 x1 y1).
Proof. exact (MK_COMB (@lem1337005) (@lem1337004 x2 x1 y1)). Qed.
Lemma lem1337007 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term343 x2 x1 y1) = (term359 x2 x1 y1).
Proof. exact (MK_COMB (@lem1337006 x2 x1 y1) (@lem1337001 x2 x1 y1)). Qed.
Lemma lem1337008 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term342 x2 x1 y1) = (term334 x2 x1 y1).
Proof. exact (eq_refl (term342 x2 x1 y1)). Qed.
Lemma lem1337009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1337010 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term360 x2 x1 y1) = (term361 x2 x1 y1).
Proof. exact (MK_COMB (@lem1337009) (@lem1337008 x2 x1 y1)). Qed.
Lemma lem1337011 (x2 : hreal) (x1 : hreal) (y1 : hreal) : ((term342 x2 x1 y1) = (term343 x2 x1 y1)) = ((term334 x2 x1 y1) = (term359 x2 x1 y1)).
Proof. exact (MK_COMB (@lem1337010 x2 x1 y1) (@lem1337007 x2 x1 y1)). Qed.
Lemma lem1337012 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term334 x2 x1 y1) = (term359 x2 x1 y1).
Proof. exact (EQ_MP (@lem1337011 x2 x1 y1) (@lem1336998 x2 x1 y1)). Qed.
Lemma lem1337013 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term359 x2 x1 y1) = (term334 x2 x1 y1).
Proof. exact (SYM (@lem1337012 x2 x1 y1)). Qed.
Lemma lem1337014 (x2 : hreal) (x1 : hreal) (y1 : hreal) (h1 : term345 x2 x1 y1) : term345 x2 x1 y1.
Proof. exact (h1). Qed.
Lemma lem1337049 (x : hreal) : x = (term44 x).
Proof. exact (EQ_MP (@lem1334971 x) (@lem1334970 x)). Qed.
Lemma lem1337050 (y1 : hreal) : y1 = (term44 y1).
Proof. exact (@lem1337049 y1). Qed.
Lemma lem1337051 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term362 x2 x1 y1) = (term362 x2 x1 y1).
Proof. exact (eq_refl (term362 x2 x1 y1)). Qed.
Lemma lem1337052 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term345 x2 x1 y1) = (term363 x2 x1 y1).
Proof. exact (MK_COMB (@lem1337051 x2 x1 y1) (@lem1337050 y1)). Qed.
Lemma lem1337053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1337054 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term354 x2 x1 y1) = (term364 x2 x1 y1).
Proof. exact (MK_COMB (@lem1337053) (@lem1337052 x2 x1 y1)). Qed.
Lemma lem1337055 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term353 x2 x1 y1) = (term353 x2 x1 y1).
Proof. exact (eq_refl (term353 x2 x1 y1)). Qed.
Lemma lem1337056 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term356 x2 x1 y1) = (term365 x2 x1 y1).
Proof. exact (MK_COMB (@lem1337054 x2 x1 y1) (@lem1337055 x2 x1 y1)). Qed.
Lemma lem1337057 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term365 x2 x1 y1) = (term356 x2 x1 y1).
Proof. exact (SYM (@lem1337056 x2 x1 y1)). Qed.
Lemma lem1337061 (m : hreal) (n : hreal) (p : hreal) : (term61 n p m) = (hreal_le n p).
Proof. exact (EQ_MP (@lem1334958 m n p) (@lem1334957 m n p)). Qed.
Lemma lem1337062 (y1 : hreal) (x2 : hreal) (x1 : hreal) : (term363 x2 x1 y1) = (term366 x2 x1).
Proof. exact (@lem1337061 y1 (term198 x2 x1) term22). Qed.
Lemma lem1337067 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1337068 (y1 : hreal) (x2 : hreal) (x1 : hreal) : (term364 x2 x1 y1) = (term367 x2 x1).
Proof. exact (MK_COMB (@lem1337067) (@lem1337062 y1 x2 x1)). Qed.
Lemma lem1337085 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term353 x2 x1 y1) = (term353 x2 x1 y1).
Proof. exact (eq_refl (term353 x2 x1 y1)). Qed.
Lemma lem1337086 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term365 x2 x1 y1) = (term368 x2 x1 y1).
Proof. exact (MK_COMB (@lem1337068 y1 x2 x1) (@lem1337085 x2 x1 y1)). Qed.
Lemma lem1337089 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term368 x2 x1 y1) = (term365 x2 x1 y1).
Proof. exact (SYM (@lem1337086 x2 x1 y1)). Qed.
Lemma lem1337090 (x2 : hreal) (x1 : hreal) (h1 : term366 x2 x1) : term366 x2 x1.
Proof. exact (h1). Qed.
Lemma lem1337091 (x2 : hreal) (x1 : hreal) (h1 : (term198 x2 x1) = term22) : (term198 x2 x1) = term22.
Proof. exact (h1). Qed.
Lemma lem1337092 (x : hreal) : term369 x.
Proof. exact (@lem1334907 x). Qed.
Lemma lem1337093 (x : hreal) : (term369 x) = (term54 x).
Proof. exact (eq_refl (term369 x)). Qed.
Lemma lem1337094 (x : hreal) : term54 x.
Proof. exact (EQ_MP (@lem1337093 x) (@lem1337092 x)). Qed.
Lemma lem1337095 (x : hreal) (y : hreal) : term370 x y.
Proof. exact (@lem1337094 x y). Qed.
Lemma lem1337096 (y : hreal) (x : hreal) : (term370 x y) = ((x = y) = (term50 y x)).
Proof. exact (eq_refl (term370 x y)). Qed.
Lemma lem1337128 (x2 : hreal) (x1 : hreal) : (term366 x2 x1) = ((term366 x2 x1) = True).
Proof. exact (@lem7 (term366 x2 x1)). Qed.
Lemma lem1337133 (y : hreal) (x : hreal) : (x = y) = (term50 y x).
Proof. exact (EQ_MP (@lem1337096 y x) (@lem1337095 x y)). Qed.
Lemma lem1337134 (x2 : hreal) (x1 : hreal) : ((term198 x2 x1) = term22) = (term371 x2 x1).
Proof. exact (@lem1337133 term22 (term198 x2 x1)). Qed.
Lemma lem1337138 (x2 : hreal) (x1 : hreal) (h1 : term366 x2 x1) : (term366 x2 x1) = True.
Proof. exact (EQ_MP (@lem1337128 x2 x1) (@lem1337090 x2 x1 h1)). Qed.
Lemma lem1337139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1337140 (x2 : hreal) (x1 : hreal) (h1 : term366 x2 x1) : (term372 x2 x1) = (and True).
Proof. exact (MK_COMB (@lem1337139) (@lem1337138 x2 x1 h1)). Qed.
Lemma lem1337146 (y : hreal) (x : hreal) : (x = y) = (term50 y x).
Proof. exact (EQ_MP (@lem1337096 y x) (@lem1337095 x y)). Qed.
Lemma lem1337147 (x1 : hreal) (d : hreal) (x2 : hreal) : (x2 = (hreal_add x1 d)) = (term373 x1 d x2).
Proof. exact (@lem1337146 (hreal_add x1 d) x2). Qed.
Lemma lem1337150 (x1 : hreal) (x2 : hreal) : (term197 x2 x1) = (term374 x1 x2).
Proof. exact (fun_ext (fun d : hreal => @lem1337147 x1 d x2)). Qed.
Lemma lem1337151 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1337152 (x1 : hreal) (x2 : hreal) : (term198 x2 x1) = (term375 x1 x2).
Proof. exact (MK_COMB (@lem1337151) (@lem1337150 x1 x2)). Qed.
Lemma lem1337153 : term376 = term376.
Proof. exact (eq_refl term376). Qed.
Lemma lem1337154 (x1 : hreal) (x2 : hreal) : (term377 x2 x1) = (term378 x1 x2).
Proof. exact (MK_COMB (@lem1337153) (@lem1337152 x1 x2)). Qed.
Lemma lem1337155 (x2 : hreal) (x1 : hreal) (h1 : term366 x2 x1) : (term371 x2 x1) = (term379 x1 x2).
Proof. exact (MK_COMB (@lem1337140 x2 x1 h1) (@lem1337154 x1 x2)). Qed.
Lemma lem1337157 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1337158 (x1 : hreal) (x2 : hreal) : (term379 x1 x2) = (term378 x1 x2).
Proof. exact (@lem1337157 (term378 x1 x2)). Qed.
Lemma lem1337161 (x2 : hreal) (x1 : hreal) (h1 : term366 x2 x1) : (term371 x2 x1) = (term378 x1 x2).
Proof. exact (TRANS (@lem1337155 x2 x1 h1) (@lem1337158 x1 x2)). Qed.
Lemma lem1337162 (x2 : hreal) (x1 : hreal) (h1 : term366 x2 x1) : ((term198 x2 x1) = term22) = (term378 x1 x2).
Proof. exact (TRANS (@lem1337134 x2 x1) (@lem1337161 x2 x1 h1)). Qed.
Lemma lem1337163 (x2 : hreal) (x1 : hreal) (h1 : term366 x2 x1) : (term378 x1 x2) = ((term198 x2 x1) = term22).
Proof. exact (SYM (@lem1337162 x2 x1 h1)). Qed.
Lemma lem1337165 (x : hreal) : x = (term44 x).
Proof. exact (EQ_MP (@lem1334892 x) (@lem1334891 x)). Qed.
Lemma lem1337166 (x1 : hreal) (x2 : hreal) : (term375 x1 x2) = (term380 x1 x2).
Proof. exact (@lem1337165 (term375 x1 x2)). Qed.
Lemma lem1337167 : term376 = term376.
Proof. exact (eq_refl term376). Qed.
Lemma lem1337168 (x1 : hreal) (x2 : hreal) : (term378 x1 x2) = (term381 x1 x2).
Proof. exact (MK_COMB (@lem1337167) (@lem1337166 x1 x2)). Qed.
Lemma lem1337169 (x1 : hreal) (x2 : hreal) : (term381 x1 x2) = (term378 x1 x2).
Proof. exact (SYM (@lem1337168 x1 x2)). Qed.
Lemma lem1337171 (x : hreal) (y : hreal) : (term43 x y) = True.
Proof. exact (EQ_MP (@lem1334879 x y) (@lem1334878 x y)). Qed.
Lemma lem1337172 (x1 : hreal) (x2 : hreal) : (term381 x1 x2) = True.
Proof. exact (@lem1337171 term22 (term375 x1 x2)). Qed.
Lemma lem1337173 (x1 : hreal) (x2 : hreal) : True = (term381 x1 x2).
Proof. exact (SYM (@lem1337172 x1 x2)). Qed.
Lemma lem1337174 (x1 : hreal) (x2 : hreal) : term381 x1 x2.
Proof. exact (EQ_MP (@lem1337173 x1 x2) (@lem0)). Qed.
Lemma lem1337175 (x1 : hreal) (x2 : hreal) : term378 x1 x2.
Proof. exact (EQ_MP (@lem1337169 x1 x2) (@lem1337174 x1 x2)). Qed.
Lemma lem1337176 (x2 : hreal) (x1 : hreal) (h1 : term366 x2 x1) : (term198 x2 x1) = term22.
Proof. exact (EQ_MP (@lem1337163 x2 x1 h1) (@lem1337175 x1 x2)). Qed.
Lemma lem1337177 (x2 : hreal) (x1 : hreal) (h1 : (term198 x2 x1) = term22) : (term198 x2 x1) = term22.
Proof. exact (h1). Qed.
Lemma lem1337178 (y1 : hreal) : (term382 y1) = (term382 y1).
Proof. exact (eq_refl (term382 y1)). Qed.
Lemma lem1337179 (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : (term198 x2 x1) = term22) : (term383 y1 x2 x1) = (term384 y1).
Proof. exact (MK_COMB (@lem1337178 y1) (@lem1337177 x2 x1 h1)). Qed.
Lemma lem1337180 (y1 : hreal) : (term384 y1) = (term385 y1).
Proof. exact (eq_refl (term384 y1)). Qed.
Lemma lem1337181 (y1 : hreal) (x2 : hreal) (x1 : hreal) : (term386 y1 x2 x1) = (term386 y1 x2 x1).
Proof. exact (eq_refl (term386 y1 x2 x1)). Qed.
Lemma lem1337182 (x2 : hreal) (x1 : hreal) (y1 : hreal) : ((term383 y1 x2 x1) = (term384 y1)) = ((term383 y1 x2 x1) = (term385 y1)).
Proof. exact (MK_COMB (@lem1337181 y1 x2 x1) (@lem1337180 y1)). Qed.
Lemma lem1337183 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term383 y1 x2 x1) = (term353 x2 x1 y1).
Proof. exact (eq_refl (term383 y1 x2 x1)). Qed.
Lemma lem1337184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1337185 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term386 y1 x2 x1) = (term387 x2 x1 y1).
Proof. exact (MK_COMB (@lem1337184) (@lem1337183 x2 x1 y1)). Qed.
Lemma lem1337186 (y1 : hreal) : (term385 y1) = (term385 y1).
Proof. exact (eq_refl (term385 y1)). Qed.
Lemma lem1337187 (x2 : hreal) (x1 : hreal) (y1 : hreal) : ((term383 y1 x2 x1) = (term385 y1)) = ((term353 x2 x1 y1) = (term385 y1)).
Proof. exact (MK_COMB (@lem1337185 x2 x1 y1) (@lem1337186 y1)). Qed.
Lemma lem1337188 (x2 : hreal) (x1 : hreal) (y1 : hreal) : ((term383 y1 x2 x1) = (term384 y1)) = ((term353 x2 x1 y1) = (term385 y1)).
Proof. exact (TRANS (@lem1337182 x2 x1 y1) (@lem1337187 x2 x1 y1)). Qed.
Lemma lem1337189 (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : (term198 x2 x1) = term22) : (term353 x2 x1 y1) = (term385 y1).
Proof. exact (EQ_MP (@lem1337188 x2 x1 y1) (@lem1337179 y1 x2 x1 h1)). Qed.
Lemma lem1337190 (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : (term198 x2 x1) = term22) : (term385 y1) = (term353 x2 x1 y1).
Proof. exact (SYM (@lem1337189 y1 x2 x1 h1)). Qed.
Lemma lem1337204 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : term124 x1 x2.
Proof. exact (h1). Qed.
Lemma lem1337246 (x1 : hreal) (x2 : hreal) (h1 : hreal_le x1 x2) : hreal_le x1 x2.
Proof. exact (h1). Qed.
Lemma lem1337247 (x1 : hreal) (x2 : hreal) : (term388 x1 x2) = (term388 x1 x2).
Proof. exact (eq_refl (term388 x1 x2)). Qed.
Lemma lem1337248 (x2 : hreal) (x1 : hreal) (h1 : (term198 x2 x1) = term22) : (term389 x2 x1) = (term390 x1 x2).
Proof. exact (MK_COMB (@lem1337247 x1 x2) (@lem1337177 x2 x1 h1)). Qed.
Lemma lem1337249 (x1 : hreal) (x2 : hreal) : (term390 x1 x2) = ((term5 x1) = x2).
Proof. exact (eq_refl (term390 x1 x2)). Qed.
Lemma lem1337250 (x2 : hreal) (x1 : hreal) : (term391 x2 x1) = (term391 x2 x1).
Proof. exact (eq_refl (term391 x2 x1)). Qed.
Lemma lem1337251 (x1 : hreal) (x2 : hreal) : ((term389 x2 x1) = (term390 x1 x2)) = ((term389 x2 x1) = ((term5 x1) = x2)).
Proof. exact (MK_COMB (@lem1337250 x2 x1) (@lem1337249 x1 x2)). Qed.
Lemma lem1337252 (x1 : hreal) (x2 : hreal) : (term389 x2 x1) = ((term253 x2 x1) = x2).
Proof. exact (eq_refl (term389 x2 x1)). Qed.
Lemma lem1337253 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1337254 (x1 : hreal) (x2 : hreal) : (term391 x2 x1) = (term392 x1 x2).
Proof. exact (MK_COMB (@lem1337253) (@lem1337252 x1 x2)). Qed.
Lemma lem1337255 (x1 : hreal) (x2 : hreal) : ((term5 x1) = x2) = ((term5 x1) = x2).
Proof. exact (eq_refl ((term5 x1) = x2)). Qed.
Lemma lem1337256 (x1 : hreal) (x2 : hreal) : ((term389 x2 x1) = ((term5 x1) = x2)) = (((term253 x2 x1) = x2) = ((term5 x1) = x2)).
Proof. exact (MK_COMB (@lem1337254 x1 x2) (@lem1337255 x1 x2)). Qed.
Lemma lem1337257 (x1 : hreal) (x2 : hreal) : ((term389 x2 x1) = (term390 x1 x2)) = (((term253 x2 x1) = x2) = ((term5 x1) = x2)).
Proof. exact (TRANS (@lem1337251 x1 x2) (@lem1337256 x1 x2)). Qed.
Lemma lem1337258 (x2 : hreal) (x1 : hreal) (h1 : (term198 x2 x1) = term22) : ((term253 x2 x1) = x2) = ((term5 x1) = x2).
Proof. exact (EQ_MP (@lem1337257 x1 x2) (@lem1337248 x2 x1 h1)). Qed.
Lemma lem1337259 (x1 : hreal) (x2 : hreal) (h1 : (term198 x2 x1) = term22) (h2 : hreal_le x1 x2) : (term5 x1) = x2.
Proof. exact (EQ_MP (@lem1337258 x2 x1 h1) (@lem1336870 x1 x2 h2)). Qed.
Lemma lem1337273 (n : hreal) : term393 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1337274 (n : hreal) : (term393 n) = ((term5 n) = n).
Proof. exact (eq_refl (term393 n)). Qed.
Lemma lem1337276 (x1 : hreal) (x2 : hreal) : term217 x1 x2.
Proof. exact (@lem82 (x1 = x2)). Qed.
Lemma lem1337315 (n : hreal) : (term5 n) = n.
Proof. exact (EQ_MP (@lem1337274 n) (@lem1337273 n)). Qed.
Lemma lem1337316 (x1 : hreal) : (term5 x1) = x1.
Proof. exact (@lem1337315 x1). Qed.
Lemma lem1337317 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1337318 (x1 : hreal) : (term30 x1) = (@eq hreal x1).
Proof. exact (MK_COMB (@lem1337317) (@lem1337316 x1)). Qed.
Lemma lem1337319 (x2 : hreal) : x2 = x2.
Proof. exact (eq_refl x2). Qed.
Lemma lem1337320 (x1 : hreal) (x2 : hreal) : ((term5 x1) = x2) = (x1 = x2).
Proof. exact (MK_COMB (@lem1337318 x1) (@lem1337319 x2)). Qed.
Lemma lem1337322 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (x1 = x2) = False.
Proof. exact (@lem1337276 x1 x2 (@lem1337204 x1 x2 h1)). Qed.
Lemma lem1337323 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : ((term5 x1) = x2) = False.
Proof. exact (TRANS (@lem1337320 x1 x2) (@lem1337322 x1 x2 h1)). Qed.
Lemma lem1337324 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1337325 (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (term394 x1 x2) = (imp False).
Proof. exact (MK_COMB (@lem1337324) (@lem1337323 x1 x2 h1)). Qed.
Lemma lem1337334 (y1 : hreal) : (term385 y1) = (term385 y1).
Proof. exact (eq_refl (term385 y1)). Qed.
Lemma lem1337335 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (term395 x1 x2 y1) = (term396 y1).
Proof. exact (MK_COMB (@lem1337325 x1 x2 h1) (@lem1337334 y1)). Qed.
Lemma lem1337337 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1337338 (y1 : hreal) : (term396 y1) = True.
Proof. exact (@lem1337337 (term385 y1)). Qed.
Lemma lem1337339 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : (term395 x1 x2 y1) = True.
Proof. exact (TRANS (@lem1337335 y1 x1 x2 h1) (@lem1337338 y1)). Qed.
Lemma lem1337340 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : True = (term395 x1 x2 y1).
Proof. exact (SYM (@lem1337339 y1 x1 x2 h1)). Qed.
Lemma lem1337341 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : term395 x1 x2 y1.
Proof. exact (EQ_MP (@lem1337340 y1 x1 x2 h1) (@lem0)). Qed.
Lemma lem1337342 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : (term198 x2 x1) = term22) (h3 : hreal_le x1 x2) : term385 y1.
Proof. exact (@lem1337341 y1 x1 x2 h1 (@lem1337259 x1 x2 h2 h3)). Qed.
Lemma lem1337343 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : (term198 x2 x1) = term22) (h3 : hreal_le x1 x2) : (hreal_le x1 x2) = (term385 y1).
Proof. exact (prop_ext (fun h4 : hreal_le x1 x2 => @lem1337342 y1 x1 x2 h1 h2 h3) (fun h4 : term385 y1 => @lem1337246 x1 x2 h3)). Qed.
Lemma lem1337344 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : (term198 x2 x1) = term22) (h3 : hreal_le x1 x2) : term385 y1.
Proof. exact (EQ_MP (@lem1337343 y1 x1 x2 h1 h2 h3) (@lem1337246 x1 x2 h3)). Qed.
Lemma lem1337345 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : (term198 x2 x1) = term22) (h3 : hreal_le x1 x2) : (term124 x1 x2) = (term385 y1).
Proof. exact (prop_ext (fun h4 : term124 x1 x2 => @lem1337344 y1 x1 x2 h1 h2 h3) (fun h4 : term385 y1 => @lem1337204 x1 x2 h1)). Qed.
Lemma lem1337346 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : (term198 x2 x1) = term22) (h3 : hreal_le x1 x2) : term385 y1.
Proof. exact (EQ_MP (@lem1337345 y1 x1 x2 h1 h2 h3) (@lem1337204 x1 x2 h1)). Qed.
Lemma lem1337347 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : (term198 x2 x1) = term22) (h3 : hreal_le x1 x2) : term353 x2 x1 y1.
Proof. exact (EQ_MP (@lem1337190 y1 x2 x1 h2) (@lem1337346 y1 x1 x2 h1 h2 h3)). Qed.
Lemma lem1337348 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) : term397 x2 x1 y1.
Proof. exact (fun h0 : (term198 x2 x1) = term22 => @lem1337347 y1 x1 x2 h1 h0 h2). Qed.
Lemma lem1337349 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : (term198 x2 x1) = term22) (h3 : hreal_le x1 x2) : term353 x2 x1 y1.
Proof. exact (@lem1337348 y1 x1 x2 h1 h3 (@lem1337091 x2 x1 h2)). Qed.
Lemma lem1337350 (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) (h3 : term366 x2 x1) : ((term198 x2 x1) = term22) = (term353 x2 x1 y1).
Proof. exact (prop_ext (fun h4 : (term198 x2 x1) = term22 => @lem1337349 y1 x1 x2 h1 h4 h2) (fun h4 : term353 x2 x1 y1 => @lem1337176 x2 x1 h3)). Qed.
Lemma lem1337351 (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) (h3 : term366 x2 x1) : term353 x2 x1 y1.
Proof. exact (EQ_MP (@lem1337350 y1 x2 x1 h1 h2 h3) (@lem1337176 x2 x1 h3)). Qed.
Lemma lem1337352 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) : term368 x2 x1 y1.
Proof. exact (fun h0 : term366 x2 x1 => @lem1337351 y1 x2 x1 h1 h2 h0). Qed.
Lemma lem1337353 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) : term365 x2 x1 y1.
Proof. exact (EQ_MP (@lem1337089 x2 x1 y1) (@lem1337352 y1 x1 x2 h1 h2)). Qed.
Lemma lem1337354 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) : term356 x2 x1 y1.
Proof. exact (EQ_MP (@lem1337057 x2 x1 y1) (@lem1337353 y1 x1 x2 h1 h2)). Qed.
Lemma lem1337357 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1334871 y x) (@lem1334870 x y)). Qed.
Lemma lem1337358 (y1 : hreal) (x2 : hreal) (x1 : hreal) : (term265 x2 x1 y1) = (term298 y1 x2 x1).
Proof. exact (@lem1337357 y1 (term198 x2 x1)). Qed.
Lemma lem1337359 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1337360 (y1 : hreal) (x2 : hreal) (x1 : hreal) : (term299 x2 x1 y1) = (term300 y1 x2 x1).
Proof. exact (MK_COMB (@lem1337359) (@lem1337358 y1 x2 x1)). Qed.
Lemma lem1337361 (y1 : hreal) (d : hreal) : (hreal_add y1 d) = (hreal_add y1 d).
Proof. exact (eq_refl (hreal_add y1 d)). Qed.
Lemma lem1337362 (x2 : hreal) (x1 : hreal) (y1 : hreal) (d : hreal) : ((term265 x2 x1 y1) = (hreal_add y1 d)) = ((term298 y1 x2 x1) = (hreal_add y1 d)).
Proof. exact (MK_COMB (@lem1337360 y1 x2 x1) (@lem1337361 y1 d)). Qed.
Lemma lem1337363 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term301 x2 x1 y1) = (term302 x2 x1 y1).
Proof. exact (fun_ext (fun d : hreal => @lem1337362 x2 x1 y1 d)). Qed.
Lemma lem1337364 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1337365 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term303 x2 x1 y1) = (term304 x2 x1 y1).
Proof. exact (MK_COMB (@lem1337364) (@lem1337363 x2 x1 y1)). Qed.
Lemma lem1337366 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1337367 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term305 x2 x1 y1) = (term306 x2 x1 y1).
Proof. exact (MK_COMB (@lem1337366) (@lem1337365 x2 x1 y1)). Qed.
Lemma lem1337368 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem1337369 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term346 x2 x1 y1) = (term398 x2 x1 y1).
Proof. exact (MK_COMB (@lem1337368) (@lem1337367 x2 x1 y1)). Qed.
Lemma lem1337370 (x2 : hreal) (x1 : hreal) : (term327 x2 x1) = (term327 x2 x1).
Proof. exact (eq_refl (term327 x2 x1)). Qed.
Lemma lem1337371 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term348 x2 x1 y1) = (term399 x2 x1 y1).
Proof. exact (MK_COMB (@lem1337370 x2 x1) (@lem1337369 x2 x1 y1)). Qed.
Lemma lem1337372 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term399 x2 x1 y1) = (term348 x2 x1 y1).
Proof. exact (SYM (@lem1337371 x2 x1 y1)). Qed.
Lemma lem1337386 (m : hreal) (n : hreal) (p : hreal) : ((hreal_add m n) = (hreal_add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1334865 m n p) (@lem1334864 m n p)). Qed.
Lemma lem1337387 (y1 : hreal) (x2 : hreal) (x1 : hreal) (d : hreal) : ((term298 y1 x2 x1) = (hreal_add y1 d)) = ((term198 x2 x1) = d).
Proof. exact (@lem1337386 y1 (term198 x2 x1) d). Qed.
Lemma lem1337394 (y1 : hreal) (x2 : hreal) (x1 : hreal) : (term302 x2 x1 y1) = (term269 x2 x1).
Proof. exact (fun_ext (fun d : hreal => @lem1337387 y1 x2 x1 d)). Qed.
Lemma lem1337395 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1337396 (y1 : hreal) (x2 : hreal) (x1 : hreal) : (term304 x2 x1 y1) = (term271 x2 x1).
Proof. exact (MK_COMB (@lem1337395) (@lem1337394 y1 x2 x1)). Qed.
Lemma lem1337399 : hreal_inv = hreal_inv.
Proof. exact (eq_refl hreal_inv). Qed.
Lemma lem1337400 (y1 : hreal) (x2 : hreal) (x1 : hreal) : (term306 x2 x1 y1) = (term273 x2 x1).
Proof. exact (MK_COMB (@lem1337399) (@lem1337396 y1 x2 x1)). Qed.
Lemma lem1337401 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem1337402 (y1 : hreal) (x2 : hreal) (x1 : hreal) : (term398 x2 x1 y1) = (term325 x2 x1).
Proof. exact (MK_COMB (@lem1337401) (@lem1337400 y1 x2 x1)). Qed.
Lemma lem1337403 (x2 : hreal) (x1 : hreal) : (term327 x2 x1) = (term327 x2 x1).
Proof. exact (eq_refl (term327 x2 x1)). Qed.
Lemma lem1337404 (y1 : hreal) (x2 : hreal) (x1 : hreal) : (term399 x2 x1 y1) = (term400 x2 x1).
Proof. exact (MK_COMB (@lem1337403 x2 x1) (@lem1337402 y1 x2 x1)). Qed.
Lemma lem1337406 (x : prod hreal hreal) : (treal_eq x x) = True.
Proof. exact (EQ_MP (@lem1334856 x) (@lem1334855 x)). Qed.
Lemma lem1337407 (x2 : hreal) (x1 : hreal) : (term400 x2 x1) = True.
Proof. exact (@lem1337406 (term325 x2 x1)). Qed.
Lemma lem1337408 (x2 : hreal) (x1 : hreal) (y1 : hreal) : (term399 x2 x1 y1) = True.
Proof. exact (TRANS (@lem1337404 y1 x2 x1) (@lem1337407 x2 x1)). Qed.
Lemma lem1337409 (x2 : hreal) (x1 : hreal) (y1 : hreal) : True = (term399 x2 x1 y1).
Proof. exact (SYM (@lem1337408 x2 x1 y1)). Qed.
Lemma lem1337410 (x2 : hreal) (x1 : hreal) (y1 : hreal) : term399 x2 x1 y1.
Proof. exact (EQ_MP (@lem1337409 x2 x1 y1) (@lem0)). Qed.
Lemma lem1337412 (x2 : hreal) (x1 : hreal) (y1 : hreal) : term348 x2 x1 y1.
Proof. exact (EQ_MP (@lem1337372 x2 x1 y1) (@lem1337410 x2 x1 y1)). Qed.
Lemma lem1337413 (x2 : hreal) (x1 : hreal) (y1 : hreal) : term351 x2 x1 y1.
Proof. exact (fun h0 : term401 x2 x1 y1 => @lem1337412 x2 x1 y1). Qed.
Lemma lem1337414 (x2 : hreal) (x1 : hreal) (y1 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) (h3 : term345 x2 x1 y1) : term353 x2 x1 y1.
Proof. exact (@lem1337354 y1 x1 x2 h1 h2 (@lem1337014 x2 x1 y1 h3)). Qed.
Lemma lem1337415 (x2 : hreal) (x1 : hreal) (y1 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) (h3 : term345 x2 x1 y1) : (term345 x2 x1 y1) = (term353 x2 x1 y1).
Proof. exact (prop_ext (fun h4 : term345 x2 x1 y1 => @lem1337414 x2 x1 y1 h1 h2 h3) (fun h4 : term353 x2 x1 y1 => @lem1337014 x2 x1 y1 h3)). Qed.
Lemma lem1337416 (x2 : hreal) (x1 : hreal) (y1 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) (h3 : term345 x2 x1 y1) : term353 x2 x1 y1.
Proof. exact (EQ_MP (@lem1337415 x2 x1 y1 h1 h2 h3) (@lem1337014 x2 x1 y1 h3)). Qed.
Lemma lem1337417 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) : term356 x2 x1 y1.
Proof. exact (fun h0 : term345 x2 x1 y1 => @lem1337416 x2 x1 y1 h1 h2 h0). Qed.
Lemma lem1337418 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) : term359 x2 x1 y1.
Proof. exact (conj (@lem1337417 y1 x1 x2 h1 h2) (@lem1337413 x2 x1 y1)). Qed.
Lemma lem1337420 (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) : term334 x2 x1 y1.
Proof. exact (EQ_MP (@lem1337013 x2 x1 y1) (@lem1337418 y1 x1 x2 h1 h2)). Qed.
Lemma lem1337421 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : y2 = (term265 x2 x1 y1)) (h3 : hreal_le x1 x2) : term329 x2 x1 y2 y1.
Proof. exact (EQ_MP (@lem1336965 y2 x2 x1 y1 h2) (@lem1337420 y1 x1 x2 h1 h3)). Qed.
Lemma lem1337422 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) : term330 x2 x1 y2 y1.
Proof. exact (fun h0 : y2 = (term265 x2 x1 y1) => @lem1337421 y2 y1 x1 x2 h1 h0 h2). Qed.
Lemma lem1337423 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) : term318 x2 x1 y2 y1.
Proof. exact (EQ_MP (@lem1336951 x2 x1 y2 y1) (@lem1337422 y2 y1 x1 x2 h1 h2)). Qed.
Lemma lem1337424 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : hreal_le x1 x2) : term320 x2 x1 y2 y1.
Proof. exact (EQ_MP (@lem1336884 y2 y1 x1 x2 h2) (@lem1337423 y2 y1 x1 x2 h1 h2)). Qed.
Lemma lem1337425 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : (hreal_add x1 y2) = (hreal_add x2 y1)) (h3 : hreal_le x1 x2) : term248 x2 x1 y2 y1.
Proof. exact (@lem1337424 y2 y1 x1 x2 h1 h3 (@lem1336108 x1 y2 x2 y1 h2)). Qed.
Lemma lem1337427 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) (h1 : term124 x1 x2) (h2 : (hreal_add x1 y2) = (hreal_add x2 y1)) : term402 x2 x1 y2 y1.
Proof. exact (fun h0 : hreal_le x1 x2 => @lem1337425 y2 y1 x1 x2 h1 h2 h0). Qed.
Lemma lem1337428 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : term116 x2 x1) (h2 : hreal_le x2 x1) : term248 x2 x1 y2 y1.
Proof. exact (@lem1336859 y2 y1 x2 x1 h1 (@lem1335055 x2 x1 h2)). Qed.
Lemma lem1337429 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : (hreal_add x1 y2) = (hreal_add x2 y1)) (h3 : hreal_le x1 x2) : term248 x2 x1 y2 y1.
Proof. exact (@lem1337427 x1 y2 x2 y1 h1 h2 (@lem1335054 x1 x2 h3)). Qed.
Lemma lem1337430 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) (h1 : term124 x1 x2) (h2 : term116 x2 x1) (h3 : (hreal_add x1 y2) = (hreal_add x2 y1)) : term248 x2 x1 y2 y1.
Proof. exact (or_elim (@lem1335053 x2 x1) (fun h0 : hreal_le x1 x2 => @lem1337429 y2 y1 x1 x2 h1 h3 h0) (fun h0 : hreal_le x2 x1 => @lem1337428 y2 y1 x2 x1 h2 h0)). Qed.
Lemma lem1337431 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) (h1 : term124 x1 x2) (h2 : term116 x2 x1) (h3 : (hreal_add x1 y2) = (hreal_add x2 y1)) : term227 x2 x1 y2 y1.
Proof. exact (EQ_MP (@lem1336536 y2 y1 x2 x1 h2) (@lem1337430 x1 y2 x2 y1 h1 h2 h3)). Qed.
Lemma lem1337432 (y2 : hreal) (y1 : hreal) (x2 : hreal) (x1 : hreal) (h1 : (hreal_add x1 y2) = (hreal_add x2 y1)) (h2 : hreal_le x2 x1) : term227 x2 x1 y2 y1.
Proof. exact (EQ_MP (@lem1336470 y2 y1 x2 x1 h2) (@lem1336761 y2 y1 x2 x1 h1 h2)). Qed.
Lemma lem1337434 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) (h1 : term124 x1 x2) (h2 : (hreal_add x1 y2) = (hreal_add x2 y1)) : term227 x2 x1 y2 y1.
Proof. exact (or_elim (@lem1335153 x2 x1) (fun h0 : hreal_le x2 x1 => @lem1337432 y2 y1 x2 x1 h2 h0) (fun h0 : term116 x2 x1 => @lem1337431 x1 y2 x2 y1 h1 h0 h2)). Qed.
Lemma lem1337436 (x2 : hreal) (x1 : hreal) : term236 x2 x1.
Proof. exact (fun h0 : x1 = x2 => @lem1336336 x1 x2 h0). Qed.
Lemma lem1337437 (y2 : hreal) (y1 : hreal) : term233 y2 y1.
Proof. exact (fun h0 : y2 = y1 => @lem1336222 y2 y1 h0). Qed.
Lemma lem1337438 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : term403 x2 x1 y2 y1.
Proof. exact (fun h0 : (hreal_add x1 y2) = (hreal_add x2 y1) => @lem1337434 x1 y2 x2 y1 h1 h0). Qed.
Lemma lem1337439 (y2 : hreal) (x2 : hreal) (x1 : hreal) : term235 y2 x2 x1.
Proof. exact (EQ_MP (@lem1336077 y2 x2 x1) (@lem1337436 x2 x1)). Qed.
Lemma lem1337440 (x2 : hreal) (y2 : hreal) (y1 : hreal) : term232 x2 y2 y1.
Proof. exact (EQ_MP (@lem1336051 x2 y2 y1) (@lem1337437 y2 y1)). Qed.
Lemma lem1337441 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) (h2 : (hreal_add x1 y2) = (hreal_add y1 x2)) : term227 x2 x1 y2 y1.
Proof. exact (@lem1337438 y2 y1 x1 x2 h1 (@lem1336023 x1 y2 y1 x2 h2)). Qed.
Lemma lem1337443 (x1 : hreal) (y2 : hreal) (x2 : hreal) (h1 : (hreal_add x1 y2) = (hreal_add y2 x2)) : term225 x2 x1.
Proof. exact (@lem1337439 y2 x2 x1 (@lem1336016 x1 y2 x2 h1)). Qed.
Lemma lem1337445 (y2 : hreal) (y1 : hreal) (x2 : hreal) (h1 : (hreal_add x2 y2) = (hreal_add y1 x2)) : term221 y2 y1.
Proof. exact (@lem1337440 x2 y2 y1 (@lem1336009 y2 y1 x2 h1)). Qed.
Lemma lem1337447 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : term228 x2 x1 y2 y1.
Proof. exact (fun h0 : (hreal_add x1 y2) = (hreal_add y1 x2) => @lem1337441 x1 y2 y1 x2 h1 h0). Qed.
Lemma lem1337448 (y2 : hreal) (x2 : hreal) (x1 : hreal) : term226 y2 x2 x1.
Proof. exact (fun h0 : (hreal_add x1 y2) = (hreal_add y2 x2) => @lem1337443 x1 y2 x2 h0). Qed.
Lemma lem1337449 (x2 : hreal) (y2 : hreal) (y1 : hreal) : term222 x2 y2 y1.
Proof. exact (fun h0 : (hreal_add x2 y2) = (hreal_add y1 x2) => @lem1337445 y2 y1 x2 h0). Qed.
Lemma lem1337450 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : term124 x1 x2) (h2 : term124 y1 y2) : term188 x2 x1 y2 y1.
Proof. exact (EQ_MP (@lem1335921 x1 x2 y1 y2 h1 h2) (@lem1337447 y2 y1 x1 x2 h1)). Qed.
Lemma lem1337451 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : term124 x1 x2) (h2 : y1 = y2) : term188 x2 x1 y2 y1.
Proof. exact (EQ_MP (@lem1335817 x1 x2 y1 y2 h1 h2) (@lem1337448 y2 x2 x1)). Qed.
Lemma lem1337452 (y1 : hreal) (y2 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 y1 y2) (h2 : x1 = x2) : term188 x2 x1 y2 y1.
Proof. exact (EQ_MP (@lem1335667 y1 y2 x1 x2 h1 h2) (@lem1337449 x2 y2 y1)). Qed.
Lemma lem1337453 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) (h1 : x1 = x2) (h2 : y1 = y2) : term188 x2 x1 y2 y1.
Proof. exact (EQ_MP (@lem1335515 x1 x2 y1 y2 h1 h2) (@lem1335940 y2 x2)). Qed.
Lemma lem1337454 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : term124 x1 x2) : term188 x2 x1 y2 y1.
Proof. exact (or_elim (@lem1335187 y1 y2) (fun h0 : y1 = y2 => @lem1337451 x1 x2 y1 y2 h1 h0) (fun h0 : term124 y1 y2 => @lem1337450 x1 x2 y1 y2 h1 h0)). Qed.
Lemma lem1337455 (y2 : hreal) (y1 : hreal) (x1 : hreal) (x2 : hreal) (h1 : x1 = x2) : term188 x2 x1 y2 y1.
Proof. exact (or_elim (@lem1335187 y1 y2) (fun h0 : y1 = y2 => @lem1337453 x1 x2 y1 y2 h1 h0) (fun h0 : term124 y1 y2 => @lem1337452 y1 y2 x1 x2 h0 h1)). Qed.
Lemma lem1337456 (x2 : hreal) (x1 : hreal) (y2 : hreal) (y1 : hreal) : term188 x2 x1 y2 y1.
Proof. exact (or_elim (@lem1335192 x1 x2) (fun h0 : x1 = x2 => @lem1337455 y2 y1 x1 x2 h0) (fun h0 : term124 x1 x2 => @lem1337454 y2 y1 x1 x2 h0)). Qed.
Lemma lem1337457 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : term170 x1 x2 y1 y2.
Proof. exact (EQ_MP (@lem1335323 x1 x2 y1 y2) (@lem1337456 x2 x1 y2 y1)). Qed.
Lemma lem1337462 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term174 x1 x2 y1.
Proof. exact (fun y2 : hreal => @lem1337457 x1 x2 y1 y2). Qed.
Lemma lem1337467 (x1 : hreal) (x2 : hreal) : term177 x1 x2.
Proof. exact (fun y1 : hreal => @lem1337462 x1 x2 y1). Qed.
Lemma lem1337472 (x1 : hreal) : term179 x1.
Proof. exact (fun x2 : hreal => @lem1337467 x1 x2). Qed.
Lemma lem1337477 : term181.
Proof. exact (fun x1 : hreal => @lem1337472 x1). Qed.
Lemma lem1337478 : term149.
Proof. exact (EQ_MP (@lem1335307) (@lem1337477)). Qed.
