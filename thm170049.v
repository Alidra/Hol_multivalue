Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm170049_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import AND_FORALL_THM_spec.
Require Import DIVMOD_UNIQ_spec.
Require Import DIV_ZERO_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LT_NZ_spec.
Require Import MOD_ZERO_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem169760 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem169761 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem169760 h1 m). Qed.
Lemma lem169762 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem169763 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem169762 m) (@lem169761 m h1)). Qed.
Lemma lem169764 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem169763 m h1 n). Qed.
Lemma lem169765 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem169766 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem169765 m n) (@lem169764 m n h1)). Qed.
Lemma lem169767 (m : nat) (n : nat) (q : nat) (h1 : term0) : term5 m n q.
Proof. exact (@lem169766 m n h1 q). Qed.
Lemma lem169768 (q : nat) (m : nat) (n : nat) : (term5 m n q) = (term6 q m n).
Proof. exact (eq_refl (term5 m n q)). Qed.
Lemma lem169769 (q : nat) (m : nat) (n : nat) (h1 : term0) : term6 q m n.
Proof. exact (EQ_MP (@lem169768 q m n) (@lem169767 m n q h1)). Qed.
Lemma lem169770 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term0) : term7 q m n r.
Proof. exact (@lem169769 q m n h1 r). Qed.
Lemma lem169771 (q : nat) (m : nat) (n : nat) (r : nat) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem169772 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term0) : term8 q m n r.
Proof. exact (EQ_MP (@lem169771 q m n r) (@lem169770 q m n r h1)). Qed.
Lemma lem169773 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term9 m q r n) : term9 m q r n.
Proof. exact (h1). Qed.
Lemma lem169774 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0) (h2 : term9 m q r n) : term10 q m n r.
Proof. exact (@lem169772 q m n r h1 (@lem169773 m q r n h2)). Qed.
Lemma lem169775 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term9 m q r n) : term11 q m n r.
Proof. exact (fun h0 : term0 => @lem169774 m q r n h0 h1). Qed.
Lemma lem169776 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem169777 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0) (h2 : term9 m q r n) : term10 q m n r.
Proof. exact (@lem169775 m q r n h2 (@lem169776 h1)). Qed.
Lemma lem169778 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term0) : term8 q m n r.
Proof. exact (fun h0 : term9 m q r n => @lem169777 m q r n h1 h0). Qed.
Lemma lem169779 (q : nat) (m : nat) (n : nat) (h1 : term0) : term6 q m n.
Proof. exact (fun r : nat => @lem169778 q m n r h1). Qed.
Lemma lem169780 (q : nat) (m : nat) (h1 : term0) : term12 q m.
Proof. exact (fun n : nat => @lem169779 q m n h1). Qed.
Lemma lem169781 (q : nat) (h1 : term0) : term13 q.
Proof. exact (fun m : nat => @lem169780 q m h1). Qed.
Lemma lem169782 (h1 : term0) : term14.
Proof. exact (fun q : nat => @lem169781 q h1). Qed.
Lemma lem169783 : term15.
Proof. exact (fun h0 : term0 => @lem169782 h0). Qed.
Lemma lem169784 : term14.
Proof. exact (@lem169783 (@lem169651)). Qed.
Lemma lem169785 (q : nat) : term16 q.
Proof. exact (@lem169784 q). Qed.
Lemma lem169786 (q : nat) : (term16 q) = (term13 q).
Proof. exact (eq_refl (term16 q)). Qed.
Lemma lem169787 (q : nat) : term13 q.
Proof. exact (EQ_MP (@lem169786 q) (@lem169785 q)). Qed.
Lemma lem169788 (q : nat) (m : nat) : term17 q m.
Proof. exact (@lem169787 q m). Qed.
Lemma lem169789 (q : nat) (m : nat) : (term17 q m) = (term12 q m).
Proof. exact (eq_refl (term17 q m)). Qed.
Lemma lem169790 (q : nat) (m : nat) : term12 q m.
Proof. exact (EQ_MP (@lem169789 q m) (@lem169788 q m)). Qed.
Lemma lem169791 (q : nat) (m : nat) (n : nat) : term18 q m n.
Proof. exact (@lem169790 q m n). Qed.
Lemma lem169792 (q : nat) (m : nat) (n : nat) : (term18 q m n) = (term6 q m n).
Proof. exact (eq_refl (term18 q m n)). Qed.
Lemma lem169793 (q : nat) (m : nat) (n : nat) : term6 q m n.
Proof. exact (EQ_MP (@lem169792 q m n) (@lem169791 q m n)). Qed.
Lemma lem169794 (q : nat) (m : nat) (n : nat) (r : nat) : term7 q m n r.
Proof. exact (@lem169793 q m n r). Qed.
Lemma lem169795 (q : nat) (m : nat) (n : nat) (r : nat) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem169797 (n : nat) : term19 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem169798 (n : nat) : (term19 n) = (term20 n).
Proof. exact (eq_refl (term19 n)). Qed.
Lemma lem169799 (n : nat) : term20 n.
Proof. exact (EQ_MP (@lem169798 n) (@lem169797 n)). Qed.
Lemma lem169801 (n : nat) (h1 : term21 n) : term21 n.
Proof. exact (h1). Qed.
Lemma lem169802 {A : Type'} (P : A -> Prop) : term22 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem169803 {A : Type'} (P : A -> Prop) : (term22 A P) = (term23 A P).
Proof. exact (eq_refl (term22 A P)). Qed.
Lemma lem169804 {A : Type'} (P : A -> Prop) : term23 A P.
Proof. exact (EQ_MP (@lem169803 A P) (@lem169802 A P)). Qed.
Lemma lem169805 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term24 A P Q.
Proof. exact (@lem169804 A P Q). Qed.
Lemma lem169806 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term24 A P Q) = ((term25 A P Q) = (term26 A P Q)).
Proof. exact (eq_refl (term24 A P Q)). Qed.
Lemma lem169809 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term25 A P Q) = (term26 A P Q).
Proof. exact (EQ_MP (@lem169806 A P Q) (@lem169805 A P Q)). Qed.
Lemma lem169810 (P : nat -> Prop) (Q : nat -> Prop) : (term27 P Q) = (term28 P Q).
Proof. exact (@lem169809 nat P Q). Qed.
Lemma lem169811 : term29 = term30.
Proof. exact (@lem169810 term31 term32). Qed.
Lemma lem169812 (n : nat) : (term33 n) = ((term34 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem169813 : term35 = term31.
Proof. exact (fun_ext (fun n : nat => @lem169812 n)). Qed.
Lemma lem169814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem169815 : term36 = term37.
Proof. exact (MK_COMB (@lem169814) (@lem169813)). Qed.
Lemma lem169816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem169817 : term38 = term39.
Proof. exact (MK_COMB (@lem169816) (@lem169815)). Qed.
Lemma lem169818 (n : nat) : (term40 n) = ((term41 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem169819 : term42 = term32.
Proof. exact (fun_ext (fun n : nat => @lem169818 n)). Qed.
Lemma lem169820 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem169821 : term43 = term44.
Proof. exact (MK_COMB (@lem169820) (@lem169819)). Qed.
Lemma lem169822 : term29 = term45.
Proof. exact (MK_COMB (@lem169817) (@lem169821)). Qed.
Lemma lem169823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem169824 : term46 = term47.
Proof. exact (MK_COMB (@lem169823) (@lem169822)). Qed.
Lemma lem169825 (n : nat) : (term33 n) = ((term34 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem169826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem169827 (n : nat) : (term48 n) = (term49 n).
Proof. exact (MK_COMB (@lem169826) (@lem169825 n)). Qed.
Lemma lem169828 (n : nat) : (term40 n) = ((term41 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem169829 (n : nat) : (term50 n) = (term51 n).
Proof. exact (MK_COMB (@lem169827 n) (@lem169828 n)). Qed.
Lemma lem169830 : term52 = term53.
Proof. exact (fun_ext (fun n : nat => @lem169829 n)). Qed.
Lemma lem169831 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem169832 : term30 = term54.
Proof. exact (MK_COMB (@lem169831) (@lem169830)). Qed.
Lemma lem169833 : (term29 = term30) = (term45 = term54).
Proof. exact (MK_COMB (@lem169824) (@lem169832)). Qed.
Lemma lem169834 : term45 = term54.
Proof. exact (EQ_MP (@lem169833) (@lem169811)). Qed.
Lemma lem169845 : term54 = term45.
Proof. exact (SYM (@lem169834)). Qed.
Lemma lem169846 (n : nat) : term55 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem169847 (n : nat) : (term55 n) = ((term56 n) = n).
Proof. exact (eq_refl (term55 n)). Qed.
Lemma lem169849 (n : nat) : term57 n.
Proof. exact (@lem158192 n). Qed.
Lemma lem169850 (n : nat) : (term57 n) = ((term58 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term57 n)). Qed.
Lemma lem169857 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem169858 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem169859 (n : nat) (h1 : n = (NUMERAL 0)) : (term34 n) = term60.
Proof. exact (MK_COMB (@lem169858) (@lem169857 n h1)). Qed.
Lemma lem169861 (n : nat) : (term58 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem169850 n) (@lem169849 n)). Qed.
Lemma lem169862 : term60 = (NUMERAL 0).
Proof. exact (@lem169861 (NUMERAL 0)). Qed.
Lemma lem169863 (n : nat) (h1 : n = (NUMERAL 0)) : (term34 n) = (NUMERAL 0).
Proof. exact (TRANS (@lem169859 n h1) (@lem169862)). Qed.
Lemma lem169864 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem169865 (n : nat) (h1 : n = (NUMERAL 0)) : (term61 n) = term62.
Proof. exact (MK_COMB (@lem169864) (@lem169863 n h1)). Qed.
Lemma lem169866 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem169867 (n : nat) (h1 : n = (NUMERAL 0)) : ((term34 n) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem169865 n h1) (@lem169866)). Qed.
Lemma lem169869 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem169870 (x : nat) : (x = x) = True.
Proof. exact (@lem169869 nat x). Qed.
Lemma lem169871 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem169870 (NUMERAL 0)). Qed.
Lemma lem169872 (n : nat) (h1 : n = (NUMERAL 0)) : ((term34 n) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem169867 n h1) (@lem169871)). Qed.
Lemma lem169873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem169874 (n : nat) (h1 : n = (NUMERAL 0)) : (term49 n) = (and True).
Proof. exact (MK_COMB (@lem169873) (@lem169872 n h1)). Qed.
Lemma lem169878 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem169879 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem169880 (n : nat) (h1 : n = (NUMERAL 0)) : (term41 n) = term64.
Proof. exact (MK_COMB (@lem169879) (@lem169878 n h1)). Qed.
Lemma lem169882 (n : nat) : (term56 n) = n.
Proof. exact (EQ_MP (@lem169847 n) (@lem169846 n)). Qed.
Lemma lem169883 : term64 = (NUMERAL 0).
Proof. exact (@lem169882 (NUMERAL 0)). Qed.
Lemma lem169884 (n : nat) (h1 : n = (NUMERAL 0)) : (term41 n) = (NUMERAL 0).
Proof. exact (TRANS (@lem169880 n h1) (@lem169883)). Qed.
Lemma lem169885 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem169886 (n : nat) (h1 : n = (NUMERAL 0)) : (term65 n) = term62.
Proof. exact (MK_COMB (@lem169885) (@lem169884 n h1)). Qed.
Lemma lem169887 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem169888 (n : nat) (h1 : n = (NUMERAL 0)) : ((term41 n) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem169886 n h1) (@lem169887)). Qed.
Lemma lem169890 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem169891 (x : nat) : (x = x) = True.
Proof. exact (@lem169890 nat x). Qed.
Lemma lem169892 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem169891 (NUMERAL 0)). Qed.
Lemma lem169893 (n : nat) (h1 : n = (NUMERAL 0)) : ((term41 n) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem169888 n h1) (@lem169892)). Qed.
Lemma lem169894 (n : nat) (h1 : n = (NUMERAL 0)) : (term51 n) = (True /\ True).
Proof. exact (MK_COMB (@lem169874 n h1) (@lem169893 n h1)). Qed.
Lemma lem169896 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem169897 : (True /\ True) = True.
Proof. exact (@lem169896 True). Qed.
Lemma lem169898 (n : nat) (h1 : n = (NUMERAL 0)) : (term51 n) = True.
Proof. exact (TRANS (@lem169894 n h1) (@lem169897)). Qed.
Lemma lem169899 (n : nat) (h1 : n = (NUMERAL 0)) : True = (term51 n).
Proof. exact (SYM (@lem169898 n h1)). Qed.
Lemma lem169900 (n : nat) (h1 : n = (NUMERAL 0)) : term51 n.
Proof. exact (EQ_MP (@lem169899 n h1) (@lem0)). Qed.
Lemma lem169929 (q : nat) (m : nat) (n : nat) (r : nat) : term8 q m n r.
Proof. exact (EQ_MP (@lem169795 q m n r) (@lem169794 q m n r)). Qed.
Lemma lem169930 (n : nat) : term66 n.
Proof. exact (@lem169929 (NUMERAL 0) (NUMERAL 0) n (NUMERAL 0)). Qed.
Lemma lem169931 (n : nat) : term67 n.
Proof. exact (@lem98731 n). Qed.
Lemma lem169932 (n : nat) : (term67 n) = ((term68 n) = (term21 n)).
Proof. exact (eq_refl (term67 n)). Qed.
Lemma lem169934 : term69.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem169950 : term70.
Proof. exact (proj1 (@lem169934)). Qed.
Lemma lem169951 (m : nat) : term71 m.
Proof. exact (@lem169950 m). Qed.
Lemma lem169952 (m : nat) : (term71 m) = ((term72 m) = m).
Proof. exact (eq_refl (term71 m)). Qed.
Lemma lem169988 : term73.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem169989 (n : nat) : term74 n.
Proof. exact (@lem169988 n). Qed.
Lemma lem169990 (n : nat) : (term74 n) = ((term75 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term74 n)). Qed.
Lemma lem169992 (n : nat) : term76 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem170010 (m : nat) : (term72 m) = m.
Proof. exact (EQ_MP (@lem169952 m) (@lem169951 m)). Qed.
Lemma lem170011 (n : nat) : (term77 n) = (term75 n).
Proof. exact (@lem170010 (term75 n)). Qed.
Lemma lem170013 (n : nat) : (term75 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem169990 n) (@lem169989 n)). Qed.
Lemma lem170014 (n : nat) : (term77 n) = (NUMERAL 0).
Proof. exact (TRANS (@lem170011 n) (@lem170013 n)). Qed.
Lemma lem170015 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem170016 (n : nat) : ((NUMERAL 0) = (term77 n)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem170015) (@lem170014 n)). Qed.
Lemma lem170018 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem170019 (x : nat) : (x = x) = True.
Proof. exact (@lem170018 nat x). Qed.
Lemma lem170020 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem170019 (NUMERAL 0)). Qed.
Lemma lem170021 (n : nat) : ((NUMERAL 0) = (term77 n)) = True.
Proof. exact (TRANS (@lem170016 n) (@lem170020)). Qed.
Lemma lem170022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem170023 (n : nat) : (term78 n) = (and True).
Proof. exact (MK_COMB (@lem170022) (@lem170021 n)). Qed.
Lemma lem170025 (n : nat) : (term68 n) = (term21 n).
Proof. exact (EQ_MP (@lem169932 n) (@lem169931 n)). Qed.
Lemma lem170027 (n : nat) (h1 : term21 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem169992 n (@lem169801 n h1)). Qed.
Lemma lem170028 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem170029 (n : nat) (h1 : term21 n) : (term21 n) = (~ False).
Proof. exact (MK_COMB (@lem170028) (@lem170027 n h1)). Qed.
Lemma lem170031 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem170032 (n : nat) (h1 : term21 n) : (term21 n) = True.
Proof. exact (TRANS (@lem170029 n h1) (@lem170031)). Qed.
Lemma lem170033 (n : nat) (h1 : term21 n) : (term68 n) = True.
Proof. exact (TRANS (@lem170025 n) (@lem170032 n h1)). Qed.
Lemma lem170034 (n : nat) (h1 : term21 n) : (term79 n) = (True /\ True).
Proof. exact (MK_COMB (@lem170023 n) (@lem170033 n h1)). Qed.
Lemma lem170036 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem170037 : (True /\ True) = True.
Proof. exact (@lem170036 True). Qed.
Lemma lem170038 (n : nat) (h1 : term21 n) : (term79 n) = True.
Proof. exact (TRANS (@lem170034 n h1) (@lem170037)). Qed.
Lemma lem170039 (n : nat) (h1 : term21 n) : True = (term79 n).
Proof. exact (SYM (@lem170038 n h1)). Qed.
Lemma lem170040 (n : nat) (h1 : term21 n) : term79 n.
Proof. exact (EQ_MP (@lem170039 n h1) (@lem0)). Qed.
Lemma lem170042 (n : nat) (h1 : term21 n) : term51 n.
Proof. exact (@lem169930 n (@lem170040 n h1)). Qed.
Lemma lem170043 (n : nat) : term51 n.
Proof. exact (or_elim (@lem169799 n) (fun h0 : n = (NUMERAL 0) => @lem169900 n h0) (fun h0 : term21 n => @lem170042 n h0)). Qed.
Lemma lem170048 : term54.
Proof. exact (fun n : nat => @lem170043 n). Qed.
Lemma lem170049 : term45.
Proof. exact (EQ_MP (@lem169845) (@lem170048)). Qed.
