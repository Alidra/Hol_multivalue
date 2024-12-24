Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_1_term_abbrevs.
Require Import LT_NZ_spec.
Require Import NOT_LT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm80360_spec.
Require Import thm89994_spec.
Lemma lem98734 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.le n m)) : (term0 m n) = (Peano.le n m).
Proof. exact (h1). Qed.
Lemma lem98735 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.le n m)) : (Peano.le n m) = (term0 m n).
Proof. exact (SYM (@lem98734 n m h1)). Qed.
Lemma lem98736 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term0 m n)) : (Peano.le n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem98737 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term0 m n)) : (term0 m n) = (Peano.le n m).
Proof. exact (SYM (@lem98736 m n h1)). Qed.
Lemma lem98738 (m : nat) (n : nat) : ((term0 m n) = (Peano.le n m)) = ((Peano.le n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.le n m) => @lem98735 n m h1) (fun h1 : (Peano.le n m) = (term0 m n) => @lem98737 m n h1)). Qed.
Lemma lem98739 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem98738 m n)). Qed.
Lemma lem98740 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98741 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem98740) (@lem98739 m)). Qed.
Lemma lem98742 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem98741 m)). Qed.
Lemma lem98743 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98744 : term7 = term8.
Proof. exact (MK_COMB (@lem98743) (@lem98742)). Qed.
Lemma lem98745 : term8.
Proof. exact (EQ_MP (@lem98744) (@lem98377)). Qed.
Lemma lem98746 : term9.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem98747 (m : nat) : term10 m.
Proof. exact (@lem98746 m). Qed.
Lemma lem98748 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem98749 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem98748 m) (@lem98747 m)). Qed.
Lemma lem98750 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem98749 m n). Qed.
Lemma lem98751 (m : nat) (n : nat) : (term12 m n) = ((term13 m n) = (term14 m n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem98753 : term15.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem98754 (m : nat) : term16 m.
Proof. exact (@lem98753 m). Qed.
Lemma lem98755 (m : nat) : (term16 m) = ((term17 m) = False).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem98757 (m : nat) : term18 m.
Proof. exact (@lem98745 m). Qed.
Lemma lem98758 (m : nat) : (term18 m) = (term4 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem98759 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem98758 m) (@lem98757 m)). Qed.
Lemma lem98760 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem98759 m n). Qed.
Lemma lem98761 (m : nat) (n : nat) : (term19 m n) = ((Peano.le n m) = (term0 m n)).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem98763 (n : nat) : term20 n.
Proof. exact (@lem98731 n). Qed.
Lemma lem98764 (n : nat) : (term20 n) = ((term21 n) = (term22 n)).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem98777 (n : nat) : (term21 n) = (term22 n).
Proof. exact (EQ_MP (@lem98764 n) (@lem98763 n)). Qed.
Lemma lem98780 (n : nat) : (term23 n) = (term23 n).
Proof. exact (eq_refl (term23 n)). Qed.
Lemma lem98781 (n : nat) : (term24 n) = (term25 n).
Proof. exact (MK_COMB (@lem98780 n) (@lem98777 n)). Qed.
Lemma lem98783 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem98784 (n : nat) : (term25 n) = True.
Proof. exact (@lem98783 (term22 n)). Qed.
Lemma lem98785 (n : nat) : (term24 n) = True.
Proof. exact (TRANS (@lem98781 n) (@lem98784 n)). Qed.
Lemma lem98786 : term26 = term27.
Proof. exact (fun_ext (fun n : nat => @lem98785 n)). Qed.
Lemma lem98787 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98788 : term28 = term29.
Proof. exact (MK_COMB (@lem98787) (@lem98786)). Qed.
Lemma lem98790 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem98791 (t : Prop) : (term31 t) = t.
Proof. exact (@lem98790 nat t). Qed.
Lemma lem98792 : term29 = True.
Proof. exact (@lem98791 True). Qed.
Lemma lem98793 : term28 = True.
Proof. exact (TRANS (@lem98788) (@lem98792)). Qed.
Lemma lem98794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem98795 : term32 = (and True).
Proof. exact (MK_COMB (@lem98794) (@lem98793)). Qed.
Lemma lem98807 (m : nat) (n : nat) : (Peano.le n m) = (term0 m n).
Proof. exact (EQ_MP (@lem98761 m n) (@lem98760 m n)). Qed.
Lemma lem98808 (n : nat) : (term33 n) = (term34 n).
Proof. exact (@lem98807 n term35). Qed.
Lemma lem98810 : term35 = term36.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem98811 (n : nat) : (Peano.lt n) = (Peano.lt n).
Proof. exact (eq_refl (Peano.lt n)). Qed.
Lemma lem98812 (n : nat) : (term37 n) = (term38 n).
Proof. exact (MK_COMB (@lem98811 n) (@lem98810)). Qed.
Lemma lem98814 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem98751 m n) (@lem98750 m n)). Qed.
Lemma lem98815 (n : nat) : (term38 n) = (term39 n).
Proof. exact (@lem98814 n (NUMERAL 0)). Qed.
Lemma lem98821 (m : nat) : (term17 m) = False.
Proof. exact (EQ_MP (@lem98755 m) (@lem98754 m)). Qed.
Lemma lem98822 (n : nat) : (term17 n) = False.
Proof. exact (@lem98821 n). Qed.
Lemma lem98823 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem98824 (n : nat) : (term39 n) = (term41 n).
Proof. exact (MK_COMB (@lem98823 n) (@lem98822 n)). Qed.
Lemma lem98826 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem98827 (n : nat) : (term41 n) = (n = (NUMERAL 0)).
Proof. exact (@lem98826 (n = (NUMERAL 0))). Qed.
Lemma lem98830 (n : nat) : (term39 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem98824 n) (@lem98827 n)). Qed.
Lemma lem98831 (n : nat) : (term38 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem98815 n) (@lem98830 n)). Qed.
Lemma lem98832 (n : nat) : (term37 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem98812 n) (@lem98831 n)). Qed.
Lemma lem98833 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem98834 (n : nat) : (term34 n) = (term22 n).
Proof. exact (MK_COMB (@lem98833) (@lem98832 n)). Qed.
Lemma lem98835 (n : nat) : (term33 n) = (term22 n).
Proof. exact (TRANS (@lem98808 n) (@lem98834 n)). Qed.
Lemma lem98836 (n : nat) : (term23 n) = (term23 n).
Proof. exact (eq_refl (term23 n)). Qed.
Lemma lem98837 (n : nat) : (term42 n) = (term25 n).
Proof. exact (MK_COMB (@lem98836 n) (@lem98835 n)). Qed.
Lemma lem98839 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem98840 (n : nat) : (term25 n) = True.
Proof. exact (@lem98839 (term22 n)). Qed.
Lemma lem98841 (n : nat) : (term42 n) = True.
Proof. exact (TRANS (@lem98837 n) (@lem98840 n)). Qed.
Lemma lem98842 : term43 = term27.
Proof. exact (fun_ext (fun n : nat => @lem98841 n)). Qed.
Lemma lem98843 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98844 : term44 = term29.
Proof. exact (MK_COMB (@lem98843) (@lem98842)). Qed.
Lemma lem98846 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem98847 (t : Prop) : (term31 t) = t.
Proof. exact (@lem98846 nat t). Qed.
Lemma lem98848 : term29 = True.
Proof. exact (@lem98847 True). Qed.
Lemma lem98849 : term44 = True.
Proof. exact (TRANS (@lem98844) (@lem98848)). Qed.
Lemma lem98850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem98851 : term45 = (and True).
Proof. exact (MK_COMB (@lem98850) (@lem98849)). Qed.
Lemma lem98861 (n : nat) : (term21 n) = (term22 n).
Proof. exact (EQ_MP (@lem98764 n) (@lem98763 n)). Qed.
Lemma lem98864 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem98865 (n : nat) : (term46 n) = (term23 n).
Proof. exact (MK_COMB (@lem98864) (@lem98861 n)). Qed.
Lemma lem98868 (n : nat) : (term22 n) = (term22 n).
Proof. exact (eq_refl (term22 n)). Qed.
Lemma lem98869 (n : nat) : (term47 n) = (term25 n).
Proof. exact (MK_COMB (@lem98865 n) (@lem98868 n)). Qed.
Lemma lem98871 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem98872 (n : nat) : (term25 n) = True.
Proof. exact (@lem98871 (term22 n)). Qed.
Lemma lem98873 (n : nat) : (term47 n) = True.
Proof. exact (TRANS (@lem98869 n) (@lem98872 n)). Qed.
Lemma lem98874 : term48 = term27.
Proof. exact (fun_ext (fun n : nat => @lem98873 n)). Qed.
Lemma lem98875 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98876 : term49 = term29.
Proof. exact (MK_COMB (@lem98875) (@lem98874)). Qed.
Lemma lem98878 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem98879 (t : Prop) : (term31 t) = t.
Proof. exact (@lem98878 nat t). Qed.
Lemma lem98880 : term29 = True.
Proof. exact (@lem98879 True). Qed.
Lemma lem98881 : term49 = True.
Proof. exact (TRANS (@lem98876) (@lem98880)). Qed.
Lemma lem98882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem98883 : term50 = (and True).
Proof. exact (MK_COMB (@lem98882) (@lem98881)). Qed.
Lemma lem98893 (n : nat) : (term21 n) = (term22 n).
Proof. exact (EQ_MP (@lem98764 n) (@lem98763 n)). Qed.
Lemma lem98896 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem98897 (n : nat) : (term46 n) = (term23 n).
Proof. exact (MK_COMB (@lem98896) (@lem98893 n)). Qed.
Lemma lem98899 (m : nat) (n : nat) : (Peano.le n m) = (term0 m n).
Proof. exact (EQ_MP (@lem98761 m n) (@lem98760 m n)). Qed.
Lemma lem98900 (n : nat) : (term33 n) = (term34 n).
Proof. exact (@lem98899 n term35). Qed.
Lemma lem98902 : term35 = term36.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem98903 (n : nat) : (Peano.lt n) = (Peano.lt n).
Proof. exact (eq_refl (Peano.lt n)). Qed.
Lemma lem98904 (n : nat) : (term37 n) = (term38 n).
Proof. exact (MK_COMB (@lem98903 n) (@lem98902)). Qed.
Lemma lem98906 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem98751 m n) (@lem98750 m n)). Qed.
Lemma lem98907 (n : nat) : (term38 n) = (term39 n).
Proof. exact (@lem98906 n (NUMERAL 0)). Qed.
Lemma lem98913 (m : nat) : (term17 m) = False.
Proof. exact (EQ_MP (@lem98755 m) (@lem98754 m)). Qed.
Lemma lem98914 (n : nat) : (term17 n) = False.
Proof. exact (@lem98913 n). Qed.
Lemma lem98915 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem98916 (n : nat) : (term39 n) = (term41 n).
Proof. exact (MK_COMB (@lem98915 n) (@lem98914 n)). Qed.
Lemma lem98918 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem98919 (n : nat) : (term41 n) = (n = (NUMERAL 0)).
Proof. exact (@lem98918 (n = (NUMERAL 0))). Qed.
Lemma lem98922 (n : nat) : (term39 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem98916 n) (@lem98919 n)). Qed.
Lemma lem98923 (n : nat) : (term38 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem98907 n) (@lem98922 n)). Qed.
Lemma lem98924 (n : nat) : (term37 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem98904 n) (@lem98923 n)). Qed.
Lemma lem98925 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem98926 (n : nat) : (term34 n) = (term22 n).
Proof. exact (MK_COMB (@lem98925) (@lem98924 n)). Qed.
Lemma lem98927 (n : nat) : (term33 n) = (term22 n).
Proof. exact (TRANS (@lem98900 n) (@lem98926 n)). Qed.
Lemma lem98928 (n : nat) : (term51 n) = (term25 n).
Proof. exact (MK_COMB (@lem98897 n) (@lem98927 n)). Qed.
Lemma lem98930 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem98931 (n : nat) : (term25 n) = True.
Proof. exact (@lem98930 (term22 n)). Qed.
Lemma lem98932 (n : nat) : (term51 n) = True.
Proof. exact (TRANS (@lem98928 n) (@lem98931 n)). Qed.
Lemma lem98933 : term52 = term27.
Proof. exact (fun_ext (fun n : nat => @lem98932 n)). Qed.
Lemma lem98934 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98935 : term53 = term29.
Proof. exact (MK_COMB (@lem98934) (@lem98933)). Qed.
Lemma lem98937 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem98938 (t : Prop) : (term31 t) = t.
Proof. exact (@lem98937 nat t). Qed.
Lemma lem98939 : term29 = True.
Proof. exact (@lem98938 True). Qed.
Lemma lem98940 : term53 = True.
Proof. exact (TRANS (@lem98935) (@lem98939)). Qed.
Lemma lem98941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem98942 : term54 = (and True).
Proof. exact (MK_COMB (@lem98941) (@lem98940)). Qed.
Lemma lem98952 (m : nat) (n : nat) : (Peano.le n m) = (term0 m n).
Proof. exact (EQ_MP (@lem98761 m n) (@lem98760 m n)). Qed.
Lemma lem98953 (n : nat) : (term33 n) = (term34 n).
Proof. exact (@lem98952 n term35). Qed.
Lemma lem98955 : term35 = term36.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem98956 (n : nat) : (Peano.lt n) = (Peano.lt n).
Proof. exact (eq_refl (Peano.lt n)). Qed.
Lemma lem98957 (n : nat) : (term37 n) = (term38 n).
Proof. exact (MK_COMB (@lem98956 n) (@lem98955)). Qed.
Lemma lem98959 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem98751 m n) (@lem98750 m n)). Qed.
Lemma lem98960 (n : nat) : (term38 n) = (term39 n).
Proof. exact (@lem98959 n (NUMERAL 0)). Qed.
Lemma lem98966 (m : nat) : (term17 m) = False.
Proof. exact (EQ_MP (@lem98755 m) (@lem98754 m)). Qed.
Lemma lem98967 (n : nat) : (term17 n) = False.
Proof. exact (@lem98966 n). Qed.
Lemma lem98968 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem98969 (n : nat) : (term39 n) = (term41 n).
Proof. exact (MK_COMB (@lem98968 n) (@lem98967 n)). Qed.
Lemma lem98971 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem98972 (n : nat) : (term41 n) = (n = (NUMERAL 0)).
Proof. exact (@lem98971 (n = (NUMERAL 0))). Qed.
Lemma lem98975 (n : nat) : (term39 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem98969 n) (@lem98972 n)). Qed.
Lemma lem98976 (n : nat) : (term38 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem98960 n) (@lem98975 n)). Qed.
Lemma lem98977 (n : nat) : (term37 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem98957 n) (@lem98976 n)). Qed.
Lemma lem98978 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem98979 (n : nat) : (term34 n) = (term22 n).
Proof. exact (MK_COMB (@lem98978) (@lem98977 n)). Qed.
Lemma lem98980 (n : nat) : (term33 n) = (term22 n).
Proof. exact (TRANS (@lem98953 n) (@lem98979 n)). Qed.
Lemma lem98981 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem98982 (n : nat) : (term55 n) = (term23 n).
Proof. exact (MK_COMB (@lem98981) (@lem98980 n)). Qed.
Lemma lem98984 (n : nat) : (term21 n) = (term22 n).
Proof. exact (EQ_MP (@lem98764 n) (@lem98763 n)). Qed.
Lemma lem98987 (n : nat) : (term56 n) = (term25 n).
Proof. exact (MK_COMB (@lem98982 n) (@lem98984 n)). Qed.
Lemma lem98989 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem98990 (n : nat) : (term25 n) = True.
Proof. exact (@lem98989 (term22 n)). Qed.
Lemma lem98991 (n : nat) : (term56 n) = True.
Proof. exact (TRANS (@lem98987 n) (@lem98990 n)). Qed.
Lemma lem98992 : term57 = term27.
Proof. exact (fun_ext (fun n : nat => @lem98991 n)). Qed.
Lemma lem98993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98994 : term58 = term29.
Proof. exact (MK_COMB (@lem98993) (@lem98992)). Qed.
Lemma lem98996 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem98997 (t : Prop) : (term31 t) = t.
Proof. exact (@lem98996 nat t). Qed.
Lemma lem98998 : term29 = True.
Proof. exact (@lem98997 True). Qed.
Lemma lem98999 : term58 = True.
Proof. exact (TRANS (@lem98994) (@lem98998)). Qed.
Lemma lem99000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem99001 : term59 = (and True).
Proof. exact (MK_COMB (@lem99000) (@lem98999)). Qed.
Lemma lem99009 (m : nat) (n : nat) : (Peano.le n m) = (term0 m n).
Proof. exact (EQ_MP (@lem98761 m n) (@lem98760 m n)). Qed.
Lemma lem99010 (n : nat) : (term33 n) = (term34 n).
Proof. exact (@lem99009 n term35). Qed.
Lemma lem99012 : term35 = term36.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem99013 (n : nat) : (Peano.lt n) = (Peano.lt n).
Proof. exact (eq_refl (Peano.lt n)). Qed.
Lemma lem99014 (n : nat) : (term37 n) = (term38 n).
Proof. exact (MK_COMB (@lem99013 n) (@lem99012)). Qed.
Lemma lem99016 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem98751 m n) (@lem98750 m n)). Qed.
Lemma lem99017 (n : nat) : (term38 n) = (term39 n).
Proof. exact (@lem99016 n (NUMERAL 0)). Qed.
Lemma lem99023 (m : nat) : (term17 m) = False.
Proof. exact (EQ_MP (@lem98755 m) (@lem98754 m)). Qed.
Lemma lem99024 (n : nat) : (term17 n) = False.
Proof. exact (@lem99023 n). Qed.
Lemma lem99025 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem99026 (n : nat) : (term39 n) = (term41 n).
Proof. exact (MK_COMB (@lem99025 n) (@lem99024 n)). Qed.
Lemma lem99028 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem99029 (n : nat) : (term41 n) = (n = (NUMERAL 0)).
Proof. exact (@lem99028 (n = (NUMERAL 0))). Qed.
Lemma lem99032 (n : nat) : (term39 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem99026 n) (@lem99029 n)). Qed.
Lemma lem99033 (n : nat) : (term38 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem99017 n) (@lem99032 n)). Qed.
Lemma lem99034 (n : nat) : (term37 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem99014 n) (@lem99033 n)). Qed.
Lemma lem99035 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem99036 (n : nat) : (term34 n) = (term22 n).
Proof. exact (MK_COMB (@lem99035) (@lem99034 n)). Qed.
Lemma lem99037 (n : nat) : (term33 n) = (term22 n).
Proof. exact (TRANS (@lem99010 n) (@lem99036 n)). Qed.
Lemma lem99038 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem99039 (n : nat) : (term55 n) = (term23 n).
Proof. exact (MK_COMB (@lem99038) (@lem99037 n)). Qed.
Lemma lem99042 (n : nat) : (term22 n) = (term22 n).
Proof. exact (eq_refl (term22 n)). Qed.
Lemma lem99043 (n : nat) : (term60 n) = (term25 n).
Proof. exact (MK_COMB (@lem99039 n) (@lem99042 n)). Qed.
Lemma lem99045 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem99046 (n : nat) : (term25 n) = True.
Proof. exact (@lem99045 (term22 n)). Qed.
Lemma lem99047 (n : nat) : (term60 n) = True.
Proof. exact (TRANS (@lem99043 n) (@lem99046 n)). Qed.
Lemma lem99048 : term61 = term27.
Proof. exact (fun_ext (fun n : nat => @lem99047 n)). Qed.
Lemma lem99049 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem99050 : term62 = term29.
Proof. exact (MK_COMB (@lem99049) (@lem99048)). Qed.
Lemma lem99052 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem99053 (t : Prop) : (term31 t) = t.
Proof. exact (@lem99052 nat t). Qed.
Lemma lem99054 : term29 = True.
Proof. exact (@lem99053 True). Qed.
Lemma lem99055 : term62 = True.
Proof. exact (TRANS (@lem99050) (@lem99054)). Qed.
Lemma lem99056 : term63 = (True /\ True).
Proof. exact (MK_COMB (@lem99001) (@lem99055)). Qed.
Lemma lem99058 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem99059 : (True /\ True) = True.
Proof. exact (@lem99058 True). Qed.
Lemma lem99060 : term63 = True.
Proof. exact (TRANS (@lem99056) (@lem99059)). Qed.
Lemma lem99061 : term64 = (True /\ True).
Proof. exact (MK_COMB (@lem98942) (@lem99060)). Qed.
Lemma lem99063 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem99064 : (True /\ True) = True.
Proof. exact (@lem99063 True). Qed.
Lemma lem99065 : term64 = True.
Proof. exact (TRANS (@lem99061) (@lem99064)). Qed.
Lemma lem99066 : term65 = (True /\ True).
Proof. exact (MK_COMB (@lem98883) (@lem99065)). Qed.
Lemma lem99068 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem99069 : (True /\ True) = True.
Proof. exact (@lem99068 True). Qed.
Lemma lem99070 : term65 = True.
Proof. exact (TRANS (@lem99066) (@lem99069)). Qed.
Lemma lem99071 : term66 = (True /\ True).
Proof. exact (MK_COMB (@lem98851) (@lem99070)). Qed.
Lemma lem99073 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem99074 : (True /\ True) = True.
Proof. exact (@lem99073 True). Qed.
Lemma lem99075 : term66 = True.
Proof. exact (TRANS (@lem99071) (@lem99074)). Qed.
Lemma lem99076 : term67 = (True /\ True).
Proof. exact (MK_COMB (@lem98795) (@lem99075)). Qed.
Lemma lem99078 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem99079 : (True /\ True) = True.
Proof. exact (@lem99078 True). Qed.
Lemma lem99080 : term67 = True.
Proof. exact (TRANS (@lem99076) (@lem99079)). Qed.
Lemma lem99081 : True = term67.
Proof. exact (SYM (@lem99080)). Qed.
Lemma lem99082 : term67.
Proof. exact (EQ_MP (@lem99081) (@lem0)). Qed.
