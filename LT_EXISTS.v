Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_EXISTS_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EXISTS_REFL_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1831_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Lemma lem99711 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem99712 {A : Type'} (x : A) (a : A) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem99711 A x a h1)). Qed.
Lemma lem99713 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem99714 {A : Type'} (a : A) (x : A) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem99713 A a x h1)). Qed.
Lemma lem99715 {A : Type'} (a : A) (x : A) : (x = a) = (a = x).
Proof. exact (prop_ext (fun h1 : x = a => @lem99712 A x a h1) (fun h1 : a = x => @lem99714 A a x h1)). Qed.
Lemma lem99716 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (fun_ext (fun x : A => @lem99715 A a x)). Qed.
Lemma lem99717 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem99718 {A : Type'} (a : A) : (term2 A a) = (term3 A a).
Proof. exact (MK_COMB (@lem99717 A) (@lem99716 A a)). Qed.
Lemma lem99719 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun a : A => @lem99718 A a)). Qed.
Lemma lem99720 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem99721 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem99720 A) (@lem99719 A)). Qed.
Lemma lem99722 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem99721 A) (@lem4363 A)). Qed.
Lemma lem99723 {A : Type'} (a : A) : term8 A a.
Proof. exact (@lem99722 A a). Qed.
Lemma lem99724 {A : Type'} (a : A) : (term8 A a) = (term3 A a).
Proof. exact (eq_refl (term8 A a)). Qed.
Lemma lem99725 {A : Type'} (a : A) : term3 A a.
Proof. exact (EQ_MP (@lem99724 A a) (@lem99723 A a)). Qed.
Lemma lem99726 {A : Type'} (a : A) : (term3 A a) = ((term3 A a) = True).
Proof. exact (@lem7 (term3 A a)). Qed.
Lemma lem99728 (m : nat) : term9 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem99729 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem99730 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem99729 m) (@lem99728 m)). Qed.
Lemma lem99731 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem99730 m n). Qed.
Lemma lem99732 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem99733 (m : nat) (n : nat) : term12 m n.
Proof. exact (EQ_MP (@lem99732 m n) (@lem99731 m n)). Qed.
Lemma lem99734 (m : nat) (n : nat) (p : nat) : term13 m n p.
Proof. exact (@lem99733 m n p). Qed.
Lemma lem99735 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term13 m n p)). Qed.
Lemma lem99737 (m : nat) : term14 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem99738 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem99739 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem99738 m) (@lem99737 m)). Qed.
Lemma lem99740 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem99739 m n). Qed.
Lemma lem99741 (m : nat) (n : nat) : (term16 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem99749 : term17.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem99750 : term18.
Proof. exact (proj2 (@lem99749)). Qed.
Lemma lem99751 : term19.
Proof. exact (proj2 (@lem99750)). Qed.
Lemma lem99752 (m : nat) : term20 m.
Proof. exact (@lem99751 m). Qed.
Lemma lem99753 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem99754 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem99753 m) (@lem99752 m)). Qed.
Lemma lem99755 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem99754 m n). Qed.
Lemma lem99756 (m : nat) (n : nat) : (term22 m n) = ((term23 m n) = (term24 m n)).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem99765 : term25.
Proof. exact (proj1 (@lem99749)). Qed.
Lemma lem99766 (m : nat) : term26 m.
Proof. exact (@lem99765 m). Qed.
Lemma lem99767 (m : nat) : (term26 m) = ((term27 m) = m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem99773 {A : Type'} (P : A -> Prop) : term28 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem99774 {A : Type'} (P : A -> Prop) : (term28 A P) = (term29 A P).
Proof. exact (eq_refl (term28 A P)). Qed.
Lemma lem99775 {A : Type'} (P : A -> Prop) : term29 A P.
Proof. exact (EQ_MP (@lem99774 A P) (@lem99773 A P)). Qed.
Lemma lem99776 {A : Type'} (P : A -> Prop) (Q : Prop) : term30 A P Q.
Proof. exact (@lem99775 A P Q). Qed.
Lemma lem99777 {A : Type'} (P : A -> Prop) (Q : Prop) : (term30 A P Q) = ((term31 A P Q) = (term32 A P Q)).
Proof. exact (eq_refl (term30 A P Q)). Qed.
Lemma lem99803 : term17.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem99819 : term25.
Proof. exact (proj1 (@lem99803)). Qed.
Lemma lem99820 (m : nat) : term26 m.
Proof. exact (@lem99819 m). Qed.
Lemma lem99821 (m : nat) : (term26 m) = ((term27 m) = m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem99829 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem99830 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem99829 n h1)). Qed.
Lemma lem99831 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem99832 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem99831 n h1)). Qed.
Lemma lem99833 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem99830 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem99832 n h1)). Qed.
Lemma lem99834 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem99835 (n : nat) : (term33 n) = (term34 n).
Proof. exact (MK_COMB (@lem99834) (@lem99833 n)). Qed.
Lemma lem99836 : term35 = term36.
Proof. exact (fun_ext (fun n : nat => @lem99835 n)). Qed.
Lemma lem99837 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem99838 : term37 = term38.
Proof. exact (MK_COMB (@lem99837) (@lem99836)). Qed.
Lemma lem99839 : term38.
Proof. exact (EQ_MP (@lem99838) (@lem75570)). Qed.
Lemma lem99840 (n : nat) : term39 n.
Proof. exact (@lem99839 n). Qed.
Lemma lem99841 (n : nat) : (term39 n) = (term34 n).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem99842 (n : nat) : term34 n.
Proof. exact (EQ_MP (@lem99841 n) (@lem99840 n)). Qed.
Lemma lem99843 (n : nat) : term40 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem99856 : term17.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem99857 : term18.
Proof. exact (proj2 (@lem99856)). Qed.
Lemma lem99858 : term19.
Proof. exact (proj2 (@lem99857)). Qed.
Lemma lem99859 (m : nat) : term20 m.
Proof. exact (@lem99858 m). Qed.
Lemma lem99860 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem99861 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem99860 m) (@lem99859 m)). Qed.
Lemma lem99862 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem99861 m n). Qed.
Lemma lem99863 (m : nat) (n : nat) : (term22 m n) = ((term23 m n) = (term24 m n)).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem99880 : term41.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem99881 (m : nat) : term42 m.
Proof. exact (@lem99880 m). Qed.
Lemma lem99882 (m : nat) : (term42 m) = (term43 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem99883 (m : nat) : term43 m.
Proof. exact (EQ_MP (@lem99882 m) (@lem99881 m)). Qed.
Lemma lem99884 (m : nat) (n : nat) : term44 m n.
Proof. exact (@lem99883 m n). Qed.
Lemma lem99885 (m : nat) (n : nat) : (term44 m n) = ((term45 m n) = (term46 m n)).
Proof. exact (eq_refl (term44 m n)). Qed.
Lemma lem99887 : term47.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem99888 (m : nat) : term48 m.
Proof. exact (@lem99887 m). Qed.
Lemma lem99889 (m : nat) : (term48 m) = ((term49 m) = False).
Proof. exact (eq_refl (term48 m)). Qed.
Lemma lem99892 (P : nat -> Prop) : term50 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem99893 (m : nat) : term51 m.
Proof. exact (@lem99892 (term52 m)). Qed.
Lemma lem99894 (m : nat) : (term53 m) = ((term49 m) = (term54 m)).
Proof. exact (eq_refl (term53 m)). Qed.
Lemma lem99895 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem99896 (m : nat) : (term55 m) = (term56 m).
Proof. exact (MK_COMB (@lem99895) (@lem99894 m)). Qed.
Lemma lem99897 (n : nat) (m : nat) : (term57 m n) = ((Peano.lt m n) = (term58 n m)).
Proof. exact (eq_refl (term57 m n)). Qed.
Lemma lem99898 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem99899 (n : nat) (m : nat) : (term59 m n) = (term60 n m).
Proof. exact (MK_COMB (@lem99898) (@lem99897 n m)). Qed.
Lemma lem99900 (n : nat) (m : nat) : (term61 m n) = ((term45 m n) = (term62 n m)).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem99901 (n : nat) (m : nat) : (term63 m n) = (term64 n m).
Proof. exact (MK_COMB (@lem99899 n m) (@lem99900 n m)). Qed.
Lemma lem99902 (m : nat) : (term65 m) = (term66 m).
Proof. exact (fun_ext (fun n : nat => @lem99901 n m)). Qed.
Lemma lem99903 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem99904 (m : nat) : (term67 m) = (term68 m).
Proof. exact (MK_COMB (@lem99903) (@lem99902 m)). Qed.
Lemma lem99905 (m : nat) : (term69 m) = (term70 m).
Proof. exact (MK_COMB (@lem99896 m) (@lem99904 m)). Qed.
Lemma lem99906 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem99907 (m : nat) : (term71 m) = (term72 m).
Proof. exact (MK_COMB (@lem99906) (@lem99905 m)). Qed.
Lemma lem99908 (n : nat) (m : nat) : (term57 m n) = ((Peano.lt m n) = (term58 n m)).
Proof. exact (eq_refl (term57 m n)). Qed.
Lemma lem99909 (m : nat) : (term73 m) = (term52 m).
Proof. exact (fun_ext (fun n : nat => @lem99908 n m)). Qed.
Lemma lem99910 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem99911 (m : nat) : (term74 m) = (term75 m).
Proof. exact (MK_COMB (@lem99910) (@lem99909 m)). Qed.
Lemma lem99912 (m : nat) : (term51 m) = (term76 m).
Proof. exact (MK_COMB (@lem99907 m) (@lem99911 m)). Qed.
Lemma lem99913 (m : nat) : term76 m.
Proof. exact (EQ_MP (@lem99912 m) (@lem99893 m)). Qed.
Lemma lem99918 (m : nat) : (term49 m) = False.
Proof. exact (EQ_MP (@lem99889 m) (@lem99888 m)). Qed.
Lemma lem99919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem99920 (m : nat) : (term77 m) = (@eq Prop False).
Proof. exact (MK_COMB (@lem99919) (@lem99918 m)). Qed.
Lemma lem99928 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (EQ_MP (@lem99863 m n) (@lem99862 m n)). Qed.
Lemma lem99929 (m : nat) (d : nat) : (term23 m d) = (term24 m d).
Proof. exact (@lem99928 m d). Qed.
Lemma lem99930 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem99931 (m : nat) (d : nat) : ((NUMERAL 0) = (term23 m d)) = ((NUMERAL 0) = (term24 m d)).
Proof. exact (MK_COMB (@lem99930) (@lem99929 m d)). Qed.
Lemma lem99933 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem99843 n (@lem99842 n)). Qed.
Lemma lem99934 (m : nat) (d : nat) : ((NUMERAL 0) = (term24 m d)) = False.
Proof. exact (@lem99933 (Nat.add m d)). Qed.
Lemma lem99935 (m : nat) (d : nat) : ((NUMERAL 0) = (term23 m d)) = False.
Proof. exact (TRANS (@lem99931 m d) (@lem99934 m d)). Qed.
Lemma lem99936 (m : nat) : (term79 m) = term80.
Proof. exact (fun_ext (fun d : nat => @lem99935 m d)). Qed.
Lemma lem99937 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem99938 (m : nat) : (term54 m) = term81.
Proof. exact (MK_COMB (@lem99937) (@lem99936 m)). Qed.
Lemma lem99940 {A : Type'} (t : Prop) : (term82 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem99941 (t : Prop) : (term83 t) = t.
Proof. exact (@lem99940 nat t). Qed.
Lemma lem99942 : term81 = False.
Proof. exact (@lem99941 False). Qed.
Lemma lem99943 (m : nat) : (term54 m) = False.
Proof. exact (TRANS (@lem99938 m) (@lem99942)). Qed.
Lemma lem99944 (m : nat) : ((term49 m) = (term54 m)) = (False = False).
Proof. exact (MK_COMB (@lem99920 m) (@lem99943 m)). Qed.
Lemma lem99946 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem99947 : (False = False) = (~ False).
Proof. exact (@lem99946 False). Qed.
Lemma lem99949 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem99950 : (False = False) = True.
Proof. exact (TRANS (@lem99947) (@lem99949)). Qed.
Lemma lem99951 (m : nat) : ((term49 m) = (term54 m)) = True.
Proof. exact (TRANS (@lem99944 m) (@lem99950)). Qed.
Lemma lem99952 (m : nat) : True = ((term49 m) = (term54 m)).
Proof. exact (SYM (@lem99951 m)). Qed.
Lemma lem99953 (m : nat) : (term49 m) = (term54 m).
Proof. exact (EQ_MP (@lem99952 m) (@lem0)). Qed.
Lemma lem99957 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (EQ_MP (@lem99885 m n) (@lem99884 m n)). Qed.
Lemma lem99962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem99963 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem99962) (@lem99957 m n)). Qed.
Lemma lem99971 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (EQ_MP (@lem99863 m n) (@lem99862 m n)). Qed.
Lemma lem99972 (m : nat) (d : nat) : (term23 m d) = (term24 m d).
Proof. exact (@lem99971 m d). Qed.
Lemma lem99973 (n : nat) : (term86 n) = (term86 n).
Proof. exact (eq_refl (term86 n)). Qed.
Lemma lem99974 (n : nat) (m : nat) (d : nat) : ((S n) = (term23 m d)) = ((S n) = (term24 m d)).
Proof. exact (MK_COMB (@lem99973 n) (@lem99972 m d)). Qed.
Lemma lem99977 (n : nat) (m : nat) : (term87 n m) = (term88 n m).
Proof. exact (fun_ext (fun d : nat => @lem99974 n m d)). Qed.
Lemma lem99978 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem99979 (n : nat) (m : nat) : (term62 n m) = (term89 n m).
Proof. exact (MK_COMB (@lem99978) (@lem99977 n m)). Qed.
Lemma lem99984 (n : nat) (m : nat) : ((term45 m n) = (term62 n m)) = ((term46 m n) = (term89 n m)).
Proof. exact (MK_COMB (@lem99963 m n) (@lem99979 n m)). Qed.
Lemma lem99987 (n : nat) (m : nat) : ((term46 m n) = (term89 n m)) = ((term45 m n) = (term62 n m)).
Proof. exact (SYM (@lem99984 n m)). Qed.
Lemma lem99988 (m : nat) : term14 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem99989 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem99990 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem99989 m) (@lem99988 m)). Qed.
Lemma lem99991 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem99990 m n). Qed.
Lemma lem99992 (m : nat) (n : nat) : (term16 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem100001 (n : nat) (m : nat) (h1 : (Peano.lt m n) = (term58 n m)) : (Peano.lt m n) = (term58 n m).
Proof. exact (h1). Qed.
Lemma lem100008 (m : nat) (n : nat) : (term90 m n) = (term90 m n).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem100009 (n : nat) (m : nat) (h1 : (Peano.lt m n) = (term58 n m)) : (term46 m n) = (term91 n m).
Proof. exact (MK_COMB (@lem100008 m n) (@lem100001 n m h1)). Qed.
Lemma lem100012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem100013 (n : nat) (m : nat) (h1 : (Peano.lt m n) = (term58 n m)) : (term85 m n) = (term92 n m).
Proof. exact (MK_COMB (@lem100012) (@lem100009 n m h1)). Qed.
Lemma lem100019 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem99992 m n) (@lem99991 m n)). Qed.
Lemma lem100020 (n : nat) (m : nat) (d : nat) : ((S n) = (term24 m d)) = (n = (Nat.add m d)).
Proof. exact (@lem100019 n (Nat.add m d)). Qed.
Lemma lem100023 (n : nat) (m : nat) : (term88 n m) = (term93 n m).
Proof. exact (fun_ext (fun d : nat => @lem100020 n m d)). Qed.
Lemma lem100024 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem100025 (n : nat) (m : nat) : (term89 n m) = (term94 n m).
Proof. exact (MK_COMB (@lem100024) (@lem100023 n m)). Qed.
Lemma lem100030 (n : nat) (m : nat) (h1 : (Peano.lt m n) = (term58 n m)) : ((term46 m n) = (term89 n m)) = ((term91 n m) = (term94 n m)).
Proof. exact (MK_COMB (@lem100013 n m h1) (@lem100025 n m)). Qed.
Lemma lem100033 (n : nat) (m : nat) (h1 : (Peano.lt m n) = (term58 n m)) : ((term91 n m) = (term94 n m)) = ((term46 m n) = (term89 n m)).
Proof. exact (SYM (@lem100030 n m h1)). Qed.
Lemma lem100034 (n : nat) (m : nat) (h1 : term91 n m) : term91 n m.
Proof. exact (h1). Qed.
Lemma lem100035 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem100036 (n : nat) (m : nat) (h1 : term58 n m) : term58 n m.
Proof. exact (h1). Qed.
Lemma lem100037 (n : nat) : (term95 n) = (term95 n).
Proof. exact (eq_refl (term95 n)). Qed.
Lemma lem100038 (m : nat) (n : nat) (h1 : m = n) : (term96 n m) = (term97 n).
Proof. exact (MK_COMB (@lem100037 n) (@lem100035 m n h1)). Qed.
Lemma lem100039 (n : nat) : (term97 n) = (term98 n).
Proof. exact (eq_refl (term97 n)). Qed.
Lemma lem100040 (n : nat) (m : nat) : (term99 n m) = (term99 n m).
Proof. exact (eq_refl (term99 n m)). Qed.
Lemma lem100041 (m : nat) (n : nat) : ((term96 n m) = (term97 n)) = ((term96 n m) = (term98 n)).
Proof. exact (MK_COMB (@lem100040 n m) (@lem100039 n)). Qed.
Lemma lem100042 (n : nat) (m : nat) : (term96 n m) = (term94 n m).
Proof. exact (eq_refl (term96 n m)). Qed.
Lemma lem100043 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem100044 (n : nat) (m : nat) : (term99 n m) = (term100 n m).
Proof. exact (MK_COMB (@lem100043) (@lem100042 n m)). Qed.
Lemma lem100045 (n : nat) : (term98 n) = (term98 n).
Proof. exact (eq_refl (term98 n)). Qed.
Lemma lem100046 (m : nat) (n : nat) : ((term96 n m) = (term98 n)) = ((term94 n m) = (term98 n)).
Proof. exact (MK_COMB (@lem100044 n m) (@lem100045 n)). Qed.
Lemma lem100047 (m : nat) (n : nat) : ((term96 n m) = (term97 n)) = ((term94 n m) = (term98 n)).
Proof. exact (TRANS (@lem100041 m n) (@lem100046 m n)). Qed.
Lemma lem100048 (m : nat) (n : nat) (h1 : m = n) : (term94 n m) = (term98 n).
Proof. exact (EQ_MP (@lem100047 m n) (@lem100038 m n h1)). Qed.
Lemma lem100049 (m : nat) (n : nat) (h1 : m = n) : (term98 n) = (term94 n m).
Proof. exact (SYM (@lem100048 m n h1)). Qed.
Lemma lem100053 (m : nat) : (term27 m) = m.
Proof. exact (EQ_MP (@lem99821 m) (@lem99820 m)). Qed.
Lemma lem100054 (n : nat) : (term27 n) = n.
Proof. exact (@lem100053 n). Qed.
Lemma lem100055 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem100056 (n : nat) : (n = (term27 n)) = (n = n).
Proof. exact (MK_COMB (@lem100055 n) (@lem100054 n)). Qed.
Lemma lem100058 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem100059 (x : nat) : (x = x) = True.
Proof. exact (@lem100058 nat x). Qed.
Lemma lem100060 (n : nat) : (n = n) = True.
Proof. exact (@lem100059 n). Qed.
Lemma lem100061 (n : nat) : (n = (term27 n)) = True.
Proof. exact (TRANS (@lem100056 n) (@lem100060 n)). Qed.
Lemma lem100062 (n : nat) : True = (n = (term27 n)).
Proof. exact (SYM (@lem100061 n)). Qed.
Lemma lem100063 (n : nat) : n = (term27 n).
Proof. exact (EQ_MP (@lem100062 n) (@lem0)). Qed.
Lemma lem100064 (n : nat) : term98 n.
Proof. exact (ex_intro (term101 n) (NUMERAL 0) (@lem100063 n)). Qed.
Lemma lem100065 (n : nat) (m : nat) (h1 : term58 n m) : term58 n m.
Proof. exact (h1). Qed.
Lemma lem100066 (n : nat) (m : nat) (d : nat) (h1 : n = (term23 m d)) : n = (term23 m d).
Proof. exact (h1). Qed.
Lemma lem100067 (m : nat) : (term102 m) = (term102 m).
Proof. exact (eq_refl (term102 m)). Qed.
Lemma lem100068 (n : nat) (m : nat) (d : nat) (h1 : n = (term23 m d)) : (term103 m n) = (term104 m d).
Proof. exact (MK_COMB (@lem100067 m) (@lem100066 n m d h1)). Qed.
Lemma lem100069 (d : nat) (m : nat) : (term104 m d) = (term105 d m).
Proof. exact (eq_refl (term104 m d)). Qed.
Lemma lem100070 (m : nat) (n : nat) : (term106 m n) = (term106 m n).
Proof. exact (eq_refl (term106 m n)). Qed.
Lemma lem100071 (n : nat) (d : nat) (m : nat) : ((term103 m n) = (term104 m d)) = ((term103 m n) = (term105 d m)).
Proof. exact (MK_COMB (@lem100070 m n) (@lem100069 d m)). Qed.
Lemma lem100072 (n : nat) (m : nat) : (term103 m n) = (term94 n m).
Proof. exact (eq_refl (term103 m n)). Qed.
Lemma lem100073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem100074 (n : nat) (m : nat) : (term106 m n) = (term100 n m).
Proof. exact (MK_COMB (@lem100073) (@lem100072 n m)). Qed.
Lemma lem100075 (d : nat) (m : nat) : (term105 d m) = (term105 d m).
Proof. exact (eq_refl (term105 d m)). Qed.
Lemma lem100076 (n : nat) (d : nat) (m : nat) : ((term103 m n) = (term105 d m)) = ((term94 n m) = (term105 d m)).
Proof. exact (MK_COMB (@lem100074 n m) (@lem100075 d m)). Qed.
Lemma lem100077 (n : nat) (d : nat) (m : nat) : ((term103 m n) = (term104 m d)) = ((term94 n m) = (term105 d m)).
Proof. exact (TRANS (@lem100071 n d m) (@lem100076 n d m)). Qed.
Lemma lem100078 (n : nat) (m : nat) (d : nat) (h1 : n = (term23 m d)) : (term94 n m) = (term105 d m).
Proof. exact (EQ_MP (@lem100077 n d m) (@lem100068 n m d h1)). Qed.
Lemma lem100079 (n : nat) (m : nat) (d : nat) (h1 : n = (term23 m d)) : (term105 d m) = (term94 n m).
Proof. exact (SYM (@lem100078 n m d h1)). Qed.
Lemma lem100081 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem100082 (x : nat) : (x = x) = True.
Proof. exact (@lem100081 nat x). Qed.
Lemma lem100083 (m : nat) (d : nat) : ((term23 m d) = (term23 m d)) = True.
Proof. exact (@lem100082 (term23 m d)). Qed.
Lemma lem100084 (m : nat) (d : nat) : True = ((term23 m d) = (term23 m d)).
Proof. exact (SYM (@lem100083 m d)). Qed.
Lemma lem100085 (m : nat) (d : nat) : (term23 m d) = (term23 m d).
Proof. exact (EQ_MP (@lem100084 m d) (@lem0)). Qed.
Lemma lem100086 (d : nat) (m : nat) : term105 d m.
Proof. exact (ex_intro (term107 d m) (S d) (@lem100085 m d)). Qed.
Lemma lem100087 (n : nat) (m : nat) (d : nat) (h1 : n = (term23 m d)) : term94 n m.
Proof. exact (EQ_MP (@lem100079 n m d h1) (@lem100086 d m)). Qed.
Lemma lem100088 (n : nat) (m : nat) (h1 : term58 n m) : term94 n m.
Proof. exact (ex_elim (@lem100065 n m h1) (fun d : nat => fun h0 : term108 n m d => @lem100087 n m d h0)). Qed.
Lemma lem100089 (n : nat) (m : nat) : term109 n m.
Proof. exact (fun h0 : term58 n m => @lem100088 n m h0). Qed.
Lemma lem100090 (n : nat) (m : nat) (h1 : term58 n m) : term94 n m.
Proof. exact (@lem100089 n m (@lem100036 n m h1)). Qed.
Lemma lem100091 (m : nat) (n : nat) (h1 : m = n) : term94 n m.
Proof. exact (EQ_MP (@lem100049 m n h1) (@lem100064 n)). Qed.
Lemma lem100092 (n : nat) (m : nat) (h1 : term91 n m) : term94 n m.
Proof. exact (or_elim (@lem100034 n m h1) (fun h0 : m = n => @lem100091 m n h0) (fun h0 : term58 n m => @lem100090 n m h0)). Qed.
Lemma lem100093 (n : nat) (m : nat) : term110 n m.
Proof. exact (fun h0 : term91 n m => @lem100092 n m h0). Qed.
Lemma lem100095 {A : Type'} (P : A -> Prop) (Q : Prop) : (term31 A P Q) = (term32 A P Q).
Proof. exact (EQ_MP (@lem99777 A P Q) (@lem99776 A P Q)). Qed.
Lemma lem100096 (P : nat -> Prop) (Q : Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem100095 nat P Q). Qed.
Lemma lem100097 (n : nat) (m : nat) : (term113 n m) = (term114 n m).
Proof. exact (@lem100096 (term93 n m) (term91 n m)). Qed.
Lemma lem100098 (n : nat) (m : nat) (d : nat) : (term115 n m d) = (n = (Nat.add m d)).
Proof. exact (eq_refl (term115 n m d)). Qed.
Lemma lem100099 (n : nat) (m : nat) : (term116 n m) = (term93 n m).
Proof. exact (fun_ext (fun d : nat => @lem100098 n m d)). Qed.
Lemma lem100100 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem100101 (n : nat) (m : nat) : (term117 n m) = (term94 n m).
Proof. exact (MK_COMB (@lem100100) (@lem100099 n m)). Qed.
Lemma lem100102 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem100103 (n : nat) (m : nat) : (term118 n m) = (term119 n m).
Proof. exact (MK_COMB (@lem100102) (@lem100101 n m)). Qed.
Lemma lem100104 (n : nat) (m : nat) : (term91 n m) = (term91 n m).
Proof. exact (eq_refl (term91 n m)). Qed.
Lemma lem100105 (n : nat) (m : nat) : (term113 n m) = (term120 n m).
Proof. exact (MK_COMB (@lem100103 n m) (@lem100104 n m)). Qed.
Lemma lem100106 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem100107 (n : nat) (m : nat) : (term121 n m) = (term122 n m).
Proof. exact (MK_COMB (@lem100106) (@lem100105 n m)). Qed.
Lemma lem100108 (n : nat) (m : nat) (d : nat) : (term115 n m d) = (n = (Nat.add m d)).
Proof. exact (eq_refl (term115 n m d)). Qed.
Lemma lem100109 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem100110 (n : nat) (m : nat) (d : nat) : (term123 n m d) = (term124 n m d).
Proof. exact (MK_COMB (@lem100109) (@lem100108 n m d)). Qed.
Lemma lem100111 (n : nat) (m : nat) : (term91 n m) = (term91 n m).
Proof. exact (eq_refl (term91 n m)). Qed.
Lemma lem100112 (d : nat) (n : nat) (m : nat) : (term125 d n m) = (term126 d n m).
Proof. exact (MK_COMB (@lem100110 n m d) (@lem100111 n m)). Qed.
Lemma lem100113 (n : nat) (m : nat) : (term127 n m) = (term128 n m).
Proof. exact (fun_ext (fun d : nat => @lem100112 d n m)). Qed.
Lemma lem100114 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100115 (n : nat) (m : nat) : (term114 n m) = (term129 n m).
Proof. exact (MK_COMB (@lem100114) (@lem100113 n m)). Qed.
Lemma lem100116 (n : nat) (m : nat) : ((term113 n m) = (term114 n m)) = ((term120 n m) = (term129 n m)).
Proof. exact (MK_COMB (@lem100107 n m) (@lem100115 n m)). Qed.
Lemma lem100117 (n : nat) (m : nat) : (term120 n m) = (term129 n m).
Proof. exact (EQ_MP (@lem100116 n m) (@lem100097 n m)). Qed.
Lemma lem100118 (n : nat) (m : nat) : (term129 n m) = (term120 n m).
Proof. exact (SYM (@lem100117 n m)). Qed.
Lemma lem100120 (P : nat -> Prop) : term50 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem100121 (n : nat) (m : nat) : term130 n m.
Proof. exact (@lem100120 (term128 n m)). Qed.
Lemma lem100122 (n : nat) (m : nat) : (term131 n m) = (term132 n m).
Proof. exact (eq_refl (term131 n m)). Qed.
Lemma lem100123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem100124 (n : nat) (m : nat) : (term133 n m) = (term134 n m).
Proof. exact (MK_COMB (@lem100123) (@lem100122 n m)). Qed.
Lemma lem100125 (d : nat) (n : nat) (m : nat) : (term135 n m d) = (term126 d n m).
Proof. exact (eq_refl (term135 n m d)). Qed.
Lemma lem100126 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem100127 (d : nat) (n : nat) (m : nat) : (term136 n m d) = (term137 d n m).
Proof. exact (MK_COMB (@lem100126) (@lem100125 d n m)). Qed.
Lemma lem100128 (d : nat) (n : nat) (m : nat) : (term138 n m d) = (term139 d n m).
Proof. exact (eq_refl (term138 n m d)). Qed.
Lemma lem100129 (d : nat) (n : nat) (m : nat) : (term140 n m d) = (term141 d n m).
Proof. exact (MK_COMB (@lem100127 d n m) (@lem100128 d n m)). Qed.
Lemma lem100130 (n : nat) (m : nat) : (term142 n m) = (term143 n m).
Proof. exact (fun_ext (fun d : nat => @lem100129 d n m)). Qed.
Lemma lem100131 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100132 (n : nat) (m : nat) : (term144 n m) = (term145 n m).
Proof. exact (MK_COMB (@lem100131) (@lem100130 n m)). Qed.
Lemma lem100133 (n : nat) (m : nat) : (term146 n m) = (term147 n m).
Proof. exact (MK_COMB (@lem100124 n m) (@lem100132 n m)). Qed.
Lemma lem100134 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem100135 (n : nat) (m : nat) : (term148 n m) = (term149 n m).
Proof. exact (MK_COMB (@lem100134) (@lem100133 n m)). Qed.
Lemma lem100136 (d : nat) (n : nat) (m : nat) : (term135 n m d) = (term126 d n m).
Proof. exact (eq_refl (term135 n m d)). Qed.
Lemma lem100137 (n : nat) (m : nat) : (term150 n m) = (term128 n m).
Proof. exact (fun_ext (fun d : nat => @lem100136 d n m)). Qed.
Lemma lem100138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100139 (n : nat) (m : nat) : (term151 n m) = (term129 n m).
Proof. exact (MK_COMB (@lem100138) (@lem100137 n m)). Qed.
Lemma lem100140 (n : nat) (m : nat) : (term130 n m) = (term152 n m).
Proof. exact (MK_COMB (@lem100135 n m) (@lem100139 n m)). Qed.
Lemma lem100141 (n : nat) (m : nat) : term152 n m.
Proof. exact (EQ_MP (@lem100140 n m) (@lem100121 n m)). Qed.
Lemma lem100150 (m : nat) : (term27 m) = m.
Proof. exact (EQ_MP (@lem99767 m) (@lem99766 m)). Qed.
Lemma lem100151 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem100152 (n : nat) (m : nat) : (n = (term27 m)) = (n = m).
Proof. exact (MK_COMB (@lem100151 n) (@lem100150 m)). Qed.
Lemma lem100155 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem100156 (n : nat) (m : nat) : (term153 n m) = (term154 n m).
Proof. exact (MK_COMB (@lem100155) (@lem100152 n m)). Qed.
Lemma lem100168 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (EQ_MP (@lem99756 m n) (@lem99755 m n)). Qed.
Lemma lem100169 (m : nat) (d : nat) : (term23 m d) = (term24 m d).
Proof. exact (@lem100168 m d). Qed.
Lemma lem100170 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem100171 (n : nat) (m : nat) (d : nat) : (n = (term23 m d)) = (n = (term24 m d)).
Proof. exact (MK_COMB (@lem100170 n) (@lem100169 m d)). Qed.
Lemma lem100174 (n : nat) (m : nat) : (term108 n m) = (term155 n m).
Proof. exact (fun_ext (fun d : nat => @lem100171 n m d)). Qed.
Lemma lem100175 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem100176 (n : nat) (m : nat) : (term58 n m) = (term156 n m).
Proof. exact (MK_COMB (@lem100175) (@lem100174 n m)). Qed.
Lemma lem100181 (m : nat) (n : nat) : (term90 m n) = (term90 m n).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem100182 (n : nat) (m : nat) : (term91 n m) = (term157 n m).
Proof. exact (MK_COMB (@lem100181 m n) (@lem100176 n m)). Qed.
Lemma lem100185 (n : nat) (m : nat) : (term132 n m) = (term158 n m).
Proof. exact (MK_COMB (@lem100156 n m) (@lem100182 n m)). Qed.
Lemma lem100190 (n : nat) (m : nat) : (term158 n m) = (term132 n m).
Proof. exact (SYM (@lem100185 n m)). Qed.
Lemma lem100198 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (EQ_MP (@lem99756 m n) (@lem99755 m n)). Qed.
Lemma lem100199 (m : nat) (d : nat) : (term23 m d) = (term24 m d).
Proof. exact (@lem100198 m d). Qed.
Lemma lem100200 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem100201 (n : nat) (m : nat) (d : nat) : (n = (term23 m d)) = (n = (term24 m d)).
Proof. exact (MK_COMB (@lem100200 n) (@lem100199 m d)). Qed.
Lemma lem100204 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem100205 (n : nat) (m : nat) (d : nat) : (term159 n m d) = (term160 n m d).
Proof. exact (MK_COMB (@lem100204) (@lem100201 n m d)). Qed.
Lemma lem100217 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (EQ_MP (@lem99756 m n) (@lem99755 m n)). Qed.
Lemma lem100218 (m : nat) (d : nat) : (term23 m d) = (term24 m d).
Proof. exact (@lem100217 m d). Qed.
Lemma lem100219 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem100220 (n : nat) (m : nat) (d : nat) : (n = (term23 m d)) = (n = (term24 m d)).
Proof. exact (MK_COMB (@lem100219 n) (@lem100218 m d)). Qed.
Lemma lem100223 (n : nat) (m : nat) : (term108 n m) = (term155 n m).
Proof. exact (fun_ext (fun d : nat => @lem100220 n m d)). Qed.
Lemma lem100224 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem100225 (n : nat) (m : nat) : (term58 n m) = (term156 n m).
Proof. exact (MK_COMB (@lem100224) (@lem100223 n m)). Qed.
Lemma lem100230 (m : nat) (n : nat) : (term90 m n) = (term90 m n).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem100231 (n : nat) (m : nat) : (term91 n m) = (term157 n m).
Proof. exact (MK_COMB (@lem100230 m n) (@lem100225 n m)). Qed.
Lemma lem100234 (d : nat) (n : nat) (m : nat) : (term139 d n m) = (term161 d n m).
Proof. exact (MK_COMB (@lem100205 n m d) (@lem100231 n m)). Qed.
Lemma lem100239 (d : nat) (n : nat) (m : nat) : (term161 d n m) = (term139 d n m).
Proof. exact (SYM (@lem100234 d n m)). Qed.
Lemma lem100240 (n : nat) (m : nat) (h1 : n = m) : n = m.
Proof. exact (h1). Qed.
Lemma lem100241 (m : nat) : (term162 m) = (term162 m).
Proof. exact (eq_refl (term162 m)). Qed.
Lemma lem100242 (n : nat) (m : nat) (h1 : n = m) : (term163 m n) = (term164 m).
Proof. exact (MK_COMB (@lem100241 m) (@lem100240 n m h1)). Qed.
Lemma lem100243 (m : nat) : (term164 m) = (term165 m).
Proof. exact (eq_refl (term164 m)). Qed.
Lemma lem100244 (m : nat) (n : nat) : (term166 m n) = (term166 m n).
Proof. exact (eq_refl (term166 m n)). Qed.
Lemma lem100245 (n : nat) (m : nat) : ((term163 m n) = (term164 m)) = ((term163 m n) = (term165 m)).
Proof. exact (MK_COMB (@lem100244 m n) (@lem100243 m)). Qed.
Lemma lem100246 (n : nat) (m : nat) : (term163 m n) = (term157 n m).
Proof. exact (eq_refl (term163 m n)). Qed.
Lemma lem100247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem100248 (n : nat) (m : nat) : (term166 m n) = (term167 n m).
Proof. exact (MK_COMB (@lem100247) (@lem100246 n m)). Qed.
Lemma lem100249 (m : nat) : (term165 m) = (term165 m).
Proof. exact (eq_refl (term165 m)). Qed.
Lemma lem100250 (n : nat) (m : nat) : ((term163 m n) = (term165 m)) = ((term157 n m) = (term165 m)).
Proof. exact (MK_COMB (@lem100248 n m) (@lem100249 m)). Qed.
Lemma lem100251 (n : nat) (m : nat) : ((term163 m n) = (term164 m)) = ((term157 n m) = (term165 m)).
Proof. exact (TRANS (@lem100245 n m) (@lem100250 n m)). Qed.
Lemma lem100252 (n : nat) (m : nat) (h1 : n = m) : (term157 n m) = (term165 m).
Proof. exact (EQ_MP (@lem100251 n m) (@lem100242 n m h1)). Qed.
Lemma lem100253 (n : nat) (m : nat) (h1 : n = m) : (term165 m) = (term157 n m).
Proof. exact (SYM (@lem100252 n m h1)). Qed.
Lemma lem100254 (n : nat) (m : nat) (d : nat) (h1 : n = (term24 m d)) : n = (term24 m d).
Proof. exact (h1). Qed.
Lemma lem100255 (m : nat) : (term162 m) = (term162 m).
Proof. exact (eq_refl (term162 m)). Qed.
Lemma lem100256 (n : nat) (m : nat) (d : nat) (h1 : n = (term24 m d)) : (term163 m n) = (term168 m d).
Proof. exact (MK_COMB (@lem100255 m) (@lem100254 n m d h1)). Qed.
Lemma lem100257 (d : nat) (m : nat) : (term168 m d) = (term169 d m).
Proof. exact (eq_refl (term168 m d)). Qed.
Lemma lem100258 (m : nat) (n : nat) : (term166 m n) = (term166 m n).
Proof. exact (eq_refl (term166 m n)). Qed.
Lemma lem100259 (n : nat) (d : nat) (m : nat) : ((term163 m n) = (term168 m d)) = ((term163 m n) = (term169 d m)).
Proof. exact (MK_COMB (@lem100258 m n) (@lem100257 d m)). Qed.
Lemma lem100260 (n : nat) (m : nat) : (term163 m n) = (term157 n m).
Proof. exact (eq_refl (term163 m n)). Qed.
Lemma lem100261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem100262 (n : nat) (m : nat) : (term166 m n) = (term167 n m).
Proof. exact (MK_COMB (@lem100261) (@lem100260 n m)). Qed.
Lemma lem100263 (d : nat) (m : nat) : (term169 d m) = (term169 d m).
Proof. exact (eq_refl (term169 d m)). Qed.
Lemma lem100264 (n : nat) (d : nat) (m : nat) : ((term163 m n) = (term169 d m)) = ((term157 n m) = (term169 d m)).
Proof. exact (MK_COMB (@lem100262 n m) (@lem100263 d m)). Qed.
Lemma lem100265 (n : nat) (d : nat) (m : nat) : ((term163 m n) = (term168 m d)) = ((term157 n m) = (term169 d m)).
Proof. exact (TRANS (@lem100259 n d m) (@lem100264 n d m)). Qed.
Lemma lem100266 (n : nat) (m : nat) (d : nat) (h1 : n = (term24 m d)) : (term157 n m) = (term169 d m).
Proof. exact (EQ_MP (@lem100265 n d m) (@lem100256 n m d h1)). Qed.
Lemma lem100267 (n : nat) (m : nat) (d : nat) (h1 : n = (term24 m d)) : (term169 d m) = (term157 n m).
Proof. exact (SYM (@lem100266 n m d h1)). Qed.
Lemma lem100271 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem100272 (x : nat) : (x = x) = True.
Proof. exact (@lem100271 nat x). Qed.
Lemma lem100273 (m : nat) : (m = m) = True.
Proof. exact (@lem100272 m). Qed.
Lemma lem100274 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem100275 (m : nat) : (term170 m) = (or True).
Proof. exact (MK_COMB (@lem100274) (@lem100273 m)). Qed.
Lemma lem100282 (m : nat) : (term171 m) = (term171 m).
Proof. exact (eq_refl (term171 m)). Qed.
Lemma lem100283 (m : nat) : (term165 m) = (term172 m).
Proof. exact (MK_COMB (@lem100275 m) (@lem100282 m)). Qed.
Lemma lem100285 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem100286 (m : nat) : (term172 m) = True.
Proof. exact (@lem100285 (term171 m)). Qed.
Lemma lem100287 (m : nat) : (term165 m) = True.
Proof. exact (TRANS (@lem100283 m) (@lem100286 m)). Qed.
Lemma lem100288 (m : nat) : True = (term165 m).
Proof. exact (SYM (@lem100287 m)). Qed.
Lemma lem100289 (m : nat) : term165 m.
Proof. exact (EQ_MP (@lem100288 m) (@lem0)). Qed.
Lemma lem100309 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem99741 m n) (@lem99740 m n)). Qed.
Lemma lem100310 (d : nat) (m : nat) (d' : nat) : ((term24 m d) = (term24 m d')) = ((Nat.add m d) = (Nat.add m d')).
Proof. exact (@lem100309 (Nat.add m d) (Nat.add m d')). Qed.
Lemma lem100312 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem99735 m n p) (@lem99734 m n p)). Qed.
Lemma lem100313 (m : nat) (d : nat) (d' : nat) : ((Nat.add m d) = (Nat.add m d')) = (d = d').
Proof. exact (@lem100312 m d d'). Qed.
Lemma lem100316 (m : nat) (d : nat) (d' : nat) : ((term24 m d) = (term24 m d')) = (d = d').
Proof. exact (TRANS (@lem100310 d m d') (@lem100313 m d d')). Qed.
Lemma lem100317 (m : nat) (d : nat) : (term173 d m) = (term174 d).
Proof. exact (fun_ext (fun d' : nat => @lem100316 m d d')). Qed.
Lemma lem100318 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem100319 (m : nat) (d : nat) : (term175 d m) = (term176 d).
Proof. exact (MK_COMB (@lem100318) (@lem100317 m d)). Qed.
Lemma lem100321 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem99726 A a) (@lem99725 A a)). Qed.
Lemma lem100322 (a : nat) : (term176 a) = True.
Proof. exact (@lem100321 nat a). Qed.
Lemma lem100323 (d : nat) : (term176 d) = True.
Proof. exact (@lem100322 d). Qed.
Lemma lem100324 (d : nat) (m : nat) : (term175 d m) = True.
Proof. exact (TRANS (@lem100319 m d) (@lem100323 d)). Qed.
Lemma lem100325 (d : nat) (m : nat) : True = (term175 d m).
Proof. exact (SYM (@lem100324 d m)). Qed.
Lemma lem100326 (d : nat) (m : nat) : term175 d m.
Proof. exact (EQ_MP (@lem100325 d m) (@lem0)). Qed.
Lemma lem100328 (d : nat) (m : nat) : term169 d m.
Proof. exact (or_intro2 (m = (term24 m d)) (@lem100326 d m)). Qed.
Lemma lem100329 (n : nat) (m : nat) (d : nat) (h1 : n = (term24 m d)) : term157 n m.
Proof. exact (EQ_MP (@lem100267 n m d h1) (@lem100328 d m)). Qed.
Lemma lem100330 (d : nat) (n : nat) (m : nat) : term161 d n m.
Proof. exact (fun h0 : n = (term24 m d) => @lem100329 n m d h0). Qed.
Lemma lem100331 (n : nat) (m : nat) (h1 : n = m) : term157 n m.
Proof. exact (EQ_MP (@lem100253 n m h1) (@lem100289 m)). Qed.
Lemma lem100332 (n : nat) (m : nat) : term158 n m.
Proof. exact (fun h0 : n = m => @lem100331 n m h0). Qed.
Lemma lem100333 (d : nat) (n : nat) (m : nat) : term139 d n m.
Proof. exact (EQ_MP (@lem100239 d n m) (@lem100330 d n m)). Qed.
Lemma lem100334 (n : nat) (m : nat) : term132 n m.
Proof. exact (EQ_MP (@lem100190 n m) (@lem100332 n m)). Qed.
Lemma lem100335 (d : nat) (n : nat) (m : nat) : term141 d n m.
Proof. exact (fun h0 : term126 d n m => @lem100333 d n m). Qed.
Lemma lem100340 (n : nat) (m : nat) : term145 n m.
Proof. exact (fun d : nat => @lem100335 d n m). Qed.
Lemma lem100341 (n : nat) (m : nat) : term147 n m.
Proof. exact (conj (@lem100334 n m) (@lem100340 n m)). Qed.
Lemma lem100342 (n : nat) (m : nat) : term129 n m.
Proof. exact (@lem100141 n m (@lem100341 n m)). Qed.
Lemma lem100343 (n : nat) (m : nat) : term120 n m.
Proof. exact (EQ_MP (@lem100118 n m) (@lem100342 n m)). Qed.
Lemma lem100344 (n : nat) (m : nat) : term177 n m.
Proof. exact (conj (@lem100093 n m) (@lem100343 n m)). Qed.
Lemma lem100345 (n : nat) (m : nat) : (term177 n m) = ((term91 n m) = (term94 n m)).
Proof. exact (@lem32 (term91 n m) (term94 n m)). Qed.
Lemma lem100346 (n : nat) (m : nat) : (term91 n m) = (term94 n m).
Proof. exact (EQ_MP (@lem100345 n m) (@lem100344 n m)). Qed.
Lemma lem100347 (n : nat) (m : nat) (h1 : (Peano.lt m n) = (term58 n m)) : (term46 m n) = (term89 n m).
Proof. exact (EQ_MP (@lem100033 n m h1) (@lem100346 n m)). Qed.
Lemma lem100348 (n : nat) (m : nat) (h1 : (Peano.lt m n) = (term58 n m)) : (term45 m n) = (term62 n m).
Proof. exact (EQ_MP (@lem99987 n m) (@lem100347 n m h1)). Qed.
Lemma lem100349 (n : nat) (m : nat) : term64 n m.
Proof. exact (fun h0 : (Peano.lt m n) = (term58 n m) => @lem100348 n m h0). Qed.
Lemma lem100354 (m : nat) : term68 m.
Proof. exact (fun n : nat => @lem100349 n m). Qed.
Lemma lem100355 (m : nat) : term70 m.
Proof. exact (conj (@lem99953 m) (@lem100354 m)). Qed.
Lemma lem100356 (m : nat) : term75 m.
Proof. exact (@lem99913 m (@lem100355 m)). Qed.
Lemma lem100361 : term178.
Proof. exact (fun m : nat => @lem100356 m). Qed.
