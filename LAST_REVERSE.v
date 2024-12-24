Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LAST_REVERSE_term_abbrevs.
Require Import LAST_APPEND_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_CONS_NIL_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1096517_spec.
Require Import thm1096523_spec.
Require Import thm1096524_spec.
Require Import thm1098347_spec.
Require Import thm1098348_spec.
Require Import thm12653_spec.
Require Import thm15249_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem1203799 {A : Type'} (h : A) : term0 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem1203800 {A : Type'} (h : A) : (term0 A h) = (term1 A h).
Proof. exact (eq_refl (term0 A h)). Qed.
Lemma lem1203801 {A : Type'} (h : A) : term1 A h.
Proof. exact (EQ_MP (@lem1203800 A h) (@lem1203799 A h)). Qed.
Lemma lem1203802 {A : Type'} (h : A) (t : list A) : term2 A h t.
Proof. exact (@lem1203801 A h t). Qed.
Lemma lem1203803 {A : Type'} (h : A) (t : list A) : (term2 A h t) = (term3 A h t).
Proof. exact (eq_refl (term2 A h t)). Qed.
Lemma lem1203804 {A : Type'} (h : A) (t : list A) : term3 A h t.
Proof. exact (EQ_MP (@lem1203803 A h t) (@lem1203802 A h t)). Qed.
Lemma lem1203805 {A : Type'} (h : A) (t : list A) : term4 A h t.
Proof. exact (@lem82 ((@cons A h t) = (@nil A))). Qed.
Lemma lem1203818 {_28101 : Type'} (p : list _28101) : term5 _28101 p.
Proof. exact (@lem1203021 _28101 p). Qed.
Lemma lem1203819 {_28101 : Type'} (p : list _28101) : (term5 _28101 p) = (term6 _28101 p).
Proof. exact (eq_refl (term5 _28101 p)). Qed.
Lemma lem1203820 {_28101 : Type'} (p : list _28101) : term6 _28101 p.
Proof. exact (EQ_MP (@lem1203819 _28101 p) (@lem1203818 _28101 p)). Qed.
Lemma lem1203821 {_28101 : Type'} (p : list _28101) (q : list _28101) : term7 _28101 p q.
Proof. exact (@lem1203820 _28101 p q). Qed.
Lemma lem1203822 {_28101 : Type'} (p : list _28101) (q : list _28101) : (term7 _28101 p q) = ((term8 _28101 p q) = (term9 _28101 p q)).
Proof. exact (eq_refl (term7 _28101 p q)). Qed.
Lemma lem1203827 {A : Type'} (P : type1143 A) : term10 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1203828 {A : Type'} (P : type1143 A) : term10 A P.
Proof. exact (@lem1203827 A P). Qed.
Lemma lem1203829 {A : Type'} : term11 A.
Proof. exact (@lem1203828 A (term12 A)). Qed.
Lemma lem1203830 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (eq_refl (term13 A)). Qed.
Lemma lem1203831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1203832 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem1203831) (@lem1203830 A)). Qed.
Lemma lem1203833 {A : Type'} (t : list A) : (term17 A t) = (term18 A t).
Proof. exact (eq_refl (term17 A t)). Qed.
Lemma lem1203834 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1203835 {A : Type'} (t : list A) : (term19 A t) = (term20 A t).
Proof. exact (MK_COMB (@lem1203834) (@lem1203833 A t)). Qed.
Lemma lem1203836 {A : Type'} (h : A) (t : list A) : (term21 A h t) = (term22 A h t).
Proof. exact (eq_refl (term21 A h t)). Qed.
Lemma lem1203837 {A : Type'} (h : A) (t : list A) : (term23 A h t) = (term24 A h t).
Proof. exact (MK_COMB (@lem1203835 A t) (@lem1203836 A h t)). Qed.
Lemma lem1203838 {A : Type'} (h : A) : (term25 A h) = (term26 A h).
Proof. exact (fun_ext (fun t : list A => @lem1203837 A h t)). Qed.
Lemma lem1203839 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1203840 {A : Type'} (h : A) : (term27 A h) = (term28 A h).
Proof. exact (MK_COMB (@lem1203839 A) (@lem1203838 A h)). Qed.
Lemma lem1203841 {A : Type'} : (term29 A) = (term30 A).
Proof. exact (fun_ext (fun h : A => @lem1203840 A h)). Qed.
Lemma lem1203842 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1203843 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (MK_COMB (@lem1203842 A) (@lem1203841 A)). Qed.
Lemma lem1203844 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (MK_COMB (@lem1203832 A) (@lem1203843 A)). Qed.
Lemma lem1203845 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1203846 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (MK_COMB (@lem1203845) (@lem1203844 A)). Qed.
Lemma lem1203847 {A : Type'} (l : list A) : (term17 A l) = (term18 A l).
Proof. exact (eq_refl (term17 A l)). Qed.
Lemma lem1203848 {A : Type'} : (term37 A) = (term12 A).
Proof. exact (fun_ext (fun l : list A => @lem1203847 A l)). Qed.
Lemma lem1203849 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1203850 {A : Type'} : (term38 A) = (term39 A).
Proof. exact (MK_COMB (@lem1203849 A) (@lem1203848 A)). Qed.
Lemma lem1203851 {A : Type'} : (term11 A) = (term40 A).
Proof. exact (MK_COMB (@lem1203846 A) (@lem1203850 A)). Qed.
Lemma lem1203852 {A : Type'} : term40 A.
Proof. exact (EQ_MP (@lem1203851 A) (@lem1203829 A)). Qed.
Lemma lem1203857 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1203858 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1203857 (list A) x). Qed.
Lemma lem1203859 {A : Type'} : ((@nil A) = (@nil A)) = True.
Proof. exact (@lem1203858 A (@nil A)). Qed.
Lemma lem1203860 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1203861 {A : Type'} : (term41 A) = (~ True).
Proof. exact (MK_COMB (@lem1203860) (@lem1203859 A)). Qed.
Lemma lem1203863 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1203864 {A : Type'} : (term41 A) = False.
Proof. exact (TRANS (@lem1203861 A) (@lem1203863)). Qed.
Lemma lem1203865 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1203866 {A : Type'} : (term42 A) = (imp False).
Proof. exact (MK_COMB (@lem1203865) (@lem1203864 A)). Qed.
Lemma lem1203870 {A : Type'} : (@List.rev A (@nil A)) = (@nil A).
Proof. exact (proj1 (@lem1096517 A)). Qed.
Lemma lem1203871 {A : Type'} : (@LAST A) = (@LAST A).
Proof. exact (eq_refl (@LAST A)). Qed.
Lemma lem1203872 {A : Type'} : (term43 A) = (@LAST A (@nil A)).
Proof. exact (MK_COMB (@lem1203871 A) (@lem1203870 A)). Qed.
Lemma lem1203873 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1203874 {A : Type'} : (term44 A) = (term45 A).
Proof. exact (MK_COMB (@lem1203873 A) (@lem1203872 A)). Qed.
Lemma lem1203875 {A : Type'} : (@hd A (@nil A)) = (@hd A (@nil A)).
Proof. exact (eq_refl (@hd A (@nil A))). Qed.
Lemma lem1203876 {A : Type'} : ((term43 A) = (@hd A (@nil A))) = ((@LAST A (@nil A)) = (@hd A (@nil A))).
Proof. exact (MK_COMB (@lem1203874 A) (@lem1203875 A)). Qed.
Lemma lem1203879 {A : Type'} : (term14 A) = (term46 A).
Proof. exact (MK_COMB (@lem1203866 A) (@lem1203876 A)). Qed.
Lemma lem1203881 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1203882 {A : Type'} : (term46 A) = True.
Proof. exact (@lem1203881 ((@LAST A (@nil A)) = (@hd A (@nil A)))). Qed.
Lemma lem1203883 {A : Type'} : (term14 A) = True.
Proof. exact (TRANS (@lem1203879 A) (@lem1203882 A)). Qed.
Lemma lem1203884 {A : Type'} : True = (term14 A).
Proof. exact (SYM (@lem1203883 A)). Qed.
Lemma lem1203885 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem1203884 A) (@lem0)). Qed.
Lemma lem1203889 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1203805 A h t (@lem1203804 A h t)). Qed.
Lemma lem1203890 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1203889 A h t). Qed.
Lemma lem1203891 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1203892 {A : Type'} (h : A) (t : list A) : (term3 A h t) = (~ False).
Proof. exact (MK_COMB (@lem1203891) (@lem1203890 A h t)). Qed.
Lemma lem1203894 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1203895 {A : Type'} (h : A) (t : list A) : (term3 A h t) = True.
Proof. exact (TRANS (@lem1203892 A h t) (@lem1203894)). Qed.
Lemma lem1203896 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1203897 {A : Type'} (h : A) (t : list A) : (term47 A h t) = (imp True).
Proof. exact (MK_COMB (@lem1203896) (@lem1203895 A h t)). Qed.
Lemma lem1203901 {A : Type'} (l : list A) (x : A) : (term48 A x l) = (term49 A l x).
Proof. exact (EQ_MP (@lem1096524 A l x) (@lem1096523 A l x)). Qed.
Lemma lem1203902 {A : Type'} (l : list A) (x : A) : (term48 A x l) = (term49 A l x).
Proof. exact (@lem1203901 A l x). Qed.
Lemma lem1203903 {A : Type'} (t : list A) (h : A) : (term48 A h t) = (term49 A t h).
Proof. exact (@lem1203902 A t h). Qed.
Lemma lem1203904 {A : Type'} : (@LAST A) = (@LAST A).
Proof. exact (eq_refl (@LAST A)). Qed.
Lemma lem1203905 {A : Type'} (t : list A) (h : A) : (term50 A h t) = (term51 A t h).
Proof. exact (MK_COMB (@lem1203904 A) (@lem1203903 A t h)). Qed.
Lemma lem1203907 {_28101 : Type'} (p : list _28101) (q : list _28101) : (term8 _28101 p q) = (term9 _28101 p q).
Proof. exact (EQ_MP (@lem1203822 _28101 p q) (@lem1203821 _28101 p q)). Qed.
Lemma lem1203908 {A : Type'} (p : list A) (q : list A) : (term8 A p q) = (term9 A p q).
Proof. exact (@lem1203907 A p q). Qed.
Lemma lem1203909 {A : Type'} (t : list A) (h : A) : (term51 A t h) = (term52 A t h).
Proof. exact (@lem1203908 A (@List.rev A t) (@cons A h (@nil A))). Qed.
Lemma lem1203913 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1203805 A h t (@lem1203804 A h t)). Qed.
Lemma lem1203914 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1203913 A h t). Qed.
Lemma lem1203915 {A : Type'} (h : A) : ((@cons A h (@nil A)) = (@nil A)) = False.
Proof. exact (@lem1203914 A h (@nil A)). Qed.
Lemma lem1203916 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem1203917 {A : Type'} (h : A) : (term53 A h) = (@COND A False).
Proof. exact (MK_COMB (@lem1203916 A) (@lem1203915 A h)). Qed.
Lemma lem1203918 {A : Type'} (t : list A) : (term54 A t) = (term54 A t).
Proof. exact (eq_refl (term54 A t)). Qed.
Lemma lem1203919 {A : Type'} (h : A) (t : list A) : (term55 A h t) = (term56 A t).
Proof. exact (MK_COMB (@lem1203917 A h) (@lem1203918 A t)). Qed.
Lemma lem1203921 {A : Type'} (h : A) (t : list A) : (term57 A h t) = (term58 A h t).
Proof. exact (EQ_MP (@lem1098348 A h t) (@lem1098347 A h t)). Qed.
Lemma lem1203922 {A : Type'} (h : A) (t : list A) : (term57 A h t) = (term58 A h t).
Proof. exact (@lem1203921 A h t). Qed.
Lemma lem1203923 {A : Type'} (h : A) : (term59 A h) = (term60 A h).
Proof. exact (@lem1203922 A h (@nil A)). Qed.
Lemma lem1203925 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term61 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem1203926 {A : Type'} (x : list A) (z : A) (y : A) : (term62 A x y z) = y.
Proof. exact (@lem1203925 A (list A) x z y). Qed.
Lemma lem1203927 {A : Type'} (h : A) : (term60 A h) = h.
Proof. exact (@lem1203926 A (@nil A) (@LAST A (@nil A)) h). Qed.
Lemma lem1203928 {A : Type'} (h : A) : (term59 A h) = h.
Proof. exact (TRANS (@lem1203923 A h) (@lem1203927 A h)). Qed.
Lemma lem1203929 {A : Type'} (t : list A) (h : A) : (term52 A t h) = (term63 A t h).
Proof. exact (MK_COMB (@lem1203919 A h t) (@lem1203928 A h)). Qed.
Lemma lem1203931 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1203932 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem1203931 A t1 t2). Qed.
Lemma lem1203933 {A : Type'} (t : list A) (h : A) : (term63 A t h) = h.
Proof. exact (@lem1203932 A (term54 A t) h). Qed.
Lemma lem1203934 {A : Type'} (t : list A) (h : A) : (term52 A t h) = h.
Proof. exact (TRANS (@lem1203929 A t h) (@lem1203933 A t h)). Qed.
Lemma lem1203935 {A : Type'} (t : list A) (h : A) : (term51 A t h) = h.
Proof. exact (TRANS (@lem1203909 A t h) (@lem1203934 A t h)). Qed.
Lemma lem1203936 {A : Type'} (t : list A) (h : A) : (term50 A h t) = h.
Proof. exact (TRANS (@lem1203905 A t h) (@lem1203935 A t h)). Qed.
Lemma lem1203937 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1203938 {A : Type'} (t : list A) (h : A) : (term64 A h t) = (@eq A h).
Proof. exact (MK_COMB (@lem1203937 A) (@lem1203936 A t h)). Qed.
Lemma lem1203940 {A : Type'} (t : list A) (h : A) : (term65 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1203941 {A : Type'} (t : list A) (h : A) : (term65 A h t) = h.
Proof. exact (@lem1203940 A t h). Qed.
Lemma lem1203942 {A : Type'} (t : list A) (h : A) : ((term50 A h t) = (term65 A h t)) = (h = h).
Proof. exact (MK_COMB (@lem1203938 A t h) (@lem1203941 A t h)). Qed.
Lemma lem1203944 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1203945 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1203944 A x). Qed.
Lemma lem1203946 {A : Type'} (h : A) : (h = h) = True.
Proof. exact (@lem1203945 A h). Qed.
Lemma lem1203947 {A : Type'} (h : A) (t : list A) : ((term50 A h t) = (term65 A h t)) = True.
Proof. exact (TRANS (@lem1203942 A t h) (@lem1203946 A h)). Qed.
Lemma lem1203948 {A : Type'} (h : A) (t : list A) : (term22 A h t) = (True -> True).
Proof. exact (MK_COMB (@lem1203897 A h t) (@lem1203947 A h t)). Qed.
Lemma lem1203950 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1203951 : (True -> True) = True.
Proof. exact (@lem1203950 True). Qed.
Lemma lem1203952 {A : Type'} (h : A) (t : list A) : (term22 A h t) = True.
Proof. exact (TRANS (@lem1203948 A h t) (@lem1203951)). Qed.
Lemma lem1203953 {A : Type'} (h : A) (t : list A) : True = (term22 A h t).
Proof. exact (SYM (@lem1203952 A h t)). Qed.
Lemma lem1203954 {A : Type'} (h : A) (t : list A) : term22 A h t.
Proof. exact (EQ_MP (@lem1203953 A h t) (@lem0)). Qed.
Lemma lem1203955 {A : Type'} (h : A) (t : list A) : term24 A h t.
Proof. exact (fun h0 : term18 A t => @lem1203954 A h t). Qed.
Lemma lem1203960 {A : Type'} (h : A) : term28 A h.
Proof. exact (fun t : list A => @lem1203955 A h t). Qed.
Lemma lem1203965 {A : Type'} : term32 A.
Proof. exact (fun h : A => @lem1203960 A h). Qed.
Lemma lem1203966 {A : Type'} : term34 A.
Proof. exact (conj (@lem1203885 A) (@lem1203965 A)). Qed.
Lemma lem1203967 {A : Type'} : term39 A.
Proof. exact (@lem1203852 A (@lem1203966 A)). Qed.
