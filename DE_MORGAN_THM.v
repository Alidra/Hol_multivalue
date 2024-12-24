Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DE_MORGAN_THM_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem9860 (t1 : Prop) : term0 t1.
Proof. exact (@lem9851 t1). Qed.
Lemma lem9861 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem9862 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem9861 t1) (@lem9860 t1)). Qed.
Lemma lem9863 (t1 : Prop) (h1 : t1 = True) : t1 = True.
Proof. exact (h1). Qed.
Lemma lem9864 (t1 : Prop) (h1 : t1 = False) : t1 = False.
Proof. exact (h1). Qed.
Lemma lem9873 (t2 : Prop) : (term2 t2) = (term2 t2).
Proof. exact (eq_refl (term2 t2)). Qed.
Lemma lem9874 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : (term3 t2 t1) = (term4 t2).
Proof. exact (MK_COMB (@lem9873 t2) (@lem9863 t1 h1)). Qed.
Lemma lem9875 (t2 : Prop) : (term4 t2) = ((term5 t2) = (term6 t2)).
Proof. exact (eq_refl (term4 t2)). Qed.
Lemma lem9876 (t2 : Prop) (t1 : Prop) : (term7 t2 t1) = (term7 t2 t1).
Proof. exact (eq_refl (term7 t2 t1)). Qed.
Lemma lem9877 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = (term4 t2)) = ((term3 t2 t1) = ((term5 t2) = (term6 t2))).
Proof. exact (MK_COMB (@lem9876 t2 t1) (@lem9875 t2)). Qed.
Lemma lem9878 (t1 : Prop) (t2 : Prop) : (term3 t2 t1) = ((term8 t1 t2) = (term9 t1 t2)).
Proof. exact (eq_refl (term3 t2 t1)). Qed.
Lemma lem9879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem9880 (t1 : Prop) (t2 : Prop) : (term7 t2 t1) = (term10 t1 t2).
Proof. exact (MK_COMB (@lem9879) (@lem9878 t1 t2)). Qed.
Lemma lem9881 (t2 : Prop) : ((term5 t2) = (term6 t2)) = ((term5 t2) = (term6 t2)).
Proof. exact (eq_refl ((term5 t2) = (term6 t2))). Qed.
Lemma lem9882 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = ((term5 t2) = (term6 t2))) = (((term8 t1 t2) = (term9 t1 t2)) = ((term5 t2) = (term6 t2))).
Proof. exact (MK_COMB (@lem9880 t1 t2) (@lem9881 t2)). Qed.
Lemma lem9883 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = (term4 t2)) = (((term8 t1 t2) = (term9 t1 t2)) = ((term5 t2) = (term6 t2))).
Proof. exact (TRANS (@lem9877 t1 t2) (@lem9882 t1 t2)). Qed.
Lemma lem9884 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : ((term8 t1 t2) = (term9 t1 t2)) = ((term5 t2) = (term6 t2)).
Proof. exact (EQ_MP (@lem9883 t1 t2) (@lem9874 t2 t1 h1)). Qed.
Lemma lem9885 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : ((term5 t2) = (term6 t2)) = ((term8 t1 t2) = (term9 t1 t2)).
Proof. exact (SYM (@lem9884 t2 t1 h1)). Qed.
Lemma lem9886 (t2 : Prop) : (term2 t2) = (term2 t2).
Proof. exact (eq_refl (term2 t2)). Qed.
Lemma lem9887 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : (term3 t2 t1) = (term11 t2).
Proof. exact (MK_COMB (@lem9886 t2) (@lem9864 t1 h1)). Qed.
Lemma lem9888 (t2 : Prop) : (term11 t2) = ((term12 t2) = (term13 t2)).
Proof. exact (eq_refl (term11 t2)). Qed.
Lemma lem9889 (t2 : Prop) (t1 : Prop) : (term7 t2 t1) = (term7 t2 t1).
Proof. exact (eq_refl (term7 t2 t1)). Qed.
Lemma lem9890 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = (term11 t2)) = ((term3 t2 t1) = ((term12 t2) = (term13 t2))).
Proof. exact (MK_COMB (@lem9889 t2 t1) (@lem9888 t2)). Qed.
Lemma lem9891 (t1 : Prop) (t2 : Prop) : (term3 t2 t1) = ((term8 t1 t2) = (term9 t1 t2)).
Proof. exact (eq_refl (term3 t2 t1)). Qed.
Lemma lem9892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem9893 (t1 : Prop) (t2 : Prop) : (term7 t2 t1) = (term10 t1 t2).
Proof. exact (MK_COMB (@lem9892) (@lem9891 t1 t2)). Qed.
Lemma lem9894 (t2 : Prop) : ((term12 t2) = (term13 t2)) = ((term12 t2) = (term13 t2)).
Proof. exact (eq_refl ((term12 t2) = (term13 t2))). Qed.
Lemma lem9895 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = ((term12 t2) = (term13 t2))) = (((term8 t1 t2) = (term9 t1 t2)) = ((term12 t2) = (term13 t2))).
Proof. exact (MK_COMB (@lem9893 t1 t2) (@lem9894 t2)). Qed.
Lemma lem9896 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = (term11 t2)) = (((term8 t1 t2) = (term9 t1 t2)) = ((term12 t2) = (term13 t2))).
Proof. exact (TRANS (@lem9890 t1 t2) (@lem9895 t1 t2)). Qed.
Lemma lem9897 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : ((term8 t1 t2) = (term9 t1 t2)) = ((term12 t2) = (term13 t2)).
Proof. exact (EQ_MP (@lem9896 t1 t2) (@lem9887 t2 t1 h1)). Qed.
Lemma lem9898 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : ((term12 t2) = (term13 t2)) = ((term8 t1 t2) = (term9 t1 t2)).
Proof. exact (SYM (@lem9897 t2 t1 h1)). Qed.
Lemma lem9902 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem9903 (t2 : Prop) : (True /\ t2) = t2.
Proof. exact (@lem9902 t2). Qed.
Lemma lem9904 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem9905 (t2 : Prop) : (term5 t2) = (~ t2).
Proof. exact (MK_COMB (@lem9904) (@lem9903 t2)). Qed.
Lemma lem9906 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem9907 (t2 : Prop) : (term14 t2) = (term15 t2).
Proof. exact (MK_COMB (@lem9906) (@lem9905 t2)). Qed.
Lemma lem9911 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem9912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem9913 : term16 = (or False).
Proof. exact (MK_COMB (@lem9912) (@lem9911)). Qed.
Lemma lem9914 (t2 : Prop) : (~ t2) = (~ t2).
Proof. exact (eq_refl (~ t2)). Qed.
Lemma lem9915 (t2 : Prop) : (term6 t2) = (term17 t2).
Proof. exact (MK_COMB (@lem9913) (@lem9914 t2)). Qed.
Lemma lem9917 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem9918 (t2 : Prop) : (term17 t2) = (~ t2).
Proof. exact (@lem9917 (~ t2)). Qed.
Lemma lem9919 (t2 : Prop) : (term6 t2) = (~ t2).
Proof. exact (TRANS (@lem9915 t2) (@lem9918 t2)). Qed.
Lemma lem9920 (t2 : Prop) : ((term5 t2) = (term6 t2)) = ((~ t2) = (~ t2)).
Proof. exact (MK_COMB (@lem9907 t2) (@lem9919 t2)). Qed.
Lemma lem9922 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem9923 (x : Prop) : (x = x) = True.
Proof. exact (@lem9922 Prop x). Qed.
Lemma lem9924 (t2 : Prop) : ((~ t2) = (~ t2)) = True.
Proof. exact (@lem9923 (~ t2)). Qed.
Lemma lem9925 (t2 : Prop) : ((term5 t2) = (term6 t2)) = True.
Proof. exact (TRANS (@lem9920 t2) (@lem9924 t2)). Qed.
Lemma lem9926 (t2 : Prop) : True = ((term5 t2) = (term6 t2)).
Proof. exact (SYM (@lem9925 t2)). Qed.
Lemma lem9927 (t2 : Prop) : (term5 t2) = (term6 t2).
Proof. exact (EQ_MP (@lem9926 t2) (@lem0)). Qed.
Lemma lem9931 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem9932 (t2 : Prop) : (False /\ t2) = False.
Proof. exact (@lem9931 t2). Qed.
Lemma lem9933 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem9934 (t2 : Prop) : (term12 t2) = (~ False).
Proof. exact (MK_COMB (@lem9933) (@lem9932 t2)). Qed.
Lemma lem9936 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem9937 (t2 : Prop) : (term12 t2) = True.
Proof. exact (TRANS (@lem9934 t2) (@lem9936)). Qed.
Lemma lem9938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem9939 (t2 : Prop) : (term18 t2) = (@eq Prop True).
Proof. exact (MK_COMB (@lem9938) (@lem9937 t2)). Qed.
Lemma lem9943 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem9944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem9945 : term19 = (or True).
Proof. exact (MK_COMB (@lem9944) (@lem9943)). Qed.
Lemma lem9946 (t2 : Prop) : (~ t2) = (~ t2).
Proof. exact (eq_refl (~ t2)). Qed.
Lemma lem9947 (t2 : Prop) : (term13 t2) = (term20 t2).
Proof. exact (MK_COMB (@lem9945) (@lem9946 t2)). Qed.
Lemma lem9949 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem9950 (t2 : Prop) : (term20 t2) = True.
Proof. exact (@lem9949 (~ t2)). Qed.
Lemma lem9951 (t2 : Prop) : (term13 t2) = True.
Proof. exact (TRANS (@lem9947 t2) (@lem9950 t2)). Qed.
Lemma lem9952 (t2 : Prop) : ((term12 t2) = (term13 t2)) = (True = True).
Proof. exact (MK_COMB (@lem9939 t2) (@lem9951 t2)). Qed.
Lemma lem9954 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem9955 : (True = True) = True.
Proof. exact (@lem9954 True). Qed.
Lemma lem9956 (t2 : Prop) : ((term12 t2) = (term13 t2)) = True.
Proof. exact (TRANS (@lem9952 t2) (@lem9955)). Qed.
Lemma lem9957 (t2 : Prop) : True = ((term12 t2) = (term13 t2)).
Proof. exact (SYM (@lem9956 t2)). Qed.
Lemma lem9958 (t2 : Prop) : (term12 t2) = (term13 t2).
Proof. exact (EQ_MP (@lem9957 t2) (@lem0)). Qed.
Lemma lem9959 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : (term8 t1 t2) = (term9 t1 t2).
Proof. exact (EQ_MP (@lem9898 t2 t1 h1) (@lem9958 t2)). Qed.
Lemma lem9960 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : (term8 t1 t2) = (term9 t1 t2).
Proof. exact (EQ_MP (@lem9885 t2 t1 h1) (@lem9927 t2)). Qed.
Lemma lem9963 (t1 : Prop) (t2 : Prop) : (term8 t1 t2) = (term9 t1 t2).
Proof. exact (or_elim (@lem9862 t1) (fun h0 : t1 = True => @lem9960 t2 t1 h0) (fun h0 : t1 = False => @lem9959 t2 t1 h0)). Qed.
Lemma lem9972 (t1 : Prop) : term0 t1.
Proof. exact (@lem9851 t1). Qed.
Lemma lem9973 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem9974 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem9973 t1) (@lem9972 t1)). Qed.
Lemma lem9975 (t1 : Prop) (h1 : t1 = True) : t1 = True.
Proof. exact (h1). Qed.
Lemma lem9976 (t1 : Prop) (h1 : t1 = False) : t1 = False.
Proof. exact (h1). Qed.
Lemma lem9985 (t2 : Prop) : (term21 t2) = (term21 t2).
Proof. exact (eq_refl (term21 t2)). Qed.
Lemma lem9986 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : (term22 t2 t1) = (term23 t2).
Proof. exact (MK_COMB (@lem9985 t2) (@lem9975 t1 h1)). Qed.
Lemma lem9987 (t2 : Prop) : (term23 t2) = ((term24 t2) = (term25 t2)).
Proof. exact (eq_refl (term23 t2)). Qed.
Lemma lem9988 (t2 : Prop) (t1 : Prop) : (term26 t2 t1) = (term26 t2 t1).
Proof. exact (eq_refl (term26 t2 t1)). Qed.
Lemma lem9989 (t1 : Prop) (t2 : Prop) : ((term22 t2 t1) = (term23 t2)) = ((term22 t2 t1) = ((term24 t2) = (term25 t2))).
Proof. exact (MK_COMB (@lem9988 t2 t1) (@lem9987 t2)). Qed.
Lemma lem9990 (t1 : Prop) (t2 : Prop) : (term22 t2 t1) = ((term27 t1 t2) = (term28 t1 t2)).
Proof. exact (eq_refl (term22 t2 t1)). Qed.
Lemma lem9991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem9992 (t1 : Prop) (t2 : Prop) : (term26 t2 t1) = (term29 t1 t2).
Proof. exact (MK_COMB (@lem9991) (@lem9990 t1 t2)). Qed.
Lemma lem9993 (t2 : Prop) : ((term24 t2) = (term25 t2)) = ((term24 t2) = (term25 t2)).
Proof. exact (eq_refl ((term24 t2) = (term25 t2))). Qed.
Lemma lem9994 (t1 : Prop) (t2 : Prop) : ((term22 t2 t1) = ((term24 t2) = (term25 t2))) = (((term27 t1 t2) = (term28 t1 t2)) = ((term24 t2) = (term25 t2))).
Proof. exact (MK_COMB (@lem9992 t1 t2) (@lem9993 t2)). Qed.
Lemma lem9995 (t1 : Prop) (t2 : Prop) : ((term22 t2 t1) = (term23 t2)) = (((term27 t1 t2) = (term28 t1 t2)) = ((term24 t2) = (term25 t2))).
Proof. exact (TRANS (@lem9989 t1 t2) (@lem9994 t1 t2)). Qed.
Lemma lem9996 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : ((term27 t1 t2) = (term28 t1 t2)) = ((term24 t2) = (term25 t2)).
Proof. exact (EQ_MP (@lem9995 t1 t2) (@lem9986 t2 t1 h1)). Qed.
Lemma lem9997 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : ((term24 t2) = (term25 t2)) = ((term27 t1 t2) = (term28 t1 t2)).
Proof. exact (SYM (@lem9996 t2 t1 h1)). Qed.
Lemma lem9998 (t2 : Prop) : (term21 t2) = (term21 t2).
Proof. exact (eq_refl (term21 t2)). Qed.
Lemma lem9999 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : (term22 t2 t1) = (term30 t2).
Proof. exact (MK_COMB (@lem9998 t2) (@lem9976 t1 h1)). Qed.
Lemma lem10000 (t2 : Prop) : (term30 t2) = ((term31 t2) = (term32 t2)).
Proof. exact (eq_refl (term30 t2)). Qed.
Lemma lem10001 (t2 : Prop) (t1 : Prop) : (term26 t2 t1) = (term26 t2 t1).
Proof. exact (eq_refl (term26 t2 t1)). Qed.
Lemma lem10002 (t1 : Prop) (t2 : Prop) : ((term22 t2 t1) = (term30 t2)) = ((term22 t2 t1) = ((term31 t2) = (term32 t2))).
Proof. exact (MK_COMB (@lem10001 t2 t1) (@lem10000 t2)). Qed.
Lemma lem10003 (t1 : Prop) (t2 : Prop) : (term22 t2 t1) = ((term27 t1 t2) = (term28 t1 t2)).
Proof. exact (eq_refl (term22 t2 t1)). Qed.
Lemma lem10004 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10005 (t1 : Prop) (t2 : Prop) : (term26 t2 t1) = (term29 t1 t2).
Proof. exact (MK_COMB (@lem10004) (@lem10003 t1 t2)). Qed.
Lemma lem10006 (t2 : Prop) : ((term31 t2) = (term32 t2)) = ((term31 t2) = (term32 t2)).
Proof. exact (eq_refl ((term31 t2) = (term32 t2))). Qed.
Lemma lem10007 (t1 : Prop) (t2 : Prop) : ((term22 t2 t1) = ((term31 t2) = (term32 t2))) = (((term27 t1 t2) = (term28 t1 t2)) = ((term31 t2) = (term32 t2))).
Proof. exact (MK_COMB (@lem10005 t1 t2) (@lem10006 t2)). Qed.
Lemma lem10008 (t1 : Prop) (t2 : Prop) : ((term22 t2 t1) = (term30 t2)) = (((term27 t1 t2) = (term28 t1 t2)) = ((term31 t2) = (term32 t2))).
Proof. exact (TRANS (@lem10002 t1 t2) (@lem10007 t1 t2)). Qed.
Lemma lem10009 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : ((term27 t1 t2) = (term28 t1 t2)) = ((term31 t2) = (term32 t2)).
Proof. exact (EQ_MP (@lem10008 t1 t2) (@lem9999 t2 t1 h1)). Qed.
Lemma lem10010 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : ((term31 t2) = (term32 t2)) = ((term27 t1 t2) = (term28 t1 t2)).
Proof. exact (SYM (@lem10009 t2 t1 h1)). Qed.
Lemma lem10014 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem10015 (t2 : Prop) : (True \/ t2) = True.
Proof. exact (@lem10014 t2). Qed.
Lemma lem10016 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem10017 (t2 : Prop) : (term24 t2) = (~ True).
Proof. exact (MK_COMB (@lem10016) (@lem10015 t2)). Qed.
Lemma lem10019 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem10020 (t2 : Prop) : (term24 t2) = False.
Proof. exact (TRANS (@lem10017 t2) (@lem10019)). Qed.
Lemma lem10021 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10022 (t2 : Prop) : (term33 t2) = (@eq Prop False).
Proof. exact (MK_COMB (@lem10021) (@lem10020 t2)). Qed.
Lemma lem10026 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem10027 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem10028 : term34 = (and False).
Proof. exact (MK_COMB (@lem10027) (@lem10026)). Qed.
Lemma lem10029 (t2 : Prop) : (~ t2) = (~ t2).
Proof. exact (eq_refl (~ t2)). Qed.
Lemma lem10030 (t2 : Prop) : (term25 t2) = (term35 t2).
Proof. exact (MK_COMB (@lem10028) (@lem10029 t2)). Qed.
Lemma lem10032 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem10033 (t2 : Prop) : (term35 t2) = False.
Proof. exact (@lem10032 (~ t2)). Qed.
Lemma lem10034 (t2 : Prop) : (term25 t2) = False.
Proof. exact (TRANS (@lem10030 t2) (@lem10033 t2)). Qed.
Lemma lem10035 (t2 : Prop) : ((term24 t2) = (term25 t2)) = (False = False).
Proof. exact (MK_COMB (@lem10022 t2) (@lem10034 t2)). Qed.
Lemma lem10037 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem10038 : (False = False) = (~ False).
Proof. exact (@lem10037 False). Qed.
Lemma lem10040 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem10041 : (False = False) = True.
Proof. exact (TRANS (@lem10038) (@lem10040)). Qed.
Lemma lem10042 (t2 : Prop) : ((term24 t2) = (term25 t2)) = True.
Proof. exact (TRANS (@lem10035 t2) (@lem10041)). Qed.
Lemma lem10043 (t2 : Prop) : True = ((term24 t2) = (term25 t2)).
Proof. exact (SYM (@lem10042 t2)). Qed.
Lemma lem10044 (t2 : Prop) : (term24 t2) = (term25 t2).
Proof. exact (EQ_MP (@lem10043 t2) (@lem0)). Qed.
Lemma lem10048 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem10049 (t2 : Prop) : (False \/ t2) = t2.
Proof. exact (@lem10048 t2). Qed.
Lemma lem10050 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem10051 (t2 : Prop) : (term31 t2) = (~ t2).
Proof. exact (MK_COMB (@lem10050) (@lem10049 t2)). Qed.
Lemma lem10052 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10053 (t2 : Prop) : (term36 t2) = (term15 t2).
Proof. exact (MK_COMB (@lem10052) (@lem10051 t2)). Qed.
Lemma lem10057 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem10058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem10059 : term37 = (and True).
Proof. exact (MK_COMB (@lem10058) (@lem10057)). Qed.
Lemma lem10060 (t2 : Prop) : (~ t2) = (~ t2).
Proof. exact (eq_refl (~ t2)). Qed.
Lemma lem10061 (t2 : Prop) : (term32 t2) = (term38 t2).
Proof. exact (MK_COMB (@lem10059) (@lem10060 t2)). Qed.
Lemma lem10063 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem10064 (t2 : Prop) : (term38 t2) = (~ t2).
Proof. exact (@lem10063 (~ t2)). Qed.
Lemma lem10065 (t2 : Prop) : (term32 t2) = (~ t2).
Proof. exact (TRANS (@lem10061 t2) (@lem10064 t2)). Qed.
Lemma lem10066 (t2 : Prop) : ((term31 t2) = (term32 t2)) = ((~ t2) = (~ t2)).
Proof. exact (MK_COMB (@lem10053 t2) (@lem10065 t2)). Qed.
Lemma lem10068 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem10069 (x : Prop) : (x = x) = True.
Proof. exact (@lem10068 Prop x). Qed.
Lemma lem10070 (t2 : Prop) : ((~ t2) = (~ t2)) = True.
Proof. exact (@lem10069 (~ t2)). Qed.
Lemma lem10071 (t2 : Prop) : ((term31 t2) = (term32 t2)) = True.
Proof. exact (TRANS (@lem10066 t2) (@lem10070 t2)). Qed.
Lemma lem10072 (t2 : Prop) : True = ((term31 t2) = (term32 t2)).
Proof. exact (SYM (@lem10071 t2)). Qed.
Lemma lem10073 (t2 : Prop) : (term31 t2) = (term32 t2).
Proof. exact (EQ_MP (@lem10072 t2) (@lem0)). Qed.
Lemma lem10074 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : (term27 t1 t2) = (term28 t1 t2).
Proof. exact (EQ_MP (@lem10010 t2 t1 h1) (@lem10073 t2)). Qed.
Lemma lem10075 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : (term27 t1 t2) = (term28 t1 t2).
Proof. exact (EQ_MP (@lem9997 t2 t1 h1) (@lem10044 t2)). Qed.
Lemma lem10078 (t1 : Prop) (t2 : Prop) : (term27 t1 t2) = (term28 t1 t2).
Proof. exact (or_elim (@lem9974 t1) (fun h0 : t1 = True => @lem10075 t2 t1 h0) (fun h0 : t1 = False => @lem10074 t2 t1 h0)). Qed.
Lemma lem10079 (t1 : Prop) (t2 : Prop) : term39 t1 t2.
Proof. exact (conj (@lem9963 t1 t2) (@lem10078 t1 t2)). Qed.
Lemma lem10084 (t1 : Prop) : term40 t1.
Proof. exact (fun t2 : Prop => @lem10079 t1 t2). Qed.
Lemma lem10089 : term41.
Proof. exact (fun t1 : Prop => @lem10084 t1). Qed.
