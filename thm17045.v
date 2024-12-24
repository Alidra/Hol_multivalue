Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17045_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem16942 (p : Prop) : term0 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem16943 (p : Prop) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem16944 (p : Prop) : term1 p.
Proof. exact (EQ_MP (@lem16943 p) (@lem16942 p)). Qed.
Lemma lem16945 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem16946 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem16955 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem16956 (q : Prop) (p : Prop) (h1 : p = True) : (term3 q p) = (term4 q).
Proof. exact (MK_COMB (@lem16955 q) (@lem16945 p h1)). Qed.
Lemma lem16957 (q : Prop) : (term4 q) = ((term5 q) = (term6 q)).
Proof. exact (eq_refl (term4 q)). Qed.
Lemma lem16958 (q : Prop) (p : Prop) : (term7 q p) = (term7 q p).
Proof. exact (eq_refl (term7 q p)). Qed.
Lemma lem16959 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = ((term3 q p) = ((term5 q) = (term6 q))).
Proof. exact (MK_COMB (@lem16958 q p) (@lem16957 q)). Qed.
Lemma lem16960 (p : Prop) (q : Prop) : (term3 q p) = ((term8 p q) = (term9 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem16961 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16962 (p : Prop) (q : Prop) : (term7 q p) = (term10 p q).
Proof. exact (MK_COMB (@lem16961) (@lem16960 p q)). Qed.
Lemma lem16963 (q : Prop) : ((term5 q) = (term6 q)) = ((term5 q) = (term6 q)).
Proof. exact (eq_refl ((term5 q) = (term6 q))). Qed.
Lemma lem16964 (p : Prop) (q : Prop) : ((term3 q p) = ((term5 q) = (term6 q))) = (((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q))).
Proof. exact (MK_COMB (@lem16962 p q) (@lem16963 q)). Qed.
Lemma lem16965 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = (((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q))).
Proof. exact (TRANS (@lem16959 p q) (@lem16964 p q)). Qed.
Lemma lem16966 (q : Prop) (p : Prop) (h1 : p = True) : ((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q)).
Proof. exact (EQ_MP (@lem16965 p q) (@lem16956 q p h1)). Qed.
Lemma lem16967 (q : Prop) (p : Prop) (h1 : p = True) : ((term5 q) = (term6 q)) = ((term8 p q) = (term9 p q)).
Proof. exact (SYM (@lem16966 q p h1)). Qed.
Lemma lem16968 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem16969 (q : Prop) (p : Prop) (h1 : p = False) : (term3 q p) = (term11 q).
Proof. exact (MK_COMB (@lem16968 q) (@lem16946 p h1)). Qed.
Lemma lem16970 (q : Prop) : (term11 q) = ((term12 q) = (term13 q)).
Proof. exact (eq_refl (term11 q)). Qed.
Lemma lem16971 (q : Prop) (p : Prop) : (term7 q p) = (term7 q p).
Proof. exact (eq_refl (term7 q p)). Qed.
Lemma lem16972 (p : Prop) (q : Prop) : ((term3 q p) = (term11 q)) = ((term3 q p) = ((term12 q) = (term13 q))).
Proof. exact (MK_COMB (@lem16971 q p) (@lem16970 q)). Qed.
Lemma lem16973 (p : Prop) (q : Prop) : (term3 q p) = ((term8 p q) = (term9 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem16974 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16975 (p : Prop) (q : Prop) : (term7 q p) = (term10 p q).
Proof. exact (MK_COMB (@lem16974) (@lem16973 p q)). Qed.
Lemma lem16976 (q : Prop) : ((term12 q) = (term13 q)) = ((term12 q) = (term13 q)).
Proof. exact (eq_refl ((term12 q) = (term13 q))). Qed.
Lemma lem16977 (p : Prop) (q : Prop) : ((term3 q p) = ((term12 q) = (term13 q))) = (((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q))).
Proof. exact (MK_COMB (@lem16975 p q) (@lem16976 q)). Qed.
Lemma lem16978 (p : Prop) (q : Prop) : ((term3 q p) = (term11 q)) = (((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q))).
Proof. exact (TRANS (@lem16972 p q) (@lem16977 p q)). Qed.
Lemma lem16979 (q : Prop) (p : Prop) (h1 : p = False) : ((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q)).
Proof. exact (EQ_MP (@lem16978 p q) (@lem16969 q p h1)). Qed.
Lemma lem16980 (q : Prop) (p : Prop) (h1 : p = False) : ((term12 q) = (term13 q)) = ((term8 p q) = (term9 p q)).
Proof. exact (SYM (@lem16979 q p h1)). Qed.
Lemma lem16984 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem16985 (q : Prop) : (True /\ q) = q.
Proof. exact (@lem16984 q). Qed.
Lemma lem16986 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem16987 (q : Prop) : (term5 q) = (~ q).
Proof. exact (MK_COMB (@lem16986) (@lem16985 q)). Qed.
Lemma lem16988 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16989 (q : Prop) : (term14 q) = (term15 q).
Proof. exact (MK_COMB (@lem16988) (@lem16987 q)). Qed.
Lemma lem16993 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem16994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem16995 : term16 = (or False).
Proof. exact (MK_COMB (@lem16994) (@lem16993)). Qed.
Lemma lem16996 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem16997 (q : Prop) : (term6 q) = (term17 q).
Proof. exact (MK_COMB (@lem16995) (@lem16996 q)). Qed.
Lemma lem16999 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem17000 (q : Prop) : (term17 q) = (~ q).
Proof. exact (@lem16999 (~ q)). Qed.
Lemma lem17001 (q : Prop) : (term6 q) = (~ q).
Proof. exact (TRANS (@lem16997 q) (@lem17000 q)). Qed.
Lemma lem17002 (q : Prop) : ((term5 q) = (term6 q)) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem16989 q) (@lem17001 q)). Qed.
Lemma lem17004 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem17005 (x : Prop) : (x = x) = True.
Proof. exact (@lem17004 Prop x). Qed.
Lemma lem17006 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem17005 (~ q)). Qed.
Lemma lem17007 (q : Prop) : ((term5 q) = (term6 q)) = True.
Proof. exact (TRANS (@lem17002 q) (@lem17006 q)). Qed.
Lemma lem17008 (q : Prop) : True = ((term5 q) = (term6 q)).
Proof. exact (SYM (@lem17007 q)). Qed.
Lemma lem17009 (q : Prop) : (term5 q) = (term6 q).
Proof. exact (EQ_MP (@lem17008 q) (@lem0)). Qed.
Lemma lem17013 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem17014 (q : Prop) : (False /\ q) = False.
Proof. exact (@lem17013 q). Qed.
Lemma lem17015 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem17016 (q : Prop) : (term12 q) = (~ False).
Proof. exact (MK_COMB (@lem17015) (@lem17014 q)). Qed.
Lemma lem17018 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem17019 (q : Prop) : (term12 q) = True.
Proof. exact (TRANS (@lem17016 q) (@lem17018)). Qed.
Lemma lem17020 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17021 (q : Prop) : (term18 q) = (@eq Prop True).
Proof. exact (MK_COMB (@lem17020) (@lem17019 q)). Qed.
Lemma lem17025 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem17026 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem17027 : term19 = (or True).
Proof. exact (MK_COMB (@lem17026) (@lem17025)). Qed.
Lemma lem17028 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem17029 (q : Prop) : (term13 q) = (term20 q).
Proof. exact (MK_COMB (@lem17027) (@lem17028 q)). Qed.
Lemma lem17031 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem17032 (q : Prop) : (term20 q) = True.
Proof. exact (@lem17031 (~ q)). Qed.
Lemma lem17033 (q : Prop) : (term13 q) = True.
Proof. exact (TRANS (@lem17029 q) (@lem17032 q)). Qed.
Lemma lem17034 (q : Prop) : ((term12 q) = (term13 q)) = (True = True).
Proof. exact (MK_COMB (@lem17021 q) (@lem17033 q)). Qed.
Lemma lem17036 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem17037 : (True = True) = True.
Proof. exact (@lem17036 True). Qed.
Lemma lem17038 (q : Prop) : ((term12 q) = (term13 q)) = True.
Proof. exact (TRANS (@lem17034 q) (@lem17037)). Qed.
Lemma lem17039 (q : Prop) : True = ((term12 q) = (term13 q)).
Proof. exact (SYM (@lem17038 q)). Qed.
Lemma lem17040 (q : Prop) : (term12 q) = (term13 q).
Proof. exact (EQ_MP (@lem17039 q) (@lem0)). Qed.
Lemma lem17041 (q : Prop) (p : Prop) (h1 : p = False) : (term8 p q) = (term9 p q).
Proof. exact (EQ_MP (@lem16980 q p h1) (@lem17040 q)). Qed.
Lemma lem17042 (q : Prop) (p : Prop) (h1 : p = True) : (term8 p q) = (term9 p q).
Proof. exact (EQ_MP (@lem16967 q p h1) (@lem17009 q)). Qed.
Lemma lem17045 (p : Prop) (q : Prop) : (term8 p q) = (term9 p q).
Proof. exact (or_elim (@lem16944 p) (fun h0 : p = True => @lem17042 q p h0) (fun h0 : p = False => @lem17041 q p h0)). Qed.
