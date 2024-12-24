Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_REM_POS_EQ_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import INT_REM_0_spec.
Require Import INT_REM_POS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem2396894 (n : int) : term0 n.
Proof. exact (@lem9784 (n = term1)). Qed.
Lemma lem2396895 (n : int) : (term0 n) = (term2 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2396896 (n : int) : term2 n.
Proof. exact (EQ_MP (@lem2396895 n) (@lem2396894 n)). Qed.
Lemma lem2396898 (n : int) (h1 : term3 n) : term3 n.
Proof. exact (h1). Qed.
Lemma lem2396914 (m : int) : term4 m.
Proof. exact (@lem2396893 m). Qed.
Lemma lem2396915 (m : int) : (term4 m) = ((term5 m) = m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem2396942 (n : int) (h1 : n = term1) : n = term1.
Proof. exact (h1). Qed.
Lemma lem2396943 (m : int) : (rem m) = (rem m).
Proof. exact (eq_refl (rem m)). Qed.
Lemma lem2396944 (m : int) (n : int) (h1 : n = term1) : (rem m n) = (term5 m).
Proof. exact (MK_COMB (@lem2396943 m) (@lem2396942 n h1)). Qed.
Lemma lem2396946 (m : int) : (term5 m) = m.
Proof. exact (EQ_MP (@lem2396915 m) (@lem2396914 m)). Qed.
Lemma lem2396947 (m : int) (n : int) (h1 : n = term1) : (rem m n) = m.
Proof. exact (TRANS (@lem2396944 m n h1) (@lem2396946 m)). Qed.
Lemma lem2396948 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem2396949 (m : int) (n : int) (h1 : n = term1) : (term7 m n) = (term8 m).
Proof. exact (MK_COMB (@lem2396948) (@lem2396947 m n h1)). Qed.
Lemma lem2396950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2396951 (m : int) (n : int) (h1 : n = term1) : (term9 m n) = (term10 m).
Proof. exact (MK_COMB (@lem2396950) (@lem2396949 m n h1)). Qed.
Lemma lem2396957 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term11 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem2396958 (p : Prop) (q : Prop) (p' : Prop) : term12 p q p'.
Proof. exact (fun q' : Prop => @lem2396957 p q p' q'). Qed.
Lemma lem2396959 (p : Prop) (q : Prop) : term13 p q.
Proof. exact (fun p' : Prop => @lem2396958 p q p'). Qed.
Lemma lem2396960 (n : int) (m : int) : term14 n m.
Proof. exact (@lem2396959 (n = term1) (term8 m)). Qed.
Lemma lem2396961 (n : int) (m : int) (p' : Prop) : term15 n m p'.
Proof. exact (@lem2396960 n m p'). Qed.
Lemma lem2396962 (n : int) (m : int) (p' : Prop) : (term15 n m p') = (term16 n m p').
Proof. exact (eq_refl (term15 n m p')). Qed.
Lemma lem2396963 (n : int) (m : int) (p' : Prop) : term16 n m p'.
Proof. exact (EQ_MP (@lem2396962 n m p') (@lem2396961 n m p')). Qed.
Lemma lem2396964 (n : int) (m : int) (p' : Prop) (q' : Prop) : term17 n m p' q'.
Proof. exact (@lem2396963 n m p' q'). Qed.
Lemma lem2396965 (n : int) (m : int) (p' : Prop) (q' : Prop) : (term17 n m p' q') = (term18 n m p' q').
Proof. exact (eq_refl (term17 n m p' q')). Qed.
Lemma lem2396966 (n : int) (m : int) (p' : Prop) (q' : Prop) : term18 n m p' q'.
Proof. exact (EQ_MP (@lem2396965 n m p' q') (@lem2396964 n m p' q')). Qed.
Lemma lem2396970 (n : int) (h1 : n = term1) : n = term1.
Proof. exact (h1). Qed.
Lemma lem2396971 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2396972 (n : int) (h1 : n = term1) : (@eq int n) = term19.
Proof. exact (MK_COMB (@lem2396971) (@lem2396970 n h1)). Qed.
Lemma lem2396973 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem2396974 (n : int) (h1 : n = term1) : (n = term1) = (term1 = term1).
Proof. exact (MK_COMB (@lem2396972 n h1) (@lem2396973)). Qed.
Lemma lem2396976 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2396977 (x : int) : (x = x) = True.
Proof. exact (@lem2396976 int x). Qed.
Lemma lem2396978 : (term1 = term1) = True.
Proof. exact (@lem2396977 term1). Qed.
Lemma lem2396979 (n : int) (h1 : n = term1) : (n = term1) = True.
Proof. exact (TRANS (@lem2396974 n h1) (@lem2396978)). Qed.
Lemma lem2396980 (n : int) (m : int) (q' : Prop) : term20 n m q'.
Proof. exact (@lem2396966 n m True q'). Qed.
Lemma lem2396981 (m : int) (q' : Prop) (n : int) (h1 : n = term1) : term21 n m q'.
Proof. exact (@lem2396980 n m q' (@lem2396979 n h1)). Qed.
Lemma lem2396987 (m : int) : (term8 m) = (term8 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem2396988 (m : int) : term22 m.
Proof. exact (fun h0 : True => @lem2396987 m). Qed.
Lemma lem2396989 (m : int) (n : int) (h1 : n = term1) : term23 n m.
Proof. exact (@lem2396981 m (term8 m) n h1). Qed.
Lemma lem2396990 (m : int) (n : int) (h1 : n = term1) : (term24 n m) = (term25 m).
Proof. exact (@lem2396989 m n h1 (@lem2396988 m)). Qed.
Lemma lem2396992 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem2396993 (m : int) : (term25 m) = (term8 m).
Proof. exact (@lem2396992 (term8 m)). Qed.
Lemma lem2396994 (m : int) (n : int) (h1 : n = term1) : (term24 n m) = (term8 m).
Proof. exact (TRANS (@lem2396990 m n h1) (@lem2396993 m)). Qed.
Lemma lem2396995 (m : int) (n : int) (h1 : n = term1) : ((term7 m n) = (term24 n m)) = ((term8 m) = (term8 m)).
Proof. exact (MK_COMB (@lem2396951 m n h1) (@lem2396994 m n h1)). Qed.
Lemma lem2396997 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2396998 (x : Prop) : (x = x) = True.
Proof. exact (@lem2396997 Prop x). Qed.
Lemma lem2396999 (m : int) : ((term8 m) = (term8 m)) = True.
Proof. exact (@lem2396998 (term8 m)). Qed.
Lemma lem2397000 (m : int) (n : int) (h1 : n = term1) : ((term7 m n) = (term24 n m)) = True.
Proof. exact (TRANS (@lem2396995 m n h1) (@lem2396999 m)). Qed.
Lemma lem2397001 (m : int) (n : int) (h1 : n = term1) : True = ((term7 m n) = (term24 n m)).
Proof. exact (SYM (@lem2397000 m n h1)). Qed.
Lemma lem2397002 (m : int) (n : int) (h1 : n = term1) : (term7 m n) = (term24 n m).
Proof. exact (EQ_MP (@lem2397001 m n h1) (@lem0)). Qed.
Lemma lem2397003 (a : int) : term26 a.
Proof. exact (@lem2394837 a). Qed.
Lemma lem2397004 (a : int) : (term26 a) = (term27 a).
Proof. exact (eq_refl (term26 a)). Qed.
Lemma lem2397005 (a : int) : term27 a.
Proof. exact (EQ_MP (@lem2397004 a) (@lem2397003 a)). Qed.
Lemma lem2397006 (a : int) (b : int) : term28 a b.
Proof. exact (@lem2397005 a b). Qed.
Lemma lem2397007 (a : int) (b : int) : (term28 a b) = (term29 a b).
Proof. exact (eq_refl (term28 a b)). Qed.
Lemma lem2397008 (a : int) (b : int) : term29 a b.
Proof. exact (EQ_MP (@lem2397007 a b) (@lem2397006 a b)). Qed.
Lemma lem2397009 (b : int) (h1 : term3 b) : term3 b.
Proof. exact (h1). Qed.
Lemma lem2397010 (a : int) (b : int) (h1 : term3 b) : term7 a b.
Proof. exact (@lem2397008 a b (@lem2397009 b h1)). Qed.
Lemma lem2397011 (a : int) (b : int) : (term7 a b) = ((term7 a b) = True).
Proof. exact (@lem7 (term7 a b)). Qed.
Lemma lem2397012 (a : int) (b : int) (h1 : term3 b) : (term7 a b) = True.
Proof. exact (EQ_MP (@lem2397011 a b) (@lem2397010 a b h1)). Qed.
Lemma lem2397021 (n : int) : term30 n.
Proof. exact (@lem82 (n = term1)). Qed.
Lemma lem2397037 (a : int) (b : int) : term31 a b.
Proof. exact (fun h0 : term3 b => @lem2397012 a b h0). Qed.
Lemma lem2397038 (m : int) (n : int) : term31 m n.
Proof. exact (@lem2397037 m n). Qed.
Lemma lem2397040 (n : int) (h1 : term3 n) : (n = term1) = False.
Proof. exact (@lem2397021 n (@lem2396898 n h1)). Qed.
Lemma lem2397041 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2397042 (n : int) (h1 : term3 n) : (term3 n) = (~ False).
Proof. exact (MK_COMB (@lem2397041) (@lem2397040 n h1)). Qed.
Lemma lem2397044 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2397045 (n : int) (h1 : term3 n) : (term3 n) = True.
Proof. exact (TRANS (@lem2397042 n h1) (@lem2397044)). Qed.
Lemma lem2397046 (n : int) (h1 : term3 n) : True = (term3 n).
Proof. exact (SYM (@lem2397045 n h1)). Qed.
Lemma lem2397047 (n : int) (h1 : term3 n) : term3 n.
Proof. exact (EQ_MP (@lem2397046 n h1) (@lem0)). Qed.
Lemma lem2397048 (m : int) (n : int) (h1 : term3 n) : (term7 m n) = True.
Proof. exact (@lem2397038 m n (@lem2397047 n h1)). Qed.
Lemma lem2397049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2397050 (m : int) (n : int) (h1 : term3 n) : (term9 m n) = (@eq Prop True).
Proof. exact (MK_COMB (@lem2397049) (@lem2397048 m n h1)). Qed.
Lemma lem2397056 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term11 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem2397057 (p : Prop) (q : Prop) (p' : Prop) : term12 p q p'.
Proof. exact (fun q' : Prop => @lem2397056 p q p' q'). Qed.
Lemma lem2397058 (p : Prop) (q : Prop) : term13 p q.
Proof. exact (fun p' : Prop => @lem2397057 p q p'). Qed.
Lemma lem2397059 (n : int) (m : int) : term14 n m.
Proof. exact (@lem2397058 (n = term1) (term8 m)). Qed.
Lemma lem2397060 (n : int) (m : int) (p' : Prop) : term15 n m p'.
Proof. exact (@lem2397059 n m p'). Qed.
Lemma lem2397061 (n : int) (m : int) (p' : Prop) : (term15 n m p') = (term16 n m p').
Proof. exact (eq_refl (term15 n m p')). Qed.
Lemma lem2397062 (n : int) (m : int) (p' : Prop) : term16 n m p'.
Proof. exact (EQ_MP (@lem2397061 n m p') (@lem2397060 n m p')). Qed.
Lemma lem2397063 (n : int) (m : int) (p' : Prop) (q' : Prop) : term17 n m p' q'.
Proof. exact (@lem2397062 n m p' q'). Qed.
Lemma lem2397064 (n : int) (m : int) (p' : Prop) (q' : Prop) : (term17 n m p' q') = (term18 n m p' q').
Proof. exact (eq_refl (term17 n m p' q')). Qed.
Lemma lem2397065 (n : int) (m : int) (p' : Prop) (q' : Prop) : term18 n m p' q'.
Proof. exact (EQ_MP (@lem2397064 n m p' q') (@lem2397063 n m p' q')). Qed.
Lemma lem2397067 (n : int) (h1 : term3 n) : (n = term1) = False.
Proof. exact (@lem2397021 n (@lem2396898 n h1)). Qed.
Lemma lem2397068 (n : int) (m : int) (q' : Prop) : term32 n m q'.
Proof. exact (@lem2397065 n m False q'). Qed.
Lemma lem2397069 (m : int) (q' : Prop) (n : int) (h1 : term3 n) : term33 n m q'.
Proof. exact (@lem2397068 n m q' (@lem2397067 n h1)). Qed.
Lemma lem2397073 (m : int) : (term8 m) = (term8 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem2397074 (m : int) : term34 m.
Proof. exact (fun h0 : False => @lem2397073 m). Qed.
Lemma lem2397075 (m : int) (n : int) (h1 : term3 n) : term35 n m.
Proof. exact (@lem2397069 m (term8 m) n h1). Qed.
Lemma lem2397076 (m : int) (n : int) (h1 : term3 n) : (term24 n m) = (term36 m).
Proof. exact (@lem2397075 m n h1 (@lem2397074 m)). Qed.
Lemma lem2397078 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem2397079 (m : int) : (term36 m) = True.
Proof. exact (@lem2397078 (term8 m)). Qed.
Lemma lem2397080 (m : int) (n : int) (h1 : term3 n) : (term24 n m) = True.
Proof. exact (TRANS (@lem2397076 m n h1) (@lem2397079 m)). Qed.
Lemma lem2397081 (m : int) (n : int) (h1 : term3 n) : ((term7 m n) = (term24 n m)) = (True = True).
Proof. exact (MK_COMB (@lem2397050 m n h1) (@lem2397080 m n h1)). Qed.
Lemma lem2397083 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem2397084 : (True = True) = True.
Proof. exact (@lem2397083 True). Qed.
Lemma lem2397085 (m : int) (n : int) (h1 : term3 n) : ((term7 m n) = (term24 n m)) = True.
Proof. exact (TRANS (@lem2397081 m n h1) (@lem2397084)). Qed.
Lemma lem2397086 (m : int) (n : int) (h1 : term3 n) : True = ((term7 m n) = (term24 n m)).
Proof. exact (SYM (@lem2397085 m n h1)). Qed.
Lemma lem2397087 (m : int) (n : int) (h1 : term3 n) : (term7 m n) = (term24 n m).
Proof. exact (EQ_MP (@lem2397086 m n h1) (@lem0)). Qed.
Lemma lem2397088 (n : int) (m : int) : (term7 m n) = (term24 n m).
Proof. exact (or_elim (@lem2396896 n) (fun h0 : n = term1 => @lem2397002 m n h0) (fun h0 : term3 n => @lem2397087 m n h0)). Qed.
Lemma lem2397093 (m : int) : term37 m.
Proof. exact (fun n : int => @lem2397088 n m). Qed.
Lemma lem2397098 : term38.
Proof. exact (fun m : int => @lem2397093 m). Qed.
