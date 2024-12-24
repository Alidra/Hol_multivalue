Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LTE_TOTAL_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm1832_spec.
Require Import thm1834_spec.
Lemma lem1367935 (y : real) : term0 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1367936 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem1367937 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem1367936 y) (@lem1367935 y)). Qed.
Lemma lem1367938 (y : real) (x : real) : term2 y x.
Proof. exact (@lem1367937 y x). Qed.
Lemma lem1367939 (y : real) (x : real) : (term2 y x) = ((real_lt x y) = (term3 y x)).
Proof. exact (eq_refl (term2 y x)). Qed.
Lemma lem1367952 (y : real) (x : real) : (real_lt x y) = (term3 y x).
Proof. exact (EQ_MP (@lem1367939 y x) (@lem1367938 y x)). Qed.
Lemma lem1367953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1367954 (y : real) (x : real) : (term4 x y) = (term5 y x).
Proof. exact (MK_COMB (@lem1367953) (@lem1367952 y x)). Qed.
Lemma lem1367955 (y : real) (x : real) : (real_le y x) = (real_le y x).
Proof. exact (eq_refl (real_le y x)). Qed.
Lemma lem1367956 (y : real) (x : real) : (term6 y x) = (term7 y x).
Proof. exact (MK_COMB (@lem1367954 y x) (@lem1367955 y x)). Qed.
Lemma lem1367959 (x : real) : (term8 x) = (term9 x).
Proof. exact (fun_ext (fun y : real => @lem1367956 y x)). Qed.
Lemma lem1367960 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1367961 (x : real) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem1367960) (@lem1367959 x)). Qed.
Lemma lem1367966 : term12 = term13.
Proof. exact (fun_ext (fun x : real => @lem1367961 x)). Qed.
Lemma lem1367967 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1367968 : term14 = term15.
Proof. exact (MK_COMB (@lem1367967) (@lem1367966)). Qed.
Lemma lem1367973 : term15 = term14.
Proof. exact (SYM (@lem1367968)). Qed.
Lemma lem1367978 (y : real) (x : real) : term16 y x.
Proof. exact (@lem9851 (real_le y x)). Qed.
Lemma lem1367979 (y : real) (x : real) : (term16 y x) = (term17 y x).
Proof. exact (eq_refl (term16 y x)). Qed.
Lemma lem1367980 (y : real) (x : real) : term17 y x.
Proof. exact (EQ_MP (@lem1367979 y x) (@lem1367978 y x)). Qed.
Lemma lem1367981 (y : real) (x : real) (h1 : (real_le y x) = True) : (real_le y x) = True.
Proof. exact (h1). Qed.
Lemma lem1367982 (y : real) (x : real) (h1 : (real_le y x) = False) : (real_le y x) = False.
Proof. exact (h1). Qed.
Lemma lem1367987 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1367988 (y : real) (x : real) (h1 : (real_le y x) = True) : (term19 y x) = term20.
Proof. exact (MK_COMB (@lem1367987) (@lem1367981 y x h1)). Qed.
Lemma lem1367989 : term20 = term21.
Proof. exact (eq_refl term20). Qed.
Lemma lem1367990 (y : real) (x : real) : (term22 y x) = (term22 y x).
Proof. exact (eq_refl (term22 y x)). Qed.
Lemma lem1367991 (y : real) (x : real) : ((term19 y x) = term20) = ((term19 y x) = term21).
Proof. exact (MK_COMB (@lem1367990 y x) (@lem1367989)). Qed.
Lemma lem1367992 (y : real) (x : real) : (term19 y x) = (term7 y x).
Proof. exact (eq_refl (term19 y x)). Qed.
Lemma lem1367993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1367994 (y : real) (x : real) : (term22 y x) = (term23 y x).
Proof. exact (MK_COMB (@lem1367993) (@lem1367992 y x)). Qed.
Lemma lem1367995 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1367996 (y : real) (x : real) : ((term19 y x) = term21) = ((term7 y x) = term21).
Proof. exact (MK_COMB (@lem1367994 y x) (@lem1367995)). Qed.
Lemma lem1367997 (y : real) (x : real) : ((term19 y x) = term20) = ((term7 y x) = term21).
Proof. exact (TRANS (@lem1367991 y x) (@lem1367996 y x)). Qed.
Lemma lem1367998 (y : real) (x : real) (h1 : (real_le y x) = True) : (term7 y x) = term21.
Proof. exact (EQ_MP (@lem1367997 y x) (@lem1367988 y x h1)). Qed.
Lemma lem1367999 (y : real) (x : real) (h1 : (real_le y x) = True) : term21 = (term7 y x).
Proof. exact (SYM (@lem1367998 y x h1)). Qed.
Lemma lem1368000 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1368001 (y : real) (x : real) (h1 : (real_le y x) = False) : (term19 y x) = term24.
Proof. exact (MK_COMB (@lem1368000) (@lem1367982 y x h1)). Qed.
Lemma lem1368002 : term24 = term25.
Proof. exact (eq_refl term24). Qed.
Lemma lem1368003 (y : real) (x : real) : (term22 y x) = (term22 y x).
Proof. exact (eq_refl (term22 y x)). Qed.
Lemma lem1368004 (y : real) (x : real) : ((term19 y x) = term24) = ((term19 y x) = term25).
Proof. exact (MK_COMB (@lem1368003 y x) (@lem1368002)). Qed.
Lemma lem1368005 (y : real) (x : real) : (term19 y x) = (term7 y x).
Proof. exact (eq_refl (term19 y x)). Qed.
Lemma lem1368006 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1368007 (y : real) (x : real) : (term22 y x) = (term23 y x).
Proof. exact (MK_COMB (@lem1368006) (@lem1368005 y x)). Qed.
Lemma lem1368008 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem1368009 (y : real) (x : real) : ((term19 y x) = term25) = ((term7 y x) = term25).
Proof. exact (MK_COMB (@lem1368007 y x) (@lem1368008)). Qed.
Lemma lem1368010 (y : real) (x : real) : ((term19 y x) = term24) = ((term7 y x) = term25).
Proof. exact (TRANS (@lem1368004 y x) (@lem1368009 y x)). Qed.
Lemma lem1368011 (y : real) (x : real) (h1 : (real_le y x) = False) : (term7 y x) = term25.
Proof. exact (EQ_MP (@lem1368010 y x) (@lem1368001 y x h1)). Qed.
Lemma lem1368012 (y : real) (x : real) (h1 : (real_le y x) = False) : term25 = (term7 y x).
Proof. exact (SYM (@lem1368011 y x h1)). Qed.
Lemma lem1368014 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1368015 : term21 = True.
Proof. exact (@lem1368014 (~ True)). Qed.
Lemma lem1368016 : True = term21.
Proof. exact (SYM (@lem1368015)). Qed.
Lemma lem1368017 : term21.
Proof. exact (EQ_MP (@lem1368016) (@lem0)). Qed.
Lemma lem1368019 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1368020 : term25 = (~ False).
Proof. exact (@lem1368019 (~ False)). Qed.
Lemma lem1368022 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1368023 : term25 = True.
Proof. exact (TRANS (@lem1368020) (@lem1368022)). Qed.
Lemma lem1368024 : True = term25.
Proof. exact (SYM (@lem1368023)). Qed.
Lemma lem1368025 : term25.
Proof. exact (EQ_MP (@lem1368024) (@lem0)). Qed.
Lemma lem1368026 (y : real) (x : real) (h1 : (real_le y x) = False) : term7 y x.
Proof. exact (EQ_MP (@lem1368012 y x h1) (@lem1368025)). Qed.
Lemma lem1368027 (y : real) (x : real) (h1 : (real_le y x) = True) : term7 y x.
Proof. exact (EQ_MP (@lem1367999 y x h1) (@lem1368017)). Qed.
Lemma lem1368030 (y : real) (x : real) : term7 y x.
Proof. exact (or_elim (@lem1367980 y x) (fun h0 : (real_le y x) = True => @lem1368027 y x h0) (fun h0 : (real_le y x) = False => @lem1368026 y x h0)). Qed.
Lemma lem1368035 (x : real) : term11 x.
Proof. exact (fun y : real => @lem1368030 y x). Qed.
Lemma lem1368040 : term15.
Proof. exact (fun x : real => @lem1368035 x). Qed.
Lemma lem1368041 : term14.
Proof. exact (EQ_MP (@lem1367973) (@lem1368040)). Qed.
