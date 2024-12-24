Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1110222_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1109959 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1109960 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1109961 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1109960 A B f) (@lem1109959 A B f)). Qed.
Lemma lem1109962 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem1109961 A B f y). Qed.
Lemma lem1109963 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem1109966 {A : Type'} (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : PAIRWISE' = (term4 A _18053).
Proof. exact (h1). Qed.
Lemma lem1109967 {A : Type'} (r : type1402 A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1109968 {A : Type'} (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (PAIRWISE' r) = (term5 A _18053 r).
Proof. exact (MK_COMB (@lem1109966 A PAIRWISE' _18053 h1) (@lem1109967 A r)). Qed.
Lemma lem1109970 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109963 A B f y) (@lem1109962 A B f y)). Qed.
Lemma lem1109971 {A : Type'} (f : type416 A) (y : type1402 A) : (term6 A f y) = (f y).
Proof. exact (@lem1109970 (type1402 A) (type1143 A) f y). Qed.
Lemma lem1109972 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term7 A _18053 r) = (term5 A _18053 r).
Proof. exact (@lem1109971 A (term4 A _18053) r). Qed.
Lemma lem1109973 {A : Type'} (_18053 : type1127 A) (_18051 : type1402 A) : (term5 A _18053 _18051) = (term8 A _18053 _18051).
Proof. exact (eq_refl (term5 A _18053 _18051)). Qed.
Lemma lem1109974 {A : Type'} (_18053 : type1127 A) : (term9 A _18053) = (term4 A _18053).
Proof. exact (fun_ext (fun _18051 : type1402 A => @lem1109973 A _18053 _18051)). Qed.
Lemma lem1109975 {A : Type'} (r : type1402 A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1109976 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term7 A _18053 r) = (term5 A _18053 r).
Proof. exact (MK_COMB (@lem1109974 A _18053) (@lem1109975 A r)). Qed.
Lemma lem1109977 {A : Type'} : (@eq ((list A) -> Prop)) = (@eq ((list A) -> Prop)).
Proof. exact (eq_refl (@eq ((list A) -> Prop))). Qed.
Lemma lem1109978 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term10 A _18053 r) = (term11 A _18053 r).
Proof. exact (MK_COMB (@lem1109977 A) (@lem1109976 A _18053 r)). Qed.
Lemma lem1109979 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term5 A _18053 r) = (term8 A _18053 r).
Proof. exact (eq_refl (term5 A _18053 r)). Qed.
Lemma lem1109980 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : ((term7 A _18053 r) = (term5 A _18053 r)) = ((term5 A _18053 r) = (term8 A _18053 r)).
Proof. exact (MK_COMB (@lem1109978 A _18053 r) (@lem1109979 A _18053 r)). Qed.
Lemma lem1109981 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term5 A _18053 r) = (term8 A _18053 r).
Proof. exact (EQ_MP (@lem1109980 A _18053 r) (@lem1109972 A _18053 r)). Qed.
Lemma lem1109982 {A : Type'} (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (PAIRWISE' r) = (term8 A _18053 r).
Proof. exact (TRANS (@lem1109968 A r PAIRWISE' _18053 h1) (@lem1109981 A _18053 r)). Qed.
Lemma lem1109983 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1109984 {A : Type'} (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (PAIRWISE' r (@nil A)) = (term12 A _18053 r).
Proof. exact (MK_COMB (@lem1109982 A r PAIRWISE' _18053 h1) (@lem1109983 A)). Qed.
Lemma lem1109986 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109963 A B f y) (@lem1109962 A B f y)). Qed.
Lemma lem1109987 {A : Type'} (f : type1143 A) (y : list A) : (term13 A f y) = (f y).
Proof. exact (@lem1109986 (list A) Prop f y). Qed.
Lemma lem1109988 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term14 A _18053 r) = (term12 A _18053 r).
Proof. exact (@lem1109987 A (term8 A _18053 r) (@nil A)). Qed.
Lemma lem1109989 {A : Type'} (_18053 : type1127 A) (_18052 : list A) (r : type1402 A) : (term15 A _18053 r _18052) = (_18053 _18052 r).
Proof. exact (eq_refl (term15 A _18053 r _18052)). Qed.
Lemma lem1109990 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term16 A _18053 r) = (term8 A _18053 r).
Proof. exact (fun_ext (fun _18052 : list A => @lem1109989 A _18053 _18052 r)). Qed.
Lemma lem1109991 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1109992 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term14 A _18053 r) = (term12 A _18053 r).
Proof. exact (MK_COMB (@lem1109990 A _18053 r) (@lem1109991 A)). Qed.
Lemma lem1109993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1109994 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term17 A _18053 r) = (term18 A _18053 r).
Proof. exact (MK_COMB (@lem1109993) (@lem1109992 A _18053 r)). Qed.
Lemma lem1109995 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term12 A _18053 r) = (_18053 (@nil A) r).
Proof. exact (eq_refl (term12 A _18053 r)). Qed.
Lemma lem1109996 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : ((term14 A _18053 r) = (term12 A _18053 r)) = ((term12 A _18053 r) = (_18053 (@nil A) r)).
Proof. exact (MK_COMB (@lem1109994 A _18053 r) (@lem1109995 A _18053 r)). Qed.
Lemma lem1109997 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term12 A _18053 r) = (_18053 (@nil A) r).
Proof. exact (EQ_MP (@lem1109996 A _18053 r) (@lem1109988 A _18053 r)). Qed.
Lemma lem1109998 {A : Type'} (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (PAIRWISE' r (@nil A)) = (_18053 (@nil A) r).
Proof. exact (TRANS (@lem1109984 A r PAIRWISE' _18053 h1) (@lem1109997 A _18053 r)). Qed.
Lemma lem1109999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1110000 {A : Type'} (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term19 A PAIRWISE' r) = (term20 A _18053 r).
Proof. exact (MK_COMB (@lem1109999) (@lem1109998 A r PAIRWISE' _18053 h1)). Qed.
Lemma lem1110001 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem1110002 {A : Type'} (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : ((PAIRWISE' r (@nil A)) = True) = ((_18053 (@nil A) r) = True).
Proof. exact (MK_COMB (@lem1110000 A r PAIRWISE' _18053 h1) (@lem1110001)). Qed.
Lemma lem1110003 {A : Type'} (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term21 A PAIRWISE') = (term22 A _18053).
Proof. exact (fun_ext (fun r : type1402 A => @lem1110002 A r PAIRWISE' _18053 h1)). Qed.
Lemma lem1110004 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem1110005 {A : Type'} (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term23 A PAIRWISE') = (term24 A _18053).
Proof. exact (MK_COMB (@lem1110004 A) (@lem1110003 A PAIRWISE' _18053 h1)). Qed.
Lemma lem1110006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1110007 {A : Type'} (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term25 A PAIRWISE') = (term26 A _18053).
Proof. exact (MK_COMB (@lem1110006) (@lem1110005 A PAIRWISE' _18053 h1)). Qed.
Lemma lem1110009 {A : Type'} (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : PAIRWISE' = (term4 A _18053).
Proof. exact (h1). Qed.
Lemma lem1110010 {A : Type'} (r : type1402 A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1110011 {A : Type'} (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (PAIRWISE' r) = (term5 A _18053 r).
Proof. exact (MK_COMB (@lem1110009 A PAIRWISE' _18053 h1) (@lem1110010 A r)). Qed.
Lemma lem1110013 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109963 A B f y) (@lem1109962 A B f y)). Qed.
Lemma lem1110014 {A : Type'} (f : type416 A) (y : type1402 A) : (term6 A f y) = (f y).
Proof. exact (@lem1110013 (type1402 A) (type1143 A) f y). Qed.
Lemma lem1110015 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term7 A _18053 r) = (term5 A _18053 r).
Proof. exact (@lem1110014 A (term4 A _18053) r). Qed.
Lemma lem1110016 {A : Type'} (_18053 : type1127 A) (_18051 : type1402 A) : (term5 A _18053 _18051) = (term8 A _18053 _18051).
Proof. exact (eq_refl (term5 A _18053 _18051)). Qed.
Lemma lem1110017 {A : Type'} (_18053 : type1127 A) : (term9 A _18053) = (term4 A _18053).
Proof. exact (fun_ext (fun _18051 : type1402 A => @lem1110016 A _18053 _18051)). Qed.
Lemma lem1110018 {A : Type'} (r : type1402 A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1110019 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term7 A _18053 r) = (term5 A _18053 r).
Proof. exact (MK_COMB (@lem1110017 A _18053) (@lem1110018 A r)). Qed.
Lemma lem1110020 {A : Type'} : (@eq ((list A) -> Prop)) = (@eq ((list A) -> Prop)).
Proof. exact (eq_refl (@eq ((list A) -> Prop))). Qed.
Lemma lem1110021 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term10 A _18053 r) = (term11 A _18053 r).
Proof. exact (MK_COMB (@lem1110020 A) (@lem1110019 A _18053 r)). Qed.
Lemma lem1110022 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term5 A _18053 r) = (term8 A _18053 r).
Proof. exact (eq_refl (term5 A _18053 r)). Qed.
Lemma lem1110023 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : ((term7 A _18053 r) = (term5 A _18053 r)) = ((term5 A _18053 r) = (term8 A _18053 r)).
Proof. exact (MK_COMB (@lem1110021 A _18053 r) (@lem1110022 A _18053 r)). Qed.
Lemma lem1110024 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term5 A _18053 r) = (term8 A _18053 r).
Proof. exact (EQ_MP (@lem1110023 A _18053 r) (@lem1110015 A _18053 r)). Qed.
Lemma lem1110025 {A : Type'} (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (PAIRWISE' r) = (term8 A _18053 r).
Proof. exact (TRANS (@lem1110011 A r PAIRWISE' _18053 h1) (@lem1110024 A _18053 r)). Qed.
Lemma lem1110026 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@cons A h t).
Proof. exact (eq_refl (@cons A h t)). Qed.
Lemma lem1110027 {A : Type'} (r : type1402 A) (h : A) (t : list A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term27 A PAIRWISE' r h t) = (term28 A _18053 r h t).
Proof. exact (MK_COMB (@lem1110025 A r PAIRWISE' _18053 h1) (@lem1110026 A h t)). Qed.
Lemma lem1110029 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109963 A B f y) (@lem1109962 A B f y)). Qed.
Lemma lem1110030 {A : Type'} (f : type1143 A) (y : list A) : (term13 A f y) = (f y).
Proof. exact (@lem1110029 (list A) Prop f y). Qed.
Lemma lem1110031 {A : Type'} (_18053 : type1127 A) (r : type1402 A) (h : A) (t : list A) : (term29 A _18053 r h t) = (term28 A _18053 r h t).
Proof. exact (@lem1110030 A (term8 A _18053 r) (@cons A h t)). Qed.
Lemma lem1110032 {A : Type'} (_18053 : type1127 A) (_18052 : list A) (r : type1402 A) : (term15 A _18053 r _18052) = (_18053 _18052 r).
Proof. exact (eq_refl (term15 A _18053 r _18052)). Qed.
Lemma lem1110033 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term16 A _18053 r) = (term8 A _18053 r).
Proof. exact (fun_ext (fun _18052 : list A => @lem1110032 A _18053 _18052 r)). Qed.
Lemma lem1110034 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@cons A h t).
Proof. exact (eq_refl (@cons A h t)). Qed.
Lemma lem1110035 {A : Type'} (_18053 : type1127 A) (r : type1402 A) (h : A) (t : list A) : (term29 A _18053 r h t) = (term28 A _18053 r h t).
Proof. exact (MK_COMB (@lem1110033 A _18053 r) (@lem1110034 A h t)). Qed.
Lemma lem1110036 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1110037 {A : Type'} (_18053 : type1127 A) (r : type1402 A) (h : A) (t : list A) : (term30 A _18053 r h t) = (term31 A _18053 r h t).
Proof. exact (MK_COMB (@lem1110036) (@lem1110035 A _18053 r h t)). Qed.
Lemma lem1110038 {A : Type'} (_18053 : type1127 A) (h : A) (t : list A) (r : type1402 A) : (term28 A _18053 r h t) = (term32 A _18053 h t r).
Proof. exact (eq_refl (term28 A _18053 r h t)). Qed.
Lemma lem1110039 {A : Type'} (_18053 : type1127 A) (h : A) (t : list A) (r : type1402 A) : ((term29 A _18053 r h t) = (term28 A _18053 r h t)) = ((term28 A _18053 r h t) = (term32 A _18053 h t r)).
Proof. exact (MK_COMB (@lem1110037 A _18053 r h t) (@lem1110038 A _18053 h t r)). Qed.
Lemma lem1110040 {A : Type'} (_18053 : type1127 A) (h : A) (t : list A) (r : type1402 A) : (term28 A _18053 r h t) = (term32 A _18053 h t r).
Proof. exact (EQ_MP (@lem1110039 A _18053 h t r) (@lem1110031 A _18053 r h t)). Qed.
Lemma lem1110041 {A : Type'} (h : A) (t : list A) (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term27 A PAIRWISE' r h t) = (term32 A _18053 h t r).
Proof. exact (TRANS (@lem1110027 A r h t PAIRWISE' _18053 h1) (@lem1110040 A _18053 h t r)). Qed.
Lemma lem1110042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1110043 {A : Type'} (h : A) (t : list A) (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term33 A PAIRWISE' r h t) = (term34 A _18053 h t r).
Proof. exact (MK_COMB (@lem1110042) (@lem1110041 A h t r PAIRWISE' _18053 h1)). Qed.
Lemma lem1110045 {A : Type'} (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : PAIRWISE' = (term4 A _18053).
Proof. exact (h1). Qed.
Lemma lem1110046 {A : Type'} (r : type1402 A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1110047 {A : Type'} (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (PAIRWISE' r) = (term5 A _18053 r).
Proof. exact (MK_COMB (@lem1110045 A PAIRWISE' _18053 h1) (@lem1110046 A r)). Qed.
Lemma lem1110049 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109963 A B f y) (@lem1109962 A B f y)). Qed.
Lemma lem1110050 {A : Type'} (f : type416 A) (y : type1402 A) : (term6 A f y) = (f y).
Proof. exact (@lem1110049 (type1402 A) (type1143 A) f y). Qed.
Lemma lem1110051 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term7 A _18053 r) = (term5 A _18053 r).
Proof. exact (@lem1110050 A (term4 A _18053) r). Qed.
Lemma lem1110052 {A : Type'} (_18053 : type1127 A) (_18051 : type1402 A) : (term5 A _18053 _18051) = (term8 A _18053 _18051).
Proof. exact (eq_refl (term5 A _18053 _18051)). Qed.
Lemma lem1110053 {A : Type'} (_18053 : type1127 A) : (term9 A _18053) = (term4 A _18053).
Proof. exact (fun_ext (fun _18051 : type1402 A => @lem1110052 A _18053 _18051)). Qed.
Lemma lem1110054 {A : Type'} (r : type1402 A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1110055 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term7 A _18053 r) = (term5 A _18053 r).
Proof. exact (MK_COMB (@lem1110053 A _18053) (@lem1110054 A r)). Qed.
Lemma lem1110056 {A : Type'} : (@eq ((list A) -> Prop)) = (@eq ((list A) -> Prop)).
Proof. exact (eq_refl (@eq ((list A) -> Prop))). Qed.
Lemma lem1110057 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term10 A _18053 r) = (term11 A _18053 r).
Proof. exact (MK_COMB (@lem1110056 A) (@lem1110055 A _18053 r)). Qed.
Lemma lem1110058 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term5 A _18053 r) = (term8 A _18053 r).
Proof. exact (eq_refl (term5 A _18053 r)). Qed.
Lemma lem1110059 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : ((term7 A _18053 r) = (term5 A _18053 r)) = ((term5 A _18053 r) = (term8 A _18053 r)).
Proof. exact (MK_COMB (@lem1110057 A _18053 r) (@lem1110058 A _18053 r)). Qed.
Lemma lem1110060 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term5 A _18053 r) = (term8 A _18053 r).
Proof. exact (EQ_MP (@lem1110059 A _18053 r) (@lem1110051 A _18053 r)). Qed.
Lemma lem1110061 {A : Type'} (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (PAIRWISE' r) = (term8 A _18053 r).
Proof. exact (TRANS (@lem1110047 A r PAIRWISE' _18053 h1) (@lem1110060 A _18053 r)). Qed.
Lemma lem1110062 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1110063 {A : Type'} (r : type1402 A) (t : list A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (PAIRWISE' r t) = (term15 A _18053 r t).
Proof. exact (MK_COMB (@lem1110061 A r PAIRWISE' _18053 h1) (@lem1110062 A t)). Qed.
Lemma lem1110065 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109963 A B f y) (@lem1109962 A B f y)). Qed.
Lemma lem1110066 {A : Type'} (f : type1143 A) (y : list A) : (term13 A f y) = (f y).
Proof. exact (@lem1110065 (list A) Prop f y). Qed.
Lemma lem1110067 {A : Type'} (_18053 : type1127 A) (r : type1402 A) (t : list A) : (term35 A _18053 r t) = (term15 A _18053 r t).
Proof. exact (@lem1110066 A (term8 A _18053 r) t). Qed.
Lemma lem1110068 {A : Type'} (_18053 : type1127 A) (_18052 : list A) (r : type1402 A) : (term15 A _18053 r _18052) = (_18053 _18052 r).
Proof. exact (eq_refl (term15 A _18053 r _18052)). Qed.
Lemma lem1110069 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term16 A _18053 r) = (term8 A _18053 r).
Proof. exact (fun_ext (fun _18052 : list A => @lem1110068 A _18053 _18052 r)). Qed.
Lemma lem1110070 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1110071 {A : Type'} (_18053 : type1127 A) (r : type1402 A) (t : list A) : (term35 A _18053 r t) = (term15 A _18053 r t).
Proof. exact (MK_COMB (@lem1110069 A _18053 r) (@lem1110070 A t)). Qed.
Lemma lem1110072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1110073 {A : Type'} (_18053 : type1127 A) (r : type1402 A) (t : list A) : (term36 A _18053 r t) = (term37 A _18053 r t).
Proof. exact (MK_COMB (@lem1110072) (@lem1110071 A _18053 r t)). Qed.
Lemma lem1110074 {A : Type'} (_18053 : type1127 A) (t : list A) (r : type1402 A) : (term15 A _18053 r t) = (_18053 t r).
Proof. exact (eq_refl (term15 A _18053 r t)). Qed.
Lemma lem1110075 {A : Type'} (_18053 : type1127 A) (t : list A) (r : type1402 A) : ((term35 A _18053 r t) = (term15 A _18053 r t)) = ((term15 A _18053 r t) = (_18053 t r)).
Proof. exact (MK_COMB (@lem1110073 A _18053 r t) (@lem1110074 A _18053 t r)). Qed.
Lemma lem1110076 {A : Type'} (_18053 : type1127 A) (t : list A) (r : type1402 A) : (term15 A _18053 r t) = (_18053 t r).
Proof. exact (EQ_MP (@lem1110075 A _18053 t r) (@lem1110067 A _18053 r t)). Qed.
Lemma lem1110077 {A : Type'} (t : list A) (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (PAIRWISE' r t) = (_18053 t r).
Proof. exact (TRANS (@lem1110063 A r t PAIRWISE' _18053 h1) (@lem1110076 A _18053 t r)). Qed.
Lemma lem1110078 {A : Type'} (r : type1402 A) (h : A) (t : list A) : (term38 A r h t) = (term38 A r h t).
Proof. exact (eq_refl (term38 A r h t)). Qed.
Lemma lem1110079 {A : Type'} (h : A) (t : list A) (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term39 A h PAIRWISE' r t) = (term40 A h _18053 t r).
Proof. exact (MK_COMB (@lem1110078 A r h t) (@lem1110077 A t r PAIRWISE' _18053 h1)). Qed.
Lemma lem1110080 {A : Type'} (h : A) (t : list A) (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : ((term27 A PAIRWISE' r h t) = (term39 A h PAIRWISE' r t)) = ((term32 A _18053 h t r) = (term40 A h _18053 t r)).
Proof. exact (MK_COMB (@lem1110043 A h t r PAIRWISE' _18053 h1) (@lem1110079 A h t r PAIRWISE' _18053 h1)). Qed.
Lemma lem1110081 {A : Type'} (h : A) (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term41 A h PAIRWISE' r) = (term42 A h _18053 r).
Proof. exact (fun_ext (fun t : list A => @lem1110080 A h t r PAIRWISE' _18053 h1)). Qed.
Lemma lem1110082 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1110083 {A : Type'} (h : A) (r : type1402 A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term43 A h PAIRWISE' r) = (term44 A h _18053 r).
Proof. exact (MK_COMB (@lem1110082 A) (@lem1110081 A h r PAIRWISE' _18053 h1)). Qed.
Lemma lem1110084 {A : Type'} (h : A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term45 A h PAIRWISE') = (term46 A h _18053).
Proof. exact (fun_ext (fun r : type1402 A => @lem1110083 A h r PAIRWISE' _18053 h1)). Qed.
Lemma lem1110085 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem1110086 {A : Type'} (h : A) (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term47 A h PAIRWISE') = (term48 A h _18053).
Proof. exact (MK_COMB (@lem1110085 A) (@lem1110084 A h PAIRWISE' _18053 h1)). Qed.
Lemma lem1110087 {A : Type'} (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term49 A PAIRWISE') = (term50 A _18053).
Proof. exact (fun_ext (fun h : A => @lem1110086 A h PAIRWISE' _18053 h1)). Qed.
Lemma lem1110088 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1110089 {A : Type'} (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term51 A PAIRWISE') = (term52 A _18053).
Proof. exact (MK_COMB (@lem1110088 A) (@lem1110087 A PAIRWISE' _18053 h1)). Qed.
Lemma lem1110090 {A : Type'} (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term53 A PAIRWISE') = (term54 A _18053).
Proof. exact (MK_COMB (@lem1110007 A PAIRWISE' _18053 h1) (@lem1110089 A PAIRWISE' _18053 h1)). Qed.
Lemma lem1110091 {A : Type'} (_18053 : type1127 A) (h1 : (_18053 (@nil A)) = (term55 A)) : (_18053 (@nil A)) = (term55 A).
Proof. exact (h1). Qed.
Lemma lem1110092 {A : Type'} (r : type1402 A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1110093 {A : Type'} (r : type1402 A) (_18053 : type1127 A) (h1 : (_18053 (@nil A)) = (term55 A)) : (_18053 (@nil A) r) = (term56 A r).
Proof. exact (MK_COMB (@lem1110091 A _18053 h1) (@lem1110092 A r)). Qed.
Lemma lem1110094 {A : Type'} (r : type1402 A) : (term56 A r) = True.
Proof. exact (eq_refl (term56 A r)). Qed.
Lemma lem1110095 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : (term20 A _18053 r) = (term20 A _18053 r).
Proof. exact (eq_refl (term20 A _18053 r)). Qed.
Lemma lem1110096 {A : Type'} (_18053 : type1127 A) (r : type1402 A) : ((_18053 (@nil A) r) = (term56 A r)) = ((_18053 (@nil A) r) = True).
Proof. exact (MK_COMB (@lem1110095 A _18053 r) (@lem1110094 A r)). Qed.
Lemma lem1110097 {A : Type'} (r : type1402 A) (_18053 : type1127 A) (h1 : (_18053 (@nil A)) = (term55 A)) : (_18053 (@nil A) r) = True.
Proof. exact (EQ_MP (@lem1110096 A _18053 r) (@lem1110093 A r _18053 h1)). Qed.
Lemma lem1110098 {A : Type'} (_18053 : type1127 A) (h1 : (_18053 (@nil A)) = (term55 A)) : term24 A _18053.
Proof. exact (fun r : type1402 A => @lem1110097 A r _18053 h1). Qed.
Lemma lem1110099 {A : Type'} (_18053 : type1127 A) (h1 : term57 A _18053) : term57 A _18053.
Proof. exact (h1). Qed.
Lemma lem1110100 {A : Type'} (h : A) (_18053 : type1127 A) (h1 : term57 A _18053) : term58 A _18053 h.
Proof. exact (@lem1110099 A _18053 h1 h). Qed.
Lemma lem1110101 {A : Type'} (h : A) (_18053 : type1127 A) : (term58 A _18053 h) = (term59 A h _18053).
Proof. exact (eq_refl (term58 A _18053 h)). Qed.
Lemma lem1110102 {A : Type'} (h : A) (_18053 : type1127 A) (h1 : term57 A _18053) : term59 A h _18053.
Proof. exact (EQ_MP (@lem1110101 A h _18053) (@lem1110100 A h _18053 h1)). Qed.
Lemma lem1110103 {A : Type'} (h : A) (t : list A) (_18053 : type1127 A) (h1 : term57 A _18053) : term60 A h _18053 t.
Proof. exact (@lem1110102 A h _18053 h1 t). Qed.
Lemma lem1110104 {A : Type'} (h : A) (_18053 : type1127 A) (t : list A) : (term60 A h _18053 t) = ((term61 A _18053 h t) = (term62 A h _18053 t)).
Proof. exact (eq_refl (term60 A h _18053 t)). Qed.
Lemma lem1110105 {A : Type'} (h : A) (t : list A) (_18053 : type1127 A) (h1 : term57 A _18053) : (term61 A _18053 h t) = (term62 A h _18053 t).
Proof. exact (EQ_MP (@lem1110104 A h _18053 t) (@lem1110103 A h t _18053 h1)). Qed.
Lemma lem1110106 {A : Type'} (r : type1402 A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1110107 {A : Type'} (h : A) (t : list A) (r : type1402 A) (_18053 : type1127 A) (h1 : term57 A _18053) : (term32 A _18053 h t r) = (term63 A h _18053 t r).
Proof. exact (MK_COMB (@lem1110105 A h t _18053 h1) (@lem1110106 A r)). Qed.
Lemma lem1110108 {A : Type'} (h : A) (_18053 : type1127 A) (t : list A) (r : type1402 A) : (term63 A h _18053 t r) = (term40 A h _18053 t r).
Proof. exact (eq_refl (term63 A h _18053 t r)). Qed.
Lemma lem1110109 {A : Type'} (_18053 : type1127 A) (h : A) (t : list A) (r : type1402 A) : (term34 A _18053 h t r) = (term34 A _18053 h t r).
Proof. exact (eq_refl (term34 A _18053 h t r)). Qed.
Lemma lem1110110 {A : Type'} (h : A) (_18053 : type1127 A) (t : list A) (r : type1402 A) : ((term32 A _18053 h t r) = (term63 A h _18053 t r)) = ((term32 A _18053 h t r) = (term40 A h _18053 t r)).
Proof. exact (MK_COMB (@lem1110109 A _18053 h t r) (@lem1110108 A h _18053 t r)). Qed.
Lemma lem1110111 {A : Type'} (h : A) (t : list A) (r : type1402 A) (_18053 : type1127 A) (h1 : term57 A _18053) : (term32 A _18053 h t r) = (term40 A h _18053 t r).
Proof. exact (EQ_MP (@lem1110110 A h _18053 t r) (@lem1110107 A h t r _18053 h1)). Qed.
Lemma lem1110112 {A : Type'} (h : A) (r : type1402 A) (_18053 : type1127 A) (h1 : term57 A _18053) : term44 A h _18053 r.
Proof. exact (fun t : list A => @lem1110111 A h t r _18053 h1). Qed.
Lemma lem1110113 {A : Type'} (h : A) (_18053 : type1127 A) (h1 : term57 A _18053) : term48 A h _18053.
Proof. exact (fun r : type1402 A => @lem1110112 A h r _18053 h1). Qed.
Lemma lem1110114 {A : Type'} (_18053 : type1127 A) (h1 : term57 A _18053) : term52 A _18053.
Proof. exact (fun h : A => @lem1110113 A h _18053 h1). Qed.
Lemma lem1110115 {A : Type'} (_18053 : type1127 A) (h1 : term64 A _18053) : term64 A _18053.
Proof. exact (h1). Qed.
Lemma lem1110116 {A : Type'} (_18053 : type1127 A) (h1 : term64 A _18053) : term57 A _18053.
Proof. exact (proj2 (@lem1110115 A _18053 h1)). Qed.
Lemma lem1110117 {A : Type'} (_18053 : type1127 A) (h1 : term64 A _18053) : (_18053 (@nil A)) = (term55 A).
Proof. exact (proj1 (@lem1110115 A _18053 h1)). Qed.
Lemma lem1110118 {A : Type'} (_18053 : type1127 A) (h1 : term64 A _18053) : ((_18053 (@nil A)) = (term55 A)) = (term24 A _18053).
Proof. exact (prop_ext (fun h2 : (_18053 (@nil A)) = (term55 A) => @lem1110098 A _18053 h2) (fun h2 : term24 A _18053 => @lem1110117 A _18053 h1)). Qed.
Lemma lem1110119 {A : Type'} (_18053 : type1127 A) (h1 : term64 A _18053) : term24 A _18053.
Proof. exact (EQ_MP (@lem1110118 A _18053 h1) (@lem1110117 A _18053 h1)). Qed.
Lemma lem1110120 {A : Type'} (_18053 : type1127 A) (h1 : term64 A _18053) : (term57 A _18053) = (term52 A _18053).
Proof. exact (prop_ext (fun h2 : term57 A _18053 => @lem1110114 A _18053 h2) (fun h2 : term52 A _18053 => @lem1110116 A _18053 h1)). Qed.
Lemma lem1110121 {A : Type'} (_18053 : type1127 A) (h1 : term64 A _18053) : term52 A _18053.
Proof. exact (EQ_MP (@lem1110120 A _18053 h1) (@lem1110116 A _18053 h1)). Qed.
Lemma lem1110122 {A : Type'} (_18053 : type1127 A) (h1 : term64 A _18053) : term54 A _18053.
Proof. exact (conj (@lem1110119 A _18053 h1) (@lem1110121 A _18053 h1)). Qed.
Lemma lem1110123 {A Z : Type'} (NIL' : Z) : term65 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1110124 {A Z : Type'} (NIL' : Z) : (term65 A Z NIL') = (term66 A Z NIL').
Proof. exact (eq_refl (term65 A Z NIL')). Qed.
Lemma lem1110125 {A Z : Type'} (NIL' : Z) : term66 A Z NIL'.
Proof. exact (EQ_MP (@lem1110124 A Z NIL') (@lem1110123 A Z NIL')). Qed.
Lemma lem1110126 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term67 A Z NIL' CONS'.
Proof. exact (@lem1110125 A Z NIL' CONS'). Qed.
Lemma lem1110127 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term67 A Z NIL' CONS') = (term68 A Z NIL' CONS').
Proof. exact (eq_refl (term67 A Z NIL' CONS')). Qed.
Lemma lem1110128 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term68 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1110127 A Z NIL' CONS') (@lem1110126 A Z NIL' CONS')). Qed.
Lemma lem1110129 {A : Type'} (NIL' : type421 A) (CONS' : type1383 A) : term69 A NIL' CONS'.
Proof. exact (@lem1110128 A (type421 A) NIL' CONS'). Qed.
Lemma lem1110130 {A : Type'} : term70 A.
Proof. exact (@lem1110129 A (term55 A) (term71 A)). Qed.
Lemma lem1110131 {A : Type'} (a0 : A) : (term72 A a0) = (term73 A a0).
Proof. exact (eq_refl (term72 A a0)). Qed.
Lemma lem1110132 {A : Type'} (a1 : list A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1110133 {A : Type'} (a0 : A) (a1 : list A) : (term74 A a0 a1) = (term75 A a0 a1).
Proof. exact (MK_COMB (@lem1110131 A a0) (@lem1110132 A a1)). Qed.
Lemma lem1110134 {A : Type'} (a0 : A) (a1 : list A) : (term75 A a0 a1) = (term76 A a0 a1).
Proof. exact (eq_refl (term75 A a0 a1)). Qed.
Lemma lem1110135 {A : Type'} (a0 : A) (a1 : list A) : (term74 A a0 a1) = (term76 A a0 a1).
Proof. exact (TRANS (@lem1110133 A a0 a1) (@lem1110134 A a0 a1)). Qed.
Lemma lem1110136 {A : Type'} (fn : type1127 A) (a1 : list A) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1110137 {A : Type'} (a0 : A) (fn : type1127 A) (a1 : list A) : (term77 A a0 fn a1) = (term78 A a0 fn a1).
Proof. exact (MK_COMB (@lem1110135 A a0 a1) (@lem1110136 A fn a1)). Qed.
Lemma lem1110138 {A : Type'} (a0 : A) (fn : type1127 A) (a1 : list A) : (term78 A a0 fn a1) = (term62 A a0 fn a1).
Proof. exact (eq_refl (term78 A a0 fn a1)). Qed.
Lemma lem1110139 {A : Type'} (a0 : A) (fn : type1127 A) (a1 : list A) : (term77 A a0 fn a1) = (term62 A a0 fn a1).
Proof. exact (TRANS (@lem1110137 A a0 fn a1) (@lem1110138 A a0 fn a1)). Qed.
Lemma lem1110140 {A : Type'} (fn : type1127 A) (a0 : A) (a1 : list A) : (term79 A fn a0 a1) = (term79 A fn a0 a1).
Proof. exact (eq_refl (term79 A fn a0 a1)). Qed.
Lemma lem1110141 {A : Type'} (a0 : A) (fn : type1127 A) (a1 : list A) : ((term61 A fn a0 a1) = (term77 A a0 fn a1)) = ((term61 A fn a0 a1) = (term62 A a0 fn a1)).
Proof. exact (MK_COMB (@lem1110140 A fn a0 a1) (@lem1110139 A a0 fn a1)). Qed.
Lemma lem1110142 {A : Type'} (a0 : A) (fn : type1127 A) : (term80 A a0 fn) = (term81 A a0 fn).
Proof. exact (fun_ext (fun a1 : list A => @lem1110141 A a0 fn a1)). Qed.
Lemma lem1110143 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1110144 {A : Type'} (a0 : A) (fn : type1127 A) : (term82 A a0 fn) = (term59 A a0 fn).
Proof. exact (MK_COMB (@lem1110143 A) (@lem1110142 A a0 fn)). Qed.
Lemma lem1110145 {A : Type'} (fn : type1127 A) : (term83 A fn) = (term84 A fn).
Proof. exact (fun_ext (fun a0 : A => @lem1110144 A a0 fn)). Qed.
Lemma lem1110146 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1110147 {A : Type'} (fn : type1127 A) : (term85 A fn) = (term57 A fn).
Proof. exact (MK_COMB (@lem1110146 A) (@lem1110145 A fn)). Qed.
Lemma lem1110148 {A : Type'} (fn : type1127 A) : (term86 A fn) = (term86 A fn).
Proof. exact (eq_refl (term86 A fn)). Qed.
Lemma lem1110149 {A : Type'} (fn : type1127 A) : (term87 A fn) = (term64 A fn).
Proof. exact (MK_COMB (@lem1110148 A fn) (@lem1110147 A fn)). Qed.
Lemma lem1110150 {A : Type'} : (term88 A) = (term89 A).
Proof. exact (fun_ext (fun fn : type1127 A => @lem1110149 A fn)). Qed.
Lemma lem1110151 {A : Type'} : (@ex ((list A) -> (A -> A -> Prop) -> Prop)) = (@ex ((list A) -> (A -> A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((list A) -> (A -> A -> Prop) -> Prop))). Qed.
Lemma lem1110152 {A : Type'} : (term70 A) = (term90 A).
Proof. exact (MK_COMB (@lem1110151 A) (@lem1110150 A)). Qed.
Lemma lem1110153 {A : Type'} : term90 A.
Proof. exact (EQ_MP (@lem1110152 A) (@lem1110130 A)). Qed.
Lemma lem1110154 {A : Type'} (_18053 : type1127 A) (h1 : term64 A _18053) : term64 A _18053.
Proof. exact (h1). Qed.
Lemma lem1110155 {A : Type'} (_18053 : type1127 A) (h1 : term64 A _18053) : term57 A _18053.
Proof. exact (proj2 (@lem1110154 A _18053 h1)). Qed.
Lemma lem1110156 {A : Type'} (_18053 : type1127 A) (h1 : term64 A _18053) : (_18053 (@nil A)) = (term55 A).
Proof. exact (proj1 (@lem1110154 A _18053 h1)). Qed.
Lemma lem1110157 {A : Type'} (_18053 : type1127 A) (h1 : term64 A _18053) : term64 A _18053.
Proof. exact (conj (@lem1110156 A _18053 h1) (@lem1110155 A _18053 h1)). Qed.
Lemma lem1110158 {A : Type'} (_18053 : type1127 A) (h1 : term64 A _18053) : term90 A.
Proof. exact (ex_intro (term89 A) _18053 (@lem1110157 A _18053 h1)). Qed.
Lemma lem1110159 {A : Type'} (h1 : term90 A) : term90 A.
Proof. exact (h1). Qed.
Lemma lem1110160 {A : Type'} (h1 : term90 A) : term90 A.
Proof. exact (ex_elim (@lem1110159 A h1) (fun _18053 : type1127 A => fun h0 : term89 A _18053 => @lem1110158 A _18053 h0)). Qed.
Lemma lem1110161 {A : Type'} : (term90 A) = (term90 A).
Proof. exact (prop_ext (fun h1 : term90 A => @lem1110160 A h1) (fun h1 : term90 A => @lem1110153 A)). Qed.
Lemma lem1110162 {A : Type'} : term90 A.
Proof. exact (EQ_MP (@lem1110161 A) (@lem1110153 A)). Qed.
Lemma lem1110163 {A : Type'} (_18053 : type1127 A) (h1 : term64 A _18053) : term91 A.
Proof. exact (ex_intro (term92 A) _18053 (@lem1110122 A _18053 h1)). Qed.
Lemma lem1110164 {A : Type'} (h1 : term90 A) : term90 A.
Proof. exact (h1). Qed.
Lemma lem1110165 {A : Type'} (h1 : term90 A) : term91 A.
Proof. exact (ex_elim (@lem1110164 A h1) (fun _18053 : type1127 A => fun h0 : term89 A _18053 => @lem1110163 A _18053 h0)). Qed.
Lemma lem1110166 {A : Type'} : (term90 A) = (term91 A).
Proof. exact (prop_ext (fun h1 : term90 A => @lem1110165 A h1) (fun h1 : term91 A => @lem1110162 A)). Qed.
Lemma lem1110167 {A : Type'} : term91 A.
Proof. exact (EQ_MP (@lem1110166 A) (@lem1110162 A)). Qed.
Lemma lem1110168 {A : Type'} (_18053 : type1127 A) (h1 : term54 A _18053) : term54 A _18053.
Proof. exact (h1). Qed.
Lemma lem1110169 {A : Type'} (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : PAIRWISE' = (term4 A _18053)) : (term54 A _18053) = (term53 A PAIRWISE').
Proof. exact (SYM (@lem1110090 A PAIRWISE' _18053 h1)). Qed.
Lemma lem1110170 {A : Type'} (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : term54 A _18053) (h2 : PAIRWISE' = (term4 A _18053)) : term53 A PAIRWISE'.
Proof. exact (EQ_MP (@lem1110169 A PAIRWISE' _18053 h2) (@lem1110168 A _18053 h1)). Qed.
Lemma lem1110171 {A : Type'} (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : term54 A _18053) (h2 : PAIRWISE' = (term4 A _18053)) : term93 A.
Proof. exact (ex_intro (term94 A) PAIRWISE' (@lem1110170 A PAIRWISE' _18053 h1 h2)). Qed.
Lemma lem1110172 {A : Type'} (_18053 : type1127 A) : (term4 A _18053) = (term4 A _18053).
Proof. exact (eq_refl (term4 A _18053)). Qed.
Lemma lem1110173 {A : Type'} (PAIRWISE' : type416 A) (_18053 : type1127 A) (h1 : term54 A _18053) : term95 A PAIRWISE' _18053.
Proof. exact (fun h0 : PAIRWISE' = (term4 A _18053) => @lem1110171 A PAIRWISE' _18053 h1 h0). Qed.
Lemma lem1110174 {A : Type'} (_18053 : type1127 A) (h1 : term54 A _18053) : term96 A _18053.
Proof. exact (@lem1110173 A (term4 A _18053) _18053 h1). Qed.
Lemma lem1110175 {A : Type'} (_18053 : type1127 A) (h1 : term54 A _18053) : term93 A.
Proof. exact (@lem1110174 A _18053 h1 (@lem1110172 A _18053)). Qed.
Lemma lem1110176 {A : Type'} (h1 : term91 A) : term91 A.
Proof. exact (h1). Qed.
Lemma lem1110177 {A : Type'} (h1 : term91 A) : term93 A.
Proof. exact (ex_elim (@lem1110176 A h1) (fun _18053 : type1127 A => fun h0 : term92 A _18053 => @lem1110175 A _18053 h0)). Qed.
Lemma lem1110178 {A : Type'} : (term91 A) = (term93 A).
Proof. exact (prop_ext (fun h1 : term91 A => @lem1110177 A h1) (fun h1 : term93 A => @lem1110167 A)). Qed.
Lemma lem1110179 {A : Type'} : term93 A.
Proof. exact (EQ_MP (@lem1110178 A) (@lem1110167 A)). Qed.
Lemma lem1110180 {A : Type'} : term97 A.
Proof. exact (fun _18057 : type1669 => @lem1110179 A). Qed.
Lemma lem1110181 {A B : Type'} (P : type1413 A B) : term98 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1110182 {A B : Type'} (P : type1413 A B) : (term98 A B P) = ((term99 A B P) = (term100 A B P)).
Proof. exact (eq_refl (term98 A B P)). Qed.
Lemma lem1110185 {A B : Type'} (P : type1413 A B) : (term99 A B P) = (term100 A B P).
Proof. exact (EQ_MP (@lem1110182 A B P) (@lem1110181 A B P)). Qed.
Lemma lem1110186 {A : Type'} (P : type1241 A) : (term101 A P) = (term102 A P).
Proof. exact (@lem1110185 type1669 (type416 A) P). Qed.
Lemma lem1110187 {A : Type'} : (term103 A) = (term104 A).
Proof. exact (@lem1110186 A (term105 A)). Qed.
Lemma lem1110188 {A : Type'} (_18057 : type1669) : (term106 A _18057) = (term94 A).
Proof. exact (eq_refl (term106 A _18057)). Qed.
Lemma lem1110189 {A : Type'} (PAIRWISE' : type416 A) : PAIRWISE' = PAIRWISE'.
Proof. exact (eq_refl PAIRWISE'). Qed.
Lemma lem1110190 {A : Type'} (_18057 : type1669) (PAIRWISE' : type416 A) : (term107 A _18057 PAIRWISE') = (term108 A PAIRWISE').
Proof. exact (MK_COMB (@lem1110188 A _18057) (@lem1110189 A PAIRWISE')). Qed.
Lemma lem1110191 {A : Type'} (PAIRWISE' : type416 A) : (term108 A PAIRWISE') = (term53 A PAIRWISE').
Proof. exact (eq_refl (term108 A PAIRWISE')). Qed.
Lemma lem1110192 {A : Type'} (_18057 : type1669) (PAIRWISE' : type416 A) : (term107 A _18057 PAIRWISE') = (term53 A PAIRWISE').
Proof. exact (TRANS (@lem1110190 A _18057 PAIRWISE') (@lem1110191 A PAIRWISE')). Qed.
Lemma lem1110193 {A : Type'} (_18057 : type1669) : (term109 A _18057) = (term94 A).
Proof. exact (fun_ext (fun PAIRWISE' : type416 A => @lem1110192 A _18057 PAIRWISE')). Qed.
Lemma lem1110194 {A : Type'} : (@ex ((A -> A -> Prop) -> (list A) -> Prop)) = (@ex ((A -> A -> Prop) -> (list A) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> (list A) -> Prop))). Qed.
Lemma lem1110195 {A : Type'} (_18057 : type1669) : (term110 A _18057) = (term93 A).
Proof. exact (MK_COMB (@lem1110194 A) (@lem1110193 A _18057)). Qed.
Lemma lem1110196 {A : Type'} : (term111 A) = (term112 A).
Proof. exact (fun_ext (fun _18057 : type1669 => @lem1110195 A _18057)). Qed.
Lemma lem1110197 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))). Qed.
Lemma lem1110198 {A : Type'} : (term103 A) = (term97 A).
Proof. exact (MK_COMB (@lem1110197) (@lem1110196 A)). Qed.
Lemma lem1110199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1110200 {A : Type'} : (term113 A) = (term114 A).
Proof. exact (MK_COMB (@lem1110199) (@lem1110198 A)). Qed.
Lemma lem1110201 {A : Type'} (_18057 : type1669) : (term106 A _18057) = (term94 A).
Proof. exact (eq_refl (term106 A _18057)). Qed.
Lemma lem1110202 {A : Type'} (PAIRWISE' : type1244 A) (_18057 : type1669) : (PAIRWISE' _18057) = (PAIRWISE' _18057).
Proof. exact (eq_refl (PAIRWISE' _18057)). Qed.
Lemma lem1110203 {A : Type'} (PAIRWISE' : type1244 A) (_18057 : type1669) : (term115 A PAIRWISE' _18057) = (term116 A PAIRWISE' _18057).
Proof. exact (MK_COMB (@lem1110201 A _18057) (@lem1110202 A PAIRWISE' _18057)). Qed.
Lemma lem1110204 {A : Type'} (PAIRWISE' : type1244 A) (_18057 : type1669) : (term116 A PAIRWISE' _18057) = (term117 A PAIRWISE' _18057).
Proof. exact (eq_refl (term116 A PAIRWISE' _18057)). Qed.
Lemma lem1110205 {A : Type'} (PAIRWISE' : type1244 A) (_18057 : type1669) : (term115 A PAIRWISE' _18057) = (term117 A PAIRWISE' _18057).
Proof. exact (TRANS (@lem1110203 A PAIRWISE' _18057) (@lem1110204 A PAIRWISE' _18057)). Qed.
Lemma lem1110206 {A : Type'} (PAIRWISE' : type1244 A) : (term118 A PAIRWISE') = (term119 A PAIRWISE').
Proof. exact (fun_ext (fun _18057 : type1669 => @lem1110205 A PAIRWISE' _18057)). Qed.
Lemma lem1110207 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))). Qed.
Lemma lem1110208 {A : Type'} (PAIRWISE' : type1244 A) : (term120 A PAIRWISE') = (term121 A PAIRWISE').
Proof. exact (MK_COMB (@lem1110207) (@lem1110206 A PAIRWISE')). Qed.
Lemma lem1110209 {A : Type'} : (term122 A) = (term123 A).
Proof. exact (fun_ext (fun PAIRWISE' : type1244 A => @lem1110208 A PAIRWISE')). Qed.
Lemma lem1110210 {A : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (A -> A -> Prop) -> (list A) -> Prop)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (A -> A -> Prop) -> (list A) -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (A -> A -> Prop) -> (list A) -> Prop))). Qed.
Lemma lem1110211 {A : Type'} : (term104 A) = (term124 A).
Proof. exact (MK_COMB (@lem1110210 A) (@lem1110209 A)). Qed.
Lemma lem1110212 {A : Type'} : ((term103 A) = (term104 A)) = ((term97 A) = (term124 A)).
Proof. exact (MK_COMB (@lem1110200 A) (@lem1110211 A)). Qed.
Lemma lem1110213 {A : Type'} : (term97 A) = (term124 A).
Proof. exact (EQ_MP (@lem1110212 A) (@lem1110187 A)). Qed.
Lemma lem1110214 {A : Type'} : term124 A.
Proof. exact (EQ_MP (@lem1110213 A) (@lem1110180 A)). Qed.
Lemma lem1110216 {A : Type'} : (@ex A) = (term125 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1110217 {A : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (A -> A -> Prop) -> (list A) -> Prop)) = (term126 A).
Proof. exact (@lem1110216 (type1244 A)). Qed.
Lemma lem1110218 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (eq_refl (term123 A)). Qed.
Lemma lem1110219 {A : Type'} : (term124 A) = (term127 A).
Proof. exact (MK_COMB (@lem1110217 A) (@lem1110218 A)). Qed.
Lemma lem1110220 {A : Type'} : (term127 A) = (term128 A).
Proof. exact (eq_refl (term127 A)). Qed.
Lemma lem1110221 {A : Type'} : (term124 A) = (term128 A).
Proof. exact (TRANS (@lem1110219 A) (@lem1110220 A)). Qed.
Lemma lem1110222 {A : Type'} : term128 A.
Proof. exact (EQ_MP (@lem1110221 A) (@lem1110214 A)). Qed.
