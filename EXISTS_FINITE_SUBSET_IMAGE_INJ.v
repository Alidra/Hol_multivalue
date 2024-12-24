Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_FINITE_SUBSET_IMAGE_INJ_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXISTS_SUBSET_IMAGE_INJ_spec.
Require Import FINITE_IMAGE_INJ_EQ_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem3655851 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3655852 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3655853 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3655852 t1) (@lem3655851 t1)). Qed.
Lemma lem3655854 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3655853 t1 t2). Qed.
Lemma lem3655855 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3655856 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3655855 t1 t2) (@lem3655854 t1 t2)). Qed.
Lemma lem3655857 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3655856 t1 t2 t3). Qed.
Lemma lem3655858 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3655859 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3655858 t1 t2 t3) (@lem3655857 t1 t2 t3)). Qed.
Lemma lem3655860 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3655859 t1 t2 t3)). Qed.
Lemma lem3655861 {_93490 _93497 : Type'} (P : type686 _93497) : term7 _93490 _93497 P.
Proof. exact (@lem3655226 _93490 _93497 P). Qed.
Lemma lem3655862 {_93490 _93497 : Type'} (P : type686 _93497) : (term7 _93490 _93497 P) = (term8 _93490 _93497 P).
Proof. exact (eq_refl (term7 _93490 _93497 P)). Qed.
Lemma lem3655863 {_93490 _93497 : Type'} (P : type686 _93497) : term8 _93490 _93497 P.
Proof. exact (EQ_MP (@lem3655862 _93490 _93497 P) (@lem3655861 _93490 _93497 P)). Qed.
Lemma lem3655864 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) : term9 _93490 _93497 P f.
Proof. exact (@lem3655863 _93490 _93497 P f). Qed.
Lemma lem3655865 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) : (term9 _93490 _93497 P f) = (term10 _93490 _93497 P f).
Proof. exact (eq_refl (term9 _93490 _93497 P f)). Qed.
Lemma lem3655866 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) : term10 _93490 _93497 P f.
Proof. exact (EQ_MP (@lem3655865 _93490 _93497 P f) (@lem3655864 _93490 _93497 P f)). Qed.
Lemma lem3655867 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (s : _93490 -> Prop) : term11 _93490 _93497 P f s.
Proof. exact (@lem3655866 _93490 _93497 P f s). Qed.
Lemma lem3655868 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term11 _93490 _93497 P f s) = ((term12 _93490 _93497 f s P) = (term13 _93490 _93497 s P f)).
Proof. exact (eq_refl (term11 _93490 _93497 P f s)). Qed.
Lemma lem3655882 (p : Prop) : term14 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem3655883 (p : Prop) : (term14 p) = (term15 p).
Proof. exact (eq_refl (term14 p)). Qed.
Lemma lem3655884 (p : Prop) : term15 p.
Proof. exact (EQ_MP (@lem3655883 p) (@lem3655882 p)). Qed.
Lemma lem3655885 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem3655886 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem3655899 (q : Prop) (r : Prop) : (term16 q r) = (term16 q r).
Proof. exact (eq_refl (term16 q r)). Qed.
Lemma lem3655900 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : (term17 q r p) = (term18 q r).
Proof. exact (MK_COMB (@lem3655899 q r) (@lem3655885 p h1)). Qed.
Lemma lem3655901 (q : Prop) (r : Prop) : (term18 q r) = ((term19 q r) = (term20 q r)).
Proof. exact (eq_refl (term18 q r)). Qed.
Lemma lem3655902 (q : Prop) (r : Prop) (p : Prop) : (term21 q r p) = (term21 q r p).
Proof. exact (eq_refl (term21 q r p)). Qed.
Lemma lem3655903 (p : Prop) (q : Prop) (r : Prop) : ((term17 q r p) = (term18 q r)) = ((term17 q r p) = ((term19 q r) = (term20 q r))).
Proof. exact (MK_COMB (@lem3655902 q r p) (@lem3655901 q r)). Qed.
Lemma lem3655904 (q : Prop) (p : Prop) (r : Prop) : (term17 q r p) = ((term22 p q r) = (term22 q p r)).
Proof. exact (eq_refl (term17 q r p)). Qed.
Lemma lem3655905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3655906 (q : Prop) (p : Prop) (r : Prop) : (term21 q r p) = (term23 q p r).
Proof. exact (MK_COMB (@lem3655905) (@lem3655904 q p r)). Qed.
Lemma lem3655907 (q : Prop) (r : Prop) : ((term19 q r) = (term20 q r)) = ((term19 q r) = (term20 q r)).
Proof. exact (eq_refl ((term19 q r) = (term20 q r))). Qed.
Lemma lem3655908 (p : Prop) (q : Prop) (r : Prop) : ((term17 q r p) = ((term19 q r) = (term20 q r))) = (((term22 p q r) = (term22 q p r)) = ((term19 q r) = (term20 q r))).
Proof. exact (MK_COMB (@lem3655906 q p r) (@lem3655907 q r)). Qed.
Lemma lem3655909 (p : Prop) (q : Prop) (r : Prop) : ((term17 q r p) = (term18 q r)) = (((term22 p q r) = (term22 q p r)) = ((term19 q r) = (term20 q r))).
Proof. exact (TRANS (@lem3655903 p q r) (@lem3655908 p q r)). Qed.
Lemma lem3655910 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : ((term22 p q r) = (term22 q p r)) = ((term19 q r) = (term20 q r)).
Proof. exact (EQ_MP (@lem3655909 p q r) (@lem3655900 q r p h1)). Qed.
Lemma lem3655911 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : ((term19 q r) = (term20 q r)) = ((term22 p q r) = (term22 q p r)).
Proof. exact (SYM (@lem3655910 q r p h1)). Qed.
Lemma lem3655912 (q : Prop) (r : Prop) : (term16 q r) = (term16 q r).
Proof. exact (eq_refl (term16 q r)). Qed.
Lemma lem3655913 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : (term17 q r p) = (term24 q r).
Proof. exact (MK_COMB (@lem3655912 q r) (@lem3655886 p h1)). Qed.
Lemma lem3655914 (q : Prop) (r : Prop) : (term24 q r) = ((term25 q r) = (term26 q r)).
Proof. exact (eq_refl (term24 q r)). Qed.
Lemma lem3655915 (q : Prop) (r : Prop) (p : Prop) : (term21 q r p) = (term21 q r p).
Proof. exact (eq_refl (term21 q r p)). Qed.
Lemma lem3655916 (p : Prop) (q : Prop) (r : Prop) : ((term17 q r p) = (term24 q r)) = ((term17 q r p) = ((term25 q r) = (term26 q r))).
Proof. exact (MK_COMB (@lem3655915 q r p) (@lem3655914 q r)). Qed.
Lemma lem3655917 (q : Prop) (p : Prop) (r : Prop) : (term17 q r p) = ((term22 p q r) = (term22 q p r)).
Proof. exact (eq_refl (term17 q r p)). Qed.
Lemma lem3655918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3655919 (q : Prop) (p : Prop) (r : Prop) : (term21 q r p) = (term23 q p r).
Proof. exact (MK_COMB (@lem3655918) (@lem3655917 q p r)). Qed.
Lemma lem3655920 (q : Prop) (r : Prop) : ((term25 q r) = (term26 q r)) = ((term25 q r) = (term26 q r)).
Proof. exact (eq_refl ((term25 q r) = (term26 q r))). Qed.
Lemma lem3655921 (p : Prop) (q : Prop) (r : Prop) : ((term17 q r p) = ((term25 q r) = (term26 q r))) = (((term22 p q r) = (term22 q p r)) = ((term25 q r) = (term26 q r))).
Proof. exact (MK_COMB (@lem3655919 q p r) (@lem3655920 q r)). Qed.
Lemma lem3655922 (p : Prop) (q : Prop) (r : Prop) : ((term17 q r p) = (term24 q r)) = (((term22 p q r) = (term22 q p r)) = ((term25 q r) = (term26 q r))).
Proof. exact (TRANS (@lem3655916 p q r) (@lem3655921 p q r)). Qed.
Lemma lem3655923 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : ((term22 p q r) = (term22 q p r)) = ((term25 q r) = (term26 q r)).
Proof. exact (EQ_MP (@lem3655922 p q r) (@lem3655913 q r p h1)). Qed.
Lemma lem3655924 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : ((term25 q r) = (term26 q r)) = ((term22 p q r) = (term22 q p r)).
Proof. exact (SYM (@lem3655923 q r p h1)). Qed.
Lemma lem3655928 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3655929 (q : Prop) (r : Prop) : (term19 q r) = (q /\ r).
Proof. exact (@lem3655928 (q /\ r)). Qed.
Lemma lem3655932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3655933 (q : Prop) (r : Prop) : (term27 q r) = (term28 q r).
Proof. exact (MK_COMB (@lem3655932) (@lem3655929 q r)). Qed.
Lemma lem3655937 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3655938 (r : Prop) : (True /\ r) = r.
Proof. exact (@lem3655937 r). Qed.
Lemma lem3655939 (q : Prop) : (and q) = (and q).
Proof. exact (eq_refl (and q)). Qed.
Lemma lem3655940 (q : Prop) (r : Prop) : (term20 q r) = (q /\ r).
Proof. exact (MK_COMB (@lem3655939 q) (@lem3655938 r)). Qed.
Lemma lem3655943 (q : Prop) (r : Prop) : ((term19 q r) = (term20 q r)) = ((q /\ r) = (q /\ r)).
Proof. exact (MK_COMB (@lem3655933 q r) (@lem3655940 q r)). Qed.
Lemma lem3655945 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3655946 (x : Prop) : (x = x) = True.
Proof. exact (@lem3655945 Prop x). Qed.
Lemma lem3655947 (q : Prop) (r : Prop) : ((q /\ r) = (q /\ r)) = True.
Proof. exact (@lem3655946 (q /\ r)). Qed.
Lemma lem3655948 (q : Prop) (r : Prop) : ((term19 q r) = (term20 q r)) = True.
Proof. exact (TRANS (@lem3655943 q r) (@lem3655947 q r)). Qed.
Lemma lem3655949 (q : Prop) (r : Prop) : True = ((term19 q r) = (term20 q r)).
Proof. exact (SYM (@lem3655948 q r)). Qed.
Lemma lem3655950 (q : Prop) (r : Prop) : (term19 q r) = (term20 q r).
Proof. exact (EQ_MP (@lem3655949 q r) (@lem0)). Qed.
Lemma lem3655954 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3655955 (q : Prop) (r : Prop) : (term25 q r) = False.
Proof. exact (@lem3655954 (q /\ r)). Qed.
Lemma lem3655956 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3655957 (q : Prop) (r : Prop) : (term29 q r) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3655956) (@lem3655955 q r)). Qed.
Lemma lem3655961 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3655962 (r : Prop) : (False /\ r) = False.
Proof. exact (@lem3655961 r). Qed.
Lemma lem3655963 (q : Prop) : (and q) = (and q).
Proof. exact (eq_refl (and q)). Qed.
Lemma lem3655964 (r : Prop) (q : Prop) : (term26 q r) = (q /\ False).
Proof. exact (MK_COMB (@lem3655963 q) (@lem3655962 r)). Qed.
Lemma lem3655966 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem3655967 (q : Prop) : (q /\ False) = False.
Proof. exact (@lem3655966 q). Qed.
Lemma lem3655968 (q : Prop) (r : Prop) : (term26 q r) = False.
Proof. exact (TRANS (@lem3655964 r q) (@lem3655967 q)). Qed.
Lemma lem3655969 (q : Prop) (r : Prop) : ((term25 q r) = (term26 q r)) = (False = False).
Proof. exact (MK_COMB (@lem3655957 q r) (@lem3655968 q r)). Qed.
Lemma lem3655971 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3655972 : (False = False) = (~ False).
Proof. exact (@lem3655971 False). Qed.
Lemma lem3655974 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3655975 : (False = False) = True.
Proof. exact (TRANS (@lem3655972) (@lem3655974)). Qed.
Lemma lem3655976 (q : Prop) (r : Prop) : ((term25 q r) = (term26 q r)) = True.
Proof. exact (TRANS (@lem3655969 q r) (@lem3655975)). Qed.
Lemma lem3655977 (q : Prop) (r : Prop) : True = ((term25 q r) = (term26 q r)).
Proof. exact (SYM (@lem3655976 q r)). Qed.
Lemma lem3655978 (q : Prop) (r : Prop) : (term25 q r) = (term26 q r).
Proof. exact (EQ_MP (@lem3655977 q r) (@lem0)). Qed.
Lemma lem3655979 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : (term22 p q r) = (term22 q p r).
Proof. exact (EQ_MP (@lem3655924 q r p h1) (@lem3655978 q r)). Qed.
Lemma lem3655980 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : (term22 p q r) = (term22 q p r).
Proof. exact (EQ_MP (@lem3655911 q r p h1) (@lem3655950 q r)). Qed.
Lemma lem3656003 (q : Prop) (p : Prop) (r : Prop) : (term22 p q r) = (term22 q p r).
Proof. exact (or_elim (@lem3655884 p) (fun h0 : p = True => @lem3655980 q r p h0) (fun h0 : p = False => @lem3655979 q r p h0)). Qed.
Lemma lem3656004 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) (P : type686 _93677) (t : _93677 -> Prop) : (term30 _93670 _93677 f s P t) = (term31 _93670 _93677 f s P t).
Proof. exact (@lem3656003 (term32 _93670 _93677 t f s) (@FINITE _93677 t) (P t)). Qed.
Lemma lem3656005 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) (P : type686 _93677) : (term33 _93670 _93677 f s P) = (term34 _93670 _93677 f s P).
Proof. exact (fun_ext (fun t : _93677 -> Prop => @lem3656004 _93670 _93677 f s P t)). Qed.
Lemma lem3656006 {_93677 : Type'} : (@ex (_93677 -> Prop)) = (@ex (_93677 -> Prop)).
Proof. exact (eq_refl (@ex (_93677 -> Prop))). Qed.
Lemma lem3656007 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) (P : type686 _93677) : (term35 _93670 _93677 f s P) = (term36 _93670 _93677 f s P).
Proof. exact (MK_COMB (@lem3656006 _93677) (@lem3656005 _93670 _93677 f s P)). Qed.
Lemma lem3656008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3656009 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) (P : type686 _93677) : (term37 _93670 _93677 f s P) = (term38 _93670 _93677 f s P).
Proof. exact (MK_COMB (@lem3656008) (@lem3656007 _93670 _93677 f s P)). Qed.
Lemma lem3656015 (q : Prop) (p : Prop) (r : Prop) : (term22 p q r) = (term22 q p r).
Proof. exact (or_elim (@lem3655884 p) (fun h0 : p = True => @lem3655980 q r p h0) (fun h0 : p = False => @lem3655979 q r p h0)). Qed.
Lemma lem3656016 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term39 _93670 _93677 s P f t) = (term40 _93670 _93677 s P f t).
Proof. exact (@lem3656015 (@SUBSET _93670 t s) (@FINITE _93670 t) (term41 _93670 _93677 P f t)). Qed.
Lemma lem3656017 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term42 _93670 _93677 s P f) = (term43 _93670 _93677 s P f).
Proof. exact (fun_ext (fun t : _93670 -> Prop => @lem3656016 _93670 _93677 s P f t)). Qed.
Lemma lem3656018 {_93670 : Type'} : (@ex (_93670 -> Prop)) = (@ex (_93670 -> Prop)).
Proof. exact (eq_refl (@ex (_93670 -> Prop))). Qed.
Lemma lem3656019 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term44 _93670 _93677 s P f) = (term45 _93670 _93677 s P f).
Proof. exact (MK_COMB (@lem3656018 _93670) (@lem3656017 _93670 _93677 s P f)). Qed.
Lemma lem3656020 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : ((term35 _93670 _93677 f s P) = (term44 _93670 _93677 s P f)) = ((term36 _93670 _93677 f s P) = (term45 _93670 _93677 s P f)).
Proof. exact (MK_COMB (@lem3656009 _93670 _93677 f s P) (@lem3656019 _93670 _93677 s P f)). Qed.
Lemma lem3656021 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) : (term46 _93670 _93677 P f) = (term47 _93670 _93677 P f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3656020 _93670 _93677 s P f)). Qed.
Lemma lem3656022 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3656023 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) : (term48 _93670 _93677 P f) = (term49 _93670 _93677 P f).
Proof. exact (MK_COMB (@lem3656022 _93670) (@lem3656021 _93670 _93677 P f)). Qed.
Lemma lem3656024 {_93670 _93677 : Type'} (P : type686 _93677) : (term50 _93670 _93677 P) = (term51 _93670 _93677 P).
Proof. exact (fun_ext (fun f : _93670 -> _93677 => @lem3656023 _93670 _93677 P f)). Qed.
Lemma lem3656025 {_93670 _93677 : Type'} : (@all (_93670 -> _93677)) = (@all (_93670 -> _93677)).
Proof. exact (eq_refl (@all (_93670 -> _93677))). Qed.
Lemma lem3656026 {_93670 _93677 : Type'} (P : type686 _93677) : (term52 _93670 _93677 P) = (term53 _93670 _93677 P).
Proof. exact (MK_COMB (@lem3656025 _93670 _93677) (@lem3656024 _93670 _93677 P)). Qed.
Lemma lem3656027 {_93670 _93677 : Type'} : (term54 _93670 _93677) = (term55 _93670 _93677).
Proof. exact (fun_ext (fun P : type686 _93677 => @lem3656026 _93670 _93677 P)). Qed.
Lemma lem3656028 {_93677 : Type'} : (@all ((_93677 -> Prop) -> Prop)) = (@all ((_93677 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_93677 -> Prop) -> Prop))). Qed.
Lemma lem3656029 {_93670 _93677 : Type'} : (term56 _93670 _93677) = (term57 _93670 _93677).
Proof. exact (MK_COMB (@lem3656028 _93677) (@lem3656027 _93670 _93677)). Qed.
Lemma lem3656030 {_93670 _93677 : Type'} : (term57 _93670 _93677) = (term56 _93670 _93677).
Proof. exact (SYM (@lem3656029 _93670 _93677)). Qed.
Lemma lem3656034 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term12 _93490 _93497 f s P) = (term13 _93490 _93497 s P f).
Proof. exact (EQ_MP (@lem3655868 _93490 _93497 s P f) (@lem3655867 _93490 _93497 P f s)). Qed.
Lemma lem3656035 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term12 _93670 _93677 f s P) = (term13 _93670 _93677 s P f).
Proof. exact (@lem3656034 _93670 _93677 s P f). Qed.
Lemma lem3656036 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term58 _93670 _93677 f s P) = (term59 _93670 _93677 s P f).
Proof. exact (@lem3656035 _93670 _93677 s (term60 _93677 P) f). Qed.
Lemma lem3656037 {_93677 : Type'} (P : type686 _93677) (t : _93677 -> Prop) : (term61 _93677 P t) = (term62 _93677 P t).
Proof. exact (eq_refl (term61 _93677 P t)). Qed.
Lemma lem3656038 {_93670 _93677 : Type'} (t : _93677 -> Prop) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term63 _93670 _93677 t f s) = (term63 _93670 _93677 t f s).
Proof. exact (eq_refl (term63 _93670 _93677 t f s)). Qed.
Lemma lem3656039 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) (P : type686 _93677) (t : _93677 -> Prop) : (term64 _93670 _93677 f s P t) = (term31 _93670 _93677 f s P t).
Proof. exact (MK_COMB (@lem3656038 _93670 _93677 t f s) (@lem3656037 _93677 P t)). Qed.
Lemma lem3656040 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) (P : type686 _93677) : (term65 _93670 _93677 f s P) = (term34 _93670 _93677 f s P).
Proof. exact (fun_ext (fun t : _93677 -> Prop => @lem3656039 _93670 _93677 f s P t)). Qed.
Lemma lem3656041 {_93677 : Type'} : (@ex (_93677 -> Prop)) = (@ex (_93677 -> Prop)).
Proof. exact (eq_refl (@ex (_93677 -> Prop))). Qed.
Lemma lem3656042 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) (P : type686 _93677) : (term58 _93670 _93677 f s P) = (term36 _93670 _93677 f s P).
Proof. exact (MK_COMB (@lem3656041 _93677) (@lem3656040 _93670 _93677 f s P)). Qed.
Lemma lem3656043 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3656044 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) (P : type686 _93677) : (term66 _93670 _93677 f s P) = (term38 _93670 _93677 f s P).
Proof. exact (MK_COMB (@lem3656043) (@lem3656042 _93670 _93677 f s P)). Qed.
Lemma lem3656045 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term67 _93670 _93677 P f t) = (term68 _93670 _93677 P f t).
Proof. exact (eq_refl (term67 _93670 _93677 P f t)). Qed.
Lemma lem3656046 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term69 _93670 _93677 t f) = (term69 _93670 _93677 t f).
Proof. exact (eq_refl (term69 _93670 _93677 t f)). Qed.
Lemma lem3656047 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term70 _93670 _93677 P f t) = (term71 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3656046 _93670 _93677 t f) (@lem3656045 _93670 _93677 P f t)). Qed.
Lemma lem3656048 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term72 _93670 t s) = (term72 _93670 t s).
Proof. exact (eq_refl (term72 _93670 t s)). Qed.
Lemma lem3656049 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term73 _93670 _93677 s P f t) = (term74 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3656048 _93670 t s) (@lem3656047 _93670 _93677 P f t)). Qed.
Lemma lem3656050 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term75 _93670 _93677 s P f) = (term76 _93670 _93677 s P f).
Proof. exact (fun_ext (fun t : _93670 -> Prop => @lem3656049 _93670 _93677 s P f t)). Qed.
Lemma lem3656051 {_93670 : Type'} : (@ex (_93670 -> Prop)) = (@ex (_93670 -> Prop)).
Proof. exact (eq_refl (@ex (_93670 -> Prop))). Qed.
Lemma lem3656052 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term59 _93670 _93677 s P f) = (term77 _93670 _93677 s P f).
Proof. exact (MK_COMB (@lem3656051 _93670) (@lem3656050 _93670 _93677 s P f)). Qed.
Lemma lem3656053 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : ((term58 _93670 _93677 f s P) = (term59 _93670 _93677 s P f)) = ((term36 _93670 _93677 f s P) = (term77 _93670 _93677 s P f)).
Proof. exact (MK_COMB (@lem3656044 _93670 _93677 f s P) (@lem3656052 _93670 _93677 s P f)). Qed.
Lemma lem3656054 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term36 _93670 _93677 f s P) = (term77 _93670 _93677 s P f).
Proof. exact (EQ_MP (@lem3656053 _93670 _93677 s P f) (@lem3656036 _93670 _93677 s P f)). Qed.
Lemma lem3656083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3656084 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term38 _93670 _93677 f s P) = (term78 _93670 _93677 s P f).
Proof. exact (MK_COMB (@lem3656083) (@lem3656054 _93670 _93677 s P f)). Qed.
Lemma lem3656113 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term45 _93670 _93677 s P f) = (term45 _93670 _93677 s P f).
Proof. exact (eq_refl (term45 _93670 _93677 s P f)). Qed.
Lemma lem3656114 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : ((term36 _93670 _93677 f s P) = (term45 _93670 _93677 s P f)) = ((term77 _93670 _93677 s P f) = (term45 _93670 _93677 s P f)).
Proof. exact (MK_COMB (@lem3656084 _93670 _93677 s P f) (@lem3656113 _93670 _93677 s P f)). Qed.
Lemma lem3656117 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : ((term77 _93670 _93677 s P f) = (term45 _93670 _93677 s P f)) = ((term36 _93670 _93677 f s P) = (term45 _93670 _93677 s P f)).
Proof. exact (SYM (@lem3656114 _93670 _93677 s P f)). Qed.
Lemma lem3656118 {_93670 : Type'} : (@ex (_93670 -> Prop)) = (@ex (_93670 -> Prop)).
Proof. exact (eq_refl (@ex (_93670 -> Prop))). Qed.
Lemma lem3656120 (p : Prop) : p = (term79 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3656121 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term74 _93670 _93677 s P f t) = (term40 _93670 _93677 s P f t)) = (term80 _93670 _93677 s P f t).
Proof. exact (@lem3656120 ((term74 _93670 _93677 s P f t) = (term40 _93670 _93677 s P f t))). Qed.
Lemma lem3656122 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term80 _93670 _93677 s P f t) = ((term74 _93670 _93677 s P f t) = (term40 _93670 _93677 s P f t)).
Proof. exact (SYM (@lem3656121 _93670 _93677 s P f t)). Qed.
Lemma lem3656123 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term81 _93670 _93677 s P f t) : term81 _93670 _93677 s P f t.
Proof. exact (h1). Qed.
Lemma lem3656124 {_93670 B : Type'} : term82 _93670 B.
Proof. exact (@lem3618990 _93670 B). Qed.
Lemma lem3656125 {_93677 A : Type'} : term83 _93677 A.
Proof. exact (@lem3618990 A _93677). Qed.
Lemma lem3656126 {_93670 A : Type'} : term83 _93670 A.
Proof. exact (@lem3618990 A _93670). Qed.
Lemma lem3656127 {_93677 B : Type'} : term82 _93677 B.
Proof. exact (@lem3618990 _93677 B). Qed.
Lemma lem3656131 {_93670 _93677 : Type'} : term82 _93670 _93677.
Proof. exact (@lem3618990 _93670 _93677). Qed.
Lemma lem3656136 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term84 _93670 _93677 A B s P f t) : term84 _93670 _93677 A B s P f t.
Proof. exact (h1). Qed.
Lemma lem3656137 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : term85 _93670 _93677 A B s P f t.
Proof. exact (fun h0 : term84 _93670 _93677 A B s P f t => @lem3656136 _93670 _93677 A B s P f t h0). Qed.
Lemma lem3656138 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term85 _93670 _93677 A B s P f t) : term85 _93670 _93677 A B s P f t.
Proof. exact (h1). Qed.
Lemma lem3656139 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term84 _93670 _93677 A B s P f t) : term84 _93670 _93677 A B s P f t.
Proof. exact (h1). Qed.
Lemma lem3656140 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term84 _93670 _93677 A B s P f t) (h2 : term85 _93670 _93677 A B s P f t) : term84 _93670 _93677 A B s P f t.
Proof. exact (@lem3656138 _93670 _93677 A B s P f t h2 (@lem3656139 _93670 _93677 A B s P f t h1)). Qed.
Lemma lem3656141 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term84 _93670 _93677 A B s P f t) : term86 _93670 _93677 A B s P f t.
Proof. exact (fun h0 : term85 _93670 _93677 A B s P f t => @lem3656140 _93670 _93677 A B s P f t h1 h0). Qed.
Lemma lem3656142 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term85 _93670 _93677 A B s P f t) : term85 _93670 _93677 A B s P f t.
Proof. exact (h1). Qed.
Lemma lem3656143 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term84 _93670 _93677 A B s P f t) (h2 : term85 _93670 _93677 A B s P f t) : term84 _93670 _93677 A B s P f t.
Proof. exact (@lem3656141 _93670 _93677 A B s P f t h1 (@lem3656142 _93670 _93677 A B s P f t h2)). Qed.
Lemma lem3656144 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term85 _93670 _93677 A B s P f t) : term85 _93670 _93677 A B s P f t.
Proof. exact (fun h0 : term84 _93670 _93677 A B s P f t => @lem3656143 _93670 _93677 A B s P f t h0 h1). Qed.
Lemma lem3656145 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : term87 _93670 _93677 A B s P f t.
Proof. exact (fun h0 : term85 _93670 _93677 A B s P f t => @lem3656144 _93670 _93677 A B s P f t h0). Qed.
Lemma lem3656148 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : term85 _93670 _93677 A B s P f t.
Proof. exact (@lem3656145 _93670 _93677 A B s P f t (@lem3656137 _93670 _93677 A B s P f t)). Qed.
Lemma lem3656149 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : term85 _93670 _93677 A B s P f t.
Proof. exact (@lem3656148 _93670 _93677 A B s P f t). Qed.
Lemma lem3656309 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3656310 {_93677 A : Type'} : (term88 _93677 A) = (term89 _93677 A).
Proof. exact (@lem3656309 (term83 _93677 A)). Qed.
Lemma lem3656335 {_93670 A : Type'} : (term90 _93670 A) = (term90 _93670 A).
Proof. exact (eq_refl (term90 _93670 A)). Qed.
Lemma lem3656336 {_93670 _93677 A : Type'} : (term91 _93670 _93677 A) = (term92 _93670 _93677 A).
Proof. exact (MK_COMB (@lem3656335 _93670 A) (@lem3656310 _93677 A)). Qed.
Lemma lem3656339 {_93677 B : Type'} : (term93 _93677 B) = (term93 _93677 B).
Proof. exact (eq_refl (term93 _93677 B)). Qed.
Lemma lem3656340 {_93670 _93677 A B : Type'} : (term94 _93670 _93677 A B) = (term95 _93670 _93677 A B).
Proof. exact (MK_COMB (@lem3656339 _93677 B) (@lem3656336 _93670 _93677 A)). Qed.
Lemma lem3656343 {_93670 B : Type'} : (term93 _93670 B) = (term93 _93670 B).
Proof. exact (eq_refl (term93 _93670 B)). Qed.
Lemma lem3656344 {_93670 _93677 A B : Type'} : (term96 _93670 _93677 A B) = (term97 _93670 _93677 A B).
Proof. exact (MK_COMB (@lem3656343 _93670 B) (@lem3656340 _93670 _93677 A B)). Qed.
Lemma lem3656347 {_93670 _93677 : Type'} : (term93 _93670 _93677) = (term93 _93670 _93677).
Proof. exact (eq_refl (term93 _93670 _93677)). Qed.
Lemma lem3656348 {_93670 _93677 A B : Type'} : (term98 _93670 _93677 A B) = (term99 _93670 _93677 A B).
Proof. exact (MK_COMB (@lem3656347 _93670 _93677) (@lem3656344 _93670 _93677 A B)). Qed.
Lemma lem3656351 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term100 _93670 _93677 s P f t) = (term100 _93670 _93677 s P f t).
Proof. exact (eq_refl (term100 _93670 _93677 s P f t)). Qed.
Lemma lem3656352 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term84 _93670 _93677 A B s P f t) = (term101 _93670 _93677 A B s P f t).
Proof. exact (MK_COMB (@lem3656351 _93670 _93677 s P f t) (@lem3656348 _93670 _93677 A B)). Qed.
Lemma lem3656355 {_93670 _93677 A B : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term102 _93670 _93677 A B P f t) = (term103 _93670 _93677 A B P f t).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3656352 _93670 _93677 A B s P f t)). Qed.
Lemma lem3656356 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3656357 {_93670 _93677 A B : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term104 _93670 _93677 A B P f t) = (term105 _93670 _93677 A B P f t).
Proof. exact (MK_COMB (@lem3656356 _93670) (@lem3656355 _93670 _93677 A B P f t)). Qed.
Lemma lem3656362 {_93670 _93677 A B : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term106 _93670 _93677 A B f t) = (term107 _93670 _93677 A B f t).
Proof. exact (fun_ext (fun P : type686 _93677 => @lem3656357 _93670 _93677 A B P f t)). Qed.
Lemma lem3656363 {_93677 : Type'} : (@all ((_93677 -> Prop) -> Prop)) = (@all ((_93677 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_93677 -> Prop) -> Prop))). Qed.
Lemma lem3656364 {_93670 _93677 A B : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term108 _93670 _93677 A B f t) = (term109 _93670 _93677 A B f t).
Proof. exact (MK_COMB (@lem3656363 _93677) (@lem3656362 _93670 _93677 A B f t)). Qed.
Lemma lem3656369 {_93670 _93677 A B : Type'} (t : _93670 -> Prop) : (term110 _93670 _93677 A B t) = (term111 _93670 _93677 A B t).
Proof. exact (fun_ext (fun f : _93670 -> _93677 => @lem3656364 _93670 _93677 A B f t)). Qed.
Lemma lem3656370 {_93670 _93677 : Type'} : (@all (_93670 -> _93677)) = (@all (_93670 -> _93677)).
Proof. exact (eq_refl (@all (_93670 -> _93677))). Qed.
Lemma lem3656371 {_93670 _93677 A B : Type'} (t : _93670 -> Prop) : (term112 _93670 _93677 A B t) = (term113 _93670 _93677 A B t).
Proof. exact (MK_COMB (@lem3656370 _93670 _93677) (@lem3656369 _93670 _93677 A B t)). Qed.
Lemma lem3656376 {_93670 _93677 A B : Type'} : (term114 _93670 _93677 A B) = (term115 _93670 _93677 A B).
Proof. exact (fun_ext (fun t : _93670 -> Prop => @lem3656371 _93670 _93677 A B t)). Qed.
Lemma lem3656377 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3656386 {_93670 _93677 A B : Type'} : (term116 _93670 _93677 A B) = (term117 _93670 _93677 A B).
Proof. exact (MK_COMB (@lem3656377 _93670) (@lem3656376 _93670 _93677 A B)). Qed.
Lemma lem3656391 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : ((term118 _93677 A f s) = (@FINITE A s)) = ((term118 _93677 A f s) = (@FINITE A s)).
Proof. exact (eq_refl ((term118 _93677 A f s) = (@FINITE A s))). Qed.
Lemma lem3656404 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) (y : A) : (term119 _93677 A s f x y) = (term119 _93677 A s f x y).
Proof. exact (eq_refl (term119 _93677 A s f x y)). Qed.
Lemma lem3656405 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term120 _93677 A s f x) = (term120 _93677 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3656404 _93677 A s f x y)). Qed.
Lemma lem3656406 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3656407 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term121 _93677 A s f x) = (term121 _93677 A s f x).
Proof. exact (MK_COMB (@lem3656406 A) (@lem3656405 _93677 A s f x)). Qed.
Lemma lem3656408 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) : (term122 _93677 A s f) = (term122 _93677 A s f).
Proof. exact (fun_ext (fun x : A => @lem3656407 _93677 A s f x)). Qed.
Lemma lem3656409 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3656410 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) : (term123 _93677 A s f) = (term123 _93677 A s f).
Proof. exact (MK_COMB (@lem3656409 A) (@lem3656408 _93677 A s f)). Qed.
Lemma lem3656411 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3656412 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) : (term124 _93677 A s f) = (term124 _93677 A s f).
Proof. exact (MK_COMB (@lem3656411) (@lem3656410 _93677 A s f)). Qed.
Lemma lem3656413 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term125 _93677 A f s) = (term125 _93677 A f s).
Proof. exact (MK_COMB (@lem3656412 _93677 A s f) (@lem3656391 _93677 A f s)). Qed.
Lemma lem3656414 {_93677 A : Type'} (f : A -> _93677) : (term126 _93677 A f) = (term126 _93677 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3656413 _93677 A f s)). Qed.
Lemma lem3656415 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3656416 {_93677 A : Type'} (f : A -> _93677) : (term127 _93677 A f) = (term127 _93677 A f).
Proof. exact (MK_COMB (@lem3656415 A) (@lem3656414 _93677 A f)). Qed.
Lemma lem3656417 {_93677 A : Type'} : (term128 _93677 A) = (term128 _93677 A).
Proof. exact (fun_ext (fun f : A -> _93677 => @lem3656416 _93677 A f)). Qed.
Lemma lem3656418 {_93677 A : Type'} : (@all (A -> _93677)) = (@all (A -> _93677)).
Proof. exact (eq_refl (@all (A -> _93677))). Qed.
Lemma lem3656419 {_93677 A : Type'} : (term83 _93677 A) = (term83 _93677 A).
Proof. exact (MK_COMB (@lem3656418 _93677 A) (@lem3656417 _93677 A)). Qed.
Lemma lem3656420 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3656421 {_93677 A : Type'} : (term89 _93677 A) = (term89 _93677 A).
Proof. exact (MK_COMB (@lem3656420) (@lem3656419 _93677 A)). Qed.
Lemma lem3656426 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : ((term118 _93670 A f s) = (@FINITE A s)) = ((term118 _93670 A f s) = (@FINITE A s)).
Proof. exact (eq_refl ((term118 _93670 A f s) = (@FINITE A s))). Qed.
Lemma lem3656439 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) (y : A) : (term119 _93670 A s f x y) = (term119 _93670 A s f x y).
Proof. exact (eq_refl (term119 _93670 A s f x y)). Qed.
Lemma lem3656440 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term120 _93670 A s f x) = (term120 _93670 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3656439 _93670 A s f x y)). Qed.
Lemma lem3656441 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3656442 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term121 _93670 A s f x) = (term121 _93670 A s f x).
Proof. exact (MK_COMB (@lem3656441 A) (@lem3656440 _93670 A s f x)). Qed.
Lemma lem3656443 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) : (term122 _93670 A s f) = (term122 _93670 A s f).
Proof. exact (fun_ext (fun x : A => @lem3656442 _93670 A s f x)). Qed.
Lemma lem3656444 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3656445 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) : (term123 _93670 A s f) = (term123 _93670 A s f).
Proof. exact (MK_COMB (@lem3656444 A) (@lem3656443 _93670 A s f)). Qed.
Lemma lem3656446 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3656447 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) : (term124 _93670 A s f) = (term124 _93670 A s f).
Proof. exact (MK_COMB (@lem3656446) (@lem3656445 _93670 A s f)). Qed.
Lemma lem3656448 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term125 _93670 A f s) = (term125 _93670 A f s).
Proof. exact (MK_COMB (@lem3656447 _93670 A s f) (@lem3656426 _93670 A f s)). Qed.
Lemma lem3656449 {_93670 A : Type'} (f : A -> _93670) : (term126 _93670 A f) = (term126 _93670 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3656448 _93670 A f s)). Qed.
Lemma lem3656450 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3656451 {_93670 A : Type'} (f : A -> _93670) : (term127 _93670 A f) = (term127 _93670 A f).
Proof. exact (MK_COMB (@lem3656450 A) (@lem3656449 _93670 A f)). Qed.
Lemma lem3656452 {_93670 A : Type'} : (term128 _93670 A) = (term128 _93670 A).
Proof. exact (fun_ext (fun f : A -> _93670 => @lem3656451 _93670 A f)). Qed.
Lemma lem3656453 {_93670 A : Type'} : (@all (A -> _93670)) = (@all (A -> _93670)).
Proof. exact (eq_refl (@all (A -> _93670))). Qed.
Lemma lem3656454 {_93670 A : Type'} : (term83 _93670 A) = (term83 _93670 A).
Proof. exact (MK_COMB (@lem3656453 _93670 A) (@lem3656452 _93670 A)). Qed.
Lemma lem3656455 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3656456 {_93670 A : Type'} : (term90 _93670 A) = (term90 _93670 A).
Proof. exact (MK_COMB (@lem3656455) (@lem3656454 _93670 A)). Qed.
Lemma lem3656457 {_93670 _93677 A : Type'} : (term92 _93670 _93677 A) = (term92 _93670 _93677 A).
Proof. exact (MK_COMB (@lem3656456 _93670 A) (@lem3656421 _93677 A)). Qed.
Lemma lem3656462 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : ((term129 _93677 B f s) = (@FINITE _93677 s)) = ((term129 _93677 B f s) = (@FINITE _93677 s)).
Proof. exact (eq_refl ((term129 _93677 B f s) = (@FINITE _93677 s))). Qed.
Lemma lem3656475 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) (y : _93677) : (term130 _93677 B s f x y) = (term130 _93677 B s f x y).
Proof. exact (eq_refl (term130 _93677 B s f x y)). Qed.
Lemma lem3656476 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term131 _93677 B s f x) = (term131 _93677 B s f x).
Proof. exact (fun_ext (fun y : _93677 => @lem3656475 _93677 B s f x y)). Qed.
Lemma lem3656477 {_93677 : Type'} : (@all _93677) = (@all _93677).
Proof. exact (eq_refl (@all _93677)). Qed.
Lemma lem3656478 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term132 _93677 B s f x) = (term132 _93677 B s f x).
Proof. exact (MK_COMB (@lem3656477 _93677) (@lem3656476 _93677 B s f x)). Qed.
Lemma lem3656479 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) : (term133 _93677 B s f) = (term133 _93677 B s f).
Proof. exact (fun_ext (fun x : _93677 => @lem3656478 _93677 B s f x)). Qed.
Lemma lem3656480 {_93677 : Type'} : (@all _93677) = (@all _93677).
Proof. exact (eq_refl (@all _93677)). Qed.
Lemma lem3656481 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) : (term134 _93677 B s f) = (term134 _93677 B s f).
Proof. exact (MK_COMB (@lem3656480 _93677) (@lem3656479 _93677 B s f)). Qed.
Lemma lem3656482 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3656483 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) : (term135 _93677 B s f) = (term135 _93677 B s f).
Proof. exact (MK_COMB (@lem3656482) (@lem3656481 _93677 B s f)). Qed.
Lemma lem3656484 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term136 _93677 B f s) = (term136 _93677 B f s).
Proof. exact (MK_COMB (@lem3656483 _93677 B s f) (@lem3656462 _93677 B f s)). Qed.
Lemma lem3656485 {_93677 B : Type'} (f : _93677 -> B) : (term137 _93677 B f) = (term137 _93677 B f).
Proof. exact (fun_ext (fun s : _93677 -> Prop => @lem3656484 _93677 B f s)). Qed.
Lemma lem3656486 {_93677 : Type'} : (@all (_93677 -> Prop)) = (@all (_93677 -> Prop)).
Proof. exact (eq_refl (@all (_93677 -> Prop))). Qed.
Lemma lem3656487 {_93677 B : Type'} (f : _93677 -> B) : (term138 _93677 B f) = (term138 _93677 B f).
Proof. exact (MK_COMB (@lem3656486 _93677) (@lem3656485 _93677 B f)). Qed.
Lemma lem3656488 {_93677 B : Type'} : (term139 _93677 B) = (term139 _93677 B).
Proof. exact (fun_ext (fun f : _93677 -> B => @lem3656487 _93677 B f)). Qed.
Lemma lem3656489 {_93677 B : Type'} : (@all (_93677 -> B)) = (@all (_93677 -> B)).
Proof. exact (eq_refl (@all (_93677 -> B))). Qed.
Lemma lem3656490 {_93677 B : Type'} : (term82 _93677 B) = (term82 _93677 B).
Proof. exact (MK_COMB (@lem3656489 _93677 B) (@lem3656488 _93677 B)). Qed.
Lemma lem3656491 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3656492 {_93677 B : Type'} : (term93 _93677 B) = (term93 _93677 B).
Proof. exact (MK_COMB (@lem3656491) (@lem3656490 _93677 B)). Qed.
Lemma lem3656493 {_93670 _93677 A B : Type'} : (term95 _93670 _93677 A B) = (term95 _93670 _93677 A B).
Proof. exact (MK_COMB (@lem3656492 _93677 B) (@lem3656457 _93670 _93677 A)). Qed.
Lemma lem3656498 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : ((term129 _93670 B f s) = (@FINITE _93670 s)) = ((term129 _93670 B f s) = (@FINITE _93670 s)).
Proof. exact (eq_refl ((term129 _93670 B f s) = (@FINITE _93670 s))). Qed.
Lemma lem3656511 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) (y : _93670) : (term130 _93670 B s f x y) = (term130 _93670 B s f x y).
Proof. exact (eq_refl (term130 _93670 B s f x y)). Qed.
Lemma lem3656512 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term131 _93670 B s f x) = (term131 _93670 B s f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3656511 _93670 B s f x y)). Qed.
Lemma lem3656513 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3656514 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term132 _93670 B s f x) = (term132 _93670 B s f x).
Proof. exact (MK_COMB (@lem3656513 _93670) (@lem3656512 _93670 B s f x)). Qed.
Lemma lem3656515 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) : (term133 _93670 B s f) = (term133 _93670 B s f).
Proof. exact (fun_ext (fun x : _93670 => @lem3656514 _93670 B s f x)). Qed.
Lemma lem3656516 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3656517 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) : (term134 _93670 B s f) = (term134 _93670 B s f).
Proof. exact (MK_COMB (@lem3656516 _93670) (@lem3656515 _93670 B s f)). Qed.
Lemma lem3656518 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3656519 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) : (term135 _93670 B s f) = (term135 _93670 B s f).
Proof. exact (MK_COMB (@lem3656518) (@lem3656517 _93670 B s f)). Qed.
Lemma lem3656520 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term136 _93670 B f s) = (term136 _93670 B f s).
Proof. exact (MK_COMB (@lem3656519 _93670 B s f) (@lem3656498 _93670 B f s)). Qed.
Lemma lem3656521 {_93670 B : Type'} (f : _93670 -> B) : (term137 _93670 B f) = (term137 _93670 B f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3656520 _93670 B f s)). Qed.
Lemma lem3656522 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3656523 {_93670 B : Type'} (f : _93670 -> B) : (term138 _93670 B f) = (term138 _93670 B f).
Proof. exact (MK_COMB (@lem3656522 _93670) (@lem3656521 _93670 B f)). Qed.
Lemma lem3656524 {_93670 B : Type'} : (term139 _93670 B) = (term139 _93670 B).
Proof. exact (fun_ext (fun f : _93670 -> B => @lem3656523 _93670 B f)). Qed.
Lemma lem3656525 {_93670 B : Type'} : (@all (_93670 -> B)) = (@all (_93670 -> B)).
Proof. exact (eq_refl (@all (_93670 -> B))). Qed.
Lemma lem3656526 {_93670 B : Type'} : (term82 _93670 B) = (term82 _93670 B).
Proof. exact (MK_COMB (@lem3656525 _93670 B) (@lem3656524 _93670 B)). Qed.
Lemma lem3656527 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3656528 {_93670 B : Type'} : (term93 _93670 B) = (term93 _93670 B).
Proof. exact (MK_COMB (@lem3656527) (@lem3656526 _93670 B)). Qed.
Lemma lem3656529 {_93670 _93677 A B : Type'} : (term97 _93670 _93677 A B) = (term97 _93670 _93677 A B).
Proof. exact (MK_COMB (@lem3656528 _93670 B) (@lem3656493 _93670 _93677 A B)). Qed.
Lemma lem3656534 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : ((term129 _93670 _93677 f s) = (@FINITE _93670 s)) = ((term129 _93670 _93677 f s) = (@FINITE _93670 s)).
Proof. exact (eq_refl ((term129 _93670 _93677 f s) = (@FINITE _93670 s))). Qed.
Lemma lem3656547 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term130 _93670 _93677 s f x y) = (term130 _93670 _93677 s f x y).
Proof. exact (eq_refl (term130 _93670 _93677 s f x y)). Qed.
Lemma lem3656548 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term131 _93670 _93677 s f x) = (term131 _93670 _93677 s f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3656547 _93670 _93677 s f x y)). Qed.
Lemma lem3656549 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3656550 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term132 _93670 _93677 s f x) = (term132 _93670 _93677 s f x).
Proof. exact (MK_COMB (@lem3656549 _93670) (@lem3656548 _93670 _93677 s f x)). Qed.
Lemma lem3656551 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) : (term133 _93670 _93677 s f) = (term133 _93670 _93677 s f).
Proof. exact (fun_ext (fun x : _93670 => @lem3656550 _93670 _93677 s f x)). Qed.
Lemma lem3656552 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3656553 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) : (term134 _93670 _93677 s f) = (term134 _93670 _93677 s f).
Proof. exact (MK_COMB (@lem3656552 _93670) (@lem3656551 _93670 _93677 s f)). Qed.
Lemma lem3656554 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3656555 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) : (term135 _93670 _93677 s f) = (term135 _93670 _93677 s f).
Proof. exact (MK_COMB (@lem3656554) (@lem3656553 _93670 _93677 s f)). Qed.
Lemma lem3656556 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term136 _93670 _93677 f s) = (term136 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3656555 _93670 _93677 s f) (@lem3656534 _93670 _93677 f s)). Qed.
Lemma lem3656557 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term137 _93670 _93677 f) = (term137 _93670 _93677 f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3656556 _93670 _93677 f s)). Qed.
Lemma lem3656558 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3656559 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term138 _93670 _93677 f) = (term138 _93670 _93677 f).
Proof. exact (MK_COMB (@lem3656558 _93670) (@lem3656557 _93670 _93677 f)). Qed.
Lemma lem3656560 {_93670 _93677 : Type'} : (term139 _93670 _93677) = (term139 _93670 _93677).
Proof. exact (fun_ext (fun f : _93670 -> _93677 => @lem3656559 _93670 _93677 f)). Qed.
Lemma lem3656561 {_93670 _93677 : Type'} : (@all (_93670 -> _93677)) = (@all (_93670 -> _93677)).
Proof. exact (eq_refl (@all (_93670 -> _93677))). Qed.
Lemma lem3656562 {_93670 _93677 : Type'} : (term82 _93670 _93677) = (term82 _93670 _93677).
Proof. exact (MK_COMB (@lem3656561 _93670 _93677) (@lem3656560 _93670 _93677)). Qed.
Lemma lem3656563 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3656564 {_93670 _93677 : Type'} : (term93 _93670 _93677) = (term93 _93670 _93677).
Proof. exact (MK_COMB (@lem3656563) (@lem3656562 _93670 _93677)). Qed.
Lemma lem3656565 {_93670 _93677 A B : Type'} : (term99 _93670 _93677 A B) = (term99 _93670 _93677 A B).
Proof. exact (MK_COMB (@lem3656564 _93670 _93677) (@lem3656529 _93670 _93677 A B)). Qed.
Lemma lem3656566 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term140 _93670 _93677 P f t) = (term140 _93670 _93677 P f t).
Proof. exact (eq_refl (term140 _93670 _93677 P f t)). Qed.
Lemma lem3656579 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term141 _93670 _93677 t f x y) = (term141 _93670 _93677 t f x y).
Proof. exact (eq_refl (term141 _93670 _93677 t f x y)). Qed.
Lemma lem3656580 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term142 _93670 _93677 t f x) = (term142 _93670 _93677 t f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3656579 _93670 _93677 t f x y)). Qed.
Lemma lem3656581 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3656582 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term143 _93670 _93677 t f x) = (term143 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3656581 _93670) (@lem3656580 _93670 _93677 t f x)). Qed.
Lemma lem3656583 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term144 _93670 _93677 t f) = (term144 _93670 _93677 t f).
Proof. exact (fun_ext (fun x : _93670 => @lem3656582 _93670 _93677 t f x)). Qed.
Lemma lem3656584 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3656585 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term145 _93670 _93677 t f) = (term145 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3656584 _93670) (@lem3656583 _93670 _93677 t f)). Qed.
Lemma lem3656586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3656587 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term69 _93670 _93677 t f) = (term69 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3656586) (@lem3656585 _93670 _93677 t f)). Qed.
Lemma lem3656588 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term41 _93670 _93677 P f t) = (term41 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3656587 _93670 _93677 t f) (@lem3656566 _93670 _93677 P f t)). Qed.
Lemma lem3656591 {_93670 : Type'} (t : _93670 -> Prop) : (term146 _93670 t) = (term146 _93670 t).
Proof. exact (eq_refl (term146 _93670 t)). Qed.
Lemma lem3656592 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term147 _93670 _93677 P f t) = (term147 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3656591 _93670 t) (@lem3656588 _93670 _93677 P f t)). Qed.
Lemma lem3656595 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term72 _93670 t s) = (term72 _93670 t s).
Proof. exact (eq_refl (term72 _93670 t s)). Qed.
Lemma lem3656596 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term40 _93670 _93677 s P f t) = (term40 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3656595 _93670 t s) (@lem3656592 _93670 _93677 P f t)). Qed.
Lemma lem3656601 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term68 _93670 _93677 P f t) = (term68 _93670 _93677 P f t).
Proof. exact (eq_refl (term68 _93670 _93677 P f t)). Qed.
Lemma lem3656614 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term141 _93670 _93677 t f x y) = (term141 _93670 _93677 t f x y).
Proof. exact (eq_refl (term141 _93670 _93677 t f x y)). Qed.
Lemma lem3656615 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term142 _93670 _93677 t f x) = (term142 _93670 _93677 t f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3656614 _93670 _93677 t f x y)). Qed.
Lemma lem3656616 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3656617 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term143 _93670 _93677 t f x) = (term143 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3656616 _93670) (@lem3656615 _93670 _93677 t f x)). Qed.
Lemma lem3656618 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term144 _93670 _93677 t f) = (term144 _93670 _93677 t f).
Proof. exact (fun_ext (fun x : _93670 => @lem3656617 _93670 _93677 t f x)). Qed.
Lemma lem3656619 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3656620 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term145 _93670 _93677 t f) = (term145 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3656619 _93670) (@lem3656618 _93670 _93677 t f)). Qed.
Lemma lem3656621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3656622 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term69 _93670 _93677 t f) = (term69 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3656621) (@lem3656620 _93670 _93677 t f)). Qed.
Lemma lem3656623 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term71 _93670 _93677 P f t) = (term71 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3656622 _93670 _93677 t f) (@lem3656601 _93670 _93677 P f t)). Qed.
Lemma lem3656626 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term72 _93670 t s) = (term72 _93670 t s).
Proof. exact (eq_refl (term72 _93670 t s)). Qed.
Lemma lem3656627 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term74 _93670 _93677 s P f t) = (term74 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3656626 _93670 t s) (@lem3656623 _93670 _93677 P f t)). Qed.
Lemma lem3656628 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3656629 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term148 _93670 _93677 s P f t) = (term148 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3656628) (@lem3656627 _93670 _93677 s P f t)). Qed.
Lemma lem3656630 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term74 _93670 _93677 s P f t) = (term40 _93670 _93677 s P f t)) = ((term74 _93670 _93677 s P f t) = (term40 _93670 _93677 s P f t)).
Proof. exact (MK_COMB (@lem3656629 _93670 _93677 s P f t) (@lem3656596 _93670 _93677 s P f t)). Qed.
Lemma lem3656631 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3656632 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term81 _93670 _93677 s P f t) = (term81 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3656631) (@lem3656630 _93670 _93677 s P f t)). Qed.
Lemma lem3656633 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3656634 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term100 _93670 _93677 s P f t) = (term100 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3656633) (@lem3656632 _93670 _93677 s P f t)). Qed.
Lemma lem3656635 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term101 _93670 _93677 A B s P f t) = (term101 _93670 _93677 A B s P f t).
Proof. exact (MK_COMB (@lem3656634 _93670 _93677 s P f t) (@lem3656565 _93670 _93677 A B)). Qed.
Lemma lem3656636 {_93670 _93677 A B : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term103 _93670 _93677 A B P f t) = (term103 _93670 _93677 A B P f t).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3656635 _93670 _93677 A B s P f t)). Qed.
Lemma lem3656637 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3656638 {_93670 _93677 A B : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term105 _93670 _93677 A B P f t) = (term105 _93670 _93677 A B P f t).
Proof. exact (MK_COMB (@lem3656637 _93670) (@lem3656636 _93670 _93677 A B P f t)). Qed.
Lemma lem3656639 {_93670 _93677 A B : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term107 _93670 _93677 A B f t) = (term107 _93670 _93677 A B f t).
Proof. exact (fun_ext (fun P : type686 _93677 => @lem3656638 _93670 _93677 A B P f t)). Qed.
Lemma lem3656640 {_93677 : Type'} : (@all ((_93677 -> Prop) -> Prop)) = (@all ((_93677 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_93677 -> Prop) -> Prop))). Qed.
Lemma lem3656641 {_93670 _93677 A B : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term109 _93670 _93677 A B f t) = (term109 _93670 _93677 A B f t).
Proof. exact (MK_COMB (@lem3656640 _93677) (@lem3656639 _93670 _93677 A B f t)). Qed.
Lemma lem3656642 {_93670 _93677 A B : Type'} (t : _93670 -> Prop) : (term111 _93670 _93677 A B t) = (term111 _93670 _93677 A B t).
Proof. exact (fun_ext (fun f : _93670 -> _93677 => @lem3656641 _93670 _93677 A B f t)). Qed.
Lemma lem3656643 {_93670 _93677 : Type'} : (@all (_93670 -> _93677)) = (@all (_93670 -> _93677)).
Proof. exact (eq_refl (@all (_93670 -> _93677))). Qed.
Lemma lem3656644 {_93670 _93677 A B : Type'} (t : _93670 -> Prop) : (term113 _93670 _93677 A B t) = (term113 _93670 _93677 A B t).
Proof. exact (MK_COMB (@lem3656643 _93670 _93677) (@lem3656642 _93670 _93677 A B t)). Qed.
Lemma lem3656645 {_93670 _93677 A B : Type'} : (term115 _93670 _93677 A B) = (term115 _93670 _93677 A B).
Proof. exact (fun_ext (fun t : _93670 -> Prop => @lem3656644 _93670 _93677 A B t)). Qed.
Lemma lem3656646 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3656647 {_93670 _93677 A B : Type'} : (term117 _93670 _93677 A B) = (term117 _93670 _93677 A B).
Proof. exact (MK_COMB (@lem3656646 _93670) (@lem3656645 _93670 _93677 A B)). Qed.
Lemma lem3656888 {_93670 _93677 A B : Type'} : (term116 _93670 _93677 A B) = (term117 _93670 _93677 A B).
Proof. exact (TRANS (@lem3656386 _93670 _93677 A B) (@lem3656647 _93670 _93677 A B)). Qed.
Lemma lem3656889 {_93670 _93677 A B : Type'} : (term117 _93670 _93677 A B) = (term116 _93670 _93677 A B).
Proof. exact (SYM (@lem3656888 _93670 _93677 A B)). Qed.
Lemma lem3656890 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term81 _93670 _93677 s P f t) : term81 _93670 _93677 s P f t.
Proof. exact (h1). Qed.
Lemma lem3656891 {_93670 _93677 : Type'} (h1 : term82 _93670 _93677) : term82 _93670 _93677.
Proof. exact (h1). Qed.
Lemma lem3656892 {_93670 B : Type'} (h1 : term82 _93670 B) : term82 _93670 B.
Proof. exact (h1). Qed.
Lemma lem3656893 {_93677 B : Type'} (h1 : term82 _93677 B) : term82 _93677 B.
Proof. exact (h1). Qed.
Lemma lem3656894 {_93670 A : Type'} (h1 : term83 _93670 A) : term83 _93670 A.
Proof. exact (h1). Qed.
Lemma lem3656895 {_93677 A : Type'} (h1 : term83 _93677 A) : term83 _93677 A.
Proof. exact (h1). Qed.
Lemma lem3656906 {_93670 : Type'} (x : _93670) (y : _93670) (t : _93670 -> Prop) : (term149 _93670 x y t) = (term150 _93670 x y t).
Proof. exact (@lem17045 (@IN _93670 x t) (@IN _93670 y t)). Qed.
Lemma lem3656924 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term151 _93670 _93677 f x y) = (term152 _93670 _93677 f x y).
Proof. exact (@lem17930 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3656935 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) (y : _93670) : (((f x) = (f y)) = (x = y)) = (term153 _93670 _93677 f x y).
Proof. exact (@lem17784 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3656937 {_93670 : Type'} (x : _93670) (y : _93670) (t : _93670 -> Prop) : (term154 _93670 x y t) = (term154 _93670 x y t).
Proof. exact (eq_refl (term154 _93670 x y t)). Qed.
Lemma lem3656938 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term155 _93670 _93677 t f x y) = (term156 _93670 _93677 t f x y).
Proof. exact (MK_COMB (@lem3656937 _93670 x y t) (@lem3656924 _93670 _93677 f x y)). Qed.
Lemma lem3656939 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term157 _93670 _93677 t f x y) = (term155 _93670 _93677 t f x y).
Proof. exact (@lem17362 (term158 _93670 x y t) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3656940 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term157 _93670 _93677 t f x y) = (term156 _93670 _93677 t f x y).
Proof. exact (TRANS (@lem3656939 _93670 _93677 t f x y) (@lem3656938 _93670 _93677 t f x y)). Qed.
Lemma lem3656941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3656942 {_93670 : Type'} (x : _93670) (y : _93670) (t : _93670 -> Prop) : (term159 _93670 x y t) = (term160 _93670 x y t).
Proof. exact (MK_COMB (@lem3656941) (@lem3656906 _93670 x y t)). Qed.
Lemma lem3656943 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term161 _93670 _93677 t f x y) = (term162 _93670 _93677 t f x y).
Proof. exact (MK_COMB (@lem3656942 _93670 x y t) (@lem3656935 _93670 _93677 f x y)). Qed.
Lemma lem3656944 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term141 _93670 _93677 t f x y) = (term161 _93670 _93677 t f x y).
Proof. exact (@lem17265 (term158 _93670 x y t) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3656945 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term141 _93670 _93677 t f x y) = (term162 _93670 _93677 t f x y).
Proof. exact (TRANS (@lem3656944 _93670 _93677 t f x y) (@lem3656943 _93670 _93677 t f x y)). Qed.
Lemma lem3656946 {_93670 : Type'} (P : _93670 -> Prop) : (term163 _93670 P) = (term164 _93670 P).
Proof. exact (@lem18392 _93670 P). Qed.
Lemma lem3656947 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term165 _93670 _93677 t f x) = (term166 _93670 _93677 t f x).
Proof. exact (@lem3656946 _93670 (term142 _93670 _93677 t f x)). Qed.
Lemma lem3656948 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term167 _93670 _93677 t f x y) = (term141 _93670 _93677 t f x y).
Proof. exact (eq_refl (term167 _93670 _93677 t f x y)). Qed.
Lemma lem3656949 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3656950 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term168 _93670 _93677 t f x y) = (term157 _93670 _93677 t f x y).
Proof. exact (MK_COMB (@lem3656949) (@lem3656948 _93670 _93677 t f x y)). Qed.
Lemma lem3656951 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term168 _93670 _93677 t f x y) = (term156 _93670 _93677 t f x y).
Proof. exact (TRANS (@lem3656950 _93670 _93677 t f x y) (@lem3656940 _93670 _93677 t f x y)). Qed.
Lemma lem3656952 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term169 _93670 _93677 t f x) = (term170 _93670 _93677 t f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3656951 _93670 _93677 t f x y)). Qed.
Lemma lem3656953 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3656954 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term166 _93670 _93677 t f x) = (term171 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3656953 _93670) (@lem3656952 _93670 _93677 t f x)). Qed.
Lemma lem3656955 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term165 _93670 _93677 t f x) = (term171 _93670 _93677 t f x).
Proof. exact (TRANS (@lem3656947 _93670 _93677 t f x) (@lem3656954 _93670 _93677 t f x)). Qed.
Lemma lem3656956 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term142 _93670 _93677 t f x) = (term172 _93670 _93677 t f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3656945 _93670 _93677 t f x y)). Qed.
Lemma lem3656957 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3656958 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term143 _93670 _93677 t f x) = (term173 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3656957 _93670) (@lem3656956 _93670 _93677 t f x)). Qed.
Lemma lem3656959 {_93670 : Type'} (P : _93670 -> Prop) : (term163 _93670 P) = (term164 _93670 P).
Proof. exact (@lem18392 _93670 P). Qed.
Lemma lem3656960 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term174 _93670 _93677 t f) = (term175 _93670 _93677 t f).
Proof. exact (@lem3656959 _93670 (term144 _93670 _93677 t f)). Qed.
Lemma lem3656961 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term176 _93670 _93677 t f x) = (term143 _93670 _93677 t f x).
Proof. exact (eq_refl (term176 _93670 _93677 t f x)). Qed.
Lemma lem3656962 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3656963 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term177 _93670 _93677 t f x) = (term165 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3656962) (@lem3656961 _93670 _93677 t f x)). Qed.
Lemma lem3656964 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term177 _93670 _93677 t f x) = (term171 _93670 _93677 t f x).
Proof. exact (TRANS (@lem3656963 _93670 _93677 t f x) (@lem3656955 _93670 _93677 t f x)). Qed.
Lemma lem3656965 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term178 _93670 _93677 t f) = (term179 _93670 _93677 t f).
Proof. exact (fun_ext (fun x : _93670 => @lem3656964 _93670 _93677 t f x)). Qed.
Lemma lem3656966 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3656967 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term175 _93670 _93677 t f) = (term180 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3656966 _93670) (@lem3656965 _93670 _93677 t f)). Qed.
Lemma lem3656968 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term174 _93670 _93677 t f) = (term180 _93670 _93677 t f).
Proof. exact (TRANS (@lem3656960 _93670 _93677 t f) (@lem3656967 _93670 _93677 t f)). Qed.
Lemma lem3656969 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term144 _93670 _93677 t f) = (term181 _93670 _93677 t f).
Proof. exact (fun_ext (fun x : _93670 => @lem3656958 _93670 _93677 t f x)). Qed.
Lemma lem3656970 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3656971 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term145 _93670 _93677 t f) = (term182 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3656970 _93670) (@lem3656969 _93670 _93677 t f)). Qed.
Lemma lem3656980 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term183 _93670 _93677 P f t) = (term184 _93670 _93677 P f t).
Proof. exact (@lem17045 (term129 _93670 _93677 f t) (term140 _93670 _93677 P f t)). Qed.
Lemma lem3656983 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term68 _93670 _93677 P f t) = (term68 _93670 _93677 P f t).
Proof. exact (eq_refl (term68 _93670 _93677 P f t)). Qed.
Lemma lem3656984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3656985 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term185 _93670 _93677 t f) = (term186 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3656984) (@lem3656968 _93670 _93677 t f)). Qed.
Lemma lem3656986 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term187 _93670 _93677 P f t) = (term188 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3656985 _93670 _93677 t f) (@lem3656980 _93670 _93677 P f t)). Qed.
Lemma lem3656987 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term189 _93670 _93677 P f t) = (term187 _93670 _93677 P f t).
Proof. exact (@lem17045 (term145 _93670 _93677 t f) (term68 _93670 _93677 P f t)). Qed.
Lemma lem3656988 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term189 _93670 _93677 P f t) = (term188 _93670 _93677 P f t).
Proof. exact (TRANS (@lem3656987 _93670 _93677 P f t) (@lem3656986 _93670 _93677 P f t)). Qed.
Lemma lem3656989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3656990 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term69 _93670 _93677 t f) = (term190 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3656989) (@lem3656971 _93670 _93677 t f)). Qed.
Lemma lem3656991 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term71 _93670 _93677 P f t) = (term191 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3656990 _93670 _93677 t f) (@lem3656983 _93670 _93677 P f t)). Qed.
Lemma lem3656993 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term192 _93670 t s) = (term192 _93670 t s).
Proof. exact (eq_refl (term192 _93670 t s)). Qed.
Lemma lem3656994 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term193 _93670 _93677 s P f t) = (term194 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3656993 _93670 t s) (@lem3656988 _93670 _93677 P f t)). Qed.
Lemma lem3656995 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term195 _93670 _93677 s P f t) = (term193 _93670 _93677 s P f t).
Proof. exact (@lem17045 (@SUBSET _93670 t s) (term71 _93670 _93677 P f t)). Qed.
Lemma lem3656996 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term195 _93670 _93677 s P f t) = (term194 _93670 _93677 s P f t).
Proof. exact (TRANS (@lem3656995 _93670 _93677 s P f t) (@lem3656994 _93670 _93677 s P f t)). Qed.
Lemma lem3656998 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term72 _93670 t s) = (term72 _93670 t s).
Proof. exact (eq_refl (term72 _93670 t s)). Qed.
Lemma lem3656999 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term74 _93670 _93677 s P f t) = (term196 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3656998 _93670 t s) (@lem3656991 _93670 _93677 P f t)). Qed.
Lemma lem3657012 {_93670 : Type'} (x : _93670) (y : _93670) (t : _93670 -> Prop) : (term149 _93670 x y t) = (term150 _93670 x y t).
Proof. exact (@lem17045 (@IN _93670 x t) (@IN _93670 y t)). Qed.
Lemma lem3657030 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term151 _93670 _93677 f x y) = (term152 _93670 _93677 f x y).
Proof. exact (@lem17930 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3657041 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) (y : _93670) : (((f x) = (f y)) = (x = y)) = (term153 _93670 _93677 f x y).
Proof. exact (@lem17784 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3657043 {_93670 : Type'} (x : _93670) (y : _93670) (t : _93670 -> Prop) : (term154 _93670 x y t) = (term154 _93670 x y t).
Proof. exact (eq_refl (term154 _93670 x y t)). Qed.
Lemma lem3657044 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term155 _93670 _93677 t f x y) = (term156 _93670 _93677 t f x y).
Proof. exact (MK_COMB (@lem3657043 _93670 x y t) (@lem3657030 _93670 _93677 f x y)). Qed.
Lemma lem3657045 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term157 _93670 _93677 t f x y) = (term155 _93670 _93677 t f x y).
Proof. exact (@lem17362 (term158 _93670 x y t) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3657046 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term157 _93670 _93677 t f x y) = (term156 _93670 _93677 t f x y).
Proof. exact (TRANS (@lem3657045 _93670 _93677 t f x y) (@lem3657044 _93670 _93677 t f x y)). Qed.
Lemma lem3657047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657048 {_93670 : Type'} (x : _93670) (y : _93670) (t : _93670 -> Prop) : (term159 _93670 x y t) = (term160 _93670 x y t).
Proof. exact (MK_COMB (@lem3657047) (@lem3657012 _93670 x y t)). Qed.
Lemma lem3657049 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term161 _93670 _93677 t f x y) = (term162 _93670 _93677 t f x y).
Proof. exact (MK_COMB (@lem3657048 _93670 x y t) (@lem3657041 _93670 _93677 f x y)). Qed.
Lemma lem3657050 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term141 _93670 _93677 t f x y) = (term161 _93670 _93677 t f x y).
Proof. exact (@lem17265 (term158 _93670 x y t) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3657051 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term141 _93670 _93677 t f x y) = (term162 _93670 _93677 t f x y).
Proof. exact (TRANS (@lem3657050 _93670 _93677 t f x y) (@lem3657049 _93670 _93677 t f x y)). Qed.
Lemma lem3657052 {_93670 : Type'} (P : _93670 -> Prop) : (term163 _93670 P) = (term164 _93670 P).
Proof. exact (@lem18392 _93670 P). Qed.
Lemma lem3657053 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term165 _93670 _93677 t f x) = (term166 _93670 _93677 t f x).
Proof. exact (@lem3657052 _93670 (term142 _93670 _93677 t f x)). Qed.
Lemma lem3657054 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term167 _93670 _93677 t f x y) = (term141 _93670 _93677 t f x y).
Proof. exact (eq_refl (term167 _93670 _93677 t f x y)). Qed.
Lemma lem3657055 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3657056 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term168 _93670 _93677 t f x y) = (term157 _93670 _93677 t f x y).
Proof. exact (MK_COMB (@lem3657055) (@lem3657054 _93670 _93677 t f x y)). Qed.
Lemma lem3657057 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term168 _93670 _93677 t f x y) = (term156 _93670 _93677 t f x y).
Proof. exact (TRANS (@lem3657056 _93670 _93677 t f x y) (@lem3657046 _93670 _93677 t f x y)). Qed.
Lemma lem3657058 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term169 _93670 _93677 t f x) = (term170 _93670 _93677 t f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3657057 _93670 _93677 t f x y)). Qed.
Lemma lem3657059 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657060 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term166 _93670 _93677 t f x) = (term171 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3657059 _93670) (@lem3657058 _93670 _93677 t f x)). Qed.
Lemma lem3657061 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term165 _93670 _93677 t f x) = (term171 _93670 _93677 t f x).
Proof. exact (TRANS (@lem3657053 _93670 _93677 t f x) (@lem3657060 _93670 _93677 t f x)). Qed.
Lemma lem3657062 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term142 _93670 _93677 t f x) = (term172 _93670 _93677 t f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3657051 _93670 _93677 t f x y)). Qed.
Lemma lem3657063 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3657064 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term143 _93670 _93677 t f x) = (term173 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3657063 _93670) (@lem3657062 _93670 _93677 t f x)). Qed.
Lemma lem3657065 {_93670 : Type'} (P : _93670 -> Prop) : (term163 _93670 P) = (term164 _93670 P).
Proof. exact (@lem18392 _93670 P). Qed.
Lemma lem3657066 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term174 _93670 _93677 t f) = (term175 _93670 _93677 t f).
Proof. exact (@lem3657065 _93670 (term144 _93670 _93677 t f)). Qed.
Lemma lem3657067 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term176 _93670 _93677 t f x) = (term143 _93670 _93677 t f x).
Proof. exact (eq_refl (term176 _93670 _93677 t f x)). Qed.
Lemma lem3657068 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3657069 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term177 _93670 _93677 t f x) = (term165 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3657068) (@lem3657067 _93670 _93677 t f x)). Qed.
Lemma lem3657070 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term177 _93670 _93677 t f x) = (term171 _93670 _93677 t f x).
Proof. exact (TRANS (@lem3657069 _93670 _93677 t f x) (@lem3657061 _93670 _93677 t f x)). Qed.
Lemma lem3657071 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term178 _93670 _93677 t f) = (term179 _93670 _93677 t f).
Proof. exact (fun_ext (fun x : _93670 => @lem3657070 _93670 _93677 t f x)). Qed.
Lemma lem3657072 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657073 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term175 _93670 _93677 t f) = (term180 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3657072 _93670) (@lem3657071 _93670 _93677 t f)). Qed.
Lemma lem3657074 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term174 _93670 _93677 t f) = (term180 _93670 _93677 t f).
Proof. exact (TRANS (@lem3657066 _93670 _93677 t f) (@lem3657073 _93670 _93677 t f)). Qed.
Lemma lem3657075 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term144 _93670 _93677 t f) = (term181 _93670 _93677 t f).
Proof. exact (fun_ext (fun x : _93670 => @lem3657064 _93670 _93677 t f x)). Qed.
Lemma lem3657076 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3657077 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term145 _93670 _93677 t f) = (term182 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3657076 _93670) (@lem3657075 _93670 _93677 t f)). Qed.
Lemma lem3657078 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term197 _93670 _93677 P f t) = (term197 _93670 _93677 P f t).
Proof. exact (eq_refl (term197 _93670 _93677 P f t)). Qed.
Lemma lem3657079 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term140 _93670 _93677 P f t) = (term140 _93670 _93677 P f t).
Proof. exact (eq_refl (term140 _93670 _93677 P f t)). Qed.
Lemma lem3657080 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657081 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term185 _93670 _93677 t f) = (term186 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3657080) (@lem3657074 _93670 _93677 t f)). Qed.
Lemma lem3657082 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term198 _93670 _93677 P f t) = (term199 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657081 _93670 _93677 t f) (@lem3657078 _93670 _93677 P f t)). Qed.
Lemma lem3657083 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term200 _93670 _93677 P f t) = (term198 _93670 _93677 P f t).
Proof. exact (@lem17045 (term145 _93670 _93677 t f) (term140 _93670 _93677 P f t)). Qed.
Lemma lem3657084 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term200 _93670 _93677 P f t) = (term199 _93670 _93677 P f t).
Proof. exact (TRANS (@lem3657083 _93670 _93677 P f t) (@lem3657082 _93670 _93677 P f t)). Qed.
Lemma lem3657085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3657086 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term69 _93670 _93677 t f) = (term190 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3657085) (@lem3657077 _93670 _93677 t f)). Qed.
Lemma lem3657087 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term41 _93670 _93677 P f t) = (term201 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657086 _93670 _93677 t f) (@lem3657079 _93670 _93677 P f t)). Qed.
Lemma lem3657089 {_93670 : Type'} (t : _93670 -> Prop) : (term202 _93670 t) = (term202 _93670 t).
Proof. exact (eq_refl (term202 _93670 t)). Qed.
Lemma lem3657090 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term203 _93670 _93677 P f t) = (term204 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657089 _93670 t) (@lem3657084 _93670 _93677 P f t)). Qed.
Lemma lem3657091 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term205 _93670 _93677 P f t) = (term203 _93670 _93677 P f t).
Proof. exact (@lem17045 (@FINITE _93670 t) (term41 _93670 _93677 P f t)). Qed.
Lemma lem3657092 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term205 _93670 _93677 P f t) = (term204 _93670 _93677 P f t).
Proof. exact (TRANS (@lem3657091 _93670 _93677 P f t) (@lem3657090 _93670 _93677 P f t)). Qed.
Lemma lem3657094 {_93670 : Type'} (t : _93670 -> Prop) : (term146 _93670 t) = (term146 _93670 t).
Proof. exact (eq_refl (term146 _93670 t)). Qed.
Lemma lem3657095 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term147 _93670 _93677 P f t) = (term206 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657094 _93670 t) (@lem3657087 _93670 _93677 P f t)). Qed.
Lemma lem3657097 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term192 _93670 t s) = (term192 _93670 t s).
Proof. exact (eq_refl (term192 _93670 t s)). Qed.
Lemma lem3657098 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term207 _93670 _93677 s P f t) = (term208 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657097 _93670 t s) (@lem3657092 _93670 _93677 P f t)). Qed.
Lemma lem3657099 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term209 _93670 _93677 s P f t) = (term207 _93670 _93677 s P f t).
Proof. exact (@lem17045 (@SUBSET _93670 t s) (term147 _93670 _93677 P f t)). Qed.
Lemma lem3657100 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term209 _93670 _93677 s P f t) = (term208 _93670 _93677 s P f t).
Proof. exact (TRANS (@lem3657099 _93670 _93677 s P f t) (@lem3657098 _93670 _93677 s P f t)). Qed.
Lemma lem3657102 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term72 _93670 t s) = (term72 _93670 t s).
Proof. exact (eq_refl (term72 _93670 t s)). Qed.
Lemma lem3657103 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term40 _93670 _93677 s P f t) = (term210 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657102 _93670 t s) (@lem3657095 _93670 _93677 P f t)). Qed.
Lemma lem3657104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3657105 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term211 _93670 _93677 s P f t) = (term212 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657104) (@lem3656996 _93670 _93677 s P f t)). Qed.
Lemma lem3657106 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term213 _93670 _93677 s P f t) = (term214 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657105 _93670 _93677 s P f t) (@lem3657103 _93670 _93677 s P f t)). Qed.
Lemma lem3657107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3657108 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term215 _93670 _93677 s P f t) = (term216 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657107) (@lem3656999 _93670 _93677 s P f t)). Qed.
Lemma lem3657109 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term217 _93670 _93677 s P f t) = (term218 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657108 _93670 _93677 s P f t) (@lem3657100 _93670 _93677 s P f t)). Qed.
Lemma lem3657110 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657111 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term219 _93670 _93677 s P f t) = (term220 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657110) (@lem3657109 _93670 _93677 s P f t)). Qed.
Lemma lem3657112 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term221 _93670 _93677 s P f t) = (term222 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657111 _93670 _93677 s P f t) (@lem3657106 _93670 _93677 s P f t)). Qed.
Lemma lem3657113 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term81 _93670 _93677 s P f t) = (term221 _93670 _93677 s P f t).
Proof. exact (@lem17646 (term74 _93670 _93677 s P f t) (term40 _93670 _93677 s P f t)). Qed.
Lemma lem3657114 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term81 _93670 _93677 s P f t) = (term222 _93670 _93677 s P f t).
Proof. exact (TRANS (@lem3657113 _93670 _93677 s P f t) (@lem3657112 _93670 _93677 s P f t)). Qed.
Lemma lem3657325 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3657326 {_93670 : Type'} (P : _93670 -> Prop) (Q : Prop) : (term223 _93670 P Q) = (term224 _93670 P Q).
Proof. exact (@lem3657325 _93670 P Q). Qed.
Lemma lem3657327 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term225 _93670 _93677 P f t) = (term226 _93670 _93677 P f t).
Proof. exact (@lem3657326 _93670 (term179 _93670 _93677 t f) (term197 _93670 _93677 P f t)). Qed.
Lemma lem3657328 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term227 _93670 _93677 t f x) = (term171 _93670 _93677 t f x).
Proof. exact (eq_refl (term227 _93670 _93677 t f x)). Qed.
Lemma lem3657329 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term228 _93670 _93677 t f) = (term179 _93670 _93677 t f).
Proof. exact (fun_ext (fun x : _93670 => @lem3657328 _93670 _93677 t f x)). Qed.
Lemma lem3657330 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657331 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term229 _93670 _93677 t f) = (term180 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3657330 _93670) (@lem3657329 _93670 _93677 t f)). Qed.
Lemma lem3657332 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657333 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term230 _93670 _93677 t f) = (term186 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3657332) (@lem3657331 _93670 _93677 t f)). Qed.
Lemma lem3657334 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term197 _93670 _93677 P f t) = (term197 _93670 _93677 P f t).
Proof. exact (eq_refl (term197 _93670 _93677 P f t)). Qed.
Lemma lem3657335 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term225 _93670 _93677 P f t) = (term199 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657333 _93670 _93677 t f) (@lem3657334 _93670 _93677 P f t)). Qed.
Lemma lem3657336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657337 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term231 _93670 _93677 P f t) = (term232 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657336) (@lem3657335 _93670 _93677 P f t)). Qed.
Lemma lem3657338 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term227 _93670 _93677 t f x) = (term171 _93670 _93677 t f x).
Proof. exact (eq_refl (term227 _93670 _93677 t f x)). Qed.
Lemma lem3657339 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657340 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term233 _93670 _93677 t f x) = (term234 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3657339) (@lem3657338 _93670 _93677 t f x)). Qed.
Lemma lem3657341 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term197 _93670 _93677 P f t) = (term197 _93670 _93677 P f t).
Proof. exact (eq_refl (term197 _93670 _93677 P f t)). Qed.
Lemma lem3657342 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term235 _93670 _93677 x P f t) = (term236 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657340 _93670 _93677 t f x) (@lem3657341 _93670 _93677 P f t)). Qed.
Lemma lem3657343 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term237 _93670 _93677 P f t) = (term238 _93670 _93677 P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657342 _93670 _93677 x P f t)). Qed.
Lemma lem3657344 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657345 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term226 _93670 _93677 P f t) = (term239 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657344 _93670) (@lem3657343 _93670 _93677 P f t)). Qed.
Lemma lem3657346 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term225 _93670 _93677 P f t) = (term226 _93670 _93677 P f t)) = ((term199 _93670 _93677 P f t) = (term239 _93670 _93677 P f t)).
Proof. exact (MK_COMB (@lem3657337 _93670 _93677 P f t) (@lem3657345 _93670 _93677 P f t)). Qed.
Lemma lem3657347 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term199 _93670 _93677 P f t) = (term239 _93670 _93677 P f t).
Proof. exact (EQ_MP (@lem3657346 _93670 _93677 P f t) (@lem3657327 _93670 _93677 P f t)). Qed.
Lemma lem3657349 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3657350 {_93670 : Type'} (P : _93670 -> Prop) (Q : Prop) : (term223 _93670 P Q) = (term224 _93670 P Q).
Proof. exact (@lem3657349 _93670 P Q). Qed.
Lemma lem3657351 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term240 _93670 _93677 x P f t) = (term241 _93670 _93677 x P f t).
Proof. exact (@lem3657350 _93670 (term170 _93670 _93677 t f x) (term197 _93670 _93677 P f t)). Qed.
Lemma lem3657352 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term242 _93670 _93677 t f x y) = (term156 _93670 _93677 t f x y).
Proof. exact (eq_refl (term242 _93670 _93677 t f x y)). Qed.
Lemma lem3657353 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term243 _93670 _93677 t f x) = (term170 _93670 _93677 t f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3657352 _93670 _93677 t f x y)). Qed.
Lemma lem3657354 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657355 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term244 _93670 _93677 t f x) = (term171 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3657354 _93670) (@lem3657353 _93670 _93677 t f x)). Qed.
Lemma lem3657356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657357 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term245 _93670 _93677 t f x) = (term234 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3657356) (@lem3657355 _93670 _93677 t f x)). Qed.
Lemma lem3657358 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term197 _93670 _93677 P f t) = (term197 _93670 _93677 P f t).
Proof. exact (eq_refl (term197 _93670 _93677 P f t)). Qed.
Lemma lem3657359 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term240 _93670 _93677 x P f t) = (term236 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657357 _93670 _93677 t f x) (@lem3657358 _93670 _93677 P f t)). Qed.
Lemma lem3657360 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657361 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term246 _93670 _93677 x P f t) = (term247 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657360) (@lem3657359 _93670 _93677 x P f t)). Qed.
Lemma lem3657362 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term242 _93670 _93677 t f x y) = (term156 _93670 _93677 t f x y).
Proof. exact (eq_refl (term242 _93670 _93677 t f x y)). Qed.
Lemma lem3657363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657364 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term248 _93670 _93677 t f x y) = (term249 _93670 _93677 t f x y).
Proof. exact (MK_COMB (@lem3657363) (@lem3657362 _93670 _93677 t f x y)). Qed.
Lemma lem3657365 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term197 _93670 _93677 P f t) = (term197 _93670 _93677 P f t).
Proof. exact (eq_refl (term197 _93670 _93677 P f t)). Qed.
Lemma lem3657366 {_93670 _93677 : Type'} (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term250 _93670 _93677 x y P f t) = (term251 _93670 _93677 x y P f t).
Proof. exact (MK_COMB (@lem3657364 _93670 _93677 t f x y) (@lem3657365 _93670 _93677 P f t)). Qed.
Lemma lem3657367 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term252 _93670 _93677 x P f t) = (term253 _93670 _93677 x P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657366 _93670 _93677 x y P f t)). Qed.
Lemma lem3657368 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657369 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term241 _93670 _93677 x P f t) = (term254 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657368 _93670) (@lem3657367 _93670 _93677 x P f t)). Qed.
Lemma lem3657370 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term240 _93670 _93677 x P f t) = (term241 _93670 _93677 x P f t)) = ((term236 _93670 _93677 x P f t) = (term254 _93670 _93677 x P f t)).
Proof. exact (MK_COMB (@lem3657361 _93670 _93677 x P f t) (@lem3657369 _93670 _93677 x P f t)). Qed.
Lemma lem3657371 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term236 _93670 _93677 x P f t) = (term254 _93670 _93677 x P f t).
Proof. exact (EQ_MP (@lem3657370 _93670 _93677 x P f t) (@lem3657351 _93670 _93677 x P f t)). Qed.
Lemma lem3657372 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term238 _93670 _93677 P f t) = (term255 _93670 _93677 P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657371 _93670 _93677 x P f t)). Qed.
Lemma lem3657373 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657374 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term239 _93670 _93677 P f t) = (term256 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657373 _93670) (@lem3657372 _93670 _93677 P f t)). Qed.
Lemma lem3657375 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term199 _93670 _93677 P f t) = (term256 _93670 _93677 P f t).
Proof. exact (TRANS (@lem3657347 _93670 _93677 P f t) (@lem3657374 _93670 _93677 P f t)). Qed.
Lemma lem3657376 {_93670 : Type'} (t : _93670 -> Prop) : (term202 _93670 t) = (term202 _93670 t).
Proof. exact (eq_refl (term202 _93670 t)). Qed.
Lemma lem3657377 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term204 _93670 _93677 P f t) = (term257 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657376 _93670 t) (@lem3657375 _93670 _93677 P f t)). Qed.
Lemma lem3657379 {A : Type'} (P : Prop) (Q : A -> Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3657380 {_93670 : Type'} (P : Prop) (Q : _93670 -> Prop) : (term258 _93670 P Q) = (term259 _93670 P Q).
Proof. exact (@lem3657379 _93670 P Q). Qed.
Lemma lem3657381 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term260 _93670 _93677 P f t) = (term261 _93670 _93677 P f t).
Proof. exact (@lem3657380 _93670 (term262 _93670 t) (term255 _93670 _93677 P f t)). Qed.
Lemma lem3657382 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term263 _93670 _93677 P f t x) = (term254 _93670 _93677 x P f t).
Proof. exact (eq_refl (term263 _93670 _93677 P f t x)). Qed.
Lemma lem3657383 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term264 _93670 _93677 P f t) = (term255 _93670 _93677 P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657382 _93670 _93677 x P f t)). Qed.
Lemma lem3657384 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657385 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term265 _93670 _93677 P f t) = (term256 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657384 _93670) (@lem3657383 _93670 _93677 P f t)). Qed.
Lemma lem3657386 {_93670 : Type'} (t : _93670 -> Prop) : (term202 _93670 t) = (term202 _93670 t).
Proof. exact (eq_refl (term202 _93670 t)). Qed.
Lemma lem3657387 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term260 _93670 _93677 P f t) = (term257 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657386 _93670 t) (@lem3657385 _93670 _93677 P f t)). Qed.
Lemma lem3657388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657389 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term266 _93670 _93677 P f t) = (term267 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657388) (@lem3657387 _93670 _93677 P f t)). Qed.
Lemma lem3657390 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term263 _93670 _93677 P f t x) = (term254 _93670 _93677 x P f t).
Proof. exact (eq_refl (term263 _93670 _93677 P f t x)). Qed.
Lemma lem3657391 {_93670 : Type'} (t : _93670 -> Prop) : (term202 _93670 t) = (term202 _93670 t).
Proof. exact (eq_refl (term202 _93670 t)). Qed.
Lemma lem3657392 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term268 _93670 _93677 P f t x) = (term269 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657391 _93670 t) (@lem3657390 _93670 _93677 x P f t)). Qed.
Lemma lem3657393 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term270 _93670 _93677 P f t) = (term271 _93670 _93677 P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657392 _93670 _93677 x P f t)). Qed.
Lemma lem3657394 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657395 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term261 _93670 _93677 P f t) = (term272 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657394 _93670) (@lem3657393 _93670 _93677 P f t)). Qed.
Lemma lem3657396 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term260 _93670 _93677 P f t) = (term261 _93670 _93677 P f t)) = ((term257 _93670 _93677 P f t) = (term272 _93670 _93677 P f t)).
Proof. exact (MK_COMB (@lem3657389 _93670 _93677 P f t) (@lem3657395 _93670 _93677 P f t)). Qed.
Lemma lem3657397 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term257 _93670 _93677 P f t) = (term272 _93670 _93677 P f t).
Proof. exact (EQ_MP (@lem3657396 _93670 _93677 P f t) (@lem3657381 _93670 _93677 P f t)). Qed.
Lemma lem3657399 {A : Type'} (P : Prop) (Q : A -> Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3657400 {_93670 : Type'} (P : Prop) (Q : _93670 -> Prop) : (term258 _93670 P Q) = (term259 _93670 P Q).
Proof. exact (@lem3657399 _93670 P Q). Qed.
Lemma lem3657401 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term273 _93670 _93677 x P f t) = (term274 _93670 _93677 x P f t).
Proof. exact (@lem3657400 _93670 (term262 _93670 t) (term253 _93670 _93677 x P f t)). Qed.
Lemma lem3657402 {_93670 _93677 : Type'} (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term275 _93670 _93677 x P f t y) = (term251 _93670 _93677 x y P f t).
Proof. exact (eq_refl (term275 _93670 _93677 x P f t y)). Qed.
Lemma lem3657403 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term276 _93670 _93677 x P f t) = (term253 _93670 _93677 x P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657402 _93670 _93677 x y P f t)). Qed.
Lemma lem3657404 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657405 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term277 _93670 _93677 x P f t) = (term254 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657404 _93670) (@lem3657403 _93670 _93677 x P f t)). Qed.
Lemma lem3657406 {_93670 : Type'} (t : _93670 -> Prop) : (term202 _93670 t) = (term202 _93670 t).
Proof. exact (eq_refl (term202 _93670 t)). Qed.
Lemma lem3657407 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term273 _93670 _93677 x P f t) = (term269 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657406 _93670 t) (@lem3657405 _93670 _93677 x P f t)). Qed.
Lemma lem3657408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657409 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term278 _93670 _93677 x P f t) = (term279 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657408) (@lem3657407 _93670 _93677 x P f t)). Qed.
Lemma lem3657410 {_93670 _93677 : Type'} (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term275 _93670 _93677 x P f t y) = (term251 _93670 _93677 x y P f t).
Proof. exact (eq_refl (term275 _93670 _93677 x P f t y)). Qed.
Lemma lem3657411 {_93670 : Type'} (t : _93670 -> Prop) : (term202 _93670 t) = (term202 _93670 t).
Proof. exact (eq_refl (term202 _93670 t)). Qed.
Lemma lem3657412 {_93670 _93677 : Type'} (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term280 _93670 _93677 x P f t y) = (term281 _93670 _93677 x y P f t).
Proof. exact (MK_COMB (@lem3657411 _93670 t) (@lem3657410 _93670 _93677 x y P f t)). Qed.
Lemma lem3657413 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term282 _93670 _93677 x P f t) = (term283 _93670 _93677 x P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657412 _93670 _93677 x y P f t)). Qed.
Lemma lem3657414 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657415 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term274 _93670 _93677 x P f t) = (term284 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657414 _93670) (@lem3657413 _93670 _93677 x P f t)). Qed.
Lemma lem3657416 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term273 _93670 _93677 x P f t) = (term274 _93670 _93677 x P f t)) = ((term269 _93670 _93677 x P f t) = (term284 _93670 _93677 x P f t)).
Proof. exact (MK_COMB (@lem3657409 _93670 _93677 x P f t) (@lem3657415 _93670 _93677 x P f t)). Qed.
Lemma lem3657417 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term269 _93670 _93677 x P f t) = (term284 _93670 _93677 x P f t).
Proof. exact (EQ_MP (@lem3657416 _93670 _93677 x P f t) (@lem3657401 _93670 _93677 x P f t)). Qed.
Lemma lem3657418 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term271 _93670 _93677 P f t) = (term285 _93670 _93677 P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657417 _93670 _93677 x P f t)). Qed.
Lemma lem3657419 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657420 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term272 _93670 _93677 P f t) = (term286 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657419 _93670) (@lem3657418 _93670 _93677 P f t)). Qed.
Lemma lem3657421 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term257 _93670 _93677 P f t) = (term286 _93670 _93677 P f t).
Proof. exact (TRANS (@lem3657397 _93670 _93677 P f t) (@lem3657420 _93670 _93677 P f t)). Qed.
Lemma lem3657422 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term204 _93670 _93677 P f t) = (term286 _93670 _93677 P f t).
Proof. exact (TRANS (@lem3657377 _93670 _93677 P f t) (@lem3657421 _93670 _93677 P f t)). Qed.
Lemma lem3657423 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term192 _93670 t s) = (term192 _93670 t s).
Proof. exact (eq_refl (term192 _93670 t s)). Qed.
Lemma lem3657424 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term208 _93670 _93677 s P f t) = (term287 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657423 _93670 t s) (@lem3657422 _93670 _93677 P f t)). Qed.
Lemma lem3657426 {A : Type'} (P : Prop) (Q : A -> Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3657427 {_93670 : Type'} (P : Prop) (Q : _93670 -> Prop) : (term258 _93670 P Q) = (term259 _93670 P Q).
Proof. exact (@lem3657426 _93670 P Q). Qed.
Lemma lem3657428 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term288 _93670 _93677 s P f t) = (term289 _93670 _93677 s P f t).
Proof. exact (@lem3657427 _93670 (term290 _93670 t s) (term285 _93670 _93677 P f t)). Qed.
Lemma lem3657429 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term291 _93670 _93677 P f t x) = (term284 _93670 _93677 x P f t).
Proof. exact (eq_refl (term291 _93670 _93677 P f t x)). Qed.
Lemma lem3657430 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term292 _93670 _93677 P f t) = (term285 _93670 _93677 P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657429 _93670 _93677 x P f t)). Qed.
Lemma lem3657431 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657432 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term293 _93670 _93677 P f t) = (term286 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657431 _93670) (@lem3657430 _93670 _93677 P f t)). Qed.
Lemma lem3657433 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term192 _93670 t s) = (term192 _93670 t s).
Proof. exact (eq_refl (term192 _93670 t s)). Qed.
Lemma lem3657434 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term288 _93670 _93677 s P f t) = (term287 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657433 _93670 t s) (@lem3657432 _93670 _93677 P f t)). Qed.
Lemma lem3657435 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657436 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term294 _93670 _93677 s P f t) = (term295 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657435) (@lem3657434 _93670 _93677 s P f t)). Qed.
Lemma lem3657437 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term291 _93670 _93677 P f t x) = (term284 _93670 _93677 x P f t).
Proof. exact (eq_refl (term291 _93670 _93677 P f t x)). Qed.
Lemma lem3657438 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term192 _93670 t s) = (term192 _93670 t s).
Proof. exact (eq_refl (term192 _93670 t s)). Qed.
Lemma lem3657439 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term296 _93670 _93677 s P f t x) = (term297 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657438 _93670 t s) (@lem3657437 _93670 _93677 x P f t)). Qed.
Lemma lem3657440 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term298 _93670 _93677 s P f t) = (term299 _93670 _93677 s P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657439 _93670 _93677 s x P f t)). Qed.
Lemma lem3657441 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657442 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term289 _93670 _93677 s P f t) = (term300 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657441 _93670) (@lem3657440 _93670 _93677 s P f t)). Qed.
Lemma lem3657443 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term288 _93670 _93677 s P f t) = (term289 _93670 _93677 s P f t)) = ((term287 _93670 _93677 s P f t) = (term300 _93670 _93677 s P f t)).
Proof. exact (MK_COMB (@lem3657436 _93670 _93677 s P f t) (@lem3657442 _93670 _93677 s P f t)). Qed.
Lemma lem3657444 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term287 _93670 _93677 s P f t) = (term300 _93670 _93677 s P f t).
Proof. exact (EQ_MP (@lem3657443 _93670 _93677 s P f t) (@lem3657428 _93670 _93677 s P f t)). Qed.
Lemma lem3657446 {A : Type'} (P : Prop) (Q : A -> Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3657447 {_93670 : Type'} (P : Prop) (Q : _93670 -> Prop) : (term258 _93670 P Q) = (term259 _93670 P Q).
Proof. exact (@lem3657446 _93670 P Q). Qed.
Lemma lem3657448 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term301 _93670 _93677 s x P f t) = (term302 _93670 _93677 s x P f t).
Proof. exact (@lem3657447 _93670 (term290 _93670 t s) (term283 _93670 _93677 x P f t)). Qed.
Lemma lem3657449 {_93670 _93677 : Type'} (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term303 _93670 _93677 x P f t y) = (term281 _93670 _93677 x y P f t).
Proof. exact (eq_refl (term303 _93670 _93677 x P f t y)). Qed.
Lemma lem3657450 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term304 _93670 _93677 x P f t) = (term283 _93670 _93677 x P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657449 _93670 _93677 x y P f t)). Qed.
Lemma lem3657451 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657452 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term305 _93670 _93677 x P f t) = (term284 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657451 _93670) (@lem3657450 _93670 _93677 x P f t)). Qed.
Lemma lem3657453 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term192 _93670 t s) = (term192 _93670 t s).
Proof. exact (eq_refl (term192 _93670 t s)). Qed.
Lemma lem3657454 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term301 _93670 _93677 s x P f t) = (term297 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657453 _93670 t s) (@lem3657452 _93670 _93677 x P f t)). Qed.
Lemma lem3657455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657456 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term306 _93670 _93677 s x P f t) = (term307 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657455) (@lem3657454 _93670 _93677 s x P f t)). Qed.
Lemma lem3657457 {_93670 _93677 : Type'} (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term303 _93670 _93677 x P f t y) = (term281 _93670 _93677 x y P f t).
Proof. exact (eq_refl (term303 _93670 _93677 x P f t y)). Qed.
Lemma lem3657458 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term192 _93670 t s) = (term192 _93670 t s).
Proof. exact (eq_refl (term192 _93670 t s)). Qed.
Lemma lem3657459 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term308 _93670 _93677 s x P f t y) = (term309 _93670 _93677 s x y P f t).
Proof. exact (MK_COMB (@lem3657458 _93670 t s) (@lem3657457 _93670 _93677 x y P f t)). Qed.
Lemma lem3657460 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term310 _93670 _93677 s x P f t) = (term311 _93670 _93677 s x P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657459 _93670 _93677 s x y P f t)). Qed.
Lemma lem3657461 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657462 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term302 _93670 _93677 s x P f t) = (term312 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657461 _93670) (@lem3657460 _93670 _93677 s x P f t)). Qed.
Lemma lem3657463 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term301 _93670 _93677 s x P f t) = (term302 _93670 _93677 s x P f t)) = ((term297 _93670 _93677 s x P f t) = (term312 _93670 _93677 s x P f t)).
Proof. exact (MK_COMB (@lem3657456 _93670 _93677 s x P f t) (@lem3657462 _93670 _93677 s x P f t)). Qed.
Lemma lem3657464 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term297 _93670 _93677 s x P f t) = (term312 _93670 _93677 s x P f t).
Proof. exact (EQ_MP (@lem3657463 _93670 _93677 s x P f t) (@lem3657448 _93670 _93677 s x P f t)). Qed.
Lemma lem3657465 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term299 _93670 _93677 s P f t) = (term313 _93670 _93677 s P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657464 _93670 _93677 s x P f t)). Qed.
Lemma lem3657466 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657467 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term300 _93670 _93677 s P f t) = (term314 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657466 _93670) (@lem3657465 _93670 _93677 s P f t)). Qed.
Lemma lem3657468 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term287 _93670 _93677 s P f t) = (term314 _93670 _93677 s P f t).
Proof. exact (TRANS (@lem3657444 _93670 _93677 s P f t) (@lem3657467 _93670 _93677 s P f t)). Qed.
Lemma lem3657469 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term208 _93670 _93677 s P f t) = (term314 _93670 _93677 s P f t).
Proof. exact (TRANS (@lem3657424 _93670 _93677 s P f t) (@lem3657468 _93670 _93677 s P f t)). Qed.
Lemma lem3657470 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term216 _93670 _93677 s P f t) = (term216 _93670 _93677 s P f t).
Proof. exact (eq_refl (term216 _93670 _93677 s P f t)). Qed.
Lemma lem3657471 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term218 _93670 _93677 s P f t) = (term315 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657470 _93670 _93677 s P f t) (@lem3657469 _93670 _93677 s P f t)). Qed.
Lemma lem3657473 {A : Type'} (P : Prop) (Q : A -> Prop) : (term316 A P Q) = (term317 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3657474 {_93670 : Type'} (P : Prop) (Q : _93670 -> Prop) : (term316 _93670 P Q) = (term317 _93670 P Q).
Proof. exact (@lem3657473 _93670 P Q). Qed.
Lemma lem3657475 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term318 _93670 _93677 s P f t) = (term319 _93670 _93677 s P f t).
Proof. exact (@lem3657474 _93670 (term196 _93670 _93677 s P f t) (term313 _93670 _93677 s P f t)). Qed.
Lemma lem3657476 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term320 _93670 _93677 s P f t x) = (term312 _93670 _93677 s x P f t).
Proof. exact (eq_refl (term320 _93670 _93677 s P f t x)). Qed.
Lemma lem3657477 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term321 _93670 _93677 s P f t) = (term313 _93670 _93677 s P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657476 _93670 _93677 s x P f t)). Qed.
Lemma lem3657478 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657479 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term322 _93670 _93677 s P f t) = (term314 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657478 _93670) (@lem3657477 _93670 _93677 s P f t)). Qed.
Lemma lem3657480 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term216 _93670 _93677 s P f t) = (term216 _93670 _93677 s P f t).
Proof. exact (eq_refl (term216 _93670 _93677 s P f t)). Qed.
Lemma lem3657481 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term318 _93670 _93677 s P f t) = (term315 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657480 _93670 _93677 s P f t) (@lem3657479 _93670 _93677 s P f t)). Qed.
Lemma lem3657482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657483 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term323 _93670 _93677 s P f t) = (term324 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657482) (@lem3657481 _93670 _93677 s P f t)). Qed.
Lemma lem3657484 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term320 _93670 _93677 s P f t x) = (term312 _93670 _93677 s x P f t).
Proof. exact (eq_refl (term320 _93670 _93677 s P f t x)). Qed.
Lemma lem3657485 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term216 _93670 _93677 s P f t) = (term216 _93670 _93677 s P f t).
Proof. exact (eq_refl (term216 _93670 _93677 s P f t)). Qed.
Lemma lem3657486 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term325 _93670 _93677 s P f t x) = (term326 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657485 _93670 _93677 s P f t) (@lem3657484 _93670 _93677 s x P f t)). Qed.
Lemma lem3657487 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term327 _93670 _93677 s P f t) = (term328 _93670 _93677 s P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657486 _93670 _93677 s x P f t)). Qed.
Lemma lem3657488 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657489 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term319 _93670 _93677 s P f t) = (term329 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657488 _93670) (@lem3657487 _93670 _93677 s P f t)). Qed.
Lemma lem3657490 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term318 _93670 _93677 s P f t) = (term319 _93670 _93677 s P f t)) = ((term315 _93670 _93677 s P f t) = (term329 _93670 _93677 s P f t)).
Proof. exact (MK_COMB (@lem3657483 _93670 _93677 s P f t) (@lem3657489 _93670 _93677 s P f t)). Qed.
Lemma lem3657491 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term315 _93670 _93677 s P f t) = (term329 _93670 _93677 s P f t).
Proof. exact (EQ_MP (@lem3657490 _93670 _93677 s P f t) (@lem3657475 _93670 _93677 s P f t)). Qed.
Lemma lem3657493 {A : Type'} (P : Prop) (Q : A -> Prop) : (term316 A P Q) = (term317 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3657494 {_93670 : Type'} (P : Prop) (Q : _93670 -> Prop) : (term316 _93670 P Q) = (term317 _93670 P Q).
Proof. exact (@lem3657493 _93670 P Q). Qed.
Lemma lem3657495 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term330 _93670 _93677 s x P f t) = (term331 _93670 _93677 s x P f t).
Proof. exact (@lem3657494 _93670 (term196 _93670 _93677 s P f t) (term311 _93670 _93677 s x P f t)). Qed.
Lemma lem3657496 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term332 _93670 _93677 s x P f t y) = (term309 _93670 _93677 s x y P f t).
Proof. exact (eq_refl (term332 _93670 _93677 s x P f t y)). Qed.
Lemma lem3657497 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term333 _93670 _93677 s x P f t) = (term311 _93670 _93677 s x P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657496 _93670 _93677 s x y P f t)). Qed.
Lemma lem3657498 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657499 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term334 _93670 _93677 s x P f t) = (term312 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657498 _93670) (@lem3657497 _93670 _93677 s x P f t)). Qed.
Lemma lem3657500 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term216 _93670 _93677 s P f t) = (term216 _93670 _93677 s P f t).
Proof. exact (eq_refl (term216 _93670 _93677 s P f t)). Qed.
Lemma lem3657501 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term330 _93670 _93677 s x P f t) = (term326 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657500 _93670 _93677 s P f t) (@lem3657499 _93670 _93677 s x P f t)). Qed.
Lemma lem3657502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657503 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term335 _93670 _93677 s x P f t) = (term336 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657502) (@lem3657501 _93670 _93677 s x P f t)). Qed.
Lemma lem3657504 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term332 _93670 _93677 s x P f t y) = (term309 _93670 _93677 s x y P f t).
Proof. exact (eq_refl (term332 _93670 _93677 s x P f t y)). Qed.
Lemma lem3657505 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term216 _93670 _93677 s P f t) = (term216 _93670 _93677 s P f t).
Proof. exact (eq_refl (term216 _93670 _93677 s P f t)). Qed.
Lemma lem3657506 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term337 _93670 _93677 s x P f t y) = (term338 _93670 _93677 s x y P f t).
Proof. exact (MK_COMB (@lem3657505 _93670 _93677 s P f t) (@lem3657504 _93670 _93677 s x y P f t)). Qed.
Lemma lem3657507 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term339 _93670 _93677 s x P f t) = (term340 _93670 _93677 s x P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657506 _93670 _93677 s x y P f t)). Qed.
Lemma lem3657508 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657509 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term331 _93670 _93677 s x P f t) = (term341 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657508 _93670) (@lem3657507 _93670 _93677 s x P f t)). Qed.
Lemma lem3657510 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term330 _93670 _93677 s x P f t) = (term331 _93670 _93677 s x P f t)) = ((term326 _93670 _93677 s x P f t) = (term341 _93670 _93677 s x P f t)).
Proof. exact (MK_COMB (@lem3657503 _93670 _93677 s x P f t) (@lem3657509 _93670 _93677 s x P f t)). Qed.
Lemma lem3657511 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term326 _93670 _93677 s x P f t) = (term341 _93670 _93677 s x P f t).
Proof. exact (EQ_MP (@lem3657510 _93670 _93677 s x P f t) (@lem3657495 _93670 _93677 s x P f t)). Qed.
Lemma lem3657512 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term328 _93670 _93677 s P f t) = (term342 _93670 _93677 s P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657511 _93670 _93677 s x P f t)). Qed.
Lemma lem3657513 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657514 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term329 _93670 _93677 s P f t) = (term343 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657513 _93670) (@lem3657512 _93670 _93677 s P f t)). Qed.
Lemma lem3657515 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term315 _93670 _93677 s P f t) = (term343 _93670 _93677 s P f t).
Proof. exact (TRANS (@lem3657491 _93670 _93677 s P f t) (@lem3657514 _93670 _93677 s P f t)). Qed.
Lemma lem3657516 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term218 _93670 _93677 s P f t) = (term343 _93670 _93677 s P f t).
Proof. exact (TRANS (@lem3657471 _93670 _93677 s P f t) (@lem3657515 _93670 _93677 s P f t)). Qed.
Lemma lem3657517 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657518 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term220 _93670 _93677 s P f t) = (term344 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657517) (@lem3657516 _93670 _93677 s P f t)). Qed.
Lemma lem3657520 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3657521 {_93670 : Type'} (P : _93670 -> Prop) (Q : Prop) : (term223 _93670 P Q) = (term224 _93670 P Q).
Proof. exact (@lem3657520 _93670 P Q). Qed.
Lemma lem3657522 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term345 _93670 _93677 P f t) = (term346 _93670 _93677 P f t).
Proof. exact (@lem3657521 _93670 (term179 _93670 _93677 t f) (term184 _93670 _93677 P f t)). Qed.
Lemma lem3657523 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term227 _93670 _93677 t f x) = (term171 _93670 _93677 t f x).
Proof. exact (eq_refl (term227 _93670 _93677 t f x)). Qed.
Lemma lem3657524 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term228 _93670 _93677 t f) = (term179 _93670 _93677 t f).
Proof. exact (fun_ext (fun x : _93670 => @lem3657523 _93670 _93677 t f x)). Qed.
Lemma lem3657525 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657526 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term229 _93670 _93677 t f) = (term180 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3657525 _93670) (@lem3657524 _93670 _93677 t f)). Qed.
Lemma lem3657527 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657528 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term230 _93670 _93677 t f) = (term186 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3657527) (@lem3657526 _93670 _93677 t f)). Qed.
Lemma lem3657529 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term184 _93670 _93677 P f t) = (term184 _93670 _93677 P f t).
Proof. exact (eq_refl (term184 _93670 _93677 P f t)). Qed.
Lemma lem3657530 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term345 _93670 _93677 P f t) = (term188 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657528 _93670 _93677 t f) (@lem3657529 _93670 _93677 P f t)). Qed.
Lemma lem3657531 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657532 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term347 _93670 _93677 P f t) = (term348 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657531) (@lem3657530 _93670 _93677 P f t)). Qed.
Lemma lem3657533 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term227 _93670 _93677 t f x) = (term171 _93670 _93677 t f x).
Proof. exact (eq_refl (term227 _93670 _93677 t f x)). Qed.
Lemma lem3657534 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657535 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term233 _93670 _93677 t f x) = (term234 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3657534) (@lem3657533 _93670 _93677 t f x)). Qed.
Lemma lem3657536 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term184 _93670 _93677 P f t) = (term184 _93670 _93677 P f t).
Proof. exact (eq_refl (term184 _93670 _93677 P f t)). Qed.
Lemma lem3657537 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term349 _93670 _93677 x P f t) = (term350 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657535 _93670 _93677 t f x) (@lem3657536 _93670 _93677 P f t)). Qed.
Lemma lem3657538 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term351 _93670 _93677 P f t) = (term352 _93670 _93677 P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657537 _93670 _93677 x P f t)). Qed.
Lemma lem3657539 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657540 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term346 _93670 _93677 P f t) = (term353 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657539 _93670) (@lem3657538 _93670 _93677 P f t)). Qed.
Lemma lem3657541 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term345 _93670 _93677 P f t) = (term346 _93670 _93677 P f t)) = ((term188 _93670 _93677 P f t) = (term353 _93670 _93677 P f t)).
Proof. exact (MK_COMB (@lem3657532 _93670 _93677 P f t) (@lem3657540 _93670 _93677 P f t)). Qed.
Lemma lem3657542 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term188 _93670 _93677 P f t) = (term353 _93670 _93677 P f t).
Proof. exact (EQ_MP (@lem3657541 _93670 _93677 P f t) (@lem3657522 _93670 _93677 P f t)). Qed.
Lemma lem3657544 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3657545 {_93670 : Type'} (P : _93670 -> Prop) (Q : Prop) : (term223 _93670 P Q) = (term224 _93670 P Q).
Proof. exact (@lem3657544 _93670 P Q). Qed.
Lemma lem3657546 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term354 _93670 _93677 x P f t) = (term355 _93670 _93677 x P f t).
Proof. exact (@lem3657545 _93670 (term170 _93670 _93677 t f x) (term184 _93670 _93677 P f t)). Qed.
Lemma lem3657547 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term242 _93670 _93677 t f x y) = (term156 _93670 _93677 t f x y).
Proof. exact (eq_refl (term242 _93670 _93677 t f x y)). Qed.
Lemma lem3657548 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term243 _93670 _93677 t f x) = (term170 _93670 _93677 t f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3657547 _93670 _93677 t f x y)). Qed.
Lemma lem3657549 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657550 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term244 _93670 _93677 t f x) = (term171 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3657549 _93670) (@lem3657548 _93670 _93677 t f x)). Qed.
Lemma lem3657551 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657552 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term245 _93670 _93677 t f x) = (term234 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3657551) (@lem3657550 _93670 _93677 t f x)). Qed.
Lemma lem3657553 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term184 _93670 _93677 P f t) = (term184 _93670 _93677 P f t).
Proof. exact (eq_refl (term184 _93670 _93677 P f t)). Qed.
Lemma lem3657554 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term354 _93670 _93677 x P f t) = (term350 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657552 _93670 _93677 t f x) (@lem3657553 _93670 _93677 P f t)). Qed.
Lemma lem3657555 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657556 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term356 _93670 _93677 x P f t) = (term357 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657555) (@lem3657554 _93670 _93677 x P f t)). Qed.
Lemma lem3657557 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term242 _93670 _93677 t f x y) = (term156 _93670 _93677 t f x y).
Proof. exact (eq_refl (term242 _93670 _93677 t f x y)). Qed.
Lemma lem3657558 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657559 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term248 _93670 _93677 t f x y) = (term249 _93670 _93677 t f x y).
Proof. exact (MK_COMB (@lem3657558) (@lem3657557 _93670 _93677 t f x y)). Qed.
Lemma lem3657560 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term184 _93670 _93677 P f t) = (term184 _93670 _93677 P f t).
Proof. exact (eq_refl (term184 _93670 _93677 P f t)). Qed.
Lemma lem3657561 {_93670 _93677 : Type'} (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term358 _93670 _93677 x y P f t) = (term359 _93670 _93677 x y P f t).
Proof. exact (MK_COMB (@lem3657559 _93670 _93677 t f x y) (@lem3657560 _93670 _93677 P f t)). Qed.
Lemma lem3657562 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term360 _93670 _93677 x P f t) = (term361 _93670 _93677 x P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657561 _93670 _93677 x y P f t)). Qed.
Lemma lem3657563 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657564 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term355 _93670 _93677 x P f t) = (term362 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657563 _93670) (@lem3657562 _93670 _93677 x P f t)). Qed.
Lemma lem3657565 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term354 _93670 _93677 x P f t) = (term355 _93670 _93677 x P f t)) = ((term350 _93670 _93677 x P f t) = (term362 _93670 _93677 x P f t)).
Proof. exact (MK_COMB (@lem3657556 _93670 _93677 x P f t) (@lem3657564 _93670 _93677 x P f t)). Qed.
Lemma lem3657566 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term350 _93670 _93677 x P f t) = (term362 _93670 _93677 x P f t).
Proof. exact (EQ_MP (@lem3657565 _93670 _93677 x P f t) (@lem3657546 _93670 _93677 x P f t)). Qed.
Lemma lem3657567 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term352 _93670 _93677 P f t) = (term363 _93670 _93677 P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657566 _93670 _93677 x P f t)). Qed.
Lemma lem3657568 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657569 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term353 _93670 _93677 P f t) = (term364 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657568 _93670) (@lem3657567 _93670 _93677 P f t)). Qed.
Lemma lem3657570 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term188 _93670 _93677 P f t) = (term364 _93670 _93677 P f t).
Proof. exact (TRANS (@lem3657542 _93670 _93677 P f t) (@lem3657569 _93670 _93677 P f t)). Qed.
Lemma lem3657571 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term192 _93670 t s) = (term192 _93670 t s).
Proof. exact (eq_refl (term192 _93670 t s)). Qed.
Lemma lem3657572 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term194 _93670 _93677 s P f t) = (term365 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657571 _93670 t s) (@lem3657570 _93670 _93677 P f t)). Qed.
Lemma lem3657574 {A : Type'} (P : Prop) (Q : A -> Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3657575 {_93670 : Type'} (P : Prop) (Q : _93670 -> Prop) : (term258 _93670 P Q) = (term259 _93670 P Q).
Proof. exact (@lem3657574 _93670 P Q). Qed.
Lemma lem3657576 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term366 _93670 _93677 s P f t) = (term367 _93670 _93677 s P f t).
Proof. exact (@lem3657575 _93670 (term290 _93670 t s) (term363 _93670 _93677 P f t)). Qed.
Lemma lem3657577 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term368 _93670 _93677 P f t x) = (term362 _93670 _93677 x P f t).
Proof. exact (eq_refl (term368 _93670 _93677 P f t x)). Qed.
Lemma lem3657578 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term369 _93670 _93677 P f t) = (term363 _93670 _93677 P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657577 _93670 _93677 x P f t)). Qed.
Lemma lem3657579 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657580 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term370 _93670 _93677 P f t) = (term364 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3657579 _93670) (@lem3657578 _93670 _93677 P f t)). Qed.
Lemma lem3657581 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term192 _93670 t s) = (term192 _93670 t s).
Proof. exact (eq_refl (term192 _93670 t s)). Qed.
Lemma lem3657582 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term366 _93670 _93677 s P f t) = (term365 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657581 _93670 t s) (@lem3657580 _93670 _93677 P f t)). Qed.
Lemma lem3657583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657584 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term371 _93670 _93677 s P f t) = (term372 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657583) (@lem3657582 _93670 _93677 s P f t)). Qed.
Lemma lem3657585 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term368 _93670 _93677 P f t x) = (term362 _93670 _93677 x P f t).
Proof. exact (eq_refl (term368 _93670 _93677 P f t x)). Qed.
Lemma lem3657586 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term192 _93670 t s) = (term192 _93670 t s).
Proof. exact (eq_refl (term192 _93670 t s)). Qed.
Lemma lem3657587 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term373 _93670 _93677 s P f t x) = (term374 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657586 _93670 t s) (@lem3657585 _93670 _93677 x P f t)). Qed.
Lemma lem3657588 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term375 _93670 _93677 s P f t) = (term376 _93670 _93677 s P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657587 _93670 _93677 s x P f t)). Qed.
Lemma lem3657589 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657590 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term367 _93670 _93677 s P f t) = (term377 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657589 _93670) (@lem3657588 _93670 _93677 s P f t)). Qed.
Lemma lem3657591 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term366 _93670 _93677 s P f t) = (term367 _93670 _93677 s P f t)) = ((term365 _93670 _93677 s P f t) = (term377 _93670 _93677 s P f t)).
Proof. exact (MK_COMB (@lem3657584 _93670 _93677 s P f t) (@lem3657590 _93670 _93677 s P f t)). Qed.
Lemma lem3657592 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term365 _93670 _93677 s P f t) = (term377 _93670 _93677 s P f t).
Proof. exact (EQ_MP (@lem3657591 _93670 _93677 s P f t) (@lem3657576 _93670 _93677 s P f t)). Qed.
Lemma lem3657594 {A : Type'} (P : Prop) (Q : A -> Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3657595 {_93670 : Type'} (P : Prop) (Q : _93670 -> Prop) : (term258 _93670 P Q) = (term259 _93670 P Q).
Proof. exact (@lem3657594 _93670 P Q). Qed.
Lemma lem3657596 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term378 _93670 _93677 s x P f t) = (term379 _93670 _93677 s x P f t).
Proof. exact (@lem3657595 _93670 (term290 _93670 t s) (term361 _93670 _93677 x P f t)). Qed.
Lemma lem3657597 {_93670 _93677 : Type'} (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term380 _93670 _93677 x P f t y) = (term359 _93670 _93677 x y P f t).
Proof. exact (eq_refl (term380 _93670 _93677 x P f t y)). Qed.
Lemma lem3657598 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term381 _93670 _93677 x P f t) = (term361 _93670 _93677 x P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657597 _93670 _93677 x y P f t)). Qed.
Lemma lem3657599 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657600 {_93670 _93677 : Type'} (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term382 _93670 _93677 x P f t) = (term362 _93670 _93677 x P f t).
Proof. exact (MK_COMB (@lem3657599 _93670) (@lem3657598 _93670 _93677 x P f t)). Qed.
Lemma lem3657601 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term192 _93670 t s) = (term192 _93670 t s).
Proof. exact (eq_refl (term192 _93670 t s)). Qed.
Lemma lem3657602 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term378 _93670 _93677 s x P f t) = (term374 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657601 _93670 t s) (@lem3657600 _93670 _93677 x P f t)). Qed.
Lemma lem3657603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657604 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term383 _93670 _93677 s x P f t) = (term384 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657603) (@lem3657602 _93670 _93677 s x P f t)). Qed.
Lemma lem3657605 {_93670 _93677 : Type'} (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term380 _93670 _93677 x P f t y) = (term359 _93670 _93677 x y P f t).
Proof. exact (eq_refl (term380 _93670 _93677 x P f t y)). Qed.
Lemma lem3657606 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term192 _93670 t s) = (term192 _93670 t s).
Proof. exact (eq_refl (term192 _93670 t s)). Qed.
Lemma lem3657607 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term385 _93670 _93677 s x P f t y) = (term386 _93670 _93677 s x y P f t).
Proof. exact (MK_COMB (@lem3657606 _93670 t s) (@lem3657605 _93670 _93677 x y P f t)). Qed.
Lemma lem3657608 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term387 _93670 _93677 s x P f t) = (term388 _93670 _93677 s x P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657607 _93670 _93677 s x y P f t)). Qed.
Lemma lem3657609 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657610 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term379 _93670 _93677 s x P f t) = (term389 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657609 _93670) (@lem3657608 _93670 _93677 s x P f t)). Qed.
Lemma lem3657611 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term378 _93670 _93677 s x P f t) = (term379 _93670 _93677 s x P f t)) = ((term374 _93670 _93677 s x P f t) = (term389 _93670 _93677 s x P f t)).
Proof. exact (MK_COMB (@lem3657604 _93670 _93677 s x P f t) (@lem3657610 _93670 _93677 s x P f t)). Qed.
Lemma lem3657612 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term374 _93670 _93677 s x P f t) = (term389 _93670 _93677 s x P f t).
Proof. exact (EQ_MP (@lem3657611 _93670 _93677 s x P f t) (@lem3657596 _93670 _93677 s x P f t)). Qed.
Lemma lem3657613 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term376 _93670 _93677 s P f t) = (term390 _93670 _93677 s P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657612 _93670 _93677 s x P f t)). Qed.
Lemma lem3657614 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657615 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term377 _93670 _93677 s P f t) = (term391 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657614 _93670) (@lem3657613 _93670 _93677 s P f t)). Qed.
Lemma lem3657616 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term365 _93670 _93677 s P f t) = (term391 _93670 _93677 s P f t).
Proof. exact (TRANS (@lem3657592 _93670 _93677 s P f t) (@lem3657615 _93670 _93677 s P f t)). Qed.
Lemma lem3657617 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term194 _93670 _93677 s P f t) = (term391 _93670 _93677 s P f t).
Proof. exact (TRANS (@lem3657572 _93670 _93677 s P f t) (@lem3657616 _93670 _93677 s P f t)). Qed.
Lemma lem3657618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3657619 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term212 _93670 _93677 s P f t) = (term392 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657618) (@lem3657617 _93670 _93677 s P f t)). Qed.
Lemma lem3657620 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term210 _93670 _93677 s P f t) = (term210 _93670 _93677 s P f t).
Proof. exact (eq_refl (term210 _93670 _93677 s P f t)). Qed.
Lemma lem3657621 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term214 _93670 _93677 s P f t) = (term393 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657619 _93670 _93677 s P f t) (@lem3657620 _93670 _93677 s P f t)). Qed.
Lemma lem3657623 {A : Type'} (P : A -> Prop) (Q : Prop) : (term394 A P Q) = (term395 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3657624 {_93670 : Type'} (P : _93670 -> Prop) (Q : Prop) : (term394 _93670 P Q) = (term395 _93670 P Q).
Proof. exact (@lem3657623 _93670 P Q). Qed.
Lemma lem3657625 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term396 _93670 _93677 s P f t) = (term397 _93670 _93677 s P f t).
Proof. exact (@lem3657624 _93670 (term390 _93670 _93677 s P f t) (term210 _93670 _93677 s P f t)). Qed.
Lemma lem3657626 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term398 _93670 _93677 s P f t x) = (term389 _93670 _93677 s x P f t).
Proof. exact (eq_refl (term398 _93670 _93677 s P f t x)). Qed.
Lemma lem3657627 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term399 _93670 _93677 s P f t) = (term390 _93670 _93677 s P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657626 _93670 _93677 s x P f t)). Qed.
Lemma lem3657628 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657629 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term400 _93670 _93677 s P f t) = (term391 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657628 _93670) (@lem3657627 _93670 _93677 s P f t)). Qed.
Lemma lem3657630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3657631 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term401 _93670 _93677 s P f t) = (term392 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657630) (@lem3657629 _93670 _93677 s P f t)). Qed.
Lemma lem3657632 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term210 _93670 _93677 s P f t) = (term210 _93670 _93677 s P f t).
Proof. exact (eq_refl (term210 _93670 _93677 s P f t)). Qed.
Lemma lem3657633 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term396 _93670 _93677 s P f t) = (term393 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657631 _93670 _93677 s P f t) (@lem3657632 _93670 _93677 s P f t)). Qed.
Lemma lem3657634 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657635 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term402 _93670 _93677 s P f t) = (term403 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657634) (@lem3657633 _93670 _93677 s P f t)). Qed.
Lemma lem3657636 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term398 _93670 _93677 s P f t x) = (term389 _93670 _93677 s x P f t).
Proof. exact (eq_refl (term398 _93670 _93677 s P f t x)). Qed.
Lemma lem3657637 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3657638 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term404 _93670 _93677 s P f t x) = (term405 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657637) (@lem3657636 _93670 _93677 s x P f t)). Qed.
Lemma lem3657639 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term210 _93670 _93677 s P f t) = (term210 _93670 _93677 s P f t).
Proof. exact (eq_refl (term210 _93670 _93677 s P f t)). Qed.
Lemma lem3657640 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term406 _93670 _93677 x s P f t) = (term407 _93670 _93677 x s P f t).
Proof. exact (MK_COMB (@lem3657638 _93670 _93677 s x P f t) (@lem3657639 _93670 _93677 s P f t)). Qed.
Lemma lem3657641 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term408 _93670 _93677 s P f t) = (term409 _93670 _93677 s P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657640 _93670 _93677 x s P f t)). Qed.
Lemma lem3657642 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657643 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term397 _93670 _93677 s P f t) = (term410 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657642 _93670) (@lem3657641 _93670 _93677 s P f t)). Qed.
Lemma lem3657644 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term396 _93670 _93677 s P f t) = (term397 _93670 _93677 s P f t)) = ((term393 _93670 _93677 s P f t) = (term410 _93670 _93677 s P f t)).
Proof. exact (MK_COMB (@lem3657635 _93670 _93677 s P f t) (@lem3657643 _93670 _93677 s P f t)). Qed.
Lemma lem3657645 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term393 _93670 _93677 s P f t) = (term410 _93670 _93677 s P f t).
Proof. exact (EQ_MP (@lem3657644 _93670 _93677 s P f t) (@lem3657625 _93670 _93677 s P f t)). Qed.
Lemma lem3657647 {A : Type'} (P : A -> Prop) (Q : Prop) : (term394 A P Q) = (term395 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3657648 {_93670 : Type'} (P : _93670 -> Prop) (Q : Prop) : (term394 _93670 P Q) = (term395 _93670 P Q).
Proof. exact (@lem3657647 _93670 P Q). Qed.
Lemma lem3657649 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term411 _93670 _93677 x s P f t) = (term412 _93670 _93677 x s P f t).
Proof. exact (@lem3657648 _93670 (term388 _93670 _93677 s x P f t) (term210 _93670 _93677 s P f t)). Qed.
Lemma lem3657650 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term413 _93670 _93677 s x P f t y) = (term386 _93670 _93677 s x y P f t).
Proof. exact (eq_refl (term413 _93670 _93677 s x P f t y)). Qed.
Lemma lem3657651 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term414 _93670 _93677 s x P f t) = (term388 _93670 _93677 s x P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657650 _93670 _93677 s x y P f t)). Qed.
Lemma lem3657652 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657653 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term415 _93670 _93677 s x P f t) = (term389 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657652 _93670) (@lem3657651 _93670 _93677 s x P f t)). Qed.
Lemma lem3657654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3657655 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term416 _93670 _93677 s x P f t) = (term405 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657654) (@lem3657653 _93670 _93677 s x P f t)). Qed.
Lemma lem3657656 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term210 _93670 _93677 s P f t) = (term210 _93670 _93677 s P f t).
Proof. exact (eq_refl (term210 _93670 _93677 s P f t)). Qed.
Lemma lem3657657 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term411 _93670 _93677 x s P f t) = (term407 _93670 _93677 x s P f t).
Proof. exact (MK_COMB (@lem3657655 _93670 _93677 s x P f t) (@lem3657656 _93670 _93677 s P f t)). Qed.
Lemma lem3657658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657659 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term417 _93670 _93677 x s P f t) = (term418 _93670 _93677 x s P f t).
Proof. exact (MK_COMB (@lem3657658) (@lem3657657 _93670 _93677 x s P f t)). Qed.
Lemma lem3657660 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term413 _93670 _93677 s x P f t y) = (term386 _93670 _93677 s x y P f t).
Proof. exact (eq_refl (term413 _93670 _93677 s x P f t y)). Qed.
Lemma lem3657661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3657662 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term419 _93670 _93677 s x P f t y) = (term420 _93670 _93677 s x y P f t).
Proof. exact (MK_COMB (@lem3657661) (@lem3657660 _93670 _93677 s x y P f t)). Qed.
Lemma lem3657663 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term210 _93670 _93677 s P f t) = (term210 _93670 _93677 s P f t).
Proof. exact (eq_refl (term210 _93670 _93677 s P f t)). Qed.
Lemma lem3657664 {_93670 _93677 : Type'} (x : _93670) (y : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term421 _93670 _93677 x y s P f t) = (term422 _93670 _93677 x y s P f t).
Proof. exact (MK_COMB (@lem3657662 _93670 _93677 s x y P f t) (@lem3657663 _93670 _93677 s P f t)). Qed.
Lemma lem3657665 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term423 _93670 _93677 x s P f t) = (term424 _93670 _93677 x s P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657664 _93670 _93677 x y s P f t)). Qed.
Lemma lem3657666 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657667 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term412 _93670 _93677 x s P f t) = (term425 _93670 _93677 x s P f t).
Proof. exact (MK_COMB (@lem3657666 _93670) (@lem3657665 _93670 _93677 x s P f t)). Qed.
Lemma lem3657668 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term411 _93670 _93677 x s P f t) = (term412 _93670 _93677 x s P f t)) = ((term407 _93670 _93677 x s P f t) = (term425 _93670 _93677 x s P f t)).
Proof. exact (MK_COMB (@lem3657659 _93670 _93677 x s P f t) (@lem3657667 _93670 _93677 x s P f t)). Qed.
Lemma lem3657669 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term407 _93670 _93677 x s P f t) = (term425 _93670 _93677 x s P f t).
Proof. exact (EQ_MP (@lem3657668 _93670 _93677 x s P f t) (@lem3657649 _93670 _93677 x s P f t)). Qed.
Lemma lem3657670 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term409 _93670 _93677 s P f t) = (term426 _93670 _93677 s P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657669 _93670 _93677 x s P f t)). Qed.
Lemma lem3657671 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657672 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term410 _93670 _93677 s P f t) = (term427 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657671 _93670) (@lem3657670 _93670 _93677 s P f t)). Qed.
Lemma lem3657673 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term393 _93670 _93677 s P f t) = (term427 _93670 _93677 s P f t).
Proof. exact (TRANS (@lem3657645 _93670 _93677 s P f t) (@lem3657672 _93670 _93677 s P f t)). Qed.
Lemma lem3657674 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term214 _93670 _93677 s P f t) = (term427 _93670 _93677 s P f t).
Proof. exact (TRANS (@lem3657621 _93670 _93677 s P f t) (@lem3657673 _93670 _93677 s P f t)). Qed.
Lemma lem3657675 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term222 _93670 _93677 s P f t) = (term428 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657518 _93670 _93677 s P f t) (@lem3657674 _93670 _93677 s P f t)). Qed.
Lemma lem3657677 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term429 A P Q) = (term430 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3657678 {_93670 : Type'} (P : _93670 -> Prop) (Q : _93670 -> Prop) : (term429 _93670 P Q) = (term430 _93670 P Q).
Proof. exact (@lem3657677 _93670 P Q). Qed.
Lemma lem3657679 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term431 _93670 _93677 s P f t) = (term432 _93670 _93677 s P f t).
Proof. exact (@lem3657678 _93670 (term342 _93670 _93677 s P f t) (term426 _93670 _93677 s P f t)). Qed.
Lemma lem3657680 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term433 _93670 _93677 s P f t x) = (term341 _93670 _93677 s x P f t).
Proof. exact (eq_refl (term433 _93670 _93677 s P f t x)). Qed.
Lemma lem3657681 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term434 _93670 _93677 s P f t) = (term342 _93670 _93677 s P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657680 _93670 _93677 s x P f t)). Qed.
Lemma lem3657682 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657683 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term435 _93670 _93677 s P f t) = (term343 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657682 _93670) (@lem3657681 _93670 _93677 s P f t)). Qed.
Lemma lem3657684 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657685 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term436 _93670 _93677 s P f t) = (term344 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657684) (@lem3657683 _93670 _93677 s P f t)). Qed.
Lemma lem3657686 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term437 _93670 _93677 s P f t x) = (term425 _93670 _93677 x s P f t).
Proof. exact (eq_refl (term437 _93670 _93677 s P f t x)). Qed.
Lemma lem3657687 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term438 _93670 _93677 s P f t) = (term426 _93670 _93677 s P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657686 _93670 _93677 x s P f t)). Qed.
Lemma lem3657688 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657689 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term439 _93670 _93677 s P f t) = (term427 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657688 _93670) (@lem3657687 _93670 _93677 s P f t)). Qed.
Lemma lem3657690 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term431 _93670 _93677 s P f t) = (term428 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657685 _93670 _93677 s P f t) (@lem3657689 _93670 _93677 s P f t)). Qed.
Lemma lem3657691 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657692 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term440 _93670 _93677 s P f t) = (term441 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657691) (@lem3657690 _93670 _93677 s P f t)). Qed.
Lemma lem3657693 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term433 _93670 _93677 s P f t x) = (term341 _93670 _93677 s x P f t).
Proof. exact (eq_refl (term433 _93670 _93677 s P f t x)). Qed.
Lemma lem3657694 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657695 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term442 _93670 _93677 s P f t x) = (term443 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657694) (@lem3657693 _93670 _93677 s x P f t)). Qed.
Lemma lem3657696 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term437 _93670 _93677 s P f t x) = (term425 _93670 _93677 x s P f t).
Proof. exact (eq_refl (term437 _93670 _93677 s P f t x)). Qed.
Lemma lem3657697 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term444 _93670 _93677 s P f t x) = (term445 _93670 _93677 x s P f t).
Proof. exact (MK_COMB (@lem3657695 _93670 _93677 s x P f t) (@lem3657696 _93670 _93677 x s P f t)). Qed.
Lemma lem3657698 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term446 _93670 _93677 s P f t) = (term447 _93670 _93677 s P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657697 _93670 _93677 x s P f t)). Qed.
Lemma lem3657699 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657700 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term432 _93670 _93677 s P f t) = (term448 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657699 _93670) (@lem3657698 _93670 _93677 s P f t)). Qed.
Lemma lem3657701 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term431 _93670 _93677 s P f t) = (term432 _93670 _93677 s P f t)) = ((term428 _93670 _93677 s P f t) = (term448 _93670 _93677 s P f t)).
Proof. exact (MK_COMB (@lem3657692 _93670 _93677 s P f t) (@lem3657700 _93670 _93677 s P f t)). Qed.
Lemma lem3657702 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term428 _93670 _93677 s P f t) = (term448 _93670 _93677 s P f t).
Proof. exact (EQ_MP (@lem3657701 _93670 _93677 s P f t) (@lem3657679 _93670 _93677 s P f t)). Qed.
Lemma lem3657704 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term429 A P Q) = (term430 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3657705 {_93670 : Type'} (P : _93670 -> Prop) (Q : _93670 -> Prop) : (term429 _93670 P Q) = (term430 _93670 P Q).
Proof. exact (@lem3657704 _93670 P Q). Qed.
Lemma lem3657706 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term449 _93670 _93677 x s P f t) = (term450 _93670 _93677 x s P f t).
Proof. exact (@lem3657705 _93670 (term340 _93670 _93677 s x P f t) (term424 _93670 _93677 x s P f t)). Qed.
Lemma lem3657707 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term451 _93670 _93677 s x P f t y) = (term338 _93670 _93677 s x y P f t).
Proof. exact (eq_refl (term451 _93670 _93677 s x P f t y)). Qed.
Lemma lem3657708 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term452 _93670 _93677 s x P f t) = (term340 _93670 _93677 s x P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657707 _93670 _93677 s x y P f t)). Qed.
Lemma lem3657709 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657710 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term453 _93670 _93677 s x P f t) = (term341 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657709 _93670) (@lem3657708 _93670 _93677 s x P f t)). Qed.
Lemma lem3657711 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657712 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term454 _93670 _93677 s x P f t) = (term443 _93670 _93677 s x P f t).
Proof. exact (MK_COMB (@lem3657711) (@lem3657710 _93670 _93677 s x P f t)). Qed.
Lemma lem3657713 {_93670 _93677 : Type'} (x : _93670) (y : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term455 _93670 _93677 x s P f t y) = (term422 _93670 _93677 x y s P f t).
Proof. exact (eq_refl (term455 _93670 _93677 x s P f t y)). Qed.
Lemma lem3657714 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term456 _93670 _93677 x s P f t) = (term424 _93670 _93677 x s P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657713 _93670 _93677 x y s P f t)). Qed.
Lemma lem3657715 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657716 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term457 _93670 _93677 x s P f t) = (term425 _93670 _93677 x s P f t).
Proof. exact (MK_COMB (@lem3657715 _93670) (@lem3657714 _93670 _93677 x s P f t)). Qed.
Lemma lem3657717 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term449 _93670 _93677 x s P f t) = (term445 _93670 _93677 x s P f t).
Proof. exact (MK_COMB (@lem3657712 _93670 _93677 s x P f t) (@lem3657716 _93670 _93677 x s P f t)). Qed.
Lemma lem3657718 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657719 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term458 _93670 _93677 x s P f t) = (term459 _93670 _93677 x s P f t).
Proof. exact (MK_COMB (@lem3657718) (@lem3657717 _93670 _93677 x s P f t)). Qed.
Lemma lem3657720 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term451 _93670 _93677 s x P f t y) = (term338 _93670 _93677 s x y P f t).
Proof. exact (eq_refl (term451 _93670 _93677 s x P f t y)). Qed.
Lemma lem3657721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657722 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x : _93670) (y : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term460 _93670 _93677 s x P f t y) = (term461 _93670 _93677 s x y P f t).
Proof. exact (MK_COMB (@lem3657721) (@lem3657720 _93670 _93677 s x y P f t)). Qed.
Lemma lem3657723 {_93670 _93677 : Type'} (x : _93670) (y : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term455 _93670 _93677 x s P f t y) = (term422 _93670 _93677 x y s P f t).
Proof. exact (eq_refl (term455 _93670 _93677 x s P f t y)). Qed.
Lemma lem3657724 {_93670 _93677 : Type'} (x : _93670) (y : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term462 _93670 _93677 x s P f t y) = (term463 _93670 _93677 x y s P f t).
Proof. exact (MK_COMB (@lem3657722 _93670 _93677 s x y P f t) (@lem3657723 _93670 _93677 x y s P f t)). Qed.
Lemma lem3657725 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term464 _93670 _93677 x s P f t) = (term465 _93670 _93677 x s P f t).
Proof. exact (fun_ext (fun y : _93670 => @lem3657724 _93670 _93677 x y s P f t)). Qed.
Lemma lem3657726 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657727 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term450 _93670 _93677 x s P f t) = (term466 _93670 _93677 x s P f t).
Proof. exact (MK_COMB (@lem3657726 _93670) (@lem3657725 _93670 _93677 x s P f t)). Qed.
Lemma lem3657728 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : ((term449 _93670 _93677 x s P f t) = (term450 _93670 _93677 x s P f t)) = ((term445 _93670 _93677 x s P f t) = (term466 _93670 _93677 x s P f t)).
Proof. exact (MK_COMB (@lem3657719 _93670 _93677 x s P f t) (@lem3657727 _93670 _93677 x s P f t)). Qed.
Lemma lem3657729 {_93670 _93677 : Type'} (x : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term445 _93670 _93677 x s P f t) = (term466 _93670 _93677 x s P f t).
Proof. exact (EQ_MP (@lem3657728 _93670 _93677 x s P f t) (@lem3657706 _93670 _93677 x s P f t)). Qed.
Lemma lem3657730 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term447 _93670 _93677 s P f t) = (term467 _93670 _93677 s P f t).
Proof. exact (fun_ext (fun x : _93670 => @lem3657729 _93670 _93677 x s P f t)). Qed.
Lemma lem3657731 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657732 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term448 _93670 _93677 s P f t) = (term468 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3657731 _93670) (@lem3657730 _93670 _93677 s P f t)). Qed.
Lemma lem3657733 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term428 _93670 _93677 s P f t) = (term468 _93670 _93677 s P f t).
Proof. exact (TRANS (@lem3657702 _93670 _93677 s P f t) (@lem3657732 _93670 _93677 s P f t)). Qed.
Lemma lem3657735 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term222 _93670 _93677 s P f t) = (term468 _93670 _93677 s P f t).
Proof. exact (TRANS (@lem3657675 _93670 _93677 s P f t) (@lem3657733 _93670 _93677 s P f t)). Qed.
Lemma lem3657736 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term81 _93670 _93677 s P f t) = (term468 _93670 _93677 s P f t).
Proof. exact (TRANS (@lem3657114 _93670 _93677 s P f t) (@lem3657735 _93670 _93677 s P f t)). Qed.
Lemma lem3657737 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term81 _93670 _93677 s P f t) : term468 _93670 _93677 s P f t.
Proof. exact (EQ_MP (@lem3657736 _93670 _93677 s P f t) (@lem3656890 _93670 _93677 s P f t h1)). Qed.
Lemma lem3657752 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term469 _93670 _93677 s f x y) = (term470 _93670 _93677 s f x y).
Proof. exact (@lem17362 (term471 _93670 _93677 s x f y) (x = y)). Qed.
Lemma lem3657753 {_93670 : Type'} (P : _93670 -> Prop) : (term163 _93670 P) = (term164 _93670 P).
Proof. exact (@lem18392 _93670 P). Qed.
Lemma lem3657754 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term472 _93670 _93677 s f x) = (term473 _93670 _93677 s f x).
Proof. exact (@lem3657753 _93670 (term131 _93670 _93677 s f x)). Qed.
Lemma lem3657755 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term474 _93670 _93677 s f x y) = (term130 _93670 _93677 s f x y).
Proof. exact (eq_refl (term474 _93670 _93677 s f x y)). Qed.
Lemma lem3657756 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3657757 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term475 _93670 _93677 s f x y) = (term469 _93670 _93677 s f x y).
Proof. exact (MK_COMB (@lem3657756) (@lem3657755 _93670 _93677 s f x y)). Qed.
Lemma lem3657758 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term475 _93670 _93677 s f x y) = (term470 _93670 _93677 s f x y).
Proof. exact (TRANS (@lem3657757 _93670 _93677 s f x y) (@lem3657752 _93670 _93677 s f x y)). Qed.
Lemma lem3657759 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term476 _93670 _93677 s f x) = (term477 _93670 _93677 s f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3657758 _93670 _93677 s f x y)). Qed.
Lemma lem3657760 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657761 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term473 _93670 _93677 s f x) = (term478 _93670 _93677 s f x).
Proof. exact (MK_COMB (@lem3657760 _93670) (@lem3657759 _93670 _93677 s f x)). Qed.
Lemma lem3657762 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term472 _93670 _93677 s f x) = (term478 _93670 _93677 s f x).
Proof. exact (TRANS (@lem3657754 _93670 _93677 s f x) (@lem3657761 _93670 _93677 s f x)). Qed.
Lemma lem3657763 {_93670 : Type'} (P : _93670 -> Prop) : (term163 _93670 P) = (term164 _93670 P).
Proof. exact (@lem18392 _93670 P). Qed.
Lemma lem3657764 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) : (term479 _93670 _93677 s f) = (term480 _93670 _93677 s f).
Proof. exact (@lem3657763 _93670 (term133 _93670 _93677 s f)). Qed.
Lemma lem3657765 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term481 _93670 _93677 s f x) = (term132 _93670 _93677 s f x).
Proof. exact (eq_refl (term481 _93670 _93677 s f x)). Qed.
Lemma lem3657766 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3657767 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term482 _93670 _93677 s f x) = (term472 _93670 _93677 s f x).
Proof. exact (MK_COMB (@lem3657766) (@lem3657765 _93670 _93677 s f x)). Qed.
Lemma lem3657768 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term482 _93670 _93677 s f x) = (term478 _93670 _93677 s f x).
Proof. exact (TRANS (@lem3657767 _93670 _93677 s f x) (@lem3657762 _93670 _93677 s f x)). Qed.
Lemma lem3657769 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) : (term483 _93670 _93677 s f) = (term484 _93670 _93677 s f).
Proof. exact (fun_ext (fun x : _93670 => @lem3657768 _93670 _93677 s f x)). Qed.
Lemma lem3657770 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657771 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) : (term480 _93670 _93677 s f) = (term485 _93670 _93677 s f).
Proof. exact (MK_COMB (@lem3657770 _93670) (@lem3657769 _93670 _93677 s f)). Qed.
Lemma lem3657772 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) : (term479 _93670 _93677 s f) = (term485 _93670 _93677 s f).
Proof. exact (TRANS (@lem3657764 _93670 _93677 s f) (@lem3657771 _93670 _93677 s f)). Qed.
Lemma lem3657787 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : ((term129 _93670 _93677 f s) = (@FINITE _93670 s)) = (term486 _93670 _93677 f s).
Proof. exact (@lem17784 (term129 _93670 _93677 f s) (@FINITE _93670 s)). Qed.
Lemma lem3657788 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657789 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) : (term487 _93670 _93677 s f) = (term488 _93670 _93677 s f).
Proof. exact (MK_COMB (@lem3657788) (@lem3657772 _93670 _93677 s f)). Qed.
Lemma lem3657790 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term489 _93670 _93677 f s) = (term490 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3657789 _93670 _93677 s f) (@lem3657787 _93670 _93677 f s)). Qed.
Lemma lem3657791 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term136 _93670 _93677 f s) = (term489 _93670 _93677 f s).
Proof. exact (@lem17265 (term134 _93670 _93677 s f) ((term129 _93670 _93677 f s) = (@FINITE _93670 s))). Qed.
Lemma lem3657792 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term136 _93670 _93677 f s) = (term490 _93670 _93677 f s).
Proof. exact (TRANS (@lem3657791 _93670 _93677 f s) (@lem3657790 _93670 _93677 f s)). Qed.
Lemma lem3657793 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term137 _93670 _93677 f) = (term491 _93670 _93677 f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3657792 _93670 _93677 f s)). Qed.
Lemma lem3657794 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3657795 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term138 _93670 _93677 f) = (term492 _93670 _93677 f).
Proof. exact (MK_COMB (@lem3657794 _93670) (@lem3657793 _93670 _93677 f)). Qed.
Lemma lem3657796 {_93670 _93677 : Type'} : (term139 _93670 _93677) = (term493 _93670 _93677).
Proof. exact (fun_ext (fun f : _93670 -> _93677 => @lem3657795 _93670 _93677 f)). Qed.
Lemma lem3657797 {_93670 _93677 : Type'} : (@all (_93670 -> _93677)) = (@all (_93670 -> _93677)).
Proof. exact (eq_refl (@all (_93670 -> _93677))). Qed.
Lemma lem3657798 {_93670 _93677 : Type'} : (term82 _93670 _93677) = (term494 _93670 _93677).
Proof. exact (MK_COMB (@lem3657797 _93670 _93677) (@lem3657796 _93670 _93677)). Qed.
Lemma lem3657905 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3657906 {_93670 : Type'} (P : _93670 -> Prop) (Q : Prop) : (term223 _93670 P Q) = (term224 _93670 P Q).
Proof. exact (@lem3657905 _93670 P Q). Qed.
Lemma lem3657907 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term495 _93670 _93677 f s) = (term496 _93670 _93677 f s).
Proof. exact (@lem3657906 _93670 (term484 _93670 _93677 s f) (term486 _93670 _93677 f s)). Qed.
Lemma lem3657908 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term497 _93670 _93677 s f x) = (term478 _93670 _93677 s f x).
Proof. exact (eq_refl (term497 _93670 _93677 s f x)). Qed.
Lemma lem3657909 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) : (term498 _93670 _93677 s f) = (term484 _93670 _93677 s f).
Proof. exact (fun_ext (fun x : _93670 => @lem3657908 _93670 _93677 s f x)). Qed.
Lemma lem3657910 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657911 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) : (term499 _93670 _93677 s f) = (term485 _93670 _93677 s f).
Proof. exact (MK_COMB (@lem3657910 _93670) (@lem3657909 _93670 _93677 s f)). Qed.
Lemma lem3657912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657913 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) : (term500 _93670 _93677 s f) = (term488 _93670 _93677 s f).
Proof. exact (MK_COMB (@lem3657912) (@lem3657911 _93670 _93677 s f)). Qed.
Lemma lem3657914 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term486 _93670 _93677 f s) = (term486 _93670 _93677 f s).
Proof. exact (eq_refl (term486 _93670 _93677 f s)). Qed.
Lemma lem3657915 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term495 _93670 _93677 f s) = (term490 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3657913 _93670 _93677 s f) (@lem3657914 _93670 _93677 f s)). Qed.
Lemma lem3657916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657917 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term501 _93670 _93677 f s) = (term502 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3657916) (@lem3657915 _93670 _93677 f s)). Qed.
Lemma lem3657918 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term497 _93670 _93677 s f x) = (term478 _93670 _93677 s f x).
Proof. exact (eq_refl (term497 _93670 _93677 s f x)). Qed.
Lemma lem3657919 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657920 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term503 _93670 _93677 s f x) = (term504 _93670 _93677 s f x).
Proof. exact (MK_COMB (@lem3657919) (@lem3657918 _93670 _93677 s f x)). Qed.
Lemma lem3657921 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term486 _93670 _93677 f s) = (term486 _93670 _93677 f s).
Proof. exact (eq_refl (term486 _93670 _93677 f s)). Qed.
Lemma lem3657922 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term505 _93670 _93677 x f s) = (term506 _93670 _93677 x f s).
Proof. exact (MK_COMB (@lem3657920 _93670 _93677 s f x) (@lem3657921 _93670 _93677 f s)). Qed.
Lemma lem3657923 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term507 _93670 _93677 f s) = (term508 _93670 _93677 f s).
Proof. exact (fun_ext (fun x : _93670 => @lem3657922 _93670 _93677 x f s)). Qed.
Lemma lem3657924 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657925 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term496 _93670 _93677 f s) = (term509 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3657924 _93670) (@lem3657923 _93670 _93677 f s)). Qed.
Lemma lem3657926 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : ((term495 _93670 _93677 f s) = (term496 _93670 _93677 f s)) = ((term490 _93670 _93677 f s) = (term509 _93670 _93677 f s)).
Proof. exact (MK_COMB (@lem3657917 _93670 _93677 f s) (@lem3657925 _93670 _93677 f s)). Qed.
Lemma lem3657927 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term490 _93670 _93677 f s) = (term509 _93670 _93677 f s).
Proof. exact (EQ_MP (@lem3657926 _93670 _93677 f s) (@lem3657907 _93670 _93677 f s)). Qed.
Lemma lem3657929 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3657930 {_93670 : Type'} (P : _93670 -> Prop) (Q : Prop) : (term223 _93670 P Q) = (term224 _93670 P Q).
Proof. exact (@lem3657929 _93670 P Q). Qed.
Lemma lem3657931 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term510 _93670 _93677 x f s) = (term511 _93670 _93677 x f s).
Proof. exact (@lem3657930 _93670 (term477 _93670 _93677 s f x) (term486 _93670 _93677 f s)). Qed.
Lemma lem3657932 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term512 _93670 _93677 s f x y) = (term470 _93670 _93677 s f x y).
Proof. exact (eq_refl (term512 _93670 _93677 s f x y)). Qed.
Lemma lem3657933 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term513 _93670 _93677 s f x) = (term477 _93670 _93677 s f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3657932 _93670 _93677 s f x y)). Qed.
Lemma lem3657934 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657935 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term514 _93670 _93677 s f x) = (term478 _93670 _93677 s f x).
Proof. exact (MK_COMB (@lem3657934 _93670) (@lem3657933 _93670 _93677 s f x)). Qed.
Lemma lem3657936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657937 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term515 _93670 _93677 s f x) = (term504 _93670 _93677 s f x).
Proof. exact (MK_COMB (@lem3657936) (@lem3657935 _93670 _93677 s f x)). Qed.
Lemma lem3657938 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term486 _93670 _93677 f s) = (term486 _93670 _93677 f s).
Proof. exact (eq_refl (term486 _93670 _93677 f s)). Qed.
Lemma lem3657939 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term510 _93670 _93677 x f s) = (term506 _93670 _93677 x f s).
Proof. exact (MK_COMB (@lem3657937 _93670 _93677 s f x) (@lem3657938 _93670 _93677 f s)). Qed.
Lemma lem3657940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657941 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term516 _93670 _93677 x f s) = (term517 _93670 _93677 x f s).
Proof. exact (MK_COMB (@lem3657940) (@lem3657939 _93670 _93677 x f s)). Qed.
Lemma lem3657942 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term512 _93670 _93677 s f x y) = (term470 _93670 _93677 s f x y).
Proof. exact (eq_refl (term512 _93670 _93677 s f x y)). Qed.
Lemma lem3657943 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3657944 {_93670 _93677 : Type'} (s : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term518 _93670 _93677 s f x y) = (term519 _93670 _93677 s f x y).
Proof. exact (MK_COMB (@lem3657943) (@lem3657942 _93670 _93677 s f x y)). Qed.
Lemma lem3657945 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term486 _93670 _93677 f s) = (term486 _93670 _93677 f s).
Proof. exact (eq_refl (term486 _93670 _93677 f s)). Qed.
Lemma lem3657946 {_93670 _93677 : Type'} (x : _93670) (y : _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term520 _93670 _93677 x y f s) = (term521 _93670 _93677 x y f s).
Proof. exact (MK_COMB (@lem3657944 _93670 _93677 s f x y) (@lem3657945 _93670 _93677 f s)). Qed.
Lemma lem3657947 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term522 _93670 _93677 x f s) = (term523 _93670 _93677 x f s).
Proof. exact (fun_ext (fun y : _93670 => @lem3657946 _93670 _93677 x y f s)). Qed.
Lemma lem3657948 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657949 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term511 _93670 _93677 x f s) = (term524 _93670 _93677 x f s).
Proof. exact (MK_COMB (@lem3657948 _93670) (@lem3657947 _93670 _93677 x f s)). Qed.
Lemma lem3657950 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : ((term510 _93670 _93677 x f s) = (term511 _93670 _93677 x f s)) = ((term506 _93670 _93677 x f s) = (term524 _93670 _93677 x f s)).
Proof. exact (MK_COMB (@lem3657941 _93670 _93677 x f s) (@lem3657949 _93670 _93677 x f s)). Qed.
Lemma lem3657951 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term506 _93670 _93677 x f s) = (term524 _93670 _93677 x f s).
Proof. exact (EQ_MP (@lem3657950 _93670 _93677 x f s) (@lem3657931 _93670 _93677 x f s)). Qed.
Lemma lem3657952 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term508 _93670 _93677 f s) = (term525 _93670 _93677 f s).
Proof. exact (fun_ext (fun x : _93670 => @lem3657951 _93670 _93677 x f s)). Qed.
Lemma lem3657953 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657954 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term509 _93670 _93677 f s) = (term526 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3657953 _93670) (@lem3657952 _93670 _93677 f s)). Qed.
Lemma lem3657955 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term490 _93670 _93677 f s) = (term526 _93670 _93677 f s).
Proof. exact (TRANS (@lem3657927 _93670 _93677 f s) (@lem3657954 _93670 _93677 f s)). Qed.
Lemma lem3657956 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term491 _93670 _93677 f) = (term527 _93670 _93677 f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3657955 _93670 _93677 f s)). Qed.
Lemma lem3657957 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3657958 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term492 _93670 _93677 f) = (term528 _93670 _93677 f).
Proof. exact (MK_COMB (@lem3657957 _93670) (@lem3657956 _93670 _93677 f)). Qed.
Lemma lem3657960 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3657961 {_93670 : Type'} (P : type672 _93670) : (term531 _93670 P) = (term532 _93670 P).
Proof. exact (@lem3657960 (_93670 -> Prop) _93670 P). Qed.
Lemma lem3657962 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term533 _93670 _93677 f) = (term534 _93670 _93677 f).
Proof. exact (@lem3657961 _93670 (term535 _93670 _93677 f)). Qed.
Lemma lem3657963 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term536 _93670 _93677 f s) = (term525 _93670 _93677 f s).
Proof. exact (eq_refl (term536 _93670 _93677 f s)). Qed.
Lemma lem3657964 {_93670 : Type'} (x : _93670) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3657965 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) (x : _93670) : (term537 _93670 _93677 f s x) = (term538 _93670 _93677 f s x).
Proof. exact (MK_COMB (@lem3657963 _93670 _93677 f s) (@lem3657964 _93670 x)). Qed.
Lemma lem3657966 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term538 _93670 _93677 f s x) = (term524 _93670 _93677 x f s).
Proof. exact (eq_refl (term538 _93670 _93677 f s x)). Qed.
Lemma lem3657967 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term537 _93670 _93677 f s x) = (term524 _93670 _93677 x f s).
Proof. exact (TRANS (@lem3657965 _93670 _93677 f s x) (@lem3657966 _93670 _93677 x f s)). Qed.
Lemma lem3657968 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term539 _93670 _93677 f s) = (term525 _93670 _93677 f s).
Proof. exact (fun_ext (fun x : _93670 => @lem3657967 _93670 _93677 x f s)). Qed.
Lemma lem3657969 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3657970 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term540 _93670 _93677 f s) = (term526 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3657969 _93670) (@lem3657968 _93670 _93677 f s)). Qed.
Lemma lem3657971 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term541 _93670 _93677 f) = (term527 _93670 _93677 f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3657970 _93670 _93677 f s)). Qed.
Lemma lem3657972 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3657973 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term533 _93670 _93677 f) = (term528 _93670 _93677 f).
Proof. exact (MK_COMB (@lem3657972 _93670) (@lem3657971 _93670 _93677 f)). Qed.
Lemma lem3657974 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3657975 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term542 _93670 _93677 f) = (term543 _93670 _93677 f).
Proof. exact (MK_COMB (@lem3657974) (@lem3657973 _93670 _93677 f)). Qed.
Lemma lem3657976 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term536 _93670 _93677 f s) = (term525 _93670 _93677 f s).
Proof. exact (eq_refl (term536 _93670 _93677 f s)). Qed.
Lemma lem3657977 {_93670 : Type'} (x : type684 _93670) (s : _93670 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3657978 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : type684 _93670) (s : _93670 -> Prop) : (term544 _93670 _93677 f x s) = (term545 _93670 _93677 f x s).
Proof. exact (MK_COMB (@lem3657976 _93670 _93677 f s) (@lem3657977 _93670 x s)). Qed.
Lemma lem3657979 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term545 _93670 _93677 f x s) = (term546 _93670 _93677 x f s).
Proof. exact (eq_refl (term545 _93670 _93677 f x s)). Qed.
Lemma lem3657980 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term544 _93670 _93677 f x s) = (term546 _93670 _93677 x f s).
Proof. exact (TRANS (@lem3657978 _93670 _93677 f x s) (@lem3657979 _93670 _93677 x f s)). Qed.
Lemma lem3657981 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) : (term547 _93670 _93677 f x) = (term548 _93670 _93677 x f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3657980 _93670 _93677 x f s)). Qed.
Lemma lem3657982 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3657983 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) : (term549 _93670 _93677 f x) = (term550 _93670 _93677 x f).
Proof. exact (MK_COMB (@lem3657982 _93670) (@lem3657981 _93670 _93677 x f)). Qed.
Lemma lem3657984 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term551 _93670 _93677 f) = (term552 _93670 _93677 f).
Proof. exact (fun_ext (fun x : type684 _93670 => @lem3657983 _93670 _93677 x f)). Qed.
Lemma lem3657985 {_93670 : Type'} : (@ex ((_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> Prop) -> _93670))). Qed.
Lemma lem3657986 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term534 _93670 _93677 f) = (term553 _93670 _93677 f).
Proof. exact (MK_COMB (@lem3657985 _93670) (@lem3657984 _93670 _93677 f)). Qed.
Lemma lem3657987 {_93670 _93677 : Type'} (f : _93670 -> _93677) : ((term533 _93670 _93677 f) = (term534 _93670 _93677 f)) = ((term528 _93670 _93677 f) = (term553 _93670 _93677 f)).
Proof. exact (MK_COMB (@lem3657975 _93670 _93677 f) (@lem3657986 _93670 _93677 f)). Qed.
Lemma lem3657988 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term528 _93670 _93677 f) = (term553 _93670 _93677 f).
Proof. exact (EQ_MP (@lem3657987 _93670 _93677 f) (@lem3657962 _93670 _93677 f)). Qed.
Lemma lem3657990 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3657991 {_93670 : Type'} (P : type672 _93670) : (term531 _93670 P) = (term532 _93670 P).
Proof. exact (@lem3657990 (_93670 -> Prop) _93670 P). Qed.
Lemma lem3657992 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) : (term554 _93670 _93677 x f) = (term555 _93670 _93677 x f).
Proof. exact (@lem3657991 _93670 (term556 _93670 _93677 x f)). Qed.
Lemma lem3657993 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term557 _93670 _93677 x f s) = (term558 _93670 _93677 x f s).
Proof. exact (eq_refl (term557 _93670 _93677 x f s)). Qed.
Lemma lem3657994 {_93670 : Type'} (y : _93670) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3657995 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) (y : _93670) : (term559 _93670 _93677 x f s y) = (term560 _93670 _93677 x f s y).
Proof. exact (MK_COMB (@lem3657993 _93670 _93677 x f s) (@lem3657994 _93670 y)). Qed.
Lemma lem3657996 {_93670 _93677 : Type'} (x : type684 _93670) (y : _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term560 _93670 _93677 x f s y) = (term561 _93670 _93677 x y f s).
Proof. exact (eq_refl (term560 _93670 _93677 x f s y)). Qed.
Lemma lem3657997 {_93670 _93677 : Type'} (x : type684 _93670) (y : _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term559 _93670 _93677 x f s y) = (term561 _93670 _93677 x y f s).
Proof. exact (TRANS (@lem3657995 _93670 _93677 x f s y) (@lem3657996 _93670 _93677 x y f s)). Qed.
Lemma lem3657998 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term562 _93670 _93677 x f s) = (term558 _93670 _93677 x f s).
Proof. exact (fun_ext (fun y : _93670 => @lem3657997 _93670 _93677 x y f s)). Qed.
Lemma lem3657999 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3658000 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term563 _93670 _93677 x f s) = (term546 _93670 _93677 x f s).
Proof. exact (MK_COMB (@lem3657999 _93670) (@lem3657998 _93670 _93677 x f s)). Qed.
Lemma lem3658001 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) : (term564 _93670 _93677 x f) = (term548 _93670 _93677 x f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3658000 _93670 _93677 x f s)). Qed.
Lemma lem3658002 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3658003 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) : (term554 _93670 _93677 x f) = (term550 _93670 _93677 x f).
Proof. exact (MK_COMB (@lem3658002 _93670) (@lem3658001 _93670 _93677 x f)). Qed.
Lemma lem3658004 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658005 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) : (term565 _93670 _93677 x f) = (term566 _93670 _93677 x f).
Proof. exact (MK_COMB (@lem3658004) (@lem3658003 _93670 _93677 x f)). Qed.
Lemma lem3658006 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term557 _93670 _93677 x f s) = (term558 _93670 _93677 x f s).
Proof. exact (eq_refl (term557 _93670 _93677 x f s)). Qed.
Lemma lem3658007 {_93670 : Type'} (y : type684 _93670) (s : _93670 -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem3658008 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) (y : type684 _93670) (s : _93670 -> Prop) : (term567 _93670 _93677 x f y s) = (term568 _93670 _93677 x f y s).
Proof. exact (MK_COMB (@lem3658006 _93670 _93677 x f s) (@lem3658007 _93670 y s)). Qed.
Lemma lem3658009 {_93670 _93677 : Type'} (x : type684 _93670) (y : type684 _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term568 _93670 _93677 x f y s) = (term569 _93670 _93677 x y f s).
Proof. exact (eq_refl (term568 _93670 _93677 x f y s)). Qed.
Lemma lem3658010 {_93670 _93677 : Type'} (x : type684 _93670) (y : type684 _93670) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term567 _93670 _93677 x f y s) = (term569 _93670 _93677 x y f s).
Proof. exact (TRANS (@lem3658008 _93670 _93677 x f y s) (@lem3658009 _93670 _93677 x y f s)). Qed.
Lemma lem3658011 {_93670 _93677 : Type'} (x : type684 _93670) (y : type684 _93670) (f : _93670 -> _93677) : (term570 _93670 _93677 x f y) = (term571 _93670 _93677 x y f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3658010 _93670 _93677 x y f s)). Qed.
Lemma lem3658012 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3658013 {_93670 _93677 : Type'} (x : type684 _93670) (y : type684 _93670) (f : _93670 -> _93677) : (term572 _93670 _93677 x f y) = (term573 _93670 _93677 x y f).
Proof. exact (MK_COMB (@lem3658012 _93670) (@lem3658011 _93670 _93677 x y f)). Qed.
Lemma lem3658014 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) : (term574 _93670 _93677 x f) = (term575 _93670 _93677 x f).
Proof. exact (fun_ext (fun y : type684 _93670 => @lem3658013 _93670 _93677 x y f)). Qed.
Lemma lem3658015 {_93670 : Type'} : (@ex ((_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658016 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) : (term555 _93670 _93677 x f) = (term576 _93670 _93677 x f).
Proof. exact (MK_COMB (@lem3658015 _93670) (@lem3658014 _93670 _93677 x f)). Qed.
Lemma lem3658017 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) : ((term554 _93670 _93677 x f) = (term555 _93670 _93677 x f)) = ((term550 _93670 _93677 x f) = (term576 _93670 _93677 x f)).
Proof. exact (MK_COMB (@lem3658005 _93670 _93677 x f) (@lem3658016 _93670 _93677 x f)). Qed.
Lemma lem3658018 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) : (term550 _93670 _93677 x f) = (term576 _93670 _93677 x f).
Proof. exact (EQ_MP (@lem3658017 _93670 _93677 x f) (@lem3657992 _93670 _93677 x f)). Qed.
Lemma lem3658019 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term552 _93670 _93677 f) = (term577 _93670 _93677 f).
Proof. exact (fun_ext (fun x : type684 _93670 => @lem3658018 _93670 _93677 x f)). Qed.
Lemma lem3658020 {_93670 : Type'} : (@ex ((_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658021 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term553 _93670 _93677 f) = (term578 _93670 _93677 f).
Proof. exact (MK_COMB (@lem3658020 _93670) (@lem3658019 _93670 _93677 f)). Qed.
Lemma lem3658022 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term528 _93670 _93677 f) = (term578 _93670 _93677 f).
Proof. exact (TRANS (@lem3657988 _93670 _93677 f) (@lem3658021 _93670 _93677 f)). Qed.
Lemma lem3658023 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term492 _93670 _93677 f) = (term578 _93670 _93677 f).
Proof. exact (TRANS (@lem3657958 _93670 _93677 f) (@lem3658022 _93670 _93677 f)). Qed.
Lemma lem3658024 {_93670 _93677 : Type'} : (term493 _93670 _93677) = (term579 _93670 _93677).
Proof. exact (fun_ext (fun f : _93670 -> _93677 => @lem3658023 _93670 _93677 f)). Qed.
Lemma lem3658025 {_93670 _93677 : Type'} : (@all (_93670 -> _93677)) = (@all (_93670 -> _93677)).
Proof. exact (eq_refl (@all (_93670 -> _93677))). Qed.
Lemma lem3658026 {_93670 _93677 : Type'} : (term494 _93670 _93677) = (term580 _93670 _93677).
Proof. exact (MK_COMB (@lem3658025 _93670 _93677) (@lem3658024 _93670 _93677)). Qed.
Lemma lem3658028 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3658029 {_93670 _93677 : Type'} (P : type503 _93670 _93677) : (term581 _93670 _93677 P) = (term582 _93670 _93677 P).
Proof. exact (@lem3658028 (_93670 -> _93677) (type684 _93670) P). Qed.
Lemma lem3658030 {_93670 _93677 : Type'} : (term583 _93670 _93677) = (term584 _93670 _93677).
Proof. exact (@lem3658029 _93670 _93677 (term585 _93670 _93677)). Qed.
Lemma lem3658031 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term586 _93670 _93677 f) = (term577 _93670 _93677 f).
Proof. exact (eq_refl (term586 _93670 _93677 f)). Qed.
Lemma lem3658032 {_93670 : Type'} (x : type684 _93670) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3658033 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : type684 _93670) : (term587 _93670 _93677 f x) = (term588 _93670 _93677 f x).
Proof. exact (MK_COMB (@lem3658031 _93670 _93677 f) (@lem3658032 _93670 x)). Qed.
Lemma lem3658034 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) : (term588 _93670 _93677 f x) = (term576 _93670 _93677 x f).
Proof. exact (eq_refl (term588 _93670 _93677 f x)). Qed.
Lemma lem3658035 {_93670 _93677 : Type'} (x : type684 _93670) (f : _93670 -> _93677) : (term587 _93670 _93677 f x) = (term576 _93670 _93677 x f).
Proof. exact (TRANS (@lem3658033 _93670 _93677 f x) (@lem3658034 _93670 _93677 x f)). Qed.
Lemma lem3658036 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term589 _93670 _93677 f) = (term577 _93670 _93677 f).
Proof. exact (fun_ext (fun x : type684 _93670 => @lem3658035 _93670 _93677 x f)). Qed.
Lemma lem3658037 {_93670 : Type'} : (@ex ((_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658038 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term590 _93670 _93677 f) = (term578 _93670 _93677 f).
Proof. exact (MK_COMB (@lem3658037 _93670) (@lem3658036 _93670 _93677 f)). Qed.
Lemma lem3658039 {_93670 _93677 : Type'} : (term591 _93670 _93677) = (term579 _93670 _93677).
Proof. exact (fun_ext (fun f : _93670 -> _93677 => @lem3658038 _93670 _93677 f)). Qed.
Lemma lem3658040 {_93670 _93677 : Type'} : (@all (_93670 -> _93677)) = (@all (_93670 -> _93677)).
Proof. exact (eq_refl (@all (_93670 -> _93677))). Qed.
Lemma lem3658041 {_93670 _93677 : Type'} : (term583 _93670 _93677) = (term580 _93670 _93677).
Proof. exact (MK_COMB (@lem3658040 _93670 _93677) (@lem3658039 _93670 _93677)). Qed.
Lemma lem3658042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658043 {_93670 _93677 : Type'} : (term592 _93670 _93677) = (term593 _93670 _93677).
Proof. exact (MK_COMB (@lem3658042) (@lem3658041 _93670 _93677)). Qed.
Lemma lem3658044 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (term586 _93670 _93677 f) = (term577 _93670 _93677 f).
Proof. exact (eq_refl (term586 _93670 _93677 f)). Qed.
Lemma lem3658045 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (f : _93670 -> _93677) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem3658046 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (f : _93670 -> _93677) : (term594 _93670 _93677 x f) = (term595 _93670 _93677 x f).
Proof. exact (MK_COMB (@lem3658044 _93670 _93677 f) (@lem3658045 _93670 _93677 x f)). Qed.
Lemma lem3658047 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (f : _93670 -> _93677) : (term595 _93670 _93677 x f) = (term596 _93670 _93677 x f).
Proof. exact (eq_refl (term595 _93670 _93677 x f)). Qed.
Lemma lem3658048 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (f : _93670 -> _93677) : (term594 _93670 _93677 x f) = (term596 _93670 _93677 x f).
Proof. exact (TRANS (@lem3658046 _93670 _93677 x f) (@lem3658047 _93670 _93677 x f)). Qed.
Lemma lem3658049 {_93670 _93677 : Type'} (x : type529 _93670 _93677) : (term597 _93670 _93677 x) = (term598 _93670 _93677 x).
Proof. exact (fun_ext (fun f : _93670 -> _93677 => @lem3658048 _93670 _93677 x f)). Qed.
Lemma lem3658050 {_93670 _93677 : Type'} : (@all (_93670 -> _93677)) = (@all (_93670 -> _93677)).
Proof. exact (eq_refl (@all (_93670 -> _93677))). Qed.
Lemma lem3658051 {_93670 _93677 : Type'} (x : type529 _93670 _93677) : (term599 _93670 _93677 x) = (term600 _93670 _93677 x).
Proof. exact (MK_COMB (@lem3658050 _93670 _93677) (@lem3658049 _93670 _93677 x)). Qed.
Lemma lem3658052 {_93670 _93677 : Type'} : (term601 _93670 _93677) = (term602 _93670 _93677).
Proof. exact (fun_ext (fun x : type529 _93670 _93677 => @lem3658051 _93670 _93677 x)). Qed.
Lemma lem3658053 {_93670 _93677 : Type'} : (@ex ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658054 {_93670 _93677 : Type'} : (term584 _93670 _93677) = (term603 _93670 _93677).
Proof. exact (MK_COMB (@lem3658053 _93670 _93677) (@lem3658052 _93670 _93677)). Qed.
Lemma lem3658055 {_93670 _93677 : Type'} : ((term583 _93670 _93677) = (term584 _93670 _93677)) = ((term580 _93670 _93677) = (term603 _93670 _93677)).
Proof. exact (MK_COMB (@lem3658043 _93670 _93677) (@lem3658054 _93670 _93677)). Qed.
Lemma lem3658056 {_93670 _93677 : Type'} : (term580 _93670 _93677) = (term603 _93670 _93677).
Proof. exact (EQ_MP (@lem3658055 _93670 _93677) (@lem3658030 _93670 _93677)). Qed.
Lemma lem3658058 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3658059 {_93670 _93677 : Type'} (P : type503 _93670 _93677) : (term581 _93670 _93677 P) = (term582 _93670 _93677 P).
Proof. exact (@lem3658058 (_93670 -> _93677) (type684 _93670) P). Qed.
Lemma lem3658060 {_93670 _93677 : Type'} (x : type529 _93670 _93677) : (term604 _93670 _93677 x) = (term605 _93670 _93677 x).
Proof. exact (@lem3658059 _93670 _93677 (term606 _93670 _93677 x)). Qed.
Lemma lem3658061 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (f : _93670 -> _93677) : (term607 _93670 _93677 x f) = (term608 _93670 _93677 x f).
Proof. exact (eq_refl (term607 _93670 _93677 x f)). Qed.
Lemma lem3658062 {_93670 : Type'} (y : type684 _93670) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3658063 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (f : _93670 -> _93677) (y : type684 _93670) : (term609 _93670 _93677 x f y) = (term610 _93670 _93677 x f y).
Proof. exact (MK_COMB (@lem3658061 _93670 _93677 x f) (@lem3658062 _93670 y)). Qed.
Lemma lem3658064 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (y : type684 _93670) (f : _93670 -> _93677) : (term610 _93670 _93677 x f y) = (term611 _93670 _93677 x y f).
Proof. exact (eq_refl (term610 _93670 _93677 x f y)). Qed.
Lemma lem3658065 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (y : type684 _93670) (f : _93670 -> _93677) : (term609 _93670 _93677 x f y) = (term611 _93670 _93677 x y f).
Proof. exact (TRANS (@lem3658063 _93670 _93677 x f y) (@lem3658064 _93670 _93677 x y f)). Qed.
Lemma lem3658066 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (f : _93670 -> _93677) : (term612 _93670 _93677 x f) = (term608 _93670 _93677 x f).
Proof. exact (fun_ext (fun y : type684 _93670 => @lem3658065 _93670 _93677 x y f)). Qed.
Lemma lem3658067 {_93670 : Type'} : (@ex ((_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658068 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (f : _93670 -> _93677) : (term613 _93670 _93677 x f) = (term596 _93670 _93677 x f).
Proof. exact (MK_COMB (@lem3658067 _93670) (@lem3658066 _93670 _93677 x f)). Qed.
Lemma lem3658069 {_93670 _93677 : Type'} (x : type529 _93670 _93677) : (term614 _93670 _93677 x) = (term598 _93670 _93677 x).
Proof. exact (fun_ext (fun f : _93670 -> _93677 => @lem3658068 _93670 _93677 x f)). Qed.
Lemma lem3658070 {_93670 _93677 : Type'} : (@all (_93670 -> _93677)) = (@all (_93670 -> _93677)).
Proof. exact (eq_refl (@all (_93670 -> _93677))). Qed.
Lemma lem3658071 {_93670 _93677 : Type'} (x : type529 _93670 _93677) : (term604 _93670 _93677 x) = (term600 _93670 _93677 x).
Proof. exact (MK_COMB (@lem3658070 _93670 _93677) (@lem3658069 _93670 _93677 x)). Qed.
Lemma lem3658072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658073 {_93670 _93677 : Type'} (x : type529 _93670 _93677) : (term615 _93670 _93677 x) = (term616 _93670 _93677 x).
Proof. exact (MK_COMB (@lem3658072) (@lem3658071 _93670 _93677 x)). Qed.
Lemma lem3658074 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (f : _93670 -> _93677) : (term607 _93670 _93677 x f) = (term608 _93670 _93677 x f).
Proof. exact (eq_refl (term607 _93670 _93677 x f)). Qed.
Lemma lem3658075 {_93670 _93677 : Type'} (y : type529 _93670 _93677) (f : _93670 -> _93677) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem3658076 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (y : type529 _93670 _93677) (f : _93670 -> _93677) : (term617 _93670 _93677 x y f) = (term618 _93670 _93677 x y f).
Proof. exact (MK_COMB (@lem3658074 _93670 _93677 x f) (@lem3658075 _93670 _93677 y f)). Qed.
Lemma lem3658077 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (y : type529 _93670 _93677) (f : _93670 -> _93677) : (term618 _93670 _93677 x y f) = (term619 _93670 _93677 x y f).
Proof. exact (eq_refl (term618 _93670 _93677 x y f)). Qed.
Lemma lem3658078 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (y : type529 _93670 _93677) (f : _93670 -> _93677) : (term617 _93670 _93677 x y f) = (term619 _93670 _93677 x y f).
Proof. exact (TRANS (@lem3658076 _93670 _93677 x y f) (@lem3658077 _93670 _93677 x y f)). Qed.
Lemma lem3658079 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (y : type529 _93670 _93677) : (term620 _93670 _93677 x y) = (term621 _93670 _93677 x y).
Proof. exact (fun_ext (fun f : _93670 -> _93677 => @lem3658078 _93670 _93677 x y f)). Qed.
Lemma lem3658080 {_93670 _93677 : Type'} : (@all (_93670 -> _93677)) = (@all (_93670 -> _93677)).
Proof. exact (eq_refl (@all (_93670 -> _93677))). Qed.
Lemma lem3658081 {_93670 _93677 : Type'} (x : type529 _93670 _93677) (y : type529 _93670 _93677) : (term622 _93670 _93677 x y) = (term623 _93670 _93677 x y).
Proof. exact (MK_COMB (@lem3658080 _93670 _93677) (@lem3658079 _93670 _93677 x y)). Qed.
Lemma lem3658082 {_93670 _93677 : Type'} (x : type529 _93670 _93677) : (term624 _93670 _93677 x) = (term625 _93670 _93677 x).
Proof. exact (fun_ext (fun y : type529 _93670 _93677 => @lem3658081 _93670 _93677 x y)). Qed.
Lemma lem3658083 {_93670 _93677 : Type'} : (@ex ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658084 {_93670 _93677 : Type'} (x : type529 _93670 _93677) : (term605 _93670 _93677 x) = (term626 _93670 _93677 x).
Proof. exact (MK_COMB (@lem3658083 _93670 _93677) (@lem3658082 _93670 _93677 x)). Qed.
Lemma lem3658085 {_93670 _93677 : Type'} (x : type529 _93670 _93677) : ((term604 _93670 _93677 x) = (term605 _93670 _93677 x)) = ((term600 _93670 _93677 x) = (term626 _93670 _93677 x)).
Proof. exact (MK_COMB (@lem3658073 _93670 _93677 x) (@lem3658084 _93670 _93677 x)). Qed.
Lemma lem3658086 {_93670 _93677 : Type'} (x : type529 _93670 _93677) : (term600 _93670 _93677 x) = (term626 _93670 _93677 x).
Proof. exact (EQ_MP (@lem3658085 _93670 _93677 x) (@lem3658060 _93670 _93677 x)). Qed.
Lemma lem3658087 {_93670 _93677 : Type'} : (term602 _93670 _93677) = (term627 _93670 _93677).
Proof. exact (fun_ext (fun x : type529 _93670 _93677 => @lem3658086 _93670 _93677 x)). Qed.
Lemma lem3658088 {_93670 _93677 : Type'} : (@ex ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658089 {_93670 _93677 : Type'} : (term603 _93670 _93677) = (term628 _93670 _93677).
Proof. exact (MK_COMB (@lem3658088 _93670 _93677) (@lem3658087 _93670 _93677)). Qed.
Lemma lem3658090 {_93670 _93677 : Type'} : (term580 _93670 _93677) = (term628 _93670 _93677).
Proof. exact (TRANS (@lem3658056 _93670 _93677) (@lem3658089 _93670 _93677)). Qed.
Lemma lem3658092 {_93670 _93677 : Type'} : (term494 _93670 _93677) = (term628 _93670 _93677).
Proof. exact (TRANS (@lem3658026 _93670 _93677) (@lem3658090 _93670 _93677)). Qed.
Lemma lem3658093 {_93670 _93677 : Type'} : (term82 _93670 _93677) = (term628 _93670 _93677).
Proof. exact (TRANS (@lem3657798 _93670 _93677) (@lem3658092 _93670 _93677)). Qed.
Lemma lem3658094 {_93670 _93677 : Type'} (h1 : term82 _93670 _93677) : term628 _93670 _93677.
Proof. exact (EQ_MP (@lem3658093 _93670 _93677) (@lem3656891 _93670 _93677 h1)). Qed.
Lemma lem3658109 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) (y : _93670) : (term469 _93670 B s f x y) = (term470 _93670 B s f x y).
Proof. exact (@lem17362 (term471 _93670 B s x f y) (x = y)). Qed.
Lemma lem3658110 {_93670 : Type'} (P : _93670 -> Prop) : (term163 _93670 P) = (term164 _93670 P).
Proof. exact (@lem18392 _93670 P). Qed.
Lemma lem3658111 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term472 _93670 B s f x) = (term473 _93670 B s f x).
Proof. exact (@lem3658110 _93670 (term131 _93670 B s f x)). Qed.
Lemma lem3658112 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) (y : _93670) : (term474 _93670 B s f x y) = (term130 _93670 B s f x y).
Proof. exact (eq_refl (term474 _93670 B s f x y)). Qed.
Lemma lem3658113 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3658114 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) (y : _93670) : (term475 _93670 B s f x y) = (term469 _93670 B s f x y).
Proof. exact (MK_COMB (@lem3658113) (@lem3658112 _93670 B s f x y)). Qed.
Lemma lem3658115 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) (y : _93670) : (term475 _93670 B s f x y) = (term470 _93670 B s f x y).
Proof. exact (TRANS (@lem3658114 _93670 B s f x y) (@lem3658109 _93670 B s f x y)). Qed.
Lemma lem3658116 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term476 _93670 B s f x) = (term477 _93670 B s f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3658115 _93670 B s f x y)). Qed.
Lemma lem3658117 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3658118 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term473 _93670 B s f x) = (term478 _93670 B s f x).
Proof. exact (MK_COMB (@lem3658117 _93670) (@lem3658116 _93670 B s f x)). Qed.
Lemma lem3658119 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term472 _93670 B s f x) = (term478 _93670 B s f x).
Proof. exact (TRANS (@lem3658111 _93670 B s f x) (@lem3658118 _93670 B s f x)). Qed.
Lemma lem3658120 {_93670 : Type'} (P : _93670 -> Prop) : (term163 _93670 P) = (term164 _93670 P).
Proof. exact (@lem18392 _93670 P). Qed.
Lemma lem3658121 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) : (term479 _93670 B s f) = (term480 _93670 B s f).
Proof. exact (@lem3658120 _93670 (term133 _93670 B s f)). Qed.
Lemma lem3658122 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term481 _93670 B s f x) = (term132 _93670 B s f x).
Proof. exact (eq_refl (term481 _93670 B s f x)). Qed.
Lemma lem3658123 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3658124 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term482 _93670 B s f x) = (term472 _93670 B s f x).
Proof. exact (MK_COMB (@lem3658123) (@lem3658122 _93670 B s f x)). Qed.
Lemma lem3658125 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term482 _93670 B s f x) = (term478 _93670 B s f x).
Proof. exact (TRANS (@lem3658124 _93670 B s f x) (@lem3658119 _93670 B s f x)). Qed.
Lemma lem3658126 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) : (term483 _93670 B s f) = (term484 _93670 B s f).
Proof. exact (fun_ext (fun x : _93670 => @lem3658125 _93670 B s f x)). Qed.
Lemma lem3658127 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3658128 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) : (term480 _93670 B s f) = (term485 _93670 B s f).
Proof. exact (MK_COMB (@lem3658127 _93670) (@lem3658126 _93670 B s f)). Qed.
Lemma lem3658129 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) : (term479 _93670 B s f) = (term485 _93670 B s f).
Proof. exact (TRANS (@lem3658121 _93670 B s f) (@lem3658128 _93670 B s f)). Qed.
Lemma lem3658144 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : ((term129 _93670 B f s) = (@FINITE _93670 s)) = (term486 _93670 B f s).
Proof. exact (@lem17784 (term129 _93670 B f s) (@FINITE _93670 s)). Qed.
Lemma lem3658145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3658146 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) : (term487 _93670 B s f) = (term488 _93670 B s f).
Proof. exact (MK_COMB (@lem3658145) (@lem3658129 _93670 B s f)). Qed.
Lemma lem3658147 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term489 _93670 B f s) = (term490 _93670 B f s).
Proof. exact (MK_COMB (@lem3658146 _93670 B s f) (@lem3658144 _93670 B f s)). Qed.
Lemma lem3658148 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term136 _93670 B f s) = (term489 _93670 B f s).
Proof. exact (@lem17265 (term134 _93670 B s f) ((term129 _93670 B f s) = (@FINITE _93670 s))). Qed.
Lemma lem3658149 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term136 _93670 B f s) = (term490 _93670 B f s).
Proof. exact (TRANS (@lem3658148 _93670 B f s) (@lem3658147 _93670 B f s)). Qed.
Lemma lem3658150 {_93670 B : Type'} (f : _93670 -> B) : (term137 _93670 B f) = (term491 _93670 B f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3658149 _93670 B f s)). Qed.
Lemma lem3658151 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3658152 {_93670 B : Type'} (f : _93670 -> B) : (term138 _93670 B f) = (term492 _93670 B f).
Proof. exact (MK_COMB (@lem3658151 _93670) (@lem3658150 _93670 B f)). Qed.
Lemma lem3658153 {_93670 B : Type'} : (term139 _93670 B) = (term493 _93670 B).
Proof. exact (fun_ext (fun f : _93670 -> B => @lem3658152 _93670 B f)). Qed.
Lemma lem3658154 {_93670 B : Type'} : (@all (_93670 -> B)) = (@all (_93670 -> B)).
Proof. exact (eq_refl (@all (_93670 -> B))). Qed.
Lemma lem3658155 {_93670 B : Type'} : (term82 _93670 B) = (term494 _93670 B).
Proof. exact (MK_COMB (@lem3658154 _93670 B) (@lem3658153 _93670 B)). Qed.
Lemma lem3658262 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3658263 {_93670 : Type'} (P : _93670 -> Prop) (Q : Prop) : (term223 _93670 P Q) = (term224 _93670 P Q).
Proof. exact (@lem3658262 _93670 P Q). Qed.
Lemma lem3658264 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term495 _93670 B f s) = (term496 _93670 B f s).
Proof. exact (@lem3658263 _93670 (term484 _93670 B s f) (term486 _93670 B f s)). Qed.
Lemma lem3658265 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term497 _93670 B s f x) = (term478 _93670 B s f x).
Proof. exact (eq_refl (term497 _93670 B s f x)). Qed.
Lemma lem3658266 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) : (term498 _93670 B s f) = (term484 _93670 B s f).
Proof. exact (fun_ext (fun x : _93670 => @lem3658265 _93670 B s f x)). Qed.
Lemma lem3658267 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3658268 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) : (term499 _93670 B s f) = (term485 _93670 B s f).
Proof. exact (MK_COMB (@lem3658267 _93670) (@lem3658266 _93670 B s f)). Qed.
Lemma lem3658269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3658270 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) : (term500 _93670 B s f) = (term488 _93670 B s f).
Proof. exact (MK_COMB (@lem3658269) (@lem3658268 _93670 B s f)). Qed.
Lemma lem3658271 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term486 _93670 B f s) = (term486 _93670 B f s).
Proof. exact (eq_refl (term486 _93670 B f s)). Qed.
Lemma lem3658272 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term495 _93670 B f s) = (term490 _93670 B f s).
Proof. exact (MK_COMB (@lem3658270 _93670 B s f) (@lem3658271 _93670 B f s)). Qed.
Lemma lem3658273 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658274 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term501 _93670 B f s) = (term502 _93670 B f s).
Proof. exact (MK_COMB (@lem3658273) (@lem3658272 _93670 B f s)). Qed.
Lemma lem3658275 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term497 _93670 B s f x) = (term478 _93670 B s f x).
Proof. exact (eq_refl (term497 _93670 B s f x)). Qed.
Lemma lem3658276 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3658277 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term503 _93670 B s f x) = (term504 _93670 B s f x).
Proof. exact (MK_COMB (@lem3658276) (@lem3658275 _93670 B s f x)). Qed.
Lemma lem3658278 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term486 _93670 B f s) = (term486 _93670 B f s).
Proof. exact (eq_refl (term486 _93670 B f s)). Qed.
Lemma lem3658279 {_93670 B : Type'} (x : _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term505 _93670 B x f s) = (term506 _93670 B x f s).
Proof. exact (MK_COMB (@lem3658277 _93670 B s f x) (@lem3658278 _93670 B f s)). Qed.
Lemma lem3658280 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term507 _93670 B f s) = (term508 _93670 B f s).
Proof. exact (fun_ext (fun x : _93670 => @lem3658279 _93670 B x f s)). Qed.
Lemma lem3658281 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3658282 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term496 _93670 B f s) = (term509 _93670 B f s).
Proof. exact (MK_COMB (@lem3658281 _93670) (@lem3658280 _93670 B f s)). Qed.
Lemma lem3658283 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : ((term495 _93670 B f s) = (term496 _93670 B f s)) = ((term490 _93670 B f s) = (term509 _93670 B f s)).
Proof. exact (MK_COMB (@lem3658274 _93670 B f s) (@lem3658282 _93670 B f s)). Qed.
Lemma lem3658284 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term490 _93670 B f s) = (term509 _93670 B f s).
Proof. exact (EQ_MP (@lem3658283 _93670 B f s) (@lem3658264 _93670 B f s)). Qed.
Lemma lem3658286 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3658287 {_93670 : Type'} (P : _93670 -> Prop) (Q : Prop) : (term223 _93670 P Q) = (term224 _93670 P Q).
Proof. exact (@lem3658286 _93670 P Q). Qed.
Lemma lem3658288 {_93670 B : Type'} (x : _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term510 _93670 B x f s) = (term511 _93670 B x f s).
Proof. exact (@lem3658287 _93670 (term477 _93670 B s f x) (term486 _93670 B f s)). Qed.
Lemma lem3658289 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) (y : _93670) : (term512 _93670 B s f x y) = (term470 _93670 B s f x y).
Proof. exact (eq_refl (term512 _93670 B s f x y)). Qed.
Lemma lem3658290 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term513 _93670 B s f x) = (term477 _93670 B s f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3658289 _93670 B s f x y)). Qed.
Lemma lem3658291 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3658292 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term514 _93670 B s f x) = (term478 _93670 B s f x).
Proof. exact (MK_COMB (@lem3658291 _93670) (@lem3658290 _93670 B s f x)). Qed.
Lemma lem3658293 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3658294 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) : (term515 _93670 B s f x) = (term504 _93670 B s f x).
Proof. exact (MK_COMB (@lem3658293) (@lem3658292 _93670 B s f x)). Qed.
Lemma lem3658295 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term486 _93670 B f s) = (term486 _93670 B f s).
Proof. exact (eq_refl (term486 _93670 B f s)). Qed.
Lemma lem3658296 {_93670 B : Type'} (x : _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term510 _93670 B x f s) = (term506 _93670 B x f s).
Proof. exact (MK_COMB (@lem3658294 _93670 B s f x) (@lem3658295 _93670 B f s)). Qed.
Lemma lem3658297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658298 {_93670 B : Type'} (x : _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term516 _93670 B x f s) = (term517 _93670 B x f s).
Proof. exact (MK_COMB (@lem3658297) (@lem3658296 _93670 B x f s)). Qed.
Lemma lem3658299 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) (y : _93670) : (term512 _93670 B s f x y) = (term470 _93670 B s f x y).
Proof. exact (eq_refl (term512 _93670 B s f x y)). Qed.
Lemma lem3658300 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3658301 {_93670 B : Type'} (s : _93670 -> Prop) (f : _93670 -> B) (x : _93670) (y : _93670) : (term518 _93670 B s f x y) = (term519 _93670 B s f x y).
Proof. exact (MK_COMB (@lem3658300) (@lem3658299 _93670 B s f x y)). Qed.
Lemma lem3658302 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term486 _93670 B f s) = (term486 _93670 B f s).
Proof. exact (eq_refl (term486 _93670 B f s)). Qed.
Lemma lem3658303 {_93670 B : Type'} (x : _93670) (y : _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term520 _93670 B x y f s) = (term521 _93670 B x y f s).
Proof. exact (MK_COMB (@lem3658301 _93670 B s f x y) (@lem3658302 _93670 B f s)). Qed.
Lemma lem3658304 {_93670 B : Type'} (x : _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term522 _93670 B x f s) = (term523 _93670 B x f s).
Proof. exact (fun_ext (fun y : _93670 => @lem3658303 _93670 B x y f s)). Qed.
Lemma lem3658305 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3658306 {_93670 B : Type'} (x : _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term511 _93670 B x f s) = (term524 _93670 B x f s).
Proof. exact (MK_COMB (@lem3658305 _93670) (@lem3658304 _93670 B x f s)). Qed.
Lemma lem3658307 {_93670 B : Type'} (x : _93670) (f : _93670 -> B) (s : _93670 -> Prop) : ((term510 _93670 B x f s) = (term511 _93670 B x f s)) = ((term506 _93670 B x f s) = (term524 _93670 B x f s)).
Proof. exact (MK_COMB (@lem3658298 _93670 B x f s) (@lem3658306 _93670 B x f s)). Qed.
Lemma lem3658308 {_93670 B : Type'} (x : _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term506 _93670 B x f s) = (term524 _93670 B x f s).
Proof. exact (EQ_MP (@lem3658307 _93670 B x f s) (@lem3658288 _93670 B x f s)). Qed.
Lemma lem3658309 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term508 _93670 B f s) = (term525 _93670 B f s).
Proof. exact (fun_ext (fun x : _93670 => @lem3658308 _93670 B x f s)). Qed.
Lemma lem3658310 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3658311 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term509 _93670 B f s) = (term526 _93670 B f s).
Proof. exact (MK_COMB (@lem3658310 _93670) (@lem3658309 _93670 B f s)). Qed.
Lemma lem3658312 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term490 _93670 B f s) = (term526 _93670 B f s).
Proof. exact (TRANS (@lem3658284 _93670 B f s) (@lem3658311 _93670 B f s)). Qed.
Lemma lem3658313 {_93670 B : Type'} (f : _93670 -> B) : (term491 _93670 B f) = (term527 _93670 B f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3658312 _93670 B f s)). Qed.
Lemma lem3658314 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3658315 {_93670 B : Type'} (f : _93670 -> B) : (term492 _93670 B f) = (term528 _93670 B f).
Proof. exact (MK_COMB (@lem3658314 _93670) (@lem3658313 _93670 B f)). Qed.
Lemma lem3658317 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3658318 {_93670 : Type'} (P : type672 _93670) : (term531 _93670 P) = (term532 _93670 P).
Proof. exact (@lem3658317 (_93670 -> Prop) _93670 P). Qed.
Lemma lem3658319 {_93670 B : Type'} (f : _93670 -> B) : (term533 _93670 B f) = (term534 _93670 B f).
Proof. exact (@lem3658318 _93670 (term535 _93670 B f)). Qed.
Lemma lem3658320 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term536 _93670 B f s) = (term525 _93670 B f s).
Proof. exact (eq_refl (term536 _93670 B f s)). Qed.
Lemma lem3658321 {_93670 : Type'} (x : _93670) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3658322 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) (x : _93670) : (term537 _93670 B f s x) = (term538 _93670 B f s x).
Proof. exact (MK_COMB (@lem3658320 _93670 B f s) (@lem3658321 _93670 x)). Qed.
Lemma lem3658323 {_93670 B : Type'} (x : _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term538 _93670 B f s x) = (term524 _93670 B x f s).
Proof. exact (eq_refl (term538 _93670 B f s x)). Qed.
Lemma lem3658324 {_93670 B : Type'} (x : _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term537 _93670 B f s x) = (term524 _93670 B x f s).
Proof. exact (TRANS (@lem3658322 _93670 B f s x) (@lem3658323 _93670 B x f s)). Qed.
Lemma lem3658325 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term539 _93670 B f s) = (term525 _93670 B f s).
Proof. exact (fun_ext (fun x : _93670 => @lem3658324 _93670 B x f s)). Qed.
Lemma lem3658326 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3658327 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term540 _93670 B f s) = (term526 _93670 B f s).
Proof. exact (MK_COMB (@lem3658326 _93670) (@lem3658325 _93670 B f s)). Qed.
Lemma lem3658328 {_93670 B : Type'} (f : _93670 -> B) : (term541 _93670 B f) = (term527 _93670 B f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3658327 _93670 B f s)). Qed.
Lemma lem3658329 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3658330 {_93670 B : Type'} (f : _93670 -> B) : (term533 _93670 B f) = (term528 _93670 B f).
Proof. exact (MK_COMB (@lem3658329 _93670) (@lem3658328 _93670 B f)). Qed.
Lemma lem3658331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658332 {_93670 B : Type'} (f : _93670 -> B) : (term542 _93670 B f) = (term543 _93670 B f).
Proof. exact (MK_COMB (@lem3658331) (@lem3658330 _93670 B f)). Qed.
Lemma lem3658333 {_93670 B : Type'} (f : _93670 -> B) (s : _93670 -> Prop) : (term536 _93670 B f s) = (term525 _93670 B f s).
Proof. exact (eq_refl (term536 _93670 B f s)). Qed.
Lemma lem3658334 {_93670 : Type'} (x : type684 _93670) (s : _93670 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3658335 {_93670 B : Type'} (f : _93670 -> B) (x : type684 _93670) (s : _93670 -> Prop) : (term544 _93670 B f x s) = (term545 _93670 B f x s).
Proof. exact (MK_COMB (@lem3658333 _93670 B f s) (@lem3658334 _93670 x s)). Qed.
Lemma lem3658336 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term545 _93670 B f x s) = (term546 _93670 B x f s).
Proof. exact (eq_refl (term545 _93670 B f x s)). Qed.
Lemma lem3658337 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term544 _93670 B f x s) = (term546 _93670 B x f s).
Proof. exact (TRANS (@lem3658335 _93670 B f x s) (@lem3658336 _93670 B x f s)). Qed.
Lemma lem3658338 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) : (term547 _93670 B f x) = (term548 _93670 B x f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3658337 _93670 B x f s)). Qed.
Lemma lem3658339 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3658340 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) : (term549 _93670 B f x) = (term550 _93670 B x f).
Proof. exact (MK_COMB (@lem3658339 _93670) (@lem3658338 _93670 B x f)). Qed.
Lemma lem3658341 {_93670 B : Type'} (f : _93670 -> B) : (term551 _93670 B f) = (term552 _93670 B f).
Proof. exact (fun_ext (fun x : type684 _93670 => @lem3658340 _93670 B x f)). Qed.
Lemma lem3658342 {_93670 : Type'} : (@ex ((_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658343 {_93670 B : Type'} (f : _93670 -> B) : (term534 _93670 B f) = (term553 _93670 B f).
Proof. exact (MK_COMB (@lem3658342 _93670) (@lem3658341 _93670 B f)). Qed.
Lemma lem3658344 {_93670 B : Type'} (f : _93670 -> B) : ((term533 _93670 B f) = (term534 _93670 B f)) = ((term528 _93670 B f) = (term553 _93670 B f)).
Proof. exact (MK_COMB (@lem3658332 _93670 B f) (@lem3658343 _93670 B f)). Qed.
Lemma lem3658345 {_93670 B : Type'} (f : _93670 -> B) : (term528 _93670 B f) = (term553 _93670 B f).
Proof. exact (EQ_MP (@lem3658344 _93670 B f) (@lem3658319 _93670 B f)). Qed.
Lemma lem3658347 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3658348 {_93670 : Type'} (P : type672 _93670) : (term531 _93670 P) = (term532 _93670 P).
Proof. exact (@lem3658347 (_93670 -> Prop) _93670 P). Qed.
Lemma lem3658349 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) : (term554 _93670 B x f) = (term555 _93670 B x f).
Proof. exact (@lem3658348 _93670 (term556 _93670 B x f)). Qed.
Lemma lem3658350 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term557 _93670 B x f s) = (term558 _93670 B x f s).
Proof. exact (eq_refl (term557 _93670 B x f s)). Qed.
Lemma lem3658351 {_93670 : Type'} (y : _93670) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3658352 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) (s : _93670 -> Prop) (y : _93670) : (term559 _93670 B x f s y) = (term560 _93670 B x f s y).
Proof. exact (MK_COMB (@lem3658350 _93670 B x f s) (@lem3658351 _93670 y)). Qed.
Lemma lem3658353 {_93670 B : Type'} (x : type684 _93670) (y : _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term560 _93670 B x f s y) = (term561 _93670 B x y f s).
Proof. exact (eq_refl (term560 _93670 B x f s y)). Qed.
Lemma lem3658354 {_93670 B : Type'} (x : type684 _93670) (y : _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term559 _93670 B x f s y) = (term561 _93670 B x y f s).
Proof. exact (TRANS (@lem3658352 _93670 B x f s y) (@lem3658353 _93670 B x y f s)). Qed.
Lemma lem3658355 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term562 _93670 B x f s) = (term558 _93670 B x f s).
Proof. exact (fun_ext (fun y : _93670 => @lem3658354 _93670 B x y f s)). Qed.
Lemma lem3658356 {_93670 : Type'} : (@ex _93670) = (@ex _93670).
Proof. exact (eq_refl (@ex _93670)). Qed.
Lemma lem3658357 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term563 _93670 B x f s) = (term546 _93670 B x f s).
Proof. exact (MK_COMB (@lem3658356 _93670) (@lem3658355 _93670 B x f s)). Qed.
Lemma lem3658358 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) : (term564 _93670 B x f) = (term548 _93670 B x f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3658357 _93670 B x f s)). Qed.
Lemma lem3658359 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3658360 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) : (term554 _93670 B x f) = (term550 _93670 B x f).
Proof. exact (MK_COMB (@lem3658359 _93670) (@lem3658358 _93670 B x f)). Qed.
Lemma lem3658361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658362 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) : (term565 _93670 B x f) = (term566 _93670 B x f).
Proof. exact (MK_COMB (@lem3658361) (@lem3658360 _93670 B x f)). Qed.
Lemma lem3658363 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term557 _93670 B x f s) = (term558 _93670 B x f s).
Proof. exact (eq_refl (term557 _93670 B x f s)). Qed.
Lemma lem3658364 {_93670 : Type'} (y : type684 _93670) (s : _93670 -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem3658365 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) (y : type684 _93670) (s : _93670 -> Prop) : (term567 _93670 B x f y s) = (term568 _93670 B x f y s).
Proof. exact (MK_COMB (@lem3658363 _93670 B x f s) (@lem3658364 _93670 y s)). Qed.
Lemma lem3658366 {_93670 B : Type'} (x : type684 _93670) (y : type684 _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term568 _93670 B x f y s) = (term569 _93670 B x y f s).
Proof. exact (eq_refl (term568 _93670 B x f y s)). Qed.
Lemma lem3658367 {_93670 B : Type'} (x : type684 _93670) (y : type684 _93670) (f : _93670 -> B) (s : _93670 -> Prop) : (term567 _93670 B x f y s) = (term569 _93670 B x y f s).
Proof. exact (TRANS (@lem3658365 _93670 B x f y s) (@lem3658366 _93670 B x y f s)). Qed.
Lemma lem3658368 {_93670 B : Type'} (x : type684 _93670) (y : type684 _93670) (f : _93670 -> B) : (term570 _93670 B x f y) = (term571 _93670 B x y f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3658367 _93670 B x y f s)). Qed.
Lemma lem3658369 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3658370 {_93670 B : Type'} (x : type684 _93670) (y : type684 _93670) (f : _93670 -> B) : (term572 _93670 B x f y) = (term573 _93670 B x y f).
Proof. exact (MK_COMB (@lem3658369 _93670) (@lem3658368 _93670 B x y f)). Qed.
Lemma lem3658371 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) : (term574 _93670 B x f) = (term575 _93670 B x f).
Proof. exact (fun_ext (fun y : type684 _93670 => @lem3658370 _93670 B x y f)). Qed.
Lemma lem3658372 {_93670 : Type'} : (@ex ((_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658373 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) : (term555 _93670 B x f) = (term576 _93670 B x f).
Proof. exact (MK_COMB (@lem3658372 _93670) (@lem3658371 _93670 B x f)). Qed.
Lemma lem3658374 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) : ((term554 _93670 B x f) = (term555 _93670 B x f)) = ((term550 _93670 B x f) = (term576 _93670 B x f)).
Proof. exact (MK_COMB (@lem3658362 _93670 B x f) (@lem3658373 _93670 B x f)). Qed.
Lemma lem3658375 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) : (term550 _93670 B x f) = (term576 _93670 B x f).
Proof. exact (EQ_MP (@lem3658374 _93670 B x f) (@lem3658349 _93670 B x f)). Qed.
Lemma lem3658376 {_93670 B : Type'} (f : _93670 -> B) : (term552 _93670 B f) = (term577 _93670 B f).
Proof. exact (fun_ext (fun x : type684 _93670 => @lem3658375 _93670 B x f)). Qed.
Lemma lem3658377 {_93670 : Type'} : (@ex ((_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658378 {_93670 B : Type'} (f : _93670 -> B) : (term553 _93670 B f) = (term578 _93670 B f).
Proof. exact (MK_COMB (@lem3658377 _93670) (@lem3658376 _93670 B f)). Qed.
Lemma lem3658379 {_93670 B : Type'} (f : _93670 -> B) : (term528 _93670 B f) = (term578 _93670 B f).
Proof. exact (TRANS (@lem3658345 _93670 B f) (@lem3658378 _93670 B f)). Qed.
Lemma lem3658380 {_93670 B : Type'} (f : _93670 -> B) : (term492 _93670 B f) = (term578 _93670 B f).
Proof. exact (TRANS (@lem3658315 _93670 B f) (@lem3658379 _93670 B f)). Qed.
Lemma lem3658381 {_93670 B : Type'} : (term493 _93670 B) = (term579 _93670 B).
Proof. exact (fun_ext (fun f : _93670 -> B => @lem3658380 _93670 B f)). Qed.
Lemma lem3658382 {_93670 B : Type'} : (@all (_93670 -> B)) = (@all (_93670 -> B)).
Proof. exact (eq_refl (@all (_93670 -> B))). Qed.
Lemma lem3658383 {_93670 B : Type'} : (term494 _93670 B) = (term580 _93670 B).
Proof. exact (MK_COMB (@lem3658382 _93670 B) (@lem3658381 _93670 B)). Qed.
Lemma lem3658385 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3658386 {_93670 B : Type'} (P : type503 _93670 B) : (term581 _93670 B P) = (term582 _93670 B P).
Proof. exact (@lem3658385 (_93670 -> B) (type684 _93670) P). Qed.
Lemma lem3658387 {_93670 B : Type'} : (term583 _93670 B) = (term584 _93670 B).
Proof. exact (@lem3658386 _93670 B (term585 _93670 B)). Qed.
Lemma lem3658388 {_93670 B : Type'} (f : _93670 -> B) : (term586 _93670 B f) = (term577 _93670 B f).
Proof. exact (eq_refl (term586 _93670 B f)). Qed.
Lemma lem3658389 {_93670 : Type'} (x : type684 _93670) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3658390 {_93670 B : Type'} (f : _93670 -> B) (x : type684 _93670) : (term587 _93670 B f x) = (term588 _93670 B f x).
Proof. exact (MK_COMB (@lem3658388 _93670 B f) (@lem3658389 _93670 x)). Qed.
Lemma lem3658391 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) : (term588 _93670 B f x) = (term576 _93670 B x f).
Proof. exact (eq_refl (term588 _93670 B f x)). Qed.
Lemma lem3658392 {_93670 B : Type'} (x : type684 _93670) (f : _93670 -> B) : (term587 _93670 B f x) = (term576 _93670 B x f).
Proof. exact (TRANS (@lem3658390 _93670 B f x) (@lem3658391 _93670 B x f)). Qed.
Lemma lem3658393 {_93670 B : Type'} (f : _93670 -> B) : (term589 _93670 B f) = (term577 _93670 B f).
Proof. exact (fun_ext (fun x : type684 _93670 => @lem3658392 _93670 B x f)). Qed.
Lemma lem3658394 {_93670 : Type'} : (@ex ((_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658395 {_93670 B : Type'} (f : _93670 -> B) : (term590 _93670 B f) = (term578 _93670 B f).
Proof. exact (MK_COMB (@lem3658394 _93670) (@lem3658393 _93670 B f)). Qed.
Lemma lem3658396 {_93670 B : Type'} : (term591 _93670 B) = (term579 _93670 B).
Proof. exact (fun_ext (fun f : _93670 -> B => @lem3658395 _93670 B f)). Qed.
Lemma lem3658397 {_93670 B : Type'} : (@all (_93670 -> B)) = (@all (_93670 -> B)).
Proof. exact (eq_refl (@all (_93670 -> B))). Qed.
Lemma lem3658398 {_93670 B : Type'} : (term583 _93670 B) = (term580 _93670 B).
Proof. exact (MK_COMB (@lem3658397 _93670 B) (@lem3658396 _93670 B)). Qed.
Lemma lem3658399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658400 {_93670 B : Type'} : (term592 _93670 B) = (term593 _93670 B).
Proof. exact (MK_COMB (@lem3658399) (@lem3658398 _93670 B)). Qed.
Lemma lem3658401 {_93670 B : Type'} (f : _93670 -> B) : (term586 _93670 B f) = (term577 _93670 B f).
Proof. exact (eq_refl (term586 _93670 B f)). Qed.
Lemma lem3658402 {_93670 B : Type'} (x : type529 _93670 B) (f : _93670 -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem3658403 {_93670 B : Type'} (x : type529 _93670 B) (f : _93670 -> B) : (term594 _93670 B x f) = (term595 _93670 B x f).
Proof. exact (MK_COMB (@lem3658401 _93670 B f) (@lem3658402 _93670 B x f)). Qed.
Lemma lem3658404 {_93670 B : Type'} (x : type529 _93670 B) (f : _93670 -> B) : (term595 _93670 B x f) = (term596 _93670 B x f).
Proof. exact (eq_refl (term595 _93670 B x f)). Qed.
Lemma lem3658405 {_93670 B : Type'} (x : type529 _93670 B) (f : _93670 -> B) : (term594 _93670 B x f) = (term596 _93670 B x f).
Proof. exact (TRANS (@lem3658403 _93670 B x f) (@lem3658404 _93670 B x f)). Qed.
Lemma lem3658406 {_93670 B : Type'} (x : type529 _93670 B) : (term597 _93670 B x) = (term598 _93670 B x).
Proof. exact (fun_ext (fun f : _93670 -> B => @lem3658405 _93670 B x f)). Qed.
Lemma lem3658407 {_93670 B : Type'} : (@all (_93670 -> B)) = (@all (_93670 -> B)).
Proof. exact (eq_refl (@all (_93670 -> B))). Qed.
Lemma lem3658408 {_93670 B : Type'} (x : type529 _93670 B) : (term599 _93670 B x) = (term600 _93670 B x).
Proof. exact (MK_COMB (@lem3658407 _93670 B) (@lem3658406 _93670 B x)). Qed.
Lemma lem3658409 {_93670 B : Type'} : (term601 _93670 B) = (term602 _93670 B).
Proof. exact (fun_ext (fun x : type529 _93670 B => @lem3658408 _93670 B x)). Qed.
Lemma lem3658410 {_93670 B : Type'} : (@ex ((_93670 -> B) -> (_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> B) -> (_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> B) -> (_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658411 {_93670 B : Type'} : (term584 _93670 B) = (term603 _93670 B).
Proof. exact (MK_COMB (@lem3658410 _93670 B) (@lem3658409 _93670 B)). Qed.
Lemma lem3658412 {_93670 B : Type'} : ((term583 _93670 B) = (term584 _93670 B)) = ((term580 _93670 B) = (term603 _93670 B)).
Proof. exact (MK_COMB (@lem3658400 _93670 B) (@lem3658411 _93670 B)). Qed.
Lemma lem3658413 {_93670 B : Type'} : (term580 _93670 B) = (term603 _93670 B).
Proof. exact (EQ_MP (@lem3658412 _93670 B) (@lem3658387 _93670 B)). Qed.
Lemma lem3658415 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3658416 {_93670 B : Type'} (P : type503 _93670 B) : (term581 _93670 B P) = (term582 _93670 B P).
Proof. exact (@lem3658415 (_93670 -> B) (type684 _93670) P). Qed.
Lemma lem3658417 {_93670 B : Type'} (x : type529 _93670 B) : (term604 _93670 B x) = (term605 _93670 B x).
Proof. exact (@lem3658416 _93670 B (term606 _93670 B x)). Qed.
Lemma lem3658418 {_93670 B : Type'} (x : type529 _93670 B) (f : _93670 -> B) : (term607 _93670 B x f) = (term608 _93670 B x f).
Proof. exact (eq_refl (term607 _93670 B x f)). Qed.
Lemma lem3658419 {_93670 : Type'} (y : type684 _93670) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3658420 {_93670 B : Type'} (x : type529 _93670 B) (f : _93670 -> B) (y : type684 _93670) : (term609 _93670 B x f y) = (term610 _93670 B x f y).
Proof. exact (MK_COMB (@lem3658418 _93670 B x f) (@lem3658419 _93670 y)). Qed.
Lemma lem3658421 {_93670 B : Type'} (x : type529 _93670 B) (y : type684 _93670) (f : _93670 -> B) : (term610 _93670 B x f y) = (term611 _93670 B x y f).
Proof. exact (eq_refl (term610 _93670 B x f y)). Qed.
Lemma lem3658422 {_93670 B : Type'} (x : type529 _93670 B) (y : type684 _93670) (f : _93670 -> B) : (term609 _93670 B x f y) = (term611 _93670 B x y f).
Proof. exact (TRANS (@lem3658420 _93670 B x f y) (@lem3658421 _93670 B x y f)). Qed.
Lemma lem3658423 {_93670 B : Type'} (x : type529 _93670 B) (f : _93670 -> B) : (term612 _93670 B x f) = (term608 _93670 B x f).
Proof. exact (fun_ext (fun y : type684 _93670 => @lem3658422 _93670 B x y f)). Qed.
Lemma lem3658424 {_93670 : Type'} : (@ex ((_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658425 {_93670 B : Type'} (x : type529 _93670 B) (f : _93670 -> B) : (term613 _93670 B x f) = (term596 _93670 B x f).
Proof. exact (MK_COMB (@lem3658424 _93670) (@lem3658423 _93670 B x f)). Qed.
Lemma lem3658426 {_93670 B : Type'} (x : type529 _93670 B) : (term614 _93670 B x) = (term598 _93670 B x).
Proof. exact (fun_ext (fun f : _93670 -> B => @lem3658425 _93670 B x f)). Qed.
Lemma lem3658427 {_93670 B : Type'} : (@all (_93670 -> B)) = (@all (_93670 -> B)).
Proof. exact (eq_refl (@all (_93670 -> B))). Qed.
Lemma lem3658428 {_93670 B : Type'} (x : type529 _93670 B) : (term604 _93670 B x) = (term600 _93670 B x).
Proof. exact (MK_COMB (@lem3658427 _93670 B) (@lem3658426 _93670 B x)). Qed.
Lemma lem3658429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658430 {_93670 B : Type'} (x : type529 _93670 B) : (term615 _93670 B x) = (term616 _93670 B x).
Proof. exact (MK_COMB (@lem3658429) (@lem3658428 _93670 B x)). Qed.
Lemma lem3658431 {_93670 B : Type'} (x : type529 _93670 B) (f : _93670 -> B) : (term607 _93670 B x f) = (term608 _93670 B x f).
Proof. exact (eq_refl (term607 _93670 B x f)). Qed.
Lemma lem3658432 {_93670 B : Type'} (y : type529 _93670 B) (f : _93670 -> B) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem3658433 {_93670 B : Type'} (x : type529 _93670 B) (y : type529 _93670 B) (f : _93670 -> B) : (term617 _93670 B x y f) = (term618 _93670 B x y f).
Proof. exact (MK_COMB (@lem3658431 _93670 B x f) (@lem3658432 _93670 B y f)). Qed.
Lemma lem3658434 {_93670 B : Type'} (x : type529 _93670 B) (y : type529 _93670 B) (f : _93670 -> B) : (term618 _93670 B x y f) = (term619 _93670 B x y f).
Proof. exact (eq_refl (term618 _93670 B x y f)). Qed.
Lemma lem3658435 {_93670 B : Type'} (x : type529 _93670 B) (y : type529 _93670 B) (f : _93670 -> B) : (term617 _93670 B x y f) = (term619 _93670 B x y f).
Proof. exact (TRANS (@lem3658433 _93670 B x y f) (@lem3658434 _93670 B x y f)). Qed.
Lemma lem3658436 {_93670 B : Type'} (x : type529 _93670 B) (y : type529 _93670 B) : (term620 _93670 B x y) = (term621 _93670 B x y).
Proof. exact (fun_ext (fun f : _93670 -> B => @lem3658435 _93670 B x y f)). Qed.
Lemma lem3658437 {_93670 B : Type'} : (@all (_93670 -> B)) = (@all (_93670 -> B)).
Proof. exact (eq_refl (@all (_93670 -> B))). Qed.
Lemma lem3658438 {_93670 B : Type'} (x : type529 _93670 B) (y : type529 _93670 B) : (term622 _93670 B x y) = (term623 _93670 B x y).
Proof. exact (MK_COMB (@lem3658437 _93670 B) (@lem3658436 _93670 B x y)). Qed.
Lemma lem3658439 {_93670 B : Type'} (x : type529 _93670 B) : (term624 _93670 B x) = (term625 _93670 B x).
Proof. exact (fun_ext (fun y : type529 _93670 B => @lem3658438 _93670 B x y)). Qed.
Lemma lem3658440 {_93670 B : Type'} : (@ex ((_93670 -> B) -> (_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> B) -> (_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> B) -> (_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658441 {_93670 B : Type'} (x : type529 _93670 B) : (term605 _93670 B x) = (term626 _93670 B x).
Proof. exact (MK_COMB (@lem3658440 _93670 B) (@lem3658439 _93670 B x)). Qed.
Lemma lem3658442 {_93670 B : Type'} (x : type529 _93670 B) : ((term604 _93670 B x) = (term605 _93670 B x)) = ((term600 _93670 B x) = (term626 _93670 B x)).
Proof. exact (MK_COMB (@lem3658430 _93670 B x) (@lem3658441 _93670 B x)). Qed.
Lemma lem3658443 {_93670 B : Type'} (x : type529 _93670 B) : (term600 _93670 B x) = (term626 _93670 B x).
Proof. exact (EQ_MP (@lem3658442 _93670 B x) (@lem3658417 _93670 B x)). Qed.
Lemma lem3658444 {_93670 B : Type'} : (term602 _93670 B) = (term627 _93670 B).
Proof. exact (fun_ext (fun x : type529 _93670 B => @lem3658443 _93670 B x)). Qed.
Lemma lem3658445 {_93670 B : Type'} : (@ex ((_93670 -> B) -> (_93670 -> Prop) -> _93670)) = (@ex ((_93670 -> B) -> (_93670 -> Prop) -> _93670)).
Proof. exact (eq_refl (@ex ((_93670 -> B) -> (_93670 -> Prop) -> _93670))). Qed.
Lemma lem3658446 {_93670 B : Type'} : (term603 _93670 B) = (term628 _93670 B).
Proof. exact (MK_COMB (@lem3658445 _93670 B) (@lem3658444 _93670 B)). Qed.
Lemma lem3658447 {_93670 B : Type'} : (term580 _93670 B) = (term628 _93670 B).
Proof. exact (TRANS (@lem3658413 _93670 B) (@lem3658446 _93670 B)). Qed.
Lemma lem3658449 {_93670 B : Type'} : (term494 _93670 B) = (term628 _93670 B).
Proof. exact (TRANS (@lem3658383 _93670 B) (@lem3658447 _93670 B)). Qed.
Lemma lem3658450 {_93670 B : Type'} : (term82 _93670 B) = (term628 _93670 B).
Proof. exact (TRANS (@lem3658155 _93670 B) (@lem3658449 _93670 B)). Qed.
Lemma lem3658451 {_93670 B : Type'} (h1 : term82 _93670 B) : term628 _93670 B.
Proof. exact (EQ_MP (@lem3658450 _93670 B) (@lem3656892 _93670 B h1)). Qed.
Lemma lem3658466 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) (y : _93677) : (term469 _93677 B s f x y) = (term470 _93677 B s f x y).
Proof. exact (@lem17362 (term471 _93677 B s x f y) (x = y)). Qed.
Lemma lem3658467 {_93677 : Type'} (P : _93677 -> Prop) : (term163 _93677 P) = (term164 _93677 P).
Proof. exact (@lem18392 _93677 P). Qed.
Lemma lem3658468 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term472 _93677 B s f x) = (term473 _93677 B s f x).
Proof. exact (@lem3658467 _93677 (term131 _93677 B s f x)). Qed.
Lemma lem3658469 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) (y : _93677) : (term474 _93677 B s f x y) = (term130 _93677 B s f x y).
Proof. exact (eq_refl (term474 _93677 B s f x y)). Qed.
Lemma lem3658470 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3658471 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) (y : _93677) : (term475 _93677 B s f x y) = (term469 _93677 B s f x y).
Proof. exact (MK_COMB (@lem3658470) (@lem3658469 _93677 B s f x y)). Qed.
Lemma lem3658472 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) (y : _93677) : (term475 _93677 B s f x y) = (term470 _93677 B s f x y).
Proof. exact (TRANS (@lem3658471 _93677 B s f x y) (@lem3658466 _93677 B s f x y)). Qed.
Lemma lem3658473 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term476 _93677 B s f x) = (term477 _93677 B s f x).
Proof. exact (fun_ext (fun y : _93677 => @lem3658472 _93677 B s f x y)). Qed.
Lemma lem3658474 {_93677 : Type'} : (@ex _93677) = (@ex _93677).
Proof. exact (eq_refl (@ex _93677)). Qed.
Lemma lem3658475 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term473 _93677 B s f x) = (term478 _93677 B s f x).
Proof. exact (MK_COMB (@lem3658474 _93677) (@lem3658473 _93677 B s f x)). Qed.
Lemma lem3658476 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term472 _93677 B s f x) = (term478 _93677 B s f x).
Proof. exact (TRANS (@lem3658468 _93677 B s f x) (@lem3658475 _93677 B s f x)). Qed.
Lemma lem3658477 {_93677 : Type'} (P : _93677 -> Prop) : (term163 _93677 P) = (term164 _93677 P).
Proof. exact (@lem18392 _93677 P). Qed.
Lemma lem3658478 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) : (term479 _93677 B s f) = (term480 _93677 B s f).
Proof. exact (@lem3658477 _93677 (term133 _93677 B s f)). Qed.
Lemma lem3658479 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term481 _93677 B s f x) = (term132 _93677 B s f x).
Proof. exact (eq_refl (term481 _93677 B s f x)). Qed.
Lemma lem3658480 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3658481 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term482 _93677 B s f x) = (term472 _93677 B s f x).
Proof. exact (MK_COMB (@lem3658480) (@lem3658479 _93677 B s f x)). Qed.
Lemma lem3658482 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term482 _93677 B s f x) = (term478 _93677 B s f x).
Proof. exact (TRANS (@lem3658481 _93677 B s f x) (@lem3658476 _93677 B s f x)). Qed.
Lemma lem3658483 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) : (term483 _93677 B s f) = (term484 _93677 B s f).
Proof. exact (fun_ext (fun x : _93677 => @lem3658482 _93677 B s f x)). Qed.
Lemma lem3658484 {_93677 : Type'} : (@ex _93677) = (@ex _93677).
Proof. exact (eq_refl (@ex _93677)). Qed.
Lemma lem3658485 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) : (term480 _93677 B s f) = (term485 _93677 B s f).
Proof. exact (MK_COMB (@lem3658484 _93677) (@lem3658483 _93677 B s f)). Qed.
Lemma lem3658486 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) : (term479 _93677 B s f) = (term485 _93677 B s f).
Proof. exact (TRANS (@lem3658478 _93677 B s f) (@lem3658485 _93677 B s f)). Qed.
Lemma lem3658501 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : ((term129 _93677 B f s) = (@FINITE _93677 s)) = (term486 _93677 B f s).
Proof. exact (@lem17784 (term129 _93677 B f s) (@FINITE _93677 s)). Qed.
Lemma lem3658502 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3658503 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) : (term487 _93677 B s f) = (term488 _93677 B s f).
Proof. exact (MK_COMB (@lem3658502) (@lem3658486 _93677 B s f)). Qed.
Lemma lem3658504 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term489 _93677 B f s) = (term490 _93677 B f s).
Proof. exact (MK_COMB (@lem3658503 _93677 B s f) (@lem3658501 _93677 B f s)). Qed.
Lemma lem3658505 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term136 _93677 B f s) = (term489 _93677 B f s).
Proof. exact (@lem17265 (term134 _93677 B s f) ((term129 _93677 B f s) = (@FINITE _93677 s))). Qed.
Lemma lem3658506 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term136 _93677 B f s) = (term490 _93677 B f s).
Proof. exact (TRANS (@lem3658505 _93677 B f s) (@lem3658504 _93677 B f s)). Qed.
Lemma lem3658507 {_93677 B : Type'} (f : _93677 -> B) : (term137 _93677 B f) = (term491 _93677 B f).
Proof. exact (fun_ext (fun s : _93677 -> Prop => @lem3658506 _93677 B f s)). Qed.
Lemma lem3658508 {_93677 : Type'} : (@all (_93677 -> Prop)) = (@all (_93677 -> Prop)).
Proof. exact (eq_refl (@all (_93677 -> Prop))). Qed.
Lemma lem3658509 {_93677 B : Type'} (f : _93677 -> B) : (term138 _93677 B f) = (term492 _93677 B f).
Proof. exact (MK_COMB (@lem3658508 _93677) (@lem3658507 _93677 B f)). Qed.
Lemma lem3658510 {_93677 B : Type'} : (term139 _93677 B) = (term493 _93677 B).
Proof. exact (fun_ext (fun f : _93677 -> B => @lem3658509 _93677 B f)). Qed.
Lemma lem3658511 {_93677 B : Type'} : (@all (_93677 -> B)) = (@all (_93677 -> B)).
Proof. exact (eq_refl (@all (_93677 -> B))). Qed.
Lemma lem3658512 {_93677 B : Type'} : (term82 _93677 B) = (term494 _93677 B).
Proof. exact (MK_COMB (@lem3658511 _93677 B) (@lem3658510 _93677 B)). Qed.
Lemma lem3658619 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3658620 {_93677 : Type'} (P : _93677 -> Prop) (Q : Prop) : (term223 _93677 P Q) = (term224 _93677 P Q).
Proof. exact (@lem3658619 _93677 P Q). Qed.
Lemma lem3658621 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term495 _93677 B f s) = (term496 _93677 B f s).
Proof. exact (@lem3658620 _93677 (term484 _93677 B s f) (term486 _93677 B f s)). Qed.
Lemma lem3658622 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term497 _93677 B s f x) = (term478 _93677 B s f x).
Proof. exact (eq_refl (term497 _93677 B s f x)). Qed.
Lemma lem3658623 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) : (term498 _93677 B s f) = (term484 _93677 B s f).
Proof. exact (fun_ext (fun x : _93677 => @lem3658622 _93677 B s f x)). Qed.
Lemma lem3658624 {_93677 : Type'} : (@ex _93677) = (@ex _93677).
Proof. exact (eq_refl (@ex _93677)). Qed.
Lemma lem3658625 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) : (term499 _93677 B s f) = (term485 _93677 B s f).
Proof. exact (MK_COMB (@lem3658624 _93677) (@lem3658623 _93677 B s f)). Qed.
Lemma lem3658626 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3658627 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) : (term500 _93677 B s f) = (term488 _93677 B s f).
Proof. exact (MK_COMB (@lem3658626) (@lem3658625 _93677 B s f)). Qed.
Lemma lem3658628 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term486 _93677 B f s) = (term486 _93677 B f s).
Proof. exact (eq_refl (term486 _93677 B f s)). Qed.
Lemma lem3658629 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term495 _93677 B f s) = (term490 _93677 B f s).
Proof. exact (MK_COMB (@lem3658627 _93677 B s f) (@lem3658628 _93677 B f s)). Qed.
Lemma lem3658630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658631 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term501 _93677 B f s) = (term502 _93677 B f s).
Proof. exact (MK_COMB (@lem3658630) (@lem3658629 _93677 B f s)). Qed.
Lemma lem3658632 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term497 _93677 B s f x) = (term478 _93677 B s f x).
Proof. exact (eq_refl (term497 _93677 B s f x)). Qed.
Lemma lem3658633 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3658634 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term503 _93677 B s f x) = (term504 _93677 B s f x).
Proof. exact (MK_COMB (@lem3658633) (@lem3658632 _93677 B s f x)). Qed.
Lemma lem3658635 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term486 _93677 B f s) = (term486 _93677 B f s).
Proof. exact (eq_refl (term486 _93677 B f s)). Qed.
Lemma lem3658636 {_93677 B : Type'} (x : _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term505 _93677 B x f s) = (term506 _93677 B x f s).
Proof. exact (MK_COMB (@lem3658634 _93677 B s f x) (@lem3658635 _93677 B f s)). Qed.
Lemma lem3658637 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term507 _93677 B f s) = (term508 _93677 B f s).
Proof. exact (fun_ext (fun x : _93677 => @lem3658636 _93677 B x f s)). Qed.
Lemma lem3658638 {_93677 : Type'} : (@ex _93677) = (@ex _93677).
Proof. exact (eq_refl (@ex _93677)). Qed.
Lemma lem3658639 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term496 _93677 B f s) = (term509 _93677 B f s).
Proof. exact (MK_COMB (@lem3658638 _93677) (@lem3658637 _93677 B f s)). Qed.
Lemma lem3658640 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : ((term495 _93677 B f s) = (term496 _93677 B f s)) = ((term490 _93677 B f s) = (term509 _93677 B f s)).
Proof. exact (MK_COMB (@lem3658631 _93677 B f s) (@lem3658639 _93677 B f s)). Qed.
Lemma lem3658641 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term490 _93677 B f s) = (term509 _93677 B f s).
Proof. exact (EQ_MP (@lem3658640 _93677 B f s) (@lem3658621 _93677 B f s)). Qed.
Lemma lem3658643 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3658644 {_93677 : Type'} (P : _93677 -> Prop) (Q : Prop) : (term223 _93677 P Q) = (term224 _93677 P Q).
Proof. exact (@lem3658643 _93677 P Q). Qed.
Lemma lem3658645 {_93677 B : Type'} (x : _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term510 _93677 B x f s) = (term511 _93677 B x f s).
Proof. exact (@lem3658644 _93677 (term477 _93677 B s f x) (term486 _93677 B f s)). Qed.
Lemma lem3658646 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) (y : _93677) : (term512 _93677 B s f x y) = (term470 _93677 B s f x y).
Proof. exact (eq_refl (term512 _93677 B s f x y)). Qed.
Lemma lem3658647 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term513 _93677 B s f x) = (term477 _93677 B s f x).
Proof. exact (fun_ext (fun y : _93677 => @lem3658646 _93677 B s f x y)). Qed.
Lemma lem3658648 {_93677 : Type'} : (@ex _93677) = (@ex _93677).
Proof. exact (eq_refl (@ex _93677)). Qed.
Lemma lem3658649 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term514 _93677 B s f x) = (term478 _93677 B s f x).
Proof. exact (MK_COMB (@lem3658648 _93677) (@lem3658647 _93677 B s f x)). Qed.
Lemma lem3658650 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3658651 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) : (term515 _93677 B s f x) = (term504 _93677 B s f x).
Proof. exact (MK_COMB (@lem3658650) (@lem3658649 _93677 B s f x)). Qed.
Lemma lem3658652 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term486 _93677 B f s) = (term486 _93677 B f s).
Proof. exact (eq_refl (term486 _93677 B f s)). Qed.
Lemma lem3658653 {_93677 B : Type'} (x : _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term510 _93677 B x f s) = (term506 _93677 B x f s).
Proof. exact (MK_COMB (@lem3658651 _93677 B s f x) (@lem3658652 _93677 B f s)). Qed.
Lemma lem3658654 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658655 {_93677 B : Type'} (x : _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term516 _93677 B x f s) = (term517 _93677 B x f s).
Proof. exact (MK_COMB (@lem3658654) (@lem3658653 _93677 B x f s)). Qed.
Lemma lem3658656 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) (y : _93677) : (term512 _93677 B s f x y) = (term470 _93677 B s f x y).
Proof. exact (eq_refl (term512 _93677 B s f x y)). Qed.
Lemma lem3658657 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3658658 {_93677 B : Type'} (s : _93677 -> Prop) (f : _93677 -> B) (x : _93677) (y : _93677) : (term518 _93677 B s f x y) = (term519 _93677 B s f x y).
Proof. exact (MK_COMB (@lem3658657) (@lem3658656 _93677 B s f x y)). Qed.
Lemma lem3658659 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term486 _93677 B f s) = (term486 _93677 B f s).
Proof. exact (eq_refl (term486 _93677 B f s)). Qed.
Lemma lem3658660 {_93677 B : Type'} (x : _93677) (y : _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term520 _93677 B x y f s) = (term521 _93677 B x y f s).
Proof. exact (MK_COMB (@lem3658658 _93677 B s f x y) (@lem3658659 _93677 B f s)). Qed.
Lemma lem3658661 {_93677 B : Type'} (x : _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term522 _93677 B x f s) = (term523 _93677 B x f s).
Proof. exact (fun_ext (fun y : _93677 => @lem3658660 _93677 B x y f s)). Qed.
Lemma lem3658662 {_93677 : Type'} : (@ex _93677) = (@ex _93677).
Proof. exact (eq_refl (@ex _93677)). Qed.
Lemma lem3658663 {_93677 B : Type'} (x : _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term511 _93677 B x f s) = (term524 _93677 B x f s).
Proof. exact (MK_COMB (@lem3658662 _93677) (@lem3658661 _93677 B x f s)). Qed.
Lemma lem3658664 {_93677 B : Type'} (x : _93677) (f : _93677 -> B) (s : _93677 -> Prop) : ((term510 _93677 B x f s) = (term511 _93677 B x f s)) = ((term506 _93677 B x f s) = (term524 _93677 B x f s)).
Proof. exact (MK_COMB (@lem3658655 _93677 B x f s) (@lem3658663 _93677 B x f s)). Qed.
Lemma lem3658665 {_93677 B : Type'} (x : _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term506 _93677 B x f s) = (term524 _93677 B x f s).
Proof. exact (EQ_MP (@lem3658664 _93677 B x f s) (@lem3658645 _93677 B x f s)). Qed.
Lemma lem3658666 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term508 _93677 B f s) = (term525 _93677 B f s).
Proof. exact (fun_ext (fun x : _93677 => @lem3658665 _93677 B x f s)). Qed.
Lemma lem3658667 {_93677 : Type'} : (@ex _93677) = (@ex _93677).
Proof. exact (eq_refl (@ex _93677)). Qed.
Lemma lem3658668 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term509 _93677 B f s) = (term526 _93677 B f s).
Proof. exact (MK_COMB (@lem3658667 _93677) (@lem3658666 _93677 B f s)). Qed.
Lemma lem3658669 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term490 _93677 B f s) = (term526 _93677 B f s).
Proof. exact (TRANS (@lem3658641 _93677 B f s) (@lem3658668 _93677 B f s)). Qed.
Lemma lem3658670 {_93677 B : Type'} (f : _93677 -> B) : (term491 _93677 B f) = (term527 _93677 B f).
Proof. exact (fun_ext (fun s : _93677 -> Prop => @lem3658669 _93677 B f s)). Qed.
Lemma lem3658671 {_93677 : Type'} : (@all (_93677 -> Prop)) = (@all (_93677 -> Prop)).
Proof. exact (eq_refl (@all (_93677 -> Prop))). Qed.
Lemma lem3658672 {_93677 B : Type'} (f : _93677 -> B) : (term492 _93677 B f) = (term528 _93677 B f).
Proof. exact (MK_COMB (@lem3658671 _93677) (@lem3658670 _93677 B f)). Qed.
Lemma lem3658674 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3658675 {_93677 : Type'} (P : type672 _93677) : (term531 _93677 P) = (term532 _93677 P).
Proof. exact (@lem3658674 (_93677 -> Prop) _93677 P). Qed.
Lemma lem3658676 {_93677 B : Type'} (f : _93677 -> B) : (term533 _93677 B f) = (term534 _93677 B f).
Proof. exact (@lem3658675 _93677 (term535 _93677 B f)). Qed.
Lemma lem3658677 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term536 _93677 B f s) = (term525 _93677 B f s).
Proof. exact (eq_refl (term536 _93677 B f s)). Qed.
Lemma lem3658678 {_93677 : Type'} (x : _93677) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3658679 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) (x : _93677) : (term537 _93677 B f s x) = (term538 _93677 B f s x).
Proof. exact (MK_COMB (@lem3658677 _93677 B f s) (@lem3658678 _93677 x)). Qed.
Lemma lem3658680 {_93677 B : Type'} (x : _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term538 _93677 B f s x) = (term524 _93677 B x f s).
Proof. exact (eq_refl (term538 _93677 B f s x)). Qed.
Lemma lem3658681 {_93677 B : Type'} (x : _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term537 _93677 B f s x) = (term524 _93677 B x f s).
Proof. exact (TRANS (@lem3658679 _93677 B f s x) (@lem3658680 _93677 B x f s)). Qed.
Lemma lem3658682 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term539 _93677 B f s) = (term525 _93677 B f s).
Proof. exact (fun_ext (fun x : _93677 => @lem3658681 _93677 B x f s)). Qed.
Lemma lem3658683 {_93677 : Type'} : (@ex _93677) = (@ex _93677).
Proof. exact (eq_refl (@ex _93677)). Qed.
Lemma lem3658684 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term540 _93677 B f s) = (term526 _93677 B f s).
Proof. exact (MK_COMB (@lem3658683 _93677) (@lem3658682 _93677 B f s)). Qed.
Lemma lem3658685 {_93677 B : Type'} (f : _93677 -> B) : (term541 _93677 B f) = (term527 _93677 B f).
Proof. exact (fun_ext (fun s : _93677 -> Prop => @lem3658684 _93677 B f s)). Qed.
Lemma lem3658686 {_93677 : Type'} : (@all (_93677 -> Prop)) = (@all (_93677 -> Prop)).
Proof. exact (eq_refl (@all (_93677 -> Prop))). Qed.
Lemma lem3658687 {_93677 B : Type'} (f : _93677 -> B) : (term533 _93677 B f) = (term528 _93677 B f).
Proof. exact (MK_COMB (@lem3658686 _93677) (@lem3658685 _93677 B f)). Qed.
Lemma lem3658688 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658689 {_93677 B : Type'} (f : _93677 -> B) : (term542 _93677 B f) = (term543 _93677 B f).
Proof. exact (MK_COMB (@lem3658688) (@lem3658687 _93677 B f)). Qed.
Lemma lem3658690 {_93677 B : Type'} (f : _93677 -> B) (s : _93677 -> Prop) : (term536 _93677 B f s) = (term525 _93677 B f s).
Proof. exact (eq_refl (term536 _93677 B f s)). Qed.
Lemma lem3658691 {_93677 : Type'} (x : type684 _93677) (s : _93677 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3658692 {_93677 B : Type'} (f : _93677 -> B) (x : type684 _93677) (s : _93677 -> Prop) : (term544 _93677 B f x s) = (term545 _93677 B f x s).
Proof. exact (MK_COMB (@lem3658690 _93677 B f s) (@lem3658691 _93677 x s)). Qed.
Lemma lem3658693 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term545 _93677 B f x s) = (term546 _93677 B x f s).
Proof. exact (eq_refl (term545 _93677 B f x s)). Qed.
Lemma lem3658694 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term544 _93677 B f x s) = (term546 _93677 B x f s).
Proof. exact (TRANS (@lem3658692 _93677 B f x s) (@lem3658693 _93677 B x f s)). Qed.
Lemma lem3658695 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) : (term547 _93677 B f x) = (term548 _93677 B x f).
Proof. exact (fun_ext (fun s : _93677 -> Prop => @lem3658694 _93677 B x f s)). Qed.
Lemma lem3658696 {_93677 : Type'} : (@all (_93677 -> Prop)) = (@all (_93677 -> Prop)).
Proof. exact (eq_refl (@all (_93677 -> Prop))). Qed.
Lemma lem3658697 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) : (term549 _93677 B f x) = (term550 _93677 B x f).
Proof. exact (MK_COMB (@lem3658696 _93677) (@lem3658695 _93677 B x f)). Qed.
Lemma lem3658698 {_93677 B : Type'} (f : _93677 -> B) : (term551 _93677 B f) = (term552 _93677 B f).
Proof. exact (fun_ext (fun x : type684 _93677 => @lem3658697 _93677 B x f)). Qed.
Lemma lem3658699 {_93677 : Type'} : (@ex ((_93677 -> Prop) -> _93677)) = (@ex ((_93677 -> Prop) -> _93677)).
Proof. exact (eq_refl (@ex ((_93677 -> Prop) -> _93677))). Qed.
Lemma lem3658700 {_93677 B : Type'} (f : _93677 -> B) : (term534 _93677 B f) = (term553 _93677 B f).
Proof. exact (MK_COMB (@lem3658699 _93677) (@lem3658698 _93677 B f)). Qed.
Lemma lem3658701 {_93677 B : Type'} (f : _93677 -> B) : ((term533 _93677 B f) = (term534 _93677 B f)) = ((term528 _93677 B f) = (term553 _93677 B f)).
Proof. exact (MK_COMB (@lem3658689 _93677 B f) (@lem3658700 _93677 B f)). Qed.
Lemma lem3658702 {_93677 B : Type'} (f : _93677 -> B) : (term528 _93677 B f) = (term553 _93677 B f).
Proof. exact (EQ_MP (@lem3658701 _93677 B f) (@lem3658676 _93677 B f)). Qed.
Lemma lem3658704 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3658705 {_93677 : Type'} (P : type672 _93677) : (term531 _93677 P) = (term532 _93677 P).
Proof. exact (@lem3658704 (_93677 -> Prop) _93677 P). Qed.
Lemma lem3658706 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) : (term554 _93677 B x f) = (term555 _93677 B x f).
Proof. exact (@lem3658705 _93677 (term556 _93677 B x f)). Qed.
Lemma lem3658707 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term557 _93677 B x f s) = (term558 _93677 B x f s).
Proof. exact (eq_refl (term557 _93677 B x f s)). Qed.
Lemma lem3658708 {_93677 : Type'} (y : _93677) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3658709 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) (s : _93677 -> Prop) (y : _93677) : (term559 _93677 B x f s y) = (term560 _93677 B x f s y).
Proof. exact (MK_COMB (@lem3658707 _93677 B x f s) (@lem3658708 _93677 y)). Qed.
Lemma lem3658710 {_93677 B : Type'} (x : type684 _93677) (y : _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term560 _93677 B x f s y) = (term561 _93677 B x y f s).
Proof. exact (eq_refl (term560 _93677 B x f s y)). Qed.
Lemma lem3658711 {_93677 B : Type'} (x : type684 _93677) (y : _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term559 _93677 B x f s y) = (term561 _93677 B x y f s).
Proof. exact (TRANS (@lem3658709 _93677 B x f s y) (@lem3658710 _93677 B x y f s)). Qed.
Lemma lem3658712 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term562 _93677 B x f s) = (term558 _93677 B x f s).
Proof. exact (fun_ext (fun y : _93677 => @lem3658711 _93677 B x y f s)). Qed.
Lemma lem3658713 {_93677 : Type'} : (@ex _93677) = (@ex _93677).
Proof. exact (eq_refl (@ex _93677)). Qed.
Lemma lem3658714 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term563 _93677 B x f s) = (term546 _93677 B x f s).
Proof. exact (MK_COMB (@lem3658713 _93677) (@lem3658712 _93677 B x f s)). Qed.
Lemma lem3658715 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) : (term564 _93677 B x f) = (term548 _93677 B x f).
Proof. exact (fun_ext (fun s : _93677 -> Prop => @lem3658714 _93677 B x f s)). Qed.
Lemma lem3658716 {_93677 : Type'} : (@all (_93677 -> Prop)) = (@all (_93677 -> Prop)).
Proof. exact (eq_refl (@all (_93677 -> Prop))). Qed.
Lemma lem3658717 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) : (term554 _93677 B x f) = (term550 _93677 B x f).
Proof. exact (MK_COMB (@lem3658716 _93677) (@lem3658715 _93677 B x f)). Qed.
Lemma lem3658718 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658719 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) : (term565 _93677 B x f) = (term566 _93677 B x f).
Proof. exact (MK_COMB (@lem3658718) (@lem3658717 _93677 B x f)). Qed.
Lemma lem3658720 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term557 _93677 B x f s) = (term558 _93677 B x f s).
Proof. exact (eq_refl (term557 _93677 B x f s)). Qed.
Lemma lem3658721 {_93677 : Type'} (y : type684 _93677) (s : _93677 -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem3658722 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) (y : type684 _93677) (s : _93677 -> Prop) : (term567 _93677 B x f y s) = (term568 _93677 B x f y s).
Proof. exact (MK_COMB (@lem3658720 _93677 B x f s) (@lem3658721 _93677 y s)). Qed.
Lemma lem3658723 {_93677 B : Type'} (x : type684 _93677) (y : type684 _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term568 _93677 B x f y s) = (term569 _93677 B x y f s).
Proof. exact (eq_refl (term568 _93677 B x f y s)). Qed.
Lemma lem3658724 {_93677 B : Type'} (x : type684 _93677) (y : type684 _93677) (f : _93677 -> B) (s : _93677 -> Prop) : (term567 _93677 B x f y s) = (term569 _93677 B x y f s).
Proof. exact (TRANS (@lem3658722 _93677 B x f y s) (@lem3658723 _93677 B x y f s)). Qed.
Lemma lem3658725 {_93677 B : Type'} (x : type684 _93677) (y : type684 _93677) (f : _93677 -> B) : (term570 _93677 B x f y) = (term571 _93677 B x y f).
Proof. exact (fun_ext (fun s : _93677 -> Prop => @lem3658724 _93677 B x y f s)). Qed.
Lemma lem3658726 {_93677 : Type'} : (@all (_93677 -> Prop)) = (@all (_93677 -> Prop)).
Proof. exact (eq_refl (@all (_93677 -> Prop))). Qed.
Lemma lem3658727 {_93677 B : Type'} (x : type684 _93677) (y : type684 _93677) (f : _93677 -> B) : (term572 _93677 B x f y) = (term573 _93677 B x y f).
Proof. exact (MK_COMB (@lem3658726 _93677) (@lem3658725 _93677 B x y f)). Qed.
Lemma lem3658728 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) : (term574 _93677 B x f) = (term575 _93677 B x f).
Proof. exact (fun_ext (fun y : type684 _93677 => @lem3658727 _93677 B x y f)). Qed.
Lemma lem3658729 {_93677 : Type'} : (@ex ((_93677 -> Prop) -> _93677)) = (@ex ((_93677 -> Prop) -> _93677)).
Proof. exact (eq_refl (@ex ((_93677 -> Prop) -> _93677))). Qed.
Lemma lem3658730 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) : (term555 _93677 B x f) = (term576 _93677 B x f).
Proof. exact (MK_COMB (@lem3658729 _93677) (@lem3658728 _93677 B x f)). Qed.
Lemma lem3658731 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) : ((term554 _93677 B x f) = (term555 _93677 B x f)) = ((term550 _93677 B x f) = (term576 _93677 B x f)).
Proof. exact (MK_COMB (@lem3658719 _93677 B x f) (@lem3658730 _93677 B x f)). Qed.
Lemma lem3658732 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) : (term550 _93677 B x f) = (term576 _93677 B x f).
Proof. exact (EQ_MP (@lem3658731 _93677 B x f) (@lem3658706 _93677 B x f)). Qed.
Lemma lem3658733 {_93677 B : Type'} (f : _93677 -> B) : (term552 _93677 B f) = (term577 _93677 B f).
Proof. exact (fun_ext (fun x : type684 _93677 => @lem3658732 _93677 B x f)). Qed.
Lemma lem3658734 {_93677 : Type'} : (@ex ((_93677 -> Prop) -> _93677)) = (@ex ((_93677 -> Prop) -> _93677)).
Proof. exact (eq_refl (@ex ((_93677 -> Prop) -> _93677))). Qed.
Lemma lem3658735 {_93677 B : Type'} (f : _93677 -> B) : (term553 _93677 B f) = (term578 _93677 B f).
Proof. exact (MK_COMB (@lem3658734 _93677) (@lem3658733 _93677 B f)). Qed.
Lemma lem3658736 {_93677 B : Type'} (f : _93677 -> B) : (term528 _93677 B f) = (term578 _93677 B f).
Proof. exact (TRANS (@lem3658702 _93677 B f) (@lem3658735 _93677 B f)). Qed.
Lemma lem3658737 {_93677 B : Type'} (f : _93677 -> B) : (term492 _93677 B f) = (term578 _93677 B f).
Proof. exact (TRANS (@lem3658672 _93677 B f) (@lem3658736 _93677 B f)). Qed.
Lemma lem3658738 {_93677 B : Type'} : (term493 _93677 B) = (term579 _93677 B).
Proof. exact (fun_ext (fun f : _93677 -> B => @lem3658737 _93677 B f)). Qed.
Lemma lem3658739 {_93677 B : Type'} : (@all (_93677 -> B)) = (@all (_93677 -> B)).
Proof. exact (eq_refl (@all (_93677 -> B))). Qed.
Lemma lem3658740 {_93677 B : Type'} : (term494 _93677 B) = (term580 _93677 B).
Proof. exact (MK_COMB (@lem3658739 _93677 B) (@lem3658738 _93677 B)). Qed.
Lemma lem3658742 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3658743 {_93677 B : Type'} (P : type503 _93677 B) : (term581 _93677 B P) = (term582 _93677 B P).
Proof. exact (@lem3658742 (_93677 -> B) (type684 _93677) P). Qed.
Lemma lem3658744 {_93677 B : Type'} : (term583 _93677 B) = (term584 _93677 B).
Proof. exact (@lem3658743 _93677 B (term585 _93677 B)). Qed.
Lemma lem3658745 {_93677 B : Type'} (f : _93677 -> B) : (term586 _93677 B f) = (term577 _93677 B f).
Proof. exact (eq_refl (term586 _93677 B f)). Qed.
Lemma lem3658746 {_93677 : Type'} (x : type684 _93677) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3658747 {_93677 B : Type'} (f : _93677 -> B) (x : type684 _93677) : (term587 _93677 B f x) = (term588 _93677 B f x).
Proof. exact (MK_COMB (@lem3658745 _93677 B f) (@lem3658746 _93677 x)). Qed.
Lemma lem3658748 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) : (term588 _93677 B f x) = (term576 _93677 B x f).
Proof. exact (eq_refl (term588 _93677 B f x)). Qed.
Lemma lem3658749 {_93677 B : Type'} (x : type684 _93677) (f : _93677 -> B) : (term587 _93677 B f x) = (term576 _93677 B x f).
Proof. exact (TRANS (@lem3658747 _93677 B f x) (@lem3658748 _93677 B x f)). Qed.
Lemma lem3658750 {_93677 B : Type'} (f : _93677 -> B) : (term589 _93677 B f) = (term577 _93677 B f).
Proof. exact (fun_ext (fun x : type684 _93677 => @lem3658749 _93677 B x f)). Qed.
Lemma lem3658751 {_93677 : Type'} : (@ex ((_93677 -> Prop) -> _93677)) = (@ex ((_93677 -> Prop) -> _93677)).
Proof. exact (eq_refl (@ex ((_93677 -> Prop) -> _93677))). Qed.
Lemma lem3658752 {_93677 B : Type'} (f : _93677 -> B) : (term590 _93677 B f) = (term578 _93677 B f).
Proof. exact (MK_COMB (@lem3658751 _93677) (@lem3658750 _93677 B f)). Qed.
Lemma lem3658753 {_93677 B : Type'} : (term591 _93677 B) = (term579 _93677 B).
Proof. exact (fun_ext (fun f : _93677 -> B => @lem3658752 _93677 B f)). Qed.
Lemma lem3658754 {_93677 B : Type'} : (@all (_93677 -> B)) = (@all (_93677 -> B)).
Proof. exact (eq_refl (@all (_93677 -> B))). Qed.
Lemma lem3658755 {_93677 B : Type'} : (term583 _93677 B) = (term580 _93677 B).
Proof. exact (MK_COMB (@lem3658754 _93677 B) (@lem3658753 _93677 B)). Qed.
Lemma lem3658756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658757 {_93677 B : Type'} : (term592 _93677 B) = (term593 _93677 B).
Proof. exact (MK_COMB (@lem3658756) (@lem3658755 _93677 B)). Qed.
Lemma lem3658758 {_93677 B : Type'} (f : _93677 -> B) : (term586 _93677 B f) = (term577 _93677 B f).
Proof. exact (eq_refl (term586 _93677 B f)). Qed.
Lemma lem3658759 {_93677 B : Type'} (x : type529 _93677 B) (f : _93677 -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem3658760 {_93677 B : Type'} (x : type529 _93677 B) (f : _93677 -> B) : (term594 _93677 B x f) = (term595 _93677 B x f).
Proof. exact (MK_COMB (@lem3658758 _93677 B f) (@lem3658759 _93677 B x f)). Qed.
Lemma lem3658761 {_93677 B : Type'} (x : type529 _93677 B) (f : _93677 -> B) : (term595 _93677 B x f) = (term596 _93677 B x f).
Proof. exact (eq_refl (term595 _93677 B x f)). Qed.
Lemma lem3658762 {_93677 B : Type'} (x : type529 _93677 B) (f : _93677 -> B) : (term594 _93677 B x f) = (term596 _93677 B x f).
Proof. exact (TRANS (@lem3658760 _93677 B x f) (@lem3658761 _93677 B x f)). Qed.
Lemma lem3658763 {_93677 B : Type'} (x : type529 _93677 B) : (term597 _93677 B x) = (term598 _93677 B x).
Proof. exact (fun_ext (fun f : _93677 -> B => @lem3658762 _93677 B x f)). Qed.
Lemma lem3658764 {_93677 B : Type'} : (@all (_93677 -> B)) = (@all (_93677 -> B)).
Proof. exact (eq_refl (@all (_93677 -> B))). Qed.
Lemma lem3658765 {_93677 B : Type'} (x : type529 _93677 B) : (term599 _93677 B x) = (term600 _93677 B x).
Proof. exact (MK_COMB (@lem3658764 _93677 B) (@lem3658763 _93677 B x)). Qed.
Lemma lem3658766 {_93677 B : Type'} : (term601 _93677 B) = (term602 _93677 B).
Proof. exact (fun_ext (fun x : type529 _93677 B => @lem3658765 _93677 B x)). Qed.
Lemma lem3658767 {_93677 B : Type'} : (@ex ((_93677 -> B) -> (_93677 -> Prop) -> _93677)) = (@ex ((_93677 -> B) -> (_93677 -> Prop) -> _93677)).
Proof. exact (eq_refl (@ex ((_93677 -> B) -> (_93677 -> Prop) -> _93677))). Qed.
Lemma lem3658768 {_93677 B : Type'} : (term584 _93677 B) = (term603 _93677 B).
Proof. exact (MK_COMB (@lem3658767 _93677 B) (@lem3658766 _93677 B)). Qed.
Lemma lem3658769 {_93677 B : Type'} : ((term583 _93677 B) = (term584 _93677 B)) = ((term580 _93677 B) = (term603 _93677 B)).
Proof. exact (MK_COMB (@lem3658757 _93677 B) (@lem3658768 _93677 B)). Qed.
Lemma lem3658770 {_93677 B : Type'} : (term580 _93677 B) = (term603 _93677 B).
Proof. exact (EQ_MP (@lem3658769 _93677 B) (@lem3658744 _93677 B)). Qed.
Lemma lem3658772 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3658773 {_93677 B : Type'} (P : type503 _93677 B) : (term581 _93677 B P) = (term582 _93677 B P).
Proof. exact (@lem3658772 (_93677 -> B) (type684 _93677) P). Qed.
Lemma lem3658774 {_93677 B : Type'} (x : type529 _93677 B) : (term604 _93677 B x) = (term605 _93677 B x).
Proof. exact (@lem3658773 _93677 B (term606 _93677 B x)). Qed.
Lemma lem3658775 {_93677 B : Type'} (x : type529 _93677 B) (f : _93677 -> B) : (term607 _93677 B x f) = (term608 _93677 B x f).
Proof. exact (eq_refl (term607 _93677 B x f)). Qed.
Lemma lem3658776 {_93677 : Type'} (y : type684 _93677) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3658777 {_93677 B : Type'} (x : type529 _93677 B) (f : _93677 -> B) (y : type684 _93677) : (term609 _93677 B x f y) = (term610 _93677 B x f y).
Proof. exact (MK_COMB (@lem3658775 _93677 B x f) (@lem3658776 _93677 y)). Qed.
Lemma lem3658778 {_93677 B : Type'} (x : type529 _93677 B) (y : type684 _93677) (f : _93677 -> B) : (term610 _93677 B x f y) = (term611 _93677 B x y f).
Proof. exact (eq_refl (term610 _93677 B x f y)). Qed.
Lemma lem3658779 {_93677 B : Type'} (x : type529 _93677 B) (y : type684 _93677) (f : _93677 -> B) : (term609 _93677 B x f y) = (term611 _93677 B x y f).
Proof. exact (TRANS (@lem3658777 _93677 B x f y) (@lem3658778 _93677 B x y f)). Qed.
Lemma lem3658780 {_93677 B : Type'} (x : type529 _93677 B) (f : _93677 -> B) : (term612 _93677 B x f) = (term608 _93677 B x f).
Proof. exact (fun_ext (fun y : type684 _93677 => @lem3658779 _93677 B x y f)). Qed.
Lemma lem3658781 {_93677 : Type'} : (@ex ((_93677 -> Prop) -> _93677)) = (@ex ((_93677 -> Prop) -> _93677)).
Proof. exact (eq_refl (@ex ((_93677 -> Prop) -> _93677))). Qed.
Lemma lem3658782 {_93677 B : Type'} (x : type529 _93677 B) (f : _93677 -> B) : (term613 _93677 B x f) = (term596 _93677 B x f).
Proof. exact (MK_COMB (@lem3658781 _93677) (@lem3658780 _93677 B x f)). Qed.
Lemma lem3658783 {_93677 B : Type'} (x : type529 _93677 B) : (term614 _93677 B x) = (term598 _93677 B x).
Proof. exact (fun_ext (fun f : _93677 -> B => @lem3658782 _93677 B x f)). Qed.
Lemma lem3658784 {_93677 B : Type'} : (@all (_93677 -> B)) = (@all (_93677 -> B)).
Proof. exact (eq_refl (@all (_93677 -> B))). Qed.
Lemma lem3658785 {_93677 B : Type'} (x : type529 _93677 B) : (term604 _93677 B x) = (term600 _93677 B x).
Proof. exact (MK_COMB (@lem3658784 _93677 B) (@lem3658783 _93677 B x)). Qed.
Lemma lem3658786 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658787 {_93677 B : Type'} (x : type529 _93677 B) : (term615 _93677 B x) = (term616 _93677 B x).
Proof. exact (MK_COMB (@lem3658786) (@lem3658785 _93677 B x)). Qed.
Lemma lem3658788 {_93677 B : Type'} (x : type529 _93677 B) (f : _93677 -> B) : (term607 _93677 B x f) = (term608 _93677 B x f).
Proof. exact (eq_refl (term607 _93677 B x f)). Qed.
Lemma lem3658789 {_93677 B : Type'} (y : type529 _93677 B) (f : _93677 -> B) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem3658790 {_93677 B : Type'} (x : type529 _93677 B) (y : type529 _93677 B) (f : _93677 -> B) : (term617 _93677 B x y f) = (term618 _93677 B x y f).
Proof. exact (MK_COMB (@lem3658788 _93677 B x f) (@lem3658789 _93677 B y f)). Qed.
Lemma lem3658791 {_93677 B : Type'} (x : type529 _93677 B) (y : type529 _93677 B) (f : _93677 -> B) : (term618 _93677 B x y f) = (term619 _93677 B x y f).
Proof. exact (eq_refl (term618 _93677 B x y f)). Qed.
Lemma lem3658792 {_93677 B : Type'} (x : type529 _93677 B) (y : type529 _93677 B) (f : _93677 -> B) : (term617 _93677 B x y f) = (term619 _93677 B x y f).
Proof. exact (TRANS (@lem3658790 _93677 B x y f) (@lem3658791 _93677 B x y f)). Qed.
Lemma lem3658793 {_93677 B : Type'} (x : type529 _93677 B) (y : type529 _93677 B) : (term620 _93677 B x y) = (term621 _93677 B x y).
Proof. exact (fun_ext (fun f : _93677 -> B => @lem3658792 _93677 B x y f)). Qed.
Lemma lem3658794 {_93677 B : Type'} : (@all (_93677 -> B)) = (@all (_93677 -> B)).
Proof. exact (eq_refl (@all (_93677 -> B))). Qed.
Lemma lem3658795 {_93677 B : Type'} (x : type529 _93677 B) (y : type529 _93677 B) : (term622 _93677 B x y) = (term623 _93677 B x y).
Proof. exact (MK_COMB (@lem3658794 _93677 B) (@lem3658793 _93677 B x y)). Qed.
Lemma lem3658796 {_93677 B : Type'} (x : type529 _93677 B) : (term624 _93677 B x) = (term625 _93677 B x).
Proof. exact (fun_ext (fun y : type529 _93677 B => @lem3658795 _93677 B x y)). Qed.
Lemma lem3658797 {_93677 B : Type'} : (@ex ((_93677 -> B) -> (_93677 -> Prop) -> _93677)) = (@ex ((_93677 -> B) -> (_93677 -> Prop) -> _93677)).
Proof. exact (eq_refl (@ex ((_93677 -> B) -> (_93677 -> Prop) -> _93677))). Qed.
Lemma lem3658798 {_93677 B : Type'} (x : type529 _93677 B) : (term605 _93677 B x) = (term626 _93677 B x).
Proof. exact (MK_COMB (@lem3658797 _93677 B) (@lem3658796 _93677 B x)). Qed.
Lemma lem3658799 {_93677 B : Type'} (x : type529 _93677 B) : ((term604 _93677 B x) = (term605 _93677 B x)) = ((term600 _93677 B x) = (term626 _93677 B x)).
Proof. exact (MK_COMB (@lem3658787 _93677 B x) (@lem3658798 _93677 B x)). Qed.
Lemma lem3658800 {_93677 B : Type'} (x : type529 _93677 B) : (term600 _93677 B x) = (term626 _93677 B x).
Proof. exact (EQ_MP (@lem3658799 _93677 B x) (@lem3658774 _93677 B x)). Qed.
Lemma lem3658801 {_93677 B : Type'} : (term602 _93677 B) = (term627 _93677 B).
Proof. exact (fun_ext (fun x : type529 _93677 B => @lem3658800 _93677 B x)). Qed.
Lemma lem3658802 {_93677 B : Type'} : (@ex ((_93677 -> B) -> (_93677 -> Prop) -> _93677)) = (@ex ((_93677 -> B) -> (_93677 -> Prop) -> _93677)).
Proof. exact (eq_refl (@ex ((_93677 -> B) -> (_93677 -> Prop) -> _93677))). Qed.
Lemma lem3658803 {_93677 B : Type'} : (term603 _93677 B) = (term628 _93677 B).
Proof. exact (MK_COMB (@lem3658802 _93677 B) (@lem3658801 _93677 B)). Qed.
Lemma lem3658804 {_93677 B : Type'} : (term580 _93677 B) = (term628 _93677 B).
Proof. exact (TRANS (@lem3658770 _93677 B) (@lem3658803 _93677 B)). Qed.
Lemma lem3658806 {_93677 B : Type'} : (term494 _93677 B) = (term628 _93677 B).
Proof. exact (TRANS (@lem3658740 _93677 B) (@lem3658804 _93677 B)). Qed.
Lemma lem3658807 {_93677 B : Type'} : (term82 _93677 B) = (term628 _93677 B).
Proof. exact (TRANS (@lem3658512 _93677 B) (@lem3658806 _93677 B)). Qed.
Lemma lem3658808 {_93677 B : Type'} (h1 : term82 _93677 B) : term628 _93677 B.
Proof. exact (EQ_MP (@lem3658807 _93677 B) (@lem3656893 _93677 B h1)). Qed.
Lemma lem3658823 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) (y : A) : (term629 _93670 A s f x y) = (term630 _93670 A s f x y).
Proof. exact (@lem17362 (term631 _93670 A s x f y) (x = y)). Qed.
Lemma lem3658824 {A : Type'} (P : A -> Prop) : (term163 A P) = (term164 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3658825 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term632 _93670 A s f x) = (term633 _93670 A s f x).
Proof. exact (@lem3658824 A (term120 _93670 A s f x)). Qed.
Lemma lem3658826 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) (y : A) : (term634 _93670 A s f x y) = (term119 _93670 A s f x y).
Proof. exact (eq_refl (term634 _93670 A s f x y)). Qed.
Lemma lem3658827 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3658828 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) (y : A) : (term635 _93670 A s f x y) = (term629 _93670 A s f x y).
Proof. exact (MK_COMB (@lem3658827) (@lem3658826 _93670 A s f x y)). Qed.
Lemma lem3658829 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) (y : A) : (term635 _93670 A s f x y) = (term630 _93670 A s f x y).
Proof. exact (TRANS (@lem3658828 _93670 A s f x y) (@lem3658823 _93670 A s f x y)). Qed.
Lemma lem3658830 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term636 _93670 A s f x) = (term637 _93670 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3658829 _93670 A s f x y)). Qed.
Lemma lem3658831 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3658832 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term633 _93670 A s f x) = (term638 _93670 A s f x).
Proof. exact (MK_COMB (@lem3658831 A) (@lem3658830 _93670 A s f x)). Qed.
Lemma lem3658833 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term632 _93670 A s f x) = (term638 _93670 A s f x).
Proof. exact (TRANS (@lem3658825 _93670 A s f x) (@lem3658832 _93670 A s f x)). Qed.
Lemma lem3658834 {A : Type'} (P : A -> Prop) : (term163 A P) = (term164 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3658835 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) : (term639 _93670 A s f) = (term640 _93670 A s f).
Proof. exact (@lem3658834 A (term122 _93670 A s f)). Qed.
Lemma lem3658836 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term641 _93670 A s f x) = (term121 _93670 A s f x).
Proof. exact (eq_refl (term641 _93670 A s f x)). Qed.
Lemma lem3658837 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3658838 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term642 _93670 A s f x) = (term632 _93670 A s f x).
Proof. exact (MK_COMB (@lem3658837) (@lem3658836 _93670 A s f x)). Qed.
Lemma lem3658839 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term642 _93670 A s f x) = (term638 _93670 A s f x).
Proof. exact (TRANS (@lem3658838 _93670 A s f x) (@lem3658833 _93670 A s f x)). Qed.
Lemma lem3658840 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) : (term643 _93670 A s f) = (term644 _93670 A s f).
Proof. exact (fun_ext (fun x : A => @lem3658839 _93670 A s f x)). Qed.
Lemma lem3658841 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3658842 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) : (term640 _93670 A s f) = (term645 _93670 A s f).
Proof. exact (MK_COMB (@lem3658841 A) (@lem3658840 _93670 A s f)). Qed.
Lemma lem3658843 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) : (term639 _93670 A s f) = (term645 _93670 A s f).
Proof. exact (TRANS (@lem3658835 _93670 A s f) (@lem3658842 _93670 A s f)). Qed.
Lemma lem3658858 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : ((term118 _93670 A f s) = (@FINITE A s)) = (term646 _93670 A f s).
Proof. exact (@lem17784 (term118 _93670 A f s) (@FINITE A s)). Qed.
Lemma lem3658859 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3658860 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) : (term647 _93670 A s f) = (term648 _93670 A s f).
Proof. exact (MK_COMB (@lem3658859) (@lem3658843 _93670 A s f)). Qed.
Lemma lem3658861 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term649 _93670 A f s) = (term650 _93670 A f s).
Proof. exact (MK_COMB (@lem3658860 _93670 A s f) (@lem3658858 _93670 A f s)). Qed.
Lemma lem3658862 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term125 _93670 A f s) = (term649 _93670 A f s).
Proof. exact (@lem17265 (term123 _93670 A s f) ((term118 _93670 A f s) = (@FINITE A s))). Qed.
Lemma lem3658863 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term125 _93670 A f s) = (term650 _93670 A f s).
Proof. exact (TRANS (@lem3658862 _93670 A f s) (@lem3658861 _93670 A f s)). Qed.
Lemma lem3658864 {_93670 A : Type'} (f : A -> _93670) : (term126 _93670 A f) = (term651 _93670 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3658863 _93670 A f s)). Qed.
Lemma lem3658865 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3658866 {_93670 A : Type'} (f : A -> _93670) : (term127 _93670 A f) = (term652 _93670 A f).
Proof. exact (MK_COMB (@lem3658865 A) (@lem3658864 _93670 A f)). Qed.
Lemma lem3658867 {_93670 A : Type'} : (term128 _93670 A) = (term653 _93670 A).
Proof. exact (fun_ext (fun f : A -> _93670 => @lem3658866 _93670 A f)). Qed.
Lemma lem3658868 {_93670 A : Type'} : (@all (A -> _93670)) = (@all (A -> _93670)).
Proof. exact (eq_refl (@all (A -> _93670))). Qed.
Lemma lem3658869 {_93670 A : Type'} : (term83 _93670 A) = (term654 _93670 A).
Proof. exact (MK_COMB (@lem3658868 _93670 A) (@lem3658867 _93670 A)). Qed.
Lemma lem3658976 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3658977 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (@lem3658976 A P Q). Qed.
Lemma lem3658978 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term655 _93670 A f s) = (term656 _93670 A f s).
Proof. exact (@lem3658977 A (term644 _93670 A s f) (term646 _93670 A f s)). Qed.
Lemma lem3658979 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term657 _93670 A s f x) = (term638 _93670 A s f x).
Proof. exact (eq_refl (term657 _93670 A s f x)). Qed.
Lemma lem3658980 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) : (term658 _93670 A s f) = (term644 _93670 A s f).
Proof. exact (fun_ext (fun x : A => @lem3658979 _93670 A s f x)). Qed.
Lemma lem3658981 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3658982 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) : (term659 _93670 A s f) = (term645 _93670 A s f).
Proof. exact (MK_COMB (@lem3658981 A) (@lem3658980 _93670 A s f)). Qed.
Lemma lem3658983 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3658984 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) : (term660 _93670 A s f) = (term648 _93670 A s f).
Proof. exact (MK_COMB (@lem3658983) (@lem3658982 _93670 A s f)). Qed.
Lemma lem3658985 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term646 _93670 A f s) = (term646 _93670 A f s).
Proof. exact (eq_refl (term646 _93670 A f s)). Qed.
Lemma lem3658986 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term655 _93670 A f s) = (term650 _93670 A f s).
Proof. exact (MK_COMB (@lem3658984 _93670 A s f) (@lem3658985 _93670 A f s)). Qed.
Lemma lem3658987 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3658988 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term661 _93670 A f s) = (term662 _93670 A f s).
Proof. exact (MK_COMB (@lem3658987) (@lem3658986 _93670 A f s)). Qed.
Lemma lem3658989 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term657 _93670 A s f x) = (term638 _93670 A s f x).
Proof. exact (eq_refl (term657 _93670 A s f x)). Qed.
Lemma lem3658990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3658991 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term663 _93670 A s f x) = (term664 _93670 A s f x).
Proof. exact (MK_COMB (@lem3658990) (@lem3658989 _93670 A s f x)). Qed.
Lemma lem3658992 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term646 _93670 A f s) = (term646 _93670 A f s).
Proof. exact (eq_refl (term646 _93670 A f s)). Qed.
Lemma lem3658993 {_93670 A : Type'} (x : A) (f : A -> _93670) (s : A -> Prop) : (term665 _93670 A x f s) = (term666 _93670 A x f s).
Proof. exact (MK_COMB (@lem3658991 _93670 A s f x) (@lem3658992 _93670 A f s)). Qed.
Lemma lem3658994 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term667 _93670 A f s) = (term668 _93670 A f s).
Proof. exact (fun_ext (fun x : A => @lem3658993 _93670 A x f s)). Qed.
Lemma lem3658995 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3658996 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term656 _93670 A f s) = (term669 _93670 A f s).
Proof. exact (MK_COMB (@lem3658995 A) (@lem3658994 _93670 A f s)). Qed.
Lemma lem3658997 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : ((term655 _93670 A f s) = (term656 _93670 A f s)) = ((term650 _93670 A f s) = (term669 _93670 A f s)).
Proof. exact (MK_COMB (@lem3658988 _93670 A f s) (@lem3658996 _93670 A f s)). Qed.
Lemma lem3658998 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term650 _93670 A f s) = (term669 _93670 A f s).
Proof. exact (EQ_MP (@lem3658997 _93670 A f s) (@lem3658978 _93670 A f s)). Qed.
Lemma lem3659000 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3659001 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (@lem3659000 A P Q). Qed.
Lemma lem3659002 {_93670 A : Type'} (x : A) (f : A -> _93670) (s : A -> Prop) : (term670 _93670 A x f s) = (term671 _93670 A x f s).
Proof. exact (@lem3659001 A (term637 _93670 A s f x) (term646 _93670 A f s)). Qed.
Lemma lem3659003 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) (y : A) : (term672 _93670 A s f x y) = (term630 _93670 A s f x y).
Proof. exact (eq_refl (term672 _93670 A s f x y)). Qed.
Lemma lem3659004 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term673 _93670 A s f x) = (term637 _93670 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3659003 _93670 A s f x y)). Qed.
Lemma lem3659005 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3659006 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term674 _93670 A s f x) = (term638 _93670 A s f x).
Proof. exact (MK_COMB (@lem3659005 A) (@lem3659004 _93670 A s f x)). Qed.
Lemma lem3659007 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3659008 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) : (term675 _93670 A s f x) = (term664 _93670 A s f x).
Proof. exact (MK_COMB (@lem3659007) (@lem3659006 _93670 A s f x)). Qed.
Lemma lem3659009 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term646 _93670 A f s) = (term646 _93670 A f s).
Proof. exact (eq_refl (term646 _93670 A f s)). Qed.
Lemma lem3659010 {_93670 A : Type'} (x : A) (f : A -> _93670) (s : A -> Prop) : (term670 _93670 A x f s) = (term666 _93670 A x f s).
Proof. exact (MK_COMB (@lem3659008 _93670 A s f x) (@lem3659009 _93670 A f s)). Qed.
Lemma lem3659011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3659012 {_93670 A : Type'} (x : A) (f : A -> _93670) (s : A -> Prop) : (term676 _93670 A x f s) = (term677 _93670 A x f s).
Proof. exact (MK_COMB (@lem3659011) (@lem3659010 _93670 A x f s)). Qed.
Lemma lem3659013 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) (y : A) : (term672 _93670 A s f x y) = (term630 _93670 A s f x y).
Proof. exact (eq_refl (term672 _93670 A s f x y)). Qed.
Lemma lem3659014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3659015 {_93670 A : Type'} (s : A -> Prop) (f : A -> _93670) (x : A) (y : A) : (term678 _93670 A s f x y) = (term679 _93670 A s f x y).
Proof. exact (MK_COMB (@lem3659014) (@lem3659013 _93670 A s f x y)). Qed.
Lemma lem3659016 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term646 _93670 A f s) = (term646 _93670 A f s).
Proof. exact (eq_refl (term646 _93670 A f s)). Qed.
Lemma lem3659017 {_93670 A : Type'} (x : A) (y : A) (f : A -> _93670) (s : A -> Prop) : (term680 _93670 A x y f s) = (term681 _93670 A x y f s).
Proof. exact (MK_COMB (@lem3659015 _93670 A s f x y) (@lem3659016 _93670 A f s)). Qed.
Lemma lem3659018 {_93670 A : Type'} (x : A) (f : A -> _93670) (s : A -> Prop) : (term682 _93670 A x f s) = (term683 _93670 A x f s).
Proof. exact (fun_ext (fun y : A => @lem3659017 _93670 A x y f s)). Qed.
Lemma lem3659019 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3659020 {_93670 A : Type'} (x : A) (f : A -> _93670) (s : A -> Prop) : (term671 _93670 A x f s) = (term684 _93670 A x f s).
Proof. exact (MK_COMB (@lem3659019 A) (@lem3659018 _93670 A x f s)). Qed.
Lemma lem3659021 {_93670 A : Type'} (x : A) (f : A -> _93670) (s : A -> Prop) : ((term670 _93670 A x f s) = (term671 _93670 A x f s)) = ((term666 _93670 A x f s) = (term684 _93670 A x f s)).
Proof. exact (MK_COMB (@lem3659012 _93670 A x f s) (@lem3659020 _93670 A x f s)). Qed.
Lemma lem3659022 {_93670 A : Type'} (x : A) (f : A -> _93670) (s : A -> Prop) : (term666 _93670 A x f s) = (term684 _93670 A x f s).
Proof. exact (EQ_MP (@lem3659021 _93670 A x f s) (@lem3659002 _93670 A x f s)). Qed.
Lemma lem3659023 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term668 _93670 A f s) = (term685 _93670 A f s).
Proof. exact (fun_ext (fun x : A => @lem3659022 _93670 A x f s)). Qed.
Lemma lem3659024 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3659025 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term669 _93670 A f s) = (term686 _93670 A f s).
Proof. exact (MK_COMB (@lem3659024 A) (@lem3659023 _93670 A f s)). Qed.
Lemma lem3659026 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term650 _93670 A f s) = (term686 _93670 A f s).
Proof. exact (TRANS (@lem3658998 _93670 A f s) (@lem3659025 _93670 A f s)). Qed.
Lemma lem3659027 {_93670 A : Type'} (f : A -> _93670) : (term651 _93670 A f) = (term687 _93670 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3659026 _93670 A f s)). Qed.
Lemma lem3659028 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3659029 {_93670 A : Type'} (f : A -> _93670) : (term652 _93670 A f) = (term688 _93670 A f).
Proof. exact (MK_COMB (@lem3659028 A) (@lem3659027 _93670 A f)). Qed.
Lemma lem3659031 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3659032 {A : Type'} (P : type672 A) : (term531 A P) = (term532 A P).
Proof. exact (@lem3659031 (A -> Prop) A P). Qed.
Lemma lem3659033 {_93670 A : Type'} (f : A -> _93670) : (term689 _93670 A f) = (term690 _93670 A f).
Proof. exact (@lem3659032 A (term691 _93670 A f)). Qed.
Lemma lem3659034 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term692 _93670 A f s) = (term685 _93670 A f s).
Proof. exact (eq_refl (term692 _93670 A f s)). Qed.
Lemma lem3659035 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3659036 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) (x : A) : (term693 _93670 A f s x) = (term694 _93670 A f s x).
Proof. exact (MK_COMB (@lem3659034 _93670 A f s) (@lem3659035 A x)). Qed.
Lemma lem3659037 {_93670 A : Type'} (x : A) (f : A -> _93670) (s : A -> Prop) : (term694 _93670 A f s x) = (term684 _93670 A x f s).
Proof. exact (eq_refl (term694 _93670 A f s x)). Qed.
Lemma lem3659038 {_93670 A : Type'} (x : A) (f : A -> _93670) (s : A -> Prop) : (term693 _93670 A f s x) = (term684 _93670 A x f s).
Proof. exact (TRANS (@lem3659036 _93670 A f s x) (@lem3659037 _93670 A x f s)). Qed.
Lemma lem3659039 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term695 _93670 A f s) = (term685 _93670 A f s).
Proof. exact (fun_ext (fun x : A => @lem3659038 _93670 A x f s)). Qed.
Lemma lem3659040 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3659041 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term696 _93670 A f s) = (term686 _93670 A f s).
Proof. exact (MK_COMB (@lem3659040 A) (@lem3659039 _93670 A f s)). Qed.
Lemma lem3659042 {_93670 A : Type'} (f : A -> _93670) : (term697 _93670 A f) = (term687 _93670 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3659041 _93670 A f s)). Qed.
Lemma lem3659043 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3659044 {_93670 A : Type'} (f : A -> _93670) : (term689 _93670 A f) = (term688 _93670 A f).
Proof. exact (MK_COMB (@lem3659043 A) (@lem3659042 _93670 A f)). Qed.
Lemma lem3659045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3659046 {_93670 A : Type'} (f : A -> _93670) : (term698 _93670 A f) = (term699 _93670 A f).
Proof. exact (MK_COMB (@lem3659045) (@lem3659044 _93670 A f)). Qed.
Lemma lem3659047 {_93670 A : Type'} (f : A -> _93670) (s : A -> Prop) : (term692 _93670 A f s) = (term685 _93670 A f s).
Proof. exact (eq_refl (term692 _93670 A f s)). Qed.
Lemma lem3659048 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3659049 {_93670 A : Type'} (f : A -> _93670) (x : type684 A) (s : A -> Prop) : (term700 _93670 A f x s) = (term701 _93670 A f x s).
Proof. exact (MK_COMB (@lem3659047 _93670 A f s) (@lem3659048 A x s)). Qed.
Lemma lem3659050 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) (s : A -> Prop) : (term701 _93670 A f x s) = (term702 _93670 A x f s).
Proof. exact (eq_refl (term701 _93670 A f x s)). Qed.
Lemma lem3659051 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) (s : A -> Prop) : (term700 _93670 A f x s) = (term702 _93670 A x f s).
Proof. exact (TRANS (@lem3659049 _93670 A f x s) (@lem3659050 _93670 A x f s)). Qed.
Lemma lem3659052 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) : (term703 _93670 A f x) = (term704 _93670 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3659051 _93670 A x f s)). Qed.
Lemma lem3659053 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3659054 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) : (term705 _93670 A f x) = (term706 _93670 A x f).
Proof. exact (MK_COMB (@lem3659053 A) (@lem3659052 _93670 A x f)). Qed.
Lemma lem3659055 {_93670 A : Type'} (f : A -> _93670) : (term707 _93670 A f) = (term708 _93670 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem3659054 _93670 A x f)). Qed.
Lemma lem3659056 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3659057 {_93670 A : Type'} (f : A -> _93670) : (term690 _93670 A f) = (term709 _93670 A f).
Proof. exact (MK_COMB (@lem3659056 A) (@lem3659055 _93670 A f)). Qed.
Lemma lem3659058 {_93670 A : Type'} (f : A -> _93670) : ((term689 _93670 A f) = (term690 _93670 A f)) = ((term688 _93670 A f) = (term709 _93670 A f)).
Proof. exact (MK_COMB (@lem3659046 _93670 A f) (@lem3659057 _93670 A f)). Qed.
Lemma lem3659059 {_93670 A : Type'} (f : A -> _93670) : (term688 _93670 A f) = (term709 _93670 A f).
Proof. exact (EQ_MP (@lem3659058 _93670 A f) (@lem3659033 _93670 A f)). Qed.
Lemma lem3659061 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3659062 {A : Type'} (P : type672 A) : (term531 A P) = (term532 A P).
Proof. exact (@lem3659061 (A -> Prop) A P). Qed.
Lemma lem3659063 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) : (term710 _93670 A x f) = (term711 _93670 A x f).
Proof. exact (@lem3659062 A (term712 _93670 A x f)). Qed.
Lemma lem3659064 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) (s : A -> Prop) : (term713 _93670 A x f s) = (term714 _93670 A x f s).
Proof. exact (eq_refl (term713 _93670 A x f s)). Qed.
Lemma lem3659065 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3659066 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) (s : A -> Prop) (y : A) : (term715 _93670 A x f s y) = (term716 _93670 A x f s y).
Proof. exact (MK_COMB (@lem3659064 _93670 A x f s) (@lem3659065 A y)). Qed.
Lemma lem3659067 {_93670 A : Type'} (x : type684 A) (y : A) (f : A -> _93670) (s : A -> Prop) : (term716 _93670 A x f s y) = (term717 _93670 A x y f s).
Proof. exact (eq_refl (term716 _93670 A x f s y)). Qed.
Lemma lem3659068 {_93670 A : Type'} (x : type684 A) (y : A) (f : A -> _93670) (s : A -> Prop) : (term715 _93670 A x f s y) = (term717 _93670 A x y f s).
Proof. exact (TRANS (@lem3659066 _93670 A x f s y) (@lem3659067 _93670 A x y f s)). Qed.
Lemma lem3659069 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) (s : A -> Prop) : (term718 _93670 A x f s) = (term714 _93670 A x f s).
Proof. exact (fun_ext (fun y : A => @lem3659068 _93670 A x y f s)). Qed.
Lemma lem3659070 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3659071 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) (s : A -> Prop) : (term719 _93670 A x f s) = (term702 _93670 A x f s).
Proof. exact (MK_COMB (@lem3659070 A) (@lem3659069 _93670 A x f s)). Qed.
Lemma lem3659072 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) : (term720 _93670 A x f) = (term704 _93670 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3659071 _93670 A x f s)). Qed.
Lemma lem3659073 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3659074 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) : (term710 _93670 A x f) = (term706 _93670 A x f).
Proof. exact (MK_COMB (@lem3659073 A) (@lem3659072 _93670 A x f)). Qed.
Lemma lem3659075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3659076 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) : (term721 _93670 A x f) = (term722 _93670 A x f).
Proof. exact (MK_COMB (@lem3659075) (@lem3659074 _93670 A x f)). Qed.
Lemma lem3659077 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) (s : A -> Prop) : (term713 _93670 A x f s) = (term714 _93670 A x f s).
Proof. exact (eq_refl (term713 _93670 A x f s)). Qed.
Lemma lem3659078 {A : Type'} (y : type684 A) (s : A -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem3659079 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) (y : type684 A) (s : A -> Prop) : (term723 _93670 A x f y s) = (term724 _93670 A x f y s).
Proof. exact (MK_COMB (@lem3659077 _93670 A x f s) (@lem3659078 A y s)). Qed.
Lemma lem3659080 {_93670 A : Type'} (x : type684 A) (y : type684 A) (f : A -> _93670) (s : A -> Prop) : (term724 _93670 A x f y s) = (term725 _93670 A x y f s).
Proof. exact (eq_refl (term724 _93670 A x f y s)). Qed.
Lemma lem3659081 {_93670 A : Type'} (x : type684 A) (y : type684 A) (f : A -> _93670) (s : A -> Prop) : (term723 _93670 A x f y s) = (term725 _93670 A x y f s).
Proof. exact (TRANS (@lem3659079 _93670 A x f y s) (@lem3659080 _93670 A x y f s)). Qed.
Lemma lem3659082 {_93670 A : Type'} (x : type684 A) (y : type684 A) (f : A -> _93670) : (term726 _93670 A x f y) = (term727 _93670 A x y f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3659081 _93670 A x y f s)). Qed.
Lemma lem3659083 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3659084 {_93670 A : Type'} (x : type684 A) (y : type684 A) (f : A -> _93670) : (term728 _93670 A x f y) = (term729 _93670 A x y f).
Proof. exact (MK_COMB (@lem3659083 A) (@lem3659082 _93670 A x y f)). Qed.
Lemma lem3659085 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) : (term730 _93670 A x f) = (term731 _93670 A x f).
Proof. exact (fun_ext (fun y : type684 A => @lem3659084 _93670 A x y f)). Qed.
Lemma lem3659086 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3659087 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) : (term711 _93670 A x f) = (term732 _93670 A x f).
Proof. exact (MK_COMB (@lem3659086 A) (@lem3659085 _93670 A x f)). Qed.
Lemma lem3659088 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) : ((term710 _93670 A x f) = (term711 _93670 A x f)) = ((term706 _93670 A x f) = (term732 _93670 A x f)).
Proof. exact (MK_COMB (@lem3659076 _93670 A x f) (@lem3659087 _93670 A x f)). Qed.
Lemma lem3659089 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) : (term706 _93670 A x f) = (term732 _93670 A x f).
Proof. exact (EQ_MP (@lem3659088 _93670 A x f) (@lem3659063 _93670 A x f)). Qed.
Lemma lem3659090 {_93670 A : Type'} (f : A -> _93670) : (term708 _93670 A f) = (term733 _93670 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem3659089 _93670 A x f)). Qed.
Lemma lem3659091 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3659092 {_93670 A : Type'} (f : A -> _93670) : (term709 _93670 A f) = (term734 _93670 A f).
Proof. exact (MK_COMB (@lem3659091 A) (@lem3659090 _93670 A f)). Qed.
Lemma lem3659093 {_93670 A : Type'} (f : A -> _93670) : (term688 _93670 A f) = (term734 _93670 A f).
Proof. exact (TRANS (@lem3659059 _93670 A f) (@lem3659092 _93670 A f)). Qed.
Lemma lem3659094 {_93670 A : Type'} (f : A -> _93670) : (term652 _93670 A f) = (term734 _93670 A f).
Proof. exact (TRANS (@lem3659029 _93670 A f) (@lem3659093 _93670 A f)). Qed.
Lemma lem3659095 {_93670 A : Type'} : (term653 _93670 A) = (term735 _93670 A).
Proof. exact (fun_ext (fun f : A -> _93670 => @lem3659094 _93670 A f)). Qed.
Lemma lem3659096 {_93670 A : Type'} : (@all (A -> _93670)) = (@all (A -> _93670)).
Proof. exact (eq_refl (@all (A -> _93670))). Qed.
Lemma lem3659097 {_93670 A : Type'} : (term654 _93670 A) = (term736 _93670 A).
Proof. exact (MK_COMB (@lem3659096 _93670 A) (@lem3659095 _93670 A)). Qed.
Lemma lem3659099 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3659100 {_93670 A : Type'} (P : type776 _93670 A) : (term737 _93670 A P) = (term738 _93670 A P).
Proof. exact (@lem3659099 (A -> _93670) (type684 A) P). Qed.
Lemma lem3659101 {_93670 A : Type'} : (term739 _93670 A) = (term740 _93670 A).
Proof. exact (@lem3659100 _93670 A (term741 _93670 A)). Qed.
Lemma lem3659102 {_93670 A : Type'} (f : A -> _93670) : (term742 _93670 A f) = (term733 _93670 A f).
Proof. exact (eq_refl (term742 _93670 A f)). Qed.
Lemma lem3659103 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3659104 {_93670 A : Type'} (f : A -> _93670) (x : type684 A) : (term743 _93670 A f x) = (term744 _93670 A f x).
Proof. exact (MK_COMB (@lem3659102 _93670 A f) (@lem3659103 A x)). Qed.
Lemma lem3659105 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) : (term744 _93670 A f x) = (term732 _93670 A x f).
Proof. exact (eq_refl (term744 _93670 A f x)). Qed.
Lemma lem3659106 {_93670 A : Type'} (x : type684 A) (f : A -> _93670) : (term743 _93670 A f x) = (term732 _93670 A x f).
Proof. exact (TRANS (@lem3659104 _93670 A f x) (@lem3659105 _93670 A x f)). Qed.
Lemma lem3659107 {_93670 A : Type'} (f : A -> _93670) : (term745 _93670 A f) = (term733 _93670 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem3659106 _93670 A x f)). Qed.
Lemma lem3659108 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3659109 {_93670 A : Type'} (f : A -> _93670) : (term746 _93670 A f) = (term734 _93670 A f).
Proof. exact (MK_COMB (@lem3659108 A) (@lem3659107 _93670 A f)). Qed.
Lemma lem3659110 {_93670 A : Type'} : (term747 _93670 A) = (term735 _93670 A).
Proof. exact (fun_ext (fun f : A -> _93670 => @lem3659109 _93670 A f)). Qed.
Lemma lem3659111 {_93670 A : Type'} : (@all (A -> _93670)) = (@all (A -> _93670)).
Proof. exact (eq_refl (@all (A -> _93670))). Qed.
Lemma lem3659112 {_93670 A : Type'} : (term739 _93670 A) = (term736 _93670 A).
Proof. exact (MK_COMB (@lem3659111 _93670 A) (@lem3659110 _93670 A)). Qed.
Lemma lem3659113 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3659114 {_93670 A : Type'} : (term748 _93670 A) = (term749 _93670 A).
Proof. exact (MK_COMB (@lem3659113) (@lem3659112 _93670 A)). Qed.
Lemma lem3659115 {_93670 A : Type'} (f : A -> _93670) : (term742 _93670 A f) = (term733 _93670 A f).
Proof. exact (eq_refl (term742 _93670 A f)). Qed.
Lemma lem3659116 {_93670 A : Type'} (x : type791 _93670 A) (f : A -> _93670) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem3659117 {_93670 A : Type'} (x : type791 _93670 A) (f : A -> _93670) : (term750 _93670 A x f) = (term751 _93670 A x f).
Proof. exact (MK_COMB (@lem3659115 _93670 A f) (@lem3659116 _93670 A x f)). Qed.
Lemma lem3659118 {_93670 A : Type'} (x : type791 _93670 A) (f : A -> _93670) : (term751 _93670 A x f) = (term752 _93670 A x f).
Proof. exact (eq_refl (term751 _93670 A x f)). Qed.
Lemma lem3659119 {_93670 A : Type'} (x : type791 _93670 A) (f : A -> _93670) : (term750 _93670 A x f) = (term752 _93670 A x f).
Proof. exact (TRANS (@lem3659117 _93670 A x f) (@lem3659118 _93670 A x f)). Qed.
Lemma lem3659120 {_93670 A : Type'} (x : type791 _93670 A) : (term753 _93670 A x) = (term754 _93670 A x).
Proof. exact (fun_ext (fun f : A -> _93670 => @lem3659119 _93670 A x f)). Qed.
Lemma lem3659121 {_93670 A : Type'} : (@all (A -> _93670)) = (@all (A -> _93670)).
Proof. exact (eq_refl (@all (A -> _93670))). Qed.
Lemma lem3659122 {_93670 A : Type'} (x : type791 _93670 A) : (term755 _93670 A x) = (term756 _93670 A x).
Proof. exact (MK_COMB (@lem3659121 _93670 A) (@lem3659120 _93670 A x)). Qed.
Lemma lem3659123 {_93670 A : Type'} : (term757 _93670 A) = (term758 _93670 A).
Proof. exact (fun_ext (fun x : type791 _93670 A => @lem3659122 _93670 A x)). Qed.
Lemma lem3659124 {_93670 A : Type'} : (@ex ((A -> _93670) -> (A -> Prop) -> A)) = (@ex ((A -> _93670) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> _93670) -> (A -> Prop) -> A))). Qed.
Lemma lem3659125 {_93670 A : Type'} : (term740 _93670 A) = (term759 _93670 A).
Proof. exact (MK_COMB (@lem3659124 _93670 A) (@lem3659123 _93670 A)). Qed.
Lemma lem3659126 {_93670 A : Type'} : ((term739 _93670 A) = (term740 _93670 A)) = ((term736 _93670 A) = (term759 _93670 A)).
Proof. exact (MK_COMB (@lem3659114 _93670 A) (@lem3659125 _93670 A)). Qed.
Lemma lem3659127 {_93670 A : Type'} : (term736 _93670 A) = (term759 _93670 A).
Proof. exact (EQ_MP (@lem3659126 _93670 A) (@lem3659101 _93670 A)). Qed.
Lemma lem3659129 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3659130 {_93670 A : Type'} (P : type776 _93670 A) : (term737 _93670 A P) = (term738 _93670 A P).
Proof. exact (@lem3659129 (A -> _93670) (type684 A) P). Qed.
Lemma lem3659131 {_93670 A : Type'} (x : type791 _93670 A) : (term760 _93670 A x) = (term761 _93670 A x).
Proof. exact (@lem3659130 _93670 A (term762 _93670 A x)). Qed.
Lemma lem3659132 {_93670 A : Type'} (x : type791 _93670 A) (f : A -> _93670) : (term763 _93670 A x f) = (term764 _93670 A x f).
Proof. exact (eq_refl (term763 _93670 A x f)). Qed.
Lemma lem3659133 {A : Type'} (y : type684 A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3659134 {_93670 A : Type'} (x : type791 _93670 A) (f : A -> _93670) (y : type684 A) : (term765 _93670 A x f y) = (term766 _93670 A x f y).
Proof. exact (MK_COMB (@lem3659132 _93670 A x f) (@lem3659133 A y)). Qed.
Lemma lem3659135 {_93670 A : Type'} (x : type791 _93670 A) (y : type684 A) (f : A -> _93670) : (term766 _93670 A x f y) = (term767 _93670 A x y f).
Proof. exact (eq_refl (term766 _93670 A x f y)). Qed.
Lemma lem3659136 {_93670 A : Type'} (x : type791 _93670 A) (y : type684 A) (f : A -> _93670) : (term765 _93670 A x f y) = (term767 _93670 A x y f).
Proof. exact (TRANS (@lem3659134 _93670 A x f y) (@lem3659135 _93670 A x y f)). Qed.
Lemma lem3659137 {_93670 A : Type'} (x : type791 _93670 A) (f : A -> _93670) : (term768 _93670 A x f) = (term764 _93670 A x f).
Proof. exact (fun_ext (fun y : type684 A => @lem3659136 _93670 A x y f)). Qed.
Lemma lem3659138 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3659139 {_93670 A : Type'} (x : type791 _93670 A) (f : A -> _93670) : (term769 _93670 A x f) = (term752 _93670 A x f).
Proof. exact (MK_COMB (@lem3659138 A) (@lem3659137 _93670 A x f)). Qed.
Lemma lem3659140 {_93670 A : Type'} (x : type791 _93670 A) : (term770 _93670 A x) = (term754 _93670 A x).
Proof. exact (fun_ext (fun f : A -> _93670 => @lem3659139 _93670 A x f)). Qed.
Lemma lem3659141 {_93670 A : Type'} : (@all (A -> _93670)) = (@all (A -> _93670)).
Proof. exact (eq_refl (@all (A -> _93670))). Qed.
Lemma lem3659142 {_93670 A : Type'} (x : type791 _93670 A) : (term760 _93670 A x) = (term756 _93670 A x).
Proof. exact (MK_COMB (@lem3659141 _93670 A) (@lem3659140 _93670 A x)). Qed.
Lemma lem3659143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3659144 {_93670 A : Type'} (x : type791 _93670 A) : (term771 _93670 A x) = (term772 _93670 A x).
Proof. exact (MK_COMB (@lem3659143) (@lem3659142 _93670 A x)). Qed.
Lemma lem3659145 {_93670 A : Type'} (x : type791 _93670 A) (f : A -> _93670) : (term763 _93670 A x f) = (term764 _93670 A x f).
Proof. exact (eq_refl (term763 _93670 A x f)). Qed.
Lemma lem3659146 {_93670 A : Type'} (y : type791 _93670 A) (f : A -> _93670) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem3659147 {_93670 A : Type'} (x : type791 _93670 A) (y : type791 _93670 A) (f : A -> _93670) : (term773 _93670 A x y f) = (term774 _93670 A x y f).
Proof. exact (MK_COMB (@lem3659145 _93670 A x f) (@lem3659146 _93670 A y f)). Qed.
Lemma lem3659148 {_93670 A : Type'} (x : type791 _93670 A) (y : type791 _93670 A) (f : A -> _93670) : (term774 _93670 A x y f) = (term775 _93670 A x y f).
Proof. exact (eq_refl (term774 _93670 A x y f)). Qed.
Lemma lem3659149 {_93670 A : Type'} (x : type791 _93670 A) (y : type791 _93670 A) (f : A -> _93670) : (term773 _93670 A x y f) = (term775 _93670 A x y f).
Proof. exact (TRANS (@lem3659147 _93670 A x y f) (@lem3659148 _93670 A x y f)). Qed.
Lemma lem3659150 {_93670 A : Type'} (x : type791 _93670 A) (y : type791 _93670 A) : (term776 _93670 A x y) = (term777 _93670 A x y).
Proof. exact (fun_ext (fun f : A -> _93670 => @lem3659149 _93670 A x y f)). Qed.
Lemma lem3659151 {_93670 A : Type'} : (@all (A -> _93670)) = (@all (A -> _93670)).
Proof. exact (eq_refl (@all (A -> _93670))). Qed.
Lemma lem3659152 {_93670 A : Type'} (x : type791 _93670 A) (y : type791 _93670 A) : (term778 _93670 A x y) = (term779 _93670 A x y).
Proof. exact (MK_COMB (@lem3659151 _93670 A) (@lem3659150 _93670 A x y)). Qed.
Lemma lem3659153 {_93670 A : Type'} (x : type791 _93670 A) : (term780 _93670 A x) = (term781 _93670 A x).
Proof. exact (fun_ext (fun y : type791 _93670 A => @lem3659152 _93670 A x y)). Qed.
Lemma lem3659154 {_93670 A : Type'} : (@ex ((A -> _93670) -> (A -> Prop) -> A)) = (@ex ((A -> _93670) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> _93670) -> (A -> Prop) -> A))). Qed.
Lemma lem3659155 {_93670 A : Type'} (x : type791 _93670 A) : (term761 _93670 A x) = (term782 _93670 A x).
Proof. exact (MK_COMB (@lem3659154 _93670 A) (@lem3659153 _93670 A x)). Qed.
Lemma lem3659156 {_93670 A : Type'} (x : type791 _93670 A) : ((term760 _93670 A x) = (term761 _93670 A x)) = ((term756 _93670 A x) = (term782 _93670 A x)).
Proof. exact (MK_COMB (@lem3659144 _93670 A x) (@lem3659155 _93670 A x)). Qed.
Lemma lem3659157 {_93670 A : Type'} (x : type791 _93670 A) : (term756 _93670 A x) = (term782 _93670 A x).
Proof. exact (EQ_MP (@lem3659156 _93670 A x) (@lem3659131 _93670 A x)). Qed.
Lemma lem3659158 {_93670 A : Type'} : (term758 _93670 A) = (term783 _93670 A).
Proof. exact (fun_ext (fun x : type791 _93670 A => @lem3659157 _93670 A x)). Qed.
Lemma lem3659159 {_93670 A : Type'} : (@ex ((A -> _93670) -> (A -> Prop) -> A)) = (@ex ((A -> _93670) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> _93670) -> (A -> Prop) -> A))). Qed.
Lemma lem3659160 {_93670 A : Type'} : (term759 _93670 A) = (term784 _93670 A).
Proof. exact (MK_COMB (@lem3659159 _93670 A) (@lem3659158 _93670 A)). Qed.
Lemma lem3659161 {_93670 A : Type'} : (term736 _93670 A) = (term784 _93670 A).
Proof. exact (TRANS (@lem3659127 _93670 A) (@lem3659160 _93670 A)). Qed.
Lemma lem3659163 {_93670 A : Type'} : (term654 _93670 A) = (term784 _93670 A).
Proof. exact (TRANS (@lem3659097 _93670 A) (@lem3659161 _93670 A)). Qed.
Lemma lem3659164 {_93670 A : Type'} : (term83 _93670 A) = (term784 _93670 A).
Proof. exact (TRANS (@lem3658869 _93670 A) (@lem3659163 _93670 A)). Qed.
Lemma lem3659165 {_93670 A : Type'} (h1 : term83 _93670 A) : term784 _93670 A.
Proof. exact (EQ_MP (@lem3659164 _93670 A) (@lem3656894 _93670 A h1)). Qed.
Lemma lem3659180 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) (y : A) : (term629 _93677 A s f x y) = (term630 _93677 A s f x y).
Proof. exact (@lem17362 (term631 _93677 A s x f y) (x = y)). Qed.
Lemma lem3659181 {A : Type'} (P : A -> Prop) : (term163 A P) = (term164 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3659182 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term632 _93677 A s f x) = (term633 _93677 A s f x).
Proof. exact (@lem3659181 A (term120 _93677 A s f x)). Qed.
Lemma lem3659183 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) (y : A) : (term634 _93677 A s f x y) = (term119 _93677 A s f x y).
Proof. exact (eq_refl (term634 _93677 A s f x y)). Qed.
Lemma lem3659184 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3659185 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) (y : A) : (term635 _93677 A s f x y) = (term629 _93677 A s f x y).
Proof. exact (MK_COMB (@lem3659184) (@lem3659183 _93677 A s f x y)). Qed.
Lemma lem3659186 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) (y : A) : (term635 _93677 A s f x y) = (term630 _93677 A s f x y).
Proof. exact (TRANS (@lem3659185 _93677 A s f x y) (@lem3659180 _93677 A s f x y)). Qed.
Lemma lem3659187 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term636 _93677 A s f x) = (term637 _93677 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3659186 _93677 A s f x y)). Qed.
Lemma lem3659188 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3659189 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term633 _93677 A s f x) = (term638 _93677 A s f x).
Proof. exact (MK_COMB (@lem3659188 A) (@lem3659187 _93677 A s f x)). Qed.
Lemma lem3659190 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term632 _93677 A s f x) = (term638 _93677 A s f x).
Proof. exact (TRANS (@lem3659182 _93677 A s f x) (@lem3659189 _93677 A s f x)). Qed.
Lemma lem3659191 {A : Type'} (P : A -> Prop) : (term163 A P) = (term164 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3659192 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) : (term639 _93677 A s f) = (term640 _93677 A s f).
Proof. exact (@lem3659191 A (term122 _93677 A s f)). Qed.
Lemma lem3659193 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term641 _93677 A s f x) = (term121 _93677 A s f x).
Proof. exact (eq_refl (term641 _93677 A s f x)). Qed.
Lemma lem3659194 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3659195 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term642 _93677 A s f x) = (term632 _93677 A s f x).
Proof. exact (MK_COMB (@lem3659194) (@lem3659193 _93677 A s f x)). Qed.
Lemma lem3659196 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term642 _93677 A s f x) = (term638 _93677 A s f x).
Proof. exact (TRANS (@lem3659195 _93677 A s f x) (@lem3659190 _93677 A s f x)). Qed.
Lemma lem3659197 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) : (term643 _93677 A s f) = (term644 _93677 A s f).
Proof. exact (fun_ext (fun x : A => @lem3659196 _93677 A s f x)). Qed.
Lemma lem3659198 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3659199 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) : (term640 _93677 A s f) = (term645 _93677 A s f).
Proof. exact (MK_COMB (@lem3659198 A) (@lem3659197 _93677 A s f)). Qed.
Lemma lem3659200 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) : (term639 _93677 A s f) = (term645 _93677 A s f).
Proof. exact (TRANS (@lem3659192 _93677 A s f) (@lem3659199 _93677 A s f)). Qed.
Lemma lem3659215 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : ((term118 _93677 A f s) = (@FINITE A s)) = (term646 _93677 A f s).
Proof. exact (@lem17784 (term118 _93677 A f s) (@FINITE A s)). Qed.
Lemma lem3659216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3659217 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) : (term647 _93677 A s f) = (term648 _93677 A s f).
Proof. exact (MK_COMB (@lem3659216) (@lem3659200 _93677 A s f)). Qed.
Lemma lem3659218 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term649 _93677 A f s) = (term650 _93677 A f s).
Proof. exact (MK_COMB (@lem3659217 _93677 A s f) (@lem3659215 _93677 A f s)). Qed.
Lemma lem3659219 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term125 _93677 A f s) = (term649 _93677 A f s).
Proof. exact (@lem17265 (term123 _93677 A s f) ((term118 _93677 A f s) = (@FINITE A s))). Qed.
Lemma lem3659220 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term125 _93677 A f s) = (term650 _93677 A f s).
Proof. exact (TRANS (@lem3659219 _93677 A f s) (@lem3659218 _93677 A f s)). Qed.
Lemma lem3659221 {_93677 A : Type'} (f : A -> _93677) : (term126 _93677 A f) = (term651 _93677 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3659220 _93677 A f s)). Qed.
Lemma lem3659222 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3659223 {_93677 A : Type'} (f : A -> _93677) : (term127 _93677 A f) = (term652 _93677 A f).
Proof. exact (MK_COMB (@lem3659222 A) (@lem3659221 _93677 A f)). Qed.
Lemma lem3659224 {_93677 A : Type'} : (term128 _93677 A) = (term653 _93677 A).
Proof. exact (fun_ext (fun f : A -> _93677 => @lem3659223 _93677 A f)). Qed.
Lemma lem3659225 {_93677 A : Type'} : (@all (A -> _93677)) = (@all (A -> _93677)).
Proof. exact (eq_refl (@all (A -> _93677))). Qed.
Lemma lem3659226 {_93677 A : Type'} : (term83 _93677 A) = (term654 _93677 A).
Proof. exact (MK_COMB (@lem3659225 _93677 A) (@lem3659224 _93677 A)). Qed.
Lemma lem3659333 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3659334 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (@lem3659333 A P Q). Qed.
Lemma lem3659335 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term655 _93677 A f s) = (term656 _93677 A f s).
Proof. exact (@lem3659334 A (term644 _93677 A s f) (term646 _93677 A f s)). Qed.
Lemma lem3659336 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term657 _93677 A s f x) = (term638 _93677 A s f x).
Proof. exact (eq_refl (term657 _93677 A s f x)). Qed.
Lemma lem3659337 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) : (term658 _93677 A s f) = (term644 _93677 A s f).
Proof. exact (fun_ext (fun x : A => @lem3659336 _93677 A s f x)). Qed.
Lemma lem3659338 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3659339 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) : (term659 _93677 A s f) = (term645 _93677 A s f).
Proof. exact (MK_COMB (@lem3659338 A) (@lem3659337 _93677 A s f)). Qed.
Lemma lem3659340 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3659341 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) : (term660 _93677 A s f) = (term648 _93677 A s f).
Proof. exact (MK_COMB (@lem3659340) (@lem3659339 _93677 A s f)). Qed.
Lemma lem3659342 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term646 _93677 A f s) = (term646 _93677 A f s).
Proof. exact (eq_refl (term646 _93677 A f s)). Qed.
Lemma lem3659343 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term655 _93677 A f s) = (term650 _93677 A f s).
Proof. exact (MK_COMB (@lem3659341 _93677 A s f) (@lem3659342 _93677 A f s)). Qed.
Lemma lem3659344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3659345 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term661 _93677 A f s) = (term662 _93677 A f s).
Proof. exact (MK_COMB (@lem3659344) (@lem3659343 _93677 A f s)). Qed.
Lemma lem3659346 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term657 _93677 A s f x) = (term638 _93677 A s f x).
Proof. exact (eq_refl (term657 _93677 A s f x)). Qed.
Lemma lem3659347 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3659348 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term663 _93677 A s f x) = (term664 _93677 A s f x).
Proof. exact (MK_COMB (@lem3659347) (@lem3659346 _93677 A s f x)). Qed.
Lemma lem3659349 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term646 _93677 A f s) = (term646 _93677 A f s).
Proof. exact (eq_refl (term646 _93677 A f s)). Qed.
Lemma lem3659350 {_93677 A : Type'} (x : A) (f : A -> _93677) (s : A -> Prop) : (term665 _93677 A x f s) = (term666 _93677 A x f s).
Proof. exact (MK_COMB (@lem3659348 _93677 A s f x) (@lem3659349 _93677 A f s)). Qed.
Lemma lem3659351 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term667 _93677 A f s) = (term668 _93677 A f s).
Proof. exact (fun_ext (fun x : A => @lem3659350 _93677 A x f s)). Qed.
Lemma lem3659352 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3659353 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term656 _93677 A f s) = (term669 _93677 A f s).
Proof. exact (MK_COMB (@lem3659352 A) (@lem3659351 _93677 A f s)). Qed.
Lemma lem3659354 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : ((term655 _93677 A f s) = (term656 _93677 A f s)) = ((term650 _93677 A f s) = (term669 _93677 A f s)).
Proof. exact (MK_COMB (@lem3659345 _93677 A f s) (@lem3659353 _93677 A f s)). Qed.
Lemma lem3659355 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term650 _93677 A f s) = (term669 _93677 A f s).
Proof. exact (EQ_MP (@lem3659354 _93677 A f s) (@lem3659335 _93677 A f s)). Qed.
Lemma lem3659357 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3659358 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (@lem3659357 A P Q). Qed.
Lemma lem3659359 {_93677 A : Type'} (x : A) (f : A -> _93677) (s : A -> Prop) : (term670 _93677 A x f s) = (term671 _93677 A x f s).
Proof. exact (@lem3659358 A (term637 _93677 A s f x) (term646 _93677 A f s)). Qed.
Lemma lem3659360 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) (y : A) : (term672 _93677 A s f x y) = (term630 _93677 A s f x y).
Proof. exact (eq_refl (term672 _93677 A s f x y)). Qed.
Lemma lem3659361 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term673 _93677 A s f x) = (term637 _93677 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3659360 _93677 A s f x y)). Qed.
Lemma lem3659362 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3659363 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term674 _93677 A s f x) = (term638 _93677 A s f x).
Proof. exact (MK_COMB (@lem3659362 A) (@lem3659361 _93677 A s f x)). Qed.
Lemma lem3659364 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3659365 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) : (term675 _93677 A s f x) = (term664 _93677 A s f x).
Proof. exact (MK_COMB (@lem3659364) (@lem3659363 _93677 A s f x)). Qed.
Lemma lem3659366 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term646 _93677 A f s) = (term646 _93677 A f s).
Proof. exact (eq_refl (term646 _93677 A f s)). Qed.
Lemma lem3659367 {_93677 A : Type'} (x : A) (f : A -> _93677) (s : A -> Prop) : (term670 _93677 A x f s) = (term666 _93677 A x f s).
Proof. exact (MK_COMB (@lem3659365 _93677 A s f x) (@lem3659366 _93677 A f s)). Qed.
Lemma lem3659368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3659369 {_93677 A : Type'} (x : A) (f : A -> _93677) (s : A -> Prop) : (term676 _93677 A x f s) = (term677 _93677 A x f s).
Proof. exact (MK_COMB (@lem3659368) (@lem3659367 _93677 A x f s)). Qed.
Lemma lem3659370 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) (y : A) : (term672 _93677 A s f x y) = (term630 _93677 A s f x y).
Proof. exact (eq_refl (term672 _93677 A s f x y)). Qed.
Lemma lem3659371 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3659372 {_93677 A : Type'} (s : A -> Prop) (f : A -> _93677) (x : A) (y : A) : (term678 _93677 A s f x y) = (term679 _93677 A s f x y).
Proof. exact (MK_COMB (@lem3659371) (@lem3659370 _93677 A s f x y)). Qed.
Lemma lem3659373 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term646 _93677 A f s) = (term646 _93677 A f s).
Proof. exact (eq_refl (term646 _93677 A f s)). Qed.
Lemma lem3659374 {_93677 A : Type'} (x : A) (y : A) (f : A -> _93677) (s : A -> Prop) : (term680 _93677 A x y f s) = (term681 _93677 A x y f s).
Proof. exact (MK_COMB (@lem3659372 _93677 A s f x y) (@lem3659373 _93677 A f s)). Qed.
Lemma lem3659375 {_93677 A : Type'} (x : A) (f : A -> _93677) (s : A -> Prop) : (term682 _93677 A x f s) = (term683 _93677 A x f s).
Proof. exact (fun_ext (fun y : A => @lem3659374 _93677 A x y f s)). Qed.
Lemma lem3659376 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3659377 {_93677 A : Type'} (x : A) (f : A -> _93677) (s : A -> Prop) : (term671 _93677 A x f s) = (term684 _93677 A x f s).
Proof. exact (MK_COMB (@lem3659376 A) (@lem3659375 _93677 A x f s)). Qed.
Lemma lem3659378 {_93677 A : Type'} (x : A) (f : A -> _93677) (s : A -> Prop) : ((term670 _93677 A x f s) = (term671 _93677 A x f s)) = ((term666 _93677 A x f s) = (term684 _93677 A x f s)).
Proof. exact (MK_COMB (@lem3659369 _93677 A x f s) (@lem3659377 _93677 A x f s)). Qed.
Lemma lem3659379 {_93677 A : Type'} (x : A) (f : A -> _93677) (s : A -> Prop) : (term666 _93677 A x f s) = (term684 _93677 A x f s).
Proof. exact (EQ_MP (@lem3659378 _93677 A x f s) (@lem3659359 _93677 A x f s)). Qed.
Lemma lem3659380 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term668 _93677 A f s) = (term685 _93677 A f s).
Proof. exact (fun_ext (fun x : A => @lem3659379 _93677 A x f s)). Qed.
Lemma lem3659381 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3659382 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term669 _93677 A f s) = (term686 _93677 A f s).
Proof. exact (MK_COMB (@lem3659381 A) (@lem3659380 _93677 A f s)). Qed.
Lemma lem3659383 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term650 _93677 A f s) = (term686 _93677 A f s).
Proof. exact (TRANS (@lem3659355 _93677 A f s) (@lem3659382 _93677 A f s)). Qed.
Lemma lem3659384 {_93677 A : Type'} (f : A -> _93677) : (term651 _93677 A f) = (term687 _93677 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3659383 _93677 A f s)). Qed.
Lemma lem3659385 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3659386 {_93677 A : Type'} (f : A -> _93677) : (term652 _93677 A f) = (term688 _93677 A f).
Proof. exact (MK_COMB (@lem3659385 A) (@lem3659384 _93677 A f)). Qed.
Lemma lem3659388 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3659389 {A : Type'} (P : type672 A) : (term531 A P) = (term532 A P).
Proof. exact (@lem3659388 (A -> Prop) A P). Qed.
Lemma lem3659390 {_93677 A : Type'} (f : A -> _93677) : (term689 _93677 A f) = (term690 _93677 A f).
Proof. exact (@lem3659389 A (term691 _93677 A f)). Qed.
Lemma lem3659391 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term692 _93677 A f s) = (term685 _93677 A f s).
Proof. exact (eq_refl (term692 _93677 A f s)). Qed.
Lemma lem3659392 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3659393 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) (x : A) : (term693 _93677 A f s x) = (term694 _93677 A f s x).
Proof. exact (MK_COMB (@lem3659391 _93677 A f s) (@lem3659392 A x)). Qed.
Lemma lem3659394 {_93677 A : Type'} (x : A) (f : A -> _93677) (s : A -> Prop) : (term694 _93677 A f s x) = (term684 _93677 A x f s).
Proof. exact (eq_refl (term694 _93677 A f s x)). Qed.
Lemma lem3659395 {_93677 A : Type'} (x : A) (f : A -> _93677) (s : A -> Prop) : (term693 _93677 A f s x) = (term684 _93677 A x f s).
Proof. exact (TRANS (@lem3659393 _93677 A f s x) (@lem3659394 _93677 A x f s)). Qed.
Lemma lem3659396 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term695 _93677 A f s) = (term685 _93677 A f s).
Proof. exact (fun_ext (fun x : A => @lem3659395 _93677 A x f s)). Qed.
Lemma lem3659397 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3659398 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term696 _93677 A f s) = (term686 _93677 A f s).
Proof. exact (MK_COMB (@lem3659397 A) (@lem3659396 _93677 A f s)). Qed.
Lemma lem3659399 {_93677 A : Type'} (f : A -> _93677) : (term697 _93677 A f) = (term687 _93677 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3659398 _93677 A f s)). Qed.
Lemma lem3659400 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3659401 {_93677 A : Type'} (f : A -> _93677) : (term689 _93677 A f) = (term688 _93677 A f).
Proof. exact (MK_COMB (@lem3659400 A) (@lem3659399 _93677 A f)). Qed.
Lemma lem3659402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3659403 {_93677 A : Type'} (f : A -> _93677) : (term698 _93677 A f) = (term699 _93677 A f).
Proof. exact (MK_COMB (@lem3659402) (@lem3659401 _93677 A f)). Qed.
Lemma lem3659404 {_93677 A : Type'} (f : A -> _93677) (s : A -> Prop) : (term692 _93677 A f s) = (term685 _93677 A f s).
Proof. exact (eq_refl (term692 _93677 A f s)). Qed.
Lemma lem3659405 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3659406 {_93677 A : Type'} (f : A -> _93677) (x : type684 A) (s : A -> Prop) : (term700 _93677 A f x s) = (term701 _93677 A f x s).
Proof. exact (MK_COMB (@lem3659404 _93677 A f s) (@lem3659405 A x s)). Qed.
Lemma lem3659407 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) (s : A -> Prop) : (term701 _93677 A f x s) = (term702 _93677 A x f s).
Proof. exact (eq_refl (term701 _93677 A f x s)). Qed.
Lemma lem3659408 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) (s : A -> Prop) : (term700 _93677 A f x s) = (term702 _93677 A x f s).
Proof. exact (TRANS (@lem3659406 _93677 A f x s) (@lem3659407 _93677 A x f s)). Qed.
Lemma lem3659409 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) : (term703 _93677 A f x) = (term704 _93677 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3659408 _93677 A x f s)). Qed.
Lemma lem3659410 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3659411 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) : (term705 _93677 A f x) = (term706 _93677 A x f).
Proof. exact (MK_COMB (@lem3659410 A) (@lem3659409 _93677 A x f)). Qed.
Lemma lem3659412 {_93677 A : Type'} (f : A -> _93677) : (term707 _93677 A f) = (term708 _93677 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem3659411 _93677 A x f)). Qed.
Lemma lem3659413 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3659414 {_93677 A : Type'} (f : A -> _93677) : (term690 _93677 A f) = (term709 _93677 A f).
Proof. exact (MK_COMB (@lem3659413 A) (@lem3659412 _93677 A f)). Qed.
Lemma lem3659415 {_93677 A : Type'} (f : A -> _93677) : ((term689 _93677 A f) = (term690 _93677 A f)) = ((term688 _93677 A f) = (term709 _93677 A f)).
Proof. exact (MK_COMB (@lem3659403 _93677 A f) (@lem3659414 _93677 A f)). Qed.
Lemma lem3659416 {_93677 A : Type'} (f : A -> _93677) : (term688 _93677 A f) = (term709 _93677 A f).
Proof. exact (EQ_MP (@lem3659415 _93677 A f) (@lem3659390 _93677 A f)). Qed.
Lemma lem3659418 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3659419 {A : Type'} (P : type672 A) : (term531 A P) = (term532 A P).
Proof. exact (@lem3659418 (A -> Prop) A P). Qed.
Lemma lem3659420 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) : (term710 _93677 A x f) = (term711 _93677 A x f).
Proof. exact (@lem3659419 A (term712 _93677 A x f)). Qed.
Lemma lem3659421 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) (s : A -> Prop) : (term713 _93677 A x f s) = (term714 _93677 A x f s).
Proof. exact (eq_refl (term713 _93677 A x f s)). Qed.
Lemma lem3659422 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3659423 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) (s : A -> Prop) (y : A) : (term715 _93677 A x f s y) = (term716 _93677 A x f s y).
Proof. exact (MK_COMB (@lem3659421 _93677 A x f s) (@lem3659422 A y)). Qed.
Lemma lem3659424 {_93677 A : Type'} (x : type684 A) (y : A) (f : A -> _93677) (s : A -> Prop) : (term716 _93677 A x f s y) = (term717 _93677 A x y f s).
Proof. exact (eq_refl (term716 _93677 A x f s y)). Qed.
Lemma lem3659425 {_93677 A : Type'} (x : type684 A) (y : A) (f : A -> _93677) (s : A -> Prop) : (term715 _93677 A x f s y) = (term717 _93677 A x y f s).
Proof. exact (TRANS (@lem3659423 _93677 A x f s y) (@lem3659424 _93677 A x y f s)). Qed.
Lemma lem3659426 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) (s : A -> Prop) : (term718 _93677 A x f s) = (term714 _93677 A x f s).
Proof. exact (fun_ext (fun y : A => @lem3659425 _93677 A x y f s)). Qed.
Lemma lem3659427 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3659428 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) (s : A -> Prop) : (term719 _93677 A x f s) = (term702 _93677 A x f s).
Proof. exact (MK_COMB (@lem3659427 A) (@lem3659426 _93677 A x f s)). Qed.
Lemma lem3659429 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) : (term720 _93677 A x f) = (term704 _93677 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3659428 _93677 A x f s)). Qed.
Lemma lem3659430 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3659431 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) : (term710 _93677 A x f) = (term706 _93677 A x f).
Proof. exact (MK_COMB (@lem3659430 A) (@lem3659429 _93677 A x f)). Qed.
Lemma lem3659432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3659433 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) : (term721 _93677 A x f) = (term722 _93677 A x f).
Proof. exact (MK_COMB (@lem3659432) (@lem3659431 _93677 A x f)). Qed.
Lemma lem3659434 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) (s : A -> Prop) : (term713 _93677 A x f s) = (term714 _93677 A x f s).
Proof. exact (eq_refl (term713 _93677 A x f s)). Qed.
Lemma lem3659435 {A : Type'} (y : type684 A) (s : A -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem3659436 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) (y : type684 A) (s : A -> Prop) : (term723 _93677 A x f y s) = (term724 _93677 A x f y s).
Proof. exact (MK_COMB (@lem3659434 _93677 A x f s) (@lem3659435 A y s)). Qed.
Lemma lem3659437 {_93677 A : Type'} (x : type684 A) (y : type684 A) (f : A -> _93677) (s : A -> Prop) : (term724 _93677 A x f y s) = (term725 _93677 A x y f s).
Proof. exact (eq_refl (term724 _93677 A x f y s)). Qed.
Lemma lem3659438 {_93677 A : Type'} (x : type684 A) (y : type684 A) (f : A -> _93677) (s : A -> Prop) : (term723 _93677 A x f y s) = (term725 _93677 A x y f s).
Proof. exact (TRANS (@lem3659436 _93677 A x f y s) (@lem3659437 _93677 A x y f s)). Qed.
Lemma lem3659439 {_93677 A : Type'} (x : type684 A) (y : type684 A) (f : A -> _93677) : (term726 _93677 A x f y) = (term727 _93677 A x y f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3659438 _93677 A x y f s)). Qed.
Lemma lem3659440 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3659441 {_93677 A : Type'} (x : type684 A) (y : type684 A) (f : A -> _93677) : (term728 _93677 A x f y) = (term729 _93677 A x y f).
Proof. exact (MK_COMB (@lem3659440 A) (@lem3659439 _93677 A x y f)). Qed.
Lemma lem3659442 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) : (term730 _93677 A x f) = (term731 _93677 A x f).
Proof. exact (fun_ext (fun y : type684 A => @lem3659441 _93677 A x y f)). Qed.
Lemma lem3659443 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3659444 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) : (term711 _93677 A x f) = (term732 _93677 A x f).
Proof. exact (MK_COMB (@lem3659443 A) (@lem3659442 _93677 A x f)). Qed.
Lemma lem3659445 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) : ((term710 _93677 A x f) = (term711 _93677 A x f)) = ((term706 _93677 A x f) = (term732 _93677 A x f)).
Proof. exact (MK_COMB (@lem3659433 _93677 A x f) (@lem3659444 _93677 A x f)). Qed.
Lemma lem3659446 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) : (term706 _93677 A x f) = (term732 _93677 A x f).
Proof. exact (EQ_MP (@lem3659445 _93677 A x f) (@lem3659420 _93677 A x f)). Qed.
Lemma lem3659447 {_93677 A : Type'} (f : A -> _93677) : (term708 _93677 A f) = (term733 _93677 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem3659446 _93677 A x f)). Qed.
Lemma lem3659448 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3659449 {_93677 A : Type'} (f : A -> _93677) : (term709 _93677 A f) = (term734 _93677 A f).
Proof. exact (MK_COMB (@lem3659448 A) (@lem3659447 _93677 A f)). Qed.
Lemma lem3659450 {_93677 A : Type'} (f : A -> _93677) : (term688 _93677 A f) = (term734 _93677 A f).
Proof. exact (TRANS (@lem3659416 _93677 A f) (@lem3659449 _93677 A f)). Qed.
Lemma lem3659451 {_93677 A : Type'} (f : A -> _93677) : (term652 _93677 A f) = (term734 _93677 A f).
Proof. exact (TRANS (@lem3659386 _93677 A f) (@lem3659450 _93677 A f)). Qed.
Lemma lem3659452 {_93677 A : Type'} : (term653 _93677 A) = (term735 _93677 A).
Proof. exact (fun_ext (fun f : A -> _93677 => @lem3659451 _93677 A f)). Qed.
Lemma lem3659453 {_93677 A : Type'} : (@all (A -> _93677)) = (@all (A -> _93677)).
Proof. exact (eq_refl (@all (A -> _93677))). Qed.
Lemma lem3659454 {_93677 A : Type'} : (term654 _93677 A) = (term736 _93677 A).
Proof. exact (MK_COMB (@lem3659453 _93677 A) (@lem3659452 _93677 A)). Qed.
Lemma lem3659456 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3659457 {_93677 A : Type'} (P : type776 _93677 A) : (term737 _93677 A P) = (term738 _93677 A P).
Proof. exact (@lem3659456 (A -> _93677) (type684 A) P). Qed.
Lemma lem3659458 {_93677 A : Type'} : (term739 _93677 A) = (term740 _93677 A).
Proof. exact (@lem3659457 _93677 A (term741 _93677 A)). Qed.
Lemma lem3659459 {_93677 A : Type'} (f : A -> _93677) : (term742 _93677 A f) = (term733 _93677 A f).
Proof. exact (eq_refl (term742 _93677 A f)). Qed.
Lemma lem3659460 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3659461 {_93677 A : Type'} (f : A -> _93677) (x : type684 A) : (term743 _93677 A f x) = (term744 _93677 A f x).
Proof. exact (MK_COMB (@lem3659459 _93677 A f) (@lem3659460 A x)). Qed.
Lemma lem3659462 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) : (term744 _93677 A f x) = (term732 _93677 A x f).
Proof. exact (eq_refl (term744 _93677 A f x)). Qed.
Lemma lem3659463 {_93677 A : Type'} (x : type684 A) (f : A -> _93677) : (term743 _93677 A f x) = (term732 _93677 A x f).
Proof. exact (TRANS (@lem3659461 _93677 A f x) (@lem3659462 _93677 A x f)). Qed.
Lemma lem3659464 {_93677 A : Type'} (f : A -> _93677) : (term745 _93677 A f) = (term733 _93677 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem3659463 _93677 A x f)). Qed.
Lemma lem3659465 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3659466 {_93677 A : Type'} (f : A -> _93677) : (term746 _93677 A f) = (term734 _93677 A f).
Proof. exact (MK_COMB (@lem3659465 A) (@lem3659464 _93677 A f)). Qed.
Lemma lem3659467 {_93677 A : Type'} : (term747 _93677 A) = (term735 _93677 A).
Proof. exact (fun_ext (fun f : A -> _93677 => @lem3659466 _93677 A f)). Qed.
Lemma lem3659468 {_93677 A : Type'} : (@all (A -> _93677)) = (@all (A -> _93677)).
Proof. exact (eq_refl (@all (A -> _93677))). Qed.
Lemma lem3659469 {_93677 A : Type'} : (term739 _93677 A) = (term736 _93677 A).
Proof. exact (MK_COMB (@lem3659468 _93677 A) (@lem3659467 _93677 A)). Qed.
Lemma lem3659470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3659471 {_93677 A : Type'} : (term748 _93677 A) = (term749 _93677 A).
Proof. exact (MK_COMB (@lem3659470) (@lem3659469 _93677 A)). Qed.
Lemma lem3659472 {_93677 A : Type'} (f : A -> _93677) : (term742 _93677 A f) = (term733 _93677 A f).
Proof. exact (eq_refl (term742 _93677 A f)). Qed.
Lemma lem3659473 {_93677 A : Type'} (x : type791 _93677 A) (f : A -> _93677) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem3659474 {_93677 A : Type'} (x : type791 _93677 A) (f : A -> _93677) : (term750 _93677 A x f) = (term751 _93677 A x f).
Proof. exact (MK_COMB (@lem3659472 _93677 A f) (@lem3659473 _93677 A x f)). Qed.
Lemma lem3659475 {_93677 A : Type'} (x : type791 _93677 A) (f : A -> _93677) : (term751 _93677 A x f) = (term752 _93677 A x f).
Proof. exact (eq_refl (term751 _93677 A x f)). Qed.
Lemma lem3659476 {_93677 A : Type'} (x : type791 _93677 A) (f : A -> _93677) : (term750 _93677 A x f) = (term752 _93677 A x f).
Proof. exact (TRANS (@lem3659474 _93677 A x f) (@lem3659475 _93677 A x f)). Qed.
Lemma lem3659477 {_93677 A : Type'} (x : type791 _93677 A) : (term753 _93677 A x) = (term754 _93677 A x).
Proof. exact (fun_ext (fun f : A -> _93677 => @lem3659476 _93677 A x f)). Qed.
Lemma lem3659478 {_93677 A : Type'} : (@all (A -> _93677)) = (@all (A -> _93677)).
Proof. exact (eq_refl (@all (A -> _93677))). Qed.
Lemma lem3659479 {_93677 A : Type'} (x : type791 _93677 A) : (term755 _93677 A x) = (term756 _93677 A x).
Proof. exact (MK_COMB (@lem3659478 _93677 A) (@lem3659477 _93677 A x)). Qed.
Lemma lem3659480 {_93677 A : Type'} : (term757 _93677 A) = (term758 _93677 A).
Proof. exact (fun_ext (fun x : type791 _93677 A => @lem3659479 _93677 A x)). Qed.
Lemma lem3659481 {_93677 A : Type'} : (@ex ((A -> _93677) -> (A -> Prop) -> A)) = (@ex ((A -> _93677) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> _93677) -> (A -> Prop) -> A))). Qed.
Lemma lem3659482 {_93677 A : Type'} : (term740 _93677 A) = (term759 _93677 A).
Proof. exact (MK_COMB (@lem3659481 _93677 A) (@lem3659480 _93677 A)). Qed.
Lemma lem3659483 {_93677 A : Type'} : ((term739 _93677 A) = (term740 _93677 A)) = ((term736 _93677 A) = (term759 _93677 A)).
Proof. exact (MK_COMB (@lem3659471 _93677 A) (@lem3659482 _93677 A)). Qed.
Lemma lem3659484 {_93677 A : Type'} : (term736 _93677 A) = (term759 _93677 A).
Proof. exact (EQ_MP (@lem3659483 _93677 A) (@lem3659458 _93677 A)). Qed.
Lemma lem3659486 {A B : Type'} (P : type1413 A B) : (term529 A B P) = (term530 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3659487 {_93677 A : Type'} (P : type776 _93677 A) : (term737 _93677 A P) = (term738 _93677 A P).
Proof. exact (@lem3659486 (A -> _93677) (type684 A) P). Qed.
Lemma lem3659488 {_93677 A : Type'} (x : type791 _93677 A) : (term760 _93677 A x) = (term761 _93677 A x).
Proof. exact (@lem3659487 _93677 A (term762 _93677 A x)). Qed.
Lemma lem3659489 {_93677 A : Type'} (x : type791 _93677 A) (f : A -> _93677) : (term763 _93677 A x f) = (term764 _93677 A x f).
Proof. exact (eq_refl (term763 _93677 A x f)). Qed.
Lemma lem3659490 {A : Type'} (y : type684 A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3659491 {_93677 A : Type'} (x : type791 _93677 A) (f : A -> _93677) (y : type684 A) : (term765 _93677 A x f y) = (term766 _93677 A x f y).
Proof. exact (MK_COMB (@lem3659489 _93677 A x f) (@lem3659490 A y)). Qed.
Lemma lem3659492 {_93677 A : Type'} (x : type791 _93677 A) (y : type684 A) (f : A -> _93677) : (term766 _93677 A x f y) = (term767 _93677 A x y f).
Proof. exact (eq_refl (term766 _93677 A x f y)). Qed.
Lemma lem3659493 {_93677 A : Type'} (x : type791 _93677 A) (y : type684 A) (f : A -> _93677) : (term765 _93677 A x f y) = (term767 _93677 A x y f).
Proof. exact (TRANS (@lem3659491 _93677 A x f y) (@lem3659492 _93677 A x y f)). Qed.
Lemma lem3659494 {_93677 A : Type'} (x : type791 _93677 A) (f : A -> _93677) : (term768 _93677 A x f) = (term764 _93677 A x f).
Proof. exact (fun_ext (fun y : type684 A => @lem3659493 _93677 A x y f)). Qed.
Lemma lem3659495 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3659496 {_93677 A : Type'} (x : type791 _93677 A) (f : A -> _93677) : (term769 _93677 A x f) = (term752 _93677 A x f).
Proof. exact (MK_COMB (@lem3659495 A) (@lem3659494 _93677 A x f)). Qed.
Lemma lem3659497 {_93677 A : Type'} (x : type791 _93677 A) : (term770 _93677 A x) = (term754 _93677 A x).
Proof. exact (fun_ext (fun f : A -> _93677 => @lem3659496 _93677 A x f)). Qed.
Lemma lem3659498 {_93677 A : Type'} : (@all (A -> _93677)) = (@all (A -> _93677)).
Proof. exact (eq_refl (@all (A -> _93677))). Qed.
Lemma lem3659499 {_93677 A : Type'} (x : type791 _93677 A) : (term760 _93677 A x) = (term756 _93677 A x).
Proof. exact (MK_COMB (@lem3659498 _93677 A) (@lem3659497 _93677 A x)). Qed.
Lemma lem3659500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3659501 {_93677 A : Type'} (x : type791 _93677 A) : (term771 _93677 A x) = (term772 _93677 A x).
Proof. exact (MK_COMB (@lem3659500) (@lem3659499 _93677 A x)). Qed.
Lemma lem3659502 {_93677 A : Type'} (x : type791 _93677 A) (f : A -> _93677) : (term763 _93677 A x f) = (term764 _93677 A x f).
Proof. exact (eq_refl (term763 _93677 A x f)). Qed.
Lemma lem3659503 {_93677 A : Type'} (y : type791 _93677 A) (f : A -> _93677) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem3659504 {_93677 A : Type'} (x : type791 _93677 A) (y : type791 _93677 A) (f : A -> _93677) : (term773 _93677 A x y f) = (term774 _93677 A x y f).
Proof. exact (MK_COMB (@lem3659502 _93677 A x f) (@lem3659503 _93677 A y f)). Qed.
Lemma lem3659505 {_93677 A : Type'} (x : type791 _93677 A) (y : type791 _93677 A) (f : A -> _93677) : (term774 _93677 A x y f) = (term775 _93677 A x y f).
Proof. exact (eq_refl (term774 _93677 A x y f)). Qed.
Lemma lem3659506 {_93677 A : Type'} (x : type791 _93677 A) (y : type791 _93677 A) (f : A -> _93677) : (term773 _93677 A x y f) = (term775 _93677 A x y f).
Proof. exact (TRANS (@lem3659504 _93677 A x y f) (@lem3659505 _93677 A x y f)). Qed.
Lemma lem3659507 {_93677 A : Type'} (x : type791 _93677 A) (y : type791 _93677 A) : (term776 _93677 A x y) = (term777 _93677 A x y).
Proof. exact (fun_ext (fun f : A -> _93677 => @lem3659506 _93677 A x y f)). Qed.
Lemma lem3659508 {_93677 A : Type'} : (@all (A -> _93677)) = (@all (A -> _93677)).
Proof. exact (eq_refl (@all (A -> _93677))). Qed.
Lemma lem3659509 {_93677 A : Type'} (x : type791 _93677 A) (y : type791 _93677 A) : (term778 _93677 A x y) = (term779 _93677 A x y).
Proof. exact (MK_COMB (@lem3659508 _93677 A) (@lem3659507 _93677 A x y)). Qed.
Lemma lem3659510 {_93677 A : Type'} (x : type791 _93677 A) : (term780 _93677 A x) = (term781 _93677 A x).
Proof. exact (fun_ext (fun y : type791 _93677 A => @lem3659509 _93677 A x y)). Qed.
Lemma lem3659511 {_93677 A : Type'} : (@ex ((A -> _93677) -> (A -> Prop) -> A)) = (@ex ((A -> _93677) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> _93677) -> (A -> Prop) -> A))). Qed.
Lemma lem3659512 {_93677 A : Type'} (x : type791 _93677 A) : (term761 _93677 A x) = (term782 _93677 A x).
Proof. exact (MK_COMB (@lem3659511 _93677 A) (@lem3659510 _93677 A x)). Qed.
Lemma lem3659513 {_93677 A : Type'} (x : type791 _93677 A) : ((term760 _93677 A x) = (term761 _93677 A x)) = ((term756 _93677 A x) = (term782 _93677 A x)).
Proof. exact (MK_COMB (@lem3659501 _93677 A x) (@lem3659512 _93677 A x)). Qed.
Lemma lem3659514 {_93677 A : Type'} (x : type791 _93677 A) : (term756 _93677 A x) = (term782 _93677 A x).
Proof. exact (EQ_MP (@lem3659513 _93677 A x) (@lem3659488 _93677 A x)). Qed.
Lemma lem3659515 {_93677 A : Type'} : (term758 _93677 A) = (term783 _93677 A).
Proof. exact (fun_ext (fun x : type791 _93677 A => @lem3659514 _93677 A x)). Qed.
Lemma lem3659516 {_93677 A : Type'} : (@ex ((A -> _93677) -> (A -> Prop) -> A)) = (@ex ((A -> _93677) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> _93677) -> (A -> Prop) -> A))). Qed.
Lemma lem3659517 {_93677 A : Type'} : (term759 _93677 A) = (term784 _93677 A).
Proof. exact (MK_COMB (@lem3659516 _93677 A) (@lem3659515 _93677 A)). Qed.
Lemma lem3659518 {_93677 A : Type'} : (term736 _93677 A) = (term784 _93677 A).
Proof. exact (TRANS (@lem3659484 _93677 A) (@lem3659517 _93677 A)). Qed.
Lemma lem3659520 {_93677 A : Type'} : (term654 _93677 A) = (term784 _93677 A).
Proof. exact (TRANS (@lem3659454 _93677 A) (@lem3659518 _93677 A)). Qed.
Lemma lem3659521 {_93677 A : Type'} : (term83 _93677 A) = (term784 _93677 A).
Proof. exact (TRANS (@lem3659226 _93677 A) (@lem3659520 _93677 A)). Qed.
Lemma lem3659522 {_93677 A : Type'} (h1 : term83 _93677 A) : term784 _93677 A.
Proof. exact (EQ_MP (@lem3659521 _93677 A) (@lem3656895 _93677 A h1)). Qed.
Lemma lem3659523 {_93677 A : Type'} (x : type791 _93677 A) (h1 : term782 _93677 A x) : term782 _93677 A x.
Proof. exact (h1). Qed.
Lemma lem3659525 {_93670 A : Type'} (x' : type791 _93670 A) (h1 : term782 _93670 A x') : term782 _93670 A x'.
Proof. exact (h1). Qed.
Lemma lem3659527 {_93677 B : Type'} (x'' : type529 _93677 B) (h1 : term626 _93677 B x'') : term626 _93677 B x''.
Proof. exact (h1). Qed.
Lemma lem3659529 {_93670 B : Type'} (x''' : type529 _93670 B) (h1 : term626 _93670 B x''') : term626 _93670 B x'''.
Proof. exact (h1). Qed.
Lemma lem3659531 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (h1 : term626 _93670 _93677 x'''') : term626 _93670 _93677 x''''.
Proof. exact (h1). Qed.
Lemma lem3659532 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term623 _93670 _93677 x'''' y''''.
Proof. exact (h1). Qed.
Lemma lem3659533 {_93670 _93677 : Type'} (x''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term466 _93670 _93677 x''''' s P f t) : term466 _93670 _93677 x''''' s P f t.
Proof. exact (h1). Qed.
Lemma lem3659534 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term463 _93670 _93677 x''''' y''''' s P f t) : term463 _93670 _93677 x''''' y''''' s P f t.
Proof. exact (h1). Qed.
Lemma lem3660547 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660548 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3660547 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3660550 {_93670 : Type'} (s : _93670 -> Prop) : (@FINITE _93670 s) = (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) s).
Proof. exact (@lem3660548 _93670 (@FINITE _93670) s). Qed.
Lemma lem3660551 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3660552 {_93677 : Type'} : (@FINITE _93677) = (@FINITE _93677).
Proof. exact (eq_refl (@FINITE _93677)). Qed.
Lemma lem3660559 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660560 {_93670 _93677 : Type'} (f : type528 _93670 _93677) (x : _93670 -> _93677) : (f x) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3660559 (_93670 -> _93677) (type678 _93670 _93677) f x). Qed.
Lemma lem3660561 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (@IMAGE _93670 _93677 f) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f).
Proof. exact (@lem3660560 _93670 _93677 (@IMAGE _93670 _93677) f). Qed.
Lemma lem3660562 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3660563 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (@IMAGE _93670 _93677 f s) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f s).
Proof. exact (MK_COMB (@lem3660561 _93670 _93677 f) (@lem3660562 _93670 s)). Qed.
Lemma lem3660565 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660566 {_93670 _93677 : Type'} (f : type678 _93670 _93677) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3660565 (_93670 -> Prop) (_93677 -> Prop) f x). Qed.
Lemma lem3660567 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f s) = (term785 _93670 _93677 f s).
Proof. exact (@lem3660566 _93670 _93677 (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f) s). Qed.
Lemma lem3660569 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (@IMAGE _93670 _93677 f s) = (term785 _93670 _93677 f s).
Proof. exact (TRANS (@lem3660563 _93670 _93677 f s) (@lem3660567 _93670 _93677 f s)). Qed.
Lemma lem3660570 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term129 _93670 _93677 f s) = (term786 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3660552 _93677) (@lem3660569 _93670 _93677 f s)). Qed.
Lemma lem3660572 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660573 {_93677 : Type'} (f : type686 _93677) (x : _93677 -> Prop) : (f x) = (@I ((_93677 -> Prop) -> Prop) f x).
Proof. exact (@lem3660572 (_93677 -> Prop) Prop f x). Qed.
Lemma lem3660574 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term786 _93670 _93677 f s) = (term787 _93670 _93677 f s).
Proof. exact (@lem3660573 _93677 (@FINITE _93677) (term785 _93670 _93677 f s)). Qed.
Lemma lem3660575 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term129 _93670 _93677 f s) = (term787 _93670 _93677 f s).
Proof. exact (TRANS (@lem3660570 _93670 _93677 f s) (@lem3660574 _93670 _93677 f s)). Qed.
Lemma lem3660576 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term788 _93670 _93677 f s) = (term789 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3660551) (@lem3660575 _93670 _93677 f s)). Qed.
Lemma lem3660577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3660578 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term790 _93670 _93677 f s) = (term791 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3660577) (@lem3660576 _93670 _93677 f s)). Qed.
Lemma lem3660579 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term792 _93670 _93677 f s) = (term793 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3660578 _93670 _93677 f s) (@lem3660550 _93670 s)). Qed.
Lemma lem3660580 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3660585 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660586 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3660585 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3660588 {_93670 : Type'} (s : _93670 -> Prop) : (@FINITE _93670 s) = (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) s).
Proof. exact (@lem3660586 _93670 (@FINITE _93670) s). Qed.
Lemma lem3660589 {_93670 : Type'} (s : _93670 -> Prop) : (term262 _93670 s) = (term794 _93670 s).
Proof. exact (MK_COMB (@lem3660580) (@lem3660588 _93670 s)). Qed.
Lemma lem3660590 {_93677 : Type'} : (@FINITE _93677) = (@FINITE _93677).
Proof. exact (eq_refl (@FINITE _93677)). Qed.
Lemma lem3660597 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660598 {_93670 _93677 : Type'} (f : type528 _93670 _93677) (x : _93670 -> _93677) : (f x) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3660597 (_93670 -> _93677) (type678 _93670 _93677) f x). Qed.
Lemma lem3660599 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (@IMAGE _93670 _93677 f) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f).
Proof. exact (@lem3660598 _93670 _93677 (@IMAGE _93670 _93677) f). Qed.
Lemma lem3660600 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3660601 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (@IMAGE _93670 _93677 f s) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f s).
Proof. exact (MK_COMB (@lem3660599 _93670 _93677 f) (@lem3660600 _93670 s)). Qed.
Lemma lem3660603 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660604 {_93670 _93677 : Type'} (f : type678 _93670 _93677) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3660603 (_93670 -> Prop) (_93677 -> Prop) f x). Qed.
Lemma lem3660605 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f s) = (term785 _93670 _93677 f s).
Proof. exact (@lem3660604 _93670 _93677 (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f) s). Qed.
Lemma lem3660607 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (@IMAGE _93670 _93677 f s) = (term785 _93670 _93677 f s).
Proof. exact (TRANS (@lem3660601 _93670 _93677 f s) (@lem3660605 _93670 _93677 f s)). Qed.
Lemma lem3660608 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term129 _93670 _93677 f s) = (term786 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3660590 _93677) (@lem3660607 _93670 _93677 f s)). Qed.
Lemma lem3660610 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660611 {_93677 : Type'} (f : type686 _93677) (x : _93677 -> Prop) : (f x) = (@I ((_93677 -> Prop) -> Prop) f x).
Proof. exact (@lem3660610 (_93677 -> Prop) Prop f x). Qed.
Lemma lem3660612 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term786 _93670 _93677 f s) = (term787 _93670 _93677 f s).
Proof. exact (@lem3660611 _93677 (@FINITE _93677) (term785 _93670 _93677 f s)). Qed.
Lemma lem3660613 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term129 _93670 _93677 f s) = (term787 _93670 _93677 f s).
Proof. exact (TRANS (@lem3660608 _93670 _93677 f s) (@lem3660612 _93670 _93677 f s)). Qed.
Lemma lem3660614 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3660615 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term795 _93670 _93677 f s) = (term796 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3660614) (@lem3660613 _93670 _93677 f s)). Qed.
Lemma lem3660616 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term797 _93670 _93677 f s) = (term798 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3660615 _93670 _93677 f s) (@lem3660589 _93670 s)). Qed.
Lemma lem3660617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3660618 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term799 _93670 _93677 f s) = (term800 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3660617) (@lem3660616 _93670 _93677 f s)). Qed.
Lemma lem3660619 {_93670 _93677 : Type'} (f : _93670 -> _93677) (s : _93670 -> Prop) : (term486 _93670 _93677 f s) = (term801 _93670 _93677 f s).
Proof. exact (MK_COMB (@lem3660618 _93670 _93677 f s) (@lem3660579 _93670 _93677 f s)). Qed.
Lemma lem3660620 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3660621 {_93670 : Type'} : (@eq _93670) = (@eq _93670).
Proof. exact (eq_refl (@eq _93670)). Qed.
Lemma lem3660628 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660629 {_93670 _93677 : Type'} (f : type529 _93670 _93677) (x : _93670 -> _93677) : (f x) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) f x).
Proof. exact (@lem3660628 (_93670 -> _93677) (type684 _93670) f x). Qed.
Lemma lem3660630 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) : (x'''' f) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) x'''' f).
Proof. exact (@lem3660629 _93670 _93677 x'''' f). Qed.
Lemma lem3660631 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3660632 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (x'''' f s) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) x'''' f s).
Proof. exact (MK_COMB (@lem3660630 _93670 _93677 x'''' f) (@lem3660631 _93670 s)). Qed.
Lemma lem3660634 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660635 {_93670 : Type'} (f : type684 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> _93670) f x).
Proof. exact (@lem3660634 (_93670 -> Prop) _93670 f x). Qed.
Lemma lem3660636 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) x'''' f s) = (term802 _93670 _93677 x'''' f s).
Proof. exact (@lem3660635 _93670 (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) x'''' f) s). Qed.
Lemma lem3660638 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (x'''' f s) = (term802 _93670 _93677 x'''' f s).
Proof. exact (TRANS (@lem3660632 _93670 _93677 x'''' f s) (@lem3660636 _93670 _93677 x'''' f s)). Qed.
Lemma lem3660645 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660646 {_93670 _93677 : Type'} (f : type529 _93670 _93677) (x : _93670 -> _93677) : (f x) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) f x).
Proof. exact (@lem3660645 (_93670 -> _93677) (type684 _93670) f x). Qed.
Lemma lem3660647 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) : (y'''' f) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) y'''' f).
Proof. exact (@lem3660646 _93670 _93677 y'''' f). Qed.
Lemma lem3660648 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3660649 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (y'''' f s) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) y'''' f s).
Proof. exact (MK_COMB (@lem3660647 _93670 _93677 y'''' f) (@lem3660648 _93670 s)). Qed.
Lemma lem3660651 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660652 {_93670 : Type'} (f : type684 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> _93670) f x).
Proof. exact (@lem3660651 (_93670 -> Prop) _93670 f x). Qed.
Lemma lem3660653 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) y'''' f s) = (term802 _93670 _93677 y'''' f s).
Proof. exact (@lem3660652 _93670 (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) y'''' f) s). Qed.
Lemma lem3660655 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (y'''' f s) = (term802 _93670 _93677 y'''' f s).
Proof. exact (TRANS (@lem3660649 _93670 _93677 y'''' f s) (@lem3660653 _93670 _93677 y'''' f s)). Qed.
Lemma lem3660656 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term803 _93670 _93677 x'''' f s) = (term804 _93670 _93677 x'''' f s).
Proof. exact (MK_COMB (@lem3660621 _93670) (@lem3660638 _93670 _93677 x'''' f s)). Qed.
Lemma lem3660657 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : ((x'''' f s) = (y'''' f s)) = ((term802 _93670 _93677 x'''' f s) = (term802 _93670 _93677 y'''' f s)).
Proof. exact (MK_COMB (@lem3660656 _93670 _93677 x'''' f s) (@lem3660655 _93670 _93677 y'''' f s)). Qed.
Lemma lem3660658 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term805 _93670 _93677 x'''' y'''' f s) = (term806 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3660620) (@lem3660657 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3660659 {_93677 : Type'} : (@eq _93677) = (@eq _93677).
Proof. exact (eq_refl (@eq _93677)). Qed.
Lemma lem3660660 {_93670 _93677 : Type'} (f : _93670 -> _93677) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3660667 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660668 {_93670 _93677 : Type'} (f : type529 _93670 _93677) (x : _93670 -> _93677) : (f x) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) f x).
Proof. exact (@lem3660667 (_93670 -> _93677) (type684 _93670) f x). Qed.
Lemma lem3660669 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) : (x'''' f) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) x'''' f).
Proof. exact (@lem3660668 _93670 _93677 x'''' f). Qed.
Lemma lem3660670 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3660671 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (x'''' f s) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) x'''' f s).
Proof. exact (MK_COMB (@lem3660669 _93670 _93677 x'''' f) (@lem3660670 _93670 s)). Qed.
Lemma lem3660673 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660674 {_93670 : Type'} (f : type684 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> _93670) f x).
Proof. exact (@lem3660673 (_93670 -> Prop) _93670 f x). Qed.
Lemma lem3660675 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) x'''' f s) = (term802 _93670 _93677 x'''' f s).
Proof. exact (@lem3660674 _93670 (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) x'''' f) s). Qed.
Lemma lem3660677 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (x'''' f s) = (term802 _93670 _93677 x'''' f s).
Proof. exact (TRANS (@lem3660671 _93670 _93677 x'''' f s) (@lem3660675 _93670 _93677 x'''' f s)). Qed.
Lemma lem3660678 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term807 _93670 _93677 x'''' f s) = (term808 _93670 _93677 x'''' f s).
Proof. exact (MK_COMB (@lem3660660 _93670 _93677 f) (@lem3660677 _93670 _93677 x'''' f s)). Qed.
Lemma lem3660680 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660681 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3660680 _93670 _93677 f x). Qed.
Lemma lem3660682 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term808 _93670 _93677 x'''' f s) = (term809 _93670 _93677 x'''' f s).
Proof. exact (@lem3660681 _93670 _93677 f (term802 _93670 _93677 x'''' f s)). Qed.
Lemma lem3660683 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term807 _93670 _93677 x'''' f s) = (term809 _93670 _93677 x'''' f s).
Proof. exact (TRANS (@lem3660678 _93670 _93677 x'''' f s) (@lem3660682 _93670 _93677 x'''' f s)). Qed.
Lemma lem3660684 {_93670 _93677 : Type'} (f : _93670 -> _93677) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3660691 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660692 {_93670 _93677 : Type'} (f : type529 _93670 _93677) (x : _93670 -> _93677) : (f x) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) f x).
Proof. exact (@lem3660691 (_93670 -> _93677) (type684 _93670) f x). Qed.
Lemma lem3660693 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) : (y'''' f) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) y'''' f).
Proof. exact (@lem3660692 _93670 _93677 y'''' f). Qed.
Lemma lem3660694 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3660695 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (y'''' f s) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) y'''' f s).
Proof. exact (MK_COMB (@lem3660693 _93670 _93677 y'''' f) (@lem3660694 _93670 s)). Qed.
Lemma lem3660697 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660698 {_93670 : Type'} (f : type684 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> _93670) f x).
Proof. exact (@lem3660697 (_93670 -> Prop) _93670 f x). Qed.
Lemma lem3660699 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) y'''' f s) = (term802 _93670 _93677 y'''' f s).
Proof. exact (@lem3660698 _93670 (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) y'''' f) s). Qed.
Lemma lem3660701 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (y'''' f s) = (term802 _93670 _93677 y'''' f s).
Proof. exact (TRANS (@lem3660695 _93670 _93677 y'''' f s) (@lem3660699 _93670 _93677 y'''' f s)). Qed.
Lemma lem3660702 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term807 _93670 _93677 y'''' f s) = (term808 _93670 _93677 y'''' f s).
Proof. exact (MK_COMB (@lem3660684 _93670 _93677 f) (@lem3660701 _93670 _93677 y'''' f s)). Qed.
Lemma lem3660704 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660705 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3660704 _93670 _93677 f x). Qed.
Lemma lem3660706 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term808 _93670 _93677 y'''' f s) = (term809 _93670 _93677 y'''' f s).
Proof. exact (@lem3660705 _93670 _93677 f (term802 _93670 _93677 y'''' f s)). Qed.
Lemma lem3660707 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term807 _93670 _93677 y'''' f s) = (term809 _93670 _93677 y'''' f s).
Proof. exact (TRANS (@lem3660702 _93670 _93677 y'''' f s) (@lem3660706 _93670 _93677 y'''' f s)). Qed.
Lemma lem3660708 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term810 _93670 _93677 x'''' f s) = (term811 _93670 _93677 x'''' f s).
Proof. exact (MK_COMB (@lem3660659 _93677) (@lem3660683 _93670 _93677 x'''' f s)). Qed.
Lemma lem3660709 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : ((term807 _93670 _93677 x'''' f s) = (term807 _93670 _93677 y'''' f s)) = ((term809 _93670 _93677 x'''' f s) = (term809 _93670 _93677 y'''' f s)).
Proof. exact (MK_COMB (@lem3660708 _93670 _93677 x'''' f s) (@lem3660707 _93670 _93677 y'''' f s)). Qed.
Lemma lem3660710 {_93670 : Type'} : (@IN _93670) = (@IN _93670).
Proof. exact (eq_refl (@IN _93670)). Qed.
Lemma lem3660717 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660718 {_93670 _93677 : Type'} (f : type529 _93670 _93677) (x : _93670 -> _93677) : (f x) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) f x).
Proof. exact (@lem3660717 (_93670 -> _93677) (type684 _93670) f x). Qed.
Lemma lem3660719 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) : (y'''' f) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) y'''' f).
Proof. exact (@lem3660718 _93670 _93677 y'''' f). Qed.
Lemma lem3660720 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3660721 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (y'''' f s) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) y'''' f s).
Proof. exact (MK_COMB (@lem3660719 _93670 _93677 y'''' f) (@lem3660720 _93670 s)). Qed.
Lemma lem3660723 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660724 {_93670 : Type'} (f : type684 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> _93670) f x).
Proof. exact (@lem3660723 (_93670 -> Prop) _93670 f x). Qed.
Lemma lem3660725 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) y'''' f s) = (term802 _93670 _93677 y'''' f s).
Proof. exact (@lem3660724 _93670 (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) y'''' f) s). Qed.
Lemma lem3660727 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (y'''' f s) = (term802 _93670 _93677 y'''' f s).
Proof. exact (TRANS (@lem3660721 _93670 _93677 y'''' f s) (@lem3660725 _93670 _93677 y'''' f s)). Qed.
Lemma lem3660728 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3660729 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term812 _93670 _93677 y'''' f s) = (term813 _93670 _93677 y'''' f s).
Proof. exact (MK_COMB (@lem3660710 _93670) (@lem3660727 _93670 _93677 y'''' f s)). Qed.
Lemma lem3660730 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term814 _93670 _93677 y'''' f s) = (term815 _93670 _93677 y'''' f s).
Proof. exact (MK_COMB (@lem3660729 _93670 _93677 y'''' f s) (@lem3660728 _93670 s)). Qed.
Lemma lem3660732 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660733 {_93670 : Type'} (f : type1364 _93670) (x : _93670) : (f x) = (@I (_93670 -> (_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3660732 _93670 (type686 _93670) f x). Qed.
Lemma lem3660734 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term813 _93670 _93677 y'''' f s) = (term816 _93670 _93677 y'''' f s).
Proof. exact (@lem3660733 _93670 (@IN _93670) (term802 _93670 _93677 y'''' f s)). Qed.
Lemma lem3660735 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3660736 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term815 _93670 _93677 y'''' f s) = (term817 _93670 _93677 y'''' f s).
Proof. exact (MK_COMB (@lem3660734 _93670 _93677 y'''' f s) (@lem3660735 _93670 s)). Qed.
Lemma lem3660738 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660739 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3660738 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3660740 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term817 _93670 _93677 y'''' f s) = (term818 _93670 _93677 y'''' f s).
Proof. exact (@lem3660739 _93670 (term816 _93670 _93677 y'''' f s) s). Qed.
Lemma lem3660741 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term815 _93670 _93677 y'''' f s) = (term818 _93670 _93677 y'''' f s).
Proof. exact (TRANS (@lem3660736 _93670 _93677 y'''' f s) (@lem3660740 _93670 _93677 y'''' f s)). Qed.
Lemma lem3660742 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term814 _93670 _93677 y'''' f s) = (term818 _93670 _93677 y'''' f s).
Proof. exact (TRANS (@lem3660730 _93670 _93677 y'''' f s) (@lem3660741 _93670 _93677 y'''' f s)). Qed.
Lemma lem3660743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3660744 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term819 _93670 _93677 y'''' f s) = (term820 _93670 _93677 y'''' f s).
Proof. exact (MK_COMB (@lem3660743) (@lem3660742 _93670 _93677 y'''' f s)). Qed.
Lemma lem3660745 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term821 _93670 _93677 x'''' y'''' f s) = (term822 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3660744 _93670 _93677 y'''' f s) (@lem3660709 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3660746 {_93670 : Type'} : (@IN _93670) = (@IN _93670).
Proof. exact (eq_refl (@IN _93670)). Qed.
Lemma lem3660753 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660754 {_93670 _93677 : Type'} (f : type529 _93670 _93677) (x : _93670 -> _93677) : (f x) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) f x).
Proof. exact (@lem3660753 (_93670 -> _93677) (type684 _93670) f x). Qed.
Lemma lem3660755 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) : (x'''' f) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) x'''' f).
Proof. exact (@lem3660754 _93670 _93677 x'''' f). Qed.
Lemma lem3660756 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3660757 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (x'''' f s) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) x'''' f s).
Proof. exact (MK_COMB (@lem3660755 _93670 _93677 x'''' f) (@lem3660756 _93670 s)). Qed.
Lemma lem3660759 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660760 {_93670 : Type'} (f : type684 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> _93670) f x).
Proof. exact (@lem3660759 (_93670 -> Prop) _93670 f x). Qed.
Lemma lem3660761 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) x'''' f s) = (term802 _93670 _93677 x'''' f s).
Proof. exact (@lem3660760 _93670 (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93670) x'''' f) s). Qed.
Lemma lem3660763 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (x'''' f s) = (term802 _93670 _93677 x'''' f s).
Proof. exact (TRANS (@lem3660757 _93670 _93677 x'''' f s) (@lem3660761 _93670 _93677 x'''' f s)). Qed.
Lemma lem3660764 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3660765 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term812 _93670 _93677 x'''' f s) = (term813 _93670 _93677 x'''' f s).
Proof. exact (MK_COMB (@lem3660746 _93670) (@lem3660763 _93670 _93677 x'''' f s)). Qed.
Lemma lem3660766 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term814 _93670 _93677 x'''' f s) = (term815 _93670 _93677 x'''' f s).
Proof. exact (MK_COMB (@lem3660765 _93670 _93677 x'''' f s) (@lem3660764 _93670 s)). Qed.
Lemma lem3660768 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660769 {_93670 : Type'} (f : type1364 _93670) (x : _93670) : (f x) = (@I (_93670 -> (_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3660768 _93670 (type686 _93670) f x). Qed.
Lemma lem3660770 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term813 _93670 _93677 x'''' f s) = (term816 _93670 _93677 x'''' f s).
Proof. exact (@lem3660769 _93670 (@IN _93670) (term802 _93670 _93677 x'''' f s)). Qed.
Lemma lem3660771 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3660772 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term815 _93670 _93677 x'''' f s) = (term817 _93670 _93677 x'''' f s).
Proof. exact (MK_COMB (@lem3660770 _93670 _93677 x'''' f s) (@lem3660771 _93670 s)). Qed.
Lemma lem3660774 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660775 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3660774 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3660776 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term817 _93670 _93677 x'''' f s) = (term818 _93670 _93677 x'''' f s).
Proof. exact (@lem3660775 _93670 (term816 _93670 _93677 x'''' f s) s). Qed.
Lemma lem3660777 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term815 _93670 _93677 x'''' f s) = (term818 _93670 _93677 x'''' f s).
Proof. exact (TRANS (@lem3660772 _93670 _93677 x'''' f s) (@lem3660776 _93670 _93677 x'''' f s)). Qed.
Lemma lem3660778 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term814 _93670 _93677 x'''' f s) = (term818 _93670 _93677 x'''' f s).
Proof. exact (TRANS (@lem3660766 _93670 _93677 x'''' f s) (@lem3660777 _93670 _93677 x'''' f s)). Qed.
Lemma lem3660779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3660780 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term819 _93670 _93677 x'''' f s) = (term820 _93670 _93677 x'''' f s).
Proof. exact (MK_COMB (@lem3660779) (@lem3660778 _93670 _93677 x'''' f s)). Qed.
Lemma lem3660781 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term823 _93670 _93677 x'''' y'''' f s) = (term824 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3660780 _93670 _93677 x'''' f s) (@lem3660745 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3660782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3660783 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term825 _93670 _93677 x'''' y'''' f s) = (term826 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3660782) (@lem3660781 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3660784 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term827 _93670 _93677 x'''' y'''' f s) = (term828 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3660783 _93670 _93677 x'''' y'''' f s) (@lem3660658 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3660785 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3660786 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term829 _93670 _93677 x'''' y'''' f s) = (term830 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3660785) (@lem3660784 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3660787 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term831 _93670 _93677 x'''' y'''' f s) = (term832 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3660786 _93670 _93677 x'''' y'''' f s) (@lem3660619 _93670 _93677 f s)). Qed.
Lemma lem3660788 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) : (term833 _93670 _93677 x'''' y'''' f) = (term834 _93670 _93677 x'''' y'''' f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3660787 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3660789 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3660790 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) : (term619 _93670 _93677 x'''' y'''' f) = (term835 _93670 _93677 x'''' y'''' f).
Proof. exact (MK_COMB (@lem3660789 _93670) (@lem3660788 _93670 _93677 x'''' y'''' f)). Qed.
Lemma lem3660791 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) : (term621 _93670 _93677 x'''' y'''') = (term836 _93670 _93677 x'''' y'''').
Proof. exact (fun_ext (fun f : _93670 -> _93677 => @lem3660790 _93670 _93677 x'''' y'''' f)). Qed.
Lemma lem3660792 {_93670 _93677 : Type'} : (@all (_93670 -> _93677)) = (@all (_93670 -> _93677)).
Proof. exact (eq_refl (@all (_93670 -> _93677))). Qed.
Lemma lem3660793 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) : (term623 _93670 _93677 x'''' y'''') = (term837 _93670 _93677 x'''' y'''').
Proof. exact (MK_COMB (@lem3660792 _93670 _93677) (@lem3660791 _93670 _93677 x'''' y'''')). Qed.
Lemma lem3660794 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term837 _93670 _93677 x'''' y''''.
Proof. exact (EQ_MP (@lem3660793 _93670 _93677 x'''' y'''') (@lem3659532 _93670 _93677 x'''' y'''' h1)). Qed.
Lemma lem3660795 {_93677 : Type'} (P : type686 _93677) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3660802 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660803 {_93670 _93677 : Type'} (f : type528 _93670 _93677) (x : _93670 -> _93677) : (f x) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3660802 (_93670 -> _93677) (type678 _93670 _93677) f x). Qed.
Lemma lem3660804 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (@IMAGE _93670 _93677 f) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f).
Proof. exact (@lem3660803 _93670 _93677 (@IMAGE _93670 _93677) f). Qed.
Lemma lem3660805 {_93670 : Type'} (t : _93670 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3660806 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@IMAGE _93670 _93677 f t) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f t).
Proof. exact (MK_COMB (@lem3660804 _93670 _93677 f) (@lem3660805 _93670 t)). Qed.
Lemma lem3660808 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660809 {_93670 _93677 : Type'} (f : type678 _93670 _93677) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3660808 (_93670 -> Prop) (_93677 -> Prop) f x). Qed.
Lemma lem3660810 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f t) = (term785 _93670 _93677 f t).
Proof. exact (@lem3660809 _93670 _93677 (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f) t). Qed.
Lemma lem3660812 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@IMAGE _93670 _93677 f t) = (term785 _93670 _93677 f t).
Proof. exact (TRANS (@lem3660806 _93670 _93677 f t) (@lem3660810 _93670 _93677 f t)). Qed.
Lemma lem3660813 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term140 _93670 _93677 P f t) = (term838 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3660795 _93677 P) (@lem3660812 _93670 _93677 f t)). Qed.
Lemma lem3660815 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660816 {_93677 : Type'} (f : type686 _93677) (x : _93677 -> Prop) : (f x) = (@I ((_93677 -> Prop) -> Prop) f x).
Proof. exact (@lem3660815 (_93677 -> Prop) Prop f x). Qed.
Lemma lem3660817 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term838 _93670 _93677 P f t) = (term839 _93670 _93677 P f t).
Proof. exact (@lem3660816 _93677 P (term785 _93670 _93677 f t)). Qed.
Lemma lem3660818 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term140 _93670 _93677 P f t) = (term839 _93670 _93677 P f t).
Proof. exact (TRANS (@lem3660813 _93670 _93677 P f t) (@lem3660817 _93670 _93677 P f t)). Qed.
Lemma lem3660823 {_93670 : Type'} (x : _93670) (y : _93670) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3660824 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3660825 {_93677 : Type'} : (@eq _93677) = (@eq _93677).
Proof. exact (eq_refl (@eq _93677)). Qed.
Lemma lem3660830 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660832 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3660830 _93670 _93677 f x). Qed.
Lemma lem3660837 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660838 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3660837 _93670 _93677 f x). Qed.
Lemma lem3660840 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y : _93670) : (f y) = (@I (_93670 -> _93677) f y).
Proof. exact (@lem3660838 _93670 _93677 f y). Qed.
Lemma lem3660841 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (term840 _93670 _93677 f x) = (term841 _93670 _93677 f x).
Proof. exact (MK_COMB (@lem3660825 _93677) (@lem3660832 _93670 _93677 f x)). Qed.
Lemma lem3660842 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (y : _93670) : ((f x) = (f y)) = ((@I (_93670 -> _93677) f x) = (@I (_93670 -> _93677) f y)).
Proof. exact (MK_COMB (@lem3660841 _93670 _93677 f x) (@lem3660840 _93670 _93677 f y)). Qed.
Lemma lem3660843 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (y : _93670) : (term842 _93670 _93677 x f y) = (term843 _93670 _93677 x f y).
Proof. exact (MK_COMB (@lem3660824) (@lem3660842 _93670 _93677 x f y)). Qed.
Lemma lem3660844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3660845 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (y : _93670) : (term844 _93670 _93677 x f y) = (term845 _93670 _93677 x f y).
Proof. exact (MK_COMB (@lem3660844) (@lem3660843 _93670 _93677 x f y)). Qed.
Lemma lem3660846 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term846 _93670 _93677 f x y) = (term847 _93670 _93677 f x y).
Proof. exact (MK_COMB (@lem3660845 _93670 _93677 x f y) (@lem3660823 _93670 x y)). Qed.
Lemma lem3660853 {_93670 : Type'} (x : _93670) (y : _93670) : (term848 _93670 x y) = (term848 _93670 x y).
Proof. exact (eq_refl (term848 _93670 x y)). Qed.
Lemma lem3660854 {_93677 : Type'} : (@eq _93677) = (@eq _93677).
Proof. exact (eq_refl (@eq _93677)). Qed.
Lemma lem3660859 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660861 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3660859 _93670 _93677 f x). Qed.
Lemma lem3660866 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660867 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3660866 _93670 _93677 f x). Qed.
Lemma lem3660869 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y : _93670) : (f y) = (@I (_93670 -> _93677) f y).
Proof. exact (@lem3660867 _93670 _93677 f y). Qed.
Lemma lem3660870 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (term840 _93670 _93677 f x) = (term841 _93670 _93677 f x).
Proof. exact (MK_COMB (@lem3660854 _93677) (@lem3660861 _93670 _93677 f x)). Qed.
Lemma lem3660871 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (y : _93670) : ((f x) = (f y)) = ((@I (_93670 -> _93677) f x) = (@I (_93670 -> _93677) f y)).
Proof. exact (MK_COMB (@lem3660870 _93670 _93677 f x) (@lem3660869 _93670 _93677 f y)). Qed.
Lemma lem3660872 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3660873 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (y : _93670) : (term849 _93670 _93677 x f y) = (term850 _93670 _93677 x f y).
Proof. exact (MK_COMB (@lem3660872) (@lem3660871 _93670 _93677 x f y)). Qed.
Lemma lem3660874 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term851 _93670 _93677 f x y) = (term852 _93670 _93677 f x y).
Proof. exact (MK_COMB (@lem3660873 _93670 _93677 x f y) (@lem3660853 _93670 x y)). Qed.
Lemma lem3660875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3660876 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term853 _93670 _93677 f x y) = (term854 _93670 _93677 f x y).
Proof. exact (MK_COMB (@lem3660875) (@lem3660874 _93670 _93677 f x y)). Qed.
Lemma lem3660877 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term153 _93670 _93677 f x y) = (term855 _93670 _93677 f x y).
Proof. exact (MK_COMB (@lem3660876 _93670 _93677 f x y) (@lem3660846 _93670 _93677 f x y)). Qed.
Lemma lem3660878 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3660885 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660886 {_93670 : Type'} (f : type1364 _93670) (x : _93670) : (f x) = (@I (_93670 -> (_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3660885 _93670 (type686 _93670) f x). Qed.
Lemma lem3660887 {_93670 : Type'} (y : _93670) : (@IN _93670 y) = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y).
Proof. exact (@lem3660886 _93670 (@IN _93670) y). Qed.
Lemma lem3660888 {_93670 : Type'} (t : _93670 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3660889 {_93670 : Type'} (y : _93670) (t : _93670 -> Prop) : (@IN _93670 y t) = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y t).
Proof. exact (MK_COMB (@lem3660887 _93670 y) (@lem3660888 _93670 t)). Qed.
Lemma lem3660891 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660892 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3660891 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3660893 {_93670 : Type'} (y : _93670) (t : _93670 -> Prop) : (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y t) = (term856 _93670 y t).
Proof. exact (@lem3660892 _93670 (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y) t). Qed.
Lemma lem3660895 {_93670 : Type'} (y : _93670) (t : _93670 -> Prop) : (@IN _93670 y t) = (term856 _93670 y t).
Proof. exact (TRANS (@lem3660889 _93670 y t) (@lem3660893 _93670 y t)). Qed.
Lemma lem3660896 {_93670 : Type'} (y : _93670) (t : _93670 -> Prop) : (term857 _93670 y t) = (term858 _93670 y t).
Proof. exact (MK_COMB (@lem3660878) (@lem3660895 _93670 y t)). Qed.
Lemma lem3660897 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3660904 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660905 {_93670 : Type'} (f : type1364 _93670) (x : _93670) : (f x) = (@I (_93670 -> (_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3660904 _93670 (type686 _93670) f x). Qed.
Lemma lem3660906 {_93670 : Type'} (x : _93670) : (@IN _93670 x) = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x).
Proof. exact (@lem3660905 _93670 (@IN _93670) x). Qed.
Lemma lem3660907 {_93670 : Type'} (t : _93670 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3660908 {_93670 : Type'} (x : _93670) (t : _93670 -> Prop) : (@IN _93670 x t) = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x t).
Proof. exact (MK_COMB (@lem3660906 _93670 x) (@lem3660907 _93670 t)). Qed.
Lemma lem3660910 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660911 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3660910 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3660912 {_93670 : Type'} (x : _93670) (t : _93670 -> Prop) : (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x t) = (term856 _93670 x t).
Proof. exact (@lem3660911 _93670 (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x) t). Qed.
Lemma lem3660914 {_93670 : Type'} (x : _93670) (t : _93670 -> Prop) : (@IN _93670 x t) = (term856 _93670 x t).
Proof. exact (TRANS (@lem3660908 _93670 x t) (@lem3660912 _93670 x t)). Qed.
Lemma lem3660915 {_93670 : Type'} (x : _93670) (t : _93670 -> Prop) : (term857 _93670 x t) = (term858 _93670 x t).
Proof. exact (MK_COMB (@lem3660897) (@lem3660914 _93670 x t)). Qed.
Lemma lem3660916 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3660917 {_93670 : Type'} (x : _93670) (t : _93670 -> Prop) : (term859 _93670 x t) = (term860 _93670 x t).
Proof. exact (MK_COMB (@lem3660916) (@lem3660915 _93670 x t)). Qed.
Lemma lem3660918 {_93670 : Type'} (x : _93670) (y : _93670) (t : _93670 -> Prop) : (term150 _93670 x y t) = (term861 _93670 x y t).
Proof. exact (MK_COMB (@lem3660917 _93670 x t) (@lem3660896 _93670 y t)). Qed.
Lemma lem3660919 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3660920 {_93670 : Type'} (x : _93670) (y : _93670) (t : _93670 -> Prop) : (term160 _93670 x y t) = (term862 _93670 x y t).
Proof. exact (MK_COMB (@lem3660919) (@lem3660918 _93670 x y t)). Qed.
Lemma lem3660921 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term162 _93670 _93677 t f x y) = (term863 _93670 _93677 t f x y).
Proof. exact (MK_COMB (@lem3660920 _93670 x y t) (@lem3660877 _93670 _93677 f x y)). Qed.
Lemma lem3660922 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term172 _93670 _93677 t f x) = (term864 _93670 _93677 t f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3660921 _93670 _93677 t f x y)). Qed.
Lemma lem3660923 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3660924 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term173 _93670 _93677 t f x) = (term865 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3660923 _93670) (@lem3660922 _93670 _93677 t f x)). Qed.
Lemma lem3660925 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term181 _93670 _93677 t f) = (term866 _93670 _93677 t f).
Proof. exact (fun_ext (fun x : _93670 => @lem3660924 _93670 _93677 t f x)). Qed.
Lemma lem3660926 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3660927 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term182 _93670 _93677 t f) = (term867 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3660926 _93670) (@lem3660925 _93670 _93677 t f)). Qed.
Lemma lem3660928 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3660929 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term190 _93670 _93677 t f) = (term868 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3660928) (@lem3660927 _93670 _93677 t f)). Qed.
Lemma lem3660930 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term201 _93670 _93677 P f t) = (term869 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3660929 _93670 _93677 t f) (@lem3660818 _93670 _93677 P f t)). Qed.
Lemma lem3660935 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660936 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3660935 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3660938 {_93670 : Type'} (t : _93670 -> Prop) : (@FINITE _93670 t) = (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t).
Proof. exact (@lem3660936 _93670 (@FINITE _93670) t). Qed.
Lemma lem3660939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3660940 {_93670 : Type'} (t : _93670 -> Prop) : (term146 _93670 t) = (term870 _93670 t).
Proof. exact (MK_COMB (@lem3660939) (@lem3660938 _93670 t)). Qed.
Lemma lem3660941 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term206 _93670 _93677 P f t) = (term871 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3660940 _93670 t) (@lem3660930 _93670 _93677 P f t)). Qed.
Lemma lem3660948 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660949 {_93670 : Type'} (f : type639 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3660948 (_93670 -> Prop) (type686 _93670) f x). Qed.
Lemma lem3660950 {_93670 : Type'} (t : _93670 -> Prop) : (@SUBSET _93670 t) = (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t).
Proof. exact (@lem3660949 _93670 (@SUBSET _93670) t). Qed.
Lemma lem3660951 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3660952 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (@SUBSET _93670 t s) = (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t s).
Proof. exact (MK_COMB (@lem3660950 _93670 t) (@lem3660951 _93670 s)). Qed.
Lemma lem3660954 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660955 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3660954 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3660956 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t s) = (term872 _93670 t s).
Proof. exact (@lem3660955 _93670 (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t) s). Qed.
Lemma lem3660958 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (@SUBSET _93670 t s) = (term872 _93670 t s).
Proof. exact (TRANS (@lem3660952 _93670 t s) (@lem3660956 _93670 t s)). Qed.
Lemma lem3660959 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3660960 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term72 _93670 t s) = (term873 _93670 t s).
Proof. exact (MK_COMB (@lem3660959) (@lem3660958 _93670 t s)). Qed.
Lemma lem3660961 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term210 _93670 _93677 s P f t) = (term874 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3660960 _93670 t s) (@lem3660941 _93670 _93677 P f t)). Qed.
Lemma lem3660962 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3660963 {_93677 : Type'} (P : type686 _93677) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3660970 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660971 {_93670 _93677 : Type'} (f : type528 _93670 _93677) (x : _93670 -> _93677) : (f x) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3660970 (_93670 -> _93677) (type678 _93670 _93677) f x). Qed.
Lemma lem3660972 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (@IMAGE _93670 _93677 f) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f).
Proof. exact (@lem3660971 _93670 _93677 (@IMAGE _93670 _93677) f). Qed.
Lemma lem3660973 {_93670 : Type'} (t : _93670 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3660974 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@IMAGE _93670 _93677 f t) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f t).
Proof. exact (MK_COMB (@lem3660972 _93670 _93677 f) (@lem3660973 _93670 t)). Qed.
Lemma lem3660976 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660977 {_93670 _93677 : Type'} (f : type678 _93670 _93677) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3660976 (_93670 -> Prop) (_93677 -> Prop) f x). Qed.
Lemma lem3660978 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f t) = (term785 _93670 _93677 f t).
Proof. exact (@lem3660977 _93670 _93677 (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f) t). Qed.
Lemma lem3660980 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@IMAGE _93670 _93677 f t) = (term785 _93670 _93677 f t).
Proof. exact (TRANS (@lem3660974 _93670 _93677 f t) (@lem3660978 _93670 _93677 f t)). Qed.
Lemma lem3660981 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term140 _93670 _93677 P f t) = (term838 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3660963 _93677 P) (@lem3660980 _93670 _93677 f t)). Qed.
Lemma lem3660983 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660984 {_93677 : Type'} (f : type686 _93677) (x : _93677 -> Prop) : (f x) = (@I ((_93677 -> Prop) -> Prop) f x).
Proof. exact (@lem3660983 (_93677 -> Prop) Prop f x). Qed.
Lemma lem3660985 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term838 _93670 _93677 P f t) = (term839 _93670 _93677 P f t).
Proof. exact (@lem3660984 _93677 P (term785 _93670 _93677 f t)). Qed.
Lemma lem3660986 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term140 _93670 _93677 P f t) = (term839 _93670 _93677 P f t).
Proof. exact (TRANS (@lem3660981 _93670 _93677 P f t) (@lem3660985 _93670 _93677 P f t)). Qed.
Lemma lem3660987 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term197 _93670 _93677 P f t) = (term875 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3660962) (@lem3660986 _93670 _93677 P f t)). Qed.
Lemma lem3660988 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3660989 {_93677 : Type'} : (@FINITE _93677) = (@FINITE _93677).
Proof. exact (eq_refl (@FINITE _93677)). Qed.
Lemma lem3660996 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3660997 {_93670 _93677 : Type'} (f : type528 _93670 _93677) (x : _93670 -> _93677) : (f x) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3660996 (_93670 -> _93677) (type678 _93670 _93677) f x). Qed.
Lemma lem3660998 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (@IMAGE _93670 _93677 f) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f).
Proof. exact (@lem3660997 _93670 _93677 (@IMAGE _93670 _93677) f). Qed.
Lemma lem3660999 {_93670 : Type'} (t : _93670 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3661000 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@IMAGE _93670 _93677 f t) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f t).
Proof. exact (MK_COMB (@lem3660998 _93670 _93677 f) (@lem3660999 _93670 t)). Qed.
Lemma lem3661002 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661003 {_93670 _93677 : Type'} (f : type678 _93670 _93677) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3661002 (_93670 -> Prop) (_93677 -> Prop) f x). Qed.
Lemma lem3661004 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f t) = (term785 _93670 _93677 f t).
Proof. exact (@lem3661003 _93670 _93677 (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f) t). Qed.
Lemma lem3661006 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@IMAGE _93670 _93677 f t) = (term785 _93670 _93677 f t).
Proof. exact (TRANS (@lem3661000 _93670 _93677 f t) (@lem3661004 _93670 _93677 f t)). Qed.
Lemma lem3661007 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term129 _93670 _93677 f t) = (term786 _93670 _93677 f t).
Proof. exact (MK_COMB (@lem3660989 _93677) (@lem3661006 _93670 _93677 f t)). Qed.
Lemma lem3661009 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661010 {_93677 : Type'} (f : type686 _93677) (x : _93677 -> Prop) : (f x) = (@I ((_93677 -> Prop) -> Prop) f x).
Proof. exact (@lem3661009 (_93677 -> Prop) Prop f x). Qed.
Lemma lem3661011 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term786 _93670 _93677 f t) = (term787 _93670 _93677 f t).
Proof. exact (@lem3661010 _93677 (@FINITE _93677) (term785 _93670 _93677 f t)). Qed.
Lemma lem3661012 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term129 _93670 _93677 f t) = (term787 _93670 _93677 f t).
Proof. exact (TRANS (@lem3661007 _93670 _93677 f t) (@lem3661011 _93670 _93677 f t)). Qed.
Lemma lem3661013 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term788 _93670 _93677 f t) = (term789 _93670 _93677 f t).
Proof. exact (MK_COMB (@lem3660988) (@lem3661012 _93670 _93677 f t)). Qed.
Lemma lem3661014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661015 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term790 _93670 _93677 f t) = (term791 _93670 _93677 f t).
Proof. exact (MK_COMB (@lem3661014) (@lem3661013 _93670 _93677 f t)). Qed.
Lemma lem3661016 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term184 _93670 _93677 P f t) = (term876 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3661015 _93670 _93677 f t) (@lem3660987 _93670 _93677 P f t)). Qed.
Lemma lem3661023 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : (term848 _93670 x''''' y''''') = (term848 _93670 x''''' y''''').
Proof. exact (eq_refl (term848 _93670 x''''' y''''')). Qed.
Lemma lem3661024 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3661025 {_93677 : Type'} : (@eq _93677) = (@eq _93677).
Proof. exact (eq_refl (@eq _93677)). Qed.
Lemma lem3661030 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661031 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3661030 _93670 _93677 f x). Qed.
Lemma lem3661033 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) : (f x''''') = (@I (_93670 -> _93677) f x''''').
Proof. exact (@lem3661031 _93670 _93677 f x'''''). Qed.
Lemma lem3661038 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661039 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3661038 _93670 _93677 f x). Qed.
Lemma lem3661041 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (f y''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (@lem3661039 _93670 _93677 f y'''''). Qed.
Lemma lem3661042 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) : (term840 _93670 _93677 f x''''') = (term841 _93670 _93677 f x''''').
Proof. exact (MK_COMB (@lem3661025 _93677) (@lem3661033 _93670 _93677 f x''''')). Qed.
Lemma lem3661043 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : ((f x''''') = (f y''''')) = ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')).
Proof. exact (MK_COMB (@lem3661042 _93670 _93677 f x''''') (@lem3661041 _93670 _93677 f y''''')). Qed.
Lemma lem3661044 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term842 _93670 _93677 x''''' f y''''') = (term843 _93670 _93677 x''''' f y''''').
Proof. exact (MK_COMB (@lem3661024) (@lem3661043 _93670 _93677 x''''' f y''''')). Qed.
Lemma lem3661045 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661046 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term844 _93670 _93677 x''''' f y''''') = (term845 _93670 _93677 x''''' f y''''').
Proof. exact (MK_COMB (@lem3661045) (@lem3661044 _93670 _93677 x''''' f y''''')). Qed.
Lemma lem3661047 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) : (term877 _93670 _93677 f x''''' y''''') = (term878 _93670 _93677 f x''''' y''''').
Proof. exact (MK_COMB (@lem3661046 _93670 _93677 x''''' f y''''') (@lem3661023 _93670 x''''' y''''')). Qed.
Lemma lem3661052 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : (x''''' = y''''') = (x''''' = y''''').
Proof. exact (eq_refl (x''''' = y''''')). Qed.
Lemma lem3661053 {_93677 : Type'} : (@eq _93677) = (@eq _93677).
Proof. exact (eq_refl (@eq _93677)). Qed.
Lemma lem3661058 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661059 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3661058 _93670 _93677 f x). Qed.
Lemma lem3661061 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) : (f x''''') = (@I (_93670 -> _93677) f x''''').
Proof. exact (@lem3661059 _93670 _93677 f x'''''). Qed.
Lemma lem3661066 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661067 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3661066 _93670 _93677 f x). Qed.
Lemma lem3661069 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (f y''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (@lem3661067 _93670 _93677 f y'''''). Qed.
Lemma lem3661070 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) : (term840 _93670 _93677 f x''''') = (term841 _93670 _93677 f x''''').
Proof. exact (MK_COMB (@lem3661053 _93677) (@lem3661061 _93670 _93677 f x''''')). Qed.
Lemma lem3661071 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : ((f x''''') = (f y''''')) = ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')).
Proof. exact (MK_COMB (@lem3661070 _93670 _93677 f x''''') (@lem3661069 _93670 _93677 f y''''')). Qed.
Lemma lem3661072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661073 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term849 _93670 _93677 x''''' f y''''') = (term850 _93670 _93677 x''''' f y''''').
Proof. exact (MK_COMB (@lem3661072) (@lem3661071 _93670 _93677 x''''' f y''''')). Qed.
Lemma lem3661074 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) : (term879 _93670 _93677 f x''''' y''''') = (term880 _93670 _93677 f x''''' y''''').
Proof. exact (MK_COMB (@lem3661073 _93670 _93677 x''''' f y''''') (@lem3661052 _93670 x''''' y''''')). Qed.
Lemma lem3661075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3661076 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) : (term881 _93670 _93677 f x''''' y''''') = (term882 _93670 _93677 f x''''' y''''').
Proof. exact (MK_COMB (@lem3661075) (@lem3661074 _93670 _93677 f x''''' y''''')). Qed.
Lemma lem3661077 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) : (term152 _93670 _93677 f x''''' y''''') = (term883 _93670 _93677 f x''''' y''''').
Proof. exact (MK_COMB (@lem3661076 _93670 _93677 f x''''' y''''') (@lem3661047 _93670 _93677 f x''''' y''''')). Qed.
Lemma lem3661084 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661085 {_93670 : Type'} (f : type1364 _93670) (x : _93670) : (f x) = (@I (_93670 -> (_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661084 _93670 (type686 _93670) f x). Qed.
Lemma lem3661086 {_93670 : Type'} (y''''' : _93670) : (@IN _93670 y''''') = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y''''').
Proof. exact (@lem3661085 _93670 (@IN _93670) y'''''). Qed.
Lemma lem3661087 {_93670 : Type'} (t : _93670 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3661088 {_93670 : Type'} (y''''' : _93670) (t : _93670 -> Prop) : (@IN _93670 y''''' t) = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y''''' t).
Proof. exact (MK_COMB (@lem3661086 _93670 y''''') (@lem3661087 _93670 t)). Qed.
Lemma lem3661090 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661091 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661090 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3661092 {_93670 : Type'} (y''''' : _93670) (t : _93670 -> Prop) : (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y''''' t) = (term856 _93670 y''''' t).
Proof. exact (@lem3661091 _93670 (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y''''') t). Qed.
Lemma lem3661094 {_93670 : Type'} (y''''' : _93670) (t : _93670 -> Prop) : (@IN _93670 y''''' t) = (term856 _93670 y''''' t).
Proof. exact (TRANS (@lem3661088 _93670 y''''' t) (@lem3661092 _93670 y''''' t)). Qed.
Lemma lem3661101 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661102 {_93670 : Type'} (f : type1364 _93670) (x : _93670) : (f x) = (@I (_93670 -> (_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661101 _93670 (type686 _93670) f x). Qed.
Lemma lem3661103 {_93670 : Type'} (x''''' : _93670) : (@IN _93670 x''''') = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x''''').
Proof. exact (@lem3661102 _93670 (@IN _93670) x'''''). Qed.
Lemma lem3661104 {_93670 : Type'} (t : _93670 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3661105 {_93670 : Type'} (x''''' : _93670) (t : _93670 -> Prop) : (@IN _93670 x''''' t) = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x''''' t).
Proof. exact (MK_COMB (@lem3661103 _93670 x''''') (@lem3661104 _93670 t)). Qed.
Lemma lem3661107 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661108 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661107 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3661109 {_93670 : Type'} (x''''' : _93670) (t : _93670 -> Prop) : (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x''''' t) = (term856 _93670 x''''' t).
Proof. exact (@lem3661108 _93670 (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x''''') t). Qed.
Lemma lem3661111 {_93670 : Type'} (x''''' : _93670) (t : _93670 -> Prop) : (@IN _93670 x''''' t) = (term856 _93670 x''''' t).
Proof. exact (TRANS (@lem3661105 _93670 x''''' t) (@lem3661109 _93670 x''''' t)). Qed.
Lemma lem3661112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3661113 {_93670 : Type'} (x''''' : _93670) (t : _93670 -> Prop) : (term884 _93670 x''''' t) = (term885 _93670 x''''' t).
Proof. exact (MK_COMB (@lem3661112) (@lem3661111 _93670 x''''' t)). Qed.
Lemma lem3661114 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (t : _93670 -> Prop) : (term158 _93670 x''''' y''''' t) = (term886 _93670 x''''' y''''' t).
Proof. exact (MK_COMB (@lem3661113 _93670 x''''' t) (@lem3661094 _93670 y''''' t)). Qed.
Lemma lem3661115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3661116 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (t : _93670 -> Prop) : (term154 _93670 x''''' y''''' t) = (term887 _93670 x''''' y''''' t).
Proof. exact (MK_COMB (@lem3661115) (@lem3661114 _93670 x''''' y''''' t)). Qed.
Lemma lem3661117 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) : (term156 _93670 _93677 t f x''''' y''''') = (term888 _93670 _93677 t f x''''' y''''').
Proof. exact (MK_COMB (@lem3661116 _93670 x''''' y''''' t) (@lem3661077 _93670 _93677 f x''''' y''''')). Qed.
Lemma lem3661118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661119 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) : (term249 _93670 _93677 t f x''''' y''''') = (term889 _93670 _93677 t f x''''' y''''').
Proof. exact (MK_COMB (@lem3661118) (@lem3661117 _93670 _93677 t f x''''' y''''')). Qed.
Lemma lem3661120 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term359 _93670 _93677 x''''' y''''' P f t) = (term890 _93670 _93677 x''''' y''''' P f t).
Proof. exact (MK_COMB (@lem3661119 _93670 _93677 t f x''''' y''''') (@lem3661016 _93670 _93677 P f t)). Qed.
Lemma lem3661121 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3661128 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661129 {_93670 : Type'} (f : type639 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661128 (_93670 -> Prop) (type686 _93670) f x). Qed.
Lemma lem3661130 {_93670 : Type'} (t : _93670 -> Prop) : (@SUBSET _93670 t) = (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t).
Proof. exact (@lem3661129 _93670 (@SUBSET _93670) t). Qed.
Lemma lem3661131 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3661132 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (@SUBSET _93670 t s) = (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t s).
Proof. exact (MK_COMB (@lem3661130 _93670 t) (@lem3661131 _93670 s)). Qed.
Lemma lem3661134 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661135 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661134 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3661136 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t s) = (term872 _93670 t s).
Proof. exact (@lem3661135 _93670 (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t) s). Qed.
Lemma lem3661138 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (@SUBSET _93670 t s) = (term872 _93670 t s).
Proof. exact (TRANS (@lem3661132 _93670 t s) (@lem3661136 _93670 t s)). Qed.
Lemma lem3661139 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term290 _93670 t s) = (term891 _93670 t s).
Proof. exact (MK_COMB (@lem3661121) (@lem3661138 _93670 t s)). Qed.
Lemma lem3661140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661141 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term192 _93670 t s) = (term892 _93670 t s).
Proof. exact (MK_COMB (@lem3661140) (@lem3661139 _93670 t s)). Qed.
Lemma lem3661142 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term386 _93670 _93677 s x''''' y''''' P f t) = (term893 _93670 _93677 s x''''' y''''' P f t).
Proof. exact (MK_COMB (@lem3661141 _93670 t s) (@lem3661120 _93670 _93677 x''''' y''''' P f t)). Qed.
Lemma lem3661143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3661144 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term420 _93670 _93677 s x''''' y''''' P f t) = (term894 _93670 _93677 s x''''' y''''' P f t).
Proof. exact (MK_COMB (@lem3661143) (@lem3661142 _93670 _93677 s x''''' y''''' P f t)). Qed.
Lemma lem3661145 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term422 _93670 _93677 x''''' y''''' s P f t) = (term895 _93670 _93677 x''''' y''''' s P f t).
Proof. exact (MK_COMB (@lem3661144 _93670 _93677 s x''''' y''''' P f t) (@lem3660961 _93670 _93677 s P f t)). Qed.
Lemma lem3661146 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3661147 {_93677 : Type'} (P : type686 _93677) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3661154 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661155 {_93670 _93677 : Type'} (f : type528 _93670 _93677) (x : _93670 -> _93677) : (f x) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3661154 (_93670 -> _93677) (type678 _93670 _93677) f x). Qed.
Lemma lem3661156 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (@IMAGE _93670 _93677 f) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f).
Proof. exact (@lem3661155 _93670 _93677 (@IMAGE _93670 _93677) f). Qed.
Lemma lem3661157 {_93670 : Type'} (t : _93670 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3661158 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@IMAGE _93670 _93677 f t) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f t).
Proof. exact (MK_COMB (@lem3661156 _93670 _93677 f) (@lem3661157 _93670 t)). Qed.
Lemma lem3661160 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661161 {_93670 _93677 : Type'} (f : type678 _93670 _93677) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3661160 (_93670 -> Prop) (_93677 -> Prop) f x). Qed.
Lemma lem3661162 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f t) = (term785 _93670 _93677 f t).
Proof. exact (@lem3661161 _93670 _93677 (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f) t). Qed.
Lemma lem3661164 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@IMAGE _93670 _93677 f t) = (term785 _93670 _93677 f t).
Proof. exact (TRANS (@lem3661158 _93670 _93677 f t) (@lem3661162 _93670 _93677 f t)). Qed.
Lemma lem3661165 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term140 _93670 _93677 P f t) = (term838 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3661147 _93677 P) (@lem3661164 _93670 _93677 f t)). Qed.
Lemma lem3661167 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661168 {_93677 : Type'} (f : type686 _93677) (x : _93677 -> Prop) : (f x) = (@I ((_93677 -> Prop) -> Prop) f x).
Proof. exact (@lem3661167 (_93677 -> Prop) Prop f x). Qed.
Lemma lem3661169 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term838 _93670 _93677 P f t) = (term839 _93670 _93677 P f t).
Proof. exact (@lem3661168 _93677 P (term785 _93670 _93677 f t)). Qed.
Lemma lem3661170 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term140 _93670 _93677 P f t) = (term839 _93670 _93677 P f t).
Proof. exact (TRANS (@lem3661165 _93670 _93677 P f t) (@lem3661169 _93670 _93677 P f t)). Qed.
Lemma lem3661171 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term197 _93670 _93677 P f t) = (term875 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3661146) (@lem3661170 _93670 _93677 P f t)). Qed.
Lemma lem3661178 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : (term848 _93670 x''''' y''''') = (term848 _93670 x''''' y''''').
Proof. exact (eq_refl (term848 _93670 x''''' y''''')). Qed.
Lemma lem3661179 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3661180 {_93677 : Type'} : (@eq _93677) = (@eq _93677).
Proof. exact (eq_refl (@eq _93677)). Qed.
Lemma lem3661185 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661186 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3661185 _93670 _93677 f x). Qed.
Lemma lem3661188 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) : (f x''''') = (@I (_93670 -> _93677) f x''''').
Proof. exact (@lem3661186 _93670 _93677 f x'''''). Qed.
Lemma lem3661193 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661194 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3661193 _93670 _93677 f x). Qed.
Lemma lem3661196 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (f y''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (@lem3661194 _93670 _93677 f y'''''). Qed.
Lemma lem3661197 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) : (term840 _93670 _93677 f x''''') = (term841 _93670 _93677 f x''''').
Proof. exact (MK_COMB (@lem3661180 _93677) (@lem3661188 _93670 _93677 f x''''')). Qed.
Lemma lem3661198 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : ((f x''''') = (f y''''')) = ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')).
Proof. exact (MK_COMB (@lem3661197 _93670 _93677 f x''''') (@lem3661196 _93670 _93677 f y''''')). Qed.
Lemma lem3661199 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term842 _93670 _93677 x''''' f y''''') = (term843 _93670 _93677 x''''' f y''''').
Proof. exact (MK_COMB (@lem3661179) (@lem3661198 _93670 _93677 x''''' f y''''')). Qed.
Lemma lem3661200 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661201 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term844 _93670 _93677 x''''' f y''''') = (term845 _93670 _93677 x''''' f y''''').
Proof. exact (MK_COMB (@lem3661200) (@lem3661199 _93670 _93677 x''''' f y''''')). Qed.
Lemma lem3661202 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) : (term877 _93670 _93677 f x''''' y''''') = (term878 _93670 _93677 f x''''' y''''').
Proof. exact (MK_COMB (@lem3661201 _93670 _93677 x''''' f y''''') (@lem3661178 _93670 x''''' y''''')). Qed.
Lemma lem3661207 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : (x''''' = y''''') = (x''''' = y''''').
Proof. exact (eq_refl (x''''' = y''''')). Qed.
Lemma lem3661208 {_93677 : Type'} : (@eq _93677) = (@eq _93677).
Proof. exact (eq_refl (@eq _93677)). Qed.
Lemma lem3661213 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661214 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3661213 _93670 _93677 f x). Qed.
Lemma lem3661216 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) : (f x''''') = (@I (_93670 -> _93677) f x''''').
Proof. exact (@lem3661214 _93670 _93677 f x'''''). Qed.
Lemma lem3661221 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661222 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3661221 _93670 _93677 f x). Qed.
Lemma lem3661224 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (f y''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (@lem3661222 _93670 _93677 f y'''''). Qed.
Lemma lem3661225 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) : (term840 _93670 _93677 f x''''') = (term841 _93670 _93677 f x''''').
Proof. exact (MK_COMB (@lem3661208 _93677) (@lem3661216 _93670 _93677 f x''''')). Qed.
Lemma lem3661226 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : ((f x''''') = (f y''''')) = ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')).
Proof. exact (MK_COMB (@lem3661225 _93670 _93677 f x''''') (@lem3661224 _93670 _93677 f y''''')). Qed.
Lemma lem3661227 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661228 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term849 _93670 _93677 x''''' f y''''') = (term850 _93670 _93677 x''''' f y''''').
Proof. exact (MK_COMB (@lem3661227) (@lem3661226 _93670 _93677 x''''' f y''''')). Qed.
Lemma lem3661229 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) : (term879 _93670 _93677 f x''''' y''''') = (term880 _93670 _93677 f x''''' y''''').
Proof. exact (MK_COMB (@lem3661228 _93670 _93677 x''''' f y''''') (@lem3661207 _93670 x''''' y''''')). Qed.
Lemma lem3661230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3661231 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) : (term881 _93670 _93677 f x''''' y''''') = (term882 _93670 _93677 f x''''' y''''').
Proof. exact (MK_COMB (@lem3661230) (@lem3661229 _93670 _93677 f x''''' y''''')). Qed.
Lemma lem3661232 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) : (term152 _93670 _93677 f x''''' y''''') = (term883 _93670 _93677 f x''''' y''''').
Proof. exact (MK_COMB (@lem3661231 _93670 _93677 f x''''' y''''') (@lem3661202 _93670 _93677 f x''''' y''''')). Qed.
Lemma lem3661239 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661240 {_93670 : Type'} (f : type1364 _93670) (x : _93670) : (f x) = (@I (_93670 -> (_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661239 _93670 (type686 _93670) f x). Qed.
Lemma lem3661241 {_93670 : Type'} (y''''' : _93670) : (@IN _93670 y''''') = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y''''').
Proof. exact (@lem3661240 _93670 (@IN _93670) y'''''). Qed.
Lemma lem3661242 {_93670 : Type'} (t : _93670 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3661243 {_93670 : Type'} (y''''' : _93670) (t : _93670 -> Prop) : (@IN _93670 y''''' t) = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y''''' t).
Proof. exact (MK_COMB (@lem3661241 _93670 y''''') (@lem3661242 _93670 t)). Qed.
Lemma lem3661245 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661246 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661245 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3661247 {_93670 : Type'} (y''''' : _93670) (t : _93670 -> Prop) : (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y''''' t) = (term856 _93670 y''''' t).
Proof. exact (@lem3661246 _93670 (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y''''') t). Qed.
Lemma lem3661249 {_93670 : Type'} (y''''' : _93670) (t : _93670 -> Prop) : (@IN _93670 y''''' t) = (term856 _93670 y''''' t).
Proof. exact (TRANS (@lem3661243 _93670 y''''' t) (@lem3661247 _93670 y''''' t)). Qed.
Lemma lem3661256 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661257 {_93670 : Type'} (f : type1364 _93670) (x : _93670) : (f x) = (@I (_93670 -> (_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661256 _93670 (type686 _93670) f x). Qed.
Lemma lem3661258 {_93670 : Type'} (x''''' : _93670) : (@IN _93670 x''''') = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x''''').
Proof. exact (@lem3661257 _93670 (@IN _93670) x'''''). Qed.
Lemma lem3661259 {_93670 : Type'} (t : _93670 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3661260 {_93670 : Type'} (x''''' : _93670) (t : _93670 -> Prop) : (@IN _93670 x''''' t) = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x''''' t).
Proof. exact (MK_COMB (@lem3661258 _93670 x''''') (@lem3661259 _93670 t)). Qed.
Lemma lem3661262 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661263 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661262 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3661264 {_93670 : Type'} (x''''' : _93670) (t : _93670 -> Prop) : (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x''''' t) = (term856 _93670 x''''' t).
Proof. exact (@lem3661263 _93670 (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x''''') t). Qed.
Lemma lem3661266 {_93670 : Type'} (x''''' : _93670) (t : _93670 -> Prop) : (@IN _93670 x''''' t) = (term856 _93670 x''''' t).
Proof. exact (TRANS (@lem3661260 _93670 x''''' t) (@lem3661264 _93670 x''''' t)). Qed.
Lemma lem3661267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3661268 {_93670 : Type'} (x''''' : _93670) (t : _93670 -> Prop) : (term884 _93670 x''''' t) = (term885 _93670 x''''' t).
Proof. exact (MK_COMB (@lem3661267) (@lem3661266 _93670 x''''' t)). Qed.
Lemma lem3661269 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (t : _93670 -> Prop) : (term158 _93670 x''''' y''''' t) = (term886 _93670 x''''' y''''' t).
Proof. exact (MK_COMB (@lem3661268 _93670 x''''' t) (@lem3661249 _93670 y''''' t)). Qed.
Lemma lem3661270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3661271 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (t : _93670 -> Prop) : (term154 _93670 x''''' y''''' t) = (term887 _93670 x''''' y''''' t).
Proof. exact (MK_COMB (@lem3661270) (@lem3661269 _93670 x''''' y''''' t)). Qed.
Lemma lem3661272 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) : (term156 _93670 _93677 t f x''''' y''''') = (term888 _93670 _93677 t f x''''' y''''').
Proof. exact (MK_COMB (@lem3661271 _93670 x''''' y''''' t) (@lem3661232 _93670 _93677 f x''''' y''''')). Qed.
Lemma lem3661273 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661274 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) : (term249 _93670 _93677 t f x''''' y''''') = (term889 _93670 _93677 t f x''''' y''''').
Proof. exact (MK_COMB (@lem3661273) (@lem3661272 _93670 _93677 t f x''''' y''''')). Qed.
Lemma lem3661275 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term251 _93670 _93677 x''''' y''''' P f t) = (term896 _93670 _93677 x''''' y''''' P f t).
Proof. exact (MK_COMB (@lem3661274 _93670 _93677 t f x''''' y''''') (@lem3661171 _93670 _93677 P f t)). Qed.
Lemma lem3661276 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3661281 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661282 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661281 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3661284 {_93670 : Type'} (t : _93670 -> Prop) : (@FINITE _93670 t) = (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t).
Proof. exact (@lem3661282 _93670 (@FINITE _93670) t). Qed.
Lemma lem3661285 {_93670 : Type'} (t : _93670 -> Prop) : (term262 _93670 t) = (term794 _93670 t).
Proof. exact (MK_COMB (@lem3661276) (@lem3661284 _93670 t)). Qed.
Lemma lem3661286 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661287 {_93670 : Type'} (t : _93670 -> Prop) : (term202 _93670 t) = (term897 _93670 t).
Proof. exact (MK_COMB (@lem3661286) (@lem3661285 _93670 t)). Qed.
Lemma lem3661288 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term281 _93670 _93677 x''''' y''''' P f t) = (term898 _93670 _93677 x''''' y''''' P f t).
Proof. exact (MK_COMB (@lem3661287 _93670 t) (@lem3661275 _93670 _93677 x''''' y''''' P f t)). Qed.
Lemma lem3661289 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3661296 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661297 {_93670 : Type'} (f : type639 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661296 (_93670 -> Prop) (type686 _93670) f x). Qed.
Lemma lem3661298 {_93670 : Type'} (t : _93670 -> Prop) : (@SUBSET _93670 t) = (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t).
Proof. exact (@lem3661297 _93670 (@SUBSET _93670) t). Qed.
Lemma lem3661299 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3661300 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (@SUBSET _93670 t s) = (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t s).
Proof. exact (MK_COMB (@lem3661298 _93670 t) (@lem3661299 _93670 s)). Qed.
Lemma lem3661302 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661303 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661302 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3661304 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t s) = (term872 _93670 t s).
Proof. exact (@lem3661303 _93670 (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t) s). Qed.
Lemma lem3661306 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (@SUBSET _93670 t s) = (term872 _93670 t s).
Proof. exact (TRANS (@lem3661300 _93670 t s) (@lem3661304 _93670 t s)). Qed.
Lemma lem3661307 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term290 _93670 t s) = (term891 _93670 t s).
Proof. exact (MK_COMB (@lem3661289) (@lem3661306 _93670 t s)). Qed.
Lemma lem3661308 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661309 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term192 _93670 t s) = (term892 _93670 t s).
Proof. exact (MK_COMB (@lem3661308) (@lem3661307 _93670 t s)). Qed.
Lemma lem3661310 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term309 _93670 _93677 s x''''' y''''' P f t) = (term899 _93670 _93677 s x''''' y''''' P f t).
Proof. exact (MK_COMB (@lem3661309 _93670 t s) (@lem3661288 _93670 _93677 x''''' y''''' P f t)). Qed.
Lemma lem3661311 {_93677 : Type'} (P : type686 _93677) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3661318 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661319 {_93670 _93677 : Type'} (f : type528 _93670 _93677) (x : _93670 -> _93677) : (f x) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3661318 (_93670 -> _93677) (type678 _93670 _93677) f x). Qed.
Lemma lem3661320 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (@IMAGE _93670 _93677 f) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f).
Proof. exact (@lem3661319 _93670 _93677 (@IMAGE _93670 _93677) f). Qed.
Lemma lem3661321 {_93670 : Type'} (t : _93670 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3661322 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@IMAGE _93670 _93677 f t) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f t).
Proof. exact (MK_COMB (@lem3661320 _93670 _93677 f) (@lem3661321 _93670 t)). Qed.
Lemma lem3661324 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661325 {_93670 _93677 : Type'} (f : type678 _93670 _93677) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3661324 (_93670 -> Prop) (_93677 -> Prop) f x). Qed.
Lemma lem3661326 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f t) = (term785 _93670 _93677 f t).
Proof. exact (@lem3661325 _93670 _93677 (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f) t). Qed.
Lemma lem3661328 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@IMAGE _93670 _93677 f t) = (term785 _93670 _93677 f t).
Proof. exact (TRANS (@lem3661322 _93670 _93677 f t) (@lem3661326 _93670 _93677 f t)). Qed.
Lemma lem3661329 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term140 _93670 _93677 P f t) = (term838 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3661311 _93677 P) (@lem3661328 _93670 _93677 f t)). Qed.
Lemma lem3661331 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661332 {_93677 : Type'} (f : type686 _93677) (x : _93677 -> Prop) : (f x) = (@I ((_93677 -> Prop) -> Prop) f x).
Proof. exact (@lem3661331 (_93677 -> Prop) Prop f x). Qed.
Lemma lem3661333 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term838 _93670 _93677 P f t) = (term839 _93670 _93677 P f t).
Proof. exact (@lem3661332 _93677 P (term785 _93670 _93677 f t)). Qed.
Lemma lem3661334 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term140 _93670 _93677 P f t) = (term839 _93670 _93677 P f t).
Proof. exact (TRANS (@lem3661329 _93670 _93677 P f t) (@lem3661333 _93670 _93677 P f t)). Qed.
Lemma lem3661335 {_93677 : Type'} : (@FINITE _93677) = (@FINITE _93677).
Proof. exact (eq_refl (@FINITE _93677)). Qed.
Lemma lem3661342 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661343 {_93670 _93677 : Type'} (f : type528 _93670 _93677) (x : _93670 -> _93677) : (f x) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3661342 (_93670 -> _93677) (type678 _93670 _93677) f x). Qed.
Lemma lem3661344 {_93670 _93677 : Type'} (f : _93670 -> _93677) : (@IMAGE _93670 _93677 f) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f).
Proof. exact (@lem3661343 _93670 _93677 (@IMAGE _93670 _93677) f). Qed.
Lemma lem3661345 {_93670 : Type'} (t : _93670 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3661346 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@IMAGE _93670 _93677 f t) = (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f t).
Proof. exact (MK_COMB (@lem3661344 _93670 _93677 f) (@lem3661345 _93670 t)). Qed.
Lemma lem3661348 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661349 {_93670 _93677 : Type'} (f : type678 _93670 _93677) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> _93677 -> Prop) f x).
Proof. exact (@lem3661348 (_93670 -> Prop) (_93677 -> Prop) f x). Qed.
Lemma lem3661350 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f t) = (term785 _93670 _93677 f t).
Proof. exact (@lem3661349 _93670 _93677 (@I ((_93670 -> _93677) -> (_93670 -> Prop) -> _93677 -> Prop) (@IMAGE _93670 _93677) f) t). Qed.
Lemma lem3661352 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (@IMAGE _93670 _93677 f t) = (term785 _93670 _93677 f t).
Proof. exact (TRANS (@lem3661346 _93670 _93677 f t) (@lem3661350 _93670 _93677 f t)). Qed.
Lemma lem3661353 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term129 _93670 _93677 f t) = (term786 _93670 _93677 f t).
Proof. exact (MK_COMB (@lem3661335 _93677) (@lem3661352 _93670 _93677 f t)). Qed.
Lemma lem3661355 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661356 {_93677 : Type'} (f : type686 _93677) (x : _93677 -> Prop) : (f x) = (@I ((_93677 -> Prop) -> Prop) f x).
Proof. exact (@lem3661355 (_93677 -> Prop) Prop f x). Qed.
Lemma lem3661357 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term786 _93670 _93677 f t) = (term787 _93670 _93677 f t).
Proof. exact (@lem3661356 _93677 (@FINITE _93677) (term785 _93670 _93677 f t)). Qed.
Lemma lem3661358 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term129 _93670 _93677 f t) = (term787 _93670 _93677 f t).
Proof. exact (TRANS (@lem3661353 _93670 _93677 f t) (@lem3661357 _93670 _93677 f t)). Qed.
Lemma lem3661359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3661360 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term900 _93670 _93677 f t) = (term901 _93670 _93677 f t).
Proof. exact (MK_COMB (@lem3661359) (@lem3661358 _93670 _93677 f t)). Qed.
Lemma lem3661361 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term68 _93670 _93677 P f t) = (term902 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3661360 _93670 _93677 f t) (@lem3661334 _93670 _93677 P f t)). Qed.
Lemma lem3661366 {_93670 : Type'} (x : _93670) (y : _93670) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3661367 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3661368 {_93677 : Type'} : (@eq _93677) = (@eq _93677).
Proof. exact (eq_refl (@eq _93677)). Qed.
Lemma lem3661373 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661375 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3661373 _93670 _93677 f x). Qed.
Lemma lem3661380 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661381 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3661380 _93670 _93677 f x). Qed.
Lemma lem3661383 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y : _93670) : (f y) = (@I (_93670 -> _93677) f y).
Proof. exact (@lem3661381 _93670 _93677 f y). Qed.
Lemma lem3661384 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (term840 _93670 _93677 f x) = (term841 _93670 _93677 f x).
Proof. exact (MK_COMB (@lem3661368 _93677) (@lem3661375 _93670 _93677 f x)). Qed.
Lemma lem3661385 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (y : _93670) : ((f x) = (f y)) = ((@I (_93670 -> _93677) f x) = (@I (_93670 -> _93677) f y)).
Proof. exact (MK_COMB (@lem3661384 _93670 _93677 f x) (@lem3661383 _93670 _93677 f y)). Qed.
Lemma lem3661386 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (y : _93670) : (term842 _93670 _93677 x f y) = (term843 _93670 _93677 x f y).
Proof. exact (MK_COMB (@lem3661367) (@lem3661385 _93670 _93677 x f y)). Qed.
Lemma lem3661387 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661388 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (y : _93670) : (term844 _93670 _93677 x f y) = (term845 _93670 _93677 x f y).
Proof. exact (MK_COMB (@lem3661387) (@lem3661386 _93670 _93677 x f y)). Qed.
Lemma lem3661389 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term846 _93670 _93677 f x y) = (term847 _93670 _93677 f x y).
Proof. exact (MK_COMB (@lem3661388 _93670 _93677 x f y) (@lem3661366 _93670 x y)). Qed.
Lemma lem3661396 {_93670 : Type'} (x : _93670) (y : _93670) : (term848 _93670 x y) = (term848 _93670 x y).
Proof. exact (eq_refl (term848 _93670 x y)). Qed.
Lemma lem3661397 {_93677 : Type'} : (@eq _93677) = (@eq _93677).
Proof. exact (eq_refl (@eq _93677)). Qed.
Lemma lem3661402 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661404 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3661402 _93670 _93677 f x). Qed.
Lemma lem3661409 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661410 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (f x) = (@I (_93670 -> _93677) f x).
Proof. exact (@lem3661409 _93670 _93677 f x). Qed.
Lemma lem3661412 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y : _93670) : (f y) = (@I (_93670 -> _93677) f y).
Proof. exact (@lem3661410 _93670 _93677 f y). Qed.
Lemma lem3661413 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) : (term840 _93670 _93677 f x) = (term841 _93670 _93677 f x).
Proof. exact (MK_COMB (@lem3661397 _93677) (@lem3661404 _93670 _93677 f x)). Qed.
Lemma lem3661414 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (y : _93670) : ((f x) = (f y)) = ((@I (_93670 -> _93677) f x) = (@I (_93670 -> _93677) f y)).
Proof. exact (MK_COMB (@lem3661413 _93670 _93677 f x) (@lem3661412 _93670 _93677 f y)). Qed.
Lemma lem3661415 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661416 {_93670 _93677 : Type'} (x : _93670) (f : _93670 -> _93677) (y : _93670) : (term849 _93670 _93677 x f y) = (term850 _93670 _93677 x f y).
Proof. exact (MK_COMB (@lem3661415) (@lem3661414 _93670 _93677 x f y)). Qed.
Lemma lem3661417 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term851 _93670 _93677 f x y) = (term852 _93670 _93677 f x y).
Proof. exact (MK_COMB (@lem3661416 _93670 _93677 x f y) (@lem3661396 _93670 x y)). Qed.
Lemma lem3661418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3661419 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term853 _93670 _93677 f x y) = (term854 _93670 _93677 f x y).
Proof. exact (MK_COMB (@lem3661418) (@lem3661417 _93670 _93677 f x y)). Qed.
Lemma lem3661420 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term153 _93670 _93677 f x y) = (term855 _93670 _93677 f x y).
Proof. exact (MK_COMB (@lem3661419 _93670 _93677 f x y) (@lem3661389 _93670 _93677 f x y)). Qed.
Lemma lem3661421 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3661428 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661429 {_93670 : Type'} (f : type1364 _93670) (x : _93670) : (f x) = (@I (_93670 -> (_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661428 _93670 (type686 _93670) f x). Qed.
Lemma lem3661430 {_93670 : Type'} (y : _93670) : (@IN _93670 y) = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y).
Proof. exact (@lem3661429 _93670 (@IN _93670) y). Qed.
Lemma lem3661431 {_93670 : Type'} (t : _93670 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3661432 {_93670 : Type'} (y : _93670) (t : _93670 -> Prop) : (@IN _93670 y t) = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y t).
Proof. exact (MK_COMB (@lem3661430 _93670 y) (@lem3661431 _93670 t)). Qed.
Lemma lem3661434 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661435 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661434 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3661436 {_93670 : Type'} (y : _93670) (t : _93670 -> Prop) : (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y t) = (term856 _93670 y t).
Proof. exact (@lem3661435 _93670 (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) y) t). Qed.
Lemma lem3661438 {_93670 : Type'} (y : _93670) (t : _93670 -> Prop) : (@IN _93670 y t) = (term856 _93670 y t).
Proof. exact (TRANS (@lem3661432 _93670 y t) (@lem3661436 _93670 y t)). Qed.
Lemma lem3661439 {_93670 : Type'} (y : _93670) (t : _93670 -> Prop) : (term857 _93670 y t) = (term858 _93670 y t).
Proof. exact (MK_COMB (@lem3661421) (@lem3661438 _93670 y t)). Qed.
Lemma lem3661440 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3661447 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661448 {_93670 : Type'} (f : type1364 _93670) (x : _93670) : (f x) = (@I (_93670 -> (_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661447 _93670 (type686 _93670) f x). Qed.
Lemma lem3661449 {_93670 : Type'} (x : _93670) : (@IN _93670 x) = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x).
Proof. exact (@lem3661448 _93670 (@IN _93670) x). Qed.
Lemma lem3661450 {_93670 : Type'} (t : _93670 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3661451 {_93670 : Type'} (x : _93670) (t : _93670 -> Prop) : (@IN _93670 x t) = (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x t).
Proof. exact (MK_COMB (@lem3661449 _93670 x) (@lem3661450 _93670 t)). Qed.
Lemma lem3661453 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661454 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661453 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3661455 {_93670 : Type'} (x : _93670) (t : _93670 -> Prop) : (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x t) = (term856 _93670 x t).
Proof. exact (@lem3661454 _93670 (@I (_93670 -> (_93670 -> Prop) -> Prop) (@IN _93670) x) t). Qed.
Lemma lem3661457 {_93670 : Type'} (x : _93670) (t : _93670 -> Prop) : (@IN _93670 x t) = (term856 _93670 x t).
Proof. exact (TRANS (@lem3661451 _93670 x t) (@lem3661455 _93670 x t)). Qed.
Lemma lem3661458 {_93670 : Type'} (x : _93670) (t : _93670 -> Prop) : (term857 _93670 x t) = (term858 _93670 x t).
Proof. exact (MK_COMB (@lem3661440) (@lem3661457 _93670 x t)). Qed.
Lemma lem3661459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661460 {_93670 : Type'} (x : _93670) (t : _93670 -> Prop) : (term859 _93670 x t) = (term860 _93670 x t).
Proof. exact (MK_COMB (@lem3661459) (@lem3661458 _93670 x t)). Qed.
Lemma lem3661461 {_93670 : Type'} (x : _93670) (y : _93670) (t : _93670 -> Prop) : (term150 _93670 x y t) = (term861 _93670 x y t).
Proof. exact (MK_COMB (@lem3661460 _93670 x t) (@lem3661439 _93670 y t)). Qed.
Lemma lem3661462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661463 {_93670 : Type'} (x : _93670) (y : _93670) (t : _93670 -> Prop) : (term160 _93670 x y t) = (term862 _93670 x y t).
Proof. exact (MK_COMB (@lem3661462) (@lem3661461 _93670 x y t)). Qed.
Lemma lem3661464 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term162 _93670 _93677 t f x y) = (term863 _93670 _93677 t f x y).
Proof. exact (MK_COMB (@lem3661463 _93670 x y t) (@lem3661420 _93670 _93677 f x y)). Qed.
Lemma lem3661465 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term172 _93670 _93677 t f x) = (term864 _93670 _93677 t f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3661464 _93670 _93677 t f x y)). Qed.
Lemma lem3661466 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3661467 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term173 _93670 _93677 t f x) = (term865 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3661466 _93670) (@lem3661465 _93670 _93677 t f x)). Qed.
Lemma lem3661468 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term181 _93670 _93677 t f) = (term866 _93670 _93677 t f).
Proof. exact (fun_ext (fun x : _93670 => @lem3661467 _93670 _93677 t f x)). Qed.
Lemma lem3661469 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3661470 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term182 _93670 _93677 t f) = (term867 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3661469 _93670) (@lem3661468 _93670 _93677 t f)). Qed.
Lemma lem3661471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3661472 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term190 _93670 _93677 t f) = (term868 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3661471) (@lem3661470 _93670 _93677 t f)). Qed.
Lemma lem3661473 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term191 _93670 _93677 P f t) = (term903 _93670 _93677 P f t).
Proof. exact (MK_COMB (@lem3661472 _93670 _93677 t f) (@lem3661361 _93670 _93677 P f t)). Qed.
Lemma lem3661480 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661481 {_93670 : Type'} (f : type639 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661480 (_93670 -> Prop) (type686 _93670) f x). Qed.
Lemma lem3661482 {_93670 : Type'} (t : _93670 -> Prop) : (@SUBSET _93670 t) = (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t).
Proof. exact (@lem3661481 _93670 (@SUBSET _93670) t). Qed.
Lemma lem3661483 {_93670 : Type'} (s : _93670 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3661484 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (@SUBSET _93670 t s) = (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t s).
Proof. exact (MK_COMB (@lem3661482 _93670 t) (@lem3661483 _93670 s)). Qed.
Lemma lem3661486 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3661487 {_93670 : Type'} (f : type686 _93670) (x : _93670 -> Prop) : (f x) = (@I ((_93670 -> Prop) -> Prop) f x).
Proof. exact (@lem3661486 (_93670 -> Prop) Prop f x). Qed.
Lemma lem3661488 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t s) = (term872 _93670 t s).
Proof. exact (@lem3661487 _93670 (@I ((_93670 -> Prop) -> (_93670 -> Prop) -> Prop) (@SUBSET _93670) t) s). Qed.
Lemma lem3661490 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (@SUBSET _93670 t s) = (term872 _93670 t s).
Proof. exact (TRANS (@lem3661484 _93670 t s) (@lem3661488 _93670 t s)). Qed.
Lemma lem3661491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3661492 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term72 _93670 t s) = (term873 _93670 t s).
Proof. exact (MK_COMB (@lem3661491) (@lem3661490 _93670 t s)). Qed.
Lemma lem3661493 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term196 _93670 _93677 s P f t) = (term904 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3661492 _93670 t s) (@lem3661473 _93670 _93677 P f t)). Qed.
Lemma lem3661494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3661495 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term216 _93670 _93677 s P f t) = (term905 _93670 _93677 s P f t).
Proof. exact (MK_COMB (@lem3661494) (@lem3661493 _93670 _93677 s P f t)). Qed.
Lemma lem3661496 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term338 _93670 _93677 s x''''' y''''' P f t) = (term906 _93670 _93677 s x''''' y''''' P f t).
Proof. exact (MK_COMB (@lem3661495 _93670 _93677 s P f t) (@lem3661310 _93670 _93677 s x''''' y''''' P f t)). Qed.
Lemma lem3661497 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3661498 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term461 _93670 _93677 s x''''' y''''' P f t) = (term907 _93670 _93677 s x''''' y''''' P f t).
Proof. exact (MK_COMB (@lem3661497) (@lem3661496 _93670 _93677 s x''''' y''''' P f t)). Qed.
Lemma lem3661499 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term463 _93670 _93677 x''''' y''''' s P f t) = (term908 _93670 _93677 x''''' y''''' s P f t).
Proof. exact (MK_COMB (@lem3661498 _93670 _93677 s x''''' y''''' P f t) (@lem3661145 _93670 _93677 x''''' y''''' s P f t)). Qed.
Lemma lem3661500 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term463 _93670 _93677 x''''' y''''' s P f t) : term908 _93670 _93677 x''''' y''''' s P f t.
Proof. exact (EQ_MP (@lem3661499 _93670 _93677 x''''' y''''' s P f t) (@lem3659534 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3661501 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term906 _93670 _93677 s x''''' y''''' P f t.
Proof. exact (h1). Qed.
Lemma lem3661502 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term895 _93670 _93677 x''''' y''''' s P f t.
Proof. exact (h1). Qed.
Lemma lem3661503 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term899 _93670 _93677 s x''''' y''''' P f t.
Proof. exact (proj2 (@lem3661501 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3661504 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term904 _93670 _93677 s P f t.
Proof. exact (proj1 (@lem3661501 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3661505 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term903 _93670 _93677 P f t.
Proof. exact (proj2 (@lem3661504 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3661507 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term902 _93670 _93677 P f t.
Proof. exact (proj2 (@lem3661505 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3661508 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term867 _93670 _93677 t f.
Proof. exact (proj1 (@lem3661505 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3661512 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term898 _93670 _93677 x''''' y''''' P f t) : term898 _93670 _93677 x''''' y''''' P f t.
Proof. exact (h1). Qed.
Lemma lem3661514 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term896 _93670 _93677 x''''' y''''' P f t) : term896 _93670 _93677 x''''' y''''' P f t.
Proof. exact (h1). Qed.
Lemma lem3661515 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term888 _93670 _93677 t f x''''' y'''''.
Proof. exact (h1). Qed.
Lemma lem3661517 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term883 _93670 _93677 f x''''' y'''''.
Proof. exact (proj2 (@lem3661515 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3661518 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term886 _93670 x''''' y''''' t.
Proof. exact (proj1 (@lem3661515 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3661519 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term878 _93670 _93677 f x''''' y'''''.
Proof. exact (proj2 (@lem3661517 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3661520 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term880 _93670 _93677 f x''''' y'''''.
Proof. exact (proj1 (@lem3661517 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3661529 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term874 _93670 _93677 s P f t.
Proof. exact (proj2 (@lem3661502 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3661530 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term893 _93670 _93677 s x''''' y''''' P f t.
Proof. exact (proj1 (@lem3661502 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3661531 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term871 _93670 _93677 P f t.
Proof. exact (proj2 (@lem3661529 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3661533 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term869 _93670 _93677 P f t.
Proof. exact (proj2 (@lem3661531 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3661536 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term867 _93670 _93677 t f.
Proof. exact (proj1 (@lem3661533 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3661538 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term890 _93670 _93677 x''''' y''''' P f t) : term890 _93670 _93677 x''''' y''''' P f t.
Proof. exact (h1). Qed.
Lemma lem3661539 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term888 _93670 _93677 t f x''''' y'''''.
Proof. exact (h1). Qed.
Lemma lem3661540 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term876 _93670 _93677 P f t) : term876 _93670 _93677 P f t.
Proof. exact (h1). Qed.
Lemma lem3661541 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term883 _93670 _93677 f x''''' y'''''.
Proof. exact (proj2 (@lem3661539 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3661542 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term886 _93670 x''''' y''''' t.
Proof. exact (proj1 (@lem3661539 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3661543 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term878 _93670 _93677 f x''''' y'''''.
Proof. exact (proj2 (@lem3661541 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3661544 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term880 _93670 _93677 f x''''' y'''''.
Proof. exact (proj1 (@lem3661541 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3662044 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) (h1 : term891 _93670 t s) : term891 _93670 t s.
Proof. exact (h1). Qed.
Lemma lem3662423 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term832 _93670 _93677 x'''' y'''' f s) = (term909 _93670 _93677 x'''' y'''' f s).
Proof. exact (@lem19490 (term798 _93670 _93677 f s) (term828 _93670 _93677 x'''' y'''' f s) (term793 _93670 _93677 f s)). Qed.
Lemma lem3662424 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term910 _93670 _93677 x'''' y'''' f s) = (term911 _93670 _93677 x'''' y'''' f s).
Proof. exact (@lem19699 (term824 _93670 _93677 x'''' y'''' f s) (term806 _93670 _93677 x'''' y'''' f s) (term793 _93670 _93677 f s)). Qed.
Lemma lem3662425 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term912 _93670 _93677 x'''' y'''' f s) = (term912 _93670 _93677 x'''' y'''' f s).
Proof. exact (eq_refl (term912 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662426 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term913 _93670 _93677 x'''' y'''' f s) = (term914 _93670 _93677 x'''' y'''' f s).
Proof. exact (@lem19699 (term818 _93670 _93677 x'''' f s) (term822 _93670 _93677 x'''' y'''' f s) (term793 _93670 _93677 f s)). Qed.
Lemma lem3662433 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term915 _93670 _93677 x'''' y'''' f s) = (term916 _93670 _93677 x'''' y'''' f s).
Proof. exact (@lem19699 (term818 _93670 _93677 y'''' f s) ((term809 _93670 _93677 x'''' f s) = (term809 _93670 _93677 y'''' f s)) (term793 _93670 _93677 f s)). Qed.
Lemma lem3662436 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term917 _93670 _93677 x'''' f s) = (term917 _93670 _93677 x'''' f s).
Proof. exact (eq_refl (term917 _93670 _93677 x'''' f s)). Qed.
Lemma lem3662437 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term914 _93670 _93677 x'''' y'''' f s) = (term918 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3662436 _93670 _93677 x'''' f s) (@lem3662433 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662438 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term913 _93670 _93677 x'''' y'''' f s) = (term918 _93670 _93677 x'''' y'''' f s).
Proof. exact (TRANS (@lem3662426 _93670 _93677 x'''' y'''' f s) (@lem3662437 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3662440 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term919 _93670 _93677 x'''' y'''' f s) = (term920 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3662439) (@lem3662438 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662441 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term911 _93670 _93677 x'''' y'''' f s) = (term921 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3662440 _93670 _93677 x'''' y'''' f s) (@lem3662425 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662442 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term910 _93670 _93677 x'''' y'''' f s) = (term921 _93670 _93677 x'''' y'''' f s).
Proof. exact (TRANS (@lem3662424 _93670 _93677 x'''' y'''' f s) (@lem3662441 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662443 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term922 _93670 _93677 x'''' y'''' f s) = (term923 _93670 _93677 x'''' y'''' f s).
Proof. exact (@lem19699 (term824 _93670 _93677 x'''' y'''' f s) (term806 _93670 _93677 x'''' y'''' f s) (term798 _93670 _93677 f s)). Qed.
Lemma lem3662444 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term924 _93670 _93677 x'''' y'''' f s) = (term924 _93670 _93677 x'''' y'''' f s).
Proof. exact (eq_refl (term924 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662445 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term925 _93670 _93677 x'''' y'''' f s) = (term926 _93670 _93677 x'''' y'''' f s).
Proof. exact (@lem19699 (term818 _93670 _93677 x'''' f s) (term822 _93670 _93677 x'''' y'''' f s) (term798 _93670 _93677 f s)). Qed.
Lemma lem3662452 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term927 _93670 _93677 x'''' y'''' f s) = (term928 _93670 _93677 x'''' y'''' f s).
Proof. exact (@lem19699 (term818 _93670 _93677 y'''' f s) ((term809 _93670 _93677 x'''' f s) = (term809 _93670 _93677 y'''' f s)) (term798 _93670 _93677 f s)). Qed.
Lemma lem3662455 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term929 _93670 _93677 x'''' f s) = (term929 _93670 _93677 x'''' f s).
Proof. exact (eq_refl (term929 _93670 _93677 x'''' f s)). Qed.
Lemma lem3662456 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term926 _93670 _93677 x'''' y'''' f s) = (term930 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3662455 _93670 _93677 x'''' f s) (@lem3662452 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662457 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term925 _93670 _93677 x'''' y'''' f s) = (term930 _93670 _93677 x'''' y'''' f s).
Proof. exact (TRANS (@lem3662445 _93670 _93677 x'''' y'''' f s) (@lem3662456 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3662459 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term931 _93670 _93677 x'''' y'''' f s) = (term932 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3662458) (@lem3662457 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662460 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term923 _93670 _93677 x'''' y'''' f s) = (term933 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3662459 _93670 _93677 x'''' y'''' f s) (@lem3662444 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662461 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term922 _93670 _93677 x'''' y'''' f s) = (term933 _93670 _93677 x'''' y'''' f s).
Proof. exact (TRANS (@lem3662443 _93670 _93677 x'''' y'''' f s) (@lem3662460 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3662463 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term934 _93670 _93677 x'''' y'''' f s) = (term935 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3662462) (@lem3662461 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662464 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term909 _93670 _93677 x'''' y'''' f s) = (term936 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3662463 _93670 _93677 x'''' y'''' f s) (@lem3662442 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662466 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term832 _93670 _93677 x'''' y'''' f s) = (term936 _93670 _93677 x'''' y'''' f s).
Proof. exact (TRANS (@lem3662423 _93670 _93677 x'''' y'''' f s) (@lem3662464 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662467 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) : (term834 _93670 _93677 x'''' y'''' f) = (term937 _93670 _93677 x'''' y'''' f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3662466 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3662468 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3662469 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) : (term835 _93670 _93677 x'''' y'''' f) = (term938 _93670 _93677 x'''' y'''' f).
Proof. exact (MK_COMB (@lem3662468 _93670) (@lem3662467 _93670 _93677 x'''' y'''' f)). Qed.
Lemma lem3662470 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) : (term836 _93670 _93677 x'''' y'''') = (term939 _93670 _93677 x'''' y'''').
Proof. exact (fun_ext (fun f : _93670 -> _93677 => @lem3662469 _93670 _93677 x'''' y'''' f)). Qed.
Lemma lem3662471 {_93670 _93677 : Type'} : (@all (_93670 -> _93677)) = (@all (_93670 -> _93677)).
Proof. exact (eq_refl (@all (_93670 -> _93677))). Qed.
Lemma lem3662473 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) : (term837 _93670 _93677 x'''' y'''') = (term940 _93670 _93677 x'''' y'''').
Proof. exact (MK_COMB (@lem3662471 _93670 _93677) (@lem3662470 _93670 _93677 x'''' y'''')). Qed.
Lemma lem3662474 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term940 _93670 _93677 x'''' y''''.
Proof. exact (EQ_MP (@lem3662473 _93670 _93677 x'''' y'''') (@lem3660794 _93670 _93677 x'''' y'''' h1)). Qed.
Lemma lem3662514 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term863 _93670 _93677 t f x y) = (term941 _93670 _93677 t f x y).
Proof. exact (@lem19490 (term852 _93670 _93677 f x y) (term861 _93670 x y t) (term847 _93670 _93677 f x y)). Qed.
Lemma lem3662515 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term864 _93670 _93677 t f x) = (term942 _93670 _93677 t f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3662514 _93670 _93677 t f x y)). Qed.
Lemma lem3662516 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3662517 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term865 _93670 _93677 t f x) = (term943 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3662516 _93670) (@lem3662515 _93670 _93677 t f x)). Qed.
Lemma lem3662518 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term866 _93670 _93677 t f) = (term944 _93670 _93677 t f).
Proof. exact (fun_ext (fun x : _93670 => @lem3662517 _93670 _93677 t f x)). Qed.
Lemma lem3662519 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3662521 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term867 _93670 _93677 t f) = (term945 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3662519 _93670) (@lem3662518 _93670 _93677 t f)). Qed.
Lemma lem3662522 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term945 _93670 _93677 t f.
Proof. exact (EQ_MP (@lem3662521 _93670 _93677 t f) (@lem3661508 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3662534 {_93670 : Type'} (t : _93670 -> Prop) (h1 : term794 _93670 t) : term794 _93670 t.
Proof. exact (h1). Qed.
Lemma lem3663032 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') : term843 _93670 _93677 x''''' f y'''''.
Proof. exact (h1). Qed.
Lemma lem3663036 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (h1). Qed.
Lemma lem3663534 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') : term843 _93670 _93677 x''''' f y'''''.
Proof. exact (h1). Qed.
Lemma lem3663538 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : x''''' = y'''''.
Proof. exact (h1). Qed.
Lemma lem3664008 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term863 _93670 _93677 t f x y) = (term941 _93670 _93677 t f x y).
Proof. exact (@lem19490 (term852 _93670 _93677 f x y) (term861 _93670 x y t) (term847 _93670 _93677 f x y)). Qed.
Lemma lem3664009 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term864 _93670 _93677 t f x) = (term942 _93670 _93677 t f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3664008 _93670 _93677 t f x y)). Qed.
Lemma lem3664010 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3664011 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term865 _93670 _93677 t f x) = (term943 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3664010 _93670) (@lem3664009 _93670 _93677 t f x)). Qed.
Lemma lem3664012 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term866 _93670 _93677 t f) = (term944 _93670 _93677 t f).
Proof. exact (fun_ext (fun x : _93670 => @lem3664011 _93670 _93677 t f x)). Qed.
Lemma lem3664013 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3664015 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term867 _93670 _93677 t f) = (term945 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3664013 _93670) (@lem3664012 _93670 _93677 t f)). Qed.
Lemma lem3664016 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term945 _93670 _93677 t f.
Proof. exact (EQ_MP (@lem3664015 _93670 _93677 t f) (@lem3661508 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3664036 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') : term848 _93670 x''''' y'''''.
Proof. exact (h1). Qed.
Lemma lem3664040 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (h1). Qed.
Lemma lem3664538 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') : term848 _93670 x''''' y'''''.
Proof. exact (h1). Qed.
Lemma lem3664542 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : x''''' = y'''''.
Proof. exact (h1). Qed.
Lemma lem3665032 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) : term875 _93670 _93677 P f t.
Proof. exact (h1). Qed.
Lemma lem3665522 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) (h1 : term891 _93670 t s) : term891 _93670 t s.
Proof. exact (h1). Qed.
Lemma lem3666020 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') : term843 _93670 _93677 x''''' f y'''''.
Proof. exact (h1). Qed.
Lemma lem3666024 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (h1). Qed.
Lemma lem3666522 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') : term843 _93670 _93677 x''''' f y'''''.
Proof. exact (h1). Qed.
Lemma lem3666526 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : x''''' = y'''''.
Proof. exact (h1). Qed.
Lemma lem3667000 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term863 _93670 _93677 t f x y) = (term941 _93670 _93677 t f x y).
Proof. exact (@lem19490 (term852 _93670 _93677 f x y) (term861 _93670 x y t) (term847 _93670 _93677 f x y)). Qed.
Lemma lem3667001 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term864 _93670 _93677 t f x) = (term942 _93670 _93677 t f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3667000 _93670 _93677 t f x y)). Qed.
Lemma lem3667002 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3667003 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term865 _93670 _93677 t f x) = (term943 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3667002 _93670) (@lem3667001 _93670 _93677 t f x)). Qed.
Lemma lem3667004 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term866 _93670 _93677 t f) = (term944 _93670 _93677 t f).
Proof. exact (fun_ext (fun x : _93670 => @lem3667003 _93670 _93677 t f x)). Qed.
Lemma lem3667005 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3667007 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term867 _93670 _93677 t f) = (term945 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3667005 _93670) (@lem3667004 _93670 _93677 t f)). Qed.
Lemma lem3667008 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term945 _93670 _93677 t f.
Proof. exact (EQ_MP (@lem3667007 _93670 _93677 t f) (@lem3661536 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3667024 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') : term848 _93670 x''''' y'''''.
Proof. exact (h1). Qed.
Lemma lem3667028 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (h1). Qed.
Lemma lem3667526 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') : term848 _93670 x''''' y'''''.
Proof. exact (h1). Qed.
Lemma lem3667530 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : x''''' = y'''''.
Proof. exact (h1). Qed.
Lemma lem3667909 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term832 _93670 _93677 x'''' y'''' f s) = (term909 _93670 _93677 x'''' y'''' f s).
Proof. exact (@lem19490 (term798 _93670 _93677 f s) (term828 _93670 _93677 x'''' y'''' f s) (term793 _93670 _93677 f s)). Qed.
Lemma lem3667910 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term910 _93670 _93677 x'''' y'''' f s) = (term911 _93670 _93677 x'''' y'''' f s).
Proof. exact (@lem19699 (term824 _93670 _93677 x'''' y'''' f s) (term806 _93670 _93677 x'''' y'''' f s) (term793 _93670 _93677 f s)). Qed.
Lemma lem3667911 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term912 _93670 _93677 x'''' y'''' f s) = (term912 _93670 _93677 x'''' y'''' f s).
Proof. exact (eq_refl (term912 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667912 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term913 _93670 _93677 x'''' y'''' f s) = (term914 _93670 _93677 x'''' y'''' f s).
Proof. exact (@lem19699 (term818 _93670 _93677 x'''' f s) (term822 _93670 _93677 x'''' y'''' f s) (term793 _93670 _93677 f s)). Qed.
Lemma lem3667919 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term915 _93670 _93677 x'''' y'''' f s) = (term916 _93670 _93677 x'''' y'''' f s).
Proof. exact (@lem19699 (term818 _93670 _93677 y'''' f s) ((term809 _93670 _93677 x'''' f s) = (term809 _93670 _93677 y'''' f s)) (term793 _93670 _93677 f s)). Qed.
Lemma lem3667922 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term917 _93670 _93677 x'''' f s) = (term917 _93670 _93677 x'''' f s).
Proof. exact (eq_refl (term917 _93670 _93677 x'''' f s)). Qed.
Lemma lem3667923 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term914 _93670 _93677 x'''' y'''' f s) = (term918 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3667922 _93670 _93677 x'''' f s) (@lem3667919 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667924 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term913 _93670 _93677 x'''' y'''' f s) = (term918 _93670 _93677 x'''' y'''' f s).
Proof. exact (TRANS (@lem3667912 _93670 _93677 x'''' y'''' f s) (@lem3667923 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3667926 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term919 _93670 _93677 x'''' y'''' f s) = (term920 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3667925) (@lem3667924 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667927 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term911 _93670 _93677 x'''' y'''' f s) = (term921 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3667926 _93670 _93677 x'''' y'''' f s) (@lem3667911 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667928 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term910 _93670 _93677 x'''' y'''' f s) = (term921 _93670 _93677 x'''' y'''' f s).
Proof. exact (TRANS (@lem3667910 _93670 _93677 x'''' y'''' f s) (@lem3667927 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667929 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term922 _93670 _93677 x'''' y'''' f s) = (term923 _93670 _93677 x'''' y'''' f s).
Proof. exact (@lem19699 (term824 _93670 _93677 x'''' y'''' f s) (term806 _93670 _93677 x'''' y'''' f s) (term798 _93670 _93677 f s)). Qed.
Lemma lem3667930 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term924 _93670 _93677 x'''' y'''' f s) = (term924 _93670 _93677 x'''' y'''' f s).
Proof. exact (eq_refl (term924 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667931 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term925 _93670 _93677 x'''' y'''' f s) = (term926 _93670 _93677 x'''' y'''' f s).
Proof. exact (@lem19699 (term818 _93670 _93677 x'''' f s) (term822 _93670 _93677 x'''' y'''' f s) (term798 _93670 _93677 f s)). Qed.
Lemma lem3667938 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term927 _93670 _93677 x'''' y'''' f s) = (term928 _93670 _93677 x'''' y'''' f s).
Proof. exact (@lem19699 (term818 _93670 _93677 y'''' f s) ((term809 _93670 _93677 x'''' f s) = (term809 _93670 _93677 y'''' f s)) (term798 _93670 _93677 f s)). Qed.
Lemma lem3667941 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term929 _93670 _93677 x'''' f s) = (term929 _93670 _93677 x'''' f s).
Proof. exact (eq_refl (term929 _93670 _93677 x'''' f s)). Qed.
Lemma lem3667942 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term926 _93670 _93677 x'''' y'''' f s) = (term930 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3667941 _93670 _93677 x'''' f s) (@lem3667938 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667943 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term925 _93670 _93677 x'''' y'''' f s) = (term930 _93670 _93677 x'''' y'''' f s).
Proof. exact (TRANS (@lem3667931 _93670 _93677 x'''' y'''' f s) (@lem3667942 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3667945 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term931 _93670 _93677 x'''' y'''' f s) = (term932 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3667944) (@lem3667943 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667946 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term923 _93670 _93677 x'''' y'''' f s) = (term933 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3667945 _93670 _93677 x'''' y'''' f s) (@lem3667930 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667947 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term922 _93670 _93677 x'''' y'''' f s) = (term933 _93670 _93677 x'''' y'''' f s).
Proof. exact (TRANS (@lem3667929 _93670 _93677 x'''' y'''' f s) (@lem3667946 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3667949 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term934 _93670 _93677 x'''' y'''' f s) = (term935 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3667948) (@lem3667947 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667950 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term909 _93670 _93677 x'''' y'''' f s) = (term936 _93670 _93677 x'''' y'''' f s).
Proof. exact (MK_COMB (@lem3667949 _93670 _93677 x'''' y'''' f s) (@lem3667928 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667952 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : (term832 _93670 _93677 x'''' y'''' f s) = (term936 _93670 _93677 x'''' y'''' f s).
Proof. exact (TRANS (@lem3667909 _93670 _93677 x'''' y'''' f s) (@lem3667950 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667953 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) : (term834 _93670 _93677 x'''' y'''' f) = (term937 _93670 _93677 x'''' y'''' f).
Proof. exact (fun_ext (fun s : _93670 -> Prop => @lem3667952 _93670 _93677 x'''' y'''' f s)). Qed.
Lemma lem3667954 {_93670 : Type'} : (@all (_93670 -> Prop)) = (@all (_93670 -> Prop)).
Proof. exact (eq_refl (@all (_93670 -> Prop))). Qed.
Lemma lem3667955 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) : (term835 _93670 _93677 x'''' y'''' f) = (term938 _93670 _93677 x'''' y'''' f).
Proof. exact (MK_COMB (@lem3667954 _93670) (@lem3667953 _93670 _93677 x'''' y'''' f)). Qed.
Lemma lem3667956 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) : (term836 _93670 _93677 x'''' y'''') = (term939 _93670 _93677 x'''' y'''').
Proof. exact (fun_ext (fun f : _93670 -> _93677 => @lem3667955 _93670 _93677 x'''' y'''' f)). Qed.
Lemma lem3667957 {_93670 _93677 : Type'} : (@all (_93670 -> _93677)) = (@all (_93670 -> _93677)).
Proof. exact (eq_refl (@all (_93670 -> _93677))). Qed.
Lemma lem3667959 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) : (term837 _93670 _93677 x'''' y'''') = (term940 _93670 _93677 x'''' y'''').
Proof. exact (MK_COMB (@lem3667957 _93670 _93677) (@lem3667956 _93670 _93677 x'''' y'''')). Qed.
Lemma lem3667960 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term940 _93670 _93677 x'''' y''''.
Proof. exact (EQ_MP (@lem3667959 _93670 _93677 x'''' y'''') (@lem3660794 _93670 _93677 x'''' y'''' h1)). Qed.
Lemma lem3668004 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) (y : _93670) : (term863 _93670 _93677 t f x y) = (term941 _93670 _93677 t f x y).
Proof. exact (@lem19490 (term852 _93670 _93677 f x y) (term861 _93670 x y t) (term847 _93670 _93677 f x y)). Qed.
Lemma lem3668005 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term864 _93670 _93677 t f x) = (term942 _93670 _93677 t f x).
Proof. exact (fun_ext (fun y : _93670 => @lem3668004 _93670 _93677 t f x y)). Qed.
Lemma lem3668006 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3668007 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x : _93670) : (term865 _93670 _93677 t f x) = (term943 _93670 _93677 t f x).
Proof. exact (MK_COMB (@lem3668006 _93670) (@lem3668005 _93670 _93677 t f x)). Qed.
Lemma lem3668008 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term866 _93670 _93677 t f) = (term944 _93670 _93677 t f).
Proof. exact (fun_ext (fun x : _93670 => @lem3668007 _93670 _93677 t f x)). Qed.
Lemma lem3668009 {_93670 : Type'} : (@all _93670) = (@all _93670).
Proof. exact (eq_refl (@all _93670)). Qed.
Lemma lem3668011 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : (term867 _93670 _93677 t f) = (term945 _93670 _93677 t f).
Proof. exact (MK_COMB (@lem3668009 _93670) (@lem3668008 _93670 _93677 t f)). Qed.
Lemma lem3668012 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term945 _93670 _93677 t f.
Proof. exact (EQ_MP (@lem3668011 _93670 _93677 t f) (@lem3661536 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3668020 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) : term789 _93670 _93677 f t.
Proof. exact (h1). Qed.
Lemma lem3668510 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) : term875 _93670 _93677 P f t.
Proof. exact (h1). Qed.
Lemma lem3668571 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term946 _93670 _93677 x'''' y'''' _40148.
Proof. exact (@lem3662474 _93670 _93677 x'''' y'''' h1 _40148). Qed.
Lemma lem3668572 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) : (term946 _93670 _93677 x'''' y'''' _40148) = (term938 _93670 _93677 x'''' y'''' _40148).
Proof. exact (eq_refl (term946 _93670 _93677 x'''' y'''' _40148)). Qed.
Lemma lem3668573 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term938 _93670 _93677 x'''' y'''' _40148.
Proof. exact (EQ_MP (@lem3668572 _93670 _93677 x'''' y'''' _40148) (@lem3668571 _93670 _93677 _40148 x'''' y'''' h1)). Qed.
Lemma lem3668574 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term947 _93670 _93677 x'''' y'''' _40148 _40149.
Proof. exact (@lem3668573 _93670 _93677 _40148 x'''' y'''' h1 _40149). Qed.
Lemma lem3668575 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term947 _93670 _93677 x'''' y'''' _40148 _40149) = (term936 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (eq_refl (term947 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3668576 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term936 _93670 _93677 x'''' y'''' _40148 _40149.
Proof. exact (EQ_MP (@lem3668575 _93670 _93677 x'''' y'''' _40148 _40149) (@lem3668574 _93670 _93677 _40148 _40149 x'''' y'''' h1)). Qed.
Lemma lem3668577 {_93670 _93677 : Type'} (_40150 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term948 _93670 _93677 t f _40150.
Proof. exact (@lem3662522 _93670 _93677 s x''''' y''''' P f t h1 _40150). Qed.
Lemma lem3668578 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40150 : _93670) : (term948 _93670 _93677 t f _40150) = (term943 _93670 _93677 t f _40150).
Proof. exact (eq_refl (term948 _93670 _93677 t f _40150)). Qed.
Lemma lem3668579 {_93670 _93677 : Type'} (_40150 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term943 _93670 _93677 t f _40150.
Proof. exact (EQ_MP (@lem3668578 _93670 _93677 t f _40150) (@lem3668577 _93670 _93677 _40150 s x''''' y''''' P f t h1)). Qed.
Lemma lem3668580 {_93670 _93677 : Type'} (_40150 : _93670) (_40151 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term949 _93670 _93677 t f _40150 _40151.
Proof. exact (@lem3668579 _93670 _93677 _40150 s x''''' y''''' P f t h1 _40151). Qed.
Lemma lem3668581 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40150 : _93670) (_40151 : _93670) : (term949 _93670 _93677 t f _40150 _40151) = (term941 _93670 _93677 t f _40150 _40151).
Proof. exact (eq_refl (term949 _93670 _93677 t f _40150 _40151)). Qed.
Lemma lem3668582 {_93670 _93677 : Type'} (_40150 : _93670) (_40151 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term941 _93670 _93677 t f _40150 _40151.
Proof. exact (EQ_MP (@lem3668581 _93670 _93677 t f _40150 _40151) (@lem3668580 _93670 _93677 _40150 _40151 s x''''' y''''' P f t h1)). Qed.
Lemma lem3668685 {_93670 _93677 : Type'} (_40186 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term948 _93670 _93677 t f _40186.
Proof. exact (@lem3664016 _93670 _93677 s x''''' y''''' P f t h1 _40186). Qed.
Lemma lem3668686 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40186 : _93670) : (term948 _93670 _93677 t f _40186) = (term943 _93670 _93677 t f _40186).
Proof. exact (eq_refl (term948 _93670 _93677 t f _40186)). Qed.
Lemma lem3668687 {_93670 _93677 : Type'} (_40186 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term943 _93670 _93677 t f _40186.
Proof. exact (EQ_MP (@lem3668686 _93670 _93677 t f _40186) (@lem3668685 _93670 _93677 _40186 s x''''' y''''' P f t h1)). Qed.
Lemma lem3668688 {_93670 _93677 : Type'} (_40186 : _93670) (_40187 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term949 _93670 _93677 t f _40186 _40187.
Proof. exact (@lem3668687 _93670 _93677 _40186 s x''''' y''''' P f t h1 _40187). Qed.
Lemma lem3668689 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) : (term949 _93670 _93677 t f _40186 _40187) = (term941 _93670 _93677 t f _40186 _40187).
Proof. exact (eq_refl (term949 _93670 _93677 t f _40186 _40187)). Qed.
Lemma lem3668690 {_93670 _93677 : Type'} (_40186 : _93670) (_40187 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term941 _93670 _93677 t f _40186 _40187.
Proof. exact (EQ_MP (@lem3668689 _93670 _93677 t f _40186 _40187) (@lem3668688 _93670 _93677 _40186 _40187 s x''''' y''''' P f t h1)). Qed.
Lemma lem3668901 {_93670 _93677 : Type'} (_40258 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term948 _93670 _93677 t f _40258.
Proof. exact (@lem3667008 _93670 _93677 x''''' y''''' s P f t h1 _40258). Qed.
Lemma lem3668902 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40258 : _93670) : (term948 _93670 _93677 t f _40258) = (term943 _93670 _93677 t f _40258).
Proof. exact (eq_refl (term948 _93670 _93677 t f _40258)). Qed.
Lemma lem3668903 {_93670 _93677 : Type'} (_40258 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term943 _93670 _93677 t f _40258.
Proof. exact (EQ_MP (@lem3668902 _93670 _93677 t f _40258) (@lem3668901 _93670 _93677 _40258 x''''' y''''' s P f t h1)). Qed.
Lemma lem3668904 {_93670 _93677 : Type'} (_40258 : _93670) (_40259 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term949 _93670 _93677 t f _40258 _40259.
Proof. exact (@lem3668903 _93670 _93677 _40258 x''''' y''''' s P f t h1 _40259). Qed.
Lemma lem3668905 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) : (term949 _93670 _93677 t f _40258 _40259) = (term941 _93670 _93677 t f _40258 _40259).
Proof. exact (eq_refl (term949 _93670 _93677 t f _40258 _40259)). Qed.
Lemma lem3668906 {_93670 _93677 : Type'} (_40258 : _93670) (_40259 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term941 _93670 _93677 t f _40258 _40259.
Proof. exact (EQ_MP (@lem3668905 _93670 _93677 t f _40258 _40259) (@lem3668904 _93670 _93677 _40258 _40259 x''''' y''''' s P f t h1)). Qed.
Lemma lem3668967 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term946 _93670 _93677 x'''' y'''' _40280.
Proof. exact (@lem3667960 _93670 _93677 x'''' y'''' h1 _40280). Qed.
Lemma lem3668968 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) : (term946 _93670 _93677 x'''' y'''' _40280) = (term938 _93670 _93677 x'''' y'''' _40280).
Proof. exact (eq_refl (term946 _93670 _93677 x'''' y'''' _40280)). Qed.
Lemma lem3668969 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term938 _93670 _93677 x'''' y'''' _40280.
Proof. exact (EQ_MP (@lem3668968 _93670 _93677 x'''' y'''' _40280) (@lem3668967 _93670 _93677 _40280 x'''' y'''' h1)). Qed.
Lemma lem3668970 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term947 _93670 _93677 x'''' y'''' _40280 _40281.
Proof. exact (@lem3668969 _93670 _93677 _40280 x'''' y'''' h1 _40281). Qed.
Lemma lem3668971 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term947 _93670 _93677 x'''' y'''' _40280 _40281) = (term936 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (eq_refl (term947 _93670 _93677 x'''' y'''' _40280 _40281)). Qed.
Lemma lem3668972 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term936 _93670 _93677 x'''' y'''' _40280 _40281.
Proof. exact (EQ_MP (@lem3668971 _93670 _93677 x'''' y'''' _40280 _40281) (@lem3668970 _93670 _93677 _40280 _40281 x'''' y'''' h1)). Qed.
Lemma lem3668973 {_93670 _93677 : Type'} (_40282 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term948 _93670 _93677 t f _40282.
Proof. exact (@lem3668012 _93670 _93677 x''''' y''''' s P f t h1 _40282). Qed.
Lemma lem3668974 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40282 : _93670) : (term948 _93670 _93677 t f _40282) = (term943 _93670 _93677 t f _40282).
Proof. exact (eq_refl (term948 _93670 _93677 t f _40282)). Qed.
Lemma lem3668975 {_93670 _93677 : Type'} (_40282 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term943 _93670 _93677 t f _40282.
Proof. exact (EQ_MP (@lem3668974 _93670 _93677 t f _40282) (@lem3668973 _93670 _93677 _40282 x''''' y''''' s P f t h1)). Qed.
Lemma lem3668976 {_93670 _93677 : Type'} (_40282 : _93670) (_40283 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term949 _93670 _93677 t f _40282 _40283.
Proof. exact (@lem3668975 _93670 _93677 _40282 x''''' y''''' s P f t h1 _40283). Qed.
Lemma lem3668977 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40282 : _93670) (_40283 : _93670) : (term949 _93670 _93677 t f _40282 _40283) = (term941 _93670 _93677 t f _40282 _40283).
Proof. exact (eq_refl (term949 _93670 _93677 t f _40282 _40283)). Qed.
Lemma lem3668978 {_93670 _93677 : Type'} (_40282 : _93670) (_40283 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term941 _93670 _93677 t f _40282 _40283.
Proof. exact (EQ_MP (@lem3668977 _93670 _93677 t f _40282 _40283) (@lem3668976 _93670 _93677 _40282 _40283 x''''' y''''' s P f t h1)). Qed.
Lemma lem3669087 {_93670 _93677 : Type'} (_40150 : _93670) (_40151 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term950 _93670 _93677 t f _40150 _40151.
Proof. exact (proj2 (@lem3668582 _93670 _93677 _40150 _40151 s x''''' y''''' P f t h1)). Qed.
Lemma lem3669089 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term921 _93670 _93677 x'''' y'''' _40148 _40149.
Proof. exact (proj2 (@lem3668576 _93670 _93677 _40148 _40149 x'''' y'''' h1)). Qed.
Lemma lem3669092 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term918 _93670 _93677 x'''' y'''' _40148 _40149.
Proof. exact (proj1 (@lem3669089 _93670 _93677 _40148 _40149 x'''' y'''' h1)). Qed.
Lemma lem3669093 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term916 _93670 _93677 x'''' y'''' _40148 _40149.
Proof. exact (proj2 (@lem3669092 _93670 _93677 _40148 _40149 x'''' y'''' h1)). Qed.
Lemma lem3669303 {_93670 _93677 : Type'} (_40186 : _93670) (_40187 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term950 _93670 _93677 t f _40186 _40187.
Proof. exact (proj2 (@lem3668690 _93670 _93677 _40186 _40187 s x''''' y''''' P f t h1)). Qed.
Lemma lem3669735 {_93670 _93677 : Type'} (_40258 : _93670) (_40259 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term950 _93670 _93677 t f _40258 _40259.
Proof. exact (proj2 (@lem3668906 _93670 _93677 _40258 _40259 x''''' y''''' s P f t h1)). Qed.
Lemma lem3669879 {_93670 _93677 : Type'} (_40282 : _93670) (_40283 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term950 _93670 _93677 t f _40282 _40283.
Proof. exact (proj2 (@lem3668978 _93670 _93677 _40282 _40283 x''''' y''''' s P f t h1)). Qed.
Lemma lem3669882 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term933 _93670 _93677 x'''' y'''' _40280 _40281.
Proof. exact (proj1 (@lem3668972 _93670 _93677 _40280 _40281 x'''' y'''' h1)). Qed.
Lemma lem3669890 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term930 _93670 _93677 x'''' y'''' _40280 _40281.
Proof. exact (proj1 (@lem3669882 _93670 _93677 _40280 _40281 x'''' y'''' h1)). Qed.
Lemma lem3669891 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term928 _93670 _93677 x'''' y'''' _40280 _40281.
Proof. exact (proj2 (@lem3669890 _93670 _93677 _40280 _40281 x'''' y'''' h1)). Qed.
Lemma lem3670030 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) (h1 : term891 _93670 t s) : term891 _93670 t s.
Proof. exact (h1). Qed.
Lemma lem3670470 {_93670 : Type'} (t : _93670 -> Prop) (h1 : term794 _93670 t) : term794 _93670 t.
Proof. exact (h1). Qed.
Lemma lem3670501 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40150 : _93670) (_40151 : _93670) : (term950 _93670 _93677 t f _40150 _40151) = (term951 _93670 _93677 t f _40150 _40151).
Proof. exact (@lem3655860 (term858 _93670 _40150 t) (term858 _93670 _40151 t) (term847 _93670 _93677 f _40150 _40151)). Qed.
Lemma lem3670502 {_93670 _93677 : Type'} (_40150 : _93670) (_40151 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term951 _93670 _93677 t f _40150 _40151.
Proof. exact (EQ_MP (@lem3670501 _93670 _93677 t f _40150 _40151) (@lem3669087 _93670 _93677 _40150 _40151 s x''''' y''''' P f t h1)). Qed.
Lemma lem3670512 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term912 _93670 _93677 x'''' y'''' _40148 _40149.
Proof. exact (proj2 (@lem3669089 _93670 _93677 _40148 _40149 x'''' y'''' h1)). Qed.
Lemma lem3670522 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term952 _93670 _93677 x'''' _40148 _40149.
Proof. exact (proj1 (@lem3669092 _93670 _93677 _40148 _40149 x'''' y'''' h1)). Qed.
Lemma lem3670532 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term952 _93670 _93677 y'''' _40148 _40149.
Proof. exact (proj1 (@lem3669093 _93670 _93677 _40148 _40149 x'''' y'''' h1)). Qed.
Lemma lem3670542 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term953 _93670 _93677 x'''' y'''' _40148 _40149.
Proof. exact (proj2 (@lem3669093 _93670 _93677 _40148 _40149 x'''' y'''' h1)). Qed.
Lemma lem3670914 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') : term843 _93670 _93677 x''''' f y'''''.
Proof. exact (h1). Qed.
Lemma lem3670916 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (h1). Qed.
Lemma lem3671360 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') : term843 _93670 _93677 x''''' f y'''''.
Proof. exact (h1). Qed.
Lemma lem3671362 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : x''''' = y'''''.
Proof. exact (h1). Qed.
Lemma lem3671806 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') : term848 _93670 x''''' y'''''.
Proof. exact (h1). Qed.
Lemma lem3671808 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (h1). Qed.
Lemma lem3671839 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) : (term950 _93670 _93677 t f _40186 _40187) = (term951 _93670 _93677 t f _40186 _40187).
Proof. exact (@lem3655860 (term858 _93670 _40186 t) (term858 _93670 _40187 t) (term847 _93670 _93677 f _40186 _40187)). Qed.
Lemma lem3671840 {_93670 _93677 : Type'} (_40186 : _93670) (_40187 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term951 _93670 _93677 t f _40186 _40187.
Proof. exact (EQ_MP (@lem3671839 _93670 _93677 t f _40186 _40187) (@lem3669303 _93670 _93677 _40186 _40187 s x''''' y''''' P f t h1)). Qed.
Lemma lem3672252 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') : term848 _93670 x''''' y'''''.
Proof. exact (h1). Qed.
Lemma lem3672254 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : x''''' = y'''''.
Proof. exact (h1). Qed.
Lemma lem3672694 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) : term875 _93670 _93677 P f t.
Proof. exact (h1). Qed.
Lemma lem3673134 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) (h1 : term891 _93670 t s) : term891 _93670 t s.
Proof. exact (h1). Qed.
Lemma lem3673578 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') : term843 _93670 _93677 x''''' f y'''''.
Proof. exact (h1). Qed.
Lemma lem3673580 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (h1). Qed.
Lemma lem3674024 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') : term843 _93670 _93677 x''''' f y'''''.
Proof. exact (h1). Qed.
Lemma lem3674026 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : x''''' = y'''''.
Proof. exact (h1). Qed.
Lemma lem3674470 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') : term848 _93670 x''''' y'''''.
Proof. exact (h1). Qed.
Lemma lem3674472 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (h1). Qed.
Lemma lem3674503 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) : (term950 _93670 _93677 t f _40258 _40259) = (term951 _93670 _93677 t f _40258 _40259).
Proof. exact (@lem3655860 (term858 _93670 _40258 t) (term858 _93670 _40259 t) (term847 _93670 _93677 f _40258 _40259)). Qed.
Lemma lem3674504 {_93670 _93677 : Type'} (_40258 : _93670) (_40259 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term951 _93670 _93677 t f _40258 _40259.
Proof. exact (EQ_MP (@lem3674503 _93670 _93677 t f _40258 _40259) (@lem3669735 _93670 _93677 _40258 _40259 x''''' y''''' s P f t h1)). Qed.
Lemma lem3674916 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') : term848 _93670 x''''' y'''''.
Proof. exact (h1). Qed.
Lemma lem3674918 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : x''''' = y'''''.
Proof. exact (h1). Qed.
Lemma lem3675358 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) : term789 _93670 _93677 f t.
Proof. exact (h1). Qed.
Lemma lem3675389 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40282 : _93670) (_40283 : _93670) : (term950 _93670 _93677 t f _40282 _40283) = (term951 _93670 _93677 t f _40282 _40283).
Proof. exact (@lem3655860 (term858 _93670 _40282 t) (term858 _93670 _40283 t) (term847 _93670 _93677 f _40282 _40283)). Qed.
Lemma lem3675390 {_93670 _93677 : Type'} (_40282 : _93670) (_40283 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term951 _93670 _93677 t f _40282 _40283.
Proof. exact (EQ_MP (@lem3675389 _93670 _93677 t f _40282 _40283) (@lem3669879 _93670 _93677 _40282 _40283 x''''' y''''' s P f t h1)). Qed.
Lemma lem3675440 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term924 _93670 _93677 x'''' y'''' _40280 _40281.
Proof. exact (proj2 (@lem3669882 _93670 _93677 _40280 _40281 x'''' y'''' h1)). Qed.
Lemma lem3675450 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term954 _93670 _93677 x'''' _40280 _40281.
Proof. exact (proj1 (@lem3669890 _93670 _93677 _40280 _40281 x'''' y'''' h1)). Qed.
Lemma lem3675460 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term954 _93670 _93677 y'''' _40280 _40281.
Proof. exact (proj1 (@lem3669891 _93670 _93677 _40280 _40281 x'''' y'''' h1)). Qed.
Lemma lem3675470 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term955 _93670 _93677 x'''' y'''' _40280 _40281.
Proof. exact (proj2 (@lem3669891 _93670 _93677 _40280 _40281 x'''' y'''' h1)). Qed.
Lemma lem3675798 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) : term875 _93670 _93677 P f t.
Proof. exact (h1). Qed.
Lemma lem3676314 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (term956 _93670 _93677 f y''''') = (term956 _93670 _93677 f y''''').
Proof. exact (eq_refl (term956 _93670 _93677 f y''''')). Qed.
Lemma lem3676315 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : (term957 _93670 _93677 f y''''' x''''') = (term958 _93670 _93677 f y''''').
Proof. exact (MK_COMB (@lem3676314 _93670 _93677 f y''''') (@lem3671362 _93670 x''''' y''''' h1)). Qed.
Lemma lem3676316 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (term958 _93670 _93677 f y''''') = (term959 _93670 _93677 f y''''').
Proof. exact (eq_refl (term958 _93670 _93677 f y''''')). Qed.
Lemma lem3676317 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) (x''''' : _93670) : (term960 _93670 _93677 f y''''' x''''') = (term960 _93670 _93677 f y''''' x''''').
Proof. exact (eq_refl (term960 _93670 _93677 f y''''' x''''')). Qed.
Lemma lem3676318 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : ((term957 _93670 _93677 f y''''' x''''') = (term958 _93670 _93677 f y''''')) = ((term957 _93670 _93677 f y''''' x''''') = (term959 _93670 _93677 f y''''')).
Proof. exact (MK_COMB (@lem3676317 _93670 _93677 f y''''' x''''') (@lem3676316 _93670 _93677 f y''''')). Qed.
Lemma lem3676319 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term957 _93670 _93677 f y''''' x''''') = (term843 _93670 _93677 x''''' f y''''').
Proof. exact (eq_refl (term957 _93670 _93677 f y''''' x''''')). Qed.
Lemma lem3676320 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3676321 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term960 _93670 _93677 f y''''' x''''') = (term961 _93670 _93677 x''''' f y''''').
Proof. exact (MK_COMB (@lem3676320) (@lem3676319 _93670 _93677 x''''' f y''''')). Qed.
Lemma lem3676322 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (term959 _93670 _93677 f y''''') = (term959 _93670 _93677 f y''''').
Proof. exact (eq_refl (term959 _93670 _93677 f y''''')). Qed.
Lemma lem3676323 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : ((term957 _93670 _93677 f y''''' x''''') = (term959 _93670 _93677 f y''''')) = ((term843 _93670 _93677 x''''' f y''''') = (term959 _93670 _93677 f y''''')).
Proof. exact (MK_COMB (@lem3676321 _93670 _93677 x''''' f y''''') (@lem3676322 _93670 _93677 f y''''')). Qed.
Lemma lem3676324 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : ((term957 _93670 _93677 f y''''' x''''') = (term958 _93670 _93677 f y''''')) = ((term843 _93670 _93677 x''''' f y''''') = (term959 _93670 _93677 f y''''')).
Proof. exact (TRANS (@lem3676318 _93670 _93677 x''''' f y''''') (@lem3676323 _93670 _93677 x''''' f y''''')). Qed.
Lemma lem3676325 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : (term843 _93670 _93677 x''''' f y''''') = (term959 _93670 _93677 f y''''').
Proof. exact (EQ_MP (@lem3676324 _93670 _93677 x''''' f y''''') (@lem3676315 _93670 _93677 f x''''' y''''' h1)). Qed.
Lemma lem3676326 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : term959 _93670 _93677 f y'''''.
Proof. exact (EQ_MP (@lem3676325 _93670 _93677 f x''''' y''''' h2) (@lem3671360 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3676998 {_93670 : Type'} (y''''' : _93670) : (term962 _93670 y''''') = (term962 _93670 y''''').
Proof. exact (eq_refl (term962 _93670 y''''')). Qed.
Lemma lem3676999 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : (term963 _93670 y''''' x''''') = (term964 _93670 y''''').
Proof. exact (MK_COMB (@lem3676998 _93670 y''''') (@lem3672254 _93670 x''''' y''''' h1)). Qed.
Lemma lem3677000 {_93670 : Type'} (y''''' : _93670) : (term964 _93670 y''''') = (term965 _93670 y''''').
Proof. exact (eq_refl (term964 _93670 y''''')). Qed.
Lemma lem3677001 {_93670 : Type'} (y''''' : _93670) (x''''' : _93670) : (term966 _93670 y''''' x''''') = (term966 _93670 y''''' x''''').
Proof. exact (eq_refl (term966 _93670 y''''' x''''')). Qed.
Lemma lem3677002 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : ((term963 _93670 y''''' x''''') = (term964 _93670 y''''')) = ((term963 _93670 y''''' x''''') = (term965 _93670 y''''')).
Proof. exact (MK_COMB (@lem3677001 _93670 y''''' x''''') (@lem3677000 _93670 y''''')). Qed.
Lemma lem3677003 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : (term963 _93670 y''''' x''''') = (term848 _93670 x''''' y''''').
Proof. exact (eq_refl (term963 _93670 y''''' x''''')). Qed.
Lemma lem3677004 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3677005 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : (term966 _93670 y''''' x''''') = (term967 _93670 x''''' y''''').
Proof. exact (MK_COMB (@lem3677004) (@lem3677003 _93670 x''''' y''''')). Qed.
Lemma lem3677006 {_93670 : Type'} (y''''' : _93670) : (term965 _93670 y''''') = (term965 _93670 y''''').
Proof. exact (eq_refl (term965 _93670 y''''')). Qed.
Lemma lem3677007 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : ((term963 _93670 y''''' x''''') = (term965 _93670 y''''')) = ((term848 _93670 x''''' y''''') = (term965 _93670 y''''')).
Proof. exact (MK_COMB (@lem3677005 _93670 x''''' y''''') (@lem3677006 _93670 y''''')). Qed.
Lemma lem3677008 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : ((term963 _93670 y''''' x''''') = (term964 _93670 y''''')) = ((term848 _93670 x''''' y''''') = (term965 _93670 y''''')).
Proof. exact (TRANS (@lem3677002 _93670 x''''' y''''') (@lem3677007 _93670 x''''' y''''')). Qed.
Lemma lem3677009 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : (term848 _93670 x''''' y''''') = (term965 _93670 y''''').
Proof. exact (EQ_MP (@lem3677008 _93670 x''''' y''''') (@lem3676999 _93670 x''''' y''''' h1)). Qed.
Lemma lem3677010 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : term965 _93670 y'''''.
Proof. exact (EQ_MP (@lem3677009 _93670 x''''' y''''' h2) (@lem3672252 _93670 x''''' y''''' h1)). Qed.
Lemma lem3677682 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (term956 _93670 _93677 f y''''') = (term956 _93670 _93677 f y''''').
Proof. exact (eq_refl (term956 _93670 _93677 f y''''')). Qed.
Lemma lem3677683 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : (term957 _93670 _93677 f y''''' x''''') = (term958 _93670 _93677 f y''''').
Proof. exact (MK_COMB (@lem3677682 _93670 _93677 f y''''') (@lem3674026 _93670 x''''' y''''' h1)). Qed.
Lemma lem3677684 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (term958 _93670 _93677 f y''''') = (term959 _93670 _93677 f y''''').
Proof. exact (eq_refl (term958 _93670 _93677 f y''''')). Qed.
Lemma lem3677685 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) (x''''' : _93670) : (term960 _93670 _93677 f y''''' x''''') = (term960 _93670 _93677 f y''''' x''''').
Proof. exact (eq_refl (term960 _93670 _93677 f y''''' x''''')). Qed.
Lemma lem3677686 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : ((term957 _93670 _93677 f y''''' x''''') = (term958 _93670 _93677 f y''''')) = ((term957 _93670 _93677 f y''''' x''''') = (term959 _93670 _93677 f y''''')).
Proof. exact (MK_COMB (@lem3677685 _93670 _93677 f y''''' x''''') (@lem3677684 _93670 _93677 f y''''')). Qed.
Lemma lem3677687 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term957 _93670 _93677 f y''''' x''''') = (term843 _93670 _93677 x''''' f y''''').
Proof. exact (eq_refl (term957 _93670 _93677 f y''''' x''''')). Qed.
Lemma lem3677688 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3677689 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term960 _93670 _93677 f y''''' x''''') = (term961 _93670 _93677 x''''' f y''''').
Proof. exact (MK_COMB (@lem3677688) (@lem3677687 _93670 _93677 x''''' f y''''')). Qed.
Lemma lem3677690 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (term959 _93670 _93677 f y''''') = (term959 _93670 _93677 f y''''').
Proof. exact (eq_refl (term959 _93670 _93677 f y''''')). Qed.
Lemma lem3677691 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : ((term957 _93670 _93677 f y''''' x''''') = (term959 _93670 _93677 f y''''')) = ((term843 _93670 _93677 x''''' f y''''') = (term959 _93670 _93677 f y''''')).
Proof. exact (MK_COMB (@lem3677689 _93670 _93677 x''''' f y''''') (@lem3677690 _93670 _93677 f y''''')). Qed.
Lemma lem3677692 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : ((term957 _93670 _93677 f y''''' x''''') = (term958 _93670 _93677 f y''''')) = ((term843 _93670 _93677 x''''' f y''''') = (term959 _93670 _93677 f y''''')).
Proof. exact (TRANS (@lem3677686 _93670 _93677 x''''' f y''''') (@lem3677691 _93670 _93677 x''''' f y''''')). Qed.
Lemma lem3677693 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : (term843 _93670 _93677 x''''' f y''''') = (term959 _93670 _93677 f y''''').
Proof. exact (EQ_MP (@lem3677692 _93670 _93677 x''''' f y''''') (@lem3677683 _93670 _93677 f x''''' y''''' h1)). Qed.
Lemma lem3677694 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : term959 _93670 _93677 f y'''''.
Proof. exact (EQ_MP (@lem3677693 _93670 _93677 f x''''' y''''' h2) (@lem3674024 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3678366 {_93670 : Type'} (y''''' : _93670) : (term962 _93670 y''''') = (term962 _93670 y''''').
Proof. exact (eq_refl (term962 _93670 y''''')). Qed.
Lemma lem3678367 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : (term963 _93670 y''''' x''''') = (term964 _93670 y''''').
Proof. exact (MK_COMB (@lem3678366 _93670 y''''') (@lem3674918 _93670 x''''' y''''' h1)). Qed.
Lemma lem3678368 {_93670 : Type'} (y''''' : _93670) : (term964 _93670 y''''') = (term965 _93670 y''''').
Proof. exact (eq_refl (term964 _93670 y''''')). Qed.
Lemma lem3678369 {_93670 : Type'} (y''''' : _93670) (x''''' : _93670) : (term966 _93670 y''''' x''''') = (term966 _93670 y''''' x''''').
Proof. exact (eq_refl (term966 _93670 y''''' x''''')). Qed.
Lemma lem3678370 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : ((term963 _93670 y''''' x''''') = (term964 _93670 y''''')) = ((term963 _93670 y''''' x''''') = (term965 _93670 y''''')).
Proof. exact (MK_COMB (@lem3678369 _93670 y''''' x''''') (@lem3678368 _93670 y''''')). Qed.
Lemma lem3678371 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : (term963 _93670 y''''' x''''') = (term848 _93670 x''''' y''''').
Proof. exact (eq_refl (term963 _93670 y''''' x''''')). Qed.
Lemma lem3678372 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3678373 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : (term966 _93670 y''''' x''''') = (term967 _93670 x''''' y''''').
Proof. exact (MK_COMB (@lem3678372) (@lem3678371 _93670 x''''' y''''')). Qed.
Lemma lem3678374 {_93670 : Type'} (y''''' : _93670) : (term965 _93670 y''''') = (term965 _93670 y''''').
Proof. exact (eq_refl (term965 _93670 y''''')). Qed.
Lemma lem3678375 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : ((term963 _93670 y''''' x''''') = (term965 _93670 y''''')) = ((term848 _93670 x''''' y''''') = (term965 _93670 y''''')).
Proof. exact (MK_COMB (@lem3678373 _93670 x''''' y''''') (@lem3678374 _93670 y''''')). Qed.
Lemma lem3678376 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : ((term963 _93670 y''''' x''''') = (term964 _93670 y''''')) = ((term848 _93670 x''''' y''''') = (term965 _93670 y''''')).
Proof. exact (TRANS (@lem3678370 _93670 x''''' y''''') (@lem3678375 _93670 x''''' y''''')). Qed.
Lemma lem3678377 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : x''''' = y''''') : (term848 _93670 x''''' y''''') = (term965 _93670 y''''').
Proof. exact (EQ_MP (@lem3678376 _93670 x''''' y''''') (@lem3678367 _93670 x''''' y''''' h1)). Qed.
Lemma lem3678378 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : term965 _93670 y'''''.
Proof. exact (EQ_MP (@lem3678377 _93670 x''''' y''''' h2) (@lem3674916 _93670 x''''' y''''' h1)). Qed.
Lemma lem3679527 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term872 _93670 t s.
Proof. exact (proj1 (@lem3661504 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3679528 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term968 _93670 t s.
Proof. exact (fun h0 : term891 _93670 t s => @lem3679527 _93670 _93677 s x''''' y''''' P f t h1). Qed.
Lemma lem3679530 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3679531 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term968 _93670 t s) = (term872 _93670 t s).
Proof. exact (@lem3679530 (term872 _93670 t s)). Qed.
Lemma lem3679532 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term872 _93670 t s.
Proof. exact (EQ_MP (@lem3679531 _93670 t s) (@lem3679528 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3679535 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3679537 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term891 _93670 t s) = (term970 _93670 t s).
Proof. exact (@lem3679535 (term872 _93670 t s)). Qed.
Lemma lem3679540 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) (h1 : term891 _93670 t s) : term970 _93670 t s.
Proof. exact (EQ_MP (@lem3679537 _93670 t s) (@lem3670030 _93670 t s h1)). Qed.
Lemma lem3679543 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (@lem3679540 _93670 t s h1 (@lem3679532 _93670 _93677 s x''''' y''''' P f t h2)). Qed.
Lemma lem3679544 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : term971.
Proof. exact (fun h0 : ~ False => @lem3679543 _93670 _93677 s x''''' y''''' P f t h1 h2). Qed.
Lemma lem3679546 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3679547 : term971 = False.
Proof. exact (@lem3679546 False). Qed.
Lemma lem3679548 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (EQ_MP (@lem3679547) (@lem3679544 _93670 _93677 s x''''' y''''' P f t h1 h2)). Qed.
Lemma lem3680109 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term787 _93670 _93677 f t.
Proof. exact (proj1 (@lem3661507 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3680110 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term972 _93670 _93677 f t.
Proof. exact (fun h0 : term789 _93670 _93677 f t => @lem3680109 _93670 _93677 s x''''' y''''' P f t h1). Qed.
Lemma lem3680112 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3680113 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term972 _93670 _93677 f t) = (term787 _93670 _93677 f t).
Proof. exact (@lem3680112 (term787 _93670 _93677 f t)). Qed.
Lemma lem3680114 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term787 _93670 _93677 f t.
Proof. exact (EQ_MP (@lem3680113 _93670 _93677 f t) (@lem3680110 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3680117 {_93670 : Type'} (t : _93670 -> Prop) (h1 : term794 _93670 t) : term794 _93670 t.
Proof. exact (h1). Qed.
Lemma lem3680118 {_93670 : Type'} (t : _93670 -> Prop) (h1 : term794 _93670 t) : term973 _93670 t.
Proof. exact (fun h0 : @I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t => @lem3680117 _93670 t h1). Qed.
Lemma lem3680120 (p : Prop) : (term974 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3680121 {_93670 : Type'} (t : _93670 -> Prop) : (term973 _93670 t) = (term794 _93670 t).
Proof. exact (@lem3680120 (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t)). Qed.
Lemma lem3680122 {_93670 : Type'} (t : _93670 -> Prop) (h1 : term794 _93670 t) : term794 _93670 t.
Proof. exact (EQ_MP (@lem3680121 _93670 t) (@lem3680118 _93670 t h1)). Qed.
Lemma lem3680124 (b : Prop) (a : Prop) : (a \/ b) = (term975 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3680125 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term952 _93670 _93677 x'''' _40148 _40149) = (term976 _93670 _93677 x'''' _40148 _40149).
Proof. exact (@lem3680124 (term793 _93670 _93677 _40148 _40149) (term818 _93670 _93677 x'''' _40148 _40149)). Qed.
Lemma lem3680127 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3680128 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term979 _93670 _93677 _40148 _40149) = (term980 _93670 _93677 _40148 _40149).
Proof. exact (@lem3680127 (term789 _93670 _93677 _40148 _40149) (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40149)). Qed.
Lemma lem3680130 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3680131 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term982 _93670 _93677 _40148 _40149) = (term787 _93670 _93677 _40148 _40149).
Proof. exact (@lem3680130 (term787 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3680133 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term983 _93670 _93677 _40148 _40149) = (term901 _93670 _93677 _40148 _40149).
Proof. exact (MK_COMB (@lem3680132) (@lem3680131 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680134 {_93670 : Type'} (_40149 : _93670 -> Prop) : (term794 _93670 _40149) = (term794 _93670 _40149).
Proof. exact (eq_refl (term794 _93670 _40149)). Qed.
Lemma lem3680135 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term980 _93670 _93677 _40148 _40149) = (term984 _93670 _93677 _40148 _40149).
Proof. exact (MK_COMB (@lem3680133 _93670 _93677 _40148 _40149) (@lem3680134 _93670 _40149)). Qed.
Lemma lem3680136 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term979 _93670 _93677 _40148 _40149) = (term984 _93670 _93677 _40148 _40149).
Proof. exact (TRANS (@lem3680128 _93670 _93677 _40148 _40149) (@lem3680135 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680137 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3680138 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term985 _93670 _93677 _40148 _40149) = (term986 _93670 _93677 _40148 _40149).
Proof. exact (MK_COMB (@lem3680137) (@lem3680136 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680139 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term818 _93670 _93677 x'''' _40148 _40149) = (term818 _93670 _93677 x'''' _40148 _40149).
Proof. exact (eq_refl (term818 _93670 _93677 x'''' _40148 _40149)). Qed.
Lemma lem3680140 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term976 _93670 _93677 x'''' _40148 _40149) = (term987 _93670 _93677 x'''' _40148 _40149).
Proof. exact (MK_COMB (@lem3680138 _93670 _93677 _40148 _40149) (@lem3680139 _93670 _93677 x'''' _40148 _40149)). Qed.
Lemma lem3680141 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term952 _93670 _93677 x'''' _40148 _40149) = (term987 _93670 _93677 x'''' _40148 _40149).
Proof. exact (TRANS (@lem3680125 _93670 _93677 x'''' _40148 _40149) (@lem3680140 _93670 _93677 x'''' _40148 _40149)). Qed.
Lemma lem3680143 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term794 _93670 t) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : term984 _93670 _93677 f t.
Proof. exact (conj (@lem3680114 _93670 _93677 s x''''' y''''' P f t h2) (@lem3680122 _93670 t h1)). Qed.
Lemma lem3680145 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term987 _93670 _93677 x'''' _40148 _40149.
Proof. exact (EQ_MP (@lem3680141 _93670 _93677 x'''' _40148 _40149) (@lem3670522 _93670 _93677 _40148 _40149 x'''' y'''' h1)). Qed.
Lemma lem3680146 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term987 _93670 _93677 x'''' _40148 _40149.
Proof. exact (@lem3680145 _93670 _93677 _40148 _40149 x'''' y'''' h1). Qed.
Lemma lem3680147 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term987 _93670 _93677 x'''' f t.
Proof. exact (@lem3680146 _93670 _93677 f t x'''' y'''' h1). Qed.
Lemma lem3680150 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term818 _93670 _93677 x'''' f t.
Proof. exact (@lem3680147 _93670 _93677 f t x'''' y'''' h1 (@lem3680143 _93670 _93677 s x''''' y''''' P f t h2 h3)). Qed.
Lemma lem3680151 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term988 _93670 _93677 x'''' f t.
Proof. exact (fun h0 : term989 _93670 _93677 x'''' f t => @lem3680150 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3). Qed.
Lemma lem3680153 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3680154 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term988 _93670 _93677 x'''' f t) = (term818 _93670 _93677 x'''' f t).
Proof. exact (@lem3680153 (term818 _93670 _93677 x'''' f t)). Qed.
Lemma lem3680155 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term818 _93670 _93677 x'''' f t.
Proof. exact (EQ_MP (@lem3680154 _93670 _93677 x'''' f t) (@lem3680151 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3)). Qed.
Lemma lem3680157 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term787 _93670 _93677 f t.
Proof. exact (proj1 (@lem3661507 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3680158 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term972 _93670 _93677 f t.
Proof. exact (fun h0 : term789 _93670 _93677 f t => @lem3680157 _93670 _93677 s x''''' y''''' P f t h1). Qed.
Lemma lem3680160 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3680161 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term972 _93670 _93677 f t) = (term787 _93670 _93677 f t).
Proof. exact (@lem3680160 (term787 _93670 _93677 f t)). Qed.
Lemma lem3680162 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term787 _93670 _93677 f t.
Proof. exact (EQ_MP (@lem3680161 _93670 _93677 f t) (@lem3680158 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3680165 {_93670 : Type'} (t : _93670 -> Prop) (h1 : term794 _93670 t) : term794 _93670 t.
Proof. exact (h1). Qed.
Lemma lem3680166 {_93670 : Type'} (t : _93670 -> Prop) (h1 : term794 _93670 t) : term973 _93670 t.
Proof. exact (fun h0 : @I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t => @lem3680165 _93670 t h1). Qed.
Lemma lem3680168 (p : Prop) : (term974 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3680169 {_93670 : Type'} (t : _93670 -> Prop) : (term973 _93670 t) = (term794 _93670 t).
Proof. exact (@lem3680168 (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t)). Qed.
Lemma lem3680170 {_93670 : Type'} (t : _93670 -> Prop) (h1 : term794 _93670 t) : term794 _93670 t.
Proof. exact (EQ_MP (@lem3680169 _93670 t) (@lem3680166 _93670 t h1)). Qed.
Lemma lem3680172 (b : Prop) (a : Prop) : (a \/ b) = (term975 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3680173 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term952 _93670 _93677 y'''' _40148 _40149) = (term976 _93670 _93677 y'''' _40148 _40149).
Proof. exact (@lem3680172 (term793 _93670 _93677 _40148 _40149) (term818 _93670 _93677 y'''' _40148 _40149)). Qed.
Lemma lem3680175 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3680176 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term979 _93670 _93677 _40148 _40149) = (term980 _93670 _93677 _40148 _40149).
Proof. exact (@lem3680175 (term789 _93670 _93677 _40148 _40149) (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40149)). Qed.
Lemma lem3680178 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3680179 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term982 _93670 _93677 _40148 _40149) = (term787 _93670 _93677 _40148 _40149).
Proof. exact (@lem3680178 (term787 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680180 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3680181 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term983 _93670 _93677 _40148 _40149) = (term901 _93670 _93677 _40148 _40149).
Proof. exact (MK_COMB (@lem3680180) (@lem3680179 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680182 {_93670 : Type'} (_40149 : _93670 -> Prop) : (term794 _93670 _40149) = (term794 _93670 _40149).
Proof. exact (eq_refl (term794 _93670 _40149)). Qed.
Lemma lem3680183 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term980 _93670 _93677 _40148 _40149) = (term984 _93670 _93677 _40148 _40149).
Proof. exact (MK_COMB (@lem3680181 _93670 _93677 _40148 _40149) (@lem3680182 _93670 _40149)). Qed.
Lemma lem3680184 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term979 _93670 _93677 _40148 _40149) = (term984 _93670 _93677 _40148 _40149).
Proof. exact (TRANS (@lem3680176 _93670 _93677 _40148 _40149) (@lem3680183 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680185 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3680186 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term985 _93670 _93677 _40148 _40149) = (term986 _93670 _93677 _40148 _40149).
Proof. exact (MK_COMB (@lem3680185) (@lem3680184 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680187 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term818 _93670 _93677 y'''' _40148 _40149) = (term818 _93670 _93677 y'''' _40148 _40149).
Proof. exact (eq_refl (term818 _93670 _93677 y'''' _40148 _40149)). Qed.
Lemma lem3680188 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term976 _93670 _93677 y'''' _40148 _40149) = (term987 _93670 _93677 y'''' _40148 _40149).
Proof. exact (MK_COMB (@lem3680186 _93670 _93677 _40148 _40149) (@lem3680187 _93670 _93677 y'''' _40148 _40149)). Qed.
Lemma lem3680189 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term952 _93670 _93677 y'''' _40148 _40149) = (term987 _93670 _93677 y'''' _40148 _40149).
Proof. exact (TRANS (@lem3680173 _93670 _93677 y'''' _40148 _40149) (@lem3680188 _93670 _93677 y'''' _40148 _40149)). Qed.
Lemma lem3680191 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term794 _93670 t) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : term984 _93670 _93677 f t.
Proof. exact (conj (@lem3680162 _93670 _93677 s x''''' y''''' P f t h2) (@lem3680170 _93670 t h1)). Qed.
Lemma lem3680193 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term987 _93670 _93677 y'''' _40148 _40149.
Proof. exact (EQ_MP (@lem3680189 _93670 _93677 y'''' _40148 _40149) (@lem3670532 _93670 _93677 _40148 _40149 x'''' y'''' h1)). Qed.
Lemma lem3680194 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term987 _93670 _93677 y'''' _40148 _40149.
Proof. exact (@lem3680193 _93670 _93677 _40148 _40149 x'''' y'''' h1). Qed.
Lemma lem3680195 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term987 _93670 _93677 y'''' f t.
Proof. exact (@lem3680194 _93670 _93677 f t x'''' y'''' h1). Qed.
Lemma lem3680198 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term818 _93670 _93677 y'''' f t.
Proof. exact (@lem3680195 _93670 _93677 f t x'''' y'''' h1 (@lem3680191 _93670 _93677 s x''''' y''''' P f t h2 h3)). Qed.
Lemma lem3680199 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term988 _93670 _93677 y'''' f t.
Proof. exact (fun h0 : term989 _93670 _93677 y'''' f t => @lem3680198 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3). Qed.
Lemma lem3680201 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3680202 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term988 _93670 _93677 y'''' f t) = (term818 _93670 _93677 y'''' f t).
Proof. exact (@lem3680201 (term818 _93670 _93677 y'''' f t)). Qed.
Lemma lem3680203 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term818 _93670 _93677 y'''' f t.
Proof. exact (EQ_MP (@lem3680202 _93670 _93677 y'''' f t) (@lem3680199 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3)). Qed.
Lemma lem3680205 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term787 _93670 _93677 f t.
Proof. exact (proj1 (@lem3661507 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3680206 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term972 _93670 _93677 f t.
Proof. exact (fun h0 : term789 _93670 _93677 f t => @lem3680205 _93670 _93677 s x''''' y''''' P f t h1). Qed.
Lemma lem3680208 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3680209 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term972 _93670 _93677 f t) = (term787 _93670 _93677 f t).
Proof. exact (@lem3680208 (term787 _93670 _93677 f t)). Qed.
Lemma lem3680210 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term787 _93670 _93677 f t.
Proof. exact (EQ_MP (@lem3680209 _93670 _93677 f t) (@lem3680206 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3680213 {_93670 : Type'} (t : _93670 -> Prop) (h1 : term794 _93670 t) : term794 _93670 t.
Proof. exact (h1). Qed.
Lemma lem3680214 {_93670 : Type'} (t : _93670 -> Prop) (h1 : term794 _93670 t) : term973 _93670 t.
Proof. exact (fun h0 : @I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t => @lem3680213 _93670 t h1). Qed.
Lemma lem3680216 (p : Prop) : (term974 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3680217 {_93670 : Type'} (t : _93670 -> Prop) : (term973 _93670 t) = (term794 _93670 t).
Proof. exact (@lem3680216 (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t)). Qed.
Lemma lem3680218 {_93670 : Type'} (t : _93670 -> Prop) (h1 : term794 _93670 t) : term794 _93670 t.
Proof. exact (EQ_MP (@lem3680217 _93670 t) (@lem3680214 _93670 t h1)). Qed.
Lemma lem3680220 (b : Prop) (a : Prop) : (a \/ b) = (term975 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3680221 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term912 _93670 _93677 x'''' y'''' _40148 _40149) = (term990 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (@lem3680220 (term793 _93670 _93677 _40148 _40149) (term806 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3680223 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3680224 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term979 _93670 _93677 _40148 _40149) = (term980 _93670 _93677 _40148 _40149).
Proof. exact (@lem3680223 (term789 _93670 _93677 _40148 _40149) (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40149)). Qed.
Lemma lem3680226 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3680227 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term982 _93670 _93677 _40148 _40149) = (term787 _93670 _93677 _40148 _40149).
Proof. exact (@lem3680226 (term787 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3680229 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term983 _93670 _93677 _40148 _40149) = (term901 _93670 _93677 _40148 _40149).
Proof. exact (MK_COMB (@lem3680228) (@lem3680227 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680230 {_93670 : Type'} (_40149 : _93670 -> Prop) : (term794 _93670 _40149) = (term794 _93670 _40149).
Proof. exact (eq_refl (term794 _93670 _40149)). Qed.
Lemma lem3680231 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term980 _93670 _93677 _40148 _40149) = (term984 _93670 _93677 _40148 _40149).
Proof. exact (MK_COMB (@lem3680229 _93670 _93677 _40148 _40149) (@lem3680230 _93670 _40149)). Qed.
Lemma lem3680232 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term979 _93670 _93677 _40148 _40149) = (term984 _93670 _93677 _40148 _40149).
Proof. exact (TRANS (@lem3680224 _93670 _93677 _40148 _40149) (@lem3680231 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680233 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3680234 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term985 _93670 _93677 _40148 _40149) = (term986 _93670 _93677 _40148 _40149).
Proof. exact (MK_COMB (@lem3680233) (@lem3680232 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680235 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term806 _93670 _93677 x'''' y'''' _40148 _40149) = (term806 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (eq_refl (term806 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3680236 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term990 _93670 _93677 x'''' y'''' _40148 _40149) = (term991 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (MK_COMB (@lem3680234 _93670 _93677 _40148 _40149) (@lem3680235 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3680237 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term912 _93670 _93677 x'''' y'''' _40148 _40149) = (term991 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (TRANS (@lem3680221 _93670 _93677 x'''' y'''' _40148 _40149) (@lem3680236 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3680239 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term794 _93670 t) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : term984 _93670 _93677 f t.
Proof. exact (conj (@lem3680210 _93670 _93677 s x''''' y''''' P f t h2) (@lem3680218 _93670 t h1)). Qed.
Lemma lem3680241 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term991 _93670 _93677 x'''' y'''' _40148 _40149.
Proof. exact (EQ_MP (@lem3680237 _93670 _93677 x'''' y'''' _40148 _40149) (@lem3670512 _93670 _93677 _40148 _40149 x'''' y'''' h1)). Qed.
Lemma lem3680242 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term991 _93670 _93677 x'''' y'''' _40148 _40149.
Proof. exact (@lem3680241 _93670 _93677 _40148 _40149 x'''' y'''' h1). Qed.
Lemma lem3680243 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term991 _93670 _93677 x'''' y'''' f t.
Proof. exact (@lem3680242 _93670 _93677 f t x'''' y'''' h1). Qed.
Lemma lem3680246 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term806 _93670 _93677 x'''' y'''' f t.
Proof. exact (@lem3680243 _93670 _93677 f t x'''' y'''' h1 (@lem3680239 _93670 _93677 s x''''' y''''' P f t h2 h3)). Qed.
Lemma lem3680247 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term992 _93670 _93677 x'''' y'''' f t.
Proof. exact (fun h0 : (term802 _93670 _93677 x'''' f t) = (term802 _93670 _93677 y'''' f t) => @lem3680246 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3). Qed.
Lemma lem3680249 (p : Prop) : (term974 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3680250 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term992 _93670 _93677 x'''' y'''' f t) = (term806 _93670 _93677 x'''' y'''' f t).
Proof. exact (@lem3680249 ((term802 _93670 _93677 x'''' f t) = (term802 _93670 _93677 y'''' f t))). Qed.
Lemma lem3680251 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term806 _93670 _93677 x'''' y'''' f t.
Proof. exact (EQ_MP (@lem3680250 _93670 _93677 x'''' y'''' f t) (@lem3680247 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3)). Qed.
Lemma lem3680267 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3680268 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (_40150 : _93670) (_40151 : _93670) : (term993 _93670 _93677 t f _40150 _40151) = (term994 _93670 _93677 f t _40150 _40151).
Proof. exact (@lem3680267 (term843 _93670 _93677 _40150 f _40151) (term858 _93670 _40151 t) (_40150 = _40151)). Qed.
Lemma lem3680284 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3680285 {_93670 : Type'} (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : (term995 _93670 t _40150 _40151) = (term996 _93670 _40150 _40151 t).
Proof. exact (@lem3680284 (_40150 = _40151) (term858 _93670 _40151 t)). Qed.
Lemma lem3680293 {_93670 _93677 : Type'} (_40150 : _93670) (f : _93670 -> _93677) (_40151 : _93670) : (term845 _93670 _93677 _40150 f _40151) = (term845 _93670 _93677 _40150 f _40151).
Proof. exact (eq_refl (term845 _93670 _93677 _40150 f _40151)). Qed.
Lemma lem3680294 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : (term994 _93670 _93677 f t _40150 _40151) = (term997 _93670 _93677 f _40150 _40151 t).
Proof. exact (MK_COMB (@lem3680293 _93670 _93677 _40150 f _40151) (@lem3680285 _93670 _40150 _40151 t)). Qed.
Lemma lem3680298 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3680299 {_93670 _93677 : Type'} (_40150 : _93670) (f : _93670 -> _93677) (_40151 : _93670) (t : _93670 -> Prop) : (term997 _93670 _93677 f _40150 _40151 t) = (term998 _93670 _93677 _40150 f _40151 t).
Proof. exact (@lem3680298 (_40150 = _40151) (term843 _93670 _93677 _40150 f _40151) (term858 _93670 _40151 t)). Qed.
Lemma lem3680319 {_93670 _93677 : Type'} (_40150 : _93670) (f : _93670 -> _93677) (_40151 : _93670) (t : _93670 -> Prop) : (term994 _93670 _93677 f t _40150 _40151) = (term998 _93670 _93677 _40150 f _40151 t).
Proof. exact (TRANS (@lem3680294 _93670 _93677 f _40150 _40151 t) (@lem3680299 _93670 _93677 _40150 f _40151 t)). Qed.
Lemma lem3680320 {_93670 _93677 : Type'} (_40150 : _93670) (f : _93670 -> _93677) (_40151 : _93670) (t : _93670 -> Prop) : (term993 _93670 _93677 t f _40150 _40151) = (term998 _93670 _93677 _40150 f _40151 t).
Proof. exact (TRANS (@lem3680268 _93670 _93677 f t _40150 _40151) (@lem3680319 _93670 _93677 _40150 f _40151 t)). Qed.
Lemma lem3680321 {_93670 : Type'} (_40150 : _93670) (t : _93670 -> Prop) : (term860 _93670 _40150 t) = (term860 _93670 _40150 t).
Proof. exact (eq_refl (term860 _93670 _40150 t)). Qed.
Lemma lem3680322 {_93670 _93677 : Type'} (_40150 : _93670) (f : _93670 -> _93677) (_40151 : _93670) (t : _93670 -> Prop) : (term951 _93670 _93677 t f _40150 _40151) = (term999 _93670 _93677 _40150 f _40151 t).
Proof. exact (MK_COMB (@lem3680321 _93670 _40150 t) (@lem3680320 _93670 _93677 _40150 f _40151 t)). Qed.
Lemma lem3680326 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3680327 {_93670 _93677 : Type'} (_40150 : _93670) (f : _93670 -> _93677) (_40151 : _93670) (t : _93670 -> Prop) : (term999 _93670 _93677 _40150 f _40151 t) = (term1000 _93670 _93677 _40150 f _40151 t).
Proof. exact (@lem3680326 (_40150 = _40151) (term858 _93670 _40150 t) (term1001 _93670 _93677 _40150 f _40151 t)). Qed.
Lemma lem3680343 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3680344 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : (term1002 _93670 _93677 _40150 f _40151 t) = (term1003 _93670 _93677 f _40150 _40151 t).
Proof. exact (@lem3680343 (term843 _93670 _93677 _40150 f _40151) (term858 _93670 _40150 t) (term858 _93670 _40151 t)). Qed.
Lemma lem3680362 {_93670 : Type'} (_40150 : _93670) (_40151 : _93670) : (term1004 _93670 _40150 _40151) = (term1004 _93670 _40150 _40151).
Proof. exact (eq_refl (term1004 _93670 _40150 _40151)). Qed.
Lemma lem3680363 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : (term1000 _93670 _93677 _40150 f _40151 t) = (term1005 _93670 _93677 f _40150 _40151 t).
Proof. exact (MK_COMB (@lem3680362 _93670 _40150 _40151) (@lem3680344 _93670 _93677 f _40150 _40151 t)). Qed.
Lemma lem3680374 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : (term999 _93670 _93677 _40150 f _40151 t) = (term1005 _93670 _93677 f _40150 _40151 t).
Proof. exact (TRANS (@lem3680327 _93670 _93677 _40150 f _40151 t) (@lem3680363 _93670 _93677 f _40150 _40151 t)). Qed.
Lemma lem3680375 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : (term951 _93670 _93677 t f _40150 _40151) = (term1005 _93670 _93677 f _40150 _40151 t).
Proof. exact (TRANS (@lem3680322 _93670 _93677 _40150 f _40151 t) (@lem3680374 _93670 _93677 f _40150 _40151 t)). Qed.
Lemma lem3680376 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3680377 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : (term1006 _93670 _93677 t f _40150 _40151) = (term1007 _93670 _93677 f _40150 _40151 t).
Proof. exact (MK_COMB (@lem3680376) (@lem3680375 _93670 _93677 f _40150 _40151 t)). Qed.
Lemma lem3680403 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3680404 {_93670 : Type'} (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : (term995 _93670 t _40150 _40151) = (term996 _93670 _40150 _40151 t).
Proof. exact (@lem3680403 (_40150 = _40151) (term858 _93670 _40151 t)). Qed.
Lemma lem3680412 {_93670 : Type'} (_40150 : _93670) (t : _93670 -> Prop) : (term860 _93670 _40150 t) = (term860 _93670 _40150 t).
Proof. exact (eq_refl (term860 _93670 _40150 t)). Qed.
Lemma lem3680413 {_93670 : Type'} (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : (term1008 _93670 t _40150 _40151) = (term1009 _93670 _40150 _40151 t).
Proof. exact (MK_COMB (@lem3680412 _93670 _40150 t) (@lem3680404 _93670 _40150 _40151 t)). Qed.
Lemma lem3680417 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3680418 {_93670 : Type'} (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : (term1009 _93670 _40150 _40151 t) = (term1010 _93670 _40150 _40151 t).
Proof. exact (@lem3680417 (_40150 = _40151) (term858 _93670 _40150 t) (term858 _93670 _40151 t)). Qed.
Lemma lem3680436 {_93670 : Type'} (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : (term1008 _93670 t _40150 _40151) = (term1010 _93670 _40150 _40151 t).
Proof. exact (TRANS (@lem3680413 _93670 _40150 _40151 t) (@lem3680418 _93670 _40150 _40151 t)). Qed.
Lemma lem3680437 {_93670 _93677 : Type'} (_40150 : _93670) (f : _93670 -> _93677) (_40151 : _93670) : (term845 _93670 _93677 _40150 f _40151) = (term845 _93670 _93677 _40150 f _40151).
Proof. exact (eq_refl (term845 _93670 _93677 _40150 f _40151)). Qed.
Lemma lem3680438 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : (term1011 _93670 _93677 f t _40150 _40151) = (term1012 _93670 _93677 f _40150 _40151 t).
Proof. exact (MK_COMB (@lem3680437 _93670 _93677 _40150 f _40151) (@lem3680436 _93670 _40150 _40151 t)). Qed.
Lemma lem3680442 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3680443 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : (term1012 _93670 _93677 f _40150 _40151 t) = (term1005 _93670 _93677 f _40150 _40151 t).
Proof. exact (@lem3680442 (_40150 = _40151) (term843 _93670 _93677 _40150 f _40151) (term861 _93670 _40150 _40151 t)). Qed.
Lemma lem3680473 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : (term1011 _93670 _93677 f t _40150 _40151) = (term1005 _93670 _93677 f _40150 _40151 t).
Proof. exact (TRANS (@lem3680438 _93670 _93677 f _40150 _40151 t) (@lem3680443 _93670 _93677 f _40150 _40151 t)). Qed.
Lemma lem3680474 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : ((term951 _93670 _93677 t f _40150 _40151) = (term1011 _93670 _93677 f t _40150 _40151)) = ((term1005 _93670 _93677 f _40150 _40151 t) = (term1005 _93670 _93677 f _40150 _40151 t)).
Proof. exact (MK_COMB (@lem3680377 _93670 _93677 f _40150 _40151 t) (@lem3680473 _93670 _93677 f _40150 _40151 t)). Qed.
Lemma lem3680476 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3680477 (x : Prop) : (x = x) = True.
Proof. exact (@lem3680476 Prop x). Qed.
Lemma lem3680478 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40150 : _93670) (_40151 : _93670) (t : _93670 -> Prop) : ((term1005 _93670 _93677 f _40150 _40151 t) = (term1005 _93670 _93677 f _40150 _40151 t)) = True.
Proof. exact (@lem3680477 (term1005 _93670 _93677 f _40150 _40151 t)). Qed.
Lemma lem3680479 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (_40150 : _93670) (_40151 : _93670) : ((term951 _93670 _93677 t f _40150 _40151) = (term1011 _93670 _93677 f t _40150 _40151)) = True.
Proof. exact (TRANS (@lem3680474 _93670 _93677 f _40150 _40151 t) (@lem3680478 _93670 _93677 f _40150 _40151 t)). Qed.
Lemma lem3680480 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (_40150 : _93670) (_40151 : _93670) : True = ((term951 _93670 _93677 t f _40150 _40151) = (term1011 _93670 _93677 f t _40150 _40151)).
Proof. exact (SYM (@lem3680479 _93670 _93677 f t _40150 _40151)). Qed.
Lemma lem3680481 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (_40150 : _93670) (_40151 : _93670) : (term951 _93670 _93677 t f _40150 _40151) = (term1011 _93670 _93677 f t _40150 _40151).
Proof. exact (EQ_MP (@lem3680480 _93670 _93677 f t _40150 _40151) (@lem0)). Qed.
Lemma lem3680482 {_93670 _93677 : Type'} (_40150 : _93670) (_40151 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term1011 _93670 _93677 f t _40150 _40151.
Proof. exact (EQ_MP (@lem3680481 _93670 _93677 f t _40150 _40151) (@lem3670502 _93670 _93677 _40150 _40151 s x''''' y''''' P f t h1)). Qed.
Lemma lem3680484 (b : Prop) (a : Prop) : (a \/ b) = (term975 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3680485 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40150 : _93670) (f : _93670 -> _93677) (_40151 : _93670) : (term1011 _93670 _93677 f t _40150 _40151) = (term1013 _93670 _93677 t _40150 f _40151).
Proof. exact (@lem3680484 (term1008 _93670 t _40150 _40151) (term843 _93670 _93677 _40150 f _40151)). Qed.
Lemma lem3680487 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3680488 {_93670 : Type'} (t : _93670 -> Prop) (_40150 : _93670) (_40151 : _93670) : (term1014 _93670 t _40150 _40151) = (term1015 _93670 t _40150 _40151).
Proof. exact (@lem3680487 (term858 _93670 _40150 t) (term995 _93670 t _40150 _40151)). Qed.
Lemma lem3680490 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3680491 {_93670 : Type'} (_40150 : _93670) (t : _93670 -> Prop) : (term1016 _93670 _40150 t) = (term856 _93670 _40150 t).
Proof. exact (@lem3680490 (term856 _93670 _40150 t)). Qed.
Lemma lem3680492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3680493 {_93670 : Type'} (_40150 : _93670) (t : _93670 -> Prop) : (term1017 _93670 _40150 t) = (term885 _93670 _40150 t).
Proof. exact (MK_COMB (@lem3680492) (@lem3680491 _93670 _40150 t)). Qed.
Lemma lem3680495 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3680496 {_93670 : Type'} (t : _93670 -> Prop) (_40150 : _93670) (_40151 : _93670) : (term1018 _93670 t _40150 _40151) = (term1019 _93670 t _40150 _40151).
Proof. exact (@lem3680495 (term858 _93670 _40151 t) (_40150 = _40151)). Qed.
Lemma lem3680498 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3680499 {_93670 : Type'} (_40151 : _93670) (t : _93670 -> Prop) : (term1016 _93670 _40151 t) = (term856 _93670 _40151 t).
Proof. exact (@lem3680498 (term856 _93670 _40151 t)). Qed.
Lemma lem3680500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3680501 {_93670 : Type'} (_40151 : _93670) (t : _93670 -> Prop) : (term1017 _93670 _40151 t) = (term885 _93670 _40151 t).
Proof. exact (MK_COMB (@lem3680500) (@lem3680499 _93670 _40151 t)). Qed.
Lemma lem3680502 {_93670 : Type'} (_40150 : _93670) (_40151 : _93670) : (term848 _93670 _40150 _40151) = (term848 _93670 _40150 _40151).
Proof. exact (eq_refl (term848 _93670 _40150 _40151)). Qed.
Lemma lem3680503 {_93670 : Type'} (t : _93670 -> Prop) (_40150 : _93670) (_40151 : _93670) : (term1019 _93670 t _40150 _40151) = (term1020 _93670 t _40150 _40151).
Proof. exact (MK_COMB (@lem3680501 _93670 _40151 t) (@lem3680502 _93670 _40150 _40151)). Qed.
Lemma lem3680504 {_93670 : Type'} (t : _93670 -> Prop) (_40150 : _93670) (_40151 : _93670) : (term1018 _93670 t _40150 _40151) = (term1020 _93670 t _40150 _40151).
Proof. exact (TRANS (@lem3680496 _93670 t _40150 _40151) (@lem3680503 _93670 t _40150 _40151)). Qed.
Lemma lem3680505 {_93670 : Type'} (t : _93670 -> Prop) (_40150 : _93670) (_40151 : _93670) : (term1015 _93670 t _40150 _40151) = (term1021 _93670 t _40150 _40151).
Proof. exact (MK_COMB (@lem3680493 _93670 _40150 t) (@lem3680504 _93670 t _40150 _40151)). Qed.
Lemma lem3680506 {_93670 : Type'} (t : _93670 -> Prop) (_40150 : _93670) (_40151 : _93670) : (term1014 _93670 t _40150 _40151) = (term1021 _93670 t _40150 _40151).
Proof. exact (TRANS (@lem3680488 _93670 t _40150 _40151) (@lem3680505 _93670 t _40150 _40151)). Qed.
Lemma lem3680507 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3680508 {_93670 : Type'} (t : _93670 -> Prop) (_40150 : _93670) (_40151 : _93670) : (term1022 _93670 t _40150 _40151) = (term1023 _93670 t _40150 _40151).
Proof. exact (MK_COMB (@lem3680507) (@lem3680506 _93670 t _40150 _40151)). Qed.
Lemma lem3680509 {_93670 _93677 : Type'} (_40150 : _93670) (f : _93670 -> _93677) (_40151 : _93670) : (term843 _93670 _93677 _40150 f _40151) = (term843 _93670 _93677 _40150 f _40151).
Proof. exact (eq_refl (term843 _93670 _93677 _40150 f _40151)). Qed.
Lemma lem3680510 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40150 : _93670) (f : _93670 -> _93677) (_40151 : _93670) : (term1013 _93670 _93677 t _40150 f _40151) = (term1024 _93670 _93677 t _40150 f _40151).
Proof. exact (MK_COMB (@lem3680508 _93670 t _40150 _40151) (@lem3680509 _93670 _93677 _40150 f _40151)). Qed.
Lemma lem3680511 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40150 : _93670) (f : _93670 -> _93677) (_40151 : _93670) : (term1011 _93670 _93677 f t _40150 _40151) = (term1024 _93670 _93677 t _40150 f _40151).
Proof. exact (TRANS (@lem3680485 _93670 _93677 t _40150 f _40151) (@lem3680510 _93670 _93677 t _40150 f _40151)). Qed.
Lemma lem3680513 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term1025 _93670 _93677 x'''' y'''' f t.
Proof. exact (conj (@lem3680203 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3) (@lem3680251 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3)). Qed.
Lemma lem3680514 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term1026 _93670 _93677 x'''' y'''' f t.
Proof. exact (conj (@lem3680155 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3) (@lem3680513 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3)). Qed.
Lemma lem3680516 {_93670 _93677 : Type'} (_40150 : _93670) (_40151 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term1024 _93670 _93677 t _40150 f _40151.
Proof. exact (EQ_MP (@lem3680511 _93670 _93677 t _40150 f _40151) (@lem3680482 _93670 _93677 _40150 _40151 s x''''' y''''' P f t h1)). Qed.
Lemma lem3680517 {_93670 _93677 : Type'} (_40150 : _93670) (_40151 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term1024 _93670 _93677 t _40150 f _40151.
Proof. exact (@lem3680516 _93670 _93677 _40150 _40151 s x''''' y''''' P f t h1). Qed.
Lemma lem3680518 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term1027 _93670 _93677 x'''' y'''' f t.
Proof. exact (@lem3680517 _93670 _93677 (term802 _93670 _93677 x'''' f t) (term802 _93670 _93677 y'''' f t) s x''''' y''''' P f t h1). Qed.
Lemma lem3680521 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term1028 _93670 _93677 x'''' y'''' f t.
Proof. exact (@lem3680518 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h3 (@lem3680514 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3)). Qed.
Lemma lem3680522 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term1029 _93670 _93677 x'''' y'''' f t.
Proof. exact (fun h0 : (term809 _93670 _93677 x'''' f t) = (term809 _93670 _93677 y'''' f t) => @lem3680521 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3). Qed.
Lemma lem3680524 (p : Prop) : (term974 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3680525 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term1029 _93670 _93677 x'''' y'''' f t) = (term1028 _93670 _93677 x'''' y'''' f t).
Proof. exact (@lem3680524 ((term809 _93670 _93677 x'''' f t) = (term809 _93670 _93677 y'''' f t))). Qed.
Lemma lem3680526 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term1028 _93670 _93677 x'''' y'''' f t.
Proof. exact (EQ_MP (@lem3680525 _93670 _93677 x'''' y'''' f t) (@lem3680522 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3)). Qed.
Lemma lem3680528 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term787 _93670 _93677 f t.
Proof. exact (proj1 (@lem3661507 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3680529 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term972 _93670 _93677 f t.
Proof. exact (fun h0 : term789 _93670 _93677 f t => @lem3680528 _93670 _93677 s x''''' y''''' P f t h1). Qed.
Lemma lem3680531 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3680532 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term972 _93670 _93677 f t) = (term787 _93670 _93677 f t).
Proof. exact (@lem3680531 (term787 _93670 _93677 f t)). Qed.
Lemma lem3680533 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term787 _93670 _93677 f t.
Proof. exact (EQ_MP (@lem3680532 _93670 _93677 f t) (@lem3680529 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3680551 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3680552 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term793 _93670 _93677 _40148 _40149) = (term1030 _93670 _93677 _40148 _40149).
Proof. exact (@lem3680551 (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40149) (term789 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680558 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term1031 _93670 _93677 x'''' y'''' _40148 _40149) = (term1031 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (eq_refl (term1031 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3680559 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term953 _93670 _93677 x'''' y'''' _40148 _40149) = (term1032 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (MK_COMB (@lem3680558 _93670 _93677 x'''' y'''' _40148 _40149) (@lem3680552 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3680571 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term1033 _93670 _93677 x'''' y'''' _40148 _40149) = (term1034 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (MK_COMB (@lem3680570) (@lem3680559 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3680575 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3680576 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term1035 _93670 _93677 x'''' y'''' _40148 _40149) = (term1032 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (@lem3680575 ((term809 _93670 _93677 x'''' _40148 _40149) = (term809 _93670 _93677 y'''' _40148 _40149)) (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40149) (term789 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680594 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : ((term953 _93670 _93677 x'''' y'''' _40148 _40149) = (term1035 _93670 _93677 x'''' y'''' _40148 _40149)) = ((term1032 _93670 _93677 x'''' y'''' _40148 _40149) = (term1032 _93670 _93677 x'''' y'''' _40148 _40149)).
Proof. exact (MK_COMB (@lem3680571 _93670 _93677 x'''' y'''' _40148 _40149) (@lem3680576 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3680596 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3680597 (x : Prop) : (x = x) = True.
Proof. exact (@lem3680596 Prop x). Qed.
Lemma lem3680598 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : ((term1032 _93670 _93677 x'''' y'''' _40148 _40149) = (term1032 _93670 _93677 x'''' y'''' _40148 _40149)) = True.
Proof. exact (@lem3680597 (term1032 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3680599 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : ((term953 _93670 _93677 x'''' y'''' _40148 _40149) = (term1035 _93670 _93677 x'''' y'''' _40148 _40149)) = True.
Proof. exact (TRANS (@lem3680594 _93670 _93677 x'''' y'''' _40148 _40149) (@lem3680598 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3680600 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : True = ((term953 _93670 _93677 x'''' y'''' _40148 _40149) = (term1035 _93670 _93677 x'''' y'''' _40148 _40149)).
Proof. exact (SYM (@lem3680599 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3680601 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term953 _93670 _93677 x'''' y'''' _40148 _40149) = (term1035 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (EQ_MP (@lem3680600 _93670 _93677 x'''' y'''' _40148 _40149) (@lem0)). Qed.
Lemma lem3680602 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1035 _93670 _93677 x'''' y'''' _40148 _40149.
Proof. exact (EQ_MP (@lem3680601 _93670 _93677 x'''' y'''' _40148 _40149) (@lem3670542 _93670 _93677 _40148 _40149 x'''' y'''' h1)). Qed.
Lemma lem3680604 (b : Prop) (a : Prop) : (a \/ b) = (term975 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3680605 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term1035 _93670 _93677 x'''' y'''' _40148 _40149) = (term1036 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (@lem3680604 (term1037 _93670 _93677 x'''' y'''' _40148 _40149) (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40149)). Qed.
Lemma lem3680607 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3680608 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term1038 _93670 _93677 x'''' y'''' _40148 _40149) = (term1039 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (@lem3680607 ((term809 _93670 _93677 x'''' _40148 _40149) = (term809 _93670 _93677 y'''' _40148 _40149)) (term789 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680610 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3680611 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term982 _93670 _93677 _40148 _40149) = (term787 _93670 _93677 _40148 _40149).
Proof. exact (@lem3680610 (term787 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680612 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term1040 _93670 _93677 x'''' y'''' _40148 _40149) = (term1040 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (eq_refl (term1040 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3680613 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term1039 _93670 _93677 x'''' y'''' _40148 _40149) = (term1041 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (MK_COMB (@lem3680612 _93670 _93677 x'''' y'''' _40148 _40149) (@lem3680611 _93670 _93677 _40148 _40149)). Qed.
Lemma lem3680614 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term1038 _93670 _93677 x'''' y'''' _40148 _40149) = (term1041 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (TRANS (@lem3680608 _93670 _93677 x'''' y'''' _40148 _40149) (@lem3680613 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3680615 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3680616 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term1042 _93670 _93677 x'''' y'''' _40148 _40149) = (term1043 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (MK_COMB (@lem3680615) (@lem3680614 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3680617 {_93670 : Type'} (_40149 : _93670 -> Prop) : (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40149) = (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40149).
Proof. exact (eq_refl (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40149)). Qed.
Lemma lem3680618 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term1036 _93670 _93677 x'''' y'''' _40148 _40149) = (term1044 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (MK_COMB (@lem3680616 _93670 _93677 x'''' y'''' _40148 _40149) (@lem3680617 _93670 _40149)). Qed.
Lemma lem3680619 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) : (term1035 _93670 _93677 x'''' y'''' _40148 _40149) = (term1044 _93670 _93677 x'''' y'''' _40148 _40149).
Proof. exact (TRANS (@lem3680605 _93670 _93677 x'''' y'''' _40148 _40149) (@lem3680618 _93670 _93677 x'''' y'''' _40148 _40149)). Qed.
Lemma lem3680621 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term1041 _93670 _93677 x'''' y'''' f t.
Proof. exact (conj (@lem3680526 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3) (@lem3680533 _93670 _93677 s x''''' y''''' P f t h3)). Qed.
Lemma lem3680623 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1044 _93670 _93677 x'''' y'''' _40148 _40149.
Proof. exact (EQ_MP (@lem3680619 _93670 _93677 x'''' y'''' _40148 _40149) (@lem3680602 _93670 _93677 _40148 _40149 x'''' y'''' h1)). Qed.
Lemma lem3680624 {_93670 _93677 : Type'} (_40148 : _93670 -> _93677) (_40149 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1044 _93670 _93677 x'''' y'''' _40148 _40149.
Proof. exact (@lem3680623 _93670 _93677 _40148 _40149 x'''' y'''' h1). Qed.
Lemma lem3680625 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1044 _93670 _93677 x'''' y'''' f t.
Proof. exact (@lem3680624 _93670 _93677 f t x'''' y'''' h1). Qed.
Lemma lem3680628 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : @I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t.
Proof. exact (@lem3680625 _93670 _93677 f t x'''' y'''' h1 (@lem3680621 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3)). Qed.
Lemma lem3680629 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : term1045 _93670 t.
Proof. exact (fun h0 : term794 _93670 t => @lem3680628 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h0 h2). Qed.
Lemma lem3680631 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3680632 {_93670 : Type'} (t : _93670 -> Prop) : (term1045 _93670 t) = (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t).
Proof. exact (@lem3680631 (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t)). Qed.
Lemma lem3680633 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : @I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t.
Proof. exact (EQ_MP (@lem3680632 _93670 t) (@lem3680629 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2)). Qed.
Lemma lem3680636 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3680638 {_93670 : Type'} (t : _93670 -> Prop) : (term794 _93670 t) = (term1046 _93670 t).
Proof. exact (@lem3680636 (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t)). Qed.
Lemma lem3680641 {_93670 : Type'} (t : _93670 -> Prop) (h1 : term794 _93670 t) : term1046 _93670 t.
Proof. exact (EQ_MP (@lem3680638 _93670 t) (@lem3670470 _93670 t h1)). Qed.
Lemma lem3680644 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (@lem3680641 _93670 t h2 (@lem3680633 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h3)). Qed.
Lemma lem3680645 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : term971.
Proof. exact (fun h0 : ~ False => @lem3680644 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3). Qed.
Lemma lem3680647 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3680648 : term971 = False.
Proof. exact (@lem3680647 False). Qed.
Lemma lem3680649 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (EQ_MP (@lem3680648) (@lem3680645 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3)). Qed.
Lemma lem3681210 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (h1). Qed.
Lemma lem3681211 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : term1047 _93670 _93677 x''''' f y'''''.
Proof. exact (fun h0 : term843 _93670 _93677 x''''' f y''''' => @lem3681210 _93670 _93677 x''''' f y''''' h1). Qed.
Lemma lem3681213 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3681214 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term1047 _93670 _93677 x''''' f y''''') = ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')).
Proof. exact (@lem3681213 ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y'''''))). Qed.
Lemma lem3681215 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (EQ_MP (@lem3681214 _93670 _93677 x''''' f y''''') (@lem3681211 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3681218 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3681220 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term843 _93670 _93677 x''''' f y''''') = (term1048 _93670 _93677 x''''' f y''''').
Proof. exact (@lem3681218 ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y'''''))). Qed.
Lemma lem3681223 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') : term1048 _93670 _93677 x''''' f y'''''.
Proof. exact (EQ_MP (@lem3681220 _93670 _93677 x''''' f y''''') (@lem3670914 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3681226 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (@lem3681223 _93670 _93677 x''''' f y''''' h1 (@lem3681215 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3681227 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : term971.
Proof. exact (fun h0 : ~ False => @lem3681226 _93670 _93677 x''''' f y''''' h1 h2). Qed.
Lemma lem3681229 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3681230 : term971 = False.
Proof. exact (@lem3681229 False). Qed.
Lemma lem3681231 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3681230) (@lem3681227 _93670 _93677 x''''' f y''''' h1 h2)). Qed.
Lemma lem3681792 {_93677 : Type'} (x : _93677) : x = x.
Proof. exact (@lem21386 _93677 x). Qed.
Lemma lem3681793 {_93677 : Type'} (x : _93677) : x = x.
Proof. exact (@lem3681792 _93677 x). Qed.
Lemma lem3681794 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (@I (_93670 -> _93677) f y''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (@lem3681793 _93677 (@I (_93670 -> _93677) f y''''')). Qed.
Lemma lem3681795 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : term1049 _93670 _93677 f y'''''.
Proof. exact (fun h0 : term959 _93670 _93677 f y''''' => @lem3681794 _93670 _93677 f y'''''). Qed.
Lemma lem3681797 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3681798 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (term1049 _93670 _93677 f y''''') = ((@I (_93670 -> _93677) f y''''') = (@I (_93670 -> _93677) f y''''')).
Proof. exact (@lem3681797 ((@I (_93670 -> _93677) f y''''') = (@I (_93670 -> _93677) f y'''''))). Qed.
Lemma lem3681799 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (@I (_93670 -> _93677) f y''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (EQ_MP (@lem3681798 _93670 _93677 f y''''') (@lem3681795 _93670 _93677 f y''''')). Qed.
Lemma lem3681802 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3681804 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (term959 _93670 _93677 f y''''') = (term1050 _93670 _93677 f y''''').
Proof. exact (@lem3681802 ((@I (_93670 -> _93677) f y''''') = (@I (_93670 -> _93677) f y'''''))). Qed.
Lemma lem3681807 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : term1050 _93670 _93677 f y'''''.
Proof. exact (EQ_MP (@lem3681804 _93670 _93677 f y''''') (@lem3676326 _93670 _93677 f x''''' y''''' h1 h2)). Qed.
Lemma lem3681810 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (@lem3681807 _93670 _93677 f x''''' y''''' h1 h2 (@lem3681799 _93670 _93677 f y''''')). Qed.
Lemma lem3681811 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : term971.
Proof. exact (fun h0 : ~ False => @lem3681810 _93670 _93677 f x''''' y''''' h1 h2). Qed.
Lemma lem3681813 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3681814 : term971 = False.
Proof. exact (@lem3681813 False). Qed.
Lemma lem3682376 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term856 _93670 x''''' t.
Proof. exact (proj1 (@lem3661518 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3682377 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term1051 _93670 x''''' t.
Proof. exact (fun h0 : term858 _93670 x''''' t => @lem3682376 _93670 _93677 t f x''''' y''''' h1). Qed.
Lemma lem3682379 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3682380 {_93670 : Type'} (x''''' : _93670) (t : _93670 -> Prop) : (term1051 _93670 x''''' t) = (term856 _93670 x''''' t).
Proof. exact (@lem3682379 (term856 _93670 x''''' t)). Qed.
Lemma lem3682381 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term856 _93670 x''''' t.
Proof. exact (EQ_MP (@lem3682380 _93670 x''''' t) (@lem3682377 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3682383 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term856 _93670 y''''' t.
Proof. exact (proj2 (@lem3661518 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3682384 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term1051 _93670 y''''' t.
Proof. exact (fun h0 : term858 _93670 y''''' t => @lem3682383 _93670 _93677 t f x''''' y''''' h1). Qed.
Lemma lem3682386 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3682387 {_93670 : Type'} (y''''' : _93670) (t : _93670 -> Prop) : (term1051 _93670 y''''' t) = (term856 _93670 y''''' t).
Proof. exact (@lem3682386 (term856 _93670 y''''' t)). Qed.
Lemma lem3682388 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term856 _93670 y''''' t.
Proof. exact (EQ_MP (@lem3682387 _93670 y''''' t) (@lem3682384 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3682390 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (h1). Qed.
Lemma lem3682391 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : term1047 _93670 _93677 x''''' f y'''''.
Proof. exact (fun h0 : term843 _93670 _93677 x''''' f y''''' => @lem3682390 _93670 _93677 x''''' f y''''' h1). Qed.
Lemma lem3682393 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3682394 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term1047 _93670 _93677 x''''' f y''''') = ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')).
Proof. exact (@lem3682393 ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y'''''))). Qed.
Lemma lem3682395 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (EQ_MP (@lem3682394 _93670 _93677 x''''' f y''''') (@lem3682391 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3682411 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3682412 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (_40186 : _93670) (_40187 : _93670) : (term993 _93670 _93677 t f _40186 _40187) = (term994 _93670 _93677 f t _40186 _40187).
Proof. exact (@lem3682411 (term843 _93670 _93677 _40186 f _40187) (term858 _93670 _40187 t) (_40186 = _40187)). Qed.
Lemma lem3682428 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3682429 {_93670 : Type'} (_40186 : _93670) (_40187 : _93670) (t : _93670 -> Prop) : (term995 _93670 t _40186 _40187) = (term996 _93670 _40186 _40187 t).
Proof. exact (@lem3682428 (_40186 = _40187) (term858 _93670 _40187 t)). Qed.
Lemma lem3682437 {_93670 _93677 : Type'} (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) : (term845 _93670 _93677 _40186 f _40187) = (term845 _93670 _93677 _40186 f _40187).
Proof. exact (eq_refl (term845 _93670 _93677 _40186 f _40187)). Qed.
Lemma lem3682438 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) (t : _93670 -> Prop) : (term994 _93670 _93677 f t _40186 _40187) = (term997 _93670 _93677 f _40186 _40187 t).
Proof. exact (MK_COMB (@lem3682437 _93670 _93677 _40186 f _40187) (@lem3682429 _93670 _40186 _40187 t)). Qed.
Lemma lem3682442 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3682443 {_93670 _93677 : Type'} (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) (t : _93670 -> Prop) : (term997 _93670 _93677 f _40186 _40187 t) = (term998 _93670 _93677 _40186 f _40187 t).
Proof. exact (@lem3682442 (_40186 = _40187) (term843 _93670 _93677 _40186 f _40187) (term858 _93670 _40187 t)). Qed.
Lemma lem3682463 {_93670 _93677 : Type'} (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) (t : _93670 -> Prop) : (term994 _93670 _93677 f t _40186 _40187) = (term998 _93670 _93677 _40186 f _40187 t).
Proof. exact (TRANS (@lem3682438 _93670 _93677 f _40186 _40187 t) (@lem3682443 _93670 _93677 _40186 f _40187 t)). Qed.
Lemma lem3682464 {_93670 _93677 : Type'} (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) (t : _93670 -> Prop) : (term993 _93670 _93677 t f _40186 _40187) = (term998 _93670 _93677 _40186 f _40187 t).
Proof. exact (TRANS (@lem3682412 _93670 _93677 f t _40186 _40187) (@lem3682463 _93670 _93677 _40186 f _40187 t)). Qed.
Lemma lem3682465 {_93670 : Type'} (_40186 : _93670) (t : _93670 -> Prop) : (term860 _93670 _40186 t) = (term860 _93670 _40186 t).
Proof. exact (eq_refl (term860 _93670 _40186 t)). Qed.
Lemma lem3682466 {_93670 _93677 : Type'} (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) (t : _93670 -> Prop) : (term951 _93670 _93677 t f _40186 _40187) = (term999 _93670 _93677 _40186 f _40187 t).
Proof. exact (MK_COMB (@lem3682465 _93670 _40186 t) (@lem3682464 _93670 _93677 _40186 f _40187 t)). Qed.
Lemma lem3682470 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3682471 {_93670 _93677 : Type'} (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) (t : _93670 -> Prop) : (term999 _93670 _93677 _40186 f _40187 t) = (term1000 _93670 _93677 _40186 f _40187 t).
Proof. exact (@lem3682470 (_40186 = _40187) (term858 _93670 _40186 t) (term1001 _93670 _93677 _40186 f _40187 t)). Qed.
Lemma lem3682487 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3682488 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) (t : _93670 -> Prop) : (term1002 _93670 _93677 _40186 f _40187 t) = (term1003 _93670 _93677 f _40186 _40187 t).
Proof. exact (@lem3682487 (term843 _93670 _93677 _40186 f _40187) (term858 _93670 _40186 t) (term858 _93670 _40187 t)). Qed.
Lemma lem3682506 {_93670 : Type'} (_40186 : _93670) (_40187 : _93670) : (term1004 _93670 _40186 _40187) = (term1004 _93670 _40186 _40187).
Proof. exact (eq_refl (term1004 _93670 _40186 _40187)). Qed.
Lemma lem3682507 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) (t : _93670 -> Prop) : (term1000 _93670 _93677 _40186 f _40187 t) = (term1005 _93670 _93677 f _40186 _40187 t).
Proof. exact (MK_COMB (@lem3682506 _93670 _40186 _40187) (@lem3682488 _93670 _93677 f _40186 _40187 t)). Qed.
Lemma lem3682518 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) (t : _93670 -> Prop) : (term999 _93670 _93677 _40186 f _40187 t) = (term1005 _93670 _93677 f _40186 _40187 t).
Proof. exact (TRANS (@lem3682471 _93670 _93677 _40186 f _40187 t) (@lem3682507 _93670 _93677 f _40186 _40187 t)). Qed.
Lemma lem3682519 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) (t : _93670 -> Prop) : (term951 _93670 _93677 t f _40186 _40187) = (term1005 _93670 _93677 f _40186 _40187 t).
Proof. exact (TRANS (@lem3682466 _93670 _93677 _40186 f _40187 t) (@lem3682518 _93670 _93677 f _40186 _40187 t)). Qed.
Lemma lem3682520 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3682521 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) (t : _93670 -> Prop) : (term1006 _93670 _93677 t f _40186 _40187) = (term1007 _93670 _93677 f _40186 _40187 t).
Proof. exact (MK_COMB (@lem3682520) (@lem3682519 _93670 _93677 f _40186 _40187 t)). Qed.
Lemma lem3682547 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3682548 {_93670 _93677 : Type'} (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) (t : _93670 -> Prop) : (term1052 _93670 _93677 t _40186 f _40187) = (term1001 _93670 _93677 _40186 f _40187 t).
Proof. exact (@lem3682547 (term843 _93670 _93677 _40186 f _40187) (term858 _93670 _40187 t)). Qed.
Lemma lem3682556 {_93670 : Type'} (_40186 : _93670) (t : _93670 -> Prop) : (term860 _93670 _40186 t) = (term860 _93670 _40186 t).
Proof. exact (eq_refl (term860 _93670 _40186 t)). Qed.
Lemma lem3682557 {_93670 _93677 : Type'} (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) (t : _93670 -> Prop) : (term1053 _93670 _93677 t _40186 f _40187) = (term1002 _93670 _93677 _40186 f _40187 t).
Proof. exact (MK_COMB (@lem3682556 _93670 _40186 t) (@lem3682548 _93670 _93677 _40186 f _40187 t)). Qed.
Lemma lem3682561 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3682562 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) (t : _93670 -> Prop) : (term1002 _93670 _93677 _40186 f _40187 t) = (term1003 _93670 _93677 f _40186 _40187 t).
Proof. exact (@lem3682561 (term843 _93670 _93677 _40186 f _40187) (term858 _93670 _40186 t) (term858 _93670 _40187 t)). Qed.
Lemma lem3682580 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) (t : _93670 -> Prop) : (term1053 _93670 _93677 t _40186 f _40187) = (term1003 _93670 _93677 f _40186 _40187 t).
Proof. exact (TRANS (@lem3682557 _93670 _93677 _40186 f _40187 t) (@lem3682562 _93670 _93677 f _40186 _40187 t)). Qed.
Lemma lem3682581 {_93670 : Type'} (_40186 : _93670) (_40187 : _93670) : (term1004 _93670 _40186 _40187) = (term1004 _93670 _40186 _40187).
Proof. exact (eq_refl (term1004 _93670 _40186 _40187)). Qed.
Lemma lem3682582 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) (t : _93670 -> Prop) : (term1054 _93670 _93677 t _40186 f _40187) = (term1005 _93670 _93677 f _40186 _40187 t).
Proof. exact (MK_COMB (@lem3682581 _93670 _40186 _40187) (@lem3682580 _93670 _93677 f _40186 _40187 t)). Qed.
Lemma lem3682593 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) (t : _93670 -> Prop) : ((term951 _93670 _93677 t f _40186 _40187) = (term1054 _93670 _93677 t _40186 f _40187)) = ((term1005 _93670 _93677 f _40186 _40187 t) = (term1005 _93670 _93677 f _40186 _40187 t)).
Proof. exact (MK_COMB (@lem3682521 _93670 _93677 f _40186 _40187 t) (@lem3682582 _93670 _93677 f _40186 _40187 t)). Qed.
Lemma lem3682595 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3682596 (x : Prop) : (x = x) = True.
Proof. exact (@lem3682595 Prop x). Qed.
Lemma lem3682597 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) (t : _93670 -> Prop) : ((term1005 _93670 _93677 f _40186 _40187 t) = (term1005 _93670 _93677 f _40186 _40187 t)) = True.
Proof. exact (@lem3682596 (term1005 _93670 _93677 f _40186 _40187 t)). Qed.
Lemma lem3682598 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) : ((term951 _93670 _93677 t f _40186 _40187) = (term1054 _93670 _93677 t _40186 f _40187)) = True.
Proof. exact (TRANS (@lem3682593 _93670 _93677 f _40186 _40187 t) (@lem3682597 _93670 _93677 f _40186 _40187 t)). Qed.
Lemma lem3682599 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) : True = ((term951 _93670 _93677 t f _40186 _40187) = (term1054 _93670 _93677 t _40186 f _40187)).
Proof. exact (SYM (@lem3682598 _93670 _93677 t _40186 f _40187)). Qed.
Lemma lem3682600 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) : (term951 _93670 _93677 t f _40186 _40187) = (term1054 _93670 _93677 t _40186 f _40187).
Proof. exact (EQ_MP (@lem3682599 _93670 _93677 t _40186 f _40187) (@lem0)). Qed.
Lemma lem3682601 {_93670 _93677 : Type'} (_40186 : _93670) (_40187 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term1054 _93670 _93677 t _40186 f _40187.
Proof. exact (EQ_MP (@lem3682600 _93670 _93677 t _40186 f _40187) (@lem3671840 _93670 _93677 _40186 _40187 s x''''' y''''' P f t h1)). Qed.
Lemma lem3682603 (b : Prop) (a : Prop) : (a \/ b) = (term975 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3682604 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) : (term1054 _93670 _93677 t _40186 f _40187) = (term1055 _93670 _93677 t f _40186 _40187).
Proof. exact (@lem3682603 (term1053 _93670 _93677 t _40186 f _40187) (_40186 = _40187)). Qed.
Lemma lem3682606 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3682607 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) : (term1056 _93670 _93677 t _40186 f _40187) = (term1057 _93670 _93677 t _40186 f _40187).
Proof. exact (@lem3682606 (term858 _93670 _40186 t) (term1052 _93670 _93677 t _40186 f _40187)). Qed.
Lemma lem3682609 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3682610 {_93670 : Type'} (_40186 : _93670) (t : _93670 -> Prop) : (term1016 _93670 _40186 t) = (term856 _93670 _40186 t).
Proof. exact (@lem3682609 (term856 _93670 _40186 t)). Qed.
Lemma lem3682611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3682612 {_93670 : Type'} (_40186 : _93670) (t : _93670 -> Prop) : (term1017 _93670 _40186 t) = (term885 _93670 _40186 t).
Proof. exact (MK_COMB (@lem3682611) (@lem3682610 _93670 _40186 t)). Qed.
Lemma lem3682614 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3682615 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) : (term1058 _93670 _93677 t _40186 f _40187) = (term1059 _93670 _93677 t _40186 f _40187).
Proof. exact (@lem3682614 (term858 _93670 _40187 t) (term843 _93670 _93677 _40186 f _40187)). Qed.
Lemma lem3682617 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3682618 {_93670 : Type'} (_40187 : _93670) (t : _93670 -> Prop) : (term1016 _93670 _40187 t) = (term856 _93670 _40187 t).
Proof. exact (@lem3682617 (term856 _93670 _40187 t)). Qed.
Lemma lem3682619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3682620 {_93670 : Type'} (_40187 : _93670) (t : _93670 -> Prop) : (term1017 _93670 _40187 t) = (term885 _93670 _40187 t).
Proof. exact (MK_COMB (@lem3682619) (@lem3682618 _93670 _40187 t)). Qed.
Lemma lem3682622 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3682623 {_93670 _93677 : Type'} (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) : (term1060 _93670 _93677 _40186 f _40187) = ((@I (_93670 -> _93677) f _40186) = (@I (_93670 -> _93677) f _40187)).
Proof. exact (@lem3682622 ((@I (_93670 -> _93677) f _40186) = (@I (_93670 -> _93677) f _40187))). Qed.
Lemma lem3682624 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) : (term1059 _93670 _93677 t _40186 f _40187) = (term1061 _93670 _93677 t _40186 f _40187).
Proof. exact (MK_COMB (@lem3682620 _93670 _40187 t) (@lem3682623 _93670 _93677 _40186 f _40187)). Qed.
Lemma lem3682625 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) : (term1058 _93670 _93677 t _40186 f _40187) = (term1061 _93670 _93677 t _40186 f _40187).
Proof. exact (TRANS (@lem3682615 _93670 _93677 t _40186 f _40187) (@lem3682624 _93670 _93677 t _40186 f _40187)). Qed.
Lemma lem3682626 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) : (term1057 _93670 _93677 t _40186 f _40187) = (term1062 _93670 _93677 t _40186 f _40187).
Proof. exact (MK_COMB (@lem3682612 _93670 _40186 t) (@lem3682625 _93670 _93677 t _40186 f _40187)). Qed.
Lemma lem3682627 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) : (term1056 _93670 _93677 t _40186 f _40187) = (term1062 _93670 _93677 t _40186 f _40187).
Proof. exact (TRANS (@lem3682607 _93670 _93677 t _40186 f _40187) (@lem3682626 _93670 _93677 t _40186 f _40187)). Qed.
Lemma lem3682628 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3682629 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40186 : _93670) (f : _93670 -> _93677) (_40187 : _93670) : (term1063 _93670 _93677 t _40186 f _40187) = (term1064 _93670 _93677 t _40186 f _40187).
Proof. exact (MK_COMB (@lem3682628) (@lem3682627 _93670 _93677 t _40186 f _40187)). Qed.
Lemma lem3682630 {_93670 : Type'} (_40186 : _93670) (_40187 : _93670) : (_40186 = _40187) = (_40186 = _40187).
Proof. exact (eq_refl (_40186 = _40187)). Qed.
Lemma lem3682631 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) : (term1055 _93670 _93677 t f _40186 _40187) = (term1065 _93670 _93677 t f _40186 _40187).
Proof. exact (MK_COMB (@lem3682629 _93670 _93677 t _40186 f _40187) (@lem3682630 _93670 _40186 _40187)). Qed.
Lemma lem3682632 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40186 : _93670) (_40187 : _93670) : (term1054 _93670 _93677 t _40186 f _40187) = (term1065 _93670 _93677 t f _40186 _40187).
Proof. exact (TRANS (@lem3682604 _93670 _93677 t f _40186 _40187) (@lem3682631 _93670 _93677 t f _40186 _40187)). Qed.
Lemma lem3682634 {_93670 _93677 : Type'} (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : term1061 _93670 _93677 t x''''' f y'''''.
Proof. exact (conj (@lem3682388 _93670 _93677 t f x''''' y''''' h1) (@lem3682395 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3682635 {_93670 _93677 : Type'} (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : term1062 _93670 _93677 t x''''' f y'''''.
Proof. exact (conj (@lem3682381 _93670 _93677 t f x''''' y''''' h1) (@lem3682634 _93670 _93677 t x''''' f y''''' h1 h2)). Qed.
Lemma lem3682637 {_93670 _93677 : Type'} (_40186 : _93670) (_40187 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term1065 _93670 _93677 t f _40186 _40187.
Proof. exact (EQ_MP (@lem3682632 _93670 _93677 t f _40186 _40187) (@lem3682601 _93670 _93677 _40186 _40187 s x''''' y''''' P f t h1)). Qed.
Lemma lem3682638 {_93670 _93677 : Type'} (_40186 : _93670) (_40187 : _93670) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term1065 _93670 _93677 t f _40186 _40187.
Proof. exact (@lem3682637 _93670 _93677 _40186 _40187 s x''''' y''''' P f t h1). Qed.
Lemma lem3682639 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term1065 _93670 _93677 t f x''''' y'''''.
Proof. exact (@lem3682638 _93670 _93677 x''''' y''''' s x''''' y''''' P f t h1). Qed.
Lemma lem3682642 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') (h2 : term906 _93670 _93677 s x''''' y''''' P f t) (h3 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : x''''' = y'''''.
Proof. exact (@lem3682639 _93670 _93677 s x''''' y''''' P f t h2 (@lem3682635 _93670 _93677 t x''''' f y''''' h1 h3)). Qed.
Lemma lem3682643 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') (h2 : term906 _93670 _93677 s x''''' y''''' P f t) (h3 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : term1066 _93670 x''''' y'''''.
Proof. exact (fun h0 : term848 _93670 x''''' y''''' => @lem3682642 _93670 _93677 s P t x''''' f y''''' h1 h2 h3). Qed.
Lemma lem3682645 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3682646 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : (term1066 _93670 x''''' y''''') = (x''''' = y''''').
Proof. exact (@lem3682645 (x''''' = y''''')). Qed.
Lemma lem3682647 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') (h2 : term906 _93670 _93677 s x''''' y''''' P f t) (h3 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : x''''' = y'''''.
Proof. exact (EQ_MP (@lem3682646 _93670 x''''' y''''') (@lem3682643 _93670 _93677 s P t x''''' f y''''' h1 h2 h3)). Qed.
Lemma lem3682650 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3682652 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : (term848 _93670 x''''' y''''') = (term1067 _93670 x''''' y''''').
Proof. exact (@lem3682650 (x''''' = y''''')). Qed.
Lemma lem3682655 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') : term1067 _93670 x''''' y'''''.
Proof. exact (EQ_MP (@lem3682652 _93670 x''''' y''''') (@lem3671806 _93670 x''''' y''''' h1)). Qed.
Lemma lem3682658 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (@lem3682655 _93670 x''''' y''''' h1 (@lem3682647 _93670 _93677 s P t x''''' f y''''' h2 h3 h4)). Qed.
Lemma lem3682659 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : term971.
Proof. exact (fun h0 : ~ False => @lem3682658 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4). Qed.
Lemma lem3682661 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3682662 : term971 = False.
Proof. exact (@lem3682661 False). Qed.
Lemma lem3682663 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3682662) (@lem3682659 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4)). Qed.
Lemma lem3683224 {_93670 : Type'} (x : _93670) : x = x.
Proof. exact (@lem21386 _93670 x). Qed.
Lemma lem3683225 {_93670 : Type'} (x : _93670) : x = x.
Proof. exact (@lem3683224 _93670 x). Qed.
Lemma lem3683226 {_93670 : Type'} (y''''' : _93670) : y''''' = y'''''.
Proof. exact (@lem3683225 _93670 y'''''). Qed.
Lemma lem3683227 {_93670 : Type'} (y''''' : _93670) : term1068 _93670 y'''''.
Proof. exact (fun h0 : term965 _93670 y''''' => @lem3683226 _93670 y'''''). Qed.
Lemma lem3683229 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3683230 {_93670 : Type'} (y''''' : _93670) : (term1068 _93670 y''''') = (y''''' = y''''').
Proof. exact (@lem3683229 (y''''' = y''''')). Qed.
Lemma lem3683231 {_93670 : Type'} (y''''' : _93670) : y''''' = y'''''.
Proof. exact (EQ_MP (@lem3683230 _93670 y''''') (@lem3683227 _93670 y''''')). Qed.
Lemma lem3683234 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3683236 {_93670 : Type'} (y''''' : _93670) : (term965 _93670 y''''') = (term1069 _93670 y''''').
Proof. exact (@lem3683234 (y''''' = y''''')). Qed.
Lemma lem3683239 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : term1069 _93670 y'''''.
Proof. exact (EQ_MP (@lem3683236 _93670 y''''') (@lem3677010 _93670 x''''' y''''' h1 h2)). Qed.
Lemma lem3683242 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (@lem3683239 _93670 x''''' y''''' h1 h2 (@lem3683231 _93670 y''''')). Qed.
Lemma lem3683243 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : term971.
Proof. exact (fun h0 : ~ False => @lem3683242 _93670 x''''' y''''' h1 h2). Qed.
Lemma lem3683245 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3683246 : term971 = False.
Proof. exact (@lem3683245 False). Qed.
Lemma lem3683808 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term839 _93670 _93677 P f t.
Proof. exact (proj2 (@lem3661507 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3683809 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term1070 _93670 _93677 P f t.
Proof. exact (fun h0 : term875 _93670 _93677 P f t => @lem3683808 _93670 _93677 s x''''' y''''' P f t h1). Qed.
Lemma lem3683811 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3683812 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term1070 _93670 _93677 P f t) = (term839 _93670 _93677 P f t).
Proof. exact (@lem3683811 (term839 _93670 _93677 P f t)). Qed.
Lemma lem3683813 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) : term839 _93670 _93677 P f t.
Proof. exact (EQ_MP (@lem3683812 _93670 _93677 P f t) (@lem3683809 _93670 _93677 s x''''' y''''' P f t h1)). Qed.
Lemma lem3683816 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3683818 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term875 _93670 _93677 P f t) = (term1071 _93670 _93677 P f t).
Proof. exact (@lem3683816 (term839 _93670 _93677 P f t)). Qed.
Lemma lem3683821 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) : term1071 _93670 _93677 P f t.
Proof. exact (EQ_MP (@lem3683818 _93670 _93677 P f t) (@lem3672694 _93670 _93677 P f t h1)). Qed.
Lemma lem3683824 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (@lem3683821 _93670 _93677 P f t h1 (@lem3683813 _93670 _93677 s x''''' y''''' P f t h2)). Qed.
Lemma lem3683825 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : term971.
Proof. exact (fun h0 : ~ False => @lem3683824 _93670 _93677 s x''''' y''''' P f t h1 h2). Qed.
Lemma lem3683827 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3683828 : term971 = False.
Proof. exact (@lem3683827 False). Qed.
Lemma lem3683829 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (EQ_MP (@lem3683828) (@lem3683825 _93670 _93677 s x''''' y''''' P f t h1 h2)). Qed.
Lemma lem3684390 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term872 _93670 t s.
Proof. exact (proj1 (@lem3661529 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3684391 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term968 _93670 t s.
Proof. exact (fun h0 : term891 _93670 t s => @lem3684390 _93670 _93677 x''''' y''''' s P f t h1). Qed.
Lemma lem3684393 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3684394 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term968 _93670 t s) = (term872 _93670 t s).
Proof. exact (@lem3684393 (term872 _93670 t s)). Qed.
Lemma lem3684395 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term872 _93670 t s.
Proof. exact (EQ_MP (@lem3684394 _93670 t s) (@lem3684391 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3684398 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3684400 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) : (term891 _93670 t s) = (term970 _93670 t s).
Proof. exact (@lem3684398 (term872 _93670 t s)). Qed.
Lemma lem3684403 {_93670 : Type'} (t : _93670 -> Prop) (s : _93670 -> Prop) (h1 : term891 _93670 t s) : term970 _93670 t s.
Proof. exact (EQ_MP (@lem3684400 _93670 t s) (@lem3673134 _93670 t s h1)). Qed.
Lemma lem3684406 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (@lem3684403 _93670 t s h1 (@lem3684395 _93670 _93677 x''''' y''''' s P f t h2)). Qed.
Lemma lem3684407 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : term971.
Proof. exact (fun h0 : ~ False => @lem3684406 _93670 _93677 x''''' y''''' s P f t h1 h2). Qed.
Lemma lem3684409 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3684410 : term971 = False.
Proof. exact (@lem3684409 False). Qed.
Lemma lem3684411 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (EQ_MP (@lem3684410) (@lem3684407 _93670 _93677 x''''' y''''' s P f t h1 h2)). Qed.
Lemma lem3684972 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (h1). Qed.
Lemma lem3684973 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : term1047 _93670 _93677 x''''' f y'''''.
Proof. exact (fun h0 : term843 _93670 _93677 x''''' f y''''' => @lem3684972 _93670 _93677 x''''' f y''''' h1). Qed.
Lemma lem3684975 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3684976 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term1047 _93670 _93677 x''''' f y''''') = ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')).
Proof. exact (@lem3684975 ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y'''''))). Qed.
Lemma lem3684977 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (EQ_MP (@lem3684976 _93670 _93677 x''''' f y''''') (@lem3684973 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3684980 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3684982 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term843 _93670 _93677 x''''' f y''''') = (term1048 _93670 _93677 x''''' f y''''').
Proof. exact (@lem3684980 ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y'''''))). Qed.
Lemma lem3684985 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') : term1048 _93670 _93677 x''''' f y'''''.
Proof. exact (EQ_MP (@lem3684982 _93670 _93677 x''''' f y''''') (@lem3673578 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3684988 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (@lem3684985 _93670 _93677 x''''' f y''''' h1 (@lem3684977 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3684989 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : term971.
Proof. exact (fun h0 : ~ False => @lem3684988 _93670 _93677 x''''' f y''''' h1 h2). Qed.
Lemma lem3684991 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3684992 : term971 = False.
Proof. exact (@lem3684991 False). Qed.
Lemma lem3684993 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3684992) (@lem3684989 _93670 _93677 x''''' f y''''' h1 h2)). Qed.
Lemma lem3685554 {_93677 : Type'} (x : _93677) : x = x.
Proof. exact (@lem21386 _93677 x). Qed.
Lemma lem3685555 {_93677 : Type'} (x : _93677) : x = x.
Proof. exact (@lem3685554 _93677 x). Qed.
Lemma lem3685556 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (@I (_93670 -> _93677) f y''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (@lem3685555 _93677 (@I (_93670 -> _93677) f y''''')). Qed.
Lemma lem3685557 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : term1049 _93670 _93677 f y'''''.
Proof. exact (fun h0 : term959 _93670 _93677 f y''''' => @lem3685556 _93670 _93677 f y'''''). Qed.
Lemma lem3685559 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3685560 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (term1049 _93670 _93677 f y''''') = ((@I (_93670 -> _93677) f y''''') = (@I (_93670 -> _93677) f y''''')).
Proof. exact (@lem3685559 ((@I (_93670 -> _93677) f y''''') = (@I (_93670 -> _93677) f y'''''))). Qed.
Lemma lem3685561 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (@I (_93670 -> _93677) f y''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (EQ_MP (@lem3685560 _93670 _93677 f y''''') (@lem3685557 _93670 _93677 f y''''')). Qed.
Lemma lem3685564 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3685566 {_93670 _93677 : Type'} (f : _93670 -> _93677) (y''''' : _93670) : (term959 _93670 _93677 f y''''') = (term1050 _93670 _93677 f y''''').
Proof. exact (@lem3685564 ((@I (_93670 -> _93677) f y''''') = (@I (_93670 -> _93677) f y'''''))). Qed.
Lemma lem3685569 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : term1050 _93670 _93677 f y'''''.
Proof. exact (EQ_MP (@lem3685566 _93670 _93677 f y''''') (@lem3677694 _93670 _93677 f x''''' y''''' h1 h2)). Qed.
Lemma lem3685572 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (@lem3685569 _93670 _93677 f x''''' y''''' h1 h2 (@lem3685561 _93670 _93677 f y''''')). Qed.
Lemma lem3685573 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : term971.
Proof. exact (fun h0 : ~ False => @lem3685572 _93670 _93677 f x''''' y''''' h1 h2). Qed.
Lemma lem3685575 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3685576 : term971 = False.
Proof. exact (@lem3685575 False). Qed.
Lemma lem3686138 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term856 _93670 x''''' t.
Proof. exact (proj1 (@lem3661542 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3686139 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term1051 _93670 x''''' t.
Proof. exact (fun h0 : term858 _93670 x''''' t => @lem3686138 _93670 _93677 t f x''''' y''''' h1). Qed.
Lemma lem3686141 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3686142 {_93670 : Type'} (x''''' : _93670) (t : _93670 -> Prop) : (term1051 _93670 x''''' t) = (term856 _93670 x''''' t).
Proof. exact (@lem3686141 (term856 _93670 x''''' t)). Qed.
Lemma lem3686143 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term856 _93670 x''''' t.
Proof. exact (EQ_MP (@lem3686142 _93670 x''''' t) (@lem3686139 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3686145 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term856 _93670 y''''' t.
Proof. exact (proj2 (@lem3661542 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3686146 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term1051 _93670 y''''' t.
Proof. exact (fun h0 : term858 _93670 y''''' t => @lem3686145 _93670 _93677 t f x''''' y''''' h1). Qed.
Lemma lem3686148 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3686149 {_93670 : Type'} (y''''' : _93670) (t : _93670 -> Prop) : (term1051 _93670 y''''' t) = (term856 _93670 y''''' t).
Proof. exact (@lem3686148 (term856 _93670 y''''' t)). Qed.
Lemma lem3686150 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') : term856 _93670 y''''' t.
Proof. exact (EQ_MP (@lem3686149 _93670 y''''' t) (@lem3686146 _93670 _93677 t f x''''' y''''' h1)). Qed.
Lemma lem3686152 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (h1). Qed.
Lemma lem3686153 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : term1047 _93670 _93677 x''''' f y'''''.
Proof. exact (fun h0 : term843 _93670 _93677 x''''' f y''''' => @lem3686152 _93670 _93677 x''''' f y''''' h1). Qed.
Lemma lem3686155 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3686156 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) : (term1047 _93670 _93677 x''''' f y''''') = ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')).
Proof. exact (@lem3686155 ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y'''''))). Qed.
Lemma lem3686157 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''').
Proof. exact (EQ_MP (@lem3686156 _93670 _93677 x''''' f y''''') (@lem3686153 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3686173 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3686174 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (_40258 : _93670) (_40259 : _93670) : (term993 _93670 _93677 t f _40258 _40259) = (term994 _93670 _93677 f t _40258 _40259).
Proof. exact (@lem3686173 (term843 _93670 _93677 _40258 f _40259) (term858 _93670 _40259 t) (_40258 = _40259)). Qed.
Lemma lem3686190 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3686191 {_93670 : Type'} (_40258 : _93670) (_40259 : _93670) (t : _93670 -> Prop) : (term995 _93670 t _40258 _40259) = (term996 _93670 _40258 _40259 t).
Proof. exact (@lem3686190 (_40258 = _40259) (term858 _93670 _40259 t)). Qed.
Lemma lem3686199 {_93670 _93677 : Type'} (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) : (term845 _93670 _93677 _40258 f _40259) = (term845 _93670 _93677 _40258 f _40259).
Proof. exact (eq_refl (term845 _93670 _93677 _40258 f _40259)). Qed.
Lemma lem3686200 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) (t : _93670 -> Prop) : (term994 _93670 _93677 f t _40258 _40259) = (term997 _93670 _93677 f _40258 _40259 t).
Proof. exact (MK_COMB (@lem3686199 _93670 _93677 _40258 f _40259) (@lem3686191 _93670 _40258 _40259 t)). Qed.
Lemma lem3686204 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3686205 {_93670 _93677 : Type'} (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) (t : _93670 -> Prop) : (term997 _93670 _93677 f _40258 _40259 t) = (term998 _93670 _93677 _40258 f _40259 t).
Proof. exact (@lem3686204 (_40258 = _40259) (term843 _93670 _93677 _40258 f _40259) (term858 _93670 _40259 t)). Qed.
Lemma lem3686225 {_93670 _93677 : Type'} (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) (t : _93670 -> Prop) : (term994 _93670 _93677 f t _40258 _40259) = (term998 _93670 _93677 _40258 f _40259 t).
Proof. exact (TRANS (@lem3686200 _93670 _93677 f _40258 _40259 t) (@lem3686205 _93670 _93677 _40258 f _40259 t)). Qed.
Lemma lem3686226 {_93670 _93677 : Type'} (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) (t : _93670 -> Prop) : (term993 _93670 _93677 t f _40258 _40259) = (term998 _93670 _93677 _40258 f _40259 t).
Proof. exact (TRANS (@lem3686174 _93670 _93677 f t _40258 _40259) (@lem3686225 _93670 _93677 _40258 f _40259 t)). Qed.
Lemma lem3686227 {_93670 : Type'} (_40258 : _93670) (t : _93670 -> Prop) : (term860 _93670 _40258 t) = (term860 _93670 _40258 t).
Proof. exact (eq_refl (term860 _93670 _40258 t)). Qed.
Lemma lem3686228 {_93670 _93677 : Type'} (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) (t : _93670 -> Prop) : (term951 _93670 _93677 t f _40258 _40259) = (term999 _93670 _93677 _40258 f _40259 t).
Proof. exact (MK_COMB (@lem3686227 _93670 _40258 t) (@lem3686226 _93670 _93677 _40258 f _40259 t)). Qed.
Lemma lem3686232 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3686233 {_93670 _93677 : Type'} (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) (t : _93670 -> Prop) : (term999 _93670 _93677 _40258 f _40259 t) = (term1000 _93670 _93677 _40258 f _40259 t).
Proof. exact (@lem3686232 (_40258 = _40259) (term858 _93670 _40258 t) (term1001 _93670 _93677 _40258 f _40259 t)). Qed.
Lemma lem3686249 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3686250 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) (t : _93670 -> Prop) : (term1002 _93670 _93677 _40258 f _40259 t) = (term1003 _93670 _93677 f _40258 _40259 t).
Proof. exact (@lem3686249 (term843 _93670 _93677 _40258 f _40259) (term858 _93670 _40258 t) (term858 _93670 _40259 t)). Qed.
Lemma lem3686268 {_93670 : Type'} (_40258 : _93670) (_40259 : _93670) : (term1004 _93670 _40258 _40259) = (term1004 _93670 _40258 _40259).
Proof. exact (eq_refl (term1004 _93670 _40258 _40259)). Qed.
Lemma lem3686269 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) (t : _93670 -> Prop) : (term1000 _93670 _93677 _40258 f _40259 t) = (term1005 _93670 _93677 f _40258 _40259 t).
Proof. exact (MK_COMB (@lem3686268 _93670 _40258 _40259) (@lem3686250 _93670 _93677 f _40258 _40259 t)). Qed.
Lemma lem3686280 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) (t : _93670 -> Prop) : (term999 _93670 _93677 _40258 f _40259 t) = (term1005 _93670 _93677 f _40258 _40259 t).
Proof. exact (TRANS (@lem3686233 _93670 _93677 _40258 f _40259 t) (@lem3686269 _93670 _93677 f _40258 _40259 t)). Qed.
Lemma lem3686281 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) (t : _93670 -> Prop) : (term951 _93670 _93677 t f _40258 _40259) = (term1005 _93670 _93677 f _40258 _40259 t).
Proof. exact (TRANS (@lem3686228 _93670 _93677 _40258 f _40259 t) (@lem3686280 _93670 _93677 f _40258 _40259 t)). Qed.
Lemma lem3686282 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3686283 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) (t : _93670 -> Prop) : (term1006 _93670 _93677 t f _40258 _40259) = (term1007 _93670 _93677 f _40258 _40259 t).
Proof. exact (MK_COMB (@lem3686282) (@lem3686281 _93670 _93677 f _40258 _40259 t)). Qed.
Lemma lem3686309 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3686310 {_93670 _93677 : Type'} (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) (t : _93670 -> Prop) : (term1052 _93670 _93677 t _40258 f _40259) = (term1001 _93670 _93677 _40258 f _40259 t).
Proof. exact (@lem3686309 (term843 _93670 _93677 _40258 f _40259) (term858 _93670 _40259 t)). Qed.
Lemma lem3686318 {_93670 : Type'} (_40258 : _93670) (t : _93670 -> Prop) : (term860 _93670 _40258 t) = (term860 _93670 _40258 t).
Proof. exact (eq_refl (term860 _93670 _40258 t)). Qed.
Lemma lem3686319 {_93670 _93677 : Type'} (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) (t : _93670 -> Prop) : (term1053 _93670 _93677 t _40258 f _40259) = (term1002 _93670 _93677 _40258 f _40259 t).
Proof. exact (MK_COMB (@lem3686318 _93670 _40258 t) (@lem3686310 _93670 _93677 _40258 f _40259 t)). Qed.
Lemma lem3686323 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3686324 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) (t : _93670 -> Prop) : (term1002 _93670 _93677 _40258 f _40259 t) = (term1003 _93670 _93677 f _40258 _40259 t).
Proof. exact (@lem3686323 (term843 _93670 _93677 _40258 f _40259) (term858 _93670 _40258 t) (term858 _93670 _40259 t)). Qed.
Lemma lem3686342 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) (t : _93670 -> Prop) : (term1053 _93670 _93677 t _40258 f _40259) = (term1003 _93670 _93677 f _40258 _40259 t).
Proof. exact (TRANS (@lem3686319 _93670 _93677 _40258 f _40259 t) (@lem3686324 _93670 _93677 f _40258 _40259 t)). Qed.
Lemma lem3686343 {_93670 : Type'} (_40258 : _93670) (_40259 : _93670) : (term1004 _93670 _40258 _40259) = (term1004 _93670 _40258 _40259).
Proof. exact (eq_refl (term1004 _93670 _40258 _40259)). Qed.
Lemma lem3686344 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) (t : _93670 -> Prop) : (term1054 _93670 _93677 t _40258 f _40259) = (term1005 _93670 _93677 f _40258 _40259 t).
Proof. exact (MK_COMB (@lem3686343 _93670 _40258 _40259) (@lem3686342 _93670 _93677 f _40258 _40259 t)). Qed.
Lemma lem3686355 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) (t : _93670 -> Prop) : ((term951 _93670 _93677 t f _40258 _40259) = (term1054 _93670 _93677 t _40258 f _40259)) = ((term1005 _93670 _93677 f _40258 _40259 t) = (term1005 _93670 _93677 f _40258 _40259 t)).
Proof. exact (MK_COMB (@lem3686283 _93670 _93677 f _40258 _40259 t) (@lem3686344 _93670 _93677 f _40258 _40259 t)). Qed.
Lemma lem3686357 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3686358 (x : Prop) : (x = x) = True.
Proof. exact (@lem3686357 Prop x). Qed.
Lemma lem3686359 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) (t : _93670 -> Prop) : ((term1005 _93670 _93677 f _40258 _40259 t) = (term1005 _93670 _93677 f _40258 _40259 t)) = True.
Proof. exact (@lem3686358 (term1005 _93670 _93677 f _40258 _40259 t)). Qed.
Lemma lem3686360 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) : ((term951 _93670 _93677 t f _40258 _40259) = (term1054 _93670 _93677 t _40258 f _40259)) = True.
Proof. exact (TRANS (@lem3686355 _93670 _93677 f _40258 _40259 t) (@lem3686359 _93670 _93677 f _40258 _40259 t)). Qed.
Lemma lem3686361 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) : True = ((term951 _93670 _93677 t f _40258 _40259) = (term1054 _93670 _93677 t _40258 f _40259)).
Proof. exact (SYM (@lem3686360 _93670 _93677 t _40258 f _40259)). Qed.
Lemma lem3686362 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) : (term951 _93670 _93677 t f _40258 _40259) = (term1054 _93670 _93677 t _40258 f _40259).
Proof. exact (EQ_MP (@lem3686361 _93670 _93677 t _40258 f _40259) (@lem0)). Qed.
Lemma lem3686363 {_93670 _93677 : Type'} (_40258 : _93670) (_40259 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term1054 _93670 _93677 t _40258 f _40259.
Proof. exact (EQ_MP (@lem3686362 _93670 _93677 t _40258 f _40259) (@lem3674504 _93670 _93677 _40258 _40259 x''''' y''''' s P f t h1)). Qed.
Lemma lem3686365 (b : Prop) (a : Prop) : (a \/ b) = (term975 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3686366 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) : (term1054 _93670 _93677 t _40258 f _40259) = (term1055 _93670 _93677 t f _40258 _40259).
Proof. exact (@lem3686365 (term1053 _93670 _93677 t _40258 f _40259) (_40258 = _40259)). Qed.
Lemma lem3686368 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3686369 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) : (term1056 _93670 _93677 t _40258 f _40259) = (term1057 _93670 _93677 t _40258 f _40259).
Proof. exact (@lem3686368 (term858 _93670 _40258 t) (term1052 _93670 _93677 t _40258 f _40259)). Qed.
Lemma lem3686371 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3686372 {_93670 : Type'} (_40258 : _93670) (t : _93670 -> Prop) : (term1016 _93670 _40258 t) = (term856 _93670 _40258 t).
Proof. exact (@lem3686371 (term856 _93670 _40258 t)). Qed.
Lemma lem3686373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3686374 {_93670 : Type'} (_40258 : _93670) (t : _93670 -> Prop) : (term1017 _93670 _40258 t) = (term885 _93670 _40258 t).
Proof. exact (MK_COMB (@lem3686373) (@lem3686372 _93670 _40258 t)). Qed.
Lemma lem3686376 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3686377 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) : (term1058 _93670 _93677 t _40258 f _40259) = (term1059 _93670 _93677 t _40258 f _40259).
Proof. exact (@lem3686376 (term858 _93670 _40259 t) (term843 _93670 _93677 _40258 f _40259)). Qed.
Lemma lem3686379 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3686380 {_93670 : Type'} (_40259 : _93670) (t : _93670 -> Prop) : (term1016 _93670 _40259 t) = (term856 _93670 _40259 t).
Proof. exact (@lem3686379 (term856 _93670 _40259 t)). Qed.
Lemma lem3686381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3686382 {_93670 : Type'} (_40259 : _93670) (t : _93670 -> Prop) : (term1017 _93670 _40259 t) = (term885 _93670 _40259 t).
Proof. exact (MK_COMB (@lem3686381) (@lem3686380 _93670 _40259 t)). Qed.
Lemma lem3686384 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3686385 {_93670 _93677 : Type'} (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) : (term1060 _93670 _93677 _40258 f _40259) = ((@I (_93670 -> _93677) f _40258) = (@I (_93670 -> _93677) f _40259)).
Proof. exact (@lem3686384 ((@I (_93670 -> _93677) f _40258) = (@I (_93670 -> _93677) f _40259))). Qed.
Lemma lem3686386 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) : (term1059 _93670 _93677 t _40258 f _40259) = (term1061 _93670 _93677 t _40258 f _40259).
Proof. exact (MK_COMB (@lem3686382 _93670 _40259 t) (@lem3686385 _93670 _93677 _40258 f _40259)). Qed.
Lemma lem3686387 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) : (term1058 _93670 _93677 t _40258 f _40259) = (term1061 _93670 _93677 t _40258 f _40259).
Proof. exact (TRANS (@lem3686377 _93670 _93677 t _40258 f _40259) (@lem3686386 _93670 _93677 t _40258 f _40259)). Qed.
Lemma lem3686388 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) : (term1057 _93670 _93677 t _40258 f _40259) = (term1062 _93670 _93677 t _40258 f _40259).
Proof. exact (MK_COMB (@lem3686374 _93670 _40258 t) (@lem3686387 _93670 _93677 t _40258 f _40259)). Qed.
Lemma lem3686389 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) : (term1056 _93670 _93677 t _40258 f _40259) = (term1062 _93670 _93677 t _40258 f _40259).
Proof. exact (TRANS (@lem3686369 _93670 _93677 t _40258 f _40259) (@lem3686388 _93670 _93677 t _40258 f _40259)). Qed.
Lemma lem3686390 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3686391 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40258 : _93670) (f : _93670 -> _93677) (_40259 : _93670) : (term1063 _93670 _93677 t _40258 f _40259) = (term1064 _93670 _93677 t _40258 f _40259).
Proof. exact (MK_COMB (@lem3686390) (@lem3686389 _93670 _93677 t _40258 f _40259)). Qed.
Lemma lem3686392 {_93670 : Type'} (_40258 : _93670) (_40259 : _93670) : (_40258 = _40259) = (_40258 = _40259).
Proof. exact (eq_refl (_40258 = _40259)). Qed.
Lemma lem3686393 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) : (term1055 _93670 _93677 t f _40258 _40259) = (term1065 _93670 _93677 t f _40258 _40259).
Proof. exact (MK_COMB (@lem3686391 _93670 _93677 t _40258 f _40259) (@lem3686392 _93670 _40258 _40259)). Qed.
Lemma lem3686394 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (_40258 : _93670) (_40259 : _93670) : (term1054 _93670 _93677 t _40258 f _40259) = (term1065 _93670 _93677 t f _40258 _40259).
Proof. exact (TRANS (@lem3686366 _93670 _93677 t f _40258 _40259) (@lem3686393 _93670 _93677 t f _40258 _40259)). Qed.
Lemma lem3686396 {_93670 _93677 : Type'} (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : term1061 _93670 _93677 t x''''' f y'''''.
Proof. exact (conj (@lem3686150 _93670 _93677 t f x''''' y''''' h1) (@lem3686157 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3686397 {_93670 _93677 : Type'} (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : term1062 _93670 _93677 t x''''' f y'''''.
Proof. exact (conj (@lem3686143 _93670 _93677 t f x''''' y''''' h1) (@lem3686396 _93670 _93677 t x''''' f y''''' h1 h2)). Qed.
Lemma lem3686399 {_93670 _93677 : Type'} (_40258 : _93670) (_40259 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term1065 _93670 _93677 t f _40258 _40259.
Proof. exact (EQ_MP (@lem3686394 _93670 _93677 t f _40258 _40259) (@lem3686363 _93670 _93677 _40258 _40259 x''''' y''''' s P f t h1)). Qed.
Lemma lem3686400 {_93670 _93677 : Type'} (_40258 : _93670) (_40259 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term1065 _93670 _93677 t f _40258 _40259.
Proof. exact (@lem3686399 _93670 _93677 _40258 _40259 x''''' y''''' s P f t h1). Qed.
Lemma lem3686401 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term1065 _93670 _93677 t f x''''' y'''''.
Proof. exact (@lem3686400 _93670 _93677 x''''' y''''' x''''' y''''' s P f t h1). Qed.
Lemma lem3686404 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') (h2 : term895 _93670 _93677 x''''' y''''' s P f t) (h3 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : x''''' = y'''''.
Proof. exact (@lem3686401 _93670 _93677 x''''' y''''' s P f t h2 (@lem3686397 _93670 _93677 t x''''' f y''''' h1 h3)). Qed.
Lemma lem3686405 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') (h2 : term895 _93670 _93677 x''''' y''''' s P f t) (h3 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : term1066 _93670 x''''' y'''''.
Proof. exact (fun h0 : term848 _93670 x''''' y''''' => @lem3686404 _93670 _93677 s P t x''''' f y''''' h1 h2 h3). Qed.
Lemma lem3686407 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3686408 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : (term1066 _93670 x''''' y''''') = (x''''' = y''''').
Proof. exact (@lem3686407 (x''''' = y''''')). Qed.
Lemma lem3686409 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term888 _93670 _93677 t f x''''' y''''') (h2 : term895 _93670 _93677 x''''' y''''' s P f t) (h3 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : x''''' = y'''''.
Proof. exact (EQ_MP (@lem3686408 _93670 x''''' y''''') (@lem3686405 _93670 _93677 s P t x''''' f y''''' h1 h2 h3)). Qed.
Lemma lem3686412 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3686414 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) : (term848 _93670 x''''' y''''') = (term1067 _93670 x''''' y''''').
Proof. exact (@lem3686412 (x''''' = y''''')). Qed.
Lemma lem3686417 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') : term1067 _93670 x''''' y'''''.
Proof. exact (EQ_MP (@lem3686414 _93670 x''''' y''''') (@lem3674470 _93670 x''''' y''''' h1)). Qed.
Lemma lem3686420 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (@lem3686417 _93670 x''''' y''''' h1 (@lem3686409 _93670 _93677 s P t x''''' f y''''' h2 h3 h4)). Qed.
Lemma lem3686421 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : term971.
Proof. exact (fun h0 : ~ False => @lem3686420 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4). Qed.
Lemma lem3686423 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3686424 : term971 = False.
Proof. exact (@lem3686423 False). Qed.
Lemma lem3686425 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3686424) (@lem3686421 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4)). Qed.
Lemma lem3686986 {_93670 : Type'} (x : _93670) : x = x.
Proof. exact (@lem21386 _93670 x). Qed.
Lemma lem3686987 {_93670 : Type'} (x : _93670) : x = x.
Proof. exact (@lem3686986 _93670 x). Qed.
Lemma lem3686988 {_93670 : Type'} (y''''' : _93670) : y''''' = y'''''.
Proof. exact (@lem3686987 _93670 y'''''). Qed.
Lemma lem3686989 {_93670 : Type'} (y''''' : _93670) : term1068 _93670 y'''''.
Proof. exact (fun h0 : term965 _93670 y''''' => @lem3686988 _93670 y'''''). Qed.
Lemma lem3686991 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3686992 {_93670 : Type'} (y''''' : _93670) : (term1068 _93670 y''''') = (y''''' = y''''').
Proof. exact (@lem3686991 (y''''' = y''''')). Qed.
Lemma lem3686993 {_93670 : Type'} (y''''' : _93670) : y''''' = y'''''.
Proof. exact (EQ_MP (@lem3686992 _93670 y''''') (@lem3686989 _93670 y''''')). Qed.
Lemma lem3686996 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3686998 {_93670 : Type'} (y''''' : _93670) : (term965 _93670 y''''') = (term1069 _93670 y''''').
Proof. exact (@lem3686996 (y''''' = y''''')). Qed.
Lemma lem3687001 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : term1069 _93670 y'''''.
Proof. exact (EQ_MP (@lem3686998 _93670 y''''') (@lem3678378 _93670 x''''' y''''' h1 h2)). Qed.
Lemma lem3687004 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (@lem3687001 _93670 x''''' y''''' h1 h2 (@lem3686993 _93670 y''''')). Qed.
Lemma lem3687005 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : term971.
Proof. exact (fun h0 : ~ False => @lem3687004 _93670 x''''' y''''' h1 h2). Qed.
Lemma lem3687007 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3687008 : term971 = False.
Proof. exact (@lem3687007 False). Qed.
Lemma lem3687571 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) : term789 _93670 _93677 f t.
Proof. exact (h1). Qed.
Lemma lem3687572 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) : term1072 _93670 _93677 f t.
Proof. exact (fun h0 : term787 _93670 _93677 f t => @lem3687571 _93670 _93677 f t h1). Qed.
Lemma lem3687574 (p : Prop) : (term974 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3687575 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term1072 _93670 _93677 f t) = (term789 _93670 _93677 f t).
Proof. exact (@lem3687574 (term787 _93670 _93677 f t)). Qed.
Lemma lem3687576 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) : term789 _93670 _93677 f t.
Proof. exact (EQ_MP (@lem3687575 _93670 _93677 f t) (@lem3687572 _93670 _93677 f t h1)). Qed.
Lemma lem3687578 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : @I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t.
Proof. exact (proj1 (@lem3661531 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3687579 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term1045 _93670 t.
Proof. exact (fun h0 : term794 _93670 t => @lem3687578 _93670 _93677 x''''' y''''' s P f t h1). Qed.
Lemma lem3687581 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3687582 {_93670 : Type'} (t : _93670 -> Prop) : (term1045 _93670 t) = (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t).
Proof. exact (@lem3687581 (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t)). Qed.
Lemma lem3687583 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : @I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t.
Proof. exact (EQ_MP (@lem3687582 _93670 t) (@lem3687579 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3687585 (b : Prop) (a : Prop) : (a \/ b) = (term975 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3687586 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term954 _93670 _93677 x'''' _40280 _40281) = (term1073 _93670 _93677 x'''' _40280 _40281).
Proof. exact (@lem3687585 (term798 _93670 _93677 _40280 _40281) (term818 _93670 _93677 x'''' _40280 _40281)). Qed.
Lemma lem3687588 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3687589 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1074 _93670 _93677 _40280 _40281) = (term1075 _93670 _93677 _40280 _40281).
Proof. exact (@lem3687588 (term787 _93670 _93677 _40280 _40281) (term794 _93670 _40281)). Qed.
Lemma lem3687591 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3687592 {_93670 : Type'} (_40281 : _93670 -> Prop) : (term1076 _93670 _40281) = (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40281).
Proof. exact (@lem3687591 (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40281)). Qed.
Lemma lem3687593 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1077 _93670 _93677 _40280 _40281) = (term1077 _93670 _93677 _40280 _40281).
Proof. exact (eq_refl (term1077 _93670 _93677 _40280 _40281)). Qed.
Lemma lem3687594 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1075 _93670 _93677 _40280 _40281) = (term1078 _93670 _93677 _40280 _40281).
Proof. exact (MK_COMB (@lem3687593 _93670 _93677 _40280 _40281) (@lem3687592 _93670 _40281)). Qed.
Lemma lem3687595 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1074 _93670 _93677 _40280 _40281) = (term1078 _93670 _93677 _40280 _40281).
Proof. exact (TRANS (@lem3687589 _93670 _93677 _40280 _40281) (@lem3687594 _93670 _93677 _40280 _40281)). Qed.
Lemma lem3687596 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3687597 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1079 _93670 _93677 _40280 _40281) = (term1080 _93670 _93677 _40280 _40281).
Proof. exact (MK_COMB (@lem3687596) (@lem3687595 _93670 _93677 _40280 _40281)). Qed.
Lemma lem3687598 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term818 _93670 _93677 x'''' _40280 _40281) = (term818 _93670 _93677 x'''' _40280 _40281).
Proof. exact (eq_refl (term818 _93670 _93677 x'''' _40280 _40281)). Qed.
Lemma lem3687599 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1073 _93670 _93677 x'''' _40280 _40281) = (term1081 _93670 _93677 x'''' _40280 _40281).
Proof. exact (MK_COMB (@lem3687597 _93670 _93677 _40280 _40281) (@lem3687598 _93670 _93677 x'''' _40280 _40281)). Qed.
Lemma lem3687600 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term954 _93670 _93677 x'''' _40280 _40281) = (term1081 _93670 _93677 x'''' _40280 _40281).
Proof. exact (TRANS (@lem3687586 _93670 _93677 x'''' _40280 _40281) (@lem3687599 _93670 _93677 x'''' _40280 _40281)). Qed.
Lemma lem3687602 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : term1078 _93670 _93677 f t.
Proof. exact (conj (@lem3687576 _93670 _93677 f t h1) (@lem3687583 _93670 _93677 x''''' y''''' s P f t h2)). Qed.
Lemma lem3687604 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1081 _93670 _93677 x'''' _40280 _40281.
Proof. exact (EQ_MP (@lem3687600 _93670 _93677 x'''' _40280 _40281) (@lem3675450 _93670 _93677 _40280 _40281 x'''' y'''' h1)). Qed.
Lemma lem3687605 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1081 _93670 _93677 x'''' _40280 _40281.
Proof. exact (@lem3687604 _93670 _93677 _40280 _40281 x'''' y'''' h1). Qed.
Lemma lem3687606 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1081 _93670 _93677 x'''' f t.
Proof. exact (@lem3687605 _93670 _93677 f t x'''' y'''' h1). Qed.
Lemma lem3687609 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term818 _93670 _93677 x'''' f t.
Proof. exact (@lem3687606 _93670 _93677 f t x'''' y'''' h1 (@lem3687602 _93670 _93677 x''''' y''''' s P f t h2 h3)). Qed.
Lemma lem3687610 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term988 _93670 _93677 x'''' f t.
Proof. exact (fun h0 : term989 _93670 _93677 x'''' f t => @lem3687609 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3). Qed.
Lemma lem3687612 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3687613 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term988 _93670 _93677 x'''' f t) = (term818 _93670 _93677 x'''' f t).
Proof. exact (@lem3687612 (term818 _93670 _93677 x'''' f t)). Qed.
Lemma lem3687614 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term818 _93670 _93677 x'''' f t.
Proof. exact (EQ_MP (@lem3687613 _93670 _93677 x'''' f t) (@lem3687610 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3)). Qed.
Lemma lem3687617 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) : term789 _93670 _93677 f t.
Proof. exact (h1). Qed.
Lemma lem3687618 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) : term1072 _93670 _93677 f t.
Proof. exact (fun h0 : term787 _93670 _93677 f t => @lem3687617 _93670 _93677 f t h1). Qed.
Lemma lem3687620 (p : Prop) : (term974 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3687621 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term1072 _93670 _93677 f t) = (term789 _93670 _93677 f t).
Proof. exact (@lem3687620 (term787 _93670 _93677 f t)). Qed.
Lemma lem3687622 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) : term789 _93670 _93677 f t.
Proof. exact (EQ_MP (@lem3687621 _93670 _93677 f t) (@lem3687618 _93670 _93677 f t h1)). Qed.
Lemma lem3687624 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : @I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t.
Proof. exact (proj1 (@lem3661531 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3687625 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term1045 _93670 t.
Proof. exact (fun h0 : term794 _93670 t => @lem3687624 _93670 _93677 x''''' y''''' s P f t h1). Qed.
Lemma lem3687627 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3687628 {_93670 : Type'} (t : _93670 -> Prop) : (term1045 _93670 t) = (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t).
Proof. exact (@lem3687627 (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t)). Qed.
Lemma lem3687629 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : @I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t.
Proof. exact (EQ_MP (@lem3687628 _93670 t) (@lem3687625 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3687631 (b : Prop) (a : Prop) : (a \/ b) = (term975 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3687632 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term954 _93670 _93677 y'''' _40280 _40281) = (term1073 _93670 _93677 y'''' _40280 _40281).
Proof. exact (@lem3687631 (term798 _93670 _93677 _40280 _40281) (term818 _93670 _93677 y'''' _40280 _40281)). Qed.
Lemma lem3687634 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3687635 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1074 _93670 _93677 _40280 _40281) = (term1075 _93670 _93677 _40280 _40281).
Proof. exact (@lem3687634 (term787 _93670 _93677 _40280 _40281) (term794 _93670 _40281)). Qed.
Lemma lem3687637 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3687638 {_93670 : Type'} (_40281 : _93670 -> Prop) : (term1076 _93670 _40281) = (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40281).
Proof. exact (@lem3687637 (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40281)). Qed.
Lemma lem3687639 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1077 _93670 _93677 _40280 _40281) = (term1077 _93670 _93677 _40280 _40281).
Proof. exact (eq_refl (term1077 _93670 _93677 _40280 _40281)). Qed.
Lemma lem3687640 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1075 _93670 _93677 _40280 _40281) = (term1078 _93670 _93677 _40280 _40281).
Proof. exact (MK_COMB (@lem3687639 _93670 _93677 _40280 _40281) (@lem3687638 _93670 _40281)). Qed.
Lemma lem3687641 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1074 _93670 _93677 _40280 _40281) = (term1078 _93670 _93677 _40280 _40281).
Proof. exact (TRANS (@lem3687635 _93670 _93677 _40280 _40281) (@lem3687640 _93670 _93677 _40280 _40281)). Qed.
Lemma lem3687642 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3687643 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1079 _93670 _93677 _40280 _40281) = (term1080 _93670 _93677 _40280 _40281).
Proof. exact (MK_COMB (@lem3687642) (@lem3687641 _93670 _93677 _40280 _40281)). Qed.
Lemma lem3687644 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term818 _93670 _93677 y'''' _40280 _40281) = (term818 _93670 _93677 y'''' _40280 _40281).
Proof. exact (eq_refl (term818 _93670 _93677 y'''' _40280 _40281)). Qed.
Lemma lem3687645 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1073 _93670 _93677 y'''' _40280 _40281) = (term1081 _93670 _93677 y'''' _40280 _40281).
Proof. exact (MK_COMB (@lem3687643 _93670 _93677 _40280 _40281) (@lem3687644 _93670 _93677 y'''' _40280 _40281)). Qed.
Lemma lem3687646 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term954 _93670 _93677 y'''' _40280 _40281) = (term1081 _93670 _93677 y'''' _40280 _40281).
Proof. exact (TRANS (@lem3687632 _93670 _93677 y'''' _40280 _40281) (@lem3687645 _93670 _93677 y'''' _40280 _40281)). Qed.
Lemma lem3687648 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : term1078 _93670 _93677 f t.
Proof. exact (conj (@lem3687622 _93670 _93677 f t h1) (@lem3687629 _93670 _93677 x''''' y''''' s P f t h2)). Qed.
Lemma lem3687650 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1081 _93670 _93677 y'''' _40280 _40281.
Proof. exact (EQ_MP (@lem3687646 _93670 _93677 y'''' _40280 _40281) (@lem3675460 _93670 _93677 _40280 _40281 x'''' y'''' h1)). Qed.
Lemma lem3687651 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1081 _93670 _93677 y'''' _40280 _40281.
Proof. exact (@lem3687650 _93670 _93677 _40280 _40281 x'''' y'''' h1). Qed.
Lemma lem3687652 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1081 _93670 _93677 y'''' f t.
Proof. exact (@lem3687651 _93670 _93677 f t x'''' y'''' h1). Qed.
Lemma lem3687655 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term818 _93670 _93677 y'''' f t.
Proof. exact (@lem3687652 _93670 _93677 f t x'''' y'''' h1 (@lem3687648 _93670 _93677 x''''' y''''' s P f t h2 h3)). Qed.
Lemma lem3687656 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term988 _93670 _93677 y'''' f t.
Proof. exact (fun h0 : term989 _93670 _93677 y'''' f t => @lem3687655 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3). Qed.
Lemma lem3687658 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3687659 {_93670 _93677 : Type'} (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term988 _93670 _93677 y'''' f t) = (term818 _93670 _93677 y'''' f t).
Proof. exact (@lem3687658 (term818 _93670 _93677 y'''' f t)). Qed.
Lemma lem3687660 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term818 _93670 _93677 y'''' f t.
Proof. exact (EQ_MP (@lem3687659 _93670 _93677 y'''' f t) (@lem3687656 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3)). Qed.
Lemma lem3687663 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) : term789 _93670 _93677 f t.
Proof. exact (h1). Qed.
Lemma lem3687664 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) : term1072 _93670 _93677 f t.
Proof. exact (fun h0 : term787 _93670 _93677 f t => @lem3687663 _93670 _93677 f t h1). Qed.
Lemma lem3687666 (p : Prop) : (term974 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3687667 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term1072 _93670 _93677 f t) = (term789 _93670 _93677 f t).
Proof. exact (@lem3687666 (term787 _93670 _93677 f t)). Qed.
Lemma lem3687668 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) : term789 _93670 _93677 f t.
Proof. exact (EQ_MP (@lem3687667 _93670 _93677 f t) (@lem3687664 _93670 _93677 f t h1)). Qed.
Lemma lem3687670 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : @I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t.
Proof. exact (proj1 (@lem3661531 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3687671 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term1045 _93670 t.
Proof. exact (fun h0 : term794 _93670 t => @lem3687670 _93670 _93677 x''''' y''''' s P f t h1). Qed.
Lemma lem3687673 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3687674 {_93670 : Type'} (t : _93670 -> Prop) : (term1045 _93670 t) = (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t).
Proof. exact (@lem3687673 (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t)). Qed.
Lemma lem3687675 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : @I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t.
Proof. exact (EQ_MP (@lem3687674 _93670 t) (@lem3687671 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3687677 (b : Prop) (a : Prop) : (a \/ b) = (term975 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3687678 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term924 _93670 _93677 x'''' y'''' _40280 _40281) = (term1082 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (@lem3687677 (term798 _93670 _93677 _40280 _40281) (term806 _93670 _93677 x'''' y'''' _40280 _40281)). Qed.
Lemma lem3687680 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3687681 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1074 _93670 _93677 _40280 _40281) = (term1075 _93670 _93677 _40280 _40281).
Proof. exact (@lem3687680 (term787 _93670 _93677 _40280 _40281) (term794 _93670 _40281)). Qed.
Lemma lem3687683 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3687684 {_93670 : Type'} (_40281 : _93670 -> Prop) : (term1076 _93670 _40281) = (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40281).
Proof. exact (@lem3687683 (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40281)). Qed.
Lemma lem3687685 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1077 _93670 _93677 _40280 _40281) = (term1077 _93670 _93677 _40280 _40281).
Proof. exact (eq_refl (term1077 _93670 _93677 _40280 _40281)). Qed.
Lemma lem3687686 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1075 _93670 _93677 _40280 _40281) = (term1078 _93670 _93677 _40280 _40281).
Proof. exact (MK_COMB (@lem3687685 _93670 _93677 _40280 _40281) (@lem3687684 _93670 _40281)). Qed.
Lemma lem3687687 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1074 _93670 _93677 _40280 _40281) = (term1078 _93670 _93677 _40280 _40281).
Proof. exact (TRANS (@lem3687681 _93670 _93677 _40280 _40281) (@lem3687686 _93670 _93677 _40280 _40281)). Qed.
Lemma lem3687688 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3687689 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1079 _93670 _93677 _40280 _40281) = (term1080 _93670 _93677 _40280 _40281).
Proof. exact (MK_COMB (@lem3687688) (@lem3687687 _93670 _93677 _40280 _40281)). Qed.
Lemma lem3687690 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term806 _93670 _93677 x'''' y'''' _40280 _40281) = (term806 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (eq_refl (term806 _93670 _93677 x'''' y'''' _40280 _40281)). Qed.
Lemma lem3687691 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1082 _93670 _93677 x'''' y'''' _40280 _40281) = (term1083 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (MK_COMB (@lem3687689 _93670 _93677 _40280 _40281) (@lem3687690 _93670 _93677 x'''' y'''' _40280 _40281)). Qed.
Lemma lem3687692 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term924 _93670 _93677 x'''' y'''' _40280 _40281) = (term1083 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (TRANS (@lem3687678 _93670 _93677 x'''' y'''' _40280 _40281) (@lem3687691 _93670 _93677 x'''' y'''' _40280 _40281)). Qed.
Lemma lem3687694 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : term1078 _93670 _93677 f t.
Proof. exact (conj (@lem3687668 _93670 _93677 f t h1) (@lem3687675 _93670 _93677 x''''' y''''' s P f t h2)). Qed.
Lemma lem3687696 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1083 _93670 _93677 x'''' y'''' _40280 _40281.
Proof. exact (EQ_MP (@lem3687692 _93670 _93677 x'''' y'''' _40280 _40281) (@lem3675440 _93670 _93677 _40280 _40281 x'''' y'''' h1)). Qed.
Lemma lem3687697 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1083 _93670 _93677 x'''' y'''' _40280 _40281.
Proof. exact (@lem3687696 _93670 _93677 _40280 _40281 x'''' y'''' h1). Qed.
Lemma lem3687698 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1083 _93670 _93677 x'''' y'''' f t.
Proof. exact (@lem3687697 _93670 _93677 f t x'''' y'''' h1). Qed.
Lemma lem3687701 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term806 _93670 _93677 x'''' y'''' f t.
Proof. exact (@lem3687698 _93670 _93677 f t x'''' y'''' h1 (@lem3687694 _93670 _93677 x''''' y''''' s P f t h2 h3)). Qed.
Lemma lem3687702 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term992 _93670 _93677 x'''' y'''' f t.
Proof. exact (fun h0 : (term802 _93670 _93677 x'''' f t) = (term802 _93670 _93677 y'''' f t) => @lem3687701 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3). Qed.
Lemma lem3687704 (p : Prop) : (term974 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3687705 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term992 _93670 _93677 x'''' y'''' f t) = (term806 _93670 _93677 x'''' y'''' f t).
Proof. exact (@lem3687704 ((term802 _93670 _93677 x'''' f t) = (term802 _93670 _93677 y'''' f t))). Qed.
Lemma lem3687706 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term806 _93670 _93677 x'''' y'''' f t.
Proof. exact (EQ_MP (@lem3687705 _93670 _93677 x'''' y'''' f t) (@lem3687702 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3)). Qed.
Lemma lem3687722 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3687723 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (_40282 : _93670) (_40283 : _93670) : (term993 _93670 _93677 t f _40282 _40283) = (term994 _93670 _93677 f t _40282 _40283).
Proof. exact (@lem3687722 (term843 _93670 _93677 _40282 f _40283) (term858 _93670 _40283 t) (_40282 = _40283)). Qed.
Lemma lem3687739 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3687740 {_93670 : Type'} (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : (term995 _93670 t _40282 _40283) = (term996 _93670 _40282 _40283 t).
Proof. exact (@lem3687739 (_40282 = _40283) (term858 _93670 _40283 t)). Qed.
Lemma lem3687748 {_93670 _93677 : Type'} (_40282 : _93670) (f : _93670 -> _93677) (_40283 : _93670) : (term845 _93670 _93677 _40282 f _40283) = (term845 _93670 _93677 _40282 f _40283).
Proof. exact (eq_refl (term845 _93670 _93677 _40282 f _40283)). Qed.
Lemma lem3687749 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : (term994 _93670 _93677 f t _40282 _40283) = (term997 _93670 _93677 f _40282 _40283 t).
Proof. exact (MK_COMB (@lem3687748 _93670 _93677 _40282 f _40283) (@lem3687740 _93670 _40282 _40283 t)). Qed.
Lemma lem3687753 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3687754 {_93670 _93677 : Type'} (_40282 : _93670) (f : _93670 -> _93677) (_40283 : _93670) (t : _93670 -> Prop) : (term997 _93670 _93677 f _40282 _40283 t) = (term998 _93670 _93677 _40282 f _40283 t).
Proof. exact (@lem3687753 (_40282 = _40283) (term843 _93670 _93677 _40282 f _40283) (term858 _93670 _40283 t)). Qed.
Lemma lem3687774 {_93670 _93677 : Type'} (_40282 : _93670) (f : _93670 -> _93677) (_40283 : _93670) (t : _93670 -> Prop) : (term994 _93670 _93677 f t _40282 _40283) = (term998 _93670 _93677 _40282 f _40283 t).
Proof. exact (TRANS (@lem3687749 _93670 _93677 f _40282 _40283 t) (@lem3687754 _93670 _93677 _40282 f _40283 t)). Qed.
Lemma lem3687775 {_93670 _93677 : Type'} (_40282 : _93670) (f : _93670 -> _93677) (_40283 : _93670) (t : _93670 -> Prop) : (term993 _93670 _93677 t f _40282 _40283) = (term998 _93670 _93677 _40282 f _40283 t).
Proof. exact (TRANS (@lem3687723 _93670 _93677 f t _40282 _40283) (@lem3687774 _93670 _93677 _40282 f _40283 t)). Qed.
Lemma lem3687776 {_93670 : Type'} (_40282 : _93670) (t : _93670 -> Prop) : (term860 _93670 _40282 t) = (term860 _93670 _40282 t).
Proof. exact (eq_refl (term860 _93670 _40282 t)). Qed.
Lemma lem3687777 {_93670 _93677 : Type'} (_40282 : _93670) (f : _93670 -> _93677) (_40283 : _93670) (t : _93670 -> Prop) : (term951 _93670 _93677 t f _40282 _40283) = (term999 _93670 _93677 _40282 f _40283 t).
Proof. exact (MK_COMB (@lem3687776 _93670 _40282 t) (@lem3687775 _93670 _93677 _40282 f _40283 t)). Qed.
Lemma lem3687781 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3687782 {_93670 _93677 : Type'} (_40282 : _93670) (f : _93670 -> _93677) (_40283 : _93670) (t : _93670 -> Prop) : (term999 _93670 _93677 _40282 f _40283 t) = (term1000 _93670 _93677 _40282 f _40283 t).
Proof. exact (@lem3687781 (_40282 = _40283) (term858 _93670 _40282 t) (term1001 _93670 _93677 _40282 f _40283 t)). Qed.
Lemma lem3687798 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3687799 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : (term1002 _93670 _93677 _40282 f _40283 t) = (term1003 _93670 _93677 f _40282 _40283 t).
Proof. exact (@lem3687798 (term843 _93670 _93677 _40282 f _40283) (term858 _93670 _40282 t) (term858 _93670 _40283 t)). Qed.
Lemma lem3687817 {_93670 : Type'} (_40282 : _93670) (_40283 : _93670) : (term1004 _93670 _40282 _40283) = (term1004 _93670 _40282 _40283).
Proof. exact (eq_refl (term1004 _93670 _40282 _40283)). Qed.
Lemma lem3687818 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : (term1000 _93670 _93677 _40282 f _40283 t) = (term1005 _93670 _93677 f _40282 _40283 t).
Proof. exact (MK_COMB (@lem3687817 _93670 _40282 _40283) (@lem3687799 _93670 _93677 f _40282 _40283 t)). Qed.
Lemma lem3687829 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : (term999 _93670 _93677 _40282 f _40283 t) = (term1005 _93670 _93677 f _40282 _40283 t).
Proof. exact (TRANS (@lem3687782 _93670 _93677 _40282 f _40283 t) (@lem3687818 _93670 _93677 f _40282 _40283 t)). Qed.
Lemma lem3687830 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : (term951 _93670 _93677 t f _40282 _40283) = (term1005 _93670 _93677 f _40282 _40283 t).
Proof. exact (TRANS (@lem3687777 _93670 _93677 _40282 f _40283 t) (@lem3687829 _93670 _93677 f _40282 _40283 t)). Qed.
Lemma lem3687831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3687832 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : (term1006 _93670 _93677 t f _40282 _40283) = (term1007 _93670 _93677 f _40282 _40283 t).
Proof. exact (MK_COMB (@lem3687831) (@lem3687830 _93670 _93677 f _40282 _40283 t)). Qed.
Lemma lem3687858 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3687859 {_93670 : Type'} (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : (term995 _93670 t _40282 _40283) = (term996 _93670 _40282 _40283 t).
Proof. exact (@lem3687858 (_40282 = _40283) (term858 _93670 _40283 t)). Qed.
Lemma lem3687867 {_93670 : Type'} (_40282 : _93670) (t : _93670 -> Prop) : (term860 _93670 _40282 t) = (term860 _93670 _40282 t).
Proof. exact (eq_refl (term860 _93670 _40282 t)). Qed.
Lemma lem3687868 {_93670 : Type'} (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : (term1008 _93670 t _40282 _40283) = (term1009 _93670 _40282 _40283 t).
Proof. exact (MK_COMB (@lem3687867 _93670 _40282 t) (@lem3687859 _93670 _40282 _40283 t)). Qed.
Lemma lem3687872 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3687873 {_93670 : Type'} (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : (term1009 _93670 _40282 _40283 t) = (term1010 _93670 _40282 _40283 t).
Proof. exact (@lem3687872 (_40282 = _40283) (term858 _93670 _40282 t) (term858 _93670 _40283 t)). Qed.
Lemma lem3687891 {_93670 : Type'} (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : (term1008 _93670 t _40282 _40283) = (term1010 _93670 _40282 _40283 t).
Proof. exact (TRANS (@lem3687868 _93670 _40282 _40283 t) (@lem3687873 _93670 _40282 _40283 t)). Qed.
Lemma lem3687892 {_93670 _93677 : Type'} (_40282 : _93670) (f : _93670 -> _93677) (_40283 : _93670) : (term845 _93670 _93677 _40282 f _40283) = (term845 _93670 _93677 _40282 f _40283).
Proof. exact (eq_refl (term845 _93670 _93677 _40282 f _40283)). Qed.
Lemma lem3687893 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : (term1011 _93670 _93677 f t _40282 _40283) = (term1012 _93670 _93677 f _40282 _40283 t).
Proof. exact (MK_COMB (@lem3687892 _93670 _93677 _40282 f _40283) (@lem3687891 _93670 _40282 _40283 t)). Qed.
Lemma lem3687897 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3687898 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : (term1012 _93670 _93677 f _40282 _40283 t) = (term1005 _93670 _93677 f _40282 _40283 t).
Proof. exact (@lem3687897 (_40282 = _40283) (term843 _93670 _93677 _40282 f _40283) (term861 _93670 _40282 _40283 t)). Qed.
Lemma lem3687928 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : (term1011 _93670 _93677 f t _40282 _40283) = (term1005 _93670 _93677 f _40282 _40283 t).
Proof. exact (TRANS (@lem3687893 _93670 _93677 f _40282 _40283 t) (@lem3687898 _93670 _93677 f _40282 _40283 t)). Qed.
Lemma lem3687929 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : ((term951 _93670 _93677 t f _40282 _40283) = (term1011 _93670 _93677 f t _40282 _40283)) = ((term1005 _93670 _93677 f _40282 _40283 t) = (term1005 _93670 _93677 f _40282 _40283 t)).
Proof. exact (MK_COMB (@lem3687832 _93670 _93677 f _40282 _40283 t) (@lem3687928 _93670 _93677 f _40282 _40283 t)). Qed.
Lemma lem3687931 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3687932 (x : Prop) : (x = x) = True.
Proof. exact (@lem3687931 Prop x). Qed.
Lemma lem3687933 {_93670 _93677 : Type'} (f : _93670 -> _93677) (_40282 : _93670) (_40283 : _93670) (t : _93670 -> Prop) : ((term1005 _93670 _93677 f _40282 _40283 t) = (term1005 _93670 _93677 f _40282 _40283 t)) = True.
Proof. exact (@lem3687932 (term1005 _93670 _93677 f _40282 _40283 t)). Qed.
Lemma lem3687934 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (_40282 : _93670) (_40283 : _93670) : ((term951 _93670 _93677 t f _40282 _40283) = (term1011 _93670 _93677 f t _40282 _40283)) = True.
Proof. exact (TRANS (@lem3687929 _93670 _93677 f _40282 _40283 t) (@lem3687933 _93670 _93677 f _40282 _40283 t)). Qed.
Lemma lem3687935 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (_40282 : _93670) (_40283 : _93670) : True = ((term951 _93670 _93677 t f _40282 _40283) = (term1011 _93670 _93677 f t _40282 _40283)).
Proof. exact (SYM (@lem3687934 _93670 _93677 f t _40282 _40283)). Qed.
Lemma lem3687936 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (_40282 : _93670) (_40283 : _93670) : (term951 _93670 _93677 t f _40282 _40283) = (term1011 _93670 _93677 f t _40282 _40283).
Proof. exact (EQ_MP (@lem3687935 _93670 _93677 f t _40282 _40283) (@lem0)). Qed.
Lemma lem3687937 {_93670 _93677 : Type'} (_40282 : _93670) (_40283 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term1011 _93670 _93677 f t _40282 _40283.
Proof. exact (EQ_MP (@lem3687936 _93670 _93677 f t _40282 _40283) (@lem3675390 _93670 _93677 _40282 _40283 x''''' y''''' s P f t h1)). Qed.
Lemma lem3687939 (b : Prop) (a : Prop) : (a \/ b) = (term975 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3687940 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40282 : _93670) (f : _93670 -> _93677) (_40283 : _93670) : (term1011 _93670 _93677 f t _40282 _40283) = (term1013 _93670 _93677 t _40282 f _40283).
Proof. exact (@lem3687939 (term1008 _93670 t _40282 _40283) (term843 _93670 _93677 _40282 f _40283)). Qed.
Lemma lem3687942 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3687943 {_93670 : Type'} (t : _93670 -> Prop) (_40282 : _93670) (_40283 : _93670) : (term1014 _93670 t _40282 _40283) = (term1015 _93670 t _40282 _40283).
Proof. exact (@lem3687942 (term858 _93670 _40282 t) (term995 _93670 t _40282 _40283)). Qed.
Lemma lem3687945 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3687946 {_93670 : Type'} (_40282 : _93670) (t : _93670 -> Prop) : (term1016 _93670 _40282 t) = (term856 _93670 _40282 t).
Proof. exact (@lem3687945 (term856 _93670 _40282 t)). Qed.
Lemma lem3687947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3687948 {_93670 : Type'} (_40282 : _93670) (t : _93670 -> Prop) : (term1017 _93670 _40282 t) = (term885 _93670 _40282 t).
Proof. exact (MK_COMB (@lem3687947) (@lem3687946 _93670 _40282 t)). Qed.
Lemma lem3687950 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3687951 {_93670 : Type'} (t : _93670 -> Prop) (_40282 : _93670) (_40283 : _93670) : (term1018 _93670 t _40282 _40283) = (term1019 _93670 t _40282 _40283).
Proof. exact (@lem3687950 (term858 _93670 _40283 t) (_40282 = _40283)). Qed.
Lemma lem3687953 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3687954 {_93670 : Type'} (_40283 : _93670) (t : _93670 -> Prop) : (term1016 _93670 _40283 t) = (term856 _93670 _40283 t).
Proof. exact (@lem3687953 (term856 _93670 _40283 t)). Qed.
Lemma lem3687955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3687956 {_93670 : Type'} (_40283 : _93670) (t : _93670 -> Prop) : (term1017 _93670 _40283 t) = (term885 _93670 _40283 t).
Proof. exact (MK_COMB (@lem3687955) (@lem3687954 _93670 _40283 t)). Qed.
Lemma lem3687957 {_93670 : Type'} (_40282 : _93670) (_40283 : _93670) : (term848 _93670 _40282 _40283) = (term848 _93670 _40282 _40283).
Proof. exact (eq_refl (term848 _93670 _40282 _40283)). Qed.
Lemma lem3687958 {_93670 : Type'} (t : _93670 -> Prop) (_40282 : _93670) (_40283 : _93670) : (term1019 _93670 t _40282 _40283) = (term1020 _93670 t _40282 _40283).
Proof. exact (MK_COMB (@lem3687956 _93670 _40283 t) (@lem3687957 _93670 _40282 _40283)). Qed.
Lemma lem3687959 {_93670 : Type'} (t : _93670 -> Prop) (_40282 : _93670) (_40283 : _93670) : (term1018 _93670 t _40282 _40283) = (term1020 _93670 t _40282 _40283).
Proof. exact (TRANS (@lem3687951 _93670 t _40282 _40283) (@lem3687958 _93670 t _40282 _40283)). Qed.
Lemma lem3687960 {_93670 : Type'} (t : _93670 -> Prop) (_40282 : _93670) (_40283 : _93670) : (term1015 _93670 t _40282 _40283) = (term1021 _93670 t _40282 _40283).
Proof. exact (MK_COMB (@lem3687948 _93670 _40282 t) (@lem3687959 _93670 t _40282 _40283)). Qed.
Lemma lem3687961 {_93670 : Type'} (t : _93670 -> Prop) (_40282 : _93670) (_40283 : _93670) : (term1014 _93670 t _40282 _40283) = (term1021 _93670 t _40282 _40283).
Proof. exact (TRANS (@lem3687943 _93670 t _40282 _40283) (@lem3687960 _93670 t _40282 _40283)). Qed.
Lemma lem3687962 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3687963 {_93670 : Type'} (t : _93670 -> Prop) (_40282 : _93670) (_40283 : _93670) : (term1022 _93670 t _40282 _40283) = (term1023 _93670 t _40282 _40283).
Proof. exact (MK_COMB (@lem3687962) (@lem3687961 _93670 t _40282 _40283)). Qed.
Lemma lem3687964 {_93670 _93677 : Type'} (_40282 : _93670) (f : _93670 -> _93677) (_40283 : _93670) : (term843 _93670 _93677 _40282 f _40283) = (term843 _93670 _93677 _40282 f _40283).
Proof. exact (eq_refl (term843 _93670 _93677 _40282 f _40283)). Qed.
Lemma lem3687965 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40282 : _93670) (f : _93670 -> _93677) (_40283 : _93670) : (term1013 _93670 _93677 t _40282 f _40283) = (term1024 _93670 _93677 t _40282 f _40283).
Proof. exact (MK_COMB (@lem3687963 _93670 t _40282 _40283) (@lem3687964 _93670 _93677 _40282 f _40283)). Qed.
Lemma lem3687966 {_93670 _93677 : Type'} (t : _93670 -> Prop) (_40282 : _93670) (f : _93670 -> _93677) (_40283 : _93670) : (term1011 _93670 _93677 f t _40282 _40283) = (term1024 _93670 _93677 t _40282 f _40283).
Proof. exact (TRANS (@lem3687940 _93670 _93677 t _40282 f _40283) (@lem3687965 _93670 _93677 t _40282 f _40283)). Qed.
Lemma lem3687968 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term1025 _93670 _93677 x'''' y'''' f t.
Proof. exact (conj (@lem3687660 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3) (@lem3687706 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3)). Qed.
Lemma lem3687969 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term1026 _93670 _93677 x'''' y'''' f t.
Proof. exact (conj (@lem3687614 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3) (@lem3687968 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3)). Qed.
Lemma lem3687971 {_93670 _93677 : Type'} (_40282 : _93670) (_40283 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term1024 _93670 _93677 t _40282 f _40283.
Proof. exact (EQ_MP (@lem3687966 _93670 _93677 t _40282 f _40283) (@lem3687937 _93670 _93677 _40282 _40283 x''''' y''''' s P f t h1)). Qed.
Lemma lem3687972 {_93670 _93677 : Type'} (_40282 : _93670) (_40283 : _93670) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term1024 _93670 _93677 t _40282 f _40283.
Proof. exact (@lem3687971 _93670 _93677 _40282 _40283 x''''' y''''' s P f t h1). Qed.
Lemma lem3687973 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term1027 _93670 _93677 x'''' y'''' f t.
Proof. exact (@lem3687972 _93670 _93677 (term802 _93670 _93677 x'''' f t) (term802 _93670 _93677 y'''' f t) x''''' y''''' s P f t h1). Qed.
Lemma lem3687976 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term1028 _93670 _93677 x'''' y'''' f t.
Proof. exact (@lem3687973 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h3 (@lem3687969 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3)). Qed.
Lemma lem3687977 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term1029 _93670 _93677 x'''' y'''' f t.
Proof. exact (fun h0 : (term809 _93670 _93677 x'''' f t) = (term809 _93670 _93677 y'''' f t) => @lem3687976 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3). Qed.
Lemma lem3687979 (p : Prop) : (term974 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3687980 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term1029 _93670 _93677 x'''' y'''' f t) = (term1028 _93670 _93677 x'''' y'''' f t).
Proof. exact (@lem3687979 ((term809 _93670 _93677 x'''' f t) = (term809 _93670 _93677 y'''' f t))). Qed.
Lemma lem3687981 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term1028 _93670 _93677 x'''' y'''' f t.
Proof. exact (EQ_MP (@lem3687980 _93670 _93677 x'''' y'''' f t) (@lem3687977 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3)). Qed.
Lemma lem3687983 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : @I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t.
Proof. exact (proj1 (@lem3661531 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3687984 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term1045 _93670 t.
Proof. exact (fun h0 : term794 _93670 t => @lem3687983 _93670 _93677 x''''' y''''' s P f t h1). Qed.
Lemma lem3687986 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3687987 {_93670 : Type'} (t : _93670 -> Prop) : (term1045 _93670 t) = (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t).
Proof. exact (@lem3687986 (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t)). Qed.
Lemma lem3687988 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : @I ((_93670 -> Prop) -> Prop) (@FINITE _93670) t.
Proof. exact (EQ_MP (@lem3687987 _93670 t) (@lem3687984 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3688011 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3688012 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1084 _93670 _93677 x'''' y'''' _40280 _40281) = (term955 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (@lem3688011 ((term809 _93670 _93677 x'''' _40280 _40281) = (term809 _93670 _93677 y'''' _40280 _40281)) (term787 _93670 _93677 _40280 _40281) (term794 _93670 _40281)). Qed.
Lemma lem3688030 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1085 _93670 _93677 x'''' y'''' _40280 _40281) = (term1085 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (eq_refl (term1085 _93670 _93677 x'''' y'''' _40280 _40281)). Qed.
Lemma lem3688031 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : ((term955 _93670 _93677 x'''' y'''' _40280 _40281) = (term1084 _93670 _93677 x'''' y'''' _40280 _40281)) = ((term955 _93670 _93677 x'''' y'''' _40280 _40281) = (term955 _93670 _93677 x'''' y'''' _40280 _40281)).
Proof. exact (MK_COMB (@lem3688030 _93670 _93677 x'''' y'''' _40280 _40281) (@lem3688012 _93670 _93677 x'''' y'''' _40280 _40281)). Qed.
Lemma lem3688033 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3688034 (x : Prop) : (x = x) = True.
Proof. exact (@lem3688033 Prop x). Qed.
Lemma lem3688035 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : ((term955 _93670 _93677 x'''' y'''' _40280 _40281) = (term955 _93670 _93677 x'''' y'''' _40280 _40281)) = True.
Proof. exact (@lem3688034 (term955 _93670 _93677 x'''' y'''' _40280 _40281)). Qed.
Lemma lem3688036 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : ((term955 _93670 _93677 x'''' y'''' _40280 _40281) = (term1084 _93670 _93677 x'''' y'''' _40280 _40281)) = True.
Proof. exact (TRANS (@lem3688031 _93670 _93677 x'''' y'''' _40280 _40281) (@lem3688035 _93670 _93677 x'''' y'''' _40280 _40281)). Qed.
Lemma lem3688037 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : True = ((term955 _93670 _93677 x'''' y'''' _40280 _40281) = (term1084 _93670 _93677 x'''' y'''' _40280 _40281)).
Proof. exact (SYM (@lem3688036 _93670 _93677 x'''' y'''' _40280 _40281)). Qed.
Lemma lem3688038 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term955 _93670 _93677 x'''' y'''' _40280 _40281) = (term1084 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (EQ_MP (@lem3688037 _93670 _93677 x'''' y'''' _40280 _40281) (@lem0)). Qed.
Lemma lem3688039 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1084 _93670 _93677 x'''' y'''' _40280 _40281.
Proof. exact (EQ_MP (@lem3688038 _93670 _93677 x'''' y'''' _40280 _40281) (@lem3675470 _93670 _93677 _40280 _40281 x'''' y'''' h1)). Qed.
Lemma lem3688041 (b : Prop) (a : Prop) : (a \/ b) = (term975 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3688042 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1084 _93670 _93677 x'''' y'''' _40280 _40281) = (term1086 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (@lem3688041 (term1087 _93670 _93677 x'''' y'''' _40280 _40281) (term787 _93670 _93677 _40280 _40281)). Qed.
Lemma lem3688044 (a : Prop) (b : Prop) : (term977 a b) = (term978 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3688045 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1088 _93670 _93677 x'''' y'''' _40280 _40281) = (term1089 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (@lem3688044 ((term809 _93670 _93677 x'''' _40280 _40281) = (term809 _93670 _93677 y'''' _40280 _40281)) (term794 _93670 _40281)). Qed.
Lemma lem3688047 (a : Prop) : (term981 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3688048 {_93670 : Type'} (_40281 : _93670 -> Prop) : (term1076 _93670 _40281) = (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40281).
Proof. exact (@lem3688047 (@I ((_93670 -> Prop) -> Prop) (@FINITE _93670) _40281)). Qed.
Lemma lem3688049 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1040 _93670 _93677 x'''' y'''' _40280 _40281) = (term1040 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (eq_refl (term1040 _93670 _93677 x'''' y'''' _40280 _40281)). Qed.
Lemma lem3688050 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1089 _93670 _93677 x'''' y'''' _40280 _40281) = (term1090 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (MK_COMB (@lem3688049 _93670 _93677 x'''' y'''' _40280 _40281) (@lem3688048 _93670 _40281)). Qed.
Lemma lem3688051 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1088 _93670 _93677 x'''' y'''' _40280 _40281) = (term1090 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (TRANS (@lem3688045 _93670 _93677 x'''' y'''' _40280 _40281) (@lem3688050 _93670 _93677 x'''' y'''' _40280 _40281)). Qed.
Lemma lem3688052 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3688053 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1091 _93670 _93677 x'''' y'''' _40280 _40281) = (term1092 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (MK_COMB (@lem3688052) (@lem3688051 _93670 _93677 x'''' y'''' _40280 _40281)). Qed.
Lemma lem3688054 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term787 _93670 _93677 _40280 _40281) = (term787 _93670 _93677 _40280 _40281).
Proof. exact (eq_refl (term787 _93670 _93677 _40280 _40281)). Qed.
Lemma lem3688055 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1086 _93670 _93677 x'''' y'''' _40280 _40281) = (term1093 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (MK_COMB (@lem3688053 _93670 _93677 x'''' y'''' _40280 _40281) (@lem3688054 _93670 _93677 _40280 _40281)). Qed.
Lemma lem3688056 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) : (term1084 _93670 _93677 x'''' y'''' _40280 _40281) = (term1093 _93670 _93677 x'''' y'''' _40280 _40281).
Proof. exact (TRANS (@lem3688042 _93670 _93677 x'''' y'''' _40280 _40281) (@lem3688055 _93670 _93677 x'''' y'''' _40280 _40281)). Qed.
Lemma lem3688058 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term1090 _93670 _93677 x'''' y'''' f t.
Proof. exact (conj (@lem3687981 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3) (@lem3687988 _93670 _93677 x''''' y''''' s P f t h3)). Qed.
Lemma lem3688060 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1093 _93670 _93677 x'''' y'''' _40280 _40281.
Proof. exact (EQ_MP (@lem3688056 _93670 _93677 x'''' y'''' _40280 _40281) (@lem3688039 _93670 _93677 _40280 _40281 x'''' y'''' h1)). Qed.
Lemma lem3688061 {_93670 _93677 : Type'} (_40280 : _93670 -> _93677) (_40281 : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1093 _93670 _93677 x'''' y'''' _40280 _40281.
Proof. exact (@lem3688060 _93670 _93677 _40280 _40281 x'''' y'''' h1). Qed.
Lemma lem3688062 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (h1 : term623 _93670 _93677 x'''' y'''') : term1093 _93670 _93677 x'''' y'''' f t.
Proof. exact (@lem3688061 _93670 _93677 f t x'''' y'''' h1). Qed.
Lemma lem3688065 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term787 _93670 _93677 f t.
Proof. exact (@lem3688062 _93670 _93677 f t x'''' y'''' h1 (@lem3688058 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3)). Qed.
Lemma lem3688066 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : term972 _93670 _93677 f t.
Proof. exact (fun h0 : term789 _93670 _93677 f t => @lem3688065 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h0 h2). Qed.
Lemma lem3688068 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3688069 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term972 _93670 _93677 f t) = (term787 _93670 _93677 f t).
Proof. exact (@lem3688068 (term787 _93670 _93677 f t)). Qed.
Lemma lem3688070 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : term787 _93670 _93677 f t.
Proof. exact (EQ_MP (@lem3688069 _93670 _93677 f t) (@lem3688066 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2)). Qed.
Lemma lem3688073 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3688075 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term789 _93670 _93677 f t) = (term1094 _93670 _93677 f t).
Proof. exact (@lem3688073 (term787 _93670 _93677 f t)). Qed.
Lemma lem3688078 {_93670 _93677 : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term789 _93670 _93677 f t) : term1094 _93670 _93677 f t.
Proof. exact (EQ_MP (@lem3688075 _93670 _93677 f t) (@lem3675358 _93670 _93677 f t h1)). Qed.
Lemma lem3688081 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (@lem3688078 _93670 _93677 f t h2 (@lem3688070 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h3)). Qed.
Lemma lem3688082 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : term971.
Proof. exact (fun h0 : ~ False => @lem3688081 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3). Qed.
Lemma lem3688084 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3688085 : term971 = False.
Proof. exact (@lem3688084 False). Qed.
Lemma lem3688086 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (EQ_MP (@lem3688085) (@lem3688082 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3)). Qed.
Lemma lem3688647 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term839 _93670 _93677 P f t.
Proof. exact (proj2 (@lem3661533 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3688648 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term1070 _93670 _93677 P f t.
Proof. exact (fun h0 : term875 _93670 _93677 P f t => @lem3688647 _93670 _93677 x''''' y''''' s P f t h1). Qed.
Lemma lem3688650 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3688651 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term1070 _93670 _93677 P f t) = (term839 _93670 _93677 P f t).
Proof. exact (@lem3688650 (term839 _93670 _93677 P f t)). Qed.
Lemma lem3688652 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term895 _93670 _93677 x''''' y''''' s P f t) : term839 _93670 _93677 P f t.
Proof. exact (EQ_MP (@lem3688651 _93670 _93677 P f t) (@lem3688648 _93670 _93677 x''''' y''''' s P f t h1)). Qed.
Lemma lem3688655 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3688657 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term875 _93670 _93677 P f t) = (term1071 _93670 _93677 P f t).
Proof. exact (@lem3688655 (term839 _93670 _93677 P f t)). Qed.
Lemma lem3688660 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) : term1071 _93670 _93677 P f t.
Proof. exact (EQ_MP (@lem3688657 _93670 _93677 P f t) (@lem3675798 _93670 _93677 P f t h1)). Qed.
Lemma lem3688663 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (@lem3688660 _93670 _93677 P f t h1 (@lem3688652 _93670 _93677 x''''' y''''' s P f t h2)). Qed.
Lemma lem3688664 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : term971.
Proof. exact (fun h0 : ~ False => @lem3688663 _93670 _93677 x''''' y''''' s P f t h1 h2). Qed.
Lemma lem3688666 (p : Prop) : (term969 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3688667 : term971 = False.
Proof. exact (@lem3688666 False). Qed.
Lemma lem3688668 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (EQ_MP (@lem3688667) (@lem3688664 _93670 _93677 x''''' y''''' s P f t h1 h2)). Qed.
Lemma lem3688669 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3687008) (@lem3687005 _93670 x''''' y''''' h1 h2)). Qed.
Lemma lem3688670 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3685576) (@lem3685573 _93670 _93677 f x''''' y''''' h1 h2)). Qed.
Lemma lem3688671 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3683246) (@lem3683243 _93670 x''''' y''''' h1 h2)). Qed.
Lemma lem3688672 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3681814) (@lem3681811 _93670 _93677 f x''''' y''''' h1 h2)). Qed.
Lemma lem3688673 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : (term875 _93670 _93677 P f t) = False.
Proof. exact (prop_ext (fun h3 : term875 _93670 _93677 P f t => @lem3688668 _93670 _93677 x''''' y''''' s P f t h1 h2) (fun h3 : False => @lem3675798 _93670 _93677 P f t h1)). Qed.
Lemma lem3688674 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (EQ_MP (@lem3688673 _93670 _93677 x''''' y''''' s P f t h1 h2) (@lem3675798 _93670 _93677 P f t h1)). Qed.
Lemma lem3688675 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : (term789 _93670 _93677 f t) = False.
Proof. exact (prop_ext (fun h4 : term789 _93670 _93677 f t => @lem3688086 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3) (fun h4 : False => @lem3675358 _93670 _93677 f t h2)). Qed.
Lemma lem3688676 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (EQ_MP (@lem3688675 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3) (@lem3675358 _93670 _93677 f t h2)). Qed.
Lemma lem3688677 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : (x''''' = y''''') = False.
Proof. exact (prop_ext (fun h3 : x''''' = y''''' => @lem3688669 _93670 x''''' y''''' h1 h2) (fun h3 : False => @lem3674918 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688678 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688677 _93670 x''''' y''''' h1 h2) (@lem3674918 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688679 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : (term848 _93670 x''''' y''''') = False.
Proof. exact (prop_ext (fun h3 : term848 _93670 x''''' y''''' => @lem3688678 _93670 x''''' y''''' h1 h2) (fun h3 : False => @lem3674916 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688680 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688679 _93670 x''''' y''''' h1 h2) (@lem3674916 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688681 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) = False.
Proof. exact (prop_ext (fun h5 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3686425 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (fun h5 : False => @lem3674472 _93670 _93677 x''''' f y''''' h4)). Qed.
Lemma lem3688682 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688681 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (@lem3674472 _93670 _93677 x''''' f y''''' h4)). Qed.
Lemma lem3688683 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (term848 _93670 x''''' y''''') = False.
Proof. exact (prop_ext (fun h5 : term848 _93670 x''''' y''''' => @lem3688682 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (fun h5 : False => @lem3674470 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688684 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688683 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (@lem3674470 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688685 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : (x''''' = y''''') = False.
Proof. exact (prop_ext (fun h3 : x''''' = y''''' => @lem3688670 _93670 _93677 f x''''' y''''' h1 h2) (fun h3 : False => @lem3674026 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688686 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688685 _93670 _93677 f x''''' y''''' h1 h2) (@lem3674026 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688687 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : (term843 _93670 _93677 x''''' f y''''') = False.
Proof. exact (prop_ext (fun h3 : term843 _93670 _93677 x''''' f y''''' => @lem3688686 _93670 _93677 f x''''' y''''' h1 h2) (fun h3 : False => @lem3674024 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688688 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688687 _93670 _93677 f x''''' y''''' h1 h2) (@lem3674024 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688689 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) = False.
Proof. exact (prop_ext (fun h3 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3684993 _93670 _93677 x''''' f y''''' h1 h2) (fun h3 : False => @lem3673580 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3688690 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688689 _93670 _93677 x''''' f y''''' h1 h2) (@lem3673580 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3688691 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (term843 _93670 _93677 x''''' f y''''') = False.
Proof. exact (prop_ext (fun h3 : term843 _93670 _93677 x''''' f y''''' => @lem3688690 _93670 _93677 x''''' f y''''' h1 h2) (fun h3 : False => @lem3673578 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688692 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688691 _93670 _93677 x''''' f y''''' h1 h2) (@lem3673578 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688693 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : (term891 _93670 t s) = False.
Proof. exact (prop_ext (fun h3 : term891 _93670 t s => @lem3684411 _93670 _93677 x''''' y''''' s P f t h1 h2) (fun h3 : False => @lem3673134 _93670 t s h1)). Qed.
Lemma lem3688694 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (EQ_MP (@lem3688693 _93670 _93677 x''''' y''''' s P f t h1 h2) (@lem3673134 _93670 t s h1)). Qed.
Lemma lem3688695 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : (term875 _93670 _93677 P f t) = False.
Proof. exact (prop_ext (fun h3 : term875 _93670 _93677 P f t => @lem3683829 _93670 _93677 s x''''' y''''' P f t h1 h2) (fun h3 : False => @lem3672694 _93670 _93677 P f t h1)). Qed.
Lemma lem3688696 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (EQ_MP (@lem3688695 _93670 _93677 s x''''' y''''' P f t h1 h2) (@lem3672694 _93670 _93677 P f t h1)). Qed.
Lemma lem3688697 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : (x''''' = y''''') = False.
Proof. exact (prop_ext (fun h3 : x''''' = y''''' => @lem3688671 _93670 x''''' y''''' h1 h2) (fun h3 : False => @lem3672254 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688698 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688697 _93670 x''''' y''''' h1 h2) (@lem3672254 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688699 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : (term848 _93670 x''''' y''''') = False.
Proof. exact (prop_ext (fun h3 : term848 _93670 x''''' y''''' => @lem3688698 _93670 x''''' y''''' h1 h2) (fun h3 : False => @lem3672252 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688700 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688699 _93670 x''''' y''''' h1 h2) (@lem3672252 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688701 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) = False.
Proof. exact (prop_ext (fun h5 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3682663 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (fun h5 : False => @lem3671808 _93670 _93677 x''''' f y''''' h4)). Qed.
Lemma lem3688702 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688701 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (@lem3671808 _93670 _93677 x''''' f y''''' h4)). Qed.
Lemma lem3688703 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (term848 _93670 x''''' y''''') = False.
Proof. exact (prop_ext (fun h5 : term848 _93670 x''''' y''''' => @lem3688702 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (fun h5 : False => @lem3671806 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688704 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688703 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (@lem3671806 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688705 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : (x''''' = y''''') = False.
Proof. exact (prop_ext (fun h3 : x''''' = y''''' => @lem3688672 _93670 _93677 f x''''' y''''' h1 h2) (fun h3 : False => @lem3671362 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688706 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688705 _93670 _93677 f x''''' y''''' h1 h2) (@lem3671362 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688707 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : (term843 _93670 _93677 x''''' f y''''') = False.
Proof. exact (prop_ext (fun h3 : term843 _93670 _93677 x''''' f y''''' => @lem3688706 _93670 _93677 f x''''' y''''' h1 h2) (fun h3 : False => @lem3671360 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688708 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688707 _93670 _93677 f x''''' y''''' h1 h2) (@lem3671360 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688709 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) = False.
Proof. exact (prop_ext (fun h3 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3681231 _93670 _93677 x''''' f y''''' h1 h2) (fun h3 : False => @lem3670916 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3688710 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688709 _93670 _93677 x''''' f y''''' h1 h2) (@lem3670916 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3688711 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (term843 _93670 _93677 x''''' f y''''') = False.
Proof. exact (prop_ext (fun h3 : term843 _93670 _93677 x''''' f y''''' => @lem3688710 _93670 _93677 x''''' f y''''' h1 h2) (fun h3 : False => @lem3670914 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688712 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688711 _93670 _93677 x''''' f y''''' h1 h2) (@lem3670914 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688713 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : (term794 _93670 t) = False.
Proof. exact (prop_ext (fun h4 : term794 _93670 t => @lem3680649 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3) (fun h4 : False => @lem3670470 _93670 t h2)). Qed.
Lemma lem3688714 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (EQ_MP (@lem3688713 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3) (@lem3670470 _93670 t h2)). Qed.
Lemma lem3688715 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : (term891 _93670 t s) = False.
Proof. exact (prop_ext (fun h3 : term891 _93670 t s => @lem3679548 _93670 _93677 s x''''' y''''' P f t h1 h2) (fun h3 : False => @lem3670030 _93670 t s h1)). Qed.
Lemma lem3688716 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (EQ_MP (@lem3688715 _93670 _93677 s x''''' y''''' P f t h1 h2) (@lem3670030 _93670 t s h1)). Qed.
Lemma lem3688717 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : (term875 _93670 _93677 P f t) = False.
Proof. exact (prop_ext (fun h3 : term875 _93670 _93677 P f t => @lem3688674 _93670 _93677 x''''' y''''' s P f t h1 h2) (fun h3 : False => @lem3668510 _93670 _93677 P f t h1)). Qed.
Lemma lem3688718 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (EQ_MP (@lem3688717 _93670 _93677 x''''' y''''' s P f t h1 h2) (@lem3668510 _93670 _93677 P f t h1)). Qed.
Lemma lem3688719 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : (term789 _93670 _93677 f t) = False.
Proof. exact (prop_ext (fun h4 : term789 _93670 _93677 f t => @lem3688676 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3) (fun h4 : False => @lem3668020 _93670 _93677 f t h2)). Qed.
Lemma lem3688720 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (EQ_MP (@lem3688719 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3) (@lem3668020 _93670 _93677 f t h2)). Qed.
Lemma lem3688721 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : (x''''' = y''''') = False.
Proof. exact (prop_ext (fun h3 : x''''' = y''''' => @lem3688680 _93670 x''''' y''''' h1 h2) (fun h3 : False => @lem3667530 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688722 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688721 _93670 x''''' y''''' h1 h2) (@lem3667530 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688723 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : (term848 _93670 x''''' y''''') = False.
Proof. exact (prop_ext (fun h3 : term848 _93670 x''''' y''''' => @lem3688722 _93670 x''''' y''''' h1 h2) (fun h3 : False => @lem3667526 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688724 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688723 _93670 x''''' y''''' h1 h2) (@lem3667526 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688725 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) = False.
Proof. exact (prop_ext (fun h5 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3688684 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (fun h5 : False => @lem3667028 _93670 _93677 x''''' f y''''' h4)). Qed.
Lemma lem3688726 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688725 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (@lem3667028 _93670 _93677 x''''' f y''''' h4)). Qed.
Lemma lem3688727 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (term848 _93670 x''''' y''''') = False.
Proof. exact (prop_ext (fun h5 : term848 _93670 x''''' y''''' => @lem3688726 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (fun h5 : False => @lem3667024 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688728 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688727 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (@lem3667024 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688729 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : (x''''' = y''''') = False.
Proof. exact (prop_ext (fun h3 : x''''' = y''''' => @lem3688688 _93670 _93677 f x''''' y''''' h1 h2) (fun h3 : False => @lem3666526 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688730 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688729 _93670 _93677 f x''''' y''''' h1 h2) (@lem3666526 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688731 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : (term843 _93670 _93677 x''''' f y''''') = False.
Proof. exact (prop_ext (fun h3 : term843 _93670 _93677 x''''' f y''''' => @lem3688730 _93670 _93677 f x''''' y''''' h1 h2) (fun h3 : False => @lem3666522 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688732 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688731 _93670 _93677 f x''''' y''''' h1 h2) (@lem3666522 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688733 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) = False.
Proof. exact (prop_ext (fun h3 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3688692 _93670 _93677 x''''' f y''''' h1 h2) (fun h3 : False => @lem3666024 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3688734 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688733 _93670 _93677 x''''' f y''''' h1 h2) (@lem3666024 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3688735 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (term843 _93670 _93677 x''''' f y''''') = False.
Proof. exact (prop_ext (fun h3 : term843 _93670 _93677 x''''' f y''''' => @lem3688734 _93670 _93677 x''''' f y''''' h1 h2) (fun h3 : False => @lem3666020 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688736 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688735 _93670 _93677 x''''' f y''''' h1 h2) (@lem3666020 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688737 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : (term891 _93670 t s) = False.
Proof. exact (prop_ext (fun h3 : term891 _93670 t s => @lem3688694 _93670 _93677 x''''' y''''' s P f t h1 h2) (fun h3 : False => @lem3665522 _93670 t s h1)). Qed.
Lemma lem3688738 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (EQ_MP (@lem3688737 _93670 _93677 x''''' y''''' s P f t h1 h2) (@lem3665522 _93670 t s h1)). Qed.
Lemma lem3688739 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : (term875 _93670 _93677 P f t) = False.
Proof. exact (prop_ext (fun h3 : term875 _93670 _93677 P f t => @lem3688696 _93670 _93677 s x''''' y''''' P f t h1 h2) (fun h3 : False => @lem3665032 _93670 _93677 P f t h1)). Qed.
Lemma lem3688740 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (EQ_MP (@lem3688739 _93670 _93677 s x''''' y''''' P f t h1 h2) (@lem3665032 _93670 _93677 P f t h1)). Qed.
Lemma lem3688741 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : (x''''' = y''''') = False.
Proof. exact (prop_ext (fun h3 : x''''' = y''''' => @lem3688700 _93670 x''''' y''''' h1 h2) (fun h3 : False => @lem3664542 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688742 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688741 _93670 x''''' y''''' h1 h2) (@lem3664542 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688743 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : (term848 _93670 x''''' y''''') = False.
Proof. exact (prop_ext (fun h3 : term848 _93670 x''''' y''''' => @lem3688742 _93670 x''''' y''''' h1 h2) (fun h3 : False => @lem3664538 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688744 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688743 _93670 x''''' y''''' h1 h2) (@lem3664538 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688745 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) = False.
Proof. exact (prop_ext (fun h5 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3688704 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (fun h5 : False => @lem3664040 _93670 _93677 x''''' f y''''' h4)). Qed.
Lemma lem3688746 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688745 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (@lem3664040 _93670 _93677 x''''' f y''''' h4)). Qed.
Lemma lem3688747 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (term848 _93670 x''''' y''''') = False.
Proof. exact (prop_ext (fun h5 : term848 _93670 x''''' y''''' => @lem3688746 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (fun h5 : False => @lem3664036 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688748 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688747 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (@lem3664036 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688749 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : (x''''' = y''''') = False.
Proof. exact (prop_ext (fun h3 : x''''' = y''''' => @lem3688708 _93670 _93677 f x''''' y''''' h1 h2) (fun h3 : False => @lem3663538 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688750 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688749 _93670 _93677 f x''''' y''''' h1 h2) (@lem3663538 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688751 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : (term843 _93670 _93677 x''''' f y''''') = False.
Proof. exact (prop_ext (fun h3 : term843 _93670 _93677 x''''' f y''''' => @lem3688750 _93670 _93677 f x''''' y''''' h1 h2) (fun h3 : False => @lem3663534 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688752 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688751 _93670 _93677 f x''''' y''''' h1 h2) (@lem3663534 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688753 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) = False.
Proof. exact (prop_ext (fun h3 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3688712 _93670 _93677 x''''' f y''''' h1 h2) (fun h3 : False => @lem3663036 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3688754 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688753 _93670 _93677 x''''' f y''''' h1 h2) (@lem3663036 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3688755 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (term843 _93670 _93677 x''''' f y''''') = False.
Proof. exact (prop_ext (fun h3 : term843 _93670 _93677 x''''' f y''''' => @lem3688754 _93670 _93677 x''''' f y''''' h1 h2) (fun h3 : False => @lem3663032 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688756 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688755 _93670 _93677 x''''' f y''''' h1 h2) (@lem3663032 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688757 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : (term794 _93670 t) = False.
Proof. exact (prop_ext (fun h4 : term794 _93670 t => @lem3688714 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3) (fun h4 : False => @lem3662534 _93670 t h2)). Qed.
Lemma lem3688758 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (EQ_MP (@lem3688757 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3) (@lem3662534 _93670 t h2)). Qed.
Lemma lem3688759 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : (term891 _93670 t s) = False.
Proof. exact (prop_ext (fun h3 : term891 _93670 t s => @lem3688716 _93670 _93677 s x''''' y''''' P f t h1 h2) (fun h3 : False => @lem3662044 _93670 t s h1)). Qed.
Lemma lem3688760 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (EQ_MP (@lem3688759 _93670 _93677 s x''''' y''''' P f t h1 h2) (@lem3662044 _93670 t s h1)). Qed.
Lemma lem3688761 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : (term875 _93670 _93677 P f t) = False.
Proof. exact (prop_ext (fun h3 : term875 _93670 _93677 P f t => @lem3688718 _93670 _93677 x''''' y''''' s P f t h1 h2) (fun h3 : False => @lem3668510 _93670 _93677 P f t h1)). Qed.
Lemma lem3688762 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (EQ_MP (@lem3688761 _93670 _93677 x''''' y''''' s P f t h1 h2) (@lem3668510 _93670 _93677 P f t h1)). Qed.
Lemma lem3688763 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : (term789 _93670 _93677 f t) = False.
Proof. exact (prop_ext (fun h4 : term789 _93670 _93677 f t => @lem3688720 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3) (fun h4 : False => @lem3668020 _93670 _93677 f t h2)). Qed.
Lemma lem3688764 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term789 _93670 _93677 f t) (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (EQ_MP (@lem3688763 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h3) (@lem3668020 _93670 _93677 f t h2)). Qed.
Lemma lem3688765 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : (x''''' = y''''') = False.
Proof. exact (prop_ext (fun h3 : x''''' = y''''' => @lem3688724 _93670 x''''' y''''' h1 h2) (fun h3 : False => @lem3667530 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688766 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688765 _93670 x''''' y''''' h1 h2) (@lem3667530 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688767 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : (term848 _93670 x''''' y''''') = False.
Proof. exact (prop_ext (fun h3 : term848 _93670 x''''' y''''' => @lem3688766 _93670 x''''' y''''' h1 h2) (fun h3 : False => @lem3667526 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688768 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688767 _93670 x''''' y''''' h1 h2) (@lem3667526 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688769 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) = False.
Proof. exact (prop_ext (fun h5 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3688728 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (fun h5 : False => @lem3667028 _93670 _93677 x''''' f y''''' h4)). Qed.
Lemma lem3688770 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688769 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (@lem3667028 _93670 _93677 x''''' f y''''' h4)). Qed.
Lemma lem3688771 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (term848 _93670 x''''' y''''') = False.
Proof. exact (prop_ext (fun h5 : term848 _93670 x''''' y''''' => @lem3688770 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (fun h5 : False => @lem3667024 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688772 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688771 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (@lem3667024 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688773 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : (x''''' = y''''') = False.
Proof. exact (prop_ext (fun h3 : x''''' = y''''' => @lem3688732 _93670 _93677 f x''''' y''''' h1 h2) (fun h3 : False => @lem3666526 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688774 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688773 _93670 _93677 f x''''' y''''' h1 h2) (@lem3666526 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688775 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : (term843 _93670 _93677 x''''' f y''''') = False.
Proof. exact (prop_ext (fun h3 : term843 _93670 _93677 x''''' f y''''' => @lem3688774 _93670 _93677 f x''''' y''''' h1 h2) (fun h3 : False => @lem3666522 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688776 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688775 _93670 _93677 f x''''' y''''' h1 h2) (@lem3666522 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688777 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) = False.
Proof. exact (prop_ext (fun h3 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3688736 _93670 _93677 x''''' f y''''' h1 h2) (fun h3 : False => @lem3666024 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3688778 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688777 _93670 _93677 x''''' f y''''' h1 h2) (@lem3666024 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3688779 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (term843 _93670 _93677 x''''' f y''''') = False.
Proof. exact (prop_ext (fun h3 : term843 _93670 _93677 x''''' f y''''' => @lem3688778 _93670 _93677 x''''' f y''''' h1 h2) (fun h3 : False => @lem3666020 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688780 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688779 _93670 _93677 x''''' f y''''' h1 h2) (@lem3666020 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688781 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : (term891 _93670 t s) = False.
Proof. exact (prop_ext (fun h3 : term891 _93670 t s => @lem3688738 _93670 _93677 x''''' y''''' s P f t h1 h2) (fun h3 : False => @lem3665522 _93670 t s h1)). Qed.
Lemma lem3688782 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (EQ_MP (@lem3688781 _93670 _93677 x''''' y''''' s P f t h1 h2) (@lem3665522 _93670 t s h1)). Qed.
Lemma lem3688783 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : (term875 _93670 _93677 P f t) = False.
Proof. exact (prop_ext (fun h3 : term875 _93670 _93677 P f t => @lem3688740 _93670 _93677 s x''''' y''''' P f t h1 h2) (fun h3 : False => @lem3665032 _93670 _93677 P f t h1)). Qed.
Lemma lem3688784 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term875 _93670 _93677 P f t) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (EQ_MP (@lem3688783 _93670 _93677 s x''''' y''''' P f t h1 h2) (@lem3665032 _93670 _93677 P f t h1)). Qed.
Lemma lem3688785 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : (x''''' = y''''') = False.
Proof. exact (prop_ext (fun h3 : x''''' = y''''' => @lem3688744 _93670 x''''' y''''' h1 h2) (fun h3 : False => @lem3664542 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688786 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688785 _93670 x''''' y''''' h1 h2) (@lem3664542 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688787 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : (term848 _93670 x''''' y''''') = False.
Proof. exact (prop_ext (fun h3 : term848 _93670 x''''' y''''' => @lem3688786 _93670 x''''' y''''' h1 h2) (fun h3 : False => @lem3664538 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688788 {_93670 : Type'} (x''''' : _93670) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688787 _93670 x''''' y''''' h1 h2) (@lem3664538 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688789 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) = False.
Proof. exact (prop_ext (fun h5 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3688748 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (fun h5 : False => @lem3664040 _93670 _93677 x''''' f y''''' h4)). Qed.
Lemma lem3688790 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688789 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (@lem3664040 _93670 _93677 x''''' f y''''' h4)). Qed.
Lemma lem3688791 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (term848 _93670 x''''' y''''') = False.
Proof. exact (prop_ext (fun h5 : term848 _93670 x''''' y''''' => @lem3688790 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (fun h5 : False => @lem3664036 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688792 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (t : _93670 -> Prop) (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) (h4 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688791 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h4) (@lem3664036 _93670 x''''' y''''' h1)). Qed.
Lemma lem3688793 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : (x''''' = y''''') = False.
Proof. exact (prop_ext (fun h3 : x''''' = y''''' => @lem3688752 _93670 _93677 f x''''' y''''' h1 h2) (fun h3 : False => @lem3663538 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688794 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688793 _93670 _93677 f x''''' y''''' h1 h2) (@lem3663538 _93670 x''''' y''''' h2)). Qed.
Lemma lem3688795 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : (term843 _93670 _93677 x''''' f y''''') = False.
Proof. exact (prop_ext (fun h3 : term843 _93670 _93677 x''''' f y''''' => @lem3688794 _93670 _93677 f x''''' y''''' h1 h2) (fun h3 : False => @lem3663534 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688796 {_93670 _93677 : Type'} (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : x''''' = y''''') : False.
Proof. exact (EQ_MP (@lem3688795 _93670 _93677 f x''''' y''''' h1 h2) (@lem3663534 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688797 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : ((@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) = False.
Proof. exact (prop_ext (fun h3 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3688756 _93670 _93677 x''''' f y''''' h1 h2) (fun h3 : False => @lem3663036 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3688798 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688797 _93670 _93677 x''''' f y''''' h1 h2) (@lem3663036 _93670 _93677 x''''' f y''''' h2)). Qed.
Lemma lem3688799 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : (term843 _93670 _93677 x''''' f y''''') = False.
Proof. exact (prop_ext (fun h3 : term843 _93670 _93677 x''''' f y''''' => @lem3688798 _93670 _93677 x''''' f y''''' h1 h2) (fun h3 : False => @lem3663032 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688800 {_93670 _93677 : Type'} (x''''' : _93670) (f : _93670 -> _93677) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''')) : False.
Proof. exact (EQ_MP (@lem3688799 _93670 _93677 x''''' f y''''' h1 h2) (@lem3663032 _93670 _93677 x''''' f y''''' h1)). Qed.
Lemma lem3688801 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : (term794 _93670 t) = False.
Proof. exact (prop_ext (fun h4 : term794 _93670 t => @lem3688758 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3) (fun h4 : False => @lem3662534 _93670 t h2)). Qed.
Lemma lem3688802 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term794 _93670 t) (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (EQ_MP (@lem3688801 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h3) (@lem3662534 _93670 t h2)). Qed.
Lemma lem3688803 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : (term891 _93670 t s) = False.
Proof. exact (prop_ext (fun h3 : term891 _93670 t s => @lem3688760 _93670 _93677 s x''''' y''''' P f t h1 h2) (fun h3 : False => @lem3662044 _93670 t s h1)). Qed.
Lemma lem3688804 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term891 _93670 t s) (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (EQ_MP (@lem3688803 _93670 _93677 s x''''' y''''' P f t h1 h2) (@lem3662044 _93670 t s h1)). Qed.
Lemma lem3688805 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term895 _93670 _93677 x''''' y''''' s P f t) (h3 : term876 _93670 _93677 P f t) : False.
Proof. exact (or_elim (@lem3661540 _93670 _93677 P f t h3) (fun h0 : term789 _93670 _93677 f t => @lem3688764 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h0 h2) (fun h0 : term875 _93670 _93677 P f t => @lem3688762 _93670 _93677 x''''' y''''' s P f t h0 h2)). Qed.
Lemma lem3688806 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (or_elim (@lem3661544 _93670 _93677 t f x''''' y''''' h2) (fun h0 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3688772 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h0) (fun h0 : x''''' = y''''' => @lem3688768 _93670 x''''' y''''' h1 h0)). Qed.
Lemma lem3688807 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') : False.
Proof. exact (or_elim (@lem3661544 _93670 _93677 t f x''''' y''''' h2) (fun h0 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3688780 _93670 _93677 x''''' f y''''' h1 h0) (fun h0 : x''''' = y''''' => @lem3688776 _93670 _93677 f x''''' y''''' h1 h0)). Qed.
Lemma lem3688808 {_93670 _93677 : Type'} (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term888 _93670 _93677 t f x''''' y''''') (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (or_elim (@lem3661543 _93670 _93677 t f x''''' y''''' h1) (fun h0 : term843 _93670 _93677 x''''' f y''''' => @lem3688807 _93670 _93677 t f x''''' y''''' h0 h1) (fun h0 : term848 _93670 x''''' y''''' => @lem3688806 _93670 _93677 x''''' y''''' s P f t h0 h1 h2)). Qed.
Lemma lem3688809 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term895 _93670 _93677 x''''' y''''' s P f t) (h3 : term890 _93670 _93677 x''''' y''''' P f t) : False.
Proof. exact (or_elim (@lem3661538 _93670 _93677 x''''' y''''' P f t h3) (fun h0 : term888 _93670 _93677 t f x''''' y''''' => @lem3688808 _93670 _93677 x''''' y''''' s P f t h0 h2) (fun h0 : term876 _93670 _93677 P f t => @lem3688805 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h2 h0)). Qed.
Lemma lem3688810 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term895 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (or_elim (@lem3661530 _93670 _93677 x''''' y''''' s P f t h2) (fun h0 : term891 _93670 t s => @lem3688782 _93670 _93677 x''''' y''''' s P f t h0 h2) (fun h0 : term890 _93670 _93677 x''''' y''''' P f t => @lem3688809 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h0)). Qed.
Lemma lem3688811 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term848 _93670 x''''' y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') (h3 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (or_elim (@lem3661520 _93670 _93677 t f x''''' y''''' h2) (fun h0 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3688792 _93670 _93677 s P t x''''' f y''''' h1 h2 h3 h0) (fun h0 : x''''' = y''''' => @lem3688788 _93670 x''''' y''''' h1 h0)). Qed.
Lemma lem3688812 {_93670 _93677 : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) (x''''' : _93670) (y''''' : _93670) (h1 : term843 _93670 _93677 x''''' f y''''') (h2 : term888 _93670 _93677 t f x''''' y''''') : False.
Proof. exact (or_elim (@lem3661520 _93670 _93677 t f x''''' y''''' h2) (fun h0 : (@I (_93670 -> _93677) f x''''') = (@I (_93670 -> _93677) f y''''') => @lem3688800 _93670 _93677 x''''' f y''''' h1 h0) (fun h0 : x''''' = y''''' => @lem3688796 _93670 _93677 f x''''' y''''' h1 h0)). Qed.
Lemma lem3688813 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term888 _93670 _93677 t f x''''' y''''') (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (or_elim (@lem3661519 _93670 _93677 t f x''''' y''''' h1) (fun h0 : term843 _93670 _93677 x''''' f y''''' => @lem3688812 _93670 _93677 t f x''''' y''''' h0 h1) (fun h0 : term848 _93670 x''''' y''''' => @lem3688811 _93670 _93677 s x''''' y''''' P f t h0 h1 h2)). Qed.
Lemma lem3688814 {_93670 _93677 : Type'} (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term906 _93670 _93677 s x''''' y''''' P f t) (h2 : term896 _93670 _93677 x''''' y''''' P f t) : False.
Proof. exact (or_elim (@lem3661514 _93670 _93677 x''''' y''''' P f t h2) (fun h0 : term888 _93670 _93677 t f x''''' y''''' => @lem3688813 _93670 _93677 s x''''' y''''' P f t h0 h1) (fun h0 : term875 _93670 _93677 P f t => @lem3688784 _93670 _93677 s x''''' y''''' P f t h0 h1)). Qed.
Lemma lem3688815 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term906 _93670 _93677 s x''''' y''''' P f t) (h3 : term898 _93670 _93677 x''''' y''''' P f t) : False.
Proof. exact (or_elim (@lem3661512 _93670 _93677 x''''' y''''' P f t h3) (fun h0 : term794 _93670 t => @lem3688802 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h0 h2) (fun h0 : term896 _93670 _93677 x''''' y''''' P f t => @lem3688814 _93670 _93677 s x''''' y''''' P f t h2 h0)). Qed.
Lemma lem3688816 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (x''''' : _93670) (y''''' : _93670) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term906 _93670 _93677 s x''''' y''''' P f t) : False.
Proof. exact (or_elim (@lem3661503 _93670 _93677 s x''''' y''''' P f t h2) (fun h0 : term891 _93670 t s => @lem3688804 _93670 _93677 s x''''' y''''' P f t h0 h2) (fun h0 : term898 _93670 _93677 x''''' y''''' P f t => @lem3688815 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h2 h0)). Qed.
Lemma lem3688817 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (y''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term463 _93670 _93677 x''''' y''''' s P f t) : False.
Proof. exact (or_elim (@lem3661500 _93670 _93677 x''''' y''''' s P f t h2) (fun h0 : term906 _93670 _93677 s x''''' y''''' P f t => @lem3688816 _93670 _93677 x'''' y'''' s x''''' y''''' P f t h1 h0) (fun h0 : term895 _93670 _93677 x''''' y''''' s P f t => @lem3688810 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h0)). Qed.
Lemma lem3688818 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (x''''' : _93670) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term466 _93670 _93677 x''''' s P f t) : False.
Proof. exact (ex_elim (@lem3659533 _93670 _93677 x''''' s P f t h2) (fun y''''' : _93670 => fun h0 : term465 _93670 _93677 x''''' s P f t y''''' => @lem3688817 _93670 _93677 x'''' y'''' x''''' y''''' s P f t h1 h0)). Qed.
Lemma lem3688819 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (y'''' : type529 _93670 _93677) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term623 _93670 _93677 x'''' y'''') (h2 : term81 _93670 _93677 s P f t) : False.
Proof. exact (ex_elim (@lem3657737 _93670 _93677 s P f t h2) (fun x''''' : _93670 => fun h0 : term467 _93670 _93677 s P f t x''''' => @lem3688818 _93670 _93677 x'''' y'''' x''''' s P f t h1 h0)). Qed.
Lemma lem3688820 {_93670 _93677 : Type'} (x'''' : type529 _93670 _93677) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term626 _93670 _93677 x'''') (h2 : term81 _93670 _93677 s P f t) : False.
Proof. exact (ex_elim (@lem3659531 _93670 _93677 x'''' h1) (fun y'''' : type529 _93670 _93677 => fun h0 : term625 _93670 _93677 x'''' y'''' => @lem3688819 _93670 _93677 x'''' y'''' s P f t h0 h2)). Qed.
Lemma lem3688821 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term82 _93670 _93677) (h2 : term81 _93670 _93677 s P f t) : False.
Proof. exact (ex_elim (@lem3658094 _93670 _93677 h1) (fun x'''' : type529 _93670 _93677 => fun h0 : term627 _93670 _93677 x'''' => @lem3688820 _93670 _93677 x'''' s P f t h0 h2)). Qed.
Lemma lem3688822 {_93670 _93677 B : Type'} (x''' : type529 _93670 B) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term82 _93670 _93677) (h2 : term626 _93670 B x''') (h3 : term81 _93670 _93677 s P f t) : False.
Proof. exact (ex_elim (@lem3659529 _93670 B x''' h2) (fun y''' : type529 _93670 B => fun h0 : term625 _93670 B x''' y''' => @lem3688821 _93670 _93677 s P f t h1 h3)). Qed.
Lemma lem3688823 {_93670 _93677 B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term82 _93670 _93677) (h2 : term82 _93670 B) (h3 : term81 _93670 _93677 s P f t) : False.
Proof. exact (ex_elim (@lem3658451 _93670 B h2) (fun x''' : type529 _93670 B => fun h0 : term627 _93670 B x''' => @lem3688822 _93670 _93677 B x''' s P f t h1 h0 h3)). Qed.
Lemma lem3688824 {_93670 _93677 B : Type'} (x'' : type529 _93677 B) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term82 _93670 _93677) (h2 : term82 _93670 B) (h3 : term626 _93677 B x'') (h4 : term81 _93670 _93677 s P f t) : False.
Proof. exact (ex_elim (@lem3659527 _93677 B x'' h3) (fun y'' : type529 _93677 B => fun h0 : term625 _93677 B x'' y'' => @lem3688823 _93670 _93677 B s P f t h1 h2 h4)). Qed.
Lemma lem3688825 {_93670 _93677 B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term82 _93670 _93677) (h2 : term82 _93670 B) (h3 : term82 _93677 B) (h4 : term81 _93670 _93677 s P f t) : False.
Proof. exact (ex_elim (@lem3658808 _93677 B h3) (fun x'' : type529 _93677 B => fun h0 : term627 _93677 B x'' => @lem3688824 _93670 _93677 B x'' s P f t h1 h2 h0 h4)). Qed.
Lemma lem3688826 {_93670 _93677 A B : Type'} (x' : type791 _93670 A) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term82 _93670 _93677) (h2 : term82 _93670 B) (h3 : term82 _93677 B) (h4 : term782 _93670 A x') (h5 : term81 _93670 _93677 s P f t) : False.
Proof. exact (ex_elim (@lem3659525 _93670 A x' h4) (fun y' : type791 _93670 A => fun h0 : term781 _93670 A x' y' => @lem3688825 _93670 _93677 B s P f t h1 h2 h3 h5)). Qed.
Lemma lem3688827 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term82 _93670 _93677) (h2 : term82 _93670 B) (h3 : term82 _93677 B) (h4 : term83 _93670 A) (h5 : term81 _93670 _93677 s P f t) : False.
Proof. exact (ex_elim (@lem3659165 _93670 A h4) (fun x' : type791 _93670 A => fun h0 : term783 _93670 A x' => @lem3688826 _93670 _93677 A B x' s P f t h1 h2 h3 h0 h5)). Qed.
Lemma lem3688828 {_93670 _93677 A B : Type'} (x : type791 _93677 A) (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term82 _93670 _93677) (h2 : term82 _93670 B) (h3 : term82 _93677 B) (h4 : term83 _93670 A) (h5 : term782 _93677 A x) (h6 : term81 _93670 _93677 s P f t) : False.
Proof. exact (ex_elim (@lem3659523 _93677 A x h5) (fun y : type791 _93677 A => fun h0 : term781 _93677 A x y => @lem3688827 _93670 _93677 A B s P f t h1 h2 h3 h4 h6)). Qed.
Lemma lem3688829 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term82 _93670 _93677) (h2 : term82 _93670 B) (h3 : term82 _93677 B) (h4 : term83 _93670 A) (h5 : term83 _93677 A) (h6 : term81 _93670 _93677 s P f t) : False.
Proof. exact (ex_elim (@lem3659522 _93677 A h5) (fun x : type791 _93677 A => fun h0 : term783 _93677 A x => @lem3688828 _93670 _93677 A B x s P f t h1 h2 h3 h4 h0 h6)). Qed.
Lemma lem3688830 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term82 _93670 _93677) (h2 : term82 _93670 B) (h3 : term82 _93677 B) (h4 : term83 _93670 A) (h5 : term81 _93670 _93677 s P f t) : term88 _93677 A.
Proof. exact (fun h0 : term83 _93677 A => @lem3688829 _93670 _93677 A B s P f t h1 h2 h3 h4 h0 h5). Qed.
Lemma lem3688831 {_93677 A : Type'} : (term88 _93677 A) = (term89 _93677 A).
Proof. exact (@lem69 (term83 _93677 A)). Qed.
Lemma lem3688832 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term82 _93670 _93677) (h2 : term82 _93670 B) (h3 : term82 _93677 B) (h4 : term83 _93670 A) (h5 : term81 _93670 _93677 s P f t) : term89 _93677 A.
Proof. exact (EQ_MP (@lem3688831 _93677 A) (@lem3688830 _93670 _93677 A B s P f t h1 h2 h3 h4 h5)). Qed.
Lemma lem3688833 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term82 _93670 _93677) (h2 : term82 _93670 B) (h3 : term82 _93677 B) (h4 : term81 _93670 _93677 s P f t) : term92 _93670 _93677 A.
Proof. exact (fun h0 : term83 _93670 A => @lem3688832 _93670 _93677 A B s P f t h1 h2 h3 h0 h4). Qed.
Lemma lem3688834 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term82 _93670 _93677) (h2 : term82 _93670 B) (h3 : term81 _93670 _93677 s P f t) : term95 _93670 _93677 A B.
Proof. exact (fun h0 : term82 _93677 B => @lem3688833 _93670 _93677 A B s P f t h1 h2 h0 h3). Qed.
Lemma lem3688835 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term82 _93670 _93677) (h2 : term81 _93670 _93677 s P f t) : term97 _93670 _93677 A B.
Proof. exact (fun h0 : term82 _93670 B => @lem3688834 _93670 _93677 A B s P f t h1 h0 h2). Qed.
Lemma lem3688836 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term81 _93670 _93677 s P f t) : term99 _93670 _93677 A B.
Proof. exact (fun h0 : term82 _93670 _93677 => @lem3688835 _93670 _93677 A B s P f t h0 h1). Qed.
Lemma lem3688837 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : term101 _93670 _93677 A B s P f t.
Proof. exact (fun h0 : term81 _93670 _93677 s P f t => @lem3688836 _93670 _93677 A B s P f t h0). Qed.
Lemma lem3688842 {_93670 _93677 A B : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : term105 _93670 _93677 A B P f t.
Proof. exact (fun s : _93670 -> Prop => @lem3688837 _93670 _93677 A B s P f t). Qed.
Lemma lem3688847 {_93670 _93677 A B : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : term109 _93670 _93677 A B f t.
Proof. exact (fun P : type686 _93677 => @lem3688842 _93670 _93677 A B P f t). Qed.
Lemma lem3688852 {_93670 _93677 A B : Type'} (t : _93670 -> Prop) : term113 _93670 _93677 A B t.
Proof. exact (fun f : _93670 -> _93677 => @lem3688847 _93670 _93677 A B f t). Qed.
Lemma lem3688857 {_93670 _93677 A B : Type'} : term117 _93670 _93677 A B.
Proof. exact (fun t : _93670 -> Prop => @lem3688852 _93670 _93677 A B t). Qed.
Lemma lem3688858 {_93670 _93677 A B : Type'} : term116 _93670 _93677 A B.
Proof. exact (EQ_MP (@lem3656889 _93670 _93677 A B) (@lem3688857 _93670 _93677 A B)). Qed.
Lemma lem3688859 {_93670 _93677 A B : Type'} (t : _93670 -> Prop) : term1095 _93670 _93677 A B t.
Proof. exact (@lem3688858 _93670 _93677 A B t). Qed.
Lemma lem3688860 {_93670 _93677 A B : Type'} (t : _93670 -> Prop) : (term1095 _93670 _93677 A B t) = (term112 _93670 _93677 A B t).
Proof. exact (eq_refl (term1095 _93670 _93677 A B t)). Qed.
Lemma lem3688861 {_93670 _93677 A B : Type'} (t : _93670 -> Prop) : term112 _93670 _93677 A B t.
Proof. exact (EQ_MP (@lem3688860 _93670 _93677 A B t) (@lem3688859 _93670 _93677 A B t)). Qed.
Lemma lem3688862 {_93670 _93677 A B : Type'} (t : _93670 -> Prop) (f : _93670 -> _93677) : term1096 _93670 _93677 A B t f.
Proof. exact (@lem3688861 _93670 _93677 A B t f). Qed.
Lemma lem3688863 {_93670 _93677 A B : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : (term1096 _93670 _93677 A B t f) = (term108 _93670 _93677 A B f t).
Proof. exact (eq_refl (term1096 _93670 _93677 A B t f)). Qed.
Lemma lem3688864 {_93670 _93677 A B : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) : term108 _93670 _93677 A B f t.
Proof. exact (EQ_MP (@lem3688863 _93670 _93677 A B f t) (@lem3688862 _93670 _93677 A B t f)). Qed.
Lemma lem3688865 {_93670 _93677 A B : Type'} (f : _93670 -> _93677) (t : _93670 -> Prop) (P : type686 _93677) : term1097 _93670 _93677 A B f t P.
Proof. exact (@lem3688864 _93670 _93677 A B f t P). Qed.
Lemma lem3688866 {_93670 _93677 A B : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term1097 _93670 _93677 A B f t P) = (term104 _93670 _93677 A B P f t).
Proof. exact (eq_refl (term1097 _93670 _93677 A B f t P)). Qed.
Lemma lem3688867 {_93670 _93677 A B : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : term104 _93670 _93677 A B P f t.
Proof. exact (EQ_MP (@lem3688866 _93670 _93677 A B P f t) (@lem3688865 _93670 _93677 A B f t P)). Qed.
Lemma lem3688868 {_93670 _93677 A B : Type'} (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (s : _93670 -> Prop) : term1098 _93670 _93677 A B P f t s.
Proof. exact (@lem3688867 _93670 _93677 A B P f t s). Qed.
Lemma lem3688869 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term1098 _93670 _93677 A B P f t s) = (term84 _93670 _93677 A B s P f t).
Proof. exact (eq_refl (term1098 _93670 _93677 A B P f t s)). Qed.
Lemma lem3688870 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : term84 _93670 _93677 A B s P f t.
Proof. exact (EQ_MP (@lem3688869 _93670 _93677 A B s P f t) (@lem3688868 _93670 _93677 A B P f t s)). Qed.
Lemma lem3688872 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : term84 _93670 _93677 A B s P f t.
Proof. exact (@lem3656149 _93670 _93677 A B s P f t (@lem3688870 _93670 _93677 A B s P f t)). Qed.
Lemma lem3688873 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term81 _93670 _93677 s P f t) : term98 _93670 _93677 A B.
Proof. exact (@lem3688872 _93670 _93677 A B s P f t (@lem3656123 _93670 _93677 s P f t h1)). Qed.
Lemma lem3688874 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term81 _93670 _93677 s P f t) : term96 _93670 _93677 A B.
Proof. exact (@lem3688873 _93670 _93677 A B s P f t h1 (@lem3656131 _93670 _93677)). Qed.
Lemma lem3688875 {_93670 _93677 A B : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term81 _93670 _93677 s P f t) : term94 _93670 _93677 A B.
Proof. exact (@lem3688874 _93670 _93677 A B s P f t h1 (@lem3656124 _93670 B)). Qed.
Lemma lem3688876 {_93670 _93677 A : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term81 _93670 _93677 s P f t) : term91 _93670 _93677 A.
Proof. exact (@lem3688875 _93670 _93677 A Prop s P f t h1 (@lem3656127 _93677 Prop)). Qed.
Lemma lem3688877 {_93670 _93677 A : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term81 _93670 _93677 s P f t) : term88 _93677 A.
Proof. exact (@lem3688876 _93670 _93677 A s P f t h1 (@lem3656126 _93670 A)). Qed.
Lemma lem3688878 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term81 _93670 _93677 s P f t) : False.
Proof. exact (@lem3688877 _93670 _93677 Prop s P f t h1 (@lem3656125 _93677 Prop)). Qed.
Lemma lem3688879 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term81 _93670 _93677 s P f t) : (term81 _93670 _93677 s P f t) = False.
Proof. exact (prop_ext (fun h2 : term81 _93670 _93677 s P f t => @lem3688878 _93670 _93677 s P f t h1) (fun h2 : False => @lem3656123 _93670 _93677 s P f t h1)). Qed.
Lemma lem3688880 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) (h1 : term81 _93670 _93677 s P f t) : False.
Proof. exact (EQ_MP (@lem3688879 _93670 _93677 s P f t h1) (@lem3656123 _93670 _93677 s P f t h1)). Qed.
Lemma lem3688881 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : term80 _93670 _93677 s P f t.
Proof. exact (fun h0 : term81 _93670 _93677 s P f t => @lem3688880 _93670 _93677 s P f t h0). Qed.
Lemma lem3688882 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) (t : _93670 -> Prop) : (term74 _93670 _93677 s P f t) = (term40 _93670 _93677 s P f t).
Proof. exact (EQ_MP (@lem3656122 _93670 _93677 s P f t) (@lem3688881 _93670 _93677 s P f t)). Qed.
Lemma lem3688885 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term76 _93670 _93677 s P f) = (term43 _93670 _93677 s P f).
Proof. exact (fun_ext (fun t : _93670 -> Prop => @lem3688882 _93670 _93677 s P f t)). Qed.
Lemma lem3688886 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term77 _93670 _93677 s P f) = (term45 _93670 _93677 s P f).
Proof. exact (MK_COMB (@lem3656118 _93670) (@lem3688885 _93670 _93677 s P f)). Qed.
Lemma lem3688887 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term36 _93670 _93677 f s P) = (term45 _93670 _93677 s P f).
Proof. exact (EQ_MP (@lem3656117 _93670 _93677 s P f) (@lem3688886 _93670 _93677 s P f)). Qed.
Lemma lem3688892 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) : term49 _93670 _93677 P f.
Proof. exact (fun s : _93670 -> Prop => @lem3688887 _93670 _93677 s P f). Qed.
Lemma lem3688897 {_93670 _93677 : Type'} (P : type686 _93677) : term53 _93670 _93677 P.
Proof. exact (fun f : _93670 -> _93677 => @lem3688892 _93670 _93677 P f). Qed.
Lemma lem3688902 {_93670 _93677 : Type'} : term57 _93670 _93677.
Proof. exact (fun P : type686 _93677 => @lem3688897 _93670 _93677 P). Qed.
Lemma lem3688903 {_93670 _93677 : Type'} : term56 _93670 _93677.
Proof. exact (EQ_MP (@lem3656030 _93670 _93677) (@lem3688902 _93670 _93677)). Qed.
