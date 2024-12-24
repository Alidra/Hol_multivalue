Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_FINITE_SUBSET_IMAGE_INJ_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Require Import EXISTS_FINITE_SUBSET_IMAGE_INJ_spec.
Require Import NOT_IMP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem3688907 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem3688908 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (SYM (@lem3688907 t1 t2 t3 h1)). Qed.
Lemma lem3688909 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem3688910 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (SYM (@lem3688909 t1 t2 t3 h1)). Qed.
Lemma lem3688911 (t1 : Prop) (t2 : Prop) (t3 : Prop) : ((term0 t1 t2 t3) = (term1 t1 t2 t3)) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (prop_ext (fun h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3) => @lem3688908 t1 t2 t3 h1) (fun h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3) => @lem3688910 t1 t2 t3 h1)). Qed.
Lemma lem3688912 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (fun_ext (fun t3 : Prop => @lem3688911 t1 t2 t3)). Qed.
Lemma lem3688913 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3688914 (t1 : Prop) (t2 : Prop) : (term4 t1 t2) = (term5 t1 t2).
Proof. exact (MK_COMB (@lem3688913) (@lem3688912 t1 t2)). Qed.
Lemma lem3688915 (t1 : Prop) : (term6 t1) = (term7 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem3688914 t1 t2)). Qed.
Lemma lem3688916 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3688917 (t1 : Prop) : (term8 t1) = (term9 t1).
Proof. exact (MK_COMB (@lem3688916) (@lem3688915 t1)). Qed.
Lemma lem3688918 : term10 = term11.
Proof. exact (fun_ext (fun t1 : Prop => @lem3688917 t1)). Qed.
Lemma lem3688919 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3688920 : term12 = term13.
Proof. exact (MK_COMB (@lem3688919) (@lem3688918)). Qed.
Lemma lem3688921 : term13.
Proof. exact (EQ_MP (@lem3688920) (@lem512)). Qed.
Lemma lem3688922 (t1 : Prop) : term14 t1.
Proof. exact (@lem3688921 t1). Qed.
Lemma lem3688923 (t1 : Prop) : (term14 t1) = (term9 t1).
Proof. exact (eq_refl (term14 t1)). Qed.
Lemma lem3688924 (t1 : Prop) : term9 t1.
Proof. exact (EQ_MP (@lem3688923 t1) (@lem3688922 t1)). Qed.
Lemma lem3688925 (t1 : Prop) (t2 : Prop) : term15 t1 t2.
Proof. exact (@lem3688924 t1 t2). Qed.
Lemma lem3688926 (t1 : Prop) (t2 : Prop) : (term15 t1 t2) = (term5 t1 t2).
Proof. exact (eq_refl (term15 t1 t2)). Qed.
Lemma lem3688927 (t1 : Prop) (t2 : Prop) : term5 t1 t2.
Proof. exact (EQ_MP (@lem3688926 t1 t2) (@lem3688925 t1 t2)). Qed.
Lemma lem3688928 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term16 t1 t2 t3.
Proof. exact (@lem3688927 t1 t2 t3). Qed.
Lemma lem3688929 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term16 t1 t2 t3) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (eq_refl (term16 t1 t2 t3)). Qed.
Lemma lem3688931 {_93670 _93677 : Type'} (P : type686 _93677) : term17 _93670 _93677 P.
Proof. exact (@lem3688903 _93670 _93677 P). Qed.
Lemma lem3688932 {_93670 _93677 : Type'} (P : type686 _93677) : (term17 _93670 _93677 P) = (term18 _93670 _93677 P).
Proof. exact (eq_refl (term17 _93670 _93677 P)). Qed.
Lemma lem3688933 {_93670 _93677 : Type'} (P : type686 _93677) : term18 _93670 _93677 P.
Proof. exact (EQ_MP (@lem3688932 _93670 _93677 P) (@lem3688931 _93670 _93677 P)). Qed.
Lemma lem3688934 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) : term19 _93670 _93677 P f.
Proof. exact (@lem3688933 _93670 _93677 P f). Qed.
Lemma lem3688935 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) : (term19 _93670 _93677 P f) = (term20 _93670 _93677 P f).
Proof. exact (eq_refl (term19 _93670 _93677 P f)). Qed.
Lemma lem3688936 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) : term20 _93670 _93677 P f.
Proof. exact (EQ_MP (@lem3688935 _93670 _93677 P f) (@lem3688934 _93670 _93677 P f)). Qed.
Lemma lem3688937 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : term21 _93670 _93677 P f s.
Proof. exact (@lem3688936 _93670 _93677 P f s). Qed.
Lemma lem3688938 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term21 _93670 _93677 P f s) = ((term22 _93670 _93677 f s P) = (term23 _93670 _93677 s P f)).
Proof. exact (eq_refl (term21 _93670 _93677 P f s)). Qed.
Lemma lem3688940 (t1 : Prop) : term24 t1.
Proof. exact (@lem10299 t1). Qed.
Lemma lem3688941 (t1 : Prop) : (term24 t1) = (term25 t1).
Proof. exact (eq_refl (term24 t1)). Qed.
Lemma lem3688942 (t1 : Prop) : term25 t1.
Proof. exact (EQ_MP (@lem3688941 t1) (@lem3688940 t1)). Qed.
Lemma lem3688943 (t1 : Prop) (t2 : Prop) : term26 t1 t2.
Proof. exact (@lem3688942 t1 t2). Qed.
Lemma lem3688944 (t1 : Prop) (t2 : Prop) : (term26 t1 t2) = ((term27 t1 t2) = (term28 t1 t2)).
Proof. exact (eq_refl (term26 t1 t2)). Qed.
Lemma lem3688957 (p : Prop) : p = (term29 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3688958 {_93692 : Type'} (p : _93692 -> Prop) : ((term30 _93692 p) = (term31 _93692 p)) = (term32 _93692 p).
Proof. exact (@lem3688957 ((term30 _93692 p) = (term31 _93692 p))). Qed.
Lemma lem3688959 {_93692 : Type'} (p : _93692 -> Prop) : (term32 _93692 p) = ((term30 _93692 p) = (term31 _93692 p)).
Proof. exact (SYM (@lem3688958 _93692 p)). Qed.
Lemma lem3688960 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term33 _93692 p) : term33 _93692 p.
Proof. exact (h1). Qed.
Lemma lem3688963 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term32 _93692 p) : term32 _93692 p.
Proof. exact (h1). Qed.
Lemma lem3688964 {_93692 : Type'} (p : _93692 -> Prop) : term34 _93692 p.
Proof. exact (fun h0 : term32 _93692 p => @lem3688963 _93692 p h0). Qed.
Lemma lem3688965 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term34 _93692 p) : term34 _93692 p.
Proof. exact (h1). Qed.
Lemma lem3688966 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term32 _93692 p) : term32 _93692 p.
Proof. exact (h1). Qed.
Lemma lem3688967 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term32 _93692 p) (h2 : term34 _93692 p) : term32 _93692 p.
Proof. exact (@lem3688965 _93692 p h2 (@lem3688966 _93692 p h1)). Qed.
Lemma lem3688968 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term32 _93692 p) : term35 _93692 p.
Proof. exact (fun h0 : term34 _93692 p => @lem3688967 _93692 p h1 h0). Qed.
Lemma lem3688969 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term34 _93692 p) : term34 _93692 p.
Proof. exact (h1). Qed.
Lemma lem3688970 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term32 _93692 p) (h2 : term34 _93692 p) : term32 _93692 p.
Proof. exact (@lem3688968 _93692 p h1 (@lem3688969 _93692 p h2)). Qed.
Lemma lem3688971 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term34 _93692 p) : term34 _93692 p.
Proof. exact (fun h0 : term32 _93692 p => @lem3688970 _93692 p h0 h1). Qed.
Lemma lem3688972 {_93692 : Type'} (p : _93692 -> Prop) : term36 _93692 p.
Proof. exact (fun h0 : term34 _93692 p => @lem3688971 _93692 p h0). Qed.
Lemma lem3688975 {_93692 : Type'} (p : _93692 -> Prop) : term34 _93692 p.
Proof. exact (@lem3688972 _93692 p (@lem3688964 _93692 p)). Qed.
Lemma lem3688976 {_93692 : Type'} (p : _93692 -> Prop) : term34 _93692 p.
Proof. exact (@lem3688975 _93692 p). Qed.
Lemma lem3688982 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3688983 {_93692 : Type'} (p : _93692 -> Prop) : (term32 _93692 p) = (term37 _93692 p).
Proof. exact (@lem3688982 (term33 _93692 p)). Qed.
Lemma lem3688985 (t : Prop) : (term38 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3688986 {_93692 : Type'} (p : _93692 -> Prop) : (term37 _93692 p) = ((term30 _93692 p) = (term31 _93692 p)).
Proof. exact (@lem3688985 ((term30 _93692 p) = (term31 _93692 p))). Qed.
Lemma lem3688987 {_93692 : Type'} (p : _93692 -> Prop) : (term32 _93692 p) = ((term30 _93692 p) = (term31 _93692 p)).
Proof. exact (TRANS (@lem3688983 _93692 p) (@lem3688986 _93692 p)). Qed.
Lemma lem3688996 {_93692 : Type'} : (term39 _93692) = (term40 _93692).
Proof. exact (fun_ext (fun p : _93692 -> Prop => @lem3688987 _93692 p)). Qed.
Lemma lem3688997 {_93692 : Type'} : (@all (_93692 -> Prop)) = (@all (_93692 -> Prop)).
Proof. exact (eq_refl (@all (_93692 -> Prop))). Qed.
Lemma lem3689006 {_93692 : Type'} : (term41 _93692) = (term42 _93692).
Proof. exact (MK_COMB (@lem3688997 _93692) (@lem3688996 _93692)). Qed.
Lemma lem3689009 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term43 _93692 p t) = (term43 _93692 p t).
Proof. exact (eq_refl (term43 _93692 p t)). Qed.
Lemma lem3689010 {_93692 : Type'} (p : _93692 -> Prop) : (term44 _93692 p) = (term44 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689009 _93692 p t)). Qed.
Lemma lem3689011 {_93692 : Type'} : (@ex _93692) = (@ex _93692).
Proof. exact (eq_refl (@ex _93692)). Qed.
Lemma lem3689012 {_93692 : Type'} (p : _93692 -> Prop) : (term45 _93692 p) = (term45 _93692 p).
Proof. exact (MK_COMB (@lem3689011 _93692) (@lem3689010 _93692 p)). Qed.
Lemma lem3689013 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3689014 {_93692 : Type'} (p : _93692 -> Prop) : (term31 _93692 p) = (term31 _93692 p).
Proof. exact (MK_COMB (@lem3689013) (@lem3689012 _93692 p)). Qed.
Lemma lem3689015 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem3689016 {_93692 : Type'} (p : _93692 -> Prop) : (term46 _93692 p) = (term46 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689015 _93692 p t)). Qed.
Lemma lem3689017 {_93692 : Type'} : (@all _93692) = (@all _93692).
Proof. exact (eq_refl (@all _93692)). Qed.
Lemma lem3689018 {_93692 : Type'} (p : _93692 -> Prop) : (term30 _93692 p) = (term30 _93692 p).
Proof. exact (MK_COMB (@lem3689017 _93692) (@lem3689016 _93692 p)). Qed.
Lemma lem3689019 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3689020 {_93692 : Type'} (p : _93692 -> Prop) : (term47 _93692 p) = (term47 _93692 p).
Proof. exact (MK_COMB (@lem3689019) (@lem3689018 _93692 p)). Qed.
Lemma lem3689021 {_93692 : Type'} (p : _93692 -> Prop) : ((term30 _93692 p) = (term31 _93692 p)) = ((term30 _93692 p) = (term31 _93692 p)).
Proof. exact (MK_COMB (@lem3689020 _93692 p) (@lem3689014 _93692 p)). Qed.
Lemma lem3689022 {_93692 : Type'} : (term40 _93692) = (term40 _93692).
Proof. exact (fun_ext (fun p : _93692 -> Prop => @lem3689021 _93692 p)). Qed.
Lemma lem3689023 {_93692 : Type'} : (@all (_93692 -> Prop)) = (@all (_93692 -> Prop)).
Proof. exact (eq_refl (@all (_93692 -> Prop))). Qed.
Lemma lem3689024 {_93692 : Type'} : (term42 _93692) = (term42 _93692).
Proof. exact (MK_COMB (@lem3689023 _93692) (@lem3689022 _93692)). Qed.
Lemma lem3689045 {_93692 : Type'} : (term41 _93692) = (term42 _93692).
Proof. exact (TRANS (@lem3689006 _93692) (@lem3689024 _93692)). Qed.
Lemma lem3689046 {_93692 : Type'} : (term42 _93692) = (term41 _93692).
Proof. exact (SYM (@lem3689045 _93692)). Qed.
Lemma lem3689048 (p : Prop) : p = (term29 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3689049 {_93692 : Type'} (p : _93692 -> Prop) : ((term30 _93692 p) = (term31 _93692 p)) = (term32 _93692 p).
Proof. exact (@lem3689048 ((term30 _93692 p) = (term31 _93692 p))). Qed.
Lemma lem3689050 {_93692 : Type'} (p : _93692 -> Prop) : (term32 _93692 p) = ((term30 _93692 p) = (term31 _93692 p)).
Proof. exact (SYM (@lem3689049 _93692 p)). Qed.
Lemma lem3689051 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term33 _93692 p) : term33 _93692 p.
Proof. exact (h1). Qed.
Lemma lem3689053 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem3689054 {_93692 : Type'} (P : _93692 -> Prop) : (term48 _93692 P) = (term45 _93692 P).
Proof. exact (@lem18392 _93692 P). Qed.
Lemma lem3689055 {_93692 : Type'} (p : _93692 -> Prop) : (term49 _93692 p) = (term50 _93692 p).
Proof. exact (@lem3689054 _93692 (term46 _93692 p)). Qed.
Lemma lem3689056 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term51 _93692 p t) = (p t).
Proof. exact (eq_refl (term51 _93692 p t)). Qed.
Lemma lem3689057 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3689059 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term52 _93692 p t) = (term43 _93692 p t).
Proof. exact (MK_COMB (@lem3689057) (@lem3689056 _93692 p t)). Qed.
Lemma lem3689060 {_93692 : Type'} (p : _93692 -> Prop) : (term53 _93692 p) = (term44 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689059 _93692 p t)). Qed.
Lemma lem3689061 {_93692 : Type'} : (@ex _93692) = (@ex _93692).
Proof. exact (eq_refl (@ex _93692)). Qed.
Lemma lem3689062 {_93692 : Type'} (p : _93692 -> Prop) : (term50 _93692 p) = (term45 _93692 p).
Proof. exact (MK_COMB (@lem3689061 _93692) (@lem3689060 _93692 p)). Qed.
Lemma lem3689063 {_93692 : Type'} (p : _93692 -> Prop) : (term49 _93692 p) = (term45 _93692 p).
Proof. exact (TRANS (@lem3689055 _93692 p) (@lem3689062 _93692 p)). Qed.
Lemma lem3689064 {_93692 : Type'} (p : _93692 -> Prop) : (term46 _93692 p) = (term46 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689053 _93692 p t)). Qed.
Lemma lem3689065 {_93692 : Type'} : (@all _93692) = (@all _93692).
Proof. exact (eq_refl (@all _93692)). Qed.
Lemma lem3689066 {_93692 : Type'} (p : _93692 -> Prop) : (term30 _93692 p) = (term30 _93692 p).
Proof. exact (MK_COMB (@lem3689065 _93692) (@lem3689064 _93692 p)). Qed.
Lemma lem3689067 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term43 _93692 p t) = (term43 _93692 p t).
Proof. exact (eq_refl (term43 _93692 p t)). Qed.
Lemma lem3689070 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term54 _93692 p t) = (p t).
Proof. exact (@lem16933 (p t)). Qed.
Lemma lem3689071 {_93692 : Type'} (P : _93692 -> Prop) : (term55 _93692 P) = (term56 _93692 P).
Proof. exact (@lem18394 _93692 P). Qed.
Lemma lem3689072 {_93692 : Type'} (p : _93692 -> Prop) : (term31 _93692 p) = (term57 _93692 p).
Proof. exact (@lem3689071 _93692 (term44 _93692 p)). Qed.
Lemma lem3689073 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term58 _93692 p t) = (term43 _93692 p t).
Proof. exact (eq_refl (term58 _93692 p t)). Qed.
Lemma lem3689074 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3689075 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term59 _93692 p t) = (term54 _93692 p t).
Proof. exact (MK_COMB (@lem3689074) (@lem3689073 _93692 p t)). Qed.
Lemma lem3689076 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term59 _93692 p t) = (p t).
Proof. exact (TRANS (@lem3689075 _93692 p t) (@lem3689070 _93692 p t)). Qed.
Lemma lem3689077 {_93692 : Type'} (p : _93692 -> Prop) : (term60 _93692 p) = (term46 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689076 _93692 p t)). Qed.
Lemma lem3689078 {_93692 : Type'} : (@all _93692) = (@all _93692).
Proof. exact (eq_refl (@all _93692)). Qed.
Lemma lem3689079 {_93692 : Type'} (p : _93692 -> Prop) : (term57 _93692 p) = (term30 _93692 p).
Proof. exact (MK_COMB (@lem3689078 _93692) (@lem3689077 _93692 p)). Qed.
Lemma lem3689080 {_93692 : Type'} (p : _93692 -> Prop) : (term31 _93692 p) = (term30 _93692 p).
Proof. exact (TRANS (@lem3689072 _93692 p) (@lem3689079 _93692 p)). Qed.
Lemma lem3689081 {_93692 : Type'} (p : _93692 -> Prop) : (term44 _93692 p) = (term44 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689067 _93692 p t)). Qed.
Lemma lem3689082 {_93692 : Type'} : (@ex _93692) = (@ex _93692).
Proof. exact (eq_refl (@ex _93692)). Qed.
Lemma lem3689083 {_93692 : Type'} (p : _93692 -> Prop) : (term45 _93692 p) = (term45 _93692 p).
Proof. exact (MK_COMB (@lem3689082 _93692) (@lem3689081 _93692 p)). Qed.
Lemma lem3689084 {_93692 : Type'} (p : _93692 -> Prop) : (term61 _93692 p) = (term45 _93692 p).
Proof. exact (@lem16933 (term45 _93692 p)). Qed.
Lemma lem3689085 {_93692 : Type'} (p : _93692 -> Prop) : (term61 _93692 p) = (term45 _93692 p).
Proof. exact (TRANS (@lem3689084 _93692 p) (@lem3689083 _93692 p)). Qed.
Lemma lem3689086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3689087 {_93692 : Type'} (p : _93692 -> Prop) : (term62 _93692 p) = (term63 _93692 p).
Proof. exact (MK_COMB (@lem3689086) (@lem3689063 _93692 p)). Qed.
Lemma lem3689088 {_93692 : Type'} (p : _93692 -> Prop) : (term64 _93692 p) = (term65 _93692 p).
Proof. exact (MK_COMB (@lem3689087 _93692 p) (@lem3689080 _93692 p)). Qed.
Lemma lem3689089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3689090 {_93692 : Type'} (p : _93692 -> Prop) : (term66 _93692 p) = (term66 _93692 p).
Proof. exact (MK_COMB (@lem3689089) (@lem3689066 _93692 p)). Qed.
Lemma lem3689091 {_93692 : Type'} (p : _93692 -> Prop) : (term67 _93692 p) = (term68 _93692 p).
Proof. exact (MK_COMB (@lem3689090 _93692 p) (@lem3689085 _93692 p)). Qed.
Lemma lem3689092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3689093 {_93692 : Type'} (p : _93692 -> Prop) : (term69 _93692 p) = (term70 _93692 p).
Proof. exact (MK_COMB (@lem3689092) (@lem3689091 _93692 p)). Qed.
Lemma lem3689094 {_93692 : Type'} (p : _93692 -> Prop) : (term71 _93692 p) = (term72 _93692 p).
Proof. exact (MK_COMB (@lem3689093 _93692 p) (@lem3689088 _93692 p)). Qed.
Lemma lem3689095 {_93692 : Type'} (p : _93692 -> Prop) : (term33 _93692 p) = (term71 _93692 p).
Proof. exact (@lem17646 (term30 _93692 p) (term31 _93692 p)). Qed.
Lemma lem3689096 {_93692 : Type'} (p : _93692 -> Prop) : (term33 _93692 p) = (term72 _93692 p).
Proof. exact (TRANS (@lem3689095 _93692 p) (@lem3689094 _93692 p)). Qed.
Lemma lem3689115 {A : Type'} (P : Prop) (Q : A -> Prop) : (term73 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3689116 {_93692 : Type'} (P : Prop) (Q : _93692 -> Prop) : (term73 _93692 P Q) = (term74 _93692 P Q).
Proof. exact (@lem3689115 _93692 P Q). Qed.
Lemma lem3689117 {_93692 : Type'} (p : _93692 -> Prop) : (term75 _93692 p) = (term76 _93692 p).
Proof. exact (@lem3689116 _93692 (term30 _93692 p) (term44 _93692 p)). Qed.
Lemma lem3689118 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term58 _93692 p t) = (term43 _93692 p t).
Proof. exact (eq_refl (term58 _93692 p t)). Qed.
Lemma lem3689119 {_93692 : Type'} (p : _93692 -> Prop) : (term77 _93692 p) = (term44 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689118 _93692 p t)). Qed.
Lemma lem3689120 {_93692 : Type'} : (@ex _93692) = (@ex _93692).
Proof. exact (eq_refl (@ex _93692)). Qed.
Lemma lem3689121 {_93692 : Type'} (p : _93692 -> Prop) : (term78 _93692 p) = (term45 _93692 p).
Proof. exact (MK_COMB (@lem3689120 _93692) (@lem3689119 _93692 p)). Qed.
Lemma lem3689122 {_93692 : Type'} (p : _93692 -> Prop) : (term66 _93692 p) = (term66 _93692 p).
Proof. exact (eq_refl (term66 _93692 p)). Qed.
Lemma lem3689123 {_93692 : Type'} (p : _93692 -> Prop) : (term75 _93692 p) = (term68 _93692 p).
Proof. exact (MK_COMB (@lem3689122 _93692 p) (@lem3689121 _93692 p)). Qed.
Lemma lem3689124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3689125 {_93692 : Type'} (p : _93692 -> Prop) : (term79 _93692 p) = (term80 _93692 p).
Proof. exact (MK_COMB (@lem3689124) (@lem3689123 _93692 p)). Qed.
Lemma lem3689126 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term58 _93692 p t) = (term43 _93692 p t).
Proof. exact (eq_refl (term58 _93692 p t)). Qed.
Lemma lem3689127 {_93692 : Type'} (p : _93692 -> Prop) : (term66 _93692 p) = (term66 _93692 p).
Proof. exact (eq_refl (term66 _93692 p)). Qed.
Lemma lem3689128 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term81 _93692 p t) = (term82 _93692 p t).
Proof. exact (MK_COMB (@lem3689127 _93692 p) (@lem3689126 _93692 p t)). Qed.
Lemma lem3689129 {_93692 : Type'} (p : _93692 -> Prop) : (term83 _93692 p) = (term84 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689128 _93692 p t)). Qed.
Lemma lem3689130 {_93692 : Type'} : (@ex _93692) = (@ex _93692).
Proof. exact (eq_refl (@ex _93692)). Qed.
Lemma lem3689131 {_93692 : Type'} (p : _93692 -> Prop) : (term76 _93692 p) = (term85 _93692 p).
Proof. exact (MK_COMB (@lem3689130 _93692) (@lem3689129 _93692 p)). Qed.
Lemma lem3689132 {_93692 : Type'} (p : _93692 -> Prop) : ((term75 _93692 p) = (term76 _93692 p)) = ((term68 _93692 p) = (term85 _93692 p)).
Proof. exact (MK_COMB (@lem3689125 _93692 p) (@lem3689131 _93692 p)). Qed.
Lemma lem3689133 {_93692 : Type'} (p : _93692 -> Prop) : (term68 _93692 p) = (term85 _93692 p).
Proof. exact (EQ_MP (@lem3689132 _93692 p) (@lem3689117 _93692 p)). Qed.
Lemma lem3689134 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3689135 {_93692 : Type'} (p : _93692 -> Prop) : (term70 _93692 p) = (term86 _93692 p).
Proof. exact (MK_COMB (@lem3689134) (@lem3689133 _93692 p)). Qed.
Lemma lem3689137 {A : Type'} (P : A -> Prop) (Q : Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3689138 {_93692 : Type'} (P : _93692 -> Prop) (Q : Prop) : (term87 _93692 P Q) = (term88 _93692 P Q).
Proof. exact (@lem3689137 _93692 P Q). Qed.
Lemma lem3689139 {_93692 : Type'} (p : _93692 -> Prop) : (term89 _93692 p) = (term90 _93692 p).
Proof. exact (@lem3689138 _93692 (term44 _93692 p) (term30 _93692 p)). Qed.
Lemma lem3689140 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term58 _93692 p t) = (term43 _93692 p t).
Proof. exact (eq_refl (term58 _93692 p t)). Qed.
Lemma lem3689141 {_93692 : Type'} (p : _93692 -> Prop) : (term77 _93692 p) = (term44 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689140 _93692 p t)). Qed.
Lemma lem3689142 {_93692 : Type'} : (@ex _93692) = (@ex _93692).
Proof. exact (eq_refl (@ex _93692)). Qed.
Lemma lem3689143 {_93692 : Type'} (p : _93692 -> Prop) : (term78 _93692 p) = (term45 _93692 p).
Proof. exact (MK_COMB (@lem3689142 _93692) (@lem3689141 _93692 p)). Qed.
Lemma lem3689144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3689145 {_93692 : Type'} (p : _93692 -> Prop) : (term91 _93692 p) = (term63 _93692 p).
Proof. exact (MK_COMB (@lem3689144) (@lem3689143 _93692 p)). Qed.
Lemma lem3689146 {_93692 : Type'} (p : _93692 -> Prop) : (term30 _93692 p) = (term30 _93692 p).
Proof. exact (eq_refl (term30 _93692 p)). Qed.
Lemma lem3689147 {_93692 : Type'} (p : _93692 -> Prop) : (term89 _93692 p) = (term65 _93692 p).
Proof. exact (MK_COMB (@lem3689145 _93692 p) (@lem3689146 _93692 p)). Qed.
Lemma lem3689148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3689149 {_93692 : Type'} (p : _93692 -> Prop) : (term92 _93692 p) = (term93 _93692 p).
Proof. exact (MK_COMB (@lem3689148) (@lem3689147 _93692 p)). Qed.
Lemma lem3689150 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term58 _93692 p t) = (term43 _93692 p t).
Proof. exact (eq_refl (term58 _93692 p t)). Qed.
Lemma lem3689151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3689152 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term94 _93692 p t) = (term95 _93692 p t).
Proof. exact (MK_COMB (@lem3689151) (@lem3689150 _93692 p t)). Qed.
Lemma lem3689153 {_93692 : Type'} (p : _93692 -> Prop) : (term30 _93692 p) = (term30 _93692 p).
Proof. exact (eq_refl (term30 _93692 p)). Qed.
Lemma lem3689154 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) : (term96 _93692 t p) = (term97 _93692 t p).
Proof. exact (MK_COMB (@lem3689152 _93692 p t) (@lem3689153 _93692 p)). Qed.
Lemma lem3689155 {_93692 : Type'} (p : _93692 -> Prop) : (term98 _93692 p) = (term99 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689154 _93692 t p)). Qed.
Lemma lem3689156 {_93692 : Type'} : (@ex _93692) = (@ex _93692).
Proof. exact (eq_refl (@ex _93692)). Qed.
Lemma lem3689157 {_93692 : Type'} (p : _93692 -> Prop) : (term90 _93692 p) = (term100 _93692 p).
Proof. exact (MK_COMB (@lem3689156 _93692) (@lem3689155 _93692 p)). Qed.
Lemma lem3689158 {_93692 : Type'} (p : _93692 -> Prop) : ((term89 _93692 p) = (term90 _93692 p)) = ((term65 _93692 p) = (term100 _93692 p)).
Proof. exact (MK_COMB (@lem3689149 _93692 p) (@lem3689157 _93692 p)). Qed.
Lemma lem3689159 {_93692 : Type'} (p : _93692 -> Prop) : (term65 _93692 p) = (term100 _93692 p).
Proof. exact (EQ_MP (@lem3689158 _93692 p) (@lem3689139 _93692 p)). Qed.
Lemma lem3689160 {_93692 : Type'} (p : _93692 -> Prop) : (term72 _93692 p) = (term101 _93692 p).
Proof. exact (MK_COMB (@lem3689135 _93692 p) (@lem3689159 _93692 p)). Qed.
Lemma lem3689162 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3689163 {_93692 : Type'} (P : _93692 -> Prop) (Q : _93692 -> Prop) : (term102 _93692 P Q) = (term103 _93692 P Q).
Proof. exact (@lem3689162 _93692 P Q). Qed.
Lemma lem3689164 {_93692 : Type'} (p : _93692 -> Prop) : (term104 _93692 p) = (term105 _93692 p).
Proof. exact (@lem3689163 _93692 (term84 _93692 p) (term99 _93692 p)). Qed.
Lemma lem3689165 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term106 _93692 p t) = (term82 _93692 p t).
Proof. exact (eq_refl (term106 _93692 p t)). Qed.
Lemma lem3689166 {_93692 : Type'} (p : _93692 -> Prop) : (term107 _93692 p) = (term84 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689165 _93692 p t)). Qed.
Lemma lem3689167 {_93692 : Type'} : (@ex _93692) = (@ex _93692).
Proof. exact (eq_refl (@ex _93692)). Qed.
Lemma lem3689168 {_93692 : Type'} (p : _93692 -> Prop) : (term108 _93692 p) = (term85 _93692 p).
Proof. exact (MK_COMB (@lem3689167 _93692) (@lem3689166 _93692 p)). Qed.
Lemma lem3689169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3689170 {_93692 : Type'} (p : _93692 -> Prop) : (term109 _93692 p) = (term86 _93692 p).
Proof. exact (MK_COMB (@lem3689169) (@lem3689168 _93692 p)). Qed.
Lemma lem3689171 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) : (term110 _93692 p t) = (term97 _93692 t p).
Proof. exact (eq_refl (term110 _93692 p t)). Qed.
Lemma lem3689172 {_93692 : Type'} (p : _93692 -> Prop) : (term111 _93692 p) = (term99 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689171 _93692 t p)). Qed.
Lemma lem3689173 {_93692 : Type'} : (@ex _93692) = (@ex _93692).
Proof. exact (eq_refl (@ex _93692)). Qed.
Lemma lem3689174 {_93692 : Type'} (p : _93692 -> Prop) : (term112 _93692 p) = (term100 _93692 p).
Proof. exact (MK_COMB (@lem3689173 _93692) (@lem3689172 _93692 p)). Qed.
Lemma lem3689175 {_93692 : Type'} (p : _93692 -> Prop) : (term104 _93692 p) = (term101 _93692 p).
Proof. exact (MK_COMB (@lem3689170 _93692 p) (@lem3689174 _93692 p)). Qed.
Lemma lem3689176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3689177 {_93692 : Type'} (p : _93692 -> Prop) : (term113 _93692 p) = (term114 _93692 p).
Proof. exact (MK_COMB (@lem3689176) (@lem3689175 _93692 p)). Qed.
Lemma lem3689178 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term106 _93692 p t) = (term82 _93692 p t).
Proof. exact (eq_refl (term106 _93692 p t)). Qed.
Lemma lem3689179 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3689180 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term115 _93692 p t) = (term116 _93692 p t).
Proof. exact (MK_COMB (@lem3689179) (@lem3689178 _93692 p t)). Qed.
Lemma lem3689181 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) : (term110 _93692 p t) = (term97 _93692 t p).
Proof. exact (eq_refl (term110 _93692 p t)). Qed.
Lemma lem3689182 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) : (term117 _93692 p t) = (term118 _93692 t p).
Proof. exact (MK_COMB (@lem3689180 _93692 p t) (@lem3689181 _93692 t p)). Qed.
Lemma lem3689183 {_93692 : Type'} (p : _93692 -> Prop) : (term119 _93692 p) = (term120 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689182 _93692 t p)). Qed.
Lemma lem3689184 {_93692 : Type'} : (@ex _93692) = (@ex _93692).
Proof. exact (eq_refl (@ex _93692)). Qed.
Lemma lem3689185 {_93692 : Type'} (p : _93692 -> Prop) : (term105 _93692 p) = (term121 _93692 p).
Proof. exact (MK_COMB (@lem3689184 _93692) (@lem3689183 _93692 p)). Qed.
Lemma lem3689186 {_93692 : Type'} (p : _93692 -> Prop) : ((term104 _93692 p) = (term105 _93692 p)) = ((term101 _93692 p) = (term121 _93692 p)).
Proof. exact (MK_COMB (@lem3689177 _93692 p) (@lem3689185 _93692 p)). Qed.
Lemma lem3689187 {_93692 : Type'} (p : _93692 -> Prop) : (term101 _93692 p) = (term121 _93692 p).
Proof. exact (EQ_MP (@lem3689186 _93692 p) (@lem3689164 _93692 p)). Qed.
Lemma lem3689189 {_93692 : Type'} (p : _93692 -> Prop) : (term72 _93692 p) = (term121 _93692 p).
Proof. exact (TRANS (@lem3689160 _93692 p) (@lem3689187 _93692 p)). Qed.
Lemma lem3689190 {_93692 : Type'} (p : _93692 -> Prop) : (term33 _93692 p) = (term121 _93692 p).
Proof. exact (TRANS (@lem3689096 _93692 p) (@lem3689189 _93692 p)). Qed.
Lemma lem3689191 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term33 _93692 p) : term121 _93692 p.
Proof. exact (EQ_MP (@lem3689190 _93692 p) (@lem3689051 _93692 p h1)). Qed.
Lemma lem3689192 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term118 _93692 t p) : term118 _93692 t p.
Proof. exact (h1). Qed.
Lemma lem3689195 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem3689196 {_93692 : Type'} (p : _93692 -> Prop) : (term46 _93692 p) = (term46 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689195 _93692 p t)). Qed.
Lemma lem3689197 {_93692 : Type'} : (@all _93692) = (@all _93692).
Proof. exact (eq_refl (@all _93692)). Qed.
Lemma lem3689198 {_93692 : Type'} (p : _93692 -> Prop) : (term30 _93692 p) = (term30 _93692 p).
Proof. exact (MK_COMB (@lem3689197 _93692) (@lem3689196 _93692 p)). Qed.
Lemma lem3689205 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term95 _93692 p t) = (term95 _93692 p t).
Proof. exact (eq_refl (term95 _93692 p t)). Qed.
Lemma lem3689206 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) : (term97 _93692 t p) = (term97 _93692 t p).
Proof. exact (MK_COMB (@lem3689205 _93692 p t) (@lem3689198 _93692 p)). Qed.
Lemma lem3689211 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term43 _93692 p t) = (term43 _93692 p t).
Proof. exact (eq_refl (term43 _93692 p t)). Qed.
Lemma lem3689214 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem3689215 {_93692 : Type'} (p : _93692 -> Prop) : (term46 _93692 p) = (term46 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689214 _93692 p t)). Qed.
Lemma lem3689216 {_93692 : Type'} : (@all _93692) = (@all _93692).
Proof. exact (eq_refl (@all _93692)). Qed.
Lemma lem3689217 {_93692 : Type'} (p : _93692 -> Prop) : (term30 _93692 p) = (term30 _93692 p).
Proof. exact (MK_COMB (@lem3689216 _93692) (@lem3689215 _93692 p)). Qed.
Lemma lem3689218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3689219 {_93692 : Type'} (p : _93692 -> Prop) : (term66 _93692 p) = (term66 _93692 p).
Proof. exact (MK_COMB (@lem3689218) (@lem3689217 _93692 p)). Qed.
Lemma lem3689220 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term82 _93692 p t) = (term82 _93692 p t).
Proof. exact (MK_COMB (@lem3689219 _93692 p) (@lem3689211 _93692 p t)). Qed.
Lemma lem3689221 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3689222 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term116 _93692 p t) = (term116 _93692 p t).
Proof. exact (MK_COMB (@lem3689221) (@lem3689220 _93692 p t)). Qed.
Lemma lem3689223 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) : (term118 _93692 t p) = (term118 _93692 t p).
Proof. exact (MK_COMB (@lem3689222 _93692 p t) (@lem3689206 _93692 t p)). Qed.
Lemma lem3689224 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term118 _93692 t p) : term118 _93692 t p.
Proof. exact (EQ_MP (@lem3689223 _93692 t p) (@lem3689192 _93692 t p h1)). Qed.
Lemma lem3689225 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) (h1 : term82 _93692 p t) : term82 _93692 p t.
Proof. exact (h1). Qed.
Lemma lem3689226 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term97 _93692 t p) : term97 _93692 t p.
Proof. exact (h1). Qed.
Lemma lem3689228 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) (h1 : term82 _93692 p t) : term30 _93692 p.
Proof. exact (proj1 (@lem3689225 _93692 p t h1)). Qed.
Lemma lem3689229 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term97 _93692 t p) : term30 _93692 p.
Proof. exact (proj2 (@lem3689226 _93692 t p h1)). Qed.
Lemma lem3689232 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem3689233 {_93692 : Type'} (p : _93692 -> Prop) : (term46 _93692 p) = (term46 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689232 _93692 p t)). Qed.
Lemma lem3689234 {_93692 : Type'} : (@all _93692) = (@all _93692).
Proof. exact (eq_refl (@all _93692)). Qed.
Lemma lem3689236 {_93692 : Type'} (p : _93692 -> Prop) : (term30 _93692 p) = (term30 _93692 p).
Proof. exact (MK_COMB (@lem3689234 _93692) (@lem3689233 _93692 p)). Qed.
Lemma lem3689237 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) (h1 : term82 _93692 p t) : term30 _93692 p.
Proof. exact (EQ_MP (@lem3689236 _93692 p) (@lem3689228 _93692 p t h1)). Qed.
Lemma lem3689247 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem3689248 {_93692 : Type'} (p : _93692 -> Prop) : (term46 _93692 p) = (term46 _93692 p).
Proof. exact (fun_ext (fun t : _93692 => @lem3689247 _93692 p t)). Qed.
Lemma lem3689249 {_93692 : Type'} : (@all _93692) = (@all _93692).
Proof. exact (eq_refl (@all _93692)). Qed.
Lemma lem3689251 {_93692 : Type'} (p : _93692 -> Prop) : (term30 _93692 p) = (term30 _93692 p).
Proof. exact (MK_COMB (@lem3689249 _93692) (@lem3689248 _93692 p)). Qed.
Lemma lem3689252 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term97 _93692 t p) : term30 _93692 p.
Proof. exact (EQ_MP (@lem3689251 _93692 p) (@lem3689229 _93692 t p h1)). Qed.
Lemma lem3689253 {_93692 : Type'} (_42424 : _93692) (p : _93692 -> Prop) (t : _93692) (h1 : term82 _93692 p t) : term51 _93692 p _42424.
Proof. exact (@lem3689237 _93692 p t h1 _42424). Qed.
Lemma lem3689254 {_93692 : Type'} (p : _93692 -> Prop) (_42424 : _93692) : (term51 _93692 p _42424) = (p _42424).
Proof. exact (eq_refl (term51 _93692 p _42424)). Qed.
Lemma lem3689256 {_93692 : Type'} (_42425 : _93692) (t : _93692) (p : _93692 -> Prop) (h1 : term97 _93692 t p) : term51 _93692 p _42425.
Proof. exact (@lem3689252 _93692 t p h1 _42425). Qed.
Lemma lem3689257 {_93692 : Type'} (p : _93692 -> Prop) (_42425 : _93692) : (term51 _93692 p _42425) = (p _42425).
Proof. exact (eq_refl (term51 _93692 p _42425)). Qed.
Lemma lem3689262 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) (h1 : term82 _93692 p t) : term43 _93692 p t.
Proof. exact (proj2 (@lem3689225 _93692 p t h1)). Qed.
Lemma lem3689264 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term97 _93692 t p) : term43 _93692 p t.
Proof. exact (proj1 (@lem3689226 _93692 t p h1)). Qed.
Lemma lem3689268 {_93692 : Type'} (_42424 : _93692) (p : _93692 -> Prop) (t : _93692) (h1 : term82 _93692 p t) : p _42424.
Proof. exact (EQ_MP (@lem3689254 _93692 p _42424) (@lem3689253 _93692 _42424 p t h1)). Qed.
Lemma lem3689269 {_93692 : Type'} (_42424 : _93692) (p : _93692 -> Prop) (t : _93692) (h1 : term82 _93692 p t) : p _42424.
Proof. exact (@lem3689268 _93692 _42424 p t h1). Qed.
Lemma lem3689270 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) (h1 : term82 _93692 p t) : p t.
Proof. exact (@lem3689269 _93692 t p t h1). Qed.
Lemma lem3689271 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) (h1 : term82 _93692 p t) : term122 _93692 p t.
Proof. exact (fun h0 : term43 _93692 p t => @lem3689270 _93692 p t h1). Qed.
Lemma lem3689273 (p : Prop) : (term123 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3689274 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term122 _93692 p t) = (p t).
Proof. exact (@lem3689273 (p t)). Qed.
Lemma lem3689275 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) (h1 : term82 _93692 p t) : p t.
Proof. exact (EQ_MP (@lem3689274 _93692 p t) (@lem3689271 _93692 p t h1)). Qed.
Lemma lem3689278 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3689280 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term43 _93692 p t) = (term124 _93692 p t).
Proof. exact (@lem3689278 (p t)). Qed.
Lemma lem3689283 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) (h1 : term82 _93692 p t) : term124 _93692 p t.
Proof. exact (EQ_MP (@lem3689280 _93692 p t) (@lem3689262 _93692 p t h1)). Qed.
Lemma lem3689286 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) (h1 : term82 _93692 p t) : False.
Proof. exact (@lem3689283 _93692 p t h1 (@lem3689275 _93692 p t h1)). Qed.
Lemma lem3689287 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) (h1 : term82 _93692 p t) : term125.
Proof. exact (fun h0 : ~ False => @lem3689286 _93692 p t h1). Qed.
Lemma lem3689289 (p : Prop) : (term123 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3689290 : term125 = False.
Proof. exact (@lem3689289 False). Qed.
Lemma lem3689291 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) (h1 : term82 _93692 p t) : False.
Proof. exact (EQ_MP (@lem3689290) (@lem3689287 _93692 p t h1)). Qed.
Lemma lem3689293 {_93692 : Type'} (_42425 : _93692) (t : _93692) (p : _93692 -> Prop) (h1 : term97 _93692 t p) : p _42425.
Proof. exact (EQ_MP (@lem3689257 _93692 p _42425) (@lem3689256 _93692 _42425 t p h1)). Qed.
Lemma lem3689294 {_93692 : Type'} (_42425 : _93692) (t : _93692) (p : _93692 -> Prop) (h1 : term97 _93692 t p) : p _42425.
Proof. exact (@lem3689293 _93692 _42425 t p h1). Qed.
Lemma lem3689295 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term97 _93692 t p) : p t.
Proof. exact (@lem3689294 _93692 t t p h1). Qed.
Lemma lem3689296 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term97 _93692 t p) : term122 _93692 p t.
Proof. exact (fun h0 : term43 _93692 p t => @lem3689295 _93692 t p h1). Qed.
Lemma lem3689298 (p : Prop) : (term123 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3689299 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term122 _93692 p t) = (p t).
Proof. exact (@lem3689298 (p t)). Qed.
Lemma lem3689300 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term97 _93692 t p) : p t.
Proof. exact (EQ_MP (@lem3689299 _93692 p t) (@lem3689296 _93692 t p h1)). Qed.
Lemma lem3689303 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3689305 {_93692 : Type'} (p : _93692 -> Prop) (t : _93692) : (term43 _93692 p t) = (term124 _93692 p t).
Proof. exact (@lem3689303 (p t)). Qed.
Lemma lem3689308 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term97 _93692 t p) : term124 _93692 p t.
Proof. exact (EQ_MP (@lem3689305 _93692 p t) (@lem3689264 _93692 t p h1)). Qed.
Lemma lem3689311 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term97 _93692 t p) : False.
Proof. exact (@lem3689308 _93692 t p h1 (@lem3689300 _93692 t p h1)). Qed.
Lemma lem3689312 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term97 _93692 t p) : term125.
Proof. exact (fun h0 : ~ False => @lem3689311 _93692 t p h1). Qed.
Lemma lem3689314 (p : Prop) : (term123 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3689315 : term125 = False.
Proof. exact (@lem3689314 False). Qed.
Lemma lem3689316 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term97 _93692 t p) : False.
Proof. exact (EQ_MP (@lem3689315) (@lem3689312 _93692 t p h1)). Qed.
Lemma lem3689317 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term118 _93692 t p) : False.
Proof. exact (or_elim (@lem3689224 _93692 t p h1) (fun h0 : term82 _93692 p t => @lem3689291 _93692 p t h0) (fun h0 : term97 _93692 t p => @lem3689316 _93692 t p h0)). Qed.
Lemma lem3689318 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term118 _93692 t p) : (term118 _93692 t p) = False.
Proof. exact (prop_ext (fun h2 : term118 _93692 t p => @lem3689317 _93692 t p h1) (fun h2 : False => @lem3689224 _93692 t p h1)). Qed.
Lemma lem3689319 {_93692 : Type'} (t : _93692) (p : _93692 -> Prop) (h1 : term118 _93692 t p) : False.
Proof. exact (EQ_MP (@lem3689318 _93692 t p h1) (@lem3689224 _93692 t p h1)). Qed.
Lemma lem3689320 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term33 _93692 p) : False.
Proof. exact (ex_elim (@lem3689191 _93692 p h1) (fun t : _93692 => fun h0 : term120 _93692 p t => @lem3689319 _93692 t p h0)). Qed.
Lemma lem3689321 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term33 _93692 p) : (term33 _93692 p) = False.
Proof. exact (prop_ext (fun h2 : term33 _93692 p => @lem3689320 _93692 p h1) (fun h2 : False => @lem3689051 _93692 p h1)). Qed.
Lemma lem3689322 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term33 _93692 p) : False.
Proof. exact (EQ_MP (@lem3689321 _93692 p h1) (@lem3689051 _93692 p h1)). Qed.
Lemma lem3689323 {_93692 : Type'} (p : _93692 -> Prop) : term32 _93692 p.
Proof. exact (fun h0 : term33 _93692 p => @lem3689322 _93692 p h0). Qed.
Lemma lem3689324 {_93692 : Type'} (p : _93692 -> Prop) : (term30 _93692 p) = (term31 _93692 p).
Proof. exact (EQ_MP (@lem3689050 _93692 p) (@lem3689323 _93692 p)). Qed.
Lemma lem3689329 {_93692 : Type'} : term42 _93692.
Proof. exact (fun p : _93692 -> Prop => @lem3689324 _93692 p). Qed.
Lemma lem3689330 {_93692 : Type'} : term41 _93692.
Proof. exact (EQ_MP (@lem3689046 _93692) (@lem3689329 _93692)). Qed.
Lemma lem3689331 {_93692 : Type'} (p : _93692 -> Prop) : term126 _93692 p.
Proof. exact (@lem3689330 _93692 p). Qed.
Lemma lem3689332 {_93692 : Type'} (p : _93692 -> Prop) : (term126 _93692 p) = (term32 _93692 p).
Proof. exact (eq_refl (term126 _93692 p)). Qed.
Lemma lem3689333 {_93692 : Type'} (p : _93692 -> Prop) : term32 _93692 p.
Proof. exact (EQ_MP (@lem3689332 _93692 p) (@lem3689331 _93692 p)). Qed.
Lemma lem3689335 {_93692 : Type'} (p : _93692 -> Prop) : term32 _93692 p.
Proof. exact (@lem3688976 _93692 p (@lem3689333 _93692 p)). Qed.
Lemma lem3689336 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term33 _93692 p) : False.
Proof. exact (@lem3689335 _93692 p (@lem3688960 _93692 p h1)). Qed.
Lemma lem3689337 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term33 _93692 p) : (term33 _93692 p) = False.
Proof. exact (prop_ext (fun h2 : term33 _93692 p => @lem3689336 _93692 p h1) (fun h2 : False => @lem3688960 _93692 p h1)). Qed.
Lemma lem3689338 {_93692 : Type'} (p : _93692 -> Prop) (h1 : term33 _93692 p) : False.
Proof. exact (EQ_MP (@lem3689337 _93692 p h1) (@lem3688960 _93692 p h1)). Qed.
Lemma lem3689339 {_93692 : Type'} (p : _93692 -> Prop) : term32 _93692 p.
Proof. exact (fun h0 : term33 _93692 p => @lem3689338 _93692 p h0). Qed.
Lemma lem3689348 {_93692 : Type'} (p : _93692 -> Prop) : (term30 _93692 p) = (term31 _93692 p).
Proof. exact (EQ_MP (@lem3688959 _93692 p) (@lem3689339 _93692 p)). Qed.
Lemma lem3689349 {_93773 : Type'} (p : type686 _93773) : (term127 _93773 p) = (term128 _93773 p).
Proof. exact (@lem3689348 (_93773 -> Prop) p). Qed.
Lemma lem3689350 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : (term129 _93766 _93773 f s P) = (term130 _93766 _93773 f s P).
Proof. exact (@lem3689349 _93773 (term131 _93766 _93773 f s P)). Qed.
Lemma lem3689351 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) (t : _93773 -> Prop) : (term132 _93766 _93773 f s P t) = (term133 _93766 _93773 f s P t).
Proof. exact (eq_refl (term132 _93766 _93773 f s P t)). Qed.
Lemma lem3689352 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : (term134 _93766 _93773 f s P) = (term131 _93766 _93773 f s P).
Proof. exact (fun_ext (fun t : _93773 -> Prop => @lem3689351 _93766 _93773 f s P t)). Qed.
Lemma lem3689353 {_93773 : Type'} : (@all (_93773 -> Prop)) = (@all (_93773 -> Prop)).
Proof. exact (eq_refl (@all (_93773 -> Prop))). Qed.
Lemma lem3689354 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : (term129 _93766 _93773 f s P) = (term135 _93766 _93773 f s P).
Proof. exact (MK_COMB (@lem3689353 _93773) (@lem3689352 _93766 _93773 f s P)). Qed.
Lemma lem3689355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3689356 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : (term136 _93766 _93773 f s P) = (term137 _93766 _93773 f s P).
Proof. exact (MK_COMB (@lem3689355) (@lem3689354 _93766 _93773 f s P)). Qed.
Lemma lem3689357 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) (t : _93773 -> Prop) : (term132 _93766 _93773 f s P t) = (term133 _93766 _93773 f s P t).
Proof. exact (eq_refl (term132 _93766 _93773 f s P t)). Qed.
Lemma lem3689358 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3689359 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) (t : _93773 -> Prop) : (term138 _93766 _93773 f s P t) = (term139 _93766 _93773 f s P t).
Proof. exact (MK_COMB (@lem3689358) (@lem3689357 _93766 _93773 f s P t)). Qed.
Lemma lem3689360 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : (term140 _93766 _93773 f s P) = (term141 _93766 _93773 f s P).
Proof. exact (fun_ext (fun t : _93773 -> Prop => @lem3689359 _93766 _93773 f s P t)). Qed.
Lemma lem3689361 {_93773 : Type'} : (@ex (_93773 -> Prop)) = (@ex (_93773 -> Prop)).
Proof. exact (eq_refl (@ex (_93773 -> Prop))). Qed.
Lemma lem3689362 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : (term142 _93766 _93773 f s P) = (term143 _93766 _93773 f s P).
Proof. exact (MK_COMB (@lem3689361 _93773) (@lem3689360 _93766 _93773 f s P)). Qed.
Lemma lem3689363 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3689364 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : (term130 _93766 _93773 f s P) = (term144 _93766 _93773 f s P).
Proof. exact (MK_COMB (@lem3689363) (@lem3689362 _93766 _93773 f s P)). Qed.
Lemma lem3689365 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : ((term129 _93766 _93773 f s P) = (term130 _93766 _93773 f s P)) = ((term135 _93766 _93773 f s P) = (term144 _93766 _93773 f s P)).
Proof. exact (MK_COMB (@lem3689356 _93766 _93773 f s P) (@lem3689364 _93766 _93773 f s P)). Qed.
Lemma lem3689366 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : (term135 _93766 _93773 f s P) = (term144 _93766 _93773 f s P).
Proof. exact (EQ_MP (@lem3689365 _93766 _93773 f s P) (@lem3689350 _93766 _93773 f s P)). Qed.
Lemma lem3689367 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3689368 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : (term137 _93766 _93773 f s P) = (term145 _93766 _93773 f s P).
Proof. exact (MK_COMB (@lem3689367) (@lem3689366 _93766 _93773 f s P)). Qed.
Lemma lem3689374 {_93692 : Type'} (p : _93692 -> Prop) : (term30 _93692 p) = (term31 _93692 p).
Proof. exact (EQ_MP (@lem3688959 _93692 p) (@lem3689339 _93692 p)). Qed.
Lemma lem3689375 {_93766 : Type'} (p : type686 _93766) : (term127 _93766 p) = (term128 _93766 p).
Proof. exact (@lem3689374 (_93766 -> Prop) p). Qed.
Lemma lem3689376 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term146 _93766 _93773 s P f) = (term147 _93766 _93773 s P f).
Proof. exact (@lem3689375 _93766 (term148 _93766 _93773 s P f)). Qed.
Lemma lem3689377 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) (t : _93766 -> Prop) : (term149 _93766 _93773 s P f t) = (term150 _93766 _93773 s P f t).
Proof. exact (eq_refl (term149 _93766 _93773 s P f t)). Qed.
Lemma lem3689378 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term151 _93766 _93773 s P f) = (term148 _93766 _93773 s P f).
Proof. exact (fun_ext (fun t : _93766 -> Prop => @lem3689377 _93766 _93773 s P f t)). Qed.
Lemma lem3689379 {_93766 : Type'} : (@all (_93766 -> Prop)) = (@all (_93766 -> Prop)).
Proof. exact (eq_refl (@all (_93766 -> Prop))). Qed.
Lemma lem3689380 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term146 _93766 _93773 s P f) = (term152 _93766 _93773 s P f).
Proof. exact (MK_COMB (@lem3689379 _93766) (@lem3689378 _93766 _93773 s P f)). Qed.
Lemma lem3689381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3689382 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term153 _93766 _93773 s P f) = (term154 _93766 _93773 s P f).
Proof. exact (MK_COMB (@lem3689381) (@lem3689380 _93766 _93773 s P f)). Qed.
Lemma lem3689383 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) (t : _93766 -> Prop) : (term149 _93766 _93773 s P f t) = (term150 _93766 _93773 s P f t).
Proof. exact (eq_refl (term149 _93766 _93773 s P f t)). Qed.
Lemma lem3689384 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3689385 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) (t : _93766 -> Prop) : (term155 _93766 _93773 s P f t) = (term156 _93766 _93773 s P f t).
Proof. exact (MK_COMB (@lem3689384) (@lem3689383 _93766 _93773 s P f t)). Qed.
Lemma lem3689386 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term157 _93766 _93773 s P f) = (term158 _93766 _93773 s P f).
Proof. exact (fun_ext (fun t : _93766 -> Prop => @lem3689385 _93766 _93773 s P f t)). Qed.
Lemma lem3689387 {_93766 : Type'} : (@ex (_93766 -> Prop)) = (@ex (_93766 -> Prop)).
Proof. exact (eq_refl (@ex (_93766 -> Prop))). Qed.
Lemma lem3689388 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term159 _93766 _93773 s P f) = (term160 _93766 _93773 s P f).
Proof. exact (MK_COMB (@lem3689387 _93766) (@lem3689386 _93766 _93773 s P f)). Qed.
Lemma lem3689389 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3689390 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term147 _93766 _93773 s P f) = (term161 _93766 _93773 s P f).
Proof. exact (MK_COMB (@lem3689389) (@lem3689388 _93766 _93773 s P f)). Qed.
Lemma lem3689391 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : ((term146 _93766 _93773 s P f) = (term147 _93766 _93773 s P f)) = ((term152 _93766 _93773 s P f) = (term161 _93766 _93773 s P f)).
Proof. exact (MK_COMB (@lem3689382 _93766 _93773 s P f) (@lem3689390 _93766 _93773 s P f)). Qed.
Lemma lem3689392 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term152 _93766 _93773 s P f) = (term161 _93766 _93773 s P f).
Proof. exact (EQ_MP (@lem3689391 _93766 _93773 s P f) (@lem3689376 _93766 _93773 s P f)). Qed.
Lemma lem3689393 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : ((term135 _93766 _93773 f s P) = (term152 _93766 _93773 s P f)) = ((term144 _93766 _93773 f s P) = (term161 _93766 _93773 s P f)).
Proof. exact (MK_COMB (@lem3689368 _93766 _93773 f s P) (@lem3689392 _93766 _93773 s P f)). Qed.
Lemma lem3689394 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : ((term144 _93766 _93773 f s P) = (term161 _93766 _93773 s P f)) = ((term135 _93766 _93773 f s P) = (term152 _93766 _93773 s P f)).
Proof. exact (SYM (@lem3689393 _93766 _93773 s P f)). Qed.
Lemma lem3689402 (t1 : Prop) (t2 : Prop) : (term27 t1 t2) = (term28 t1 t2).
Proof. exact (EQ_MP (@lem3688944 t1 t2) (@lem3688943 t1 t2)). Qed.
Lemma lem3689403 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) (t : _93773 -> Prop) : (term139 _93766 _93773 f s P t) = (term162 _93766 _93773 f s P t).
Proof. exact (@lem3689402 (term163 _93766 _93773 t f s) (P t)). Qed.
Lemma lem3689405 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem3688929 t1 t2 t3) (@lem3688928 t1 t2 t3)). Qed.
Lemma lem3689406 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) (t : _93773 -> Prop) : (term162 _93766 _93773 f s P t) = (term164 _93766 _93773 f s P t).
Proof. exact (@lem3689405 (@FINITE _93773 t) (term165 _93766 _93773 t f s) (term166 _93773 P t)). Qed.
Lemma lem3689409 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) (t : _93773 -> Prop) : (term139 _93766 _93773 f s P t) = (term164 _93766 _93773 f s P t).
Proof. exact (TRANS (@lem3689403 _93766 _93773 f s P t) (@lem3689406 _93766 _93773 f s P t)). Qed.
Lemma lem3689412 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : (term141 _93766 _93773 f s P) = (term167 _93766 _93773 f s P).
Proof. exact (fun_ext (fun t : _93773 -> Prop => @lem3689409 _93766 _93773 f s P t)). Qed.
Lemma lem3689413 {_93773 : Type'} : (@ex (_93773 -> Prop)) = (@ex (_93773 -> Prop)).
Proof. exact (eq_refl (@ex (_93773 -> Prop))). Qed.
Lemma lem3689414 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : (term143 _93766 _93773 f s P) = (term168 _93766 _93773 f s P).
Proof. exact (MK_COMB (@lem3689413 _93773) (@lem3689412 _93766 _93773 f s P)). Qed.
Lemma lem3689416 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term22 _93670 _93677 f s P) = (term23 _93670 _93677 s P f).
Proof. exact (EQ_MP (@lem3688938 _93670 _93677 s P f) (@lem3688937 _93670 _93677 P f s)). Qed.
Lemma lem3689417 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term22 _93766 _93773 f s P) = (term23 _93766 _93773 s P f).
Proof. exact (@lem3689416 _93766 _93773 s P f). Qed.
Lemma lem3689418 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term169 _93766 _93773 f s P) = (term170 _93766 _93773 s P f).
Proof. exact (@lem3689417 _93766 _93773 s (term171 _93773 P) f). Qed.
Lemma lem3689419 {_93773 : Type'} (P : type686 _93773) (t : _93773 -> Prop) : (term172 _93773 P t) = (term166 _93773 P t).
Proof. exact (eq_refl (term172 _93773 P t)). Qed.
Lemma lem3689420 {_93766 _93773 : Type'} (t : _93773 -> Prop) (f : _93766 -> _93773) (s : _93766 -> Prop) : (term173 _93766 _93773 t f s) = (term173 _93766 _93773 t f s).
Proof. exact (eq_refl (term173 _93766 _93773 t f s)). Qed.
Lemma lem3689421 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) (t : _93773 -> Prop) : (term174 _93766 _93773 f s P t) = (term175 _93766 _93773 f s P t).
Proof. exact (MK_COMB (@lem3689420 _93766 _93773 t f s) (@lem3689419 _93773 P t)). Qed.
Lemma lem3689422 {_93773 : Type'} (t : _93773 -> Prop) : (term176 _93773 t) = (term176 _93773 t).
Proof. exact (eq_refl (term176 _93773 t)). Qed.
Lemma lem3689423 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) (t : _93773 -> Prop) : (term177 _93766 _93773 f s P t) = (term164 _93766 _93773 f s P t).
Proof. exact (MK_COMB (@lem3689422 _93773 t) (@lem3689421 _93766 _93773 f s P t)). Qed.
Lemma lem3689424 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : (term178 _93766 _93773 f s P) = (term167 _93766 _93773 f s P).
Proof. exact (fun_ext (fun t : _93773 -> Prop => @lem3689423 _93766 _93773 f s P t)). Qed.
Lemma lem3689425 {_93773 : Type'} : (@ex (_93773 -> Prop)) = (@ex (_93773 -> Prop)).
Proof. exact (eq_refl (@ex (_93773 -> Prop))). Qed.
Lemma lem3689426 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : (term169 _93766 _93773 f s P) = (term168 _93766 _93773 f s P).
Proof. exact (MK_COMB (@lem3689425 _93773) (@lem3689424 _93766 _93773 f s P)). Qed.
Lemma lem3689427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3689428 {_93766 _93773 : Type'} (f : _93766 -> _93773) (s : _93766 -> Prop) (P : type686 _93773) : (term179 _93766 _93773 f s P) = (term180 _93766 _93773 f s P).
Proof. exact (MK_COMB (@lem3689427) (@lem3689426 _93766 _93773 f s P)). Qed.
Lemma lem3689429 {_93766 _93773 : Type'} (P : type686 _93773) (f : _93766 -> _93773) (t : _93766 -> Prop) : (term181 _93766 _93773 P f t) = (term182 _93766 _93773 P f t).
Proof. exact (eq_refl (term181 _93766 _93773 P f t)). Qed.
Lemma lem3689430 {_93766 _93773 : Type'} (t : _93766 -> Prop) (f : _93766 -> _93773) : (term183 _93766 _93773 t f) = (term183 _93766 _93773 t f).
Proof. exact (eq_refl (term183 _93766 _93773 t f)). Qed.
Lemma lem3689431 {_93766 _93773 : Type'} (P : type686 _93773) (f : _93766 -> _93773) (t : _93766 -> Prop) : (term184 _93766 _93773 P f t) = (term185 _93766 _93773 P f t).
Proof. exact (MK_COMB (@lem3689430 _93766 _93773 t f) (@lem3689429 _93766 _93773 P f t)). Qed.
Lemma lem3689432 {_93766 : Type'} (t : _93766 -> Prop) (s : _93766 -> Prop) : (term186 _93766 t s) = (term186 _93766 t s).
Proof. exact (eq_refl (term186 _93766 t s)). Qed.
Lemma lem3689433 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) (t : _93766 -> Prop) : (term187 _93766 _93773 s P f t) = (term188 _93766 _93773 s P f t).
Proof. exact (MK_COMB (@lem3689432 _93766 t s) (@lem3689431 _93766 _93773 P f t)). Qed.
Lemma lem3689434 {_93766 : Type'} (t : _93766 -> Prop) : (term176 _93766 t) = (term176 _93766 t).
Proof. exact (eq_refl (term176 _93766 t)). Qed.
Lemma lem3689435 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) (t : _93766 -> Prop) : (term189 _93766 _93773 s P f t) = (term190 _93766 _93773 s P f t).
Proof. exact (MK_COMB (@lem3689434 _93766 t) (@lem3689433 _93766 _93773 s P f t)). Qed.
Lemma lem3689436 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term191 _93766 _93773 s P f) = (term192 _93766 _93773 s P f).
Proof. exact (fun_ext (fun t : _93766 -> Prop => @lem3689435 _93766 _93773 s P f t)). Qed.
Lemma lem3689437 {_93766 : Type'} : (@ex (_93766 -> Prop)) = (@ex (_93766 -> Prop)).
Proof. exact (eq_refl (@ex (_93766 -> Prop))). Qed.
Lemma lem3689438 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term170 _93766 _93773 s P f) = (term193 _93766 _93773 s P f).
Proof. exact (MK_COMB (@lem3689437 _93766) (@lem3689436 _93766 _93773 s P f)). Qed.
Lemma lem3689439 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : ((term169 _93766 _93773 f s P) = (term170 _93766 _93773 s P f)) = ((term168 _93766 _93773 f s P) = (term193 _93766 _93773 s P f)).
Proof. exact (MK_COMB (@lem3689428 _93766 _93773 f s P) (@lem3689438 _93766 _93773 s P f)). Qed.
Lemma lem3689440 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term168 _93766 _93773 f s P) = (term193 _93766 _93773 s P f).
Proof. exact (EQ_MP (@lem3689439 _93766 _93773 s P f) (@lem3689418 _93766 _93773 s P f)). Qed.
Lemma lem3689469 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term143 _93766 _93773 f s P) = (term193 _93766 _93773 s P f).
Proof. exact (TRANS (@lem3689414 _93766 _93773 f s P) (@lem3689440 _93766 _93773 s P f)). Qed.
Lemma lem3689470 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3689471 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term144 _93766 _93773 f s P) = (term194 _93766 _93773 s P f).
Proof. exact (MK_COMB (@lem3689470) (@lem3689469 _93766 _93773 s P f)). Qed.
Lemma lem3689472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3689473 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term145 _93766 _93773 f s P) = (term195 _93766 _93773 s P f).
Proof. exact (MK_COMB (@lem3689472) (@lem3689471 _93766 _93773 s P f)). Qed.
Lemma lem3689479 (t1 : Prop) (t2 : Prop) : (term27 t1 t2) = (term28 t1 t2).
Proof. exact (EQ_MP (@lem3688944 t1 t2) (@lem3688943 t1 t2)). Qed.
Lemma lem3689480 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) (t : _93766 -> Prop) : (term156 _93766 _93773 s P f t) = (term196 _93766 _93773 s P f t).
Proof. exact (@lem3689479 (term197 _93766 _93773 s t f) (term198 _93766 _93773 P f t)). Qed.
Lemma lem3689482 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem3688929 t1 t2 t3) (@lem3688928 t1 t2 t3)). Qed.
Lemma lem3689483 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) (t : _93766 -> Prop) : (term196 _93766 _93773 s P f t) = (term199 _93766 _93773 s P f t).
Proof. exact (@lem3689482 (@FINITE _93766 t) (term200 _93766 _93773 s t f) (term182 _93766 _93773 P f t)). Qed.
Lemma lem3689486 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) (t : _93766 -> Prop) : (term156 _93766 _93773 s P f t) = (term199 _93766 _93773 s P f t).
Proof. exact (TRANS (@lem3689480 _93766 _93773 s P f t) (@lem3689483 _93766 _93773 s P f t)). Qed.
Lemma lem3689488 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem3688929 t1 t2 t3) (@lem3688928 t1 t2 t3)). Qed.
Lemma lem3689489 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) (t : _93766 -> Prop) : (term201 _93766 _93773 s P f t) = (term188 _93766 _93773 s P f t).
Proof. exact (@lem3689488 (@SUBSET _93766 t s) (term202 _93766 _93773 t f) (term182 _93766 _93773 P f t)). Qed.
Lemma lem3689512 {_93766 : Type'} (t : _93766 -> Prop) : (term176 _93766 t) = (term176 _93766 t).
Proof. exact (eq_refl (term176 _93766 t)). Qed.
Lemma lem3689513 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) (t : _93766 -> Prop) : (term199 _93766 _93773 s P f t) = (term190 _93766 _93773 s P f t).
Proof. exact (MK_COMB (@lem3689512 _93766 t) (@lem3689489 _93766 _93773 s P f t)). Qed.
Lemma lem3689516 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) (t : _93766 -> Prop) : (term156 _93766 _93773 s P f t) = (term190 _93766 _93773 s P f t).
Proof. exact (TRANS (@lem3689486 _93766 _93773 s P f t) (@lem3689513 _93766 _93773 s P f t)). Qed.
Lemma lem3689517 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term158 _93766 _93773 s P f) = (term192 _93766 _93773 s P f).
Proof. exact (fun_ext (fun t : _93766 -> Prop => @lem3689516 _93766 _93773 s P f t)). Qed.
Lemma lem3689518 {_93766 : Type'} : (@ex (_93766 -> Prop)) = (@ex (_93766 -> Prop)).
Proof. exact (eq_refl (@ex (_93766 -> Prop))). Qed.
Lemma lem3689519 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term160 _93766 _93773 s P f) = (term193 _93766 _93773 s P f).
Proof. exact (MK_COMB (@lem3689518 _93766) (@lem3689517 _93766 _93773 s P f)). Qed.
Lemma lem3689524 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3689525 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term161 _93766 _93773 s P f) = (term194 _93766 _93773 s P f).
Proof. exact (MK_COMB (@lem3689524) (@lem3689519 _93766 _93773 s P f)). Qed.
Lemma lem3689526 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : ((term144 _93766 _93773 f s P) = (term161 _93766 _93773 s P f)) = ((term194 _93766 _93773 s P f) = (term194 _93766 _93773 s P f)).
Proof. exact (MK_COMB (@lem3689473 _93766 _93773 s P f) (@lem3689525 _93766 _93773 s P f)). Qed.
Lemma lem3689528 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3689529 (x : Prop) : (x = x) = True.
Proof. exact (@lem3689528 Prop x). Qed.
Lemma lem3689530 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : ((term194 _93766 _93773 s P f) = (term194 _93766 _93773 s P f)) = True.
Proof. exact (@lem3689529 (term194 _93766 _93773 s P f)). Qed.
Lemma lem3689531 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : ((term144 _93766 _93773 f s P) = (term161 _93766 _93773 s P f)) = True.
Proof. exact (TRANS (@lem3689526 _93766 _93773 s P f) (@lem3689530 _93766 _93773 s P f)). Qed.
Lemma lem3689532 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : True = ((term144 _93766 _93773 f s P) = (term161 _93766 _93773 s P f)).
Proof. exact (SYM (@lem3689531 _93766 _93773 s P f)). Qed.
Lemma lem3689533 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term144 _93766 _93773 f s P) = (term161 _93766 _93773 s P f).
Proof. exact (EQ_MP (@lem3689532 _93766 _93773 s P f) (@lem0)). Qed.
Lemma lem3689534 {_93766 _93773 : Type'} (s : _93766 -> Prop) (P : type686 _93773) (f : _93766 -> _93773) : (term135 _93766 _93773 f s P) = (term152 _93766 _93773 s P f).
Proof. exact (EQ_MP (@lem3689394 _93766 _93773 s P f) (@lem3689533 _93766 _93773 s P f)). Qed.
Lemma lem3689539 {_93766 _93773 : Type'} (P : type686 _93773) (f : _93766 -> _93773) : term203 _93766 _93773 P f.
Proof. exact (fun s : _93766 -> Prop => @lem3689534 _93766 _93773 s P f). Qed.
Lemma lem3689544 {_93766 _93773 : Type'} (P : type686 _93773) : term204 _93766 _93773 P.
Proof. exact (fun f : _93766 -> _93773 => @lem3689539 _93766 _93773 P f). Qed.
Lemma lem3689549 {_93766 _93773 : Type'} : term205 _93766 _93773.
Proof. exact (fun P : type686 _93773 => @lem3689544 _93766 _93773 P). Qed.
