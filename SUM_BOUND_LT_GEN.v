Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_BOUND_LT_GEN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_0_spec.
Require Import REAL_DIV_LMUL_spec.
Require Import SUM_BOUND_LT_ALL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1340231_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem7142724 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7142725 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7142726 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7142725 t1) (@lem7142724 t1)). Qed.
Lemma lem7142727 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7142726 t1 t2). Qed.
Lemma lem7142728 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7142729 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7142728 t1 t2) (@lem7142727 t1 t2)). Qed.
Lemma lem7142730 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7142729 t1 t2 t3). Qed.
Lemma lem7142731 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7142732 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7142731 t1 t2 t3) (@lem7142730 t1 t2 t3)). Qed.
Lemma lem7142733 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7142732 t1 t2 t3)). Qed.
Lemma lem7142735 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7142736 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (@lem7142735 (term8 A)). Qed.
Lemma lem7142737 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem7142736 A)). Qed.
Lemma lem7142738 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem7142739 {A : Type'} : term11 A.
Proof. exact (@lem7142723 A). Qed.
Lemma lem7142746 {_133668 : Type'} : term12 _133668.
Proof. exact (@lem3864294 _133668). Qed.
Lemma lem7142749 {A : Type'} : term13 A.
Proof. exact (@lem3863773 A). Qed.
Lemma lem7142750 {_133668 : Type'} : term13 _133668.
Proof. exact (@lem3863773 _133668). Qed.
Lemma lem7142757 {_100044 _133668 A : Type'} (h1 : term14 _100044 _133668 A) : term14 _100044 _133668 A.
Proof. exact (h1). Qed.
Lemma lem7142758 {_100044 _133668 A : Type'} : term15 _100044 _133668 A.
Proof. exact (fun h0 : term14 _100044 _133668 A => @lem7142757 _100044 _133668 A h0). Qed.
Lemma lem7142759 {_100044 _133668 A : Type'} (h1 : term15 _100044 _133668 A) : term15 _100044 _133668 A.
Proof. exact (h1). Qed.
Lemma lem7142760 {_100044 _133668 A : Type'} (h1 : term14 _100044 _133668 A) : term14 _100044 _133668 A.
Proof. exact (h1). Qed.
Lemma lem7142761 {_100044 _133668 A : Type'} (h1 : term14 _100044 _133668 A) (h2 : term15 _100044 _133668 A) : term14 _100044 _133668 A.
Proof. exact (@lem7142759 _100044 _133668 A h2 (@lem7142760 _100044 _133668 A h1)). Qed.
Lemma lem7142762 {_100044 _133668 A : Type'} (h1 : term14 _100044 _133668 A) : term16 _100044 _133668 A.
Proof. exact (fun h0 : term15 _100044 _133668 A => @lem7142761 _100044 _133668 A h1 h0). Qed.
Lemma lem7142763 {_100044 _133668 A : Type'} (h1 : term15 _100044 _133668 A) : term15 _100044 _133668 A.
Proof. exact (h1). Qed.
Lemma lem7142764 {_100044 _133668 A : Type'} (h1 : term14 _100044 _133668 A) (h2 : term15 _100044 _133668 A) : term14 _100044 _133668 A.
Proof. exact (@lem7142762 _100044 _133668 A h1 (@lem7142763 _100044 _133668 A h2)). Qed.
Lemma lem7142765 {_100044 _133668 A : Type'} (h1 : term15 _100044 _133668 A) : term15 _100044 _133668 A.
Proof. exact (fun h0 : term14 _100044 _133668 A => @lem7142764 _100044 _133668 A h0 h1). Qed.
Lemma lem7142766 {_100044 _133668 A : Type'} : term17 _100044 _133668 A.
Proof. exact (fun h0 : term15 _100044 _133668 A => @lem7142765 _100044 _133668 A h0). Qed.
Lemma lem7142769 {_100044 _133668 A : Type'} : term15 _100044 _133668 A.
Proof. exact (@lem7142766 _100044 _133668 A (@lem7142758 _100044 _133668 A)). Qed.
Lemma lem7142770 {_100044 _133668 A : Type'} : term15 _100044 _133668 A.
Proof. exact (@lem7142769 _100044 _133668 A). Qed.
Lemma lem7142894 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7142895 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (@lem7142894 (term11 A)). Qed.
Lemma lem7142920 {_133668 : Type'} : (term20 _133668) = (term20 _133668).
Proof. exact (eq_refl (term20 _133668)). Qed.
Lemma lem7142921 {_133668 A : Type'} : (term21 _133668 A) = (term22 _133668 A).
Proof. exact (MK_COMB (@lem7142920 _133668) (@lem7142895 A)). Qed.
Lemma lem7142924 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7142925 {_133668 A : Type'} : (term24 _133668 A) = (term25 _133668 A).
Proof. exact (MK_COMB (@lem7142924) (@lem7142921 _133668 A)). Qed.
Lemma lem7142928 : term26 = term26.
Proof. exact (eq_refl term26). Qed.
Lemma lem7142929 {_133668 A : Type'} : (term27 _133668 A) = (term28 _133668 A).
Proof. exact (MK_COMB (@lem7142928) (@lem7142925 _133668 A)). Qed.
Lemma lem7142932 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (eq_refl (term29 A)). Qed.
Lemma lem7142933 {_133668 A : Type'} : (term30 _133668 A) = (term31 _133668 A).
Proof. exact (MK_COMB (@lem7142932 A) (@lem7142929 _133668 A)). Qed.
Lemma lem7142936 {_133668 : Type'} : (term29 _133668) = (term29 _133668).
Proof. exact (eq_refl (term29 _133668)). Qed.
Lemma lem7142937 {_133668 A : Type'} : (term32 _133668 A) = (term33 _133668 A).
Proof. exact (MK_COMB (@lem7142936 _133668) (@lem7142933 _133668 A)). Qed.
Lemma lem7142940 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (eq_refl (term34 A)). Qed.
Lemma lem7142941 {_133668 A : Type'} : (term35 _133668 A) = (term36 _133668 A).
Proof. exact (MK_COMB (@lem7142940 A) (@lem7142937 _133668 A)). Qed.
Lemma lem7142944 {_133668 : Type'} : (term34 _133668) = (term34 _133668).
Proof. exact (eq_refl (term34 _133668)). Qed.
Lemma lem7142945 {_133668 A : Type'} : (term37 _133668 A) = (term38 _133668 A).
Proof. exact (MK_COMB (@lem7142944 _133668) (@lem7142941 _133668 A)). Qed.
Lemma lem7142948 {_100044 : Type'} : (term34 _100044) = (term34 _100044).
Proof. exact (eq_refl (term34 _100044)). Qed.
Lemma lem7142949 {_100044 _133668 A : Type'} : (term39 _100044 _133668 A) = (term40 _100044 _133668 A).
Proof. exact (MK_COMB (@lem7142948 _100044) (@lem7142945 _133668 A)). Qed.
Lemma lem7142952 {A : Type'} : (term41 A) = (term41 A).
Proof. exact (eq_refl (term41 A)). Qed.
Lemma lem7142959 {_100044 _133668 A : Type'} : (term14 _100044 _133668 A) = (term42 _100044 _133668 A).
Proof. exact (MK_COMB (@lem7142952 A) (@lem7142949 _100044 _133668 A)). Qed.
Lemma lem7142960 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term43 A f s b) = (term43 A f s b).
Proof. exact (eq_refl (term43 A f s b)). Qed.
Lemma lem7142965 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term44 A s f x b) = (term44 A s f x b).
Proof. exact (eq_refl (term44 A s f x b)). Qed.
Lemma lem7142966 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term45 A s f b) = (term45 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7142965 A s f x b)). Qed.
Lemma lem7142967 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7142968 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term46 A s f b) = (term46 A s f b).
Proof. exact (MK_COMB (@lem7142967 A) (@lem7142966 A s f b)). Qed.
Lemma lem7142973 {A : Type'} (s : A -> Prop) : (term47 A s) = (term47 A s).
Proof. exact (eq_refl (term47 A s)). Qed.
Lemma lem7142974 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term48 A s f b) = (term48 A s f b).
Proof. exact (MK_COMB (@lem7142973 A s) (@lem7142968 A s f b)). Qed.
Lemma lem7142977 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (eq_refl (term49 A s)). Qed.
Lemma lem7142978 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term50 A s f b) = (term50 A s f b).
Proof. exact (MK_COMB (@lem7142977 A s) (@lem7142974 A s f b)). Qed.
Lemma lem7142979 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7142980 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term51 A s f b) = (term51 A s f b).
Proof. exact (MK_COMB (@lem7142979) (@lem7142978 A s f b)). Qed.
Lemma lem7142981 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term52 A f s b) = (term52 A f s b).
Proof. exact (MK_COMB (@lem7142980 A s f b) (@lem7142960 A f s b)). Qed.
Lemma lem7142982 {A : Type'} (f : A -> real) (s : A -> Prop) : (term53 A f s) = (term53 A f s).
Proof. exact (fun_ext (fun b : real => @lem7142981 A f s b)). Qed.
Lemma lem7142983 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7142984 {A : Type'} (f : A -> real) (s : A -> Prop) : (term54 A f s) = (term54 A f s).
Proof. exact (MK_COMB (@lem7142983) (@lem7142982 A f s)). Qed.
Lemma lem7142985 {A : Type'} (s : A -> Prop) : (term55 A s) = (term55 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7142984 A f s)). Qed.
Lemma lem7142986 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7142987 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (MK_COMB (@lem7142986 A) (@lem7142985 A s)). Qed.
Lemma lem7142988 {A : Type'} : (term57 A) = (term57 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7142987 A s)). Qed.
Lemma lem7142989 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7142990 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem7142989 A) (@lem7142988 A)). Qed.
Lemma lem7142991 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7142992 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7142991) (@lem7142990 A)). Qed.
Lemma lem7142993 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term43 _133668 f s b) = (term43 _133668 f s b).
Proof. exact (eq_refl (term43 _133668 f s b)). Qed.
Lemma lem7142998 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term44 _133668 s f x b) = (term44 _133668 s f x b).
Proof. exact (eq_refl (term44 _133668 s f x b)). Qed.
Lemma lem7142999 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term45 _133668 s f b) = (term45 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7142998 _133668 s f x b)). Qed.
Lemma lem7143000 {_133668 : Type'} : (@all _133668) = (@all _133668).
Proof. exact (eq_refl (@all _133668)). Qed.
Lemma lem7143001 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term46 _133668 s f b) = (term46 _133668 s f b).
Proof. exact (MK_COMB (@lem7143000 _133668) (@lem7142999 _133668 s f b)). Qed.
Lemma lem7143006 {_133668 : Type'} (s : _133668 -> Prop) : (term47 _133668 s) = (term47 _133668 s).
Proof. exact (eq_refl (term47 _133668 s)). Qed.
Lemma lem7143007 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term48 _133668 s f b) = (term48 _133668 s f b).
Proof. exact (MK_COMB (@lem7143006 _133668 s) (@lem7143001 _133668 s f b)). Qed.
Lemma lem7143010 {_133668 : Type'} (s : _133668 -> Prop) : (term49 _133668 s) = (term49 _133668 s).
Proof. exact (eq_refl (term49 _133668 s)). Qed.
Lemma lem7143011 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term50 _133668 s f b) = (term50 _133668 s f b).
Proof. exact (MK_COMB (@lem7143010 _133668 s) (@lem7143007 _133668 s f b)). Qed.
Lemma lem7143012 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7143013 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term51 _133668 s f b) = (term51 _133668 s f b).
Proof. exact (MK_COMB (@lem7143012) (@lem7143011 _133668 s f b)). Qed.
Lemma lem7143014 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term52 _133668 f s b) = (term52 _133668 f s b).
Proof. exact (MK_COMB (@lem7143013 _133668 s f b) (@lem7142993 _133668 f s b)). Qed.
Lemma lem7143015 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term53 _133668 f s) = (term53 _133668 f s).
Proof. exact (fun_ext (fun b : real => @lem7143014 _133668 f s b)). Qed.
Lemma lem7143016 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7143017 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term54 _133668 f s) = (term54 _133668 f s).
Proof. exact (MK_COMB (@lem7143016) (@lem7143015 _133668 f s)). Qed.
Lemma lem7143018 {_133668 : Type'} (s : _133668 -> Prop) : (term55 _133668 s) = (term55 _133668 s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7143017 _133668 f s)). Qed.
Lemma lem7143019 {_133668 : Type'} : (@all (_133668 -> real)) = (@all (_133668 -> real)).
Proof. exact (eq_refl (@all (_133668 -> real))). Qed.
Lemma lem7143020 {_133668 : Type'} (s : _133668 -> Prop) : (term56 _133668 s) = (term56 _133668 s).
Proof. exact (MK_COMB (@lem7143019 _133668) (@lem7143018 _133668 s)). Qed.
Lemma lem7143021 {_133668 : Type'} : (term57 _133668) = (term57 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7143020 _133668 s)). Qed.
Lemma lem7143022 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7143023 {_133668 : Type'} : (term11 _133668) = (term11 _133668).
Proof. exact (MK_COMB (@lem7143022 _133668) (@lem7143021 _133668)). Qed.
Lemma lem7143024 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7143025 {_133668 : Type'} : (term20 _133668) = (term20 _133668).
Proof. exact (MK_COMB (@lem7143024) (@lem7143023 _133668)). Qed.
Lemma lem7143026 {_133668 A : Type'} : (term22 _133668 A) = (term22 _133668 A).
Proof. exact (MK_COMB (@lem7143025 _133668) (@lem7142992 A)). Qed.
Lemma lem7143033 (y : real) (x : real) : (term58 y x) = (term58 y x).
Proof. exact (eq_refl (term58 y x)). Qed.
Lemma lem7143034 (x : real) : (term59 x) = (term59 x).
Proof. exact (fun_ext (fun y : real => @lem7143033 y x)). Qed.
Lemma lem7143035 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7143036 (x : real) : (term60 x) = (term60 x).
Proof. exact (MK_COMB (@lem7143035) (@lem7143034 x)). Qed.
Lemma lem7143037 : term61 = term61.
Proof. exact (fun_ext (fun x : real => @lem7143036 x)). Qed.
Lemma lem7143038 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7143039 : term62 = term62.
Proof. exact (MK_COMB (@lem7143038) (@lem7143037)). Qed.
Lemma lem7143040 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7143041 : term23 = term23.
Proof. exact (MK_COMB (@lem7143040) (@lem7143039)). Qed.
Lemma lem7143042 {_133668 A : Type'} : (term25 _133668 A) = (term25 _133668 A).
Proof. exact (MK_COMB (@lem7143041) (@lem7143026 _133668 A)). Qed.
Lemma lem7143047 (m : nat) (n : nat) : (((real_of_num m) = (real_of_num n)) = (m = n)) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (((real_of_num m) = (real_of_num n)) = (m = n))). Qed.
Lemma lem7143048 (m : nat) : (term63 m) = (term63 m).
Proof. exact (fun_ext (fun n : nat => @lem7143047 m n)). Qed.
Lemma lem7143049 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7143050 (m : nat) : (term64 m) = (term64 m).
Proof. exact (MK_COMB (@lem7143049) (@lem7143048 m)). Qed.
Lemma lem7143051 : term65 = term65.
Proof. exact (fun_ext (fun m : nat => @lem7143050 m)). Qed.
Lemma lem7143052 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7143053 : term66 = term66.
Proof. exact (MK_COMB (@lem7143052) (@lem7143051)). Qed.
Lemma lem7143054 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7143055 : term26 = term26.
Proof. exact (MK_COMB (@lem7143054) (@lem7143053)). Qed.
Lemma lem7143056 {_133668 A : Type'} : (term28 _133668 A) = (term28 _133668 A).
Proof. exact (MK_COMB (@lem7143055) (@lem7143042 _133668 A)). Qed.
Lemma lem7143061 {A : Type'} (s : A -> Prop) : ((term67 A s) = (s = (@EMPTY A))) = ((term67 A s) = (s = (@EMPTY A))).
Proof. exact (eq_refl ((term67 A s) = (s = (@EMPTY A)))). Qed.
Lemma lem7143062 {A : Type'} : (term68 A) = (term68 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7143061 A s)). Qed.
Lemma lem7143063 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7143064 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem7143063 A) (@lem7143062 A)). Qed.
Lemma lem7143065 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7143066 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (MK_COMB (@lem7143065) (@lem7143064 A)). Qed.
Lemma lem7143067 {_133668 A : Type'} : (term31 _133668 A) = (term31 _133668 A).
Proof. exact (MK_COMB (@lem7143066 A) (@lem7143056 _133668 A)). Qed.
Lemma lem7143072 {_133668 : Type'} (s : _133668 -> Prop) : ((term67 _133668 s) = (s = (@EMPTY _133668))) = ((term67 _133668 s) = (s = (@EMPTY _133668))).
Proof. exact (eq_refl ((term67 _133668 s) = (s = (@EMPTY _133668)))). Qed.
Lemma lem7143073 {_133668 : Type'} : (term68 _133668) = (term68 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7143072 _133668 s)). Qed.
Lemma lem7143074 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7143075 {_133668 : Type'} : (term12 _133668) = (term12 _133668).
Proof. exact (MK_COMB (@lem7143074 _133668) (@lem7143073 _133668)). Qed.
Lemma lem7143076 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7143077 {_133668 : Type'} : (term29 _133668) = (term29 _133668).
Proof. exact (MK_COMB (@lem7143076) (@lem7143075 _133668)). Qed.
Lemma lem7143078 {_133668 A : Type'} : (term33 _133668 A) = (term33 _133668 A).
Proof. exact (MK_COMB (@lem7143077 _133668) (@lem7143067 _133668 A)). Qed.
Lemma lem7143087 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term69 A s n)) = ((@HAS_SIZE A s n) = (term69 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (term69 A s n))). Qed.
Lemma lem7143088 {A : Type'} (s : A -> Prop) : (term70 A s) = (term70 A s).
Proof. exact (fun_ext (fun n : nat => @lem7143087 A s n)). Qed.
Lemma lem7143089 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7143090 {A : Type'} (s : A -> Prop) : (term71 A s) = (term71 A s).
Proof. exact (MK_COMB (@lem7143089) (@lem7143088 A s)). Qed.
Lemma lem7143091 {A : Type'} : (term72 A) = (term72 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7143090 A s)). Qed.
Lemma lem7143092 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7143093 {A : Type'} : (term13 A) = (term13 A).
Proof. exact (MK_COMB (@lem7143092 A) (@lem7143091 A)). Qed.
Lemma lem7143094 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7143095 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (MK_COMB (@lem7143094) (@lem7143093 A)). Qed.
Lemma lem7143096 {_133668 A : Type'} : (term36 _133668 A) = (term36 _133668 A).
Proof. exact (MK_COMB (@lem7143095 A) (@lem7143078 _133668 A)). Qed.
Lemma lem7143105 {_133668 : Type'} (s : _133668 -> Prop) (n : nat) : ((@HAS_SIZE _133668 s n) = (term69 _133668 s n)) = ((@HAS_SIZE _133668 s n) = (term69 _133668 s n)).
Proof. exact (eq_refl ((@HAS_SIZE _133668 s n) = (term69 _133668 s n))). Qed.
Lemma lem7143106 {_133668 : Type'} (s : _133668 -> Prop) : (term70 _133668 s) = (term70 _133668 s).
Proof. exact (fun_ext (fun n : nat => @lem7143105 _133668 s n)). Qed.
Lemma lem7143107 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7143108 {_133668 : Type'} (s : _133668 -> Prop) : (term71 _133668 s) = (term71 _133668 s).
Proof. exact (MK_COMB (@lem7143107) (@lem7143106 _133668 s)). Qed.
Lemma lem7143109 {_133668 : Type'} : (term72 _133668) = (term72 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7143108 _133668 s)). Qed.
Lemma lem7143110 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7143111 {_133668 : Type'} : (term13 _133668) = (term13 _133668).
Proof. exact (MK_COMB (@lem7143110 _133668) (@lem7143109 _133668)). Qed.
Lemma lem7143112 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7143113 {_133668 : Type'} : (term34 _133668) = (term34 _133668).
Proof. exact (MK_COMB (@lem7143112) (@lem7143111 _133668)). Qed.
Lemma lem7143114 {_133668 A : Type'} : (term38 _133668 A) = (term38 _133668 A).
Proof. exact (MK_COMB (@lem7143113 _133668) (@lem7143096 _133668 A)). Qed.
Lemma lem7143123 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term69 _100044 s n)) = ((@HAS_SIZE _100044 s n) = (term69 _100044 s n)).
Proof. exact (eq_refl ((@HAS_SIZE _100044 s n) = (term69 _100044 s n))). Qed.
Lemma lem7143124 {_100044 : Type'} (s : _100044 -> Prop) : (term70 _100044 s) = (term70 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7143123 _100044 s n)). Qed.
Lemma lem7143125 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7143126 {_100044 : Type'} (s : _100044 -> Prop) : (term71 _100044 s) = (term71 _100044 s).
Proof. exact (MK_COMB (@lem7143125) (@lem7143124 _100044 s)). Qed.
Lemma lem7143127 {_100044 : Type'} : (term72 _100044) = (term72 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7143126 _100044 s)). Qed.
Lemma lem7143128 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7143129 {_100044 : Type'} : (term13 _100044) = (term13 _100044).
Proof. exact (MK_COMB (@lem7143128 _100044) (@lem7143127 _100044)). Qed.
Lemma lem7143130 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7143131 {_100044 : Type'} : (term34 _100044) = (term34 _100044).
Proof. exact (MK_COMB (@lem7143130) (@lem7143129 _100044)). Qed.
Lemma lem7143132 {_100044 _133668 A : Type'} : (term40 _100044 _133668 A) = (term40 _100044 _133668 A).
Proof. exact (MK_COMB (@lem7143131 _100044) (@lem7143114 _133668 A)). Qed.
Lemma lem7143133 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term73 A s f b) = (term73 A s f b).
Proof. exact (eq_refl (term73 A s f b)). Qed.
Lemma lem7143138 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term74 A f x b s) = (term74 A f x b s).
Proof. exact (eq_refl (term74 A f x b s)). Qed.
Lemma lem7143139 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term75 A f b s) = (term75 A f b s).
Proof. exact (fun_ext (fun x : A => @lem7143138 A f x b s)). Qed.
Lemma lem7143140 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7143141 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term76 A f b s) = (term76 A f b s).
Proof. exact (MK_COMB (@lem7143140 A) (@lem7143139 A f b s)). Qed.
Lemma lem7143146 {A : Type'} (s : A -> Prop) : (term47 A s) = (term47 A s).
Proof. exact (eq_refl (term47 A s)). Qed.
Lemma lem7143147 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term77 A f b s) = (term77 A f b s).
Proof. exact (MK_COMB (@lem7143146 A s) (@lem7143141 A f b s)). Qed.
Lemma lem7143150 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (eq_refl (term49 A s)). Qed.
Lemma lem7143151 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term78 A f b s) = (term78 A f b s).
Proof. exact (MK_COMB (@lem7143150 A s) (@lem7143147 A f b s)). Qed.
Lemma lem7143152 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7143153 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term79 A f b s) = (term79 A f b s).
Proof. exact (MK_COMB (@lem7143152) (@lem7143151 A f b s)). Qed.
Lemma lem7143154 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term80 A s f b) = (term80 A s f b).
Proof. exact (MK_COMB (@lem7143153 A f b s) (@lem7143133 A s f b)). Qed.
Lemma lem7143155 {A : Type'} (s : A -> Prop) (f : A -> real) : (term81 A s f) = (term81 A s f).
Proof. exact (fun_ext (fun b : real => @lem7143154 A s f b)). Qed.
Lemma lem7143156 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7143157 {A : Type'} (s : A -> Prop) (f : A -> real) : (term82 A s f) = (term82 A s f).
Proof. exact (MK_COMB (@lem7143156) (@lem7143155 A s f)). Qed.
Lemma lem7143158 {A : Type'} (s : A -> Prop) : (term83 A s) = (term83 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7143157 A s f)). Qed.
Lemma lem7143159 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7143160 {A : Type'} (s : A -> Prop) : (term84 A s) = (term84 A s).
Proof. exact (MK_COMB (@lem7143159 A) (@lem7143158 A s)). Qed.
Lemma lem7143161 {A : Type'} : (term85 A) = (term85 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7143160 A s)). Qed.
Lemma lem7143162 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7143163 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (MK_COMB (@lem7143162 A) (@lem7143161 A)). Qed.
Lemma lem7143164 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7143165 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem7143164) (@lem7143163 A)). Qed.
Lemma lem7143166 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7143167 {A : Type'} : (term41 A) = (term41 A).
Proof. exact (MK_COMB (@lem7143166) (@lem7143165 A)). Qed.
Lemma lem7143168 {_100044 _133668 A : Type'} : (term42 _100044 _133668 A) = (term42 _100044 _133668 A).
Proof. exact (MK_COMB (@lem7143167 A) (@lem7143132 _100044 _133668 A)). Qed.
Lemma lem7143365 {_100044 _133668 A : Type'} : (term14 _100044 _133668 A) = (term42 _100044 _133668 A).
Proof. exact (TRANS (@lem7142959 _100044 _133668 A) (@lem7143168 _100044 _133668 A)). Qed.
Lemma lem7143366 {_100044 _133668 A : Type'} : (term42 _100044 _133668 A) = (term14 _100044 _133668 A).
Proof. exact (SYM (@lem7143365 _100044 _133668 A)). Qed.
Lemma lem7143367 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem7143370 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem7143372 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem7143373 (h1 : term66) : term66.
Proof. exact (h1). Qed.
Lemma lem7143374 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem7143375 {_133668 : Type'} (h1 : term11 _133668) : term11 _133668.
Proof. exact (h1). Qed.
Lemma lem7143376 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem7143385 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term74 A f x b s) = (term86 A f x b s).
Proof. exact (@lem17265 (@IN A x s) (term87 A f x b s)). Qed.
Lemma lem7143386 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term75 A f b s) = (term88 A f b s).
Proof. exact (fun_ext (fun x : A => @lem7143385 A f x b s)). Qed.
Lemma lem7143387 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7143388 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term76 A f b s) = (term89 A f b s).
Proof. exact (MK_COMB (@lem7143387 A) (@lem7143386 A f b s)). Qed.
Lemma lem7143390 {A : Type'} (s : A -> Prop) : (term47 A s) = (term47 A s).
Proof. exact (eq_refl (term47 A s)). Qed.
Lemma lem7143391 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term77 A f b s) = (term90 A f b s).
Proof. exact (MK_COMB (@lem7143390 A s) (@lem7143388 A f b s)). Qed.
Lemma lem7143393 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (eq_refl (term49 A s)). Qed.
Lemma lem7143394 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term78 A f b s) = (term91 A f b s).
Proof. exact (MK_COMB (@lem7143393 A s) (@lem7143391 A f b s)). Qed.
Lemma lem7143395 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term92 A s f b) = (term92 A s f b).
Proof. exact (eq_refl (term92 A s f b)). Qed.
Lemma lem7143396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7143397 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term93 A f b s) = (term94 A f b s).
Proof. exact (MK_COMB (@lem7143396) (@lem7143394 A f b s)). Qed.
Lemma lem7143398 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term95 A s f b) = (term96 A s f b).
Proof. exact (MK_COMB (@lem7143397 A f b s) (@lem7143395 A s f b)). Qed.
Lemma lem7143399 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term97 A s f b) = (term95 A s f b).
Proof. exact (@lem17362 (term78 A f b s) (term73 A s f b)). Qed.
Lemma lem7143400 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term97 A s f b) = (term96 A s f b).
Proof. exact (TRANS (@lem7143399 A s f b) (@lem7143398 A s f b)). Qed.
Lemma lem7143401 (P : real -> Prop) : (term98 P) = (term99 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7143402 {A : Type'} (s : A -> Prop) (f : A -> real) : (term100 A s f) = (term101 A s f).
Proof. exact (@lem7143401 (term81 A s f)). Qed.
Lemma lem7143403 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term102 A s f b) = (term80 A s f b).
Proof. exact (eq_refl (term102 A s f b)). Qed.
Lemma lem7143404 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7143405 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term103 A s f b) = (term97 A s f b).
Proof. exact (MK_COMB (@lem7143404) (@lem7143403 A s f b)). Qed.
Lemma lem7143406 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term103 A s f b) = (term96 A s f b).
Proof. exact (TRANS (@lem7143405 A s f b) (@lem7143400 A s f b)). Qed.
Lemma lem7143407 {A : Type'} (s : A -> Prop) (f : A -> real) : (term104 A s f) = (term105 A s f).
Proof. exact (fun_ext (fun b : real => @lem7143406 A s f b)). Qed.
Lemma lem7143408 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7143409 {A : Type'} (s : A -> Prop) (f : A -> real) : (term101 A s f) = (term106 A s f).
Proof. exact (MK_COMB (@lem7143408) (@lem7143407 A s f)). Qed.
Lemma lem7143410 {A : Type'} (s : A -> Prop) (f : A -> real) : (term100 A s f) = (term106 A s f).
Proof. exact (TRANS (@lem7143402 A s f) (@lem7143409 A s f)). Qed.
Lemma lem7143411 {A : Type'} (P : type716 A) : (term107 A P) = (term108 A P).
Proof. exact (@lem18392 (A -> real) P). Qed.
Lemma lem7143412 {A : Type'} (s : A -> Prop) : (term109 A s) = (term110 A s).
Proof. exact (@lem7143411 A (term83 A s)). Qed.
Lemma lem7143413 {A : Type'} (s : A -> Prop) (f : A -> real) : (term111 A s f) = (term82 A s f).
Proof. exact (eq_refl (term111 A s f)). Qed.
Lemma lem7143414 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7143415 {A : Type'} (s : A -> Prop) (f : A -> real) : (term112 A s f) = (term100 A s f).
Proof. exact (MK_COMB (@lem7143414) (@lem7143413 A s f)). Qed.
Lemma lem7143416 {A : Type'} (s : A -> Prop) (f : A -> real) : (term112 A s f) = (term106 A s f).
Proof. exact (TRANS (@lem7143415 A s f) (@lem7143410 A s f)). Qed.
Lemma lem7143417 {A : Type'} (s : A -> Prop) : (term113 A s) = (term114 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7143416 A s f)). Qed.
Lemma lem7143418 {A : Type'} : (@ex (A -> real)) = (@ex (A -> real)).
Proof. exact (eq_refl (@ex (A -> real))). Qed.
Lemma lem7143419 {A : Type'} (s : A -> Prop) : (term110 A s) = (term115 A s).
Proof. exact (MK_COMB (@lem7143418 A) (@lem7143417 A s)). Qed.
Lemma lem7143420 {A : Type'} (s : A -> Prop) : (term109 A s) = (term115 A s).
Proof. exact (TRANS (@lem7143412 A s) (@lem7143419 A s)). Qed.
Lemma lem7143421 {A : Type'} (P : type686 A) : (term116 A P) = (term117 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem7143422 {A : Type'} : (term10 A) = (term118 A).
Proof. exact (@lem7143421 A (term85 A)). Qed.
Lemma lem7143423 {A : Type'} (s : A -> Prop) : (term119 A s) = (term84 A s).
Proof. exact (eq_refl (term119 A s)). Qed.
Lemma lem7143424 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7143425 {A : Type'} (s : A -> Prop) : (term120 A s) = (term109 A s).
Proof. exact (MK_COMB (@lem7143424) (@lem7143423 A s)). Qed.
Lemma lem7143426 {A : Type'} (s : A -> Prop) : (term120 A s) = (term115 A s).
Proof. exact (TRANS (@lem7143425 A s) (@lem7143420 A s)). Qed.
Lemma lem7143427 {A : Type'} : (term121 A) = (term122 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7143426 A s)). Qed.
Lemma lem7143428 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7143429 {A : Type'} : (term118 A) = (term123 A).
Proof. exact (MK_COMB (@lem7143428 A) (@lem7143427 A)). Qed.
Lemma lem7143538 {A : Type'} : (term10 A) = (term123 A).
Proof. exact (TRANS (@lem7143422 A) (@lem7143429 A)). Qed.
Lemma lem7143539 {A : Type'} (h1 : term10 A) : term123 A.
Proof. exact (EQ_MP (@lem7143538 A) (@lem7143367 A h1)). Qed.
Lemma lem7144144 {A : Type'} (s : A -> Prop) (n : nat) : (term124 A s n) = (term125 A s n).
Proof. exact (@lem17045 (@FINITE A s) ((@CARD A s) = n)). Qed.
Lemma lem7144150 {A : Type'} (s : A -> Prop) (n : nat) : (term126 A s n) = (term126 A s n).
Proof. exact (eq_refl (term126 A s n)). Qed.
Lemma lem7144152 {A : Type'} (s : A -> Prop) (n : nat) : (term127 A s n) = (term127 A s n).
Proof. exact (eq_refl (term127 A s n)). Qed.
Lemma lem7144153 {A : Type'} (s : A -> Prop) (n : nat) : (term128 A s n) = (term129 A s n).
Proof. exact (MK_COMB (@lem7144152 A s n) (@lem7144144 A s n)). Qed.
Lemma lem7144154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7144155 {A : Type'} (s : A -> Prop) (n : nat) : (term130 A s n) = (term131 A s n).
Proof. exact (MK_COMB (@lem7144154) (@lem7144153 A s n)). Qed.
Lemma lem7144156 {A : Type'} (s : A -> Prop) (n : nat) : (term132 A s n) = (term133 A s n).
Proof. exact (MK_COMB (@lem7144155 A s n) (@lem7144150 A s n)). Qed.
Lemma lem7144157 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term69 A s n)) = (term132 A s n).
Proof. exact (@lem17784 (@HAS_SIZE A s n) (term69 A s n)). Qed.
Lemma lem7144158 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term69 A s n)) = (term133 A s n).
Proof. exact (TRANS (@lem7144157 A s n) (@lem7144156 A s n)). Qed.
Lemma lem7144159 {A : Type'} (s : A -> Prop) : (term70 A s) = (term134 A s).
Proof. exact (fun_ext (fun n : nat => @lem7144158 A s n)). Qed.
Lemma lem7144160 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7144161 {A : Type'} (s : A -> Prop) : (term71 A s) = (term135 A s).
Proof. exact (MK_COMB (@lem7144160) (@lem7144159 A s)). Qed.
Lemma lem7144162 {A : Type'} : (term72 A) = (term136 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7144161 A s)). Qed.
Lemma lem7144163 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7144164 {A : Type'} : (term13 A) = (term137 A).
Proof. exact (MK_COMB (@lem7144163 A) (@lem7144162 A)). Qed.
Lemma lem7144170 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7144171 (P : nat -> Prop) (Q : nat -> Prop) : (term140 P Q) = (term141 P Q).
Proof. exact (@lem7144170 nat P Q). Qed.
Lemma lem7144172 {A : Type'} (s : A -> Prop) : (term142 A s) = (term143 A s).
Proof. exact (@lem7144171 (term144 A s) (term145 A s)). Qed.
Lemma lem7144173 {A : Type'} (s : A -> Prop) (n : nat) : (term146 A s n) = (term129 A s n).
Proof. exact (eq_refl (term146 A s n)). Qed.
Lemma lem7144174 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7144175 {A : Type'} (s : A -> Prop) (n : nat) : (term147 A s n) = (term131 A s n).
Proof. exact (MK_COMB (@lem7144174) (@lem7144173 A s n)). Qed.
Lemma lem7144176 {A : Type'} (s : A -> Prop) (n : nat) : (term148 A s n) = (term126 A s n).
Proof. exact (eq_refl (term148 A s n)). Qed.
Lemma lem7144177 {A : Type'} (s : A -> Prop) (n : nat) : (term149 A s n) = (term133 A s n).
Proof. exact (MK_COMB (@lem7144175 A s n) (@lem7144176 A s n)). Qed.
Lemma lem7144178 {A : Type'} (s : A -> Prop) : (term150 A s) = (term134 A s).
Proof. exact (fun_ext (fun n : nat => @lem7144177 A s n)). Qed.
Lemma lem7144179 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7144180 {A : Type'} (s : A -> Prop) : (term142 A s) = (term135 A s).
Proof. exact (MK_COMB (@lem7144179) (@lem7144178 A s)). Qed.
Lemma lem7144181 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7144182 {A : Type'} (s : A -> Prop) : (term151 A s) = (term152 A s).
Proof. exact (MK_COMB (@lem7144181) (@lem7144180 A s)). Qed.
Lemma lem7144183 {A : Type'} (s : A -> Prop) (n : nat) : (term146 A s n) = (term129 A s n).
Proof. exact (eq_refl (term146 A s n)). Qed.
Lemma lem7144184 {A : Type'} (s : A -> Prop) : (term153 A s) = (term144 A s).
Proof. exact (fun_ext (fun n : nat => @lem7144183 A s n)). Qed.
Lemma lem7144185 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7144186 {A : Type'} (s : A -> Prop) : (term154 A s) = (term155 A s).
Proof. exact (MK_COMB (@lem7144185) (@lem7144184 A s)). Qed.
Lemma lem7144187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7144188 {A : Type'} (s : A -> Prop) : (term156 A s) = (term157 A s).
Proof. exact (MK_COMB (@lem7144187) (@lem7144186 A s)). Qed.
Lemma lem7144189 {A : Type'} (s : A -> Prop) (n : nat) : (term148 A s n) = (term126 A s n).
Proof. exact (eq_refl (term148 A s n)). Qed.
Lemma lem7144190 {A : Type'} (s : A -> Prop) : (term158 A s) = (term145 A s).
Proof. exact (fun_ext (fun n : nat => @lem7144189 A s n)). Qed.
Lemma lem7144191 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7144192 {A : Type'} (s : A -> Prop) : (term159 A s) = (term160 A s).
Proof. exact (MK_COMB (@lem7144191) (@lem7144190 A s)). Qed.
Lemma lem7144193 {A : Type'} (s : A -> Prop) : (term143 A s) = (term161 A s).
Proof. exact (MK_COMB (@lem7144188 A s) (@lem7144192 A s)). Qed.
Lemma lem7144194 {A : Type'} (s : A -> Prop) : ((term142 A s) = (term143 A s)) = ((term135 A s) = (term161 A s)).
Proof. exact (MK_COMB (@lem7144182 A s) (@lem7144193 A s)). Qed.
Lemma lem7144195 {A : Type'} (s : A -> Prop) : (term135 A s) = (term161 A s).
Proof. exact (EQ_MP (@lem7144194 A s) (@lem7144172 A s)). Qed.
Lemma lem7144292 {A : Type'} : (term136 A) = (term162 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7144195 A s)). Qed.
Lemma lem7144293 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7144294 {A : Type'} : (term137 A) = (term163 A).
Proof. exact (MK_COMB (@lem7144293 A) (@lem7144292 A)). Qed.
Lemma lem7144296 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7144297 {A : Type'} (P : type686 A) (Q : type686 A) : (term164 A P Q) = (term165 A P Q).
Proof. exact (@lem7144296 (A -> Prop) P Q). Qed.
Lemma lem7144298 {A : Type'} : (term166 A) = (term167 A).
Proof. exact (@lem7144297 A (term168 A) (term169 A)). Qed.
Lemma lem7144299 {A : Type'} (s : A -> Prop) : (term170 A s) = (term155 A s).
Proof. exact (eq_refl (term170 A s)). Qed.
Lemma lem7144300 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7144301 {A : Type'} (s : A -> Prop) : (term171 A s) = (term157 A s).
Proof. exact (MK_COMB (@lem7144300) (@lem7144299 A s)). Qed.
Lemma lem7144302 {A : Type'} (s : A -> Prop) : (term172 A s) = (term160 A s).
Proof. exact (eq_refl (term172 A s)). Qed.
Lemma lem7144303 {A : Type'} (s : A -> Prop) : (term173 A s) = (term161 A s).
Proof. exact (MK_COMB (@lem7144301 A s) (@lem7144302 A s)). Qed.
Lemma lem7144304 {A : Type'} : (term174 A) = (term162 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7144303 A s)). Qed.
Lemma lem7144305 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7144306 {A : Type'} : (term166 A) = (term163 A).
Proof. exact (MK_COMB (@lem7144305 A) (@lem7144304 A)). Qed.
Lemma lem7144307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7144308 {A : Type'} : (term175 A) = (term176 A).
Proof. exact (MK_COMB (@lem7144307) (@lem7144306 A)). Qed.
Lemma lem7144309 {A : Type'} (s : A -> Prop) : (term170 A s) = (term155 A s).
Proof. exact (eq_refl (term170 A s)). Qed.
Lemma lem7144310 {A : Type'} : (term177 A) = (term168 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7144309 A s)). Qed.
Lemma lem7144311 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7144312 {A : Type'} : (term178 A) = (term179 A).
Proof. exact (MK_COMB (@lem7144311 A) (@lem7144310 A)). Qed.
Lemma lem7144313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7144314 {A : Type'} : (term180 A) = (term181 A).
Proof. exact (MK_COMB (@lem7144313) (@lem7144312 A)). Qed.
Lemma lem7144315 {A : Type'} (s : A -> Prop) : (term172 A s) = (term160 A s).
Proof. exact (eq_refl (term172 A s)). Qed.
Lemma lem7144316 {A : Type'} : (term182 A) = (term169 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7144315 A s)). Qed.
Lemma lem7144317 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7144318 {A : Type'} : (term183 A) = (term184 A).
Proof. exact (MK_COMB (@lem7144317 A) (@lem7144316 A)). Qed.
Lemma lem7144319 {A : Type'} : (term167 A) = (term185 A).
Proof. exact (MK_COMB (@lem7144314 A) (@lem7144318 A)). Qed.
Lemma lem7144320 {A : Type'} : ((term166 A) = (term167 A)) = ((term163 A) = (term185 A)).
Proof. exact (MK_COMB (@lem7144308 A) (@lem7144319 A)). Qed.
Lemma lem7144321 {A : Type'} : (term163 A) = (term185 A).
Proof. exact (EQ_MP (@lem7144320 A) (@lem7144298 A)). Qed.
Lemma lem7144428 {A : Type'} : (term137 A) = (term185 A).
Proof. exact (TRANS (@lem7144294 A) (@lem7144321 A)). Qed.
Lemma lem7144429 {A : Type'} : (term13 A) = (term185 A).
Proof. exact (TRANS (@lem7144164 A) (@lem7144428 A)). Qed.
Lemma lem7144430 {A : Type'} (h1 : term13 A) : term185 A.
Proof. exact (EQ_MP (@lem7144429 A) (@lem7143370 A h1)). Qed.
Lemma lem7144590 {A : Type'} (s : A -> Prop) : ((term67 A s) = (s = (@EMPTY A))) = (term186 A s).
Proof. exact (@lem17784 (term67 A s) (s = (@EMPTY A))). Qed.
Lemma lem7144591 {A : Type'} : (term68 A) = (term187 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7144590 A s)). Qed.
Lemma lem7144592 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7144593 {A : Type'} : (term12 A) = (term188 A).
Proof. exact (MK_COMB (@lem7144592 A) (@lem7144591 A)). Qed.
Lemma lem7144595 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7144596 {A : Type'} (P : type686 A) (Q : type686 A) : (term164 A P Q) = (term165 A P Q).
Proof. exact (@lem7144595 (A -> Prop) P Q). Qed.
Lemma lem7144597 {A : Type'} : (term189 A) = (term190 A).
Proof. exact (@lem7144596 A (term191 A) (term192 A)). Qed.
Lemma lem7144598 {A : Type'} (s : A -> Prop) : (term193 A s) = (term194 A s).
Proof. exact (eq_refl (term193 A s)). Qed.
Lemma lem7144599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7144600 {A : Type'} (s : A -> Prop) : (term195 A s) = (term196 A s).
Proof. exact (MK_COMB (@lem7144599) (@lem7144598 A s)). Qed.
Lemma lem7144601 {A : Type'} (s : A -> Prop) : (term197 A s) = (term198 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem7144602 {A : Type'} (s : A -> Prop) : (term199 A s) = (term186 A s).
Proof. exact (MK_COMB (@lem7144600 A s) (@lem7144601 A s)). Qed.
Lemma lem7144603 {A : Type'} : (term200 A) = (term187 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7144602 A s)). Qed.
Lemma lem7144604 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7144605 {A : Type'} : (term189 A) = (term188 A).
Proof. exact (MK_COMB (@lem7144604 A) (@lem7144603 A)). Qed.
Lemma lem7144606 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7144607 {A : Type'} : (term201 A) = (term202 A).
Proof. exact (MK_COMB (@lem7144606) (@lem7144605 A)). Qed.
Lemma lem7144608 {A : Type'} (s : A -> Prop) : (term193 A s) = (term194 A s).
Proof. exact (eq_refl (term193 A s)). Qed.
Lemma lem7144609 {A : Type'} : (term203 A) = (term191 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7144608 A s)). Qed.
Lemma lem7144610 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7144611 {A : Type'} : (term204 A) = (term205 A).
Proof. exact (MK_COMB (@lem7144610 A) (@lem7144609 A)). Qed.
Lemma lem7144612 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7144613 {A : Type'} : (term206 A) = (term207 A).
Proof. exact (MK_COMB (@lem7144612) (@lem7144611 A)). Qed.
Lemma lem7144614 {A : Type'} (s : A -> Prop) : (term197 A s) = (term198 A s).
Proof. exact (eq_refl (term197 A s)). Qed.
Lemma lem7144615 {A : Type'} : (term208 A) = (term192 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7144614 A s)). Qed.
Lemma lem7144616 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7144617 {A : Type'} : (term209 A) = (term210 A).
Proof. exact (MK_COMB (@lem7144616 A) (@lem7144615 A)). Qed.
Lemma lem7144618 {A : Type'} : (term190 A) = (term211 A).
Proof. exact (MK_COMB (@lem7144613 A) (@lem7144617 A)). Qed.
Lemma lem7144619 {A : Type'} : ((term189 A) = (term190 A)) = ((term188 A) = (term211 A)).
Proof. exact (MK_COMB (@lem7144607 A) (@lem7144618 A)). Qed.
Lemma lem7144718 {A : Type'} : (term188 A) = (term211 A).
Proof. exact (EQ_MP (@lem7144619 A) (@lem7144597 A)). Qed.
Lemma lem7144719 {A : Type'} : (term12 A) = (term211 A).
Proof. exact (TRANS (@lem7144593 A) (@lem7144718 A)). Qed.
Lemma lem7144720 {A : Type'} (h1 : term12 A) : term211 A.
Proof. exact (EQ_MP (@lem7144719 A) (@lem7143372 A h1)). Qed.
Lemma lem7144735 (m : nat) (n : nat) : (((real_of_num m) = (real_of_num n)) = (m = n)) = (term212 m n).
Proof. exact (@lem17784 ((real_of_num m) = (real_of_num n)) (m = n)). Qed.
Lemma lem7144736 (m : nat) : (term63 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem7144735 m n)). Qed.
Lemma lem7144737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7144738 (m : nat) : (term64 m) = (term214 m).
Proof. exact (MK_COMB (@lem7144737) (@lem7144736 m)). Qed.
Lemma lem7144739 : term65 = term215.
Proof. exact (fun_ext (fun m : nat => @lem7144738 m)). Qed.
Lemma lem7144740 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7144741 : term66 = term216.
Proof. exact (MK_COMB (@lem7144740) (@lem7144739)). Qed.
Lemma lem7144747 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7144748 (P : nat -> Prop) (Q : nat -> Prop) : (term140 P Q) = (term141 P Q).
Proof. exact (@lem7144747 nat P Q). Qed.
Lemma lem7144749 (m : nat) : (term217 m) = (term218 m).
Proof. exact (@lem7144748 (term219 m) (term220 m)). Qed.
Lemma lem7144750 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (eq_refl (term221 m n)). Qed.
Lemma lem7144751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7144752 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (MK_COMB (@lem7144751) (@lem7144750 m n)). Qed.
Lemma lem7144753 (m : nat) (n : nat) : (term225 m n) = (term226 m n).
Proof. exact (eq_refl (term225 m n)). Qed.
Lemma lem7144754 (m : nat) (n : nat) : (term227 m n) = (term212 m n).
Proof. exact (MK_COMB (@lem7144752 m n) (@lem7144753 m n)). Qed.
Lemma lem7144755 (m : nat) : (term228 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem7144754 m n)). Qed.
Lemma lem7144756 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7144757 (m : nat) : (term217 m) = (term214 m).
Proof. exact (MK_COMB (@lem7144756) (@lem7144755 m)). Qed.
Lemma lem7144758 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7144759 (m : nat) : (term229 m) = (term230 m).
Proof. exact (MK_COMB (@lem7144758) (@lem7144757 m)). Qed.
Lemma lem7144760 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (eq_refl (term221 m n)). Qed.
Lemma lem7144761 (m : nat) : (term231 m) = (term219 m).
Proof. exact (fun_ext (fun n : nat => @lem7144760 m n)). Qed.
Lemma lem7144762 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7144763 (m : nat) : (term232 m) = (term233 m).
Proof. exact (MK_COMB (@lem7144762) (@lem7144761 m)). Qed.
Lemma lem7144764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7144765 (m : nat) : (term234 m) = (term235 m).
Proof. exact (MK_COMB (@lem7144764) (@lem7144763 m)). Qed.
Lemma lem7144766 (m : nat) (n : nat) : (term225 m n) = (term226 m n).
Proof. exact (eq_refl (term225 m n)). Qed.
Lemma lem7144767 (m : nat) : (term236 m) = (term220 m).
Proof. exact (fun_ext (fun n : nat => @lem7144766 m n)). Qed.
Lemma lem7144768 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7144769 (m : nat) : (term237 m) = (term238 m).
Proof. exact (MK_COMB (@lem7144768) (@lem7144767 m)). Qed.
Lemma lem7144770 (m : nat) : (term218 m) = (term239 m).
Proof. exact (MK_COMB (@lem7144765 m) (@lem7144769 m)). Qed.
Lemma lem7144771 (m : nat) : ((term217 m) = (term218 m)) = ((term214 m) = (term239 m)).
Proof. exact (MK_COMB (@lem7144759 m) (@lem7144770 m)). Qed.
Lemma lem7144772 (m : nat) : (term214 m) = (term239 m).
Proof. exact (EQ_MP (@lem7144771 m) (@lem7144749 m)). Qed.
Lemma lem7144869 : term215 = term240.
Proof. exact (fun_ext (fun m : nat => @lem7144772 m)). Qed.
Lemma lem7144870 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7144871 : term216 = term241.
Proof. exact (MK_COMB (@lem7144870) (@lem7144869)). Qed.
Lemma lem7144873 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7144874 (P : nat -> Prop) (Q : nat -> Prop) : (term140 P Q) = (term141 P Q).
Proof. exact (@lem7144873 nat P Q). Qed.
Lemma lem7144875 : term242 = term243.
Proof. exact (@lem7144874 term244 term245). Qed.
Lemma lem7144876 (m : nat) : (term246 m) = (term233 m).
Proof. exact (eq_refl (term246 m)). Qed.
Lemma lem7144877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7144878 (m : nat) : (term247 m) = (term235 m).
Proof. exact (MK_COMB (@lem7144877) (@lem7144876 m)). Qed.
Lemma lem7144879 (m : nat) : (term248 m) = (term238 m).
Proof. exact (eq_refl (term248 m)). Qed.
Lemma lem7144880 (m : nat) : (term249 m) = (term239 m).
Proof. exact (MK_COMB (@lem7144878 m) (@lem7144879 m)). Qed.
Lemma lem7144881 : term250 = term240.
Proof. exact (fun_ext (fun m : nat => @lem7144880 m)). Qed.
Lemma lem7144882 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7144883 : term242 = term241.
Proof. exact (MK_COMB (@lem7144882) (@lem7144881)). Qed.
Lemma lem7144884 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7144885 : term251 = term252.
Proof. exact (MK_COMB (@lem7144884) (@lem7144883)). Qed.
Lemma lem7144886 (m : nat) : (term246 m) = (term233 m).
Proof. exact (eq_refl (term246 m)). Qed.
Lemma lem7144887 : term253 = term244.
Proof. exact (fun_ext (fun m : nat => @lem7144886 m)). Qed.
Lemma lem7144888 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7144889 : term254 = term255.
Proof. exact (MK_COMB (@lem7144888) (@lem7144887)). Qed.
Lemma lem7144890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7144891 : term256 = term257.
Proof. exact (MK_COMB (@lem7144890) (@lem7144889)). Qed.
Lemma lem7144892 (m : nat) : (term248 m) = (term238 m).
Proof. exact (eq_refl (term248 m)). Qed.
Lemma lem7144893 : term258 = term245.
Proof. exact (fun_ext (fun m : nat => @lem7144892 m)). Qed.
Lemma lem7144894 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7144895 : term259 = term260.
Proof. exact (MK_COMB (@lem7144894) (@lem7144893)). Qed.
Lemma lem7144896 : term243 = term261.
Proof. exact (MK_COMB (@lem7144891) (@lem7144895)). Qed.
Lemma lem7144897 : (term242 = term243) = (term241 = term261).
Proof. exact (MK_COMB (@lem7144885) (@lem7144896)). Qed.
Lemma lem7144898 : term241 = term261.
Proof. exact (EQ_MP (@lem7144897) (@lem7144875)). Qed.
Lemma lem7145005 : term216 = term261.
Proof. exact (TRANS (@lem7144871) (@lem7144898)). Qed.
Lemma lem7145006 : term66 = term261.
Proof. exact (TRANS (@lem7144741) (@lem7145005)). Qed.
Lemma lem7145007 (h1 : term66) : term261.
Proof. exact (EQ_MP (@lem7145006) (@lem7143373 h1)). Qed.
Lemma lem7145010 (y : real) : (term262 y) = (y = term263).
Proof. exact (@lem16933 (y = term263)). Qed.
Lemma lem7145011 (y : real) (x : real) : ((term264 x y) = x) = ((term264 x y) = x).
Proof. exact (eq_refl ((term264 x y) = x)). Qed.
Lemma lem7145012 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7145013 (y : real) : (term265 y) = (term266 y).
Proof. exact (MK_COMB (@lem7145012) (@lem7145010 y)). Qed.
Lemma lem7145014 (y : real) (x : real) : (term267 y x) = (term268 y x).
Proof. exact (MK_COMB (@lem7145013 y) (@lem7145011 y x)). Qed.
Lemma lem7145015 (y : real) (x : real) : (term58 y x) = (term267 y x).
Proof. exact (@lem17265 (term269 y) ((term264 x y) = x)). Qed.
Lemma lem7145016 (y : real) (x : real) : (term58 y x) = (term268 y x).
Proof. exact (TRANS (@lem7145015 y x) (@lem7145014 y x)). Qed.
Lemma lem7145017 (x : real) : (term59 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem7145016 y x)). Qed.
Lemma lem7145018 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7145019 (x : real) : (term60 x) = (term271 x).
Proof. exact (MK_COMB (@lem7145018) (@lem7145017 x)). Qed.
Lemma lem7145020 : term61 = term272.
Proof. exact (fun_ext (fun x : real => @lem7145019 x)). Qed.
Lemma lem7145021 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7145078 : term62 = term273.
Proof. exact (MK_COMB (@lem7145021) (@lem7145020)). Qed.
Lemma lem7145079 (h1 : term62) : term273.
Proof. exact (EQ_MP (@lem7145078) (@lem7143374 h1)). Qed.
Lemma lem7145083 {_133668 : Type'} (s : _133668 -> Prop) : (term274 _133668 s) = (s = (@EMPTY _133668)).
Proof. exact (@lem16933 (s = (@EMPTY _133668))). Qed.
Lemma lem7145090 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term275 _133668 s f x b) = (term276 _133668 s f x b).
Proof. exact (@lem17362 (@IN _133668 x s) (term277 _133668 f x b)). Qed.
Lemma lem7145091 {_133668 : Type'} (P : _133668 -> Prop) : (term278 _133668 P) = (term279 _133668 P).
Proof. exact (@lem18392 _133668 P). Qed.
Lemma lem7145092 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term280 _133668 s f b) = (term281 _133668 s f b).
Proof. exact (@lem7145091 _133668 (term45 _133668 s f b)). Qed.
Lemma lem7145093 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term282 _133668 s f b x) = (term44 _133668 s f x b).
Proof. exact (eq_refl (term282 _133668 s f b x)). Qed.
Lemma lem7145094 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7145095 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term283 _133668 s f b x) = (term275 _133668 s f x b).
Proof. exact (MK_COMB (@lem7145094) (@lem7145093 _133668 s f x b)). Qed.
Lemma lem7145096 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term283 _133668 s f b x) = (term276 _133668 s f x b).
Proof. exact (TRANS (@lem7145095 _133668 s f x b) (@lem7145090 _133668 s f x b)). Qed.
Lemma lem7145097 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term284 _133668 s f b) = (term285 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7145096 _133668 s f x b)). Qed.
Lemma lem7145098 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7145099 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term281 _133668 s f b) = (term286 _133668 s f b).
Proof. exact (MK_COMB (@lem7145098 _133668) (@lem7145097 _133668 s f b)). Qed.
Lemma lem7145100 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term280 _133668 s f b) = (term286 _133668 s f b).
Proof. exact (TRANS (@lem7145092 _133668 s f b) (@lem7145099 _133668 s f b)). Qed.
Lemma lem7145101 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7145102 {_133668 : Type'} (s : _133668 -> Prop) : (term287 _133668 s) = (term288 _133668 s).
Proof. exact (MK_COMB (@lem7145101) (@lem7145083 _133668 s)). Qed.
Lemma lem7145103 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term289 _133668 s f b) = (term290 _133668 s f b).
Proof. exact (MK_COMB (@lem7145102 _133668 s) (@lem7145100 _133668 s f b)). Qed.
Lemma lem7145104 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term291 _133668 s f b) = (term289 _133668 s f b).
Proof. exact (@lem17045 (term292 _133668 s) (term46 _133668 s f b)). Qed.
Lemma lem7145105 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term291 _133668 s f b) = (term290 _133668 s f b).
Proof. exact (TRANS (@lem7145104 _133668 s f b) (@lem7145103 _133668 s f b)). Qed.
Lemma lem7145107 {_133668 : Type'} (s : _133668 -> Prop) : (term293 _133668 s) = (term293 _133668 s).
Proof. exact (eq_refl (term293 _133668 s)). Qed.
Lemma lem7145108 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term294 _133668 s f b) = (term295 _133668 s f b).
Proof. exact (MK_COMB (@lem7145107 _133668 s) (@lem7145105 _133668 s f b)). Qed.
Lemma lem7145109 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term296 _133668 s f b) = (term294 _133668 s f b).
Proof. exact (@lem17045 (@FINITE _133668 s) (term48 _133668 s f b)). Qed.
Lemma lem7145110 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term296 _133668 s f b) = (term295 _133668 s f b).
Proof. exact (TRANS (@lem7145109 _133668 s f b) (@lem7145108 _133668 s f b)). Qed.
Lemma lem7145111 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term43 _133668 f s b) = (term43 _133668 f s b).
Proof. exact (eq_refl (term43 _133668 f s b)). Qed.
Lemma lem7145112 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7145113 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term297 _133668 s f b) = (term298 _133668 s f b).
Proof. exact (MK_COMB (@lem7145112) (@lem7145110 _133668 s f b)). Qed.
Lemma lem7145114 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term299 _133668 f s b) = (term300 _133668 f s b).
Proof. exact (MK_COMB (@lem7145113 _133668 s f b) (@lem7145111 _133668 f s b)). Qed.
Lemma lem7145115 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term52 _133668 f s b) = (term299 _133668 f s b).
Proof. exact (@lem17265 (term50 _133668 s f b) (term43 _133668 f s b)). Qed.
Lemma lem7145116 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term52 _133668 f s b) = (term300 _133668 f s b).
Proof. exact (TRANS (@lem7145115 _133668 f s b) (@lem7145114 _133668 f s b)). Qed.
Lemma lem7145117 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term53 _133668 f s) = (term301 _133668 f s).
Proof. exact (fun_ext (fun b : real => @lem7145116 _133668 f s b)). Qed.
Lemma lem7145118 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7145119 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term54 _133668 f s) = (term302 _133668 f s).
Proof. exact (MK_COMB (@lem7145118) (@lem7145117 _133668 f s)). Qed.
Lemma lem7145120 {_133668 : Type'} (s : _133668 -> Prop) : (term55 _133668 s) = (term303 _133668 s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7145119 _133668 f s)). Qed.
Lemma lem7145121 {_133668 : Type'} : (@all (_133668 -> real)) = (@all (_133668 -> real)).
Proof. exact (eq_refl (@all (_133668 -> real))). Qed.
Lemma lem7145122 {_133668 : Type'} (s : _133668 -> Prop) : (term56 _133668 s) = (term304 _133668 s).
Proof. exact (MK_COMB (@lem7145121 _133668) (@lem7145120 _133668 s)). Qed.
Lemma lem7145123 {_133668 : Type'} : (term57 _133668) = (term305 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7145122 _133668 s)). Qed.
Lemma lem7145124 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7145125 {_133668 : Type'} : (term11 _133668) = (term306 _133668).
Proof. exact (MK_COMB (@lem7145124 _133668) (@lem7145123 _133668)). Qed.
Lemma lem7145232 {A : Type'} (P : Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7145233 {_133668 : Type'} (P : Prop) (Q : _133668 -> Prop) : (term307 _133668 P Q) = (term308 _133668 P Q).
Proof. exact (@lem7145232 _133668 P Q). Qed.
Lemma lem7145234 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term309 _133668 s f b) = (term310 _133668 s f b).
Proof. exact (@lem7145233 _133668 (s = (@EMPTY _133668)) (term285 _133668 s f b)). Qed.
Lemma lem7145235 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term311 _133668 s f b x) = (term276 _133668 s f x b).
Proof. exact (eq_refl (term311 _133668 s f b x)). Qed.
Lemma lem7145236 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term312 _133668 s f b) = (term285 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7145235 _133668 s f x b)). Qed.
Lemma lem7145237 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7145238 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term313 _133668 s f b) = (term286 _133668 s f b).
Proof. exact (MK_COMB (@lem7145237 _133668) (@lem7145236 _133668 s f b)). Qed.
Lemma lem7145239 {_133668 : Type'} (s : _133668 -> Prop) : (term288 _133668 s) = (term288 _133668 s).
Proof. exact (eq_refl (term288 _133668 s)). Qed.
Lemma lem7145240 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term309 _133668 s f b) = (term290 _133668 s f b).
Proof. exact (MK_COMB (@lem7145239 _133668 s) (@lem7145238 _133668 s f b)). Qed.
Lemma lem7145241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7145242 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term314 _133668 s f b) = (term315 _133668 s f b).
Proof. exact (MK_COMB (@lem7145241) (@lem7145240 _133668 s f b)). Qed.
Lemma lem7145243 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term311 _133668 s f b x) = (term276 _133668 s f x b).
Proof. exact (eq_refl (term311 _133668 s f b x)). Qed.
Lemma lem7145244 {_133668 : Type'} (s : _133668 -> Prop) : (term288 _133668 s) = (term288 _133668 s).
Proof. exact (eq_refl (term288 _133668 s)). Qed.
Lemma lem7145245 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term316 _133668 s f b x) = (term317 _133668 s f x b).
Proof. exact (MK_COMB (@lem7145244 _133668 s) (@lem7145243 _133668 s f x b)). Qed.
Lemma lem7145246 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term318 _133668 s f b) = (term319 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7145245 _133668 s f x b)). Qed.
Lemma lem7145247 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7145248 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term310 _133668 s f b) = (term320 _133668 s f b).
Proof. exact (MK_COMB (@lem7145247 _133668) (@lem7145246 _133668 s f b)). Qed.
Lemma lem7145249 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : ((term309 _133668 s f b) = (term310 _133668 s f b)) = ((term290 _133668 s f b) = (term320 _133668 s f b)).
Proof. exact (MK_COMB (@lem7145242 _133668 s f b) (@lem7145248 _133668 s f b)). Qed.
Lemma lem7145250 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term290 _133668 s f b) = (term320 _133668 s f b).
Proof. exact (EQ_MP (@lem7145249 _133668 s f b) (@lem7145234 _133668 s f b)). Qed.
Lemma lem7145251 {_133668 : Type'} (s : _133668 -> Prop) : (term293 _133668 s) = (term293 _133668 s).
Proof. exact (eq_refl (term293 _133668 s)). Qed.
Lemma lem7145252 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term295 _133668 s f b) = (term321 _133668 s f b).
Proof. exact (MK_COMB (@lem7145251 _133668 s) (@lem7145250 _133668 s f b)). Qed.
Lemma lem7145254 {A : Type'} (P : Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7145255 {_133668 : Type'} (P : Prop) (Q : _133668 -> Prop) : (term307 _133668 P Q) = (term308 _133668 P Q).
Proof. exact (@lem7145254 _133668 P Q). Qed.
Lemma lem7145256 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term322 _133668 s f b) = (term323 _133668 s f b).
Proof. exact (@lem7145255 _133668 (term324 _133668 s) (term319 _133668 s f b)). Qed.
Lemma lem7145257 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term325 _133668 s f b x) = (term317 _133668 s f x b).
Proof. exact (eq_refl (term325 _133668 s f b x)). Qed.
Lemma lem7145258 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term326 _133668 s f b) = (term319 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7145257 _133668 s f x b)). Qed.
Lemma lem7145259 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7145260 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term327 _133668 s f b) = (term320 _133668 s f b).
Proof. exact (MK_COMB (@lem7145259 _133668) (@lem7145258 _133668 s f b)). Qed.
Lemma lem7145261 {_133668 : Type'} (s : _133668 -> Prop) : (term293 _133668 s) = (term293 _133668 s).
Proof. exact (eq_refl (term293 _133668 s)). Qed.
Lemma lem7145262 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term322 _133668 s f b) = (term321 _133668 s f b).
Proof. exact (MK_COMB (@lem7145261 _133668 s) (@lem7145260 _133668 s f b)). Qed.
Lemma lem7145263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7145264 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term328 _133668 s f b) = (term329 _133668 s f b).
Proof. exact (MK_COMB (@lem7145263) (@lem7145262 _133668 s f b)). Qed.
Lemma lem7145265 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term325 _133668 s f b x) = (term317 _133668 s f x b).
Proof. exact (eq_refl (term325 _133668 s f b x)). Qed.
Lemma lem7145266 {_133668 : Type'} (s : _133668 -> Prop) : (term293 _133668 s) = (term293 _133668 s).
Proof. exact (eq_refl (term293 _133668 s)). Qed.
Lemma lem7145267 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term330 _133668 s f b x) = (term331 _133668 s f x b).
Proof. exact (MK_COMB (@lem7145266 _133668 s) (@lem7145265 _133668 s f x b)). Qed.
Lemma lem7145268 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term332 _133668 s f b) = (term333 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7145267 _133668 s f x b)). Qed.
Lemma lem7145269 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7145270 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term323 _133668 s f b) = (term334 _133668 s f b).
Proof. exact (MK_COMB (@lem7145269 _133668) (@lem7145268 _133668 s f b)). Qed.
Lemma lem7145271 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : ((term322 _133668 s f b) = (term323 _133668 s f b)) = ((term321 _133668 s f b) = (term334 _133668 s f b)).
Proof. exact (MK_COMB (@lem7145264 _133668 s f b) (@lem7145270 _133668 s f b)). Qed.
Lemma lem7145272 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term321 _133668 s f b) = (term334 _133668 s f b).
Proof. exact (EQ_MP (@lem7145271 _133668 s f b) (@lem7145256 _133668 s f b)). Qed.
Lemma lem7145273 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term295 _133668 s f b) = (term334 _133668 s f b).
Proof. exact (TRANS (@lem7145252 _133668 s f b) (@lem7145272 _133668 s f b)). Qed.
Lemma lem7145274 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7145275 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term298 _133668 s f b) = (term335 _133668 s f b).
Proof. exact (MK_COMB (@lem7145274) (@lem7145273 _133668 s f b)). Qed.
Lemma lem7145276 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term43 _133668 f s b) = (term43 _133668 f s b).
Proof. exact (eq_refl (term43 _133668 f s b)). Qed.
Lemma lem7145277 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term300 _133668 f s b) = (term336 _133668 f s b).
Proof. exact (MK_COMB (@lem7145275 _133668 s f b) (@lem7145276 _133668 f s b)). Qed.
Lemma lem7145279 {A : Type'} (P : A -> Prop) (Q : Prop) : (term337 A P Q) = (term338 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7145280 {_133668 : Type'} (P : _133668 -> Prop) (Q : Prop) : (term337 _133668 P Q) = (term338 _133668 P Q).
Proof. exact (@lem7145279 _133668 P Q). Qed.
Lemma lem7145281 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term339 _133668 f s b) = (term340 _133668 f s b).
Proof. exact (@lem7145280 _133668 (term333 _133668 s f b) (term43 _133668 f s b)). Qed.
Lemma lem7145282 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term341 _133668 s f b x) = (term331 _133668 s f x b).
Proof. exact (eq_refl (term341 _133668 s f b x)). Qed.
Lemma lem7145283 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term342 _133668 s f b) = (term333 _133668 s f b).
Proof. exact (fun_ext (fun x : _133668 => @lem7145282 _133668 s f x b)). Qed.
Lemma lem7145284 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7145285 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term343 _133668 s f b) = (term334 _133668 s f b).
Proof. exact (MK_COMB (@lem7145284 _133668) (@lem7145283 _133668 s f b)). Qed.
Lemma lem7145286 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7145287 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (b : real) : (term344 _133668 s f b) = (term335 _133668 s f b).
Proof. exact (MK_COMB (@lem7145286) (@lem7145285 _133668 s f b)). Qed.
Lemma lem7145288 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term43 _133668 f s b) = (term43 _133668 f s b).
Proof. exact (eq_refl (term43 _133668 f s b)). Qed.
Lemma lem7145289 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term339 _133668 f s b) = (term336 _133668 f s b).
Proof. exact (MK_COMB (@lem7145287 _133668 s f b) (@lem7145288 _133668 f s b)). Qed.
Lemma lem7145290 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7145291 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term345 _133668 f s b) = (term346 _133668 f s b).
Proof. exact (MK_COMB (@lem7145290) (@lem7145289 _133668 f s b)). Qed.
Lemma lem7145292 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term341 _133668 s f b x) = (term331 _133668 s f x b).
Proof. exact (eq_refl (term341 _133668 s f b x)). Qed.
Lemma lem7145293 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7145294 {_133668 : Type'} (s : _133668 -> Prop) (f : _133668 -> real) (x : _133668) (b : real) : (term347 _133668 s f b x) = (term348 _133668 s f x b).
Proof. exact (MK_COMB (@lem7145293) (@lem7145292 _133668 s f x b)). Qed.
Lemma lem7145295 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term43 _133668 f s b) = (term43 _133668 f s b).
Proof. exact (eq_refl (term43 _133668 f s b)). Qed.
Lemma lem7145296 {_133668 : Type'} (x : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term349 _133668 x f s b) = (term350 _133668 x f s b).
Proof. exact (MK_COMB (@lem7145294 _133668 s f x b) (@lem7145295 _133668 f s b)). Qed.
Lemma lem7145297 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term351 _133668 f s b) = (term352 _133668 f s b).
Proof. exact (fun_ext (fun x : _133668 => @lem7145296 _133668 x f s b)). Qed.
Lemma lem7145298 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7145299 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term340 _133668 f s b) = (term353 _133668 f s b).
Proof. exact (MK_COMB (@lem7145298 _133668) (@lem7145297 _133668 f s b)). Qed.
Lemma lem7145300 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : ((term339 _133668 f s b) = (term340 _133668 f s b)) = ((term336 _133668 f s b) = (term353 _133668 f s b)).
Proof. exact (MK_COMB (@lem7145291 _133668 f s b) (@lem7145299 _133668 f s b)). Qed.
Lemma lem7145301 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term336 _133668 f s b) = (term353 _133668 f s b).
Proof. exact (EQ_MP (@lem7145300 _133668 f s b) (@lem7145281 _133668 f s b)). Qed.
Lemma lem7145302 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term300 _133668 f s b) = (term353 _133668 f s b).
Proof. exact (TRANS (@lem7145277 _133668 f s b) (@lem7145301 _133668 f s b)). Qed.
Lemma lem7145303 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term301 _133668 f s) = (term354 _133668 f s).
Proof. exact (fun_ext (fun b : real => @lem7145302 _133668 f s b)). Qed.
Lemma lem7145304 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7145305 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term302 _133668 f s) = (term355 _133668 f s).
Proof. exact (MK_COMB (@lem7145304) (@lem7145303 _133668 f s)). Qed.
Lemma lem7145307 {A B : Type'} (P : type1413 A B) : (term356 A B P) = (term357 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7145308 {_133668 : Type'} (P : type1620 _133668) : (term358 _133668 P) = (term359 _133668 P).
Proof. exact (@lem7145307 real _133668 P). Qed.
Lemma lem7145309 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term360 _133668 f s) = (term361 _133668 f s).
Proof. exact (@lem7145308 _133668 (term362 _133668 f s)). Qed.
Lemma lem7145310 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term363 _133668 f s b) = (term352 _133668 f s b).
Proof. exact (eq_refl (term363 _133668 f s b)). Qed.
Lemma lem7145311 {_133668 : Type'} (x : _133668) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7145312 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) (x : _133668) : (term364 _133668 f s b x) = (term365 _133668 f s b x).
Proof. exact (MK_COMB (@lem7145310 _133668 f s b) (@lem7145311 _133668 x)). Qed.
Lemma lem7145313 {_133668 : Type'} (x : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term365 _133668 f s b x) = (term350 _133668 x f s b).
Proof. exact (eq_refl (term365 _133668 f s b x)). Qed.
Lemma lem7145314 {_133668 : Type'} (x : _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term364 _133668 f s b x) = (term350 _133668 x f s b).
Proof. exact (TRANS (@lem7145312 _133668 f s b x) (@lem7145313 _133668 x f s b)). Qed.
Lemma lem7145315 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term366 _133668 f s b) = (term352 _133668 f s b).
Proof. exact (fun_ext (fun x : _133668 => @lem7145314 _133668 x f s b)). Qed.
Lemma lem7145316 {_133668 : Type'} : (@ex _133668) = (@ex _133668).
Proof. exact (eq_refl (@ex _133668)). Qed.
Lemma lem7145317 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term367 _133668 f s b) = (term353 _133668 f s b).
Proof. exact (MK_COMB (@lem7145316 _133668) (@lem7145315 _133668 f s b)). Qed.
Lemma lem7145318 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term368 _133668 f s) = (term354 _133668 f s).
Proof. exact (fun_ext (fun b : real => @lem7145317 _133668 f s b)). Qed.
Lemma lem7145319 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7145320 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term360 _133668 f s) = (term355 _133668 f s).
Proof. exact (MK_COMB (@lem7145319) (@lem7145318 _133668 f s)). Qed.
Lemma lem7145321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7145322 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term369 _133668 f s) = (term370 _133668 f s).
Proof. exact (MK_COMB (@lem7145321) (@lem7145320 _133668 f s)). Qed.
Lemma lem7145323 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term363 _133668 f s b) = (term352 _133668 f s b).
Proof. exact (eq_refl (term363 _133668 f s b)). Qed.
Lemma lem7145324 {_133668 : Type'} (x : real -> _133668) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem7145325 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (x : real -> _133668) (b : real) : (term371 _133668 f s x b) = (term372 _133668 f s x b).
Proof. exact (MK_COMB (@lem7145323 _133668 f s b) (@lem7145324 _133668 x b)). Qed.
Lemma lem7145326 {_133668 : Type'} (x : real -> _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term372 _133668 f s x b) = (term373 _133668 x f s b).
Proof. exact (eq_refl (term372 _133668 f s x b)). Qed.
Lemma lem7145327 {_133668 : Type'} (x : real -> _133668) (f : _133668 -> real) (s : _133668 -> Prop) (b : real) : (term371 _133668 f s x b) = (term373 _133668 x f s b).
Proof. exact (TRANS (@lem7145325 _133668 f s x b) (@lem7145326 _133668 x f s b)). Qed.
Lemma lem7145328 {_133668 : Type'} (x : real -> _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term374 _133668 f s x) = (term375 _133668 x f s).
Proof. exact (fun_ext (fun b : real => @lem7145327 _133668 x f s b)). Qed.
Lemma lem7145329 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7145330 {_133668 : Type'} (x : real -> _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term376 _133668 f s x) = (term377 _133668 x f s).
Proof. exact (MK_COMB (@lem7145329) (@lem7145328 _133668 x f s)). Qed.
Lemma lem7145331 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term378 _133668 f s) = (term379 _133668 f s).
Proof. exact (fun_ext (fun x : real -> _133668 => @lem7145330 _133668 x f s)). Qed.
Lemma lem7145332 {_133668 : Type'} : (@ex (real -> _133668)) = (@ex (real -> _133668)).
Proof. exact (eq_refl (@ex (real -> _133668))). Qed.
Lemma lem7145333 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term361 _133668 f s) = (term380 _133668 f s).
Proof. exact (MK_COMB (@lem7145332 _133668) (@lem7145331 _133668 f s)). Qed.
Lemma lem7145334 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : ((term360 _133668 f s) = (term361 _133668 f s)) = ((term355 _133668 f s) = (term380 _133668 f s)).
Proof. exact (MK_COMB (@lem7145322 _133668 f s) (@lem7145333 _133668 f s)). Qed.
Lemma lem7145335 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term355 _133668 f s) = (term380 _133668 f s).
Proof. exact (EQ_MP (@lem7145334 _133668 f s) (@lem7145309 _133668 f s)). Qed.
Lemma lem7145336 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term302 _133668 f s) = (term380 _133668 f s).
Proof. exact (TRANS (@lem7145305 _133668 f s) (@lem7145335 _133668 f s)). Qed.
Lemma lem7145337 {_133668 : Type'} (s : _133668 -> Prop) : (term303 _133668 s) = (term381 _133668 s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7145336 _133668 f s)). Qed.
Lemma lem7145338 {_133668 : Type'} : (@all (_133668 -> real)) = (@all (_133668 -> real)).
Proof. exact (eq_refl (@all (_133668 -> real))). Qed.
Lemma lem7145339 {_133668 : Type'} (s : _133668 -> Prop) : (term304 _133668 s) = (term382 _133668 s).
Proof. exact (MK_COMB (@lem7145338 _133668) (@lem7145337 _133668 s)). Qed.
Lemma lem7145341 {A B : Type'} (P : type1413 A B) : (term356 A B P) = (term357 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7145342 {_133668 : Type'} (P : type713 _133668) : (term383 _133668 P) = (term384 _133668 P).
Proof. exact (@lem7145341 (_133668 -> real) (real -> _133668) P). Qed.
Lemma lem7145343 {_133668 : Type'} (s : _133668 -> Prop) : (term385 _133668 s) = (term386 _133668 s).
Proof. exact (@lem7145342 _133668 (term387 _133668 s)). Qed.
Lemma lem7145344 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term388 _133668 s f) = (term379 _133668 f s).
Proof. exact (eq_refl (term388 _133668 s f)). Qed.
Lemma lem7145345 {_133668 : Type'} (x : real -> _133668) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7145346 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) (x : real -> _133668) : (term389 _133668 s f x) = (term390 _133668 f s x).
Proof. exact (MK_COMB (@lem7145344 _133668 f s) (@lem7145345 _133668 x)). Qed.
Lemma lem7145347 {_133668 : Type'} (x : real -> _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term390 _133668 f s x) = (term377 _133668 x f s).
Proof. exact (eq_refl (term390 _133668 f s x)). Qed.
Lemma lem7145348 {_133668 : Type'} (x : real -> _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term389 _133668 s f x) = (term377 _133668 x f s).
Proof. exact (TRANS (@lem7145346 _133668 f s x) (@lem7145347 _133668 x f s)). Qed.
Lemma lem7145349 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term391 _133668 s f) = (term379 _133668 f s).
Proof. exact (fun_ext (fun x : real -> _133668 => @lem7145348 _133668 x f s)). Qed.
Lemma lem7145350 {_133668 : Type'} : (@ex (real -> _133668)) = (@ex (real -> _133668)).
Proof. exact (eq_refl (@ex (real -> _133668))). Qed.
Lemma lem7145351 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term392 _133668 s f) = (term380 _133668 f s).
Proof. exact (MK_COMB (@lem7145350 _133668) (@lem7145349 _133668 f s)). Qed.
Lemma lem7145352 {_133668 : Type'} (s : _133668 -> Prop) : (term393 _133668 s) = (term381 _133668 s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7145351 _133668 f s)). Qed.
Lemma lem7145353 {_133668 : Type'} : (@all (_133668 -> real)) = (@all (_133668 -> real)).
Proof. exact (eq_refl (@all (_133668 -> real))). Qed.
Lemma lem7145354 {_133668 : Type'} (s : _133668 -> Prop) : (term385 _133668 s) = (term382 _133668 s).
Proof. exact (MK_COMB (@lem7145353 _133668) (@lem7145352 _133668 s)). Qed.
Lemma lem7145355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7145356 {_133668 : Type'} (s : _133668 -> Prop) : (term394 _133668 s) = (term395 _133668 s).
Proof. exact (MK_COMB (@lem7145355) (@lem7145354 _133668 s)). Qed.
Lemma lem7145357 {_133668 : Type'} (f : _133668 -> real) (s : _133668 -> Prop) : (term388 _133668 s f) = (term379 _133668 f s).
Proof. exact (eq_refl (term388 _133668 s f)). Qed.
Lemma lem7145358 {_133668 : Type'} (x : type715 _133668) (f : _133668 -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7145359 {_133668 : Type'} (s : _133668 -> Prop) (x : type715 _133668) (f : _133668 -> real) : (term396 _133668 s x f) = (term397 _133668 s x f).
Proof. exact (MK_COMB (@lem7145357 _133668 f s) (@lem7145358 _133668 x f)). Qed.
Lemma lem7145360 {_133668 : Type'} (x : type715 _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term397 _133668 s x f) = (term398 _133668 x f s).
Proof. exact (eq_refl (term397 _133668 s x f)). Qed.
Lemma lem7145361 {_133668 : Type'} (x : type715 _133668) (f : _133668 -> real) (s : _133668 -> Prop) : (term396 _133668 s x f) = (term398 _133668 x f s).
Proof. exact (TRANS (@lem7145359 _133668 s x f) (@lem7145360 _133668 x f s)). Qed.
Lemma lem7145362 {_133668 : Type'} (x : type715 _133668) (s : _133668 -> Prop) : (term399 _133668 s x) = (term400 _133668 x s).
Proof. exact (fun_ext (fun f : _133668 -> real => @lem7145361 _133668 x f s)). Qed.
Lemma lem7145363 {_133668 : Type'} : (@all (_133668 -> real)) = (@all (_133668 -> real)).
Proof. exact (eq_refl (@all (_133668 -> real))). Qed.
Lemma lem7145364 {_133668 : Type'} (x : type715 _133668) (s : _133668 -> Prop) : (term401 _133668 s x) = (term402 _133668 x s).
Proof. exact (MK_COMB (@lem7145363 _133668) (@lem7145362 _133668 x s)). Qed.
Lemma lem7145365 {_133668 : Type'} (s : _133668 -> Prop) : (term403 _133668 s) = (term404 _133668 s).
Proof. exact (fun_ext (fun x : type715 _133668 => @lem7145364 _133668 x s)). Qed.
Lemma lem7145366 {_133668 : Type'} : (@ex ((_133668 -> real) -> real -> _133668)) = (@ex ((_133668 -> real) -> real -> _133668)).
Proof. exact (eq_refl (@ex ((_133668 -> real) -> real -> _133668))). Qed.
Lemma lem7145367 {_133668 : Type'} (s : _133668 -> Prop) : (term386 _133668 s) = (term405 _133668 s).
Proof. exact (MK_COMB (@lem7145366 _133668) (@lem7145365 _133668 s)). Qed.
Lemma lem7145368 {_133668 : Type'} (s : _133668 -> Prop) : ((term385 _133668 s) = (term386 _133668 s)) = ((term382 _133668 s) = (term405 _133668 s)).
Proof. exact (MK_COMB (@lem7145356 _133668 s) (@lem7145367 _133668 s)). Qed.
Lemma lem7145369 {_133668 : Type'} (s : _133668 -> Prop) : (term382 _133668 s) = (term405 _133668 s).
Proof. exact (EQ_MP (@lem7145368 _133668 s) (@lem7145343 _133668 s)). Qed.
Lemma lem7145370 {_133668 : Type'} (s : _133668 -> Prop) : (term304 _133668 s) = (term405 _133668 s).
Proof. exact (TRANS (@lem7145339 _133668 s) (@lem7145369 _133668 s)). Qed.
Lemma lem7145371 {_133668 : Type'} : (term305 _133668) = (term406 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7145370 _133668 s)). Qed.
Lemma lem7145372 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7145373 {_133668 : Type'} : (term306 _133668) = (term407 _133668).
Proof. exact (MK_COMB (@lem7145372 _133668) (@lem7145371 _133668)). Qed.
Lemma lem7145375 {A B : Type'} (P : type1413 A B) : (term356 A B P) = (term357 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7145376 {_133668 : Type'} (P : type603 _133668) : (term408 _133668 P) = (term409 _133668 P).
Proof. exact (@lem7145375 (_133668 -> Prop) (type715 _133668) P). Qed.
Lemma lem7145377 {_133668 : Type'} : (term410 _133668) = (term411 _133668).
Proof. exact (@lem7145376 _133668 (term412 _133668)). Qed.
Lemma lem7145378 {_133668 : Type'} (s : _133668 -> Prop) : (term413 _133668 s) = (term404 _133668 s).
Proof. exact (eq_refl (term413 _133668 s)). Qed.
Lemma lem7145379 {_133668 : Type'} (x : type715 _133668) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7145380 {_133668 : Type'} (s : _133668 -> Prop) (x : type715 _133668) : (term414 _133668 s x) = (term415 _133668 s x).
Proof. exact (MK_COMB (@lem7145378 _133668 s) (@lem7145379 _133668 x)). Qed.
Lemma lem7145381 {_133668 : Type'} (x : type715 _133668) (s : _133668 -> Prop) : (term415 _133668 s x) = (term402 _133668 x s).
Proof. exact (eq_refl (term415 _133668 s x)). Qed.
Lemma lem7145382 {_133668 : Type'} (x : type715 _133668) (s : _133668 -> Prop) : (term414 _133668 s x) = (term402 _133668 x s).
Proof. exact (TRANS (@lem7145380 _133668 s x) (@lem7145381 _133668 x s)). Qed.
Lemma lem7145383 {_133668 : Type'} (s : _133668 -> Prop) : (term416 _133668 s) = (term404 _133668 s).
Proof. exact (fun_ext (fun x : type715 _133668 => @lem7145382 _133668 x s)). Qed.
Lemma lem7145384 {_133668 : Type'} : (@ex ((_133668 -> real) -> real -> _133668)) = (@ex ((_133668 -> real) -> real -> _133668)).
Proof. exact (eq_refl (@ex ((_133668 -> real) -> real -> _133668))). Qed.
Lemma lem7145385 {_133668 : Type'} (s : _133668 -> Prop) : (term417 _133668 s) = (term405 _133668 s).
Proof. exact (MK_COMB (@lem7145384 _133668) (@lem7145383 _133668 s)). Qed.
Lemma lem7145386 {_133668 : Type'} : (term418 _133668) = (term406 _133668).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7145385 _133668 s)). Qed.
Lemma lem7145387 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7145388 {_133668 : Type'} : (term410 _133668) = (term407 _133668).
Proof. exact (MK_COMB (@lem7145387 _133668) (@lem7145386 _133668)). Qed.
Lemma lem7145389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7145390 {_133668 : Type'} : (term419 _133668) = (term420 _133668).
Proof. exact (MK_COMB (@lem7145389) (@lem7145388 _133668)). Qed.
Lemma lem7145391 {_133668 : Type'} (s : _133668 -> Prop) : (term413 _133668 s) = (term404 _133668 s).
Proof. exact (eq_refl (term413 _133668 s)). Qed.
Lemma lem7145392 {_133668 : Type'} (x : type645 _133668) (s : _133668 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7145393 {_133668 : Type'} (x : type645 _133668) (s : _133668 -> Prop) : (term421 _133668 x s) = (term422 _133668 x s).
Proof. exact (MK_COMB (@lem7145391 _133668 s) (@lem7145392 _133668 x s)). Qed.
Lemma lem7145394 {_133668 : Type'} (x : type645 _133668) (s : _133668 -> Prop) : (term422 _133668 x s) = (term423 _133668 x s).
Proof. exact (eq_refl (term422 _133668 x s)). Qed.
Lemma lem7145395 {_133668 : Type'} (x : type645 _133668) (s : _133668 -> Prop) : (term421 _133668 x s) = (term423 _133668 x s).
Proof. exact (TRANS (@lem7145393 _133668 x s) (@lem7145394 _133668 x s)). Qed.
Lemma lem7145396 {_133668 : Type'} (x : type645 _133668) : (term424 _133668 x) = (term425 _133668 x).
Proof. exact (fun_ext (fun s : _133668 -> Prop => @lem7145395 _133668 x s)). Qed.
Lemma lem7145397 {_133668 : Type'} : (@all (_133668 -> Prop)) = (@all (_133668 -> Prop)).
Proof. exact (eq_refl (@all (_133668 -> Prop))). Qed.
Lemma lem7145398 {_133668 : Type'} (x : type645 _133668) : (term426 _133668 x) = (term427 _133668 x).
Proof. exact (MK_COMB (@lem7145397 _133668) (@lem7145396 _133668 x)). Qed.
Lemma lem7145399 {_133668 : Type'} : (term428 _133668) = (term429 _133668).
Proof. exact (fun_ext (fun x : type645 _133668 => @lem7145398 _133668 x)). Qed.
Lemma lem7145400 {_133668 : Type'} : (@ex ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668)) = (@ex ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668)).
Proof. exact (eq_refl (@ex ((_133668 -> Prop) -> (_133668 -> real) -> real -> _133668))). Qed.
Lemma lem7145401 {_133668 : Type'} : (term411 _133668) = (term430 _133668).
Proof. exact (MK_COMB (@lem7145400 _133668) (@lem7145399 _133668)). Qed.
Lemma lem7145402 {_133668 : Type'} : ((term410 _133668) = (term411 _133668)) = ((term407 _133668) = (term430 _133668)).
Proof. exact (MK_COMB (@lem7145390 _133668) (@lem7145401 _133668)). Qed.
Lemma lem7145403 {_133668 : Type'} : (term407 _133668) = (term430 _133668).
Proof. exact (EQ_MP (@lem7145402 _133668) (@lem7145377 _133668)). Qed.
Lemma lem7145405 {_133668 : Type'} : (term306 _133668) = (term430 _133668).
Proof. exact (TRANS (@lem7145373 _133668) (@lem7145403 _133668)). Qed.
Lemma lem7145406 {_133668 : Type'} : (term11 _133668) = (term430 _133668).
Proof. exact (TRANS (@lem7145125 _133668) (@lem7145405 _133668)). Qed.
Lemma lem7145407 {_133668 : Type'} (h1 : term11 _133668) : term430 _133668.
Proof. exact (EQ_MP (@lem7145406 _133668) (@lem7143375 _133668 h1)). Qed.
Lemma lem7145411 {A : Type'} (s : A -> Prop) : (term274 A s) = (s = (@EMPTY A)).
Proof. exact (@lem16933 (s = (@EMPTY A))). Qed.
Lemma lem7145418 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term275 A s f x b) = (term276 A s f x b).
Proof. exact (@lem17362 (@IN A x s) (term277 A f x b)). Qed.
Lemma lem7145419 {A : Type'} (P : A -> Prop) : (term278 A P) = (term279 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7145420 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term280 A s f b) = (term281 A s f b).
Proof. exact (@lem7145419 A (term45 A s f b)). Qed.
Lemma lem7145421 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term282 A s f b x) = (term44 A s f x b).
Proof. exact (eq_refl (term282 A s f b x)). Qed.
Lemma lem7145422 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7145423 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term283 A s f b x) = (term275 A s f x b).
Proof. exact (MK_COMB (@lem7145422) (@lem7145421 A s f x b)). Qed.
Lemma lem7145424 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term283 A s f b x) = (term276 A s f x b).
Proof. exact (TRANS (@lem7145423 A s f x b) (@lem7145418 A s f x b)). Qed.
Lemma lem7145425 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term284 A s f b) = (term285 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7145424 A s f x b)). Qed.
Lemma lem7145426 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7145427 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term281 A s f b) = (term286 A s f b).
Proof. exact (MK_COMB (@lem7145426 A) (@lem7145425 A s f b)). Qed.
Lemma lem7145428 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term280 A s f b) = (term286 A s f b).
Proof. exact (TRANS (@lem7145420 A s f b) (@lem7145427 A s f b)). Qed.
Lemma lem7145429 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7145430 {A : Type'} (s : A -> Prop) : (term287 A s) = (term288 A s).
Proof. exact (MK_COMB (@lem7145429) (@lem7145411 A s)). Qed.
Lemma lem7145431 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term289 A s f b) = (term290 A s f b).
Proof. exact (MK_COMB (@lem7145430 A s) (@lem7145428 A s f b)). Qed.
Lemma lem7145432 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term291 A s f b) = (term289 A s f b).
Proof. exact (@lem17045 (term292 A s) (term46 A s f b)). Qed.
Lemma lem7145433 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term291 A s f b) = (term290 A s f b).
Proof. exact (TRANS (@lem7145432 A s f b) (@lem7145431 A s f b)). Qed.
Lemma lem7145435 {A : Type'} (s : A -> Prop) : (term293 A s) = (term293 A s).
Proof. exact (eq_refl (term293 A s)). Qed.
Lemma lem7145436 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term294 A s f b) = (term295 A s f b).
Proof. exact (MK_COMB (@lem7145435 A s) (@lem7145433 A s f b)). Qed.
Lemma lem7145437 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term296 A s f b) = (term294 A s f b).
Proof. exact (@lem17045 (@FINITE A s) (term48 A s f b)). Qed.
Lemma lem7145438 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term296 A s f b) = (term295 A s f b).
Proof. exact (TRANS (@lem7145437 A s f b) (@lem7145436 A s f b)). Qed.
Lemma lem7145439 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term43 A f s b) = (term43 A f s b).
Proof. exact (eq_refl (term43 A f s b)). Qed.
Lemma lem7145440 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7145441 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term297 A s f b) = (term298 A s f b).
Proof. exact (MK_COMB (@lem7145440) (@lem7145438 A s f b)). Qed.
Lemma lem7145442 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term299 A f s b) = (term300 A f s b).
Proof. exact (MK_COMB (@lem7145441 A s f b) (@lem7145439 A f s b)). Qed.
Lemma lem7145443 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term52 A f s b) = (term299 A f s b).
Proof. exact (@lem17265 (term50 A s f b) (term43 A f s b)). Qed.
Lemma lem7145444 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term52 A f s b) = (term300 A f s b).
Proof. exact (TRANS (@lem7145443 A f s b) (@lem7145442 A f s b)). Qed.
Lemma lem7145445 {A : Type'} (f : A -> real) (s : A -> Prop) : (term53 A f s) = (term301 A f s).
Proof. exact (fun_ext (fun b : real => @lem7145444 A f s b)). Qed.
Lemma lem7145446 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7145447 {A : Type'} (f : A -> real) (s : A -> Prop) : (term54 A f s) = (term302 A f s).
Proof. exact (MK_COMB (@lem7145446) (@lem7145445 A f s)). Qed.
Lemma lem7145448 {A : Type'} (s : A -> Prop) : (term55 A s) = (term303 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7145447 A f s)). Qed.
Lemma lem7145449 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7145450 {A : Type'} (s : A -> Prop) : (term56 A s) = (term304 A s).
Proof. exact (MK_COMB (@lem7145449 A) (@lem7145448 A s)). Qed.
Lemma lem7145451 {A : Type'} : (term57 A) = (term305 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7145450 A s)). Qed.
Lemma lem7145452 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7145453 {A : Type'} : (term11 A) = (term306 A).
Proof. exact (MK_COMB (@lem7145452 A) (@lem7145451 A)). Qed.
Lemma lem7145560 {A : Type'} (P : Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7145561 {A : Type'} (P : Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (@lem7145560 A P Q). Qed.
Lemma lem7145562 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term309 A s f b) = (term310 A s f b).
Proof. exact (@lem7145561 A (s = (@EMPTY A)) (term285 A s f b)). Qed.
Lemma lem7145563 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term311 A s f b x) = (term276 A s f x b).
Proof. exact (eq_refl (term311 A s f b x)). Qed.
Lemma lem7145564 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term312 A s f b) = (term285 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7145563 A s f x b)). Qed.
Lemma lem7145565 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7145566 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term313 A s f b) = (term286 A s f b).
Proof. exact (MK_COMB (@lem7145565 A) (@lem7145564 A s f b)). Qed.
Lemma lem7145567 {A : Type'} (s : A -> Prop) : (term288 A s) = (term288 A s).
Proof. exact (eq_refl (term288 A s)). Qed.
Lemma lem7145568 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term309 A s f b) = (term290 A s f b).
Proof. exact (MK_COMB (@lem7145567 A s) (@lem7145566 A s f b)). Qed.
Lemma lem7145569 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7145570 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term314 A s f b) = (term315 A s f b).
Proof. exact (MK_COMB (@lem7145569) (@lem7145568 A s f b)). Qed.
Lemma lem7145571 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term311 A s f b x) = (term276 A s f x b).
Proof. exact (eq_refl (term311 A s f b x)). Qed.
Lemma lem7145572 {A : Type'} (s : A -> Prop) : (term288 A s) = (term288 A s).
Proof. exact (eq_refl (term288 A s)). Qed.
Lemma lem7145573 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term316 A s f b x) = (term317 A s f x b).
Proof. exact (MK_COMB (@lem7145572 A s) (@lem7145571 A s f x b)). Qed.
Lemma lem7145574 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term318 A s f b) = (term319 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7145573 A s f x b)). Qed.
Lemma lem7145575 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7145576 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term310 A s f b) = (term320 A s f b).
Proof. exact (MK_COMB (@lem7145575 A) (@lem7145574 A s f b)). Qed.
Lemma lem7145577 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : ((term309 A s f b) = (term310 A s f b)) = ((term290 A s f b) = (term320 A s f b)).
Proof. exact (MK_COMB (@lem7145570 A s f b) (@lem7145576 A s f b)). Qed.
Lemma lem7145578 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term290 A s f b) = (term320 A s f b).
Proof. exact (EQ_MP (@lem7145577 A s f b) (@lem7145562 A s f b)). Qed.
Lemma lem7145579 {A : Type'} (s : A -> Prop) : (term293 A s) = (term293 A s).
Proof. exact (eq_refl (term293 A s)). Qed.
Lemma lem7145580 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term295 A s f b) = (term321 A s f b).
Proof. exact (MK_COMB (@lem7145579 A s) (@lem7145578 A s f b)). Qed.
Lemma lem7145582 {A : Type'} (P : Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7145583 {A : Type'} (P : Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (@lem7145582 A P Q). Qed.
Lemma lem7145584 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term322 A s f b) = (term323 A s f b).
Proof. exact (@lem7145583 A (term324 A s) (term319 A s f b)). Qed.
Lemma lem7145585 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term325 A s f b x) = (term317 A s f x b).
Proof. exact (eq_refl (term325 A s f b x)). Qed.
Lemma lem7145586 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term326 A s f b) = (term319 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7145585 A s f x b)). Qed.
Lemma lem7145587 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7145588 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term327 A s f b) = (term320 A s f b).
Proof. exact (MK_COMB (@lem7145587 A) (@lem7145586 A s f b)). Qed.
Lemma lem7145589 {A : Type'} (s : A -> Prop) : (term293 A s) = (term293 A s).
Proof. exact (eq_refl (term293 A s)). Qed.
Lemma lem7145590 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term322 A s f b) = (term321 A s f b).
Proof. exact (MK_COMB (@lem7145589 A s) (@lem7145588 A s f b)). Qed.
Lemma lem7145591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7145592 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term328 A s f b) = (term329 A s f b).
Proof. exact (MK_COMB (@lem7145591) (@lem7145590 A s f b)). Qed.
Lemma lem7145593 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term325 A s f b x) = (term317 A s f x b).
Proof. exact (eq_refl (term325 A s f b x)). Qed.
Lemma lem7145594 {A : Type'} (s : A -> Prop) : (term293 A s) = (term293 A s).
Proof. exact (eq_refl (term293 A s)). Qed.
Lemma lem7145595 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term330 A s f b x) = (term331 A s f x b).
Proof. exact (MK_COMB (@lem7145594 A s) (@lem7145593 A s f x b)). Qed.
Lemma lem7145596 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term332 A s f b) = (term333 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7145595 A s f x b)). Qed.
Lemma lem7145597 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7145598 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term323 A s f b) = (term334 A s f b).
Proof. exact (MK_COMB (@lem7145597 A) (@lem7145596 A s f b)). Qed.
Lemma lem7145599 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : ((term322 A s f b) = (term323 A s f b)) = ((term321 A s f b) = (term334 A s f b)).
Proof. exact (MK_COMB (@lem7145592 A s f b) (@lem7145598 A s f b)). Qed.
Lemma lem7145600 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term321 A s f b) = (term334 A s f b).
Proof. exact (EQ_MP (@lem7145599 A s f b) (@lem7145584 A s f b)). Qed.
Lemma lem7145601 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term295 A s f b) = (term334 A s f b).
Proof. exact (TRANS (@lem7145580 A s f b) (@lem7145600 A s f b)). Qed.
Lemma lem7145602 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7145603 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term298 A s f b) = (term335 A s f b).
Proof. exact (MK_COMB (@lem7145602) (@lem7145601 A s f b)). Qed.
Lemma lem7145604 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term43 A f s b) = (term43 A f s b).
Proof. exact (eq_refl (term43 A f s b)). Qed.
Lemma lem7145605 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term300 A f s b) = (term336 A f s b).
Proof. exact (MK_COMB (@lem7145603 A s f b) (@lem7145604 A f s b)). Qed.
Lemma lem7145607 {A : Type'} (P : A -> Prop) (Q : Prop) : (term337 A P Q) = (term338 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7145608 {A : Type'} (P : A -> Prop) (Q : Prop) : (term337 A P Q) = (term338 A P Q).
Proof. exact (@lem7145607 A P Q). Qed.
Lemma lem7145609 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term339 A f s b) = (term340 A f s b).
Proof. exact (@lem7145608 A (term333 A s f b) (term43 A f s b)). Qed.
Lemma lem7145610 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term341 A s f b x) = (term331 A s f x b).
Proof. exact (eq_refl (term341 A s f b x)). Qed.
Lemma lem7145611 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term342 A s f b) = (term333 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7145610 A s f x b)). Qed.
Lemma lem7145612 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7145613 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term343 A s f b) = (term334 A s f b).
Proof. exact (MK_COMB (@lem7145612 A) (@lem7145611 A s f b)). Qed.
Lemma lem7145614 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7145615 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term344 A s f b) = (term335 A s f b).
Proof. exact (MK_COMB (@lem7145614) (@lem7145613 A s f b)). Qed.
Lemma lem7145616 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term43 A f s b) = (term43 A f s b).
Proof. exact (eq_refl (term43 A f s b)). Qed.
Lemma lem7145617 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term339 A f s b) = (term336 A f s b).
Proof. exact (MK_COMB (@lem7145615 A s f b) (@lem7145616 A f s b)). Qed.
Lemma lem7145618 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7145619 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term345 A f s b) = (term346 A f s b).
Proof. exact (MK_COMB (@lem7145618) (@lem7145617 A f s b)). Qed.
Lemma lem7145620 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term341 A s f b x) = (term331 A s f x b).
Proof. exact (eq_refl (term341 A s f b x)). Qed.
Lemma lem7145621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7145622 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term347 A s f b x) = (term348 A s f x b).
Proof. exact (MK_COMB (@lem7145621) (@lem7145620 A s f x b)). Qed.
Lemma lem7145623 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term43 A f s b) = (term43 A f s b).
Proof. exact (eq_refl (term43 A f s b)). Qed.
Lemma lem7145624 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (b : real) : (term349 A x f s b) = (term350 A x f s b).
Proof. exact (MK_COMB (@lem7145622 A s f x b) (@lem7145623 A f s b)). Qed.
Lemma lem7145625 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term351 A f s b) = (term352 A f s b).
Proof. exact (fun_ext (fun x : A => @lem7145624 A x f s b)). Qed.
Lemma lem7145626 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7145627 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term340 A f s b) = (term353 A f s b).
Proof. exact (MK_COMB (@lem7145626 A) (@lem7145625 A f s b)). Qed.
Lemma lem7145628 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : ((term339 A f s b) = (term340 A f s b)) = ((term336 A f s b) = (term353 A f s b)).
Proof. exact (MK_COMB (@lem7145619 A f s b) (@lem7145627 A f s b)). Qed.
Lemma lem7145629 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term336 A f s b) = (term353 A f s b).
Proof. exact (EQ_MP (@lem7145628 A f s b) (@lem7145609 A f s b)). Qed.
Lemma lem7145630 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term300 A f s b) = (term353 A f s b).
Proof. exact (TRANS (@lem7145605 A f s b) (@lem7145629 A f s b)). Qed.
Lemma lem7145631 {A : Type'} (f : A -> real) (s : A -> Prop) : (term301 A f s) = (term354 A f s).
Proof. exact (fun_ext (fun b : real => @lem7145630 A f s b)). Qed.
Lemma lem7145632 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7145633 {A : Type'} (f : A -> real) (s : A -> Prop) : (term302 A f s) = (term355 A f s).
Proof. exact (MK_COMB (@lem7145632) (@lem7145631 A f s)). Qed.
Lemma lem7145635 {A B : Type'} (P : type1413 A B) : (term356 A B P) = (term357 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7145636 {A : Type'} (P : type1620 A) : (term358 A P) = (term359 A P).
Proof. exact (@lem7145635 real A P). Qed.
Lemma lem7145637 {A : Type'} (f : A -> real) (s : A -> Prop) : (term360 A f s) = (term361 A f s).
Proof. exact (@lem7145636 A (term362 A f s)). Qed.
Lemma lem7145638 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term363 A f s b) = (term352 A f s b).
Proof. exact (eq_refl (term363 A f s b)). Qed.
Lemma lem7145639 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7145640 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) (x : A) : (term364 A f s b x) = (term365 A f s b x).
Proof. exact (MK_COMB (@lem7145638 A f s b) (@lem7145639 A x)). Qed.
Lemma lem7145641 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (b : real) : (term365 A f s b x) = (term350 A x f s b).
Proof. exact (eq_refl (term365 A f s b x)). Qed.
Lemma lem7145642 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (b : real) : (term364 A f s b x) = (term350 A x f s b).
Proof. exact (TRANS (@lem7145640 A f s b x) (@lem7145641 A x f s b)). Qed.
Lemma lem7145643 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term366 A f s b) = (term352 A f s b).
Proof. exact (fun_ext (fun x : A => @lem7145642 A x f s b)). Qed.
Lemma lem7145644 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7145645 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term367 A f s b) = (term353 A f s b).
Proof. exact (MK_COMB (@lem7145644 A) (@lem7145643 A f s b)). Qed.
Lemma lem7145646 {A : Type'} (f : A -> real) (s : A -> Prop) : (term368 A f s) = (term354 A f s).
Proof. exact (fun_ext (fun b : real => @lem7145645 A f s b)). Qed.
Lemma lem7145647 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7145648 {A : Type'} (f : A -> real) (s : A -> Prop) : (term360 A f s) = (term355 A f s).
Proof. exact (MK_COMB (@lem7145647) (@lem7145646 A f s)). Qed.
Lemma lem7145649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7145650 {A : Type'} (f : A -> real) (s : A -> Prop) : (term369 A f s) = (term370 A f s).
Proof. exact (MK_COMB (@lem7145649) (@lem7145648 A f s)). Qed.
Lemma lem7145651 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term363 A f s b) = (term352 A f s b).
Proof. exact (eq_refl (term363 A f s b)). Qed.
Lemma lem7145652 {A : Type'} (x : real -> A) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem7145653 {A : Type'} (f : A -> real) (s : A -> Prop) (x : real -> A) (b : real) : (term371 A f s x b) = (term372 A f s x b).
Proof. exact (MK_COMB (@lem7145651 A f s b) (@lem7145652 A x b)). Qed.
Lemma lem7145654 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) (b : real) : (term372 A f s x b) = (term373 A x f s b).
Proof. exact (eq_refl (term372 A f s x b)). Qed.
Lemma lem7145655 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) (b : real) : (term371 A f s x b) = (term373 A x f s b).
Proof. exact (TRANS (@lem7145653 A f s x b) (@lem7145654 A x f s b)). Qed.
Lemma lem7145656 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) : (term374 A f s x) = (term375 A x f s).
Proof. exact (fun_ext (fun b : real => @lem7145655 A x f s b)). Qed.
Lemma lem7145657 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7145658 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) : (term376 A f s x) = (term377 A x f s).
Proof. exact (MK_COMB (@lem7145657) (@lem7145656 A x f s)). Qed.
Lemma lem7145659 {A : Type'} (f : A -> real) (s : A -> Prop) : (term378 A f s) = (term379 A f s).
Proof. exact (fun_ext (fun x : real -> A => @lem7145658 A x f s)). Qed.
Lemma lem7145660 {A : Type'} : (@ex (real -> A)) = (@ex (real -> A)).
Proof. exact (eq_refl (@ex (real -> A))). Qed.
Lemma lem7145661 {A : Type'} (f : A -> real) (s : A -> Prop) : (term361 A f s) = (term380 A f s).
Proof. exact (MK_COMB (@lem7145660 A) (@lem7145659 A f s)). Qed.
Lemma lem7145662 {A : Type'} (f : A -> real) (s : A -> Prop) : ((term360 A f s) = (term361 A f s)) = ((term355 A f s) = (term380 A f s)).
Proof. exact (MK_COMB (@lem7145650 A f s) (@lem7145661 A f s)). Qed.
Lemma lem7145663 {A : Type'} (f : A -> real) (s : A -> Prop) : (term355 A f s) = (term380 A f s).
Proof. exact (EQ_MP (@lem7145662 A f s) (@lem7145637 A f s)). Qed.
Lemma lem7145664 {A : Type'} (f : A -> real) (s : A -> Prop) : (term302 A f s) = (term380 A f s).
Proof. exact (TRANS (@lem7145633 A f s) (@lem7145663 A f s)). Qed.
Lemma lem7145665 {A : Type'} (s : A -> Prop) : (term303 A s) = (term381 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7145664 A f s)). Qed.
Lemma lem7145666 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7145667 {A : Type'} (s : A -> Prop) : (term304 A s) = (term382 A s).
Proof. exact (MK_COMB (@lem7145666 A) (@lem7145665 A s)). Qed.
Lemma lem7145669 {A B : Type'} (P : type1413 A B) : (term356 A B P) = (term357 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7145670 {A : Type'} (P : type713 A) : (term383 A P) = (term384 A P).
Proof. exact (@lem7145669 (A -> real) (real -> A) P). Qed.
Lemma lem7145671 {A : Type'} (s : A -> Prop) : (term385 A s) = (term386 A s).
Proof. exact (@lem7145670 A (term387 A s)). Qed.
Lemma lem7145672 {A : Type'} (f : A -> real) (s : A -> Prop) : (term388 A s f) = (term379 A f s).
Proof. exact (eq_refl (term388 A s f)). Qed.
Lemma lem7145673 {A : Type'} (x : real -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7145674 {A : Type'} (f : A -> real) (s : A -> Prop) (x : real -> A) : (term389 A s f x) = (term390 A f s x).
Proof. exact (MK_COMB (@lem7145672 A f s) (@lem7145673 A x)). Qed.
Lemma lem7145675 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) : (term390 A f s x) = (term377 A x f s).
Proof. exact (eq_refl (term390 A f s x)). Qed.
Lemma lem7145676 {A : Type'} (x : real -> A) (f : A -> real) (s : A -> Prop) : (term389 A s f x) = (term377 A x f s).
Proof. exact (TRANS (@lem7145674 A f s x) (@lem7145675 A x f s)). Qed.
Lemma lem7145677 {A : Type'} (f : A -> real) (s : A -> Prop) : (term391 A s f) = (term379 A f s).
Proof. exact (fun_ext (fun x : real -> A => @lem7145676 A x f s)). Qed.
Lemma lem7145678 {A : Type'} : (@ex (real -> A)) = (@ex (real -> A)).
Proof. exact (eq_refl (@ex (real -> A))). Qed.
Lemma lem7145679 {A : Type'} (f : A -> real) (s : A -> Prop) : (term392 A s f) = (term380 A f s).
Proof. exact (MK_COMB (@lem7145678 A) (@lem7145677 A f s)). Qed.
Lemma lem7145680 {A : Type'} (s : A -> Prop) : (term393 A s) = (term381 A s).
Proof. exact (fun_ext (fun f : A -> real => @lem7145679 A f s)). Qed.
Lemma lem7145681 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7145682 {A : Type'} (s : A -> Prop) : (term385 A s) = (term382 A s).
Proof. exact (MK_COMB (@lem7145681 A) (@lem7145680 A s)). Qed.
Lemma lem7145683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7145684 {A : Type'} (s : A -> Prop) : (term394 A s) = (term395 A s).
Proof. exact (MK_COMB (@lem7145683) (@lem7145682 A s)). Qed.
Lemma lem7145685 {A : Type'} (f : A -> real) (s : A -> Prop) : (term388 A s f) = (term379 A f s).
Proof. exact (eq_refl (term388 A s f)). Qed.
Lemma lem7145686 {A : Type'} (x : type715 A) (f : A -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7145687 {A : Type'} (s : A -> Prop) (x : type715 A) (f : A -> real) : (term396 A s x f) = (term397 A s x f).
Proof. exact (MK_COMB (@lem7145685 A f s) (@lem7145686 A x f)). Qed.
Lemma lem7145688 {A : Type'} (x : type715 A) (f : A -> real) (s : A -> Prop) : (term397 A s x f) = (term398 A x f s).
Proof. exact (eq_refl (term397 A s x f)). Qed.
Lemma lem7145689 {A : Type'} (x : type715 A) (f : A -> real) (s : A -> Prop) : (term396 A s x f) = (term398 A x f s).
Proof. exact (TRANS (@lem7145687 A s x f) (@lem7145688 A x f s)). Qed.
Lemma lem7145690 {A : Type'} (x : type715 A) (s : A -> Prop) : (term399 A s x) = (term400 A x s).
Proof. exact (fun_ext (fun f : A -> real => @lem7145689 A x f s)). Qed.
Lemma lem7145691 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7145692 {A : Type'} (x : type715 A) (s : A -> Prop) : (term401 A s x) = (term402 A x s).
Proof. exact (MK_COMB (@lem7145691 A) (@lem7145690 A x s)). Qed.
Lemma lem7145693 {A : Type'} (s : A -> Prop) : (term403 A s) = (term404 A s).
Proof. exact (fun_ext (fun x : type715 A => @lem7145692 A x s)). Qed.
Lemma lem7145694 {A : Type'} : (@ex ((A -> real) -> real -> A)) = (@ex ((A -> real) -> real -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> real -> A))). Qed.
Lemma lem7145695 {A : Type'} (s : A -> Prop) : (term386 A s) = (term405 A s).
Proof. exact (MK_COMB (@lem7145694 A) (@lem7145693 A s)). Qed.
Lemma lem7145696 {A : Type'} (s : A -> Prop) : ((term385 A s) = (term386 A s)) = ((term382 A s) = (term405 A s)).
Proof. exact (MK_COMB (@lem7145684 A s) (@lem7145695 A s)). Qed.
Lemma lem7145697 {A : Type'} (s : A -> Prop) : (term382 A s) = (term405 A s).
Proof. exact (EQ_MP (@lem7145696 A s) (@lem7145671 A s)). Qed.
Lemma lem7145698 {A : Type'} (s : A -> Prop) : (term304 A s) = (term405 A s).
Proof. exact (TRANS (@lem7145667 A s) (@lem7145697 A s)). Qed.
Lemma lem7145699 {A : Type'} : (term305 A) = (term406 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7145698 A s)). Qed.
Lemma lem7145700 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7145701 {A : Type'} : (term306 A) = (term407 A).
Proof. exact (MK_COMB (@lem7145700 A) (@lem7145699 A)). Qed.
Lemma lem7145703 {A B : Type'} (P : type1413 A B) : (term356 A B P) = (term357 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7145704 {A : Type'} (P : type603 A) : (term408 A P) = (term409 A P).
Proof. exact (@lem7145703 (A -> Prop) (type715 A) P). Qed.
Lemma lem7145705 {A : Type'} : (term410 A) = (term411 A).
Proof. exact (@lem7145704 A (term412 A)). Qed.
Lemma lem7145706 {A : Type'} (s : A -> Prop) : (term413 A s) = (term404 A s).
Proof. exact (eq_refl (term413 A s)). Qed.
Lemma lem7145707 {A : Type'} (x : type715 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7145708 {A : Type'} (s : A -> Prop) (x : type715 A) : (term414 A s x) = (term415 A s x).
Proof. exact (MK_COMB (@lem7145706 A s) (@lem7145707 A x)). Qed.
Lemma lem7145709 {A : Type'} (x : type715 A) (s : A -> Prop) : (term415 A s x) = (term402 A x s).
Proof. exact (eq_refl (term415 A s x)). Qed.
Lemma lem7145710 {A : Type'} (x : type715 A) (s : A -> Prop) : (term414 A s x) = (term402 A x s).
Proof. exact (TRANS (@lem7145708 A s x) (@lem7145709 A x s)). Qed.
Lemma lem7145711 {A : Type'} (s : A -> Prop) : (term416 A s) = (term404 A s).
Proof. exact (fun_ext (fun x : type715 A => @lem7145710 A x s)). Qed.
Lemma lem7145712 {A : Type'} : (@ex ((A -> real) -> real -> A)) = (@ex ((A -> real) -> real -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> real -> A))). Qed.
Lemma lem7145713 {A : Type'} (s : A -> Prop) : (term417 A s) = (term405 A s).
Proof. exact (MK_COMB (@lem7145712 A) (@lem7145711 A s)). Qed.
Lemma lem7145714 {A : Type'} : (term418 A) = (term406 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7145713 A s)). Qed.
Lemma lem7145715 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7145716 {A : Type'} : (term410 A) = (term407 A).
Proof. exact (MK_COMB (@lem7145715 A) (@lem7145714 A)). Qed.
Lemma lem7145717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7145718 {A : Type'} : (term419 A) = (term420 A).
Proof. exact (MK_COMB (@lem7145717) (@lem7145716 A)). Qed.
Lemma lem7145719 {A : Type'} (s : A -> Prop) : (term413 A s) = (term404 A s).
Proof. exact (eq_refl (term413 A s)). Qed.
Lemma lem7145720 {A : Type'} (x : type645 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7145721 {A : Type'} (x : type645 A) (s : A -> Prop) : (term421 A x s) = (term422 A x s).
Proof. exact (MK_COMB (@lem7145719 A s) (@lem7145720 A x s)). Qed.
Lemma lem7145722 {A : Type'} (x : type645 A) (s : A -> Prop) : (term422 A x s) = (term423 A x s).
Proof. exact (eq_refl (term422 A x s)). Qed.
Lemma lem7145723 {A : Type'} (x : type645 A) (s : A -> Prop) : (term421 A x s) = (term423 A x s).
Proof. exact (TRANS (@lem7145721 A x s) (@lem7145722 A x s)). Qed.
Lemma lem7145724 {A : Type'} (x : type645 A) : (term424 A x) = (term425 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7145723 A x s)). Qed.
Lemma lem7145725 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7145726 {A : Type'} (x : type645 A) : (term426 A x) = (term427 A x).
Proof. exact (MK_COMB (@lem7145725 A) (@lem7145724 A x)). Qed.
Lemma lem7145727 {A : Type'} : (term428 A) = (term429 A).
Proof. exact (fun_ext (fun x : type645 A => @lem7145726 A x)). Qed.
Lemma lem7145728 {A : Type'} : (@ex ((A -> Prop) -> (A -> real) -> real -> A)) = (@ex ((A -> Prop) -> (A -> real) -> real -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> real) -> real -> A))). Qed.
Lemma lem7145729 {A : Type'} : (term411 A) = (term430 A).
Proof. exact (MK_COMB (@lem7145728 A) (@lem7145727 A)). Qed.
Lemma lem7145730 {A : Type'} : ((term410 A) = (term411 A)) = ((term407 A) = (term430 A)).
Proof. exact (MK_COMB (@lem7145718 A) (@lem7145729 A)). Qed.
Lemma lem7145731 {A : Type'} : (term407 A) = (term430 A).
Proof. exact (EQ_MP (@lem7145730 A) (@lem7145705 A)). Qed.
Lemma lem7145733 {A : Type'} : (term306 A) = (term430 A).
Proof. exact (TRANS (@lem7145701 A) (@lem7145731 A)). Qed.
Lemma lem7145734 {A : Type'} : (term11 A) = (term430 A).
Proof. exact (TRANS (@lem7145453 A) (@lem7145733 A)). Qed.
Lemma lem7145735 {A : Type'} (h1 : term11 A) : term430 A.
Proof. exact (EQ_MP (@lem7145734 A) (@lem7143376 A h1)). Qed.
Lemma lem7145736 {A : Type'} (x : type645 A) (h1 : term427 A x) : term427 A x.
Proof. exact (h1). Qed.
Lemma lem7145738 {A : Type'} (s : A -> Prop) (h1 : term115 A s) : term115 A s.
Proof. exact (h1). Qed.
Lemma lem7145739 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term106 A s f) : term106 A s f.
Proof. exact (h1). Qed.
Lemma lem7145740 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term96 A s f b.
Proof. exact (h1). Qed.
Lemma lem7145957 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7145962 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7145963 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem7145962 (A -> Prop) nat f x). Qed.
Lemma lem7145965 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem7145963 A (@CARD A) s). Qed.
Lemma lem7145966 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7145967 {A : Type'} (s : A -> Prop) : (term431 A s) = (term432 A s).
Proof. exact (MK_COMB (@lem7145957) (@lem7145965 A s)). Qed.
Lemma lem7145968 {A : Type'} (s : A -> Prop) (n : nat) : ((@CARD A s) = n) = ((@I ((A -> Prop) -> nat) (@CARD A) s) = n).
Proof. exact (MK_COMB (@lem7145967 A s) (@lem7145966 n)). Qed.
Lemma lem7145973 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7145974 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7145973 (A -> Prop) Prop f x). Qed.
Lemma lem7145976 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7145974 A (@FINITE A) s). Qed.
Lemma lem7145977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7145978 {A : Type'} (s : A -> Prop) : (term49 A s) = (term433 A s).
Proof. exact (MK_COMB (@lem7145977) (@lem7145976 A s)). Qed.
Lemma lem7145979 {A : Type'} (s : A -> Prop) (n : nat) : (term69 A s n) = (term434 A s n).
Proof. exact (MK_COMB (@lem7145978 A s) (@lem7145968 A s n)). Qed.
Lemma lem7145980 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7145987 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7145988 {A : Type'} (f : type682 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat -> Prop) f x).
Proof. exact (@lem7145987 (A -> Prop) (nat -> Prop) f x). Qed.
Lemma lem7145989 {A : Type'} (s : A -> Prop) : (@HAS_SIZE A s) = (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s).
Proof. exact (@lem7145988 A (@HAS_SIZE A) s). Qed.
Lemma lem7145990 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7145991 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s n).
Proof. exact (MK_COMB (@lem7145989 A s) (@lem7145990 n)). Qed.
Lemma lem7145993 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7145994 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7145993 nat Prop f x). Qed.
Lemma lem7145995 {A : Type'} (s : A -> Prop) (n : nat) : (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s n) = (term435 A s n).
Proof. exact (@lem7145994 (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s) n). Qed.
Lemma lem7145997 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term435 A s n).
Proof. exact (TRANS (@lem7145991 A s n) (@lem7145995 A s n)). Qed.
Lemma lem7145998 {A : Type'} (s : A -> Prop) (n : nat) : (term436 A s n) = (term437 A s n).
Proof. exact (MK_COMB (@lem7145980) (@lem7145997 A s n)). Qed.
Lemma lem7145999 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7146000 {A : Type'} (s : A -> Prop) (n : nat) : (term438 A s n) = (term439 A s n).
Proof. exact (MK_COMB (@lem7145999) (@lem7145998 A s n)). Qed.
Lemma lem7146001 {A : Type'} (s : A -> Prop) (n : nat) : (term126 A s n) = (term440 A s n).
Proof. exact (MK_COMB (@lem7146000 A s n) (@lem7145979 A s n)). Qed.
Lemma lem7146002 {A : Type'} (s : A -> Prop) : (term145 A s) = (term441 A s).
Proof. exact (fun_ext (fun n : nat => @lem7146001 A s n)). Qed.
Lemma lem7146003 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7146004 {A : Type'} (s : A -> Prop) : (term160 A s) = (term442 A s).
Proof. exact (MK_COMB (@lem7146003) (@lem7146002 A s)). Qed.
Lemma lem7146005 {A : Type'} : (term169 A) = (term443 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7146004 A s)). Qed.
Lemma lem7146006 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7146007 {A : Type'} : (term184 A) = (term444 A).
Proof. exact (MK_COMB (@lem7146006 A) (@lem7146005 A)). Qed.
Lemma lem7146008 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7146009 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7146014 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146015 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem7146014 (A -> Prop) nat f x). Qed.
Lemma lem7146017 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem7146015 A (@CARD A) s). Qed.
Lemma lem7146018 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7146019 {A : Type'} (s : A -> Prop) : (term431 A s) = (term432 A s).
Proof. exact (MK_COMB (@lem7146009) (@lem7146017 A s)). Qed.
Lemma lem7146020 {A : Type'} (s : A -> Prop) (n : nat) : ((@CARD A s) = n) = ((@I ((A -> Prop) -> nat) (@CARD A) s) = n).
Proof. exact (MK_COMB (@lem7146019 A s) (@lem7146018 n)). Qed.
Lemma lem7146021 {A : Type'} (s : A -> Prop) (n : nat) : (term445 A s n) = (term446 A s n).
Proof. exact (MK_COMB (@lem7146008) (@lem7146020 A s n)). Qed.
Lemma lem7146022 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7146027 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146028 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7146027 (A -> Prop) Prop f x). Qed.
Lemma lem7146030 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7146028 A (@FINITE A) s). Qed.
Lemma lem7146031 {A : Type'} (s : A -> Prop) : (term324 A s) = (term447 A s).
Proof. exact (MK_COMB (@lem7146022) (@lem7146030 A s)). Qed.
Lemma lem7146032 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7146033 {A : Type'} (s : A -> Prop) : (term293 A s) = (term448 A s).
Proof. exact (MK_COMB (@lem7146032) (@lem7146031 A s)). Qed.
Lemma lem7146034 {A : Type'} (s : A -> Prop) (n : nat) : (term125 A s n) = (term449 A s n).
Proof. exact (MK_COMB (@lem7146033 A s) (@lem7146021 A s n)). Qed.
Lemma lem7146041 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146042 {A : Type'} (f : type682 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat -> Prop) f x).
Proof. exact (@lem7146041 (A -> Prop) (nat -> Prop) f x). Qed.
Lemma lem7146043 {A : Type'} (s : A -> Prop) : (@HAS_SIZE A s) = (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s).
Proof. exact (@lem7146042 A (@HAS_SIZE A) s). Qed.
Lemma lem7146044 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7146045 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s n).
Proof. exact (MK_COMB (@lem7146043 A s) (@lem7146044 n)). Qed.
Lemma lem7146047 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146048 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7146047 nat Prop f x). Qed.
Lemma lem7146049 {A : Type'} (s : A -> Prop) (n : nat) : (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s n) = (term435 A s n).
Proof. exact (@lem7146048 (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s) n). Qed.
Lemma lem7146051 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term435 A s n).
Proof. exact (TRANS (@lem7146045 A s n) (@lem7146049 A s n)). Qed.
Lemma lem7146052 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7146053 {A : Type'} (s : A -> Prop) (n : nat) : (term127 A s n) = (term450 A s n).
Proof. exact (MK_COMB (@lem7146052) (@lem7146051 A s n)). Qed.
Lemma lem7146054 {A : Type'} (s : A -> Prop) (n : nat) : (term129 A s n) = (term451 A s n).
Proof. exact (MK_COMB (@lem7146053 A s n) (@lem7146034 A s n)). Qed.
Lemma lem7146055 {A : Type'} (s : A -> Prop) : (term144 A s) = (term452 A s).
Proof. exact (fun_ext (fun n : nat => @lem7146054 A s n)). Qed.
Lemma lem7146056 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7146057 {A : Type'} (s : A -> Prop) : (term155 A s) = (term453 A s).
Proof. exact (MK_COMB (@lem7146056) (@lem7146055 A s)). Qed.
Lemma lem7146058 {A : Type'} : (term168 A) = (term454 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7146057 A s)). Qed.
Lemma lem7146059 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7146060 {A : Type'} : (term179 A) = (term455 A).
Proof. exact (MK_COMB (@lem7146059 A) (@lem7146058 A)). Qed.
Lemma lem7146061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7146062 {A : Type'} : (term181 A) = (term456 A).
Proof. exact (MK_COMB (@lem7146061) (@lem7146060 A)). Qed.
Lemma lem7146063 {A : Type'} : (term185 A) = (term457 A).
Proof. exact (MK_COMB (@lem7146062 A) (@lem7146007 A)). Qed.
Lemma lem7146064 {A : Type'} (h1 : term13 A) : term457 A.
Proof. exact (EQ_MP (@lem7146063 A) (@lem7144430 A h1)). Qed.
Lemma lem7146147 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (s = (@EMPTY A)).
Proof. exact (eq_refl (s = (@EMPTY A))). Qed.
Lemma lem7146148 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7146155 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146156 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7146155 nat nat f x). Qed.
Lemma lem7146158 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7146156 NUMERAL 0). Qed.
Lemma lem7146159 {A : Type'} (s : A -> Prop) : (@HAS_SIZE A s) = (@HAS_SIZE A s).
Proof. exact (eq_refl (@HAS_SIZE A s)). Qed.
Lemma lem7146160 {A : Type'} (s : A -> Prop) : (term67 A s) = (term458 A s).
Proof. exact (MK_COMB (@lem7146159 A s) (@lem7146158)). Qed.
Lemma lem7146162 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146163 {A : Type'} (f : type682 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat -> Prop) f x).
Proof. exact (@lem7146162 (A -> Prop) (nat -> Prop) f x). Qed.
Lemma lem7146164 {A : Type'} (s : A -> Prop) : (@HAS_SIZE A s) = (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s).
Proof. exact (@lem7146163 A (@HAS_SIZE A) s). Qed.
Lemma lem7146165 : (@I (nat -> nat) NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (eq_refl (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7146166 {A : Type'} (s : A -> Prop) : (term458 A s) = (term459 A s).
Proof. exact (MK_COMB (@lem7146164 A s) (@lem7146165)). Qed.
Lemma lem7146168 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146169 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7146168 nat Prop f x). Qed.
Lemma lem7146170 {A : Type'} (s : A -> Prop) : (term459 A s) = (term460 A s).
Proof. exact (@lem7146169 (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s) (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7146171 {A : Type'} (s : A -> Prop) : (term458 A s) = (term460 A s).
Proof. exact (TRANS (@lem7146166 A s) (@lem7146170 A s)). Qed.
Lemma lem7146172 {A : Type'} (s : A -> Prop) : (term67 A s) = (term460 A s).
Proof. exact (TRANS (@lem7146160 A s) (@lem7146171 A s)). Qed.
Lemma lem7146173 {A : Type'} (s : A -> Prop) : (term461 A s) = (term462 A s).
Proof. exact (MK_COMB (@lem7146148) (@lem7146172 A s)). Qed.
Lemma lem7146174 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7146175 {A : Type'} (s : A -> Prop) : (term463 A s) = (term464 A s).
Proof. exact (MK_COMB (@lem7146174) (@lem7146173 A s)). Qed.
Lemma lem7146176 {A : Type'} (s : A -> Prop) : (term198 A s) = (term465 A s).
Proof. exact (MK_COMB (@lem7146175 A s) (@lem7146147 A s)). Qed.
Lemma lem7146177 {A : Type'} : (term192 A) = (term466 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7146176 A s)). Qed.
Lemma lem7146178 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7146179 {A : Type'} : (term210 A) = (term467 A).
Proof. exact (MK_COMB (@lem7146178 A) (@lem7146177 A)). Qed.
Lemma lem7146186 {A : Type'} (s : A -> Prop) : (term292 A s) = (term292 A s).
Proof. exact (eq_refl (term292 A s)). Qed.
Lemma lem7146193 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146194 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7146193 nat nat f x). Qed.
Lemma lem7146196 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7146194 NUMERAL 0). Qed.
Lemma lem7146197 {A : Type'} (s : A -> Prop) : (@HAS_SIZE A s) = (@HAS_SIZE A s).
Proof. exact (eq_refl (@HAS_SIZE A s)). Qed.
Lemma lem7146198 {A : Type'} (s : A -> Prop) : (term67 A s) = (term458 A s).
Proof. exact (MK_COMB (@lem7146197 A s) (@lem7146196)). Qed.
Lemma lem7146200 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146201 {A : Type'} (f : type682 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat -> Prop) f x).
Proof. exact (@lem7146200 (A -> Prop) (nat -> Prop) f x). Qed.
Lemma lem7146202 {A : Type'} (s : A -> Prop) : (@HAS_SIZE A s) = (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s).
Proof. exact (@lem7146201 A (@HAS_SIZE A) s). Qed.
Lemma lem7146203 : (@I (nat -> nat) NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (eq_refl (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7146204 {A : Type'} (s : A -> Prop) : (term458 A s) = (term459 A s).
Proof. exact (MK_COMB (@lem7146202 A s) (@lem7146203)). Qed.
Lemma lem7146206 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146207 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7146206 nat Prop f x). Qed.
Lemma lem7146208 {A : Type'} (s : A -> Prop) : (term459 A s) = (term460 A s).
Proof. exact (@lem7146207 (@I ((A -> Prop) -> nat -> Prop) (@HAS_SIZE A) s) (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7146209 {A : Type'} (s : A -> Prop) : (term458 A s) = (term460 A s).
Proof. exact (TRANS (@lem7146204 A s) (@lem7146208 A s)). Qed.
Lemma lem7146210 {A : Type'} (s : A -> Prop) : (term67 A s) = (term460 A s).
Proof. exact (TRANS (@lem7146198 A s) (@lem7146209 A s)). Qed.
Lemma lem7146211 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7146212 {A : Type'} (s : A -> Prop) : (term468 A s) = (term469 A s).
Proof. exact (MK_COMB (@lem7146211) (@lem7146210 A s)). Qed.
Lemma lem7146213 {A : Type'} (s : A -> Prop) : (term194 A s) = (term470 A s).
Proof. exact (MK_COMB (@lem7146212 A s) (@lem7146186 A s)). Qed.
Lemma lem7146214 {A : Type'} : (term191 A) = (term471 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7146213 A s)). Qed.
Lemma lem7146215 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7146216 {A : Type'} : (term205 A) = (term472 A).
Proof. exact (MK_COMB (@lem7146215 A) (@lem7146214 A)). Qed.
Lemma lem7146217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7146218 {A : Type'} : (term207 A) = (term473 A).
Proof. exact (MK_COMB (@lem7146217) (@lem7146216 A)). Qed.
Lemma lem7146219 {A : Type'} : (term211 A) = (term474 A).
Proof. exact (MK_COMB (@lem7146218 A) (@lem7146179 A)). Qed.
Lemma lem7146220 {A : Type'} (h1 : term12 A) : term474 A.
Proof. exact (EQ_MP (@lem7146219 A) (@lem7144720 A h1)). Qed.
Lemma lem7146225 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem7146226 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7146227 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7146232 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146233 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7146232 nat real f x). Qed.
Lemma lem7146235 (m : nat) : (real_of_num m) = (@I (nat -> real) real_of_num m).
Proof. exact (@lem7146233 real_of_num m). Qed.
Lemma lem7146240 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146241 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7146240 nat real f x). Qed.
Lemma lem7146243 (n : nat) : (real_of_num n) = (@I (nat -> real) real_of_num n).
Proof. exact (@lem7146241 real_of_num n). Qed.
Lemma lem7146244 (m : nat) : (term475 m) = (term476 m).
Proof. exact (MK_COMB (@lem7146227) (@lem7146235 m)). Qed.
Lemma lem7146245 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = ((@I (nat -> real) real_of_num m) = (@I (nat -> real) real_of_num n)).
Proof. exact (MK_COMB (@lem7146244 m) (@lem7146243 n)). Qed.
Lemma lem7146246 (m : nat) (n : nat) : (term477 m n) = (term478 m n).
Proof. exact (MK_COMB (@lem7146226) (@lem7146245 m n)). Qed.
Lemma lem7146247 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7146248 (m : nat) (n : nat) : (term479 m n) = (term480 m n).
Proof. exact (MK_COMB (@lem7146247) (@lem7146246 m n)). Qed.
Lemma lem7146249 (m : nat) (n : nat) : (term226 m n) = (term481 m n).
Proof. exact (MK_COMB (@lem7146248 m n) (@lem7146225 m n)). Qed.
Lemma lem7146250 (m : nat) : (term220 m) = (term482 m).
Proof. exact (fun_ext (fun n : nat => @lem7146249 m n)). Qed.
Lemma lem7146251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7146252 (m : nat) : (term238 m) = (term483 m).
Proof. exact (MK_COMB (@lem7146251) (@lem7146250 m)). Qed.
Lemma lem7146253 : term245 = term484.
Proof. exact (fun_ext (fun m : nat => @lem7146252 m)). Qed.
Lemma lem7146254 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7146255 : term260 = term485.
Proof. exact (MK_COMB (@lem7146254) (@lem7146253)). Qed.
Lemma lem7146262 (m : nat) (n : nat) : (term486 m n) = (term486 m n).
Proof. exact (eq_refl (term486 m n)). Qed.
Lemma lem7146263 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7146268 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146269 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7146268 nat real f x). Qed.
Lemma lem7146271 (m : nat) : (real_of_num m) = (@I (nat -> real) real_of_num m).
Proof. exact (@lem7146269 real_of_num m). Qed.
Lemma lem7146276 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146277 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7146276 nat real f x). Qed.
Lemma lem7146279 (n : nat) : (real_of_num n) = (@I (nat -> real) real_of_num n).
Proof. exact (@lem7146277 real_of_num n). Qed.
Lemma lem7146280 (m : nat) : (term475 m) = (term476 m).
Proof. exact (MK_COMB (@lem7146263) (@lem7146271 m)). Qed.
Lemma lem7146281 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = ((@I (nat -> real) real_of_num m) = (@I (nat -> real) real_of_num n)).
Proof. exact (MK_COMB (@lem7146280 m) (@lem7146279 n)). Qed.
Lemma lem7146282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7146283 (m : nat) (n : nat) : (term487 m n) = (term488 m n).
Proof. exact (MK_COMB (@lem7146282) (@lem7146281 m n)). Qed.
Lemma lem7146284 (m : nat) (n : nat) : (term222 m n) = (term489 m n).
Proof. exact (MK_COMB (@lem7146283 m n) (@lem7146262 m n)). Qed.
Lemma lem7146285 (m : nat) : (term219 m) = (term490 m).
Proof. exact (fun_ext (fun n : nat => @lem7146284 m n)). Qed.
Lemma lem7146286 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7146287 (m : nat) : (term233 m) = (term491 m).
Proof. exact (MK_COMB (@lem7146286) (@lem7146285 m)). Qed.
Lemma lem7146288 : term244 = term492.
Proof. exact (fun_ext (fun m : nat => @lem7146287 m)). Qed.
Lemma lem7146289 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7146290 : term255 = term493.
Proof. exact (MK_COMB (@lem7146289) (@lem7146288)). Qed.
Lemma lem7146291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7146292 : term257 = term494.
Proof. exact (MK_COMB (@lem7146291) (@lem7146290)). Qed.
Lemma lem7146293 : term261 = term495.
Proof. exact (MK_COMB (@lem7146292) (@lem7146255)). Qed.
Lemma lem7146294 (h1 : term66) : term495.
Proof. exact (EQ_MP (@lem7146293) (@lem7145007 h1)). Qed.
Lemma lem7146295 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7146304 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146305 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7146304 real (real -> real) f x). Qed.
Lemma lem7146306 (x : real) : (real_div x) = (@I (real -> real -> real) real_div x).
Proof. exact (@lem7146305 real_div x). Qed.
Lemma lem7146307 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7146308 (x : real) (y : real) : (real_div x y) = (@I (real -> real -> real) real_div x y).
Proof. exact (MK_COMB (@lem7146306 x) (@lem7146307 y)). Qed.
Lemma lem7146310 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146311 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7146310 real real f x). Qed.
Lemma lem7146312 (x : real) (y : real) : (@I (real -> real -> real) real_div x y) = (term496 x y).
Proof. exact (@lem7146311 (@I (real -> real -> real) real_div x) y). Qed.
Lemma lem7146314 (x : real) (y : real) : (real_div x y) = (term496 x y).
Proof. exact (TRANS (@lem7146308 x y) (@lem7146312 x y)). Qed.
Lemma lem7146315 (y : real) : (real_mul y) = (real_mul y).
Proof. exact (eq_refl (real_mul y)). Qed.
Lemma lem7146316 (x : real) (y : real) : (term264 x y) = (term497 x y).
Proof. exact (MK_COMB (@lem7146315 y) (@lem7146314 x y)). Qed.
Lemma lem7146318 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146319 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7146318 real (real -> real) f x). Qed.
Lemma lem7146320 (y : real) : (real_mul y) = (@I (real -> real -> real) real_mul y).
Proof. exact (@lem7146319 real_mul y). Qed.
Lemma lem7146321 (x : real) (y : real) : (term496 x y) = (term496 x y).
Proof. exact (eq_refl (term496 x y)). Qed.
Lemma lem7146322 (x : real) (y : real) : (term497 x y) = (term498 x y).
Proof. exact (MK_COMB (@lem7146320 y) (@lem7146321 x y)). Qed.
Lemma lem7146324 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146325 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7146324 real real f x). Qed.
Lemma lem7146326 (x : real) (y : real) : (term498 x y) = (term499 x y).
Proof. exact (@lem7146325 (@I (real -> real -> real) real_mul y) (term496 x y)). Qed.
Lemma lem7146327 (x : real) (y : real) : (term497 x y) = (term499 x y).
Proof. exact (TRANS (@lem7146322 x y) (@lem7146326 x y)). Qed.
Lemma lem7146328 (x : real) (y : real) : (term264 x y) = (term499 x y).
Proof. exact (TRANS (@lem7146316 x y) (@lem7146327 x y)). Qed.
Lemma lem7146329 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7146330 (x : real) (y : real) : (term500 x y) = (term501 x y).
Proof. exact (MK_COMB (@lem7146295) (@lem7146328 x y)). Qed.
Lemma lem7146331 (y : real) (x : real) : ((term264 x y) = x) = ((term499 x y) = x).
Proof. exact (MK_COMB (@lem7146330 x y) (@lem7146329 x)). Qed.
Lemma lem7146334 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7146339 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146340 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7146339 nat nat f x). Qed.
Lemma lem7146342 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7146340 NUMERAL 0). Qed.
Lemma lem7146343 : term263 = term502.
Proof. exact (MK_COMB (@lem7146334) (@lem7146342)). Qed.
Lemma lem7146345 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146346 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7146345 nat real f x). Qed.
Lemma lem7146347 : term502 = term503.
Proof. exact (@lem7146346 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7146348 : term263 = term503.
Proof. exact (TRANS (@lem7146343) (@lem7146347)). Qed.
Lemma lem7146349 (y : real) : (@eq real y) = (@eq real y).
Proof. exact (eq_refl (@eq real y)). Qed.
Lemma lem7146350 (y : real) : (y = term263) = (y = term503).
Proof. exact (MK_COMB (@lem7146349 y) (@lem7146348)). Qed.
Lemma lem7146351 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7146352 (y : real) : (term266 y) = (term504 y).
Proof. exact (MK_COMB (@lem7146351) (@lem7146350 y)). Qed.
Lemma lem7146353 (y : real) (x : real) : (term268 y x) = (term505 y x).
Proof. exact (MK_COMB (@lem7146352 y) (@lem7146331 y x)). Qed.
Lemma lem7146354 (x : real) : (term270 x) = (term506 x).
Proof. exact (fun_ext (fun y : real => @lem7146353 y x)). Qed.
Lemma lem7146355 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7146356 (x : real) : (term271 x) = (term507 x).
Proof. exact (MK_COMB (@lem7146355) (@lem7146354 x)). Qed.
Lemma lem7146357 : term272 = term508.
Proof. exact (fun_ext (fun x : real => @lem7146356 x)). Qed.
Lemma lem7146358 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7146359 : term273 = term509.
Proof. exact (MK_COMB (@lem7146358) (@lem7146357)). Qed.
Lemma lem7146360 (h1 : term62) : term509.
Proof. exact (EQ_MP (@lem7146359) (@lem7145079 h1)). Qed.
Lemma lem7146361 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7146368 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146369 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7146368 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7146370 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7146369 A (@sum A) s). Qed.
Lemma lem7146371 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7146372 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f).
Proof. exact (MK_COMB (@lem7146370 A s) (@lem7146371 A f)). Qed.
Lemma lem7146374 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146375 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7146374 (A -> real) real f x). Qed.
Lemma lem7146376 {A : Type'} (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f) = (term510 A s f).
Proof. exact (@lem7146375 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) f). Qed.
Lemma lem7146378 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term510 A s f).
Proof. exact (TRANS (@lem7146372 A s f) (@lem7146376 A s f)). Qed.
Lemma lem7146379 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7146380 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7146385 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146386 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem7146385 (A -> Prop) nat f x). Qed.
Lemma lem7146388 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem7146386 A (@CARD A) s). Qed.
Lemma lem7146389 {A : Type'} (s : A -> Prop) : (term511 A s) = (term512 A s).
Proof. exact (MK_COMB (@lem7146380) (@lem7146388 A s)). Qed.
Lemma lem7146391 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146392 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7146391 nat real f x). Qed.
Lemma lem7146393 {A : Type'} (s : A -> Prop) : (term512 A s) = (term513 A s).
Proof. exact (@lem7146392 real_of_num (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem7146394 {A : Type'} (s : A -> Prop) : (term511 A s) = (term513 A s).
Proof. exact (TRANS (@lem7146389 A s) (@lem7146393 A s)). Qed.
Lemma lem7146395 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7146396 {A : Type'} (s : A -> Prop) : (term514 A s) = (term515 A s).
Proof. exact (MK_COMB (@lem7146379) (@lem7146394 A s)). Qed.
Lemma lem7146397 {A : Type'} (s : A -> Prop) (b : real) : (term516 A s b) = (term517 A s b).
Proof. exact (MK_COMB (@lem7146396 A s) (@lem7146395 b)). Qed.
Lemma lem7146399 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146400 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7146399 real (real -> real) f x). Qed.
Lemma lem7146401 {A : Type'} (s : A -> Prop) : (term515 A s) = (term518 A s).
Proof. exact (@lem7146400 real_mul (term513 A s)). Qed.
Lemma lem7146402 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7146403 {A : Type'} (s : A -> Prop) (b : real) : (term517 A s b) = (term519 A s b).
Proof. exact (MK_COMB (@lem7146401 A s) (@lem7146402 b)). Qed.
Lemma lem7146405 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146406 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7146405 real real f x). Qed.
Lemma lem7146407 {A : Type'} (s : A -> Prop) (b : real) : (term519 A s b) = (term520 A s b).
Proof. exact (@lem7146406 (term518 A s) b). Qed.
Lemma lem7146408 {A : Type'} (s : A -> Prop) (b : real) : (term517 A s b) = (term520 A s b).
Proof. exact (TRANS (@lem7146403 A s b) (@lem7146407 A s b)). Qed.
Lemma lem7146409 {A : Type'} (s : A -> Prop) (b : real) : (term516 A s b) = (term520 A s b).
Proof. exact (TRANS (@lem7146397 A s b) (@lem7146408 A s b)). Qed.
Lemma lem7146410 {A : Type'} (s : A -> Prop) (f : A -> real) : (term521 A s f) = (term522 A s f).
Proof. exact (MK_COMB (@lem7146361) (@lem7146378 A s f)). Qed.
Lemma lem7146411 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term43 A f s b) = (term523 A f s b).
Proof. exact (MK_COMB (@lem7146410 A s f) (@lem7146409 A s b)). Qed.
Lemma lem7146413 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146414 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7146413 real (real -> Prop) f x). Qed.
Lemma lem7146415 {A : Type'} (s : A -> Prop) (f : A -> real) : (term522 A s f) = (term524 A s f).
Proof. exact (@lem7146414 real_lt (term510 A s f)). Qed.
Lemma lem7146416 {A : Type'} (s : A -> Prop) (b : real) : (term520 A s b) = (term520 A s b).
Proof. exact (eq_refl (term520 A s b)). Qed.
Lemma lem7146417 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term523 A f s b) = (term525 A f s b).
Proof. exact (MK_COMB (@lem7146415 A s f) (@lem7146416 A s b)). Qed.
Lemma lem7146419 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146420 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7146419 real Prop f x). Qed.
Lemma lem7146421 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term525 A f s b) = (term526 A f s b).
Proof. exact (@lem7146420 (term524 A s f) (term520 A s b)). Qed.
Lemma lem7146422 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term523 A f s b) = (term526 A f s b).
Proof. exact (TRANS (@lem7146417 A f s b) (@lem7146421 A f s b)). Qed.
Lemma lem7146423 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term43 A f s b) = (term526 A f s b).
Proof. exact (TRANS (@lem7146411 A f s b) (@lem7146422 A f s b)). Qed.
Lemma lem7146424 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7146425 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7146426 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7146435 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146436 {A : Type'} (f : type645 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real -> A) f x).
Proof. exact (@lem7146435 (A -> Prop) (type715 A) f x). Qed.
Lemma lem7146437 {A : Type'} (x : type645 A) (s : A -> Prop) : (x s) = (@I ((A -> Prop) -> (A -> real) -> real -> A) x s).
Proof. exact (@lem7146436 A x s). Qed.
Lemma lem7146438 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7146439 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) : (x s f) = (@I ((A -> Prop) -> (A -> real) -> real -> A) x s f).
Proof. exact (MK_COMB (@lem7146437 A x s) (@lem7146438 A f)). Qed.
Lemma lem7146441 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146442 {A : Type'} (f : type715 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real -> A) f x).
Proof. exact (@lem7146441 (A -> real) (real -> A) f x). Qed.
Lemma lem7146443 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real -> A) x s f) = (term527 A x s f).
Proof. exact (@lem7146442 A (@I ((A -> Prop) -> (A -> real) -> real -> A) x s) f). Qed.
Lemma lem7146444 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) : (x s f) = (term527 A x s f).
Proof. exact (TRANS (@lem7146439 A x s f) (@lem7146443 A x s f)). Qed.
Lemma lem7146445 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7146446 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (x s f b) = (term528 A x s f b).
Proof. exact (MK_COMB (@lem7146444 A x s f) (@lem7146445 b)). Qed.
Lemma lem7146448 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146449 {A : Type'} (f : real -> A) (x : real) : (f x) = (@I (real -> A) f x).
Proof. exact (@lem7146448 real A f x). Qed.
Lemma lem7146450 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term528 A x s f b) = (term529 A x s f b).
Proof. exact (@lem7146449 A (term527 A x s f) b). Qed.
Lemma lem7146452 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (x s f b) = (term529 A x s f b).
Proof. exact (TRANS (@lem7146446 A x s f b) (@lem7146450 A x s f b)). Qed.
Lemma lem7146453 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term530 A x s f b) = (term531 A x s f b).
Proof. exact (MK_COMB (@lem7146426 A f) (@lem7146452 A x s f b)). Qed.
Lemma lem7146455 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146456 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7146455 A real f x). Qed.
Lemma lem7146457 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term531 A x s f b) = (term532 A x s f b).
Proof. exact (@lem7146456 A f (term529 A x s f b)). Qed.
Lemma lem7146458 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term530 A x s f b) = (term532 A x s f b).
Proof. exact (TRANS (@lem7146453 A x s f b) (@lem7146457 A x s f b)). Qed.
Lemma lem7146459 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7146460 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term533 A x s f b) = (term534 A x s f b).
Proof. exact (MK_COMB (@lem7146425) (@lem7146458 A x s f b)). Qed.
Lemma lem7146461 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term535 A x s f b) = (term536 A x s f b).
Proof. exact (MK_COMB (@lem7146460 A x s f b) (@lem7146459 b)). Qed.
Lemma lem7146463 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146464 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7146463 real (real -> Prop) f x). Qed.
Lemma lem7146465 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term534 A x s f b) = (term537 A x s f b).
Proof. exact (@lem7146464 real_lt (term532 A x s f b)). Qed.
Lemma lem7146466 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7146467 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term536 A x s f b) = (term538 A x s f b).
Proof. exact (MK_COMB (@lem7146465 A x s f b) (@lem7146466 b)). Qed.
Lemma lem7146469 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146470 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7146469 real Prop f x). Qed.
Lemma lem7146471 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term538 A x s f b) = (term539 A x s f b).
Proof. exact (@lem7146470 (term537 A x s f b) b). Qed.
Lemma lem7146472 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term536 A x s f b) = (term539 A x s f b).
Proof. exact (TRANS (@lem7146467 A x s f b) (@lem7146471 A x s f b)). Qed.
Lemma lem7146473 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term535 A x s f b) = (term539 A x s f b).
Proof. exact (TRANS (@lem7146461 A x s f b) (@lem7146472 A x s f b)). Qed.
Lemma lem7146474 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term540 A x s f b) = (term541 A x s f b).
Proof. exact (MK_COMB (@lem7146424) (@lem7146473 A x s f b)). Qed.
Lemma lem7146475 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem7146484 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146485 {A : Type'} (f : type645 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real -> A) f x).
Proof. exact (@lem7146484 (A -> Prop) (type715 A) f x). Qed.
Lemma lem7146486 {A : Type'} (x : type645 A) (s : A -> Prop) : (x s) = (@I ((A -> Prop) -> (A -> real) -> real -> A) x s).
Proof. exact (@lem7146485 A x s). Qed.
Lemma lem7146487 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7146488 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) : (x s f) = (@I ((A -> Prop) -> (A -> real) -> real -> A) x s f).
Proof. exact (MK_COMB (@lem7146486 A x s) (@lem7146487 A f)). Qed.
Lemma lem7146490 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146491 {A : Type'} (f : type715 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real -> A) f x).
Proof. exact (@lem7146490 (A -> real) (real -> A) f x). Qed.
Lemma lem7146492 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real -> A) x s f) = (term527 A x s f).
Proof. exact (@lem7146491 A (@I ((A -> Prop) -> (A -> real) -> real -> A) x s) f). Qed.
Lemma lem7146493 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) : (x s f) = (term527 A x s f).
Proof. exact (TRANS (@lem7146488 A x s f) (@lem7146492 A x s f)). Qed.
Lemma lem7146494 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7146495 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (x s f b) = (term528 A x s f b).
Proof. exact (MK_COMB (@lem7146493 A x s f) (@lem7146494 b)). Qed.
Lemma lem7146497 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146498 {A : Type'} (f : real -> A) (x : real) : (f x) = (@I (real -> A) f x).
Proof. exact (@lem7146497 real A f x). Qed.
Lemma lem7146499 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term528 A x s f b) = (term529 A x s f b).
Proof. exact (@lem7146498 A (term527 A x s f) b). Qed.
Lemma lem7146501 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (x s f b) = (term529 A x s f b).
Proof. exact (TRANS (@lem7146495 A x s f b) (@lem7146499 A x s f b)). Qed.
Lemma lem7146502 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7146503 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term542 A x s f b) = (term543 A x s f b).
Proof. exact (MK_COMB (@lem7146475 A) (@lem7146501 A x s f b)). Qed.
Lemma lem7146504 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term544 A x f b s) = (term545 A x f b s).
Proof. exact (MK_COMB (@lem7146503 A x s f b) (@lem7146502 A s)). Qed.
Lemma lem7146506 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146507 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7146506 A (type686 A) f x). Qed.
Lemma lem7146508 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term543 A x s f b) = (term546 A x s f b).
Proof. exact (@lem7146507 A (@IN A) (term529 A x s f b)). Qed.
Lemma lem7146509 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7146510 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term545 A x f b s) = (term547 A x f b s).
Proof. exact (MK_COMB (@lem7146508 A x s f b) (@lem7146509 A s)). Qed.
Lemma lem7146512 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146513 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7146512 (A -> Prop) Prop f x). Qed.
Lemma lem7146514 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term547 A x f b s) = (term548 A x f b s).
Proof. exact (@lem7146513 A (term546 A x s f b) s). Qed.
Lemma lem7146515 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term545 A x f b s) = (term548 A x f b s).
Proof. exact (TRANS (@lem7146510 A x f b s) (@lem7146514 A x f b s)). Qed.
Lemma lem7146516 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term544 A x f b s) = (term548 A x f b s).
Proof. exact (TRANS (@lem7146504 A x f b s) (@lem7146515 A x f b s)). Qed.
Lemma lem7146517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7146518 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term549 A x f b s) = (term550 A x f b s).
Proof. exact (MK_COMB (@lem7146517) (@lem7146516 A x f b s)). Qed.
Lemma lem7146519 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term551 A x s f b) = (term552 A x s f b).
Proof. exact (MK_COMB (@lem7146518 A x f b s) (@lem7146474 A x s f b)). Qed.
Lemma lem7146526 {A : Type'} (s : A -> Prop) : (term288 A s) = (term288 A s).
Proof. exact (eq_refl (term288 A s)). Qed.
Lemma lem7146527 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term553 A x s f b) = (term554 A x s f b).
Proof. exact (MK_COMB (@lem7146526 A s) (@lem7146519 A x s f b)). Qed.
Lemma lem7146528 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7146533 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146534 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7146533 (A -> Prop) Prop f x). Qed.
Lemma lem7146536 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7146534 A (@FINITE A) s). Qed.
Lemma lem7146537 {A : Type'} (s : A -> Prop) : (term324 A s) = (term447 A s).
Proof. exact (MK_COMB (@lem7146528) (@lem7146536 A s)). Qed.
Lemma lem7146538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7146539 {A : Type'} (s : A -> Prop) : (term293 A s) = (term448 A s).
Proof. exact (MK_COMB (@lem7146538) (@lem7146537 A s)). Qed.
Lemma lem7146540 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term555 A x s f b) = (term556 A x s f b).
Proof. exact (MK_COMB (@lem7146539 A s) (@lem7146527 A x s f b)). Qed.
Lemma lem7146541 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7146542 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term557 A x s f b) = (term558 A x s f b).
Proof. exact (MK_COMB (@lem7146541) (@lem7146540 A x s f b)). Qed.
Lemma lem7146543 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) (b : real) : (term559 A x f s b) = (term560 A x f s b).
Proof. exact (MK_COMB (@lem7146542 A x s f b) (@lem7146423 A f s b)). Qed.
Lemma lem7146544 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) : (term561 A x f s) = (term562 A x f s).
Proof. exact (fun_ext (fun b : real => @lem7146543 A x f s b)). Qed.
Lemma lem7146545 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7146546 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) : (term563 A x f s) = (term564 A x f s).
Proof. exact (MK_COMB (@lem7146545) (@lem7146544 A x f s)). Qed.
Lemma lem7146547 {A : Type'} (x : type645 A) (s : A -> Prop) : (term565 A x s) = (term566 A x s).
Proof. exact (fun_ext (fun f : A -> real => @lem7146546 A x f s)). Qed.
Lemma lem7146548 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7146549 {A : Type'} (x : type645 A) (s : A -> Prop) : (term423 A x s) = (term567 A x s).
Proof. exact (MK_COMB (@lem7146548 A) (@lem7146547 A x s)). Qed.
Lemma lem7146550 {A : Type'} (x : type645 A) : (term425 A x) = (term568 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7146549 A x s)). Qed.
Lemma lem7146551 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7146552 {A : Type'} (x : type645 A) : (term427 A x) = (term569 A x).
Proof. exact (MK_COMB (@lem7146551 A) (@lem7146550 A x)). Qed.
Lemma lem7146553 {A : Type'} (x : type645 A) (h1 : term427 A x) : term569 A x.
Proof. exact (EQ_MP (@lem7146552 A x) (@lem7145736 A x h1)). Qed.
Lemma lem7146747 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7146748 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7146755 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146756 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7146755 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7146757 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7146756 A (@sum A) s). Qed.
Lemma lem7146758 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7146759 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f).
Proof. exact (MK_COMB (@lem7146757 A s) (@lem7146758 A f)). Qed.
Lemma lem7146761 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146762 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7146761 (A -> real) real f x). Qed.
Lemma lem7146763 {A : Type'} (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f) = (term510 A s f).
Proof. exact (@lem7146762 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) f). Qed.
Lemma lem7146765 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term510 A s f).
Proof. exact (TRANS (@lem7146759 A s f) (@lem7146763 A s f)). Qed.
Lemma lem7146766 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7146767 {A : Type'} (s : A -> Prop) (f : A -> real) : (term521 A s f) = (term522 A s f).
Proof. exact (MK_COMB (@lem7146748) (@lem7146765 A s f)). Qed.
Lemma lem7146768 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term73 A s f b) = (term570 A s f b).
Proof. exact (MK_COMB (@lem7146767 A s f) (@lem7146766 b)). Qed.
Lemma lem7146770 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146771 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7146770 real (real -> Prop) f x). Qed.
Lemma lem7146772 {A : Type'} (s : A -> Prop) (f : A -> real) : (term522 A s f) = (term524 A s f).
Proof. exact (@lem7146771 real_lt (term510 A s f)). Qed.
Lemma lem7146773 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7146774 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term570 A s f b) = (term571 A s f b).
Proof. exact (MK_COMB (@lem7146772 A s f) (@lem7146773 b)). Qed.
Lemma lem7146776 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146777 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7146776 real Prop f x). Qed.
Lemma lem7146778 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term571 A s f b) = (term572 A s f b).
Proof. exact (@lem7146777 (term524 A s f) b). Qed.
Lemma lem7146779 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term570 A s f b) = (term572 A s f b).
Proof. exact (TRANS (@lem7146774 A s f b) (@lem7146778 A s f b)). Qed.
Lemma lem7146780 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term73 A s f b) = (term572 A s f b).
Proof. exact (TRANS (@lem7146768 A s f b) (@lem7146779 A s f b)). Qed.
Lemma lem7146781 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term92 A s f b) = (term573 A s f b).
Proof. exact (MK_COMB (@lem7146747) (@lem7146780 A s f b)). Qed.
Lemma lem7146782 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7146787 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146789 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7146787 A real f x). Qed.
Lemma lem7146792 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7146797 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146798 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem7146797 (A -> Prop) nat f x). Qed.
Lemma lem7146800 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem7146798 A (@CARD A) s). Qed.
Lemma lem7146801 {A : Type'} (s : A -> Prop) : (term511 A s) = (term512 A s).
Proof. exact (MK_COMB (@lem7146792) (@lem7146800 A s)). Qed.
Lemma lem7146803 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146804 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7146803 nat real f x). Qed.
Lemma lem7146805 {A : Type'} (s : A -> Prop) : (term512 A s) = (term513 A s).
Proof. exact (@lem7146804 real_of_num (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem7146806 {A : Type'} (s : A -> Prop) : (term511 A s) = (term513 A s).
Proof. exact (TRANS (@lem7146801 A s) (@lem7146805 A s)). Qed.
Lemma lem7146807 (b : real) : (real_div b) = (real_div b).
Proof. exact (eq_refl (real_div b)). Qed.
Lemma lem7146808 {A : Type'} (b : real) (s : A -> Prop) : (term574 A b s) = (term575 A b s).
Proof. exact (MK_COMB (@lem7146807 b) (@lem7146806 A s)). Qed.
Lemma lem7146810 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146811 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7146810 real (real -> real) f x). Qed.
Lemma lem7146812 (b : real) : (real_div b) = (@I (real -> real -> real) real_div b).
Proof. exact (@lem7146811 real_div b). Qed.
Lemma lem7146813 {A : Type'} (s : A -> Prop) : (term513 A s) = (term513 A s).
Proof. exact (eq_refl (term513 A s)). Qed.
Lemma lem7146814 {A : Type'} (b : real) (s : A -> Prop) : (term575 A b s) = (term576 A b s).
Proof. exact (MK_COMB (@lem7146812 b) (@lem7146813 A s)). Qed.
Lemma lem7146816 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146817 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7146816 real real f x). Qed.
Lemma lem7146818 {A : Type'} (b : real) (s : A -> Prop) : (term576 A b s) = (term577 A b s).
Proof. exact (@lem7146817 (@I (real -> real -> real) real_div b) (term513 A s)). Qed.
Lemma lem7146819 {A : Type'} (b : real) (s : A -> Prop) : (term575 A b s) = (term577 A b s).
Proof. exact (TRANS (@lem7146814 A b s) (@lem7146818 A b s)). Qed.
Lemma lem7146820 {A : Type'} (b : real) (s : A -> Prop) : (term574 A b s) = (term577 A b s).
Proof. exact (TRANS (@lem7146808 A b s) (@lem7146819 A b s)). Qed.
Lemma lem7146821 {A : Type'} (f : A -> real) (x : A) : (term578 A f x) = (term579 A f x).
Proof. exact (MK_COMB (@lem7146782) (@lem7146789 A f x)). Qed.
Lemma lem7146822 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term87 A f x b s) = (term580 A f x b s).
Proof. exact (MK_COMB (@lem7146821 A f x) (@lem7146820 A b s)). Qed.
Lemma lem7146824 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146825 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7146824 real (real -> Prop) f x). Qed.
Lemma lem7146826 {A : Type'} (f : A -> real) (x : A) : (term579 A f x) = (term581 A f x).
Proof. exact (@lem7146825 real_lt (@I (A -> real) f x)). Qed.
Lemma lem7146827 {A : Type'} (b : real) (s : A -> Prop) : (term577 A b s) = (term577 A b s).
Proof. exact (eq_refl (term577 A b s)). Qed.
Lemma lem7146828 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term580 A f x b s) = (term582 A f x b s).
Proof. exact (MK_COMB (@lem7146826 A f x) (@lem7146827 A b s)). Qed.
Lemma lem7146830 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146831 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7146830 real Prop f x). Qed.
Lemma lem7146832 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term582 A f x b s) = (term583 A f x b s).
Proof. exact (@lem7146831 (term581 A f x) (term577 A b s)). Qed.
Lemma lem7146833 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term580 A f x b s) = (term583 A f x b s).
Proof. exact (TRANS (@lem7146828 A f x b s) (@lem7146832 A f x b s)). Qed.
Lemma lem7146834 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term87 A f x b s) = (term583 A f x b s).
Proof. exact (TRANS (@lem7146822 A f x b s) (@lem7146833 A f x b s)). Qed.
Lemma lem7146835 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7146842 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146843 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7146842 A (type686 A) f x). Qed.
Lemma lem7146844 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7146843 A (@IN A) x). Qed.
Lemma lem7146845 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7146846 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem7146844 A x) (@lem7146845 A s)). Qed.
Lemma lem7146848 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146849 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7146848 (A -> Prop) Prop f x). Qed.
Lemma lem7146850 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term584 A x s).
Proof. exact (@lem7146849 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem7146852 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term584 A x s).
Proof. exact (TRANS (@lem7146846 A x s) (@lem7146850 A x s)). Qed.
Lemma lem7146853 {A : Type'} (x : A) (s : A -> Prop) : (term585 A x s) = (term586 A x s).
Proof. exact (MK_COMB (@lem7146835) (@lem7146852 A x s)). Qed.
Lemma lem7146854 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7146855 {A : Type'} (x : A) (s : A -> Prop) : (term587 A x s) = (term588 A x s).
Proof. exact (MK_COMB (@lem7146854) (@lem7146853 A x s)). Qed.
Lemma lem7146856 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term86 A f x b s) = (term589 A f x b s).
Proof. exact (MK_COMB (@lem7146855 A x s) (@lem7146834 A f x b s)). Qed.
Lemma lem7146857 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term88 A f b s) = (term590 A f b s).
Proof. exact (fun_ext (fun x : A => @lem7146856 A f x b s)). Qed.
Lemma lem7146858 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7146859 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term89 A f b s) = (term591 A f b s).
Proof. exact (MK_COMB (@lem7146858 A) (@lem7146857 A f b s)). Qed.
Lemma lem7146868 {A : Type'} (s : A -> Prop) : (term47 A s) = (term47 A s).
Proof. exact (eq_refl (term47 A s)). Qed.
Lemma lem7146869 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term90 A f b s) = (term592 A f b s).
Proof. exact (MK_COMB (@lem7146868 A s) (@lem7146859 A f b s)). Qed.
Lemma lem7146874 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7146875 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7146874 (A -> Prop) Prop f x). Qed.
Lemma lem7146877 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7146875 A (@FINITE A) s). Qed.
Lemma lem7146878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7146879 {A : Type'} (s : A -> Prop) : (term49 A s) = (term433 A s).
Proof. exact (MK_COMB (@lem7146878) (@lem7146877 A s)). Qed.
Lemma lem7146880 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term91 A f b s) = (term593 A f b s).
Proof. exact (MK_COMB (@lem7146879 A s) (@lem7146869 A f b s)). Qed.
Lemma lem7146881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7146882 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term94 A f b s) = (term594 A f b s).
Proof. exact (MK_COMB (@lem7146881) (@lem7146880 A f b s)). Qed.
Lemma lem7146883 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term96 A s f b) = (term595 A s f b).
Proof. exact (MK_COMB (@lem7146882 A f b s) (@lem7146781 A s f b)). Qed.
Lemma lem7146884 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term595 A s f b.
Proof. exact (EQ_MP (@lem7146883 A s f b) (@lem7145740 A s f b h1)). Qed.
Lemma lem7146886 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term593 A f b s.
Proof. exact (proj1 (@lem7146884 A s f b h1)). Qed.
Lemma lem7146887 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term592 A f b s.
Proof. exact (proj2 (@lem7146886 A s f b h1)). Qed.
Lemma lem7146889 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term591 A f b s.
Proof. exact (proj2 (@lem7146887 A s f b h1)). Qed.
Lemma lem7146891 (h1 : term66) : term485.
Proof. exact (proj2 (@lem7146294 h1)). Qed.
Lemma lem7146893 {A : Type'} (h1 : term12 A) : term467 A.
Proof. exact (proj2 (@lem7146220 A h1)). Qed.
Lemma lem7146898 {A : Type'} (h1 : term13 A) : term455 A.
Proof. exact (proj1 (@lem7146064 A h1)). Qed.
Lemma lem7146910 (y : real) (x : real) : (term505 y x) = (term505 y x).
Proof. exact (eq_refl (term505 y x)). Qed.
Lemma lem7146911 (x : real) : (term506 x) = (term506 x).
Proof. exact (fun_ext (fun y : real => @lem7146910 y x)). Qed.
Lemma lem7146912 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7146913 (x : real) : (term507 x) = (term507 x).
Proof. exact (MK_COMB (@lem7146912) (@lem7146911 x)). Qed.
Lemma lem7146914 : term508 = term508.
Proof. exact (fun_ext (fun x : real => @lem7146913 x)). Qed.
Lemma lem7146915 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7146917 : term509 = term509.
Proof. exact (MK_COMB (@lem7146915) (@lem7146914)). Qed.
Lemma lem7146918 (h1 : term62) : term509.
Proof. exact (EQ_MP (@lem7146917) (@lem7146360 h1)). Qed.
Lemma lem7146920 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term526 A f s b) = (term526 A f s b).
Proof. exact (eq_refl (term526 A f s b)). Qed.
Lemma lem7146937 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term554 A x s f b) = (term596 A x s f b).
Proof. exact (@lem19490 (term548 A x f b s) (s = (@EMPTY A)) (term541 A x s f b)). Qed.
Lemma lem7146940 {A : Type'} (s : A -> Prop) : (term448 A s) = (term448 A s).
Proof. exact (eq_refl (term448 A s)). Qed.
Lemma lem7146941 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term556 A x s f b) = (term597 A x s f b).
Proof. exact (MK_COMB (@lem7146940 A s) (@lem7146937 A x s f b)). Qed.
Lemma lem7146948 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term597 A x s f b) = (term598 A x s f b).
Proof. exact (@lem19490 (term599 A x f b s) (term447 A s) (term600 A x s f b)). Qed.
Lemma lem7146949 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term556 A x s f b) = (term598 A x s f b).
Proof. exact (TRANS (@lem7146941 A x s f b) (@lem7146948 A x s f b)). Qed.
Lemma lem7146950 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7146951 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) : (term558 A x s f b) = (term601 A x s f b).
Proof. exact (MK_COMB (@lem7146950) (@lem7146949 A x s f b)). Qed.
Lemma lem7146952 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) (b : real) : (term560 A x f s b) = (term602 A x f s b).
Proof. exact (MK_COMB (@lem7146951 A x s f b) (@lem7146920 A f s b)). Qed.
Lemma lem7146959 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) (b : real) : (term602 A x f s b) = (term603 A x f s b).
Proof. exact (@lem19699 (term604 A x f b s) (term605 A x s f b) (term526 A f s b)). Qed.
Lemma lem7146960 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) (b : real) : (term560 A x f s b) = (term603 A x f s b).
Proof. exact (TRANS (@lem7146952 A x f s b) (@lem7146959 A x f s b)). Qed.
Lemma lem7146961 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) : (term562 A x f s) = (term606 A x f s).
Proof. exact (fun_ext (fun b : real => @lem7146960 A x f s b)). Qed.
Lemma lem7146962 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7146963 {A : Type'} (x : type645 A) (f : A -> real) (s : A -> Prop) : (term564 A x f s) = (term607 A x f s).
Proof. exact (MK_COMB (@lem7146962) (@lem7146961 A x f s)). Qed.
Lemma lem7146964 {A : Type'} (x : type645 A) (s : A -> Prop) : (term566 A x s) = (term608 A x s).
Proof. exact (fun_ext (fun f : A -> real => @lem7146963 A x f s)). Qed.
Lemma lem7146965 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7146966 {A : Type'} (x : type645 A) (s : A -> Prop) : (term567 A x s) = (term609 A x s).
Proof. exact (MK_COMB (@lem7146965 A) (@lem7146964 A x s)). Qed.
Lemma lem7146967 {A : Type'} (x : type645 A) : (term568 A x) = (term610 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7146966 A x s)). Qed.
Lemma lem7146968 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7146970 {A : Type'} (x : type645 A) : (term569 A x) = (term611 A x).
Proof. exact (MK_COMB (@lem7146968 A) (@lem7146967 A x)). Qed.
Lemma lem7146971 {A : Type'} (x : type645 A) (h1 : term427 A x) : term611 A x.
Proof. exact (EQ_MP (@lem7146970 A x) (@lem7146553 A x h1)). Qed.
Lemma lem7147044 {A : Type'} (f : A -> real) (x : A) (b : real) (s : A -> Prop) : (term589 A f x b s) = (term589 A f x b s).
Proof. exact (eq_refl (term589 A f x b s)). Qed.
Lemma lem7147045 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term590 A f b s) = (term590 A f b s).
Proof. exact (fun_ext (fun x : A => @lem7147044 A f x b s)). Qed.
Lemma lem7147046 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7147048 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term591 A f b s) = (term591 A f b s).
Proof. exact (MK_COMB (@lem7147046 A) (@lem7147045 A f b s)). Qed.
Lemma lem7147049 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term591 A f b s.
Proof. exact (EQ_MP (@lem7147048 A f b s) (@lem7146889 A s f b h1)). Qed.
Lemma lem7147073 (m : nat) (n : nat) : (term481 m n) = (term481 m n).
Proof. exact (eq_refl (term481 m n)). Qed.
Lemma lem7147074 (m : nat) : (term482 m) = (term482 m).
Proof. exact (fun_ext (fun n : nat => @lem7147073 m n)). Qed.
Lemma lem7147075 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7147076 (m : nat) : (term483 m) = (term483 m).
Proof. exact (MK_COMB (@lem7147075) (@lem7147074 m)). Qed.
Lemma lem7147077 : term484 = term484.
Proof. exact (fun_ext (fun m : nat => @lem7147076 m)). Qed.
Lemma lem7147078 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7147080 : term485 = term485.
Proof. exact (MK_COMB (@lem7147078) (@lem7147077)). Qed.
Lemma lem7147081 (h1 : term66) : term485.
Proof. exact (EQ_MP (@lem7147080) (@lem7146891 h1)). Qed.
Lemma lem7147102 {A : Type'} (s : A -> Prop) : (term465 A s) = (term465 A s).
Proof. exact (eq_refl (term465 A s)). Qed.
Lemma lem7147103 {A : Type'} : (term466 A) = (term466 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7147102 A s)). Qed.
Lemma lem7147104 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7147106 {A : Type'} : (term467 A) = (term467 A).
Proof. exact (MK_COMB (@lem7147104 A) (@lem7147103 A)). Qed.
Lemma lem7147107 {A : Type'} (h1 : term12 A) : term467 A.
Proof. exact (EQ_MP (@lem7147106 A) (@lem7146893 A h1)). Qed.
Lemma lem7147147 {A : Type'} (s : A -> Prop) (n : nat) : (term451 A s n) = (term451 A s n).
Proof. exact (eq_refl (term451 A s n)). Qed.
Lemma lem7147148 {A : Type'} (s : A -> Prop) : (term452 A s) = (term452 A s).
Proof. exact (fun_ext (fun n : nat => @lem7147147 A s n)). Qed.
Lemma lem7147149 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7147150 {A : Type'} (s : A -> Prop) : (term453 A s) = (term453 A s).
Proof. exact (MK_COMB (@lem7147149) (@lem7147148 A s)). Qed.
Lemma lem7147151 {A : Type'} : (term454 A) = (term454 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7147150 A s)). Qed.
Lemma lem7147152 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7147154 {A : Type'} : (term455 A) = (term455 A).
Proof. exact (MK_COMB (@lem7147152 A) (@lem7147151 A)). Qed.
Lemma lem7147155 {A : Type'} (h1 : term13 A) : term455 A.
Proof. exact (EQ_MP (@lem7147154 A) (@lem7146898 A h1)). Qed.
Lemma lem7147278 (_95446 : real) (h1 : term62) : term612 _95446.
Proof. exact (@lem7146918 h1 _95446). Qed.
Lemma lem7147279 (_95446 : real) : (term612 _95446) = (term507 _95446).
Proof. exact (eq_refl (term612 _95446)). Qed.
Lemma lem7147280 (_95446 : real) (h1 : term62) : term507 _95446.
Proof. exact (EQ_MP (@lem7147279 _95446) (@lem7147278 _95446 h1)). Qed.
Lemma lem7147281 (_95446 : real) (_95447 : real) (h1 : term62) : term613 _95446 _95447.
Proof. exact (@lem7147280 _95446 h1 _95447). Qed.
Lemma lem7147282 (_95447 : real) (_95446 : real) : (term613 _95446 _95447) = (term505 _95447 _95446).
Proof. exact (eq_refl (term613 _95446 _95447)). Qed.
Lemma lem7147284 {A : Type'} (_95448 : A -> Prop) (x : type645 A) (h1 : term427 A x) : term614 A x _95448.
Proof. exact (@lem7146971 A x h1 _95448). Qed.
Lemma lem7147285 {A : Type'} (x : type645 A) (_95448 : A -> Prop) : (term614 A x _95448) = (term609 A x _95448).
Proof. exact (eq_refl (term614 A x _95448)). Qed.
Lemma lem7147286 {A : Type'} (_95448 : A -> Prop) (x : type645 A) (h1 : term427 A x) : term609 A x _95448.
Proof. exact (EQ_MP (@lem7147285 A x _95448) (@lem7147284 A _95448 x h1)). Qed.
Lemma lem7147287 {A : Type'} (_95448 : A -> Prop) (_95449 : A -> real) (x : type645 A) (h1 : term427 A x) : term615 A x _95448 _95449.
Proof. exact (@lem7147286 A _95448 x h1 _95449). Qed.
Lemma lem7147288 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) : (term615 A x _95448 _95449) = (term607 A x _95449 _95448).
Proof. exact (eq_refl (term615 A x _95448 _95449)). Qed.
Lemma lem7147289 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (x : type645 A) (h1 : term427 A x) : term607 A x _95449 _95448.
Proof. exact (EQ_MP (@lem7147288 A x _95449 _95448) (@lem7147287 A _95448 _95449 x h1)). Qed.
Lemma lem7147290 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) (x : type645 A) (h1 : term427 A x) : term616 A x _95449 _95448 _95450.
Proof. exact (@lem7147289 A _95449 _95448 x h1 _95450). Qed.
Lemma lem7147291 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term616 A x _95449 _95448 _95450) = (term603 A x _95449 _95448 _95450).
Proof. exact (eq_refl (term616 A x _95449 _95448 _95450)). Qed.
Lemma lem7147292 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) (x : type645 A) (h1 : term427 A x) : term603 A x _95449 _95448 _95450.
Proof. exact (EQ_MP (@lem7147291 A x _95449 _95448 _95450) (@lem7147290 A _95449 _95448 _95450 x h1)). Qed.
Lemma lem7147302 {A : Type'} (_95454 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term617 A f b s _95454.
Proof. exact (@lem7147049 A s f b h1 _95454). Qed.
Lemma lem7147303 {A : Type'} (f : A -> real) (_95454 : A) (b : real) (s : A -> Prop) : (term617 A f b s _95454) = (term589 A f _95454 b s).
Proof. exact (eq_refl (term617 A f b s _95454)). Qed.
Lemma lem7147311 (_95457 : nat) (h1 : term66) : term618 _95457.
Proof. exact (@lem7147081 h1 _95457). Qed.
Lemma lem7147312 (_95457 : nat) : (term618 _95457) = (term483 _95457).
Proof. exact (eq_refl (term618 _95457)). Qed.
Lemma lem7147313 (_95457 : nat) (h1 : term66) : term483 _95457.
Proof. exact (EQ_MP (@lem7147312 _95457) (@lem7147311 _95457 h1)). Qed.
Lemma lem7147314 (_95457 : nat) (_95458 : nat) (h1 : term66) : term619 _95457 _95458.
Proof. exact (@lem7147313 _95457 h1 _95458). Qed.
Lemma lem7147315 (_95457 : nat) (_95458 : nat) : (term619 _95457 _95458) = (term481 _95457 _95458).
Proof. exact (eq_refl (term619 _95457 _95458)). Qed.
Lemma lem7147320 {A : Type'} (_95460 : A -> Prop) (h1 : term12 A) : term620 A _95460.
Proof. exact (@lem7147107 A h1 _95460). Qed.
Lemma lem7147321 {A : Type'} (_95460 : A -> Prop) : (term620 A _95460) = (term465 A _95460).
Proof. exact (eq_refl (term620 A _95460)). Qed.
Lemma lem7147329 {A : Type'} (_95463 : A -> Prop) (h1 : term13 A) : term621 A _95463.
Proof. exact (@lem7147155 A h1 _95463). Qed.
Lemma lem7147330 {A : Type'} (_95463 : A -> Prop) : (term621 A _95463) = (term453 A _95463).
Proof. exact (eq_refl (term621 A _95463)). Qed.
Lemma lem7147331 {A : Type'} (_95463 : A -> Prop) (h1 : term13 A) : term453 A _95463.
Proof. exact (EQ_MP (@lem7147330 A _95463) (@lem7147329 A _95463 h1)). Qed.
Lemma lem7147332 {A : Type'} (_95463 : A -> Prop) (_95464 : nat) (h1 : term13 A) : term622 A _95463 _95464.
Proof. exact (@lem7147331 A _95463 h1 _95464). Qed.
Lemma lem7147333 {A : Type'} (_95463 : A -> Prop) (_95464 : nat) : (term622 A _95463 _95464) = (term451 A _95463 _95464).
Proof. exact (eq_refl (term622 A _95463 _95464)). Qed.
Lemma lem7147373 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) (x : type645 A) (h1 : term427 A x) : term623 A x _95449 _95448 _95450.
Proof. exact (proj2 (@lem7147292 A _95449 _95448 _95450 x h1)). Qed.
Lemma lem7147374 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) (x : type645 A) (h1 : term427 A x) : term624 A x _95449 _95448 _95450.
Proof. exact (proj1 (@lem7147292 A _95449 _95448 _95450 x h1)). Qed.
Lemma lem7147380 (_95447 : real) (_95446 : real) (h1 : term62) : term505 _95447 _95446.
Proof. exact (EQ_MP (@lem7147282 _95447 _95446) (@lem7147281 _95446 _95447 h1)). Qed.
Lemma lem7147386 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term292 A s.
Proof. exact (proj1 (@lem7146887 A s f b h1)). Qed.
Lemma lem7147392 {A : Type'} (_95454 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term589 A f _95454 b s.
Proof. exact (EQ_MP (@lem7147303 A f _95454 b s) (@lem7147302 A _95454 s f b h1)). Qed.
Lemma lem7147404 (_95457 : nat) (_95458 : nat) (h1 : term66) : term481 _95457 _95458.
Proof. exact (EQ_MP (@lem7147315 _95457 _95458) (@lem7147314 _95457 _95458 h1)). Qed.
Lemma lem7147416 {A : Type'} (_95460 : A -> Prop) (h1 : term12 A) : term465 A _95460.
Proof. exact (EQ_MP (@lem7147321 A _95460) (@lem7147320 A _95460 h1)). Qed.
Lemma lem7147438 {A : Type'} (_95463 : A -> Prop) (_95464 : nat) (h1 : term13 A) : term451 A _95463 _95464.
Proof. exact (EQ_MP (@lem7147333 A _95463 _95464) (@lem7147332 A _95463 _95464 h1)). Qed.
Lemma lem7147534 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term624 A x _95449 _95448 _95450) = (term625 A x _95449 _95448 _95450).
Proof. exact (@lem7142733 (term447 A _95448) (term599 A x _95449 _95450 _95448) (term526 A _95449 _95448 _95450)). Qed.
Lemma lem7147541 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term626 A x _95449 _95448 _95450) = (term627 A x _95449 _95448 _95450).
Proof. exact (@lem7142733 (_95448 = (@EMPTY A)) (term548 A x _95449 _95450 _95448) (term526 A _95449 _95448 _95450)). Qed.
Lemma lem7147542 {A : Type'} (_95448 : A -> Prop) : (term448 A _95448) = (term448 A _95448).
Proof. exact (eq_refl (term448 A _95448)). Qed.
Lemma lem7147545 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term625 A x _95449 _95448 _95450) = (term628 A x _95449 _95448 _95450).
Proof. exact (MK_COMB (@lem7147542 A _95448) (@lem7147541 A x _95449 _95448 _95450)). Qed.
Lemma lem7147547 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term624 A x _95449 _95448 _95450) = (term628 A x _95449 _95448 _95450).
Proof. exact (TRANS (@lem7147534 A x _95449 _95448 _95450) (@lem7147545 A x _95449 _95448 _95450)). Qed.
Lemma lem7147548 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) (x : type645 A) (h1 : term427 A x) : term628 A x _95449 _95448 _95450.
Proof. exact (EQ_MP (@lem7147547 A x _95449 _95448 _95450) (@lem7147374 A _95449 _95448 _95450 x h1)). Qed.
Lemma lem7147552 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term623 A x _95449 _95448 _95450) = (term629 A x _95449 _95448 _95450).
Proof. exact (@lem7142733 (term447 A _95448) (term600 A x _95448 _95449 _95450) (term526 A _95449 _95448 _95450)). Qed.
Lemma lem7147559 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term630 A x _95449 _95448 _95450) = (term631 A x _95449 _95448 _95450).
Proof. exact (@lem7142733 (_95448 = (@EMPTY A)) (term541 A x _95448 _95449 _95450) (term526 A _95449 _95448 _95450)). Qed.
Lemma lem7147560 {A : Type'} (_95448 : A -> Prop) : (term448 A _95448) = (term448 A _95448).
Proof. exact (eq_refl (term448 A _95448)). Qed.
Lemma lem7147563 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term629 A x _95449 _95448 _95450) = (term632 A x _95449 _95448 _95450).
Proof. exact (MK_COMB (@lem7147560 A _95448) (@lem7147559 A x _95449 _95448 _95450)). Qed.
Lemma lem7147565 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term623 A x _95449 _95448 _95450) = (term632 A x _95449 _95448 _95450).
Proof. exact (TRANS (@lem7147552 A x _95449 _95448 _95450) (@lem7147563 A x _95449 _95448 _95450)). Qed.
Lemma lem7147566 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) (x : type645 A) (h1 : term427 A x) : term632 A x _95449 _95448 _95450.
Proof. exact (EQ_MP (@lem7147565 A x _95449 _95448 _95450) (@lem7147373 A _95449 _95448 _95450 x h1)). Qed.
Lemma lem7147643 : (@I (real -> Prop)) = (@I (real -> Prop)).
Proof. exact (eq_refl (@I (real -> Prop))). Qed.
Lemma lem7147644 (_95491 : real -> Prop) (_95493 : real -> Prop) (h1 : _95491 = _95493) : _95491 = _95493.
Proof. exact (h1). Qed.
Lemma lem7147645 (_95492 : real) (_95494 : real) (h1 : _95492 = _95494) : _95492 = _95494.
Proof. exact (h1). Qed.
Lemma lem7147646 (_95491 : real -> Prop) (_95493 : real -> Prop) (h1 : _95491 = _95493) : (@I (real -> Prop) _95491) = (@I (real -> Prop) _95493).
Proof. exact (MK_COMB (@lem7147643) (@lem7147644 _95491 _95493 h1)). Qed.
Lemma lem7147647 (_95491 : real -> Prop) (_95493 : real -> Prop) (_95492 : real) (_95494 : real) (h1 : _95491 = _95493) (h2 : _95492 = _95494) : (@I (real -> Prop) _95491 _95492) = (@I (real -> Prop) _95493 _95494).
Proof. exact (MK_COMB (@lem7147646 _95491 _95493 h1) (@lem7147645 _95492 _95494 h2)). Qed.
Lemma lem7147649 (b : Prop) (a : Prop) : term633 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem7147650 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : term634 _95493 _95494 _95491 _95492.
Proof. exact (@lem7147649 (@I (real -> Prop) _95493 _95494) (@I (real -> Prop) _95491 _95492)). Qed.
Lemma lem7147651 (_95491 : real -> Prop) (_95493 : real -> Prop) (_95492 : real) (_95494 : real) (h1 : _95491 = _95493) (h2 : _95492 = _95494) : term635 _95493 _95494 _95491 _95492.
Proof. exact (@lem7147650 _95493 _95494 _95491 _95492 (@lem7147647 _95491 _95493 _95492 _95494 h1 h2)). Qed.
Lemma lem7147652 (_95494 : real) (_95492 : real) (_95491 : real -> Prop) (_95493 : real -> Prop) (h1 : _95491 = _95493) : term636 _95493 _95494 _95491 _95492.
Proof. exact (fun h0 : _95492 = _95494 => @lem7147651 _95491 _95493 _95492 _95494 h1 h0). Qed.
Lemma lem7147654 (a : Prop) (b : Prop) : (a -> b) = (term637 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7147655 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term636 _95493 _95494 _95491 _95492) = (term638 _95493 _95494 _95491 _95492).
Proof. exact (@lem7147654 (_95492 = _95494) (term635 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7147656 (_95494 : real) (_95492 : real) (_95491 : real -> Prop) (_95493 : real -> Prop) (h1 : _95491 = _95493) : term638 _95493 _95494 _95491 _95492.
Proof. exact (EQ_MP (@lem7147655 _95493 _95494 _95491 _95492) (@lem7147652 _95494 _95492 _95491 _95493 h1)). Qed.
Lemma lem7147657 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : term639 _95493 _95494 _95491 _95492.
Proof. exact (fun h0 : _95491 = _95493 => @lem7147656 _95494 _95492 _95491 _95493 h0). Qed.
Lemma lem7147659 (a : Prop) (b : Prop) : (a -> b) = (term637 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7147660 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term639 _95493 _95494 _95491 _95492) = (term640 _95493 _95494 _95491 _95492).
Proof. exact (@lem7147659 (_95491 = _95493) (term638 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7147661 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : term640 _95493 _95494 _95491 _95492.
Proof. exact (EQ_MP (@lem7147660 _95493 _95494 _95491 _95492) (@lem7147657 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148112 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem7146886 A s f b h1)). Qed.
Lemma lem7148113 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term641 A s.
Proof. exact (fun h0 : term447 A s => @lem7148112 A s f b h1). Qed.
Lemma lem7148115 (p : Prop) : (term642 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7148116 {A : Type'} (s : A -> Prop) : (term641 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7148115 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem7148117 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7148116 A s) (@lem7148113 A s f b h1)). Qed.
Lemma lem7148119 (x : real -> Prop) : x = x.
Proof. exact (@lem21386 (real -> Prop) x). Qed.
Lemma lem7148120 {A : Type'} (s : A -> Prop) (f : A -> real) : (term524 A s f) = (term524 A s f).
Proof. exact (@lem7148119 (term524 A s f)). Qed.
Lemma lem7148121 {A : Type'} (s : A -> Prop) (f : A -> real) : term643 A s f.
Proof. exact (fun h0 : term644 A s f => @lem7148120 A s f). Qed.
Lemma lem7148123 (p : Prop) : (term642 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7148124 {A : Type'} (s : A -> Prop) (f : A -> real) : (term643 A s f) = ((term524 A s f) = (term524 A s f)).
Proof. exact (@lem7148123 ((term524 A s f) = (term524 A s f))). Qed.
Lemma lem7148125 {A : Type'} (s : A -> Prop) (f : A -> real) : (term524 A s f) = (term524 A s f).
Proof. exact (EQ_MP (@lem7148124 A s f) (@lem7148121 A s f)). Qed.
Lemma lem7148127 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term573 A s f b.
Proof. exact (proj2 (@lem7146884 A s f b h1)). Qed.
Lemma lem7148128 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term645 A s f b.
Proof. exact (fun h0 : term572 A s f b => @lem7148127 A s f b h1). Qed.
Lemma lem7148130 (p : Prop) : (term646 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7148131 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term645 A s f b) = (term573 A s f b).
Proof. exact (@lem7148130 (term572 A s f b)). Qed.
Lemma lem7148132 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term573 A s f b.
Proof. exact (EQ_MP (@lem7148131 A s f b) (@lem7148128 A s f b h1)). Qed.
Lemma lem7148134 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem7146886 A s f b h1)). Qed.
Lemma lem7148135 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term641 A s.
Proof. exact (fun h0 : term447 A s => @lem7148134 A s f b h1). Qed.
Lemma lem7148137 (p : Prop) : (term642 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7148138 {A : Type'} (s : A -> Prop) : (term641 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7148137 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem7148139 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7148138 A s) (@lem7148135 A s f b h1)). Qed.
Lemma lem7148142 {A : Type'} (s : A -> Prop) (h1 : term292 A s) : term292 A s.
Proof. exact (h1). Qed.
Lemma lem7148143 {A : Type'} (s : A -> Prop) (h1 : term292 A s) : term647 A s.
Proof. exact (fun h0 : s = (@EMPTY A) => @lem7148142 A s h1). Qed.
Lemma lem7148145 (p : Prop) : (term646 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7148146 {A : Type'} (s : A -> Prop) : (term647 A s) = (term292 A s).
Proof. exact (@lem7148145 (s = (@EMPTY A))). Qed.
Lemma lem7148147 {A : Type'} (s : A -> Prop) (h1 : term292 A s) : term292 A s.
Proof. exact (EQ_MP (@lem7148146 A s) (@lem7148143 A s h1)). Qed.
Lemma lem7148149 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem7146886 A s f b h1)). Qed.
Lemma lem7148150 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term641 A s.
Proof. exact (fun h0 : term447 A s => @lem7148149 A s f b h1). Qed.
Lemma lem7148152 (p : Prop) : (term642 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7148153 {A : Type'} (s : A -> Prop) : (term641 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7148152 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem7148154 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7148153 A s) (@lem7148150 A s f b h1)). Qed.
Lemma lem7148157 {A : Type'} (s : A -> Prop) (h1 : term292 A s) : term292 A s.
Proof. exact (h1). Qed.
Lemma lem7148158 {A : Type'} (s : A -> Prop) (h1 : term292 A s) : term647 A s.
Proof. exact (fun h0 : s = (@EMPTY A) => @lem7148157 A s h1). Qed.
Lemma lem7148160 (p : Prop) : (term646 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7148161 {A : Type'} (s : A -> Prop) : (term647 A s) = (term292 A s).
Proof. exact (@lem7148160 (s = (@EMPTY A))). Qed.
Lemma lem7148162 {A : Type'} (s : A -> Prop) (h1 : term292 A s) : term292 A s.
Proof. exact (EQ_MP (@lem7148161 A s) (@lem7148158 A s h1)). Qed.
Lemma lem7148165 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term648 A f b s) : term648 A f b s.
Proof. exact (h1). Qed.
Lemma lem7148166 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term648 A f b s) : term649 A f b s.
Proof. exact (fun h0 : term650 A f b s => @lem7148165 A f b s h1). Qed.
Lemma lem7148168 (p : Prop) : (term646 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7148169 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term649 A f b s) = (term648 A f b s).
Proof. exact (@lem7148168 (term650 A f b s)). Qed.
Lemma lem7148170 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term648 A f b s) : term648 A f b s.
Proof. exact (EQ_MP (@lem7148169 A f b s) (@lem7148166 A f b s h1)). Qed.
Lemma lem7148176 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7148177 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term628 A x _95449 _95448 _95450) = (term651 A x _95449 _95448 _95450).
Proof. exact (@lem7148176 (_95448 = (@EMPTY A)) (term447 A _95448) (term652 A x _95449 _95448 _95450)). Qed.
Lemma lem7148193 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7148194 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term653 A x _95449 _95448 _95450) = (term654 A x _95449 _95448 _95450).
Proof. exact (@lem7148193 (term548 A x _95449 _95450 _95448) (term447 A _95448) (term526 A _95449 _95448 _95450)). Qed.
Lemma lem7148208 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7148209 {A : Type'} (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term655 A _95449 _95448 _95450) = (term656 A _95449 _95450 _95448).
Proof. exact (@lem7148208 (term526 A _95449 _95448 _95450) (term447 A _95448)). Qed.
Lemma lem7148215 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term657 A x _95449 _95450 _95448) = (term657 A x _95449 _95450 _95448).
Proof. exact (eq_refl (term657 A x _95449 _95450 _95448)). Qed.
Lemma lem7148216 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term654 A x _95449 _95448 _95450) = (term658 A x _95449 _95450 _95448).
Proof. exact (MK_COMB (@lem7148215 A x _95449 _95450 _95448) (@lem7148209 A _95449 _95450 _95448)). Qed.
Lemma lem7148227 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term653 A x _95449 _95448 _95450) = (term658 A x _95449 _95450 _95448).
Proof. exact (TRANS (@lem7148194 A x _95449 _95448 _95450) (@lem7148216 A x _95449 _95450 _95448)). Qed.
Lemma lem7148228 {A : Type'} (_95448 : A -> Prop) : (term288 A _95448) = (term288 A _95448).
Proof. exact (eq_refl (term288 A _95448)). Qed.
Lemma lem7148229 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term651 A x _95449 _95448 _95450) = (term659 A x _95449 _95450 _95448).
Proof. exact (MK_COMB (@lem7148228 A _95448) (@lem7148227 A x _95449 _95450 _95448)). Qed.
Lemma lem7148240 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term628 A x _95449 _95448 _95450) = (term659 A x _95449 _95450 _95448).
Proof. exact (TRANS (@lem7148177 A x _95449 _95448 _95450) (@lem7148229 A x _95449 _95450 _95448)). Qed.
Lemma lem7148241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7148242 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term660 A x _95449 _95448 _95450) = (term661 A x _95449 _95450 _95448).
Proof. exact (MK_COMB (@lem7148241) (@lem7148240 A x _95449 _95450 _95448)). Qed.
Lemma lem7148256 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7148257 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term662 A _95449 _95448 _95450) = (term663 A _95449 _95448 _95450).
Proof. exact (@lem7148256 (_95448 = (@EMPTY A)) (term447 A _95448) (term526 A _95449 _95448 _95450)). Qed.
Lemma lem7148273 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7148274 {A : Type'} (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term655 A _95449 _95448 _95450) = (term656 A _95449 _95450 _95448).
Proof. exact (@lem7148273 (term526 A _95449 _95448 _95450) (term447 A _95448)). Qed.
Lemma lem7148280 {A : Type'} (_95448 : A -> Prop) : (term288 A _95448) = (term288 A _95448).
Proof. exact (eq_refl (term288 A _95448)). Qed.
Lemma lem7148281 {A : Type'} (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term663 A _95449 _95448 _95450) = (term664 A _95449 _95450 _95448).
Proof. exact (MK_COMB (@lem7148280 A _95448) (@lem7148274 A _95449 _95450 _95448)). Qed.
Lemma lem7148292 {A : Type'} (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term662 A _95449 _95448 _95450) = (term664 A _95449 _95450 _95448).
Proof. exact (TRANS (@lem7148257 A _95449 _95448 _95450) (@lem7148281 A _95449 _95450 _95448)). Qed.
Lemma lem7148293 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term657 A x _95449 _95450 _95448) = (term657 A x _95449 _95450 _95448).
Proof. exact (eq_refl (term657 A x _95449 _95450 _95448)). Qed.
Lemma lem7148294 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term665 A x _95449 _95448 _95450) = (term666 A x _95449 _95450 _95448).
Proof. exact (MK_COMB (@lem7148293 A x _95449 _95450 _95448) (@lem7148292 A _95449 _95450 _95448)). Qed.
Lemma lem7148298 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7148299 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term666 A x _95449 _95450 _95448) = (term659 A x _95449 _95450 _95448).
Proof. exact (@lem7148298 (_95448 = (@EMPTY A)) (term548 A x _95449 _95450 _95448) (term656 A _95449 _95450 _95448)). Qed.
Lemma lem7148327 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term665 A x _95449 _95448 _95450) = (term659 A x _95449 _95450 _95448).
Proof. exact (TRANS (@lem7148294 A x _95449 _95450 _95448) (@lem7148299 A x _95449 _95450 _95448)). Qed.
Lemma lem7148328 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : ((term628 A x _95449 _95448 _95450) = (term665 A x _95449 _95448 _95450)) = ((term659 A x _95449 _95450 _95448) = (term659 A x _95449 _95450 _95448)).
Proof. exact (MK_COMB (@lem7148242 A x _95449 _95450 _95448) (@lem7148327 A x _95449 _95450 _95448)). Qed.
Lemma lem7148330 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7148331 (x : Prop) : (x = x) = True.
Proof. exact (@lem7148330 Prop x). Qed.
Lemma lem7148332 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : ((term659 A x _95449 _95450 _95448) = (term659 A x _95449 _95450 _95448)) = True.
Proof. exact (@lem7148331 (term659 A x _95449 _95450 _95448)). Qed.
Lemma lem7148333 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : ((term628 A x _95449 _95448 _95450) = (term665 A x _95449 _95448 _95450)) = True.
Proof. exact (TRANS (@lem7148328 A x _95449 _95450 _95448) (@lem7148332 A x _95449 _95450 _95448)). Qed.
Lemma lem7148334 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : True = ((term628 A x _95449 _95448 _95450) = (term665 A x _95449 _95448 _95450)).
Proof. exact (SYM (@lem7148333 A x _95449 _95448 _95450)). Qed.
Lemma lem7148335 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term628 A x _95449 _95448 _95450) = (term665 A x _95449 _95448 _95450).
Proof. exact (EQ_MP (@lem7148334 A x _95449 _95448 _95450) (@lem0)). Qed.
Lemma lem7148336 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) (x : type645 A) (h1 : term427 A x) : term665 A x _95449 _95448 _95450.
Proof. exact (EQ_MP (@lem7148335 A x _95449 _95448 _95450) (@lem7147548 A _95449 _95448 _95450 x h1)). Qed.
Lemma lem7148338 (b : Prop) (a : Prop) : (a \/ b) = (term667 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7148339 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term665 A x _95449 _95448 _95450) = (term668 A x _95449 _95450 _95448).
Proof. exact (@lem7148338 (term662 A _95449 _95448 _95450) (term548 A x _95449 _95450 _95448)). Qed.
Lemma lem7148341 (a : Prop) (b : Prop) : (term669 a b) = (term670 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7148342 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term671 A _95449 _95448 _95450) = (term672 A _95449 _95448 _95450).
Proof. exact (@lem7148341 (term447 A _95448) (term673 A _95449 _95448 _95450)). Qed.
Lemma lem7148344 (a : Prop) : (term674 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7148345 {A : Type'} (_95448 : A -> Prop) : (term675 A _95448) = (@I ((A -> Prop) -> Prop) (@FINITE A) _95448).
Proof. exact (@lem7148344 (@I ((A -> Prop) -> Prop) (@FINITE A) _95448)). Qed.
Lemma lem7148346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7148347 {A : Type'} (_95448 : A -> Prop) : (term676 A _95448) = (term433 A _95448).
Proof. exact (MK_COMB (@lem7148346) (@lem7148345 A _95448)). Qed.
Lemma lem7148349 (a : Prop) (b : Prop) : (term669 a b) = (term670 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7148350 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term677 A _95449 _95448 _95450) = (term678 A _95449 _95448 _95450).
Proof. exact (@lem7148349 (_95448 = (@EMPTY A)) (term526 A _95449 _95448 _95450)). Qed.
Lemma lem7148351 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term672 A _95449 _95448 _95450) = (term679 A _95449 _95448 _95450).
Proof. exact (MK_COMB (@lem7148347 A _95448) (@lem7148350 A _95449 _95448 _95450)). Qed.
Lemma lem7148352 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term671 A _95449 _95448 _95450) = (term679 A _95449 _95448 _95450).
Proof. exact (TRANS (@lem7148342 A _95449 _95448 _95450) (@lem7148351 A _95449 _95448 _95450)). Qed.
Lemma lem7148353 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7148354 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term680 A _95449 _95448 _95450) = (term681 A _95449 _95448 _95450).
Proof. exact (MK_COMB (@lem7148353) (@lem7148352 A _95449 _95448 _95450)). Qed.
Lemma lem7148355 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term548 A x _95449 _95450 _95448) = (term548 A x _95449 _95450 _95448).
Proof. exact (eq_refl (term548 A x _95449 _95450 _95448)). Qed.
Lemma lem7148356 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term668 A x _95449 _95450 _95448) = (term682 A x _95449 _95450 _95448).
Proof. exact (MK_COMB (@lem7148354 A _95449 _95448 _95450) (@lem7148355 A x _95449 _95450 _95448)). Qed.
Lemma lem7148357 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) : (term665 A x _95449 _95448 _95450) = (term682 A x _95449 _95450 _95448).
Proof. exact (TRANS (@lem7148339 A x _95449 _95450 _95448) (@lem7148356 A x _95449 _95450 _95448)). Qed.
Lemma lem7148359 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term292 A s) (h2 : term648 A f b s) : term683 A f b s.
Proof. exact (conj (@lem7148162 A s h1) (@lem7148170 A f b s h2)). Qed.
Lemma lem7148360 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term292 A s) (h2 : term648 A f b s) (h3 : term96 A s f b) : term684 A f b s.
Proof. exact (conj (@lem7148154 A s f b h3) (@lem7148359 A f b s h1 h2)). Qed.
Lemma lem7148362 {A : Type'} (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) (x : type645 A) (h1 : term427 A x) : term682 A x _95449 _95450 _95448.
Proof. exact (EQ_MP (@lem7148357 A x _95449 _95450 _95448) (@lem7148336 A _95449 _95448 _95450 x h1)). Qed.
Lemma lem7148363 {A : Type'} (_95449 : A -> real) (_95450 : real) (_95448 : A -> Prop) (x : type645 A) (h1 : term427 A x) : term682 A x _95449 _95450 _95448.
Proof. exact (@lem7148362 A _95449 _95450 _95448 x h1). Qed.
Lemma lem7148364 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (x : type645 A) (h1 : term427 A x) : term685 A x f b s.
Proof. exact (@lem7148363 A f (term577 A b s) s x h1). Qed.
Lemma lem7148367 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term648 A f b s) (h4 : term96 A s f b) : term686 A x f b s.
Proof. exact (@lem7148364 A f b s x h1 (@lem7148360 A s f b h2 h3 h4)). Qed.
Lemma lem7148368 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term648 A f b s) (h4 : term96 A s f b) : term687 A x f b s.
Proof. exact (fun h0 : term688 A x f b s => @lem7148367 A x s f b h1 h2 h3 h4). Qed.
Lemma lem7148370 (p : Prop) : (term642 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7148371 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term687 A x f b s) = (term686 A x f b s).
Proof. exact (@lem7148370 (term686 A x f b s)). Qed.
Lemma lem7148372 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term648 A f b s) (h4 : term96 A s f b) : term686 A x f b s.
Proof. exact (EQ_MP (@lem7148371 A x f b s) (@lem7148368 A x s f b h1 h2 h3 h4)). Qed.
Lemma lem7148378 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7148379 {A : Type'} (f : A -> real) (b : real) (_95454 : A) (s : A -> Prop) : (term589 A f _95454 b s) = (term689 A f b _95454 s).
Proof. exact (@lem7148378 (term583 A f _95454 b s) (term586 A _95454 s)). Qed.
Lemma lem7148385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7148386 {A : Type'} (f : A -> real) (b : real) (_95454 : A) (s : A -> Prop) : (term690 A f _95454 b s) = (term691 A f b _95454 s).
Proof. exact (MK_COMB (@lem7148385) (@lem7148379 A f b _95454 s)). Qed.
Lemma lem7148392 {A : Type'} (f : A -> real) (b : real) (_95454 : A) (s : A -> Prop) : (term689 A f b _95454 s) = (term689 A f b _95454 s).
Proof. exact (eq_refl (term689 A f b _95454 s)). Qed.
Lemma lem7148393 {A : Type'} (f : A -> real) (b : real) (_95454 : A) (s : A -> Prop) : ((term589 A f _95454 b s) = (term689 A f b _95454 s)) = ((term689 A f b _95454 s) = (term689 A f b _95454 s)).
Proof. exact (MK_COMB (@lem7148386 A f b _95454 s) (@lem7148392 A f b _95454 s)). Qed.
Lemma lem7148395 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7148396 (x : Prop) : (x = x) = True.
Proof. exact (@lem7148395 Prop x). Qed.
Lemma lem7148397 {A : Type'} (f : A -> real) (b : real) (_95454 : A) (s : A -> Prop) : ((term689 A f b _95454 s) = (term689 A f b _95454 s)) = True.
Proof. exact (@lem7148396 (term689 A f b _95454 s)). Qed.
Lemma lem7148398 {A : Type'} (f : A -> real) (b : real) (_95454 : A) (s : A -> Prop) : ((term589 A f _95454 b s) = (term689 A f b _95454 s)) = True.
Proof. exact (TRANS (@lem7148393 A f b _95454 s) (@lem7148397 A f b _95454 s)). Qed.
Lemma lem7148399 {A : Type'} (f : A -> real) (b : real) (_95454 : A) (s : A -> Prop) : True = ((term589 A f _95454 b s) = (term689 A f b _95454 s)).
Proof. exact (SYM (@lem7148398 A f b _95454 s)). Qed.
Lemma lem7148400 {A : Type'} (f : A -> real) (b : real) (_95454 : A) (s : A -> Prop) : (term589 A f _95454 b s) = (term689 A f b _95454 s).
Proof. exact (EQ_MP (@lem7148399 A f b _95454 s) (@lem0)). Qed.
Lemma lem7148401 {A : Type'} (_95454 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term689 A f b _95454 s.
Proof. exact (EQ_MP (@lem7148400 A f b _95454 s) (@lem7147392 A _95454 s f b h1)). Qed.
Lemma lem7148403 (b : Prop) (a : Prop) : (a \/ b) = (term667 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7148404 {A : Type'} (f : A -> real) (_95454 : A) (b : real) (s : A -> Prop) : (term689 A f b _95454 s) = (term692 A f _95454 b s).
Proof. exact (@lem7148403 (term586 A _95454 s) (term583 A f _95454 b s)). Qed.
Lemma lem7148406 (a : Prop) : (term674 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7148407 {A : Type'} (_95454 : A) (s : A -> Prop) : (term693 A _95454 s) = (term584 A _95454 s).
Proof. exact (@lem7148406 (term584 A _95454 s)). Qed.
Lemma lem7148408 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7148409 {A : Type'} (_95454 : A) (s : A -> Prop) : (term694 A _95454 s) = (term695 A _95454 s).
Proof. exact (MK_COMB (@lem7148408) (@lem7148407 A _95454 s)). Qed.
Lemma lem7148410 {A : Type'} (f : A -> real) (_95454 : A) (b : real) (s : A -> Prop) : (term583 A f _95454 b s) = (term583 A f _95454 b s).
Proof. exact (eq_refl (term583 A f _95454 b s)). Qed.
Lemma lem7148411 {A : Type'} (f : A -> real) (_95454 : A) (b : real) (s : A -> Prop) : (term692 A f _95454 b s) = (term696 A f _95454 b s).
Proof. exact (MK_COMB (@lem7148409 A _95454 s) (@lem7148410 A f _95454 b s)). Qed.
Lemma lem7148412 {A : Type'} (f : A -> real) (_95454 : A) (b : real) (s : A -> Prop) : (term689 A f b _95454 s) = (term696 A f _95454 b s).
Proof. exact (TRANS (@lem7148404 A f _95454 b s) (@lem7148411 A f _95454 b s)). Qed.
Lemma lem7148415 {A : Type'} (_95454 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term696 A f _95454 b s.
Proof. exact (EQ_MP (@lem7148412 A f _95454 b s) (@lem7148401 A _95454 s f b h1)). Qed.
Lemma lem7148416 {A : Type'} (_95454 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term696 A f _95454 b s.
Proof. exact (@lem7148415 A _95454 s f b h1). Qed.
Lemma lem7148417 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term697 A x f b s.
Proof. exact (@lem7148416 A (term698 A x f b s) s f b h1). Qed.
Lemma lem7148420 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term648 A f b s) (h4 : term96 A s f b) : term699 A x f b s.
Proof. exact (@lem7148417 A x s f b h4 (@lem7148372 A x s f b h1 h2 h3 h4)). Qed.
Lemma lem7148421 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term648 A f b s) (h4 : term96 A s f b) : term700 A x f b s.
Proof. exact (fun h0 : term701 A x f b s => @lem7148420 A x s f b h1 h2 h3 h4). Qed.
Lemma lem7148423 (p : Prop) : (term642 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7148424 {A : Type'} (x : type645 A) (f : A -> real) (b : real) (s : A -> Prop) : (term700 A x f b s) = (term699 A x f b s).
Proof. exact (@lem7148423 (term699 A x f b s)). Qed.
Lemma lem7148425 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term648 A f b s) (h4 : term96 A s f b) : term699 A x f b s.
Proof. exact (EQ_MP (@lem7148424 A x f b s) (@lem7148421 A x s f b h1 h2 h3 h4)). Qed.
Lemma lem7148431 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7148432 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term632 A x _95449 _95448 _95450) = (term702 A x _95449 _95448 _95450).
Proof. exact (@lem7148431 (_95448 = (@EMPTY A)) (term447 A _95448) (term703 A x _95449 _95448 _95450)). Qed.
Lemma lem7148458 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7148459 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term703 A x _95449 _95448 _95450) = (term704 A x _95448 _95449 _95450).
Proof. exact (@lem7148458 (term526 A _95449 _95448 _95450) (term541 A x _95448 _95449 _95450)). Qed.
Lemma lem7148465 {A : Type'} (_95448 : A -> Prop) : (term448 A _95448) = (term448 A _95448).
Proof. exact (eq_refl (term448 A _95448)). Qed.
Lemma lem7148466 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term705 A x _95449 _95448 _95450) = (term706 A x _95448 _95449 _95450).
Proof. exact (MK_COMB (@lem7148465 A _95448) (@lem7148459 A x _95448 _95449 _95450)). Qed.
Lemma lem7148470 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7148471 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term706 A x _95448 _95449 _95450) = (term707 A x _95448 _95449 _95450).
Proof. exact (@lem7148470 (term526 A _95449 _95448 _95450) (term447 A _95448) (term541 A x _95448 _95449 _95450)). Qed.
Lemma lem7148487 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term705 A x _95449 _95448 _95450) = (term707 A x _95448 _95449 _95450).
Proof. exact (TRANS (@lem7148466 A x _95448 _95449 _95450) (@lem7148471 A x _95448 _95449 _95450)). Qed.
Lemma lem7148488 {A : Type'} (_95448 : A -> Prop) : (term288 A _95448) = (term288 A _95448).
Proof. exact (eq_refl (term288 A _95448)). Qed.
Lemma lem7148489 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term702 A x _95449 _95448 _95450) = (term708 A x _95448 _95449 _95450).
Proof. exact (MK_COMB (@lem7148488 A _95448) (@lem7148487 A x _95448 _95449 _95450)). Qed.
Lemma lem7148500 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term632 A x _95449 _95448 _95450) = (term708 A x _95448 _95449 _95450).
Proof. exact (TRANS (@lem7148432 A x _95449 _95448 _95450) (@lem7148489 A x _95448 _95449 _95450)). Qed.
Lemma lem7148501 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7148502 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term709 A x _95449 _95448 _95450) = (term710 A x _95448 _95449 _95450).
Proof. exact (MK_COMB (@lem7148501) (@lem7148500 A x _95448 _95449 _95450)). Qed.
Lemma lem7148516 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7148517 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term605 A x _95448 _95449 _95450) = (term711 A x _95448 _95449 _95450).
Proof. exact (@lem7148516 (_95448 = (@EMPTY A)) (term447 A _95448) (term541 A x _95448 _95449 _95450)). Qed.
Lemma lem7148535 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term712 A _95449 _95448 _95450) = (term712 A _95449 _95448 _95450).
Proof. exact (eq_refl (term712 A _95449 _95448 _95450)). Qed.
Lemma lem7148536 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term713 A x _95448 _95449 _95450) = (term714 A x _95448 _95449 _95450).
Proof. exact (MK_COMB (@lem7148535 A _95449 _95448 _95450) (@lem7148517 A x _95448 _95449 _95450)). Qed.
Lemma lem7148540 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7148541 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term714 A x _95448 _95449 _95450) = (term708 A x _95448 _95449 _95450).
Proof. exact (@lem7148540 (_95448 = (@EMPTY A)) (term526 A _95449 _95448 _95450) (term715 A x _95448 _95449 _95450)). Qed.
Lemma lem7148569 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term713 A x _95448 _95449 _95450) = (term708 A x _95448 _95449 _95450).
Proof. exact (TRANS (@lem7148536 A x _95448 _95449 _95450) (@lem7148541 A x _95448 _95449 _95450)). Qed.
Lemma lem7148570 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : ((term632 A x _95449 _95448 _95450) = (term713 A x _95448 _95449 _95450)) = ((term708 A x _95448 _95449 _95450) = (term708 A x _95448 _95449 _95450)).
Proof. exact (MK_COMB (@lem7148502 A x _95448 _95449 _95450) (@lem7148569 A x _95448 _95449 _95450)). Qed.
Lemma lem7148572 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7148573 (x : Prop) : (x = x) = True.
Proof. exact (@lem7148572 Prop x). Qed.
Lemma lem7148574 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : ((term708 A x _95448 _95449 _95450) = (term708 A x _95448 _95449 _95450)) = True.
Proof. exact (@lem7148573 (term708 A x _95448 _95449 _95450)). Qed.
Lemma lem7148575 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : ((term632 A x _95449 _95448 _95450) = (term713 A x _95448 _95449 _95450)) = True.
Proof. exact (TRANS (@lem7148570 A x _95448 _95449 _95450) (@lem7148574 A x _95448 _95449 _95450)). Qed.
Lemma lem7148576 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : True = ((term632 A x _95449 _95448 _95450) = (term713 A x _95448 _95449 _95450)).
Proof. exact (SYM (@lem7148575 A x _95448 _95449 _95450)). Qed.
Lemma lem7148577 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term632 A x _95449 _95448 _95450) = (term713 A x _95448 _95449 _95450).
Proof. exact (EQ_MP (@lem7148576 A x _95448 _95449 _95450) (@lem0)). Qed.
Lemma lem7148578 {A : Type'} (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) (x : type645 A) (h1 : term427 A x) : term713 A x _95448 _95449 _95450.
Proof. exact (EQ_MP (@lem7148577 A x _95448 _95449 _95450) (@lem7147566 A _95449 _95448 _95450 x h1)). Qed.
Lemma lem7148580 (b : Prop) (a : Prop) : (a \/ b) = (term667 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7148581 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term713 A x _95448 _95449 _95450) = (term716 A x _95449 _95448 _95450).
Proof. exact (@lem7148580 (term605 A x _95448 _95449 _95450) (term526 A _95449 _95448 _95450)). Qed.
Lemma lem7148583 (a : Prop) (b : Prop) : (term669 a b) = (term670 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7148584 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term717 A x _95448 _95449 _95450) = (term718 A x _95448 _95449 _95450).
Proof. exact (@lem7148583 (term447 A _95448) (term600 A x _95448 _95449 _95450)). Qed.
Lemma lem7148586 (a : Prop) : (term674 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7148587 {A : Type'} (_95448 : A -> Prop) : (term675 A _95448) = (@I ((A -> Prop) -> Prop) (@FINITE A) _95448).
Proof. exact (@lem7148586 (@I ((A -> Prop) -> Prop) (@FINITE A) _95448)). Qed.
Lemma lem7148588 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7148589 {A : Type'} (_95448 : A -> Prop) : (term676 A _95448) = (term433 A _95448).
Proof. exact (MK_COMB (@lem7148588) (@lem7148587 A _95448)). Qed.
Lemma lem7148591 (a : Prop) (b : Prop) : (term669 a b) = (term670 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7148592 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term719 A x _95448 _95449 _95450) = (term720 A x _95448 _95449 _95450).
Proof. exact (@lem7148591 (_95448 = (@EMPTY A)) (term541 A x _95448 _95449 _95450)). Qed.
Lemma lem7148594 (a : Prop) : (term674 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7148595 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term721 A x _95448 _95449 _95450) = (term539 A x _95448 _95449 _95450).
Proof. exact (@lem7148594 (term539 A x _95448 _95449 _95450)). Qed.
Lemma lem7148596 {A : Type'} (_95448 : A -> Prop) : (term47 A _95448) = (term47 A _95448).
Proof. exact (eq_refl (term47 A _95448)). Qed.
Lemma lem7148597 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term720 A x _95448 _95449 _95450) = (term722 A x _95448 _95449 _95450).
Proof. exact (MK_COMB (@lem7148596 A _95448) (@lem7148595 A x _95448 _95449 _95450)). Qed.
Lemma lem7148598 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term719 A x _95448 _95449 _95450) = (term722 A x _95448 _95449 _95450).
Proof. exact (TRANS (@lem7148592 A x _95448 _95449 _95450) (@lem7148597 A x _95448 _95449 _95450)). Qed.
Lemma lem7148599 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term718 A x _95448 _95449 _95450) = (term723 A x _95448 _95449 _95450).
Proof. exact (MK_COMB (@lem7148589 A _95448) (@lem7148598 A x _95448 _95449 _95450)). Qed.
Lemma lem7148600 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term717 A x _95448 _95449 _95450) = (term723 A x _95448 _95449 _95450).
Proof. exact (TRANS (@lem7148584 A x _95448 _95449 _95450) (@lem7148599 A x _95448 _95449 _95450)). Qed.
Lemma lem7148601 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7148602 {A : Type'} (x : type645 A) (_95448 : A -> Prop) (_95449 : A -> real) (_95450 : real) : (term724 A x _95448 _95449 _95450) = (term725 A x _95448 _95449 _95450).
Proof. exact (MK_COMB (@lem7148601) (@lem7148600 A x _95448 _95449 _95450)). Qed.
Lemma lem7148603 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term526 A _95449 _95448 _95450) = (term526 A _95449 _95448 _95450).
Proof. exact (eq_refl (term526 A _95449 _95448 _95450)). Qed.
Lemma lem7148604 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term716 A x _95449 _95448 _95450) = (term726 A x _95449 _95448 _95450).
Proof. exact (MK_COMB (@lem7148602 A x _95448 _95449 _95450) (@lem7148603 A _95449 _95448 _95450)). Qed.
Lemma lem7148605 {A : Type'} (x : type645 A) (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) : (term713 A x _95448 _95449 _95450) = (term726 A x _95449 _95448 _95450).
Proof. exact (TRANS (@lem7148581 A x _95449 _95448 _95450) (@lem7148604 A x _95449 _95448 _95450)). Qed.
Lemma lem7148607 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term648 A f b s) (h4 : term96 A s f b) : term727 A x f b s.
Proof. exact (conj (@lem7148147 A s h2) (@lem7148425 A x s f b h1 h2 h3 h4)). Qed.
Lemma lem7148608 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term648 A f b s) (h4 : term96 A s f b) : term728 A x f b s.
Proof. exact (conj (@lem7148139 A s f b h4) (@lem7148607 A x s f b h1 h2 h3 h4)). Qed.
Lemma lem7148610 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) (x : type645 A) (h1 : term427 A x) : term726 A x _95449 _95448 _95450.
Proof. exact (EQ_MP (@lem7148605 A x _95449 _95448 _95450) (@lem7148578 A _95448 _95449 _95450 x h1)). Qed.
Lemma lem7148611 {A : Type'} (_95449 : A -> real) (_95448 : A -> Prop) (_95450 : real) (x : type645 A) (h1 : term427 A x) : term726 A x _95449 _95448 _95450.
Proof. exact (@lem7148610 A _95449 _95448 _95450 x h1). Qed.
Lemma lem7148612 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (x : type645 A) (h1 : term427 A x) : term729 A x f b s.
Proof. exact (@lem7148611 A f s (term577 A b s) x h1). Qed.
Lemma lem7148615 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term648 A f b s) (h4 : term96 A s f b) : term650 A f b s.
Proof. exact (@lem7148612 A f b s x h1 (@lem7148608 A x s f b h1 h2 h3 h4)). Qed.
Lemma lem7148616 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term96 A s f b) : term730 A f b s.
Proof. exact (fun h0 : term648 A f b s => @lem7148615 A x s f b h1 h2 h0 h3). Qed.
Lemma lem7148618 (p : Prop) : (term642 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7148619 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : (term730 A f b s) = (term650 A f b s).
Proof. exact (@lem7148618 (term650 A f b s)). Qed.
Lemma lem7148620 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term96 A s f b) : term650 A f b s.
Proof. exact (EQ_MP (@lem7148619 A f b s) (@lem7148616 A x s f b h1 h2 h3)). Qed.
Lemma lem7148638 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7148639 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term638 _95493 _95494 _95491 _95492) = (term731 _95493 _95494 _95491 _95492).
Proof. exact (@lem7148638 (@I (real -> Prop) _95493 _95494) (term732 _95492 _95494) (term733 _95491 _95492)). Qed.
Lemma lem7148657 (_95491 : real -> Prop) (_95493 : real -> Prop) : (term734 _95491 _95493) = (term734 _95491 _95493).
Proof. exact (eq_refl (term734 _95491 _95493)). Qed.
Lemma lem7148658 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term640 _95493 _95494 _95491 _95492) = (term735 _95493 _95494 _95491 _95492).
Proof. exact (MK_COMB (@lem7148657 _95491 _95493) (@lem7148639 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148662 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7148663 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term735 _95493 _95494 _95491 _95492) = (term736 _95493 _95494 _95491 _95492).
Proof. exact (@lem7148662 (@I (real -> Prop) _95493 _95494) (term737 _95491 _95493) (term738 _95494 _95491 _95492)). Qed.
Lemma lem7148693 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term640 _95493 _95494 _95491 _95492) = (term736 _95493 _95494 _95491 _95492).
Proof. exact (TRANS (@lem7148658 _95493 _95494 _95491 _95492) (@lem7148663 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7148695 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term739 _95493 _95494 _95491 _95492) = (term740 _95493 _95494 _95491 _95492).
Proof. exact (MK_COMB (@lem7148694) (@lem7148693 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148699 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7148700 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term741 _95493 _95494 _95491 _95492) = (term640 _95493 _95494 _95491 _95492).
Proof. exact (@lem7148699 (term737 _95491 _95493) (term732 _95492 _95494) (term635 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148716 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7148717 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term638 _95493 _95494 _95491 _95492) = (term731 _95493 _95494 _95491 _95492).
Proof. exact (@lem7148716 (@I (real -> Prop) _95493 _95494) (term732 _95492 _95494) (term733 _95491 _95492)). Qed.
Lemma lem7148735 (_95491 : real -> Prop) (_95493 : real -> Prop) : (term734 _95491 _95493) = (term734 _95491 _95493).
Proof. exact (eq_refl (term734 _95491 _95493)). Qed.
Lemma lem7148736 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term640 _95493 _95494 _95491 _95492) = (term735 _95493 _95494 _95491 _95492).
Proof. exact (MK_COMB (@lem7148735 _95491 _95493) (@lem7148717 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148740 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7148741 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term735 _95493 _95494 _95491 _95492) = (term736 _95493 _95494 _95491 _95492).
Proof. exact (@lem7148740 (@I (real -> Prop) _95493 _95494) (term737 _95491 _95493) (term738 _95494 _95491 _95492)). Qed.
Lemma lem7148771 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term640 _95493 _95494 _95491 _95492) = (term736 _95493 _95494 _95491 _95492).
Proof. exact (TRANS (@lem7148736 _95493 _95494 _95491 _95492) (@lem7148741 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148772 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term741 _95493 _95494 _95491 _95492) = (term736 _95493 _95494 _95491 _95492).
Proof. exact (TRANS (@lem7148700 _95493 _95494 _95491 _95492) (@lem7148771 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148773 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : ((term640 _95493 _95494 _95491 _95492) = (term741 _95493 _95494 _95491 _95492)) = ((term736 _95493 _95494 _95491 _95492) = (term736 _95493 _95494 _95491 _95492)).
Proof. exact (MK_COMB (@lem7148695 _95493 _95494 _95491 _95492) (@lem7148772 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148775 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7148776 (x : Prop) : (x = x) = True.
Proof. exact (@lem7148775 Prop x). Qed.
Lemma lem7148777 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : ((term736 _95493 _95494 _95491 _95492) = (term736 _95493 _95494 _95491 _95492)) = True.
Proof. exact (@lem7148776 (term736 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148778 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : ((term640 _95493 _95494 _95491 _95492) = (term741 _95493 _95494 _95491 _95492)) = True.
Proof. exact (TRANS (@lem7148773 _95493 _95494 _95491 _95492) (@lem7148777 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148779 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : True = ((term640 _95493 _95494 _95491 _95492) = (term741 _95493 _95494 _95491 _95492)).
Proof. exact (SYM (@lem7148778 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148780 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term640 _95493 _95494 _95491 _95492) = (term741 _95493 _95494 _95491 _95492).
Proof. exact (EQ_MP (@lem7148779 _95493 _95494 _95491 _95492) (@lem0)). Qed.
Lemma lem7148781 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : term741 _95493 _95494 _95491 _95492.
Proof. exact (EQ_MP (@lem7148780 _95493 _95494 _95491 _95492) (@lem7147661 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148783 (b : Prop) (a : Prop) : (a \/ b) = (term667 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7148784 (_95493 : real -> Prop) (_95491 : real -> Prop) (_95492 : real) (_95494 : real) : (term741 _95493 _95494 _95491 _95492) = (term742 _95493 _95491 _95492 _95494).
Proof. exact (@lem7148783 (term743 _95493 _95494 _95491 _95492) (term732 _95492 _95494)). Qed.
Lemma lem7148786 (a : Prop) (b : Prop) : (term669 a b) = (term670 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7148787 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term744 _95493 _95494 _95491 _95492) = (term745 _95493 _95494 _95491 _95492).
Proof. exact (@lem7148786 (term737 _95491 _95493) (term635 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148789 (a : Prop) : (term674 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7148790 (_95491 : real -> Prop) (_95493 : real -> Prop) : (term746 _95491 _95493) = (_95491 = _95493).
Proof. exact (@lem7148789 (_95491 = _95493)). Qed.
Lemma lem7148791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7148792 (_95491 : real -> Prop) (_95493 : real -> Prop) : (term747 _95491 _95493) = (term748 _95491 _95493).
Proof. exact (MK_COMB (@lem7148791) (@lem7148790 _95491 _95493)). Qed.
Lemma lem7148794 (a : Prop) (b : Prop) : (term669 a b) = (term670 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7148795 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term749 _95493 _95494 _95491 _95492) = (term750 _95493 _95494 _95491 _95492).
Proof. exact (@lem7148794 (@I (real -> Prop) _95493 _95494) (term733 _95491 _95492)). Qed.
Lemma lem7148797 (a : Prop) : (term674 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7148798 (_95491 : real -> Prop) (_95492 : real) : (term751 _95491 _95492) = (@I (real -> Prop) _95491 _95492).
Proof. exact (@lem7148797 (@I (real -> Prop) _95491 _95492)). Qed.
Lemma lem7148799 (_95493 : real -> Prop) (_95494 : real) : (term752 _95493 _95494) = (term752 _95493 _95494).
Proof. exact (eq_refl (term752 _95493 _95494)). Qed.
Lemma lem7148800 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term750 _95493 _95494 _95491 _95492) = (term753 _95493 _95494 _95491 _95492).
Proof. exact (MK_COMB (@lem7148799 _95493 _95494) (@lem7148798 _95491 _95492)). Qed.
Lemma lem7148801 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term749 _95493 _95494 _95491 _95492) = (term753 _95493 _95494 _95491 _95492).
Proof. exact (TRANS (@lem7148795 _95493 _95494 _95491 _95492) (@lem7148800 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148802 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term745 _95493 _95494 _95491 _95492) = (term754 _95493 _95494 _95491 _95492).
Proof. exact (MK_COMB (@lem7148792 _95491 _95493) (@lem7148801 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148803 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term744 _95493 _95494 _95491 _95492) = (term754 _95493 _95494 _95491 _95492).
Proof. exact (TRANS (@lem7148787 _95493 _95494 _95491 _95492) (@lem7148802 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148804 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7148805 (_95493 : real -> Prop) (_95494 : real) (_95491 : real -> Prop) (_95492 : real) : (term755 _95493 _95494 _95491 _95492) = (term756 _95493 _95494 _95491 _95492).
Proof. exact (MK_COMB (@lem7148804) (@lem7148803 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148806 (_95492 : real) (_95494 : real) : (term732 _95492 _95494) = (term732 _95492 _95494).
Proof. exact (eq_refl (term732 _95492 _95494)). Qed.
Lemma lem7148807 (_95493 : real -> Prop) (_95491 : real -> Prop) (_95492 : real) (_95494 : real) : (term742 _95493 _95491 _95492 _95494) = (term757 _95493 _95491 _95492 _95494).
Proof. exact (MK_COMB (@lem7148805 _95493 _95494 _95491 _95492) (@lem7148806 _95492 _95494)). Qed.
Lemma lem7148808 (_95493 : real -> Prop) (_95491 : real -> Prop) (_95492 : real) (_95494 : real) : (term741 _95493 _95494 _95491 _95492) = (term757 _95493 _95491 _95492 _95494).
Proof. exact (TRANS (@lem7148784 _95493 _95491 _95492 _95494) (@lem7148807 _95493 _95491 _95492 _95494)). Qed.
Lemma lem7148810 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term96 A s f b) : term758 A f b s.
Proof. exact (conj (@lem7148132 A s f b h3) (@lem7148620 A x s f b h1 h2 h3)). Qed.
Lemma lem7148811 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term96 A s f b) : term759 A f b s.
Proof. exact (conj (@lem7148125 A s f) (@lem7148810 A x s f b h1 h2 h3)). Qed.
Lemma lem7148813 (_95493 : real -> Prop) (_95491 : real -> Prop) (_95492 : real) (_95494 : real) : term757 _95493 _95491 _95492 _95494.
Proof. exact (EQ_MP (@lem7148808 _95493 _95491 _95492 _95494) (@lem7148781 _95493 _95494 _95491 _95492)). Qed.
Lemma lem7148814 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term760 A f s b.
Proof. exact (@lem7148813 (term524 A s f) (term524 A s f) (term761 A b s) b). Qed.
Lemma lem7148817 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term96 A s f b) : term762 A s b.
Proof. exact (@lem7148814 A f s b (@lem7148811 A x s f b h1 h2 h3)). Qed.
Lemma lem7148818 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term96 A s f b) : term763 A s b.
Proof. exact (fun h0 : (term761 A b s) = b => @lem7148817 A x s f b h1 h2 h3). Qed.
Lemma lem7148820 (p : Prop) : (term646 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7148821 {A : Type'} (s : A -> Prop) (b : real) : (term763 A s b) = (term762 A s b).
Proof. exact (@lem7148820 ((term761 A b s) = b)). Qed.
Lemma lem7148822 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term292 A s) (h3 : term96 A s f b) : term762 A s b.
Proof. exact (EQ_MP (@lem7148821 A s b) (@lem7148818 A x s f b h1 h2 h3)). Qed.
Lemma lem7148824 (b : Prop) (a : Prop) : (a \/ b) = (term667 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7148827 (_95446 : real) (_95447 : real) : (term505 _95447 _95446) = (term764 _95446 _95447).
Proof. exact (@lem7148824 ((term499 _95446 _95447) = _95446) (_95447 = term503)). Qed.
Lemma lem7148830 (_95446 : real) (_95447 : real) (h1 : term62) : term764 _95446 _95447.
Proof. exact (EQ_MP (@lem7148827 _95446 _95447) (@lem7147380 _95447 _95446 h1)). Qed.
Lemma lem7148831 {A : Type'} (b : real) (s : A -> Prop) (h1 : term62) : term765 A b s.
Proof. exact (@lem7148830 b (term513 A s) h1). Qed.
Lemma lem7148834 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term62) (h3 : term292 A s) (h4 : term96 A s f b) : (term513 A s) = term503.
Proof. exact (@lem7148831 A b s h2 (@lem7148822 A x s f b h1 h3 h4)). Qed.
Lemma lem7148835 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term62) (h3 : term292 A s) (h4 : term96 A s f b) : term766 A s.
Proof. exact (fun h0 : term767 A s => @lem7148834 A x s f b h1 h2 h3 h4). Qed.
Lemma lem7148837 (p : Prop) : (term642 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7148838 {A : Type'} (s : A -> Prop) : (term766 A s) = ((term513 A s) = term503).
Proof. exact (@lem7148837 ((term513 A s) = term503)). Qed.
Lemma lem7148839 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term62) (h3 : term292 A s) (h4 : term96 A s f b) : (term513 A s) = term503.
Proof. exact (EQ_MP (@lem7148838 A s) (@lem7148835 A x s f b h1 h2 h3 h4)). Qed.
Lemma lem7148845 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7148846 (_95457 : nat) (_95458 : nat) : (term481 _95457 _95458) = (term768 _95457 _95458).
Proof. exact (@lem7148845 (_95457 = _95458) (term478 _95457 _95458)). Qed.
Lemma lem7148856 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7148857 (_95457 : nat) (_95458 : nat) : (term769 _95457 _95458) = (term770 _95457 _95458).
Proof. exact (MK_COMB (@lem7148856) (@lem7148846 _95457 _95458)). Qed.
Lemma lem7148867 (_95457 : nat) (_95458 : nat) : (term768 _95457 _95458) = (term768 _95457 _95458).
Proof. exact (eq_refl (term768 _95457 _95458)). Qed.
Lemma lem7148868 (_95457 : nat) (_95458 : nat) : ((term481 _95457 _95458) = (term768 _95457 _95458)) = ((term768 _95457 _95458) = (term768 _95457 _95458)).
Proof. exact (MK_COMB (@lem7148857 _95457 _95458) (@lem7148867 _95457 _95458)). Qed.
Lemma lem7148870 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7148871 (x : Prop) : (x = x) = True.
Proof. exact (@lem7148870 Prop x). Qed.
Lemma lem7148872 (_95457 : nat) (_95458 : nat) : ((term768 _95457 _95458) = (term768 _95457 _95458)) = True.
Proof. exact (@lem7148871 (term768 _95457 _95458)). Qed.
Lemma lem7148873 (_95457 : nat) (_95458 : nat) : ((term481 _95457 _95458) = (term768 _95457 _95458)) = True.
Proof. exact (TRANS (@lem7148868 _95457 _95458) (@lem7148872 _95457 _95458)). Qed.
Lemma lem7148874 (_95457 : nat) (_95458 : nat) : True = ((term481 _95457 _95458) = (term768 _95457 _95458)).
Proof. exact (SYM (@lem7148873 _95457 _95458)). Qed.
Lemma lem7148875 (_95457 : nat) (_95458 : nat) : (term481 _95457 _95458) = (term768 _95457 _95458).
Proof. exact (EQ_MP (@lem7148874 _95457 _95458) (@lem0)). Qed.
Lemma lem7148876 (_95457 : nat) (_95458 : nat) (h1 : term66) : term768 _95457 _95458.
Proof. exact (EQ_MP (@lem7148875 _95457 _95458) (@lem7147404 _95457 _95458 h1)). Qed.
Lemma lem7148878 (b : Prop) (a : Prop) : (a \/ b) = (term667 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7148879 (_95457 : nat) (_95458 : nat) : (term768 _95457 _95458) = (term771 _95457 _95458).
Proof. exact (@lem7148878 (term478 _95457 _95458) (_95457 = _95458)). Qed.
Lemma lem7148881 (a : Prop) : (term674 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7148882 (_95457 : nat) (_95458 : nat) : (term772 _95457 _95458) = ((@I (nat -> real) real_of_num _95457) = (@I (nat -> real) real_of_num _95458)).
Proof. exact (@lem7148881 ((@I (nat -> real) real_of_num _95457) = (@I (nat -> real) real_of_num _95458))). Qed.
Lemma lem7148883 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7148884 (_95457 : nat) (_95458 : nat) : (term773 _95457 _95458) = (term774 _95457 _95458).
Proof. exact (MK_COMB (@lem7148883) (@lem7148882 _95457 _95458)). Qed.
Lemma lem7148885 (_95457 : nat) (_95458 : nat) : (_95457 = _95458) = (_95457 = _95458).
Proof. exact (eq_refl (_95457 = _95458)). Qed.
Lemma lem7148886 (_95457 : nat) (_95458 : nat) : (term771 _95457 _95458) = (term775 _95457 _95458).
Proof. exact (MK_COMB (@lem7148884 _95457 _95458) (@lem7148885 _95457 _95458)). Qed.
Lemma lem7148887 (_95457 : nat) (_95458 : nat) : (term768 _95457 _95458) = (term775 _95457 _95458).
Proof. exact (TRANS (@lem7148879 _95457 _95458) (@lem7148886 _95457 _95458)). Qed.
Lemma lem7148890 (_95457 : nat) (_95458 : nat) (h1 : term66) : term775 _95457 _95458.
Proof. exact (EQ_MP (@lem7148887 _95457 _95458) (@lem7148876 _95457 _95458 h1)). Qed.
Lemma lem7148891 {A : Type'} (s : A -> Prop) (h1 : term66) : term776 A s.
Proof. exact (@lem7148890 (@I ((A -> Prop) -> nat) (@CARD A) s) (@I (nat -> nat) NUMERAL 0) h1). Qed.
Lemma lem7148894 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term66) (h3 : term62) (h4 : term292 A s) (h5 : term96 A s f b) : (@I ((A -> Prop) -> nat) (@CARD A) s) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7148891 A s h2 (@lem7148839 A x s f b h1 h3 h4 h5)). Qed.
Lemma lem7148895 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term66) (h3 : term62) (h4 : term292 A s) (h5 : term96 A s f b) : term777 A s.
Proof. exact (fun h0 : term778 A s => @lem7148894 A x s f b h1 h2 h3 h4 h5). Qed.
Lemma lem7148897 (p : Prop) : (term642 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7148898 {A : Type'} (s : A -> Prop) : (term777 A s) = ((@I ((A -> Prop) -> nat) (@CARD A) s) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (@lem7148897 ((@I ((A -> Prop) -> nat) (@CARD A) s) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem7148899 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term66) (h3 : term62) (h4 : term292 A s) (h5 : term96 A s f b) : (@I ((A -> Prop) -> nat) (@CARD A) s) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (EQ_MP (@lem7148898 A s) (@lem7148895 A x s f b h1 h2 h3 h4 h5)). Qed.
Lemma lem7148901 (b : Prop) (a : Prop) : (a \/ b) = (term667 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7148902 {A : Type'} (_95463 : A -> Prop) (_95464 : nat) : (term451 A _95463 _95464) = (term779 A _95463 _95464).
Proof. exact (@lem7148901 (term449 A _95463 _95464) (term435 A _95463 _95464)). Qed.
Lemma lem7148904 (a : Prop) (b : Prop) : (term669 a b) = (term670 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7148905 {A : Type'} (_95463 : A -> Prop) (_95464 : nat) : (term780 A _95463 _95464) = (term781 A _95463 _95464).
Proof. exact (@lem7148904 (term447 A _95463) (term446 A _95463 _95464)). Qed.
Lemma lem7148907 (a : Prop) : (term674 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7148908 {A : Type'} (_95463 : A -> Prop) : (term675 A _95463) = (@I ((A -> Prop) -> Prop) (@FINITE A) _95463).
Proof. exact (@lem7148907 (@I ((A -> Prop) -> Prop) (@FINITE A) _95463)). Qed.
Lemma lem7148909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7148910 {A : Type'} (_95463 : A -> Prop) : (term676 A _95463) = (term433 A _95463).
Proof. exact (MK_COMB (@lem7148909) (@lem7148908 A _95463)). Qed.
Lemma lem7148912 (a : Prop) : (term674 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7148913 {A : Type'} (_95463 : A -> Prop) (_95464 : nat) : (term782 A _95463 _95464) = ((@I ((A -> Prop) -> nat) (@CARD A) _95463) = _95464).
Proof. exact (@lem7148912 ((@I ((A -> Prop) -> nat) (@CARD A) _95463) = _95464)). Qed.
Lemma lem7148914 {A : Type'} (_95463 : A -> Prop) (_95464 : nat) : (term781 A _95463 _95464) = (term434 A _95463 _95464).
Proof. exact (MK_COMB (@lem7148910 A _95463) (@lem7148913 A _95463 _95464)). Qed.
Lemma lem7148915 {A : Type'} (_95463 : A -> Prop) (_95464 : nat) : (term780 A _95463 _95464) = (term434 A _95463 _95464).
Proof. exact (TRANS (@lem7148905 A _95463 _95464) (@lem7148914 A _95463 _95464)). Qed.
Lemma lem7148916 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7148917 {A : Type'} (_95463 : A -> Prop) (_95464 : nat) : (term783 A _95463 _95464) = (term784 A _95463 _95464).
Proof. exact (MK_COMB (@lem7148916) (@lem7148915 A _95463 _95464)). Qed.
Lemma lem7148918 {A : Type'} (_95463 : A -> Prop) (_95464 : nat) : (term435 A _95463 _95464) = (term435 A _95463 _95464).
Proof. exact (eq_refl (term435 A _95463 _95464)). Qed.
Lemma lem7148919 {A : Type'} (_95463 : A -> Prop) (_95464 : nat) : (term779 A _95463 _95464) = (term785 A _95463 _95464).
Proof. exact (MK_COMB (@lem7148917 A _95463 _95464) (@lem7148918 A _95463 _95464)). Qed.
Lemma lem7148920 {A : Type'} (_95463 : A -> Prop) (_95464 : nat) : (term451 A _95463 _95464) = (term785 A _95463 _95464).
Proof. exact (TRANS (@lem7148902 A _95463 _95464) (@lem7148919 A _95463 _95464)). Qed.
Lemma lem7148922 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term66) (h3 : term62) (h4 : term292 A s) (h5 : term96 A s f b) : term786 A s.
Proof. exact (conj (@lem7148117 A s f b h5) (@lem7148899 A x s f b h1 h2 h3 h4 h5)). Qed.
Lemma lem7148924 {A : Type'} (_95463 : A -> Prop) (_95464 : nat) (h1 : term13 A) : term785 A _95463 _95464.
Proof. exact (EQ_MP (@lem7148920 A _95463 _95464) (@lem7147438 A _95463 _95464 h1)). Qed.
Lemma lem7148925 {A : Type'} (_95463 : A -> Prop) (_95464 : nat) (h1 : term13 A) : term785 A _95463 _95464.
Proof. exact (@lem7148924 A _95463 _95464 h1). Qed.
Lemma lem7148926 {A : Type'} (s : A -> Prop) (h1 : term13 A) : term787 A s.
Proof. exact (@lem7148925 A s (@I (nat -> nat) NUMERAL 0) h1). Qed.
Lemma lem7148929 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term13 A) (h3 : term66) (h4 : term62) (h5 : term292 A s) (h6 : term96 A s f b) : term460 A s.
Proof. exact (@lem7148926 A s h2 (@lem7148922 A x s f b h1 h3 h4 h5 h6)). Qed.
Lemma lem7148930 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term13 A) (h3 : term66) (h4 : term62) (h5 : term292 A s) (h6 : term96 A s f b) : term788 A s.
Proof. exact (fun h0 : term462 A s => @lem7148929 A x s f b h1 h2 h3 h4 h5 h6). Qed.
Lemma lem7148932 (p : Prop) : (term642 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7148933 {A : Type'} (s : A -> Prop) : (term788 A s) = (term460 A s).
Proof. exact (@lem7148932 (term460 A s)). Qed.
Lemma lem7148934 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term13 A) (h3 : term66) (h4 : term62) (h5 : term292 A s) (h6 : term96 A s f b) : term460 A s.
Proof. exact (EQ_MP (@lem7148933 A s) (@lem7148930 A x s f b h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem7148940 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7148941 {A : Type'} (_95460 : A -> Prop) : (term465 A _95460) = (term789 A _95460).
Proof. exact (@lem7148940 (_95460 = (@EMPTY A)) (term462 A _95460)). Qed.
Lemma lem7148949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7148950 {A : Type'} (_95460 : A -> Prop) : (term790 A _95460) = (term791 A _95460).
Proof. exact (MK_COMB (@lem7148949) (@lem7148941 A _95460)). Qed.
Lemma lem7148958 {A : Type'} (_95460 : A -> Prop) : (term789 A _95460) = (term789 A _95460).
Proof. exact (eq_refl (term789 A _95460)). Qed.
Lemma lem7148959 {A : Type'} (_95460 : A -> Prop) : ((term465 A _95460) = (term789 A _95460)) = ((term789 A _95460) = (term789 A _95460)).
Proof. exact (MK_COMB (@lem7148950 A _95460) (@lem7148958 A _95460)). Qed.
Lemma lem7148961 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7148962 (x : Prop) : (x = x) = True.
Proof. exact (@lem7148961 Prop x). Qed.
Lemma lem7148963 {A : Type'} (_95460 : A -> Prop) : ((term789 A _95460) = (term789 A _95460)) = True.
Proof. exact (@lem7148962 (term789 A _95460)). Qed.
Lemma lem7148964 {A : Type'} (_95460 : A -> Prop) : ((term465 A _95460) = (term789 A _95460)) = True.
Proof. exact (TRANS (@lem7148959 A _95460) (@lem7148963 A _95460)). Qed.
Lemma lem7148965 {A : Type'} (_95460 : A -> Prop) : True = ((term465 A _95460) = (term789 A _95460)).
Proof. exact (SYM (@lem7148964 A _95460)). Qed.
Lemma lem7148966 {A : Type'} (_95460 : A -> Prop) : (term465 A _95460) = (term789 A _95460).
Proof. exact (EQ_MP (@lem7148965 A _95460) (@lem0)). Qed.
Lemma lem7148967 {A : Type'} (_95460 : A -> Prop) (h1 : term12 A) : term789 A _95460.
Proof. exact (EQ_MP (@lem7148966 A _95460) (@lem7147416 A _95460 h1)). Qed.
Lemma lem7148969 (b : Prop) (a : Prop) : (a \/ b) = (term667 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7148970 {A : Type'} (_95460 : A -> Prop) : (term789 A _95460) = (term792 A _95460).
Proof. exact (@lem7148969 (term462 A _95460) (_95460 = (@EMPTY A))). Qed.
Lemma lem7148972 (a : Prop) : (term674 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7148973 {A : Type'} (_95460 : A -> Prop) : (term793 A _95460) = (term460 A _95460).
Proof. exact (@lem7148972 (term460 A _95460)). Qed.
Lemma lem7148974 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7148975 {A : Type'} (_95460 : A -> Prop) : (term794 A _95460) = (term795 A _95460).
Proof. exact (MK_COMB (@lem7148974) (@lem7148973 A _95460)). Qed.
Lemma lem7148976 {A : Type'} (_95460 : A -> Prop) : (_95460 = (@EMPTY A)) = (_95460 = (@EMPTY A)).
Proof. exact (eq_refl (_95460 = (@EMPTY A))). Qed.
Lemma lem7148977 {A : Type'} (_95460 : A -> Prop) : (term792 A _95460) = (term796 A _95460).
Proof. exact (MK_COMB (@lem7148975 A _95460) (@lem7148976 A _95460)). Qed.
Lemma lem7148978 {A : Type'} (_95460 : A -> Prop) : (term789 A _95460) = (term796 A _95460).
Proof. exact (TRANS (@lem7148970 A _95460) (@lem7148977 A _95460)). Qed.
Lemma lem7148981 {A : Type'} (_95460 : A -> Prop) (h1 : term12 A) : term796 A _95460.
Proof. exact (EQ_MP (@lem7148978 A _95460) (@lem7148967 A _95460 h1)). Qed.
Lemma lem7148982 {A : Type'} (_95460 : A -> Prop) (h1 : term12 A) : term796 A _95460.
Proof. exact (@lem7148981 A _95460 h1). Qed.
Lemma lem7148983 {A : Type'} (s : A -> Prop) (h1 : term12 A) : term796 A s.
Proof. exact (@lem7148982 A s h1). Qed.
Lemma lem7148986 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term13 A) (h3 : term12 A) (h4 : term66) (h5 : term62) (h6 : term292 A s) (h7 : term96 A s f b) : s = (@EMPTY A).
Proof. exact (@lem7148983 A s h3 (@lem7148934 A x s f b h1 h2 h4 h5 h6 h7)). Qed.
Lemma lem7148987 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term13 A) (h3 : term12 A) (h4 : term66) (h5 : term62) (h6 : term96 A s f b) : term797 A s.
Proof. exact (fun h0 : term292 A s => @lem7148986 A x s f b h1 h2 h3 h4 h5 h0 h6). Qed.
Lemma lem7148989 (p : Prop) : (term642 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7148990 {A : Type'} (s : A -> Prop) : (term797 A s) = (s = (@EMPTY A)).
Proof. exact (@lem7148989 (s = (@EMPTY A))). Qed.
Lemma lem7148991 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term13 A) (h3 : term12 A) (h4 : term66) (h5 : term62) (h6 : term96 A s f b) : s = (@EMPTY A).
Proof. exact (EQ_MP (@lem7148990 A s) (@lem7148987 A x s f b h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem7148994 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7148996 {A : Type'} (s : A -> Prop) : (term292 A s) = (term798 A s).
Proof. exact (@lem7148994 (s = (@EMPTY A))). Qed.
Lemma lem7148999 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term96 A s f b) : term798 A s.
Proof. exact (EQ_MP (@lem7148996 A s) (@lem7147386 A s f b h1)). Qed.
Lemma lem7149002 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term13 A) (h3 : term12 A) (h4 : term66) (h5 : term62) (h6 : term96 A s f b) : False.
Proof. exact (@lem7148999 A s f b h6 (@lem7148991 A x s f b h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem7149003 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term13 A) (h3 : term12 A) (h4 : term66) (h5 : term62) (h6 : term96 A s f b) : term799.
Proof. exact (fun h0 : ~ False => @lem7149002 A x s f b h1 h2 h3 h4 h5 h6). Qed.
Lemma lem7149005 (p : Prop) : (term642 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7149006 : term799 = False.
Proof. exact (@lem7149005 False). Qed.
Lemma lem7149007 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term427 A x) (h2 : term13 A) (h3 : term12 A) (h4 : term66) (h5 : term62) (h6 : term96 A s f b) : False.
Proof. exact (EQ_MP (@lem7149006) (@lem7149003 A x s f b h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem7149008 {A : Type'} (x : type645 A) (s : A -> Prop) (f : A -> real) (h1 : term427 A x) (h2 : term13 A) (h3 : term12 A) (h4 : term66) (h5 : term62) (h6 : term106 A s f) : False.
Proof. exact (ex_elim (@lem7145739 A s f h6) (fun b : real => fun h0 : term105 A s f b => @lem7149007 A x s f b h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem7149009 {A : Type'} (x : type645 A) (s : A -> Prop) (h1 : term427 A x) (h2 : term13 A) (h3 : term12 A) (h4 : term66) (h5 : term62) (h6 : term115 A s) : False.
Proof. exact (ex_elim (@lem7145738 A s h6) (fun f : A -> real => fun h0 : term114 A s f => @lem7149008 A x s f h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem7149010 {A : Type'} (x : type645 A) (h1 : term427 A x) (h2 : term13 A) (h3 : term12 A) (h4 : term66) (h5 : term62) (h6 : term10 A) : False.
Proof. exact (ex_elim (@lem7143539 A h6) (fun s : A -> Prop => fun h0 : term122 A s => @lem7149009 A x s h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem7149011 {_133668 A : Type'} (x : type645 A) (h1 : term11 _133668) (h2 : term427 A x) (h3 : term13 A) (h4 : term12 A) (h5 : term66) (h6 : term62) (h7 : term10 A) : False.
Proof. exact (ex_elim (@lem7145407 _133668 h1) (fun x' : type645 _133668 => fun h0 : term429 _133668 x' => @lem7149010 A x h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem7149012 {_133668 A : Type'} (h1 : term11 _133668) (h2 : term11 A) (h3 : term13 A) (h4 : term12 A) (h5 : term66) (h6 : term62) (h7 : term10 A) : False.
Proof. exact (ex_elim (@lem7145735 A h2) (fun x : type645 A => fun h0 : term429 A x => @lem7149011 _133668 A x h1 h0 h3 h4 h5 h6 h7)). Qed.
Lemma lem7149013 {_133668 A : Type'} (h1 : term11 _133668) (h2 : term13 A) (h3 : term12 A) (h4 : term66) (h5 : term62) (h6 : term10 A) : term18 A.
Proof. exact (fun h0 : term11 A => @lem7149012 _133668 A h1 h0 h2 h3 h4 h5 h6). Qed.
Lemma lem7149014 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (@lem69 (term11 A)). Qed.
Lemma lem7149015 {_133668 A : Type'} (h1 : term11 _133668) (h2 : term13 A) (h3 : term12 A) (h4 : term66) (h5 : term62) (h6 : term10 A) : term19 A.
Proof. exact (EQ_MP (@lem7149014 A) (@lem7149013 _133668 A h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem7149016 {_133668 A : Type'} (h1 : term13 A) (h2 : term12 A) (h3 : term66) (h4 : term62) (h5 : term10 A) : term22 _133668 A.
Proof. exact (fun h0 : term11 _133668 => @lem7149015 _133668 A h0 h1 h2 h3 h4 h5). Qed.
Lemma lem7149017 {_133668 A : Type'} (h1 : term13 A) (h2 : term12 A) (h3 : term66) (h4 : term10 A) : term25 _133668 A.
Proof. exact (fun h0 : term62 => @lem7149016 _133668 A h1 h2 h3 h0 h4). Qed.
Lemma lem7149018 {_133668 A : Type'} (h1 : term13 A) (h2 : term12 A) (h3 : term10 A) : term28 _133668 A.
Proof. exact (fun h0 : term66 => @lem7149017 _133668 A h1 h2 h0 h3). Qed.
Lemma lem7149019 {_133668 A : Type'} (h1 : term13 A) (h2 : term10 A) : term31 _133668 A.
Proof. exact (fun h0 : term12 A => @lem7149018 _133668 A h1 h0 h2). Qed.
Lemma lem7149020 {_133668 A : Type'} (h1 : term13 A) (h2 : term10 A) : term33 _133668 A.
Proof. exact (fun h0 : term12 _133668 => @lem7149019 _133668 A h1 h2). Qed.
Lemma lem7149021 {_133668 A : Type'} (h1 : term10 A) : term36 _133668 A.
Proof. exact (fun h0 : term13 A => @lem7149020 _133668 A h0 h1). Qed.
Lemma lem7149022 {_133668 A : Type'} (h1 : term10 A) : term38 _133668 A.
Proof. exact (fun h0 : term13 _133668 => @lem7149021 _133668 A h1). Qed.
Lemma lem7149023 {_100044 _133668 A : Type'} (h1 : term10 A) : term40 _100044 _133668 A.
Proof. exact (fun h0 : term13 _100044 => @lem7149022 _133668 A h1). Qed.
Lemma lem7149024 {_100044 _133668 A : Type'} : term42 _100044 _133668 A.
Proof. exact (fun h0 : term10 A => @lem7149023 _100044 _133668 A h0). Qed.
Lemma lem7149025 {_100044 _133668 A : Type'} : term14 _100044 _133668 A.
Proof. exact (EQ_MP (@lem7143366 _100044 _133668 A) (@lem7149024 _100044 _133668 A)). Qed.
Lemma lem7149027 {_100044 _133668 A : Type'} : term14 _100044 _133668 A.
Proof. exact (@lem7142770 _100044 _133668 A (@lem7149025 _100044 _133668 A)). Qed.
Lemma lem7149028 {_100044 _133668 A : Type'} (h1 : term10 A) : term39 _100044 _133668 A.
Proof. exact (@lem7149027 _100044 _133668 A (@lem7142738 A h1)). Qed.
Lemma lem7149029 {_133668 A : Type'} (h1 : term10 A) : term37 _133668 A.
Proof. exact (@lem7149028 Prop _133668 A h1 (@lem3863773 Prop)). Qed.
Lemma lem7149030 {_133668 A : Type'} (h1 : term10 A) : term35 _133668 A.
Proof. exact (@lem7149029 _133668 A h1 (@lem7142750 _133668)). Qed.
Lemma lem7149031 {_133668 A : Type'} (h1 : term10 A) : term32 _133668 A.
Proof. exact (@lem7149030 _133668 A h1 (@lem7142749 A)). Qed.
Lemma lem7149032 {_133668 A : Type'} (h1 : term10 A) : term30 _133668 A.
Proof. exact (@lem7149031 _133668 A h1 (@lem7142746 _133668)). Qed.
Lemma lem7149033 {_133668 A : Type'} (h1 : term10 A) : term27 _133668 A.
Proof. exact (@lem7149032 _133668 A h1 (@lem3864294 A)). Qed.
Lemma lem7149034 {_133668 A : Type'} (h1 : term10 A) : term24 _133668 A.
Proof. exact (@lem7149033 _133668 A h1 (@lem1340231)). Qed.
Lemma lem7149035 {_133668 A : Type'} (h1 : term10 A) : term21 _133668 A.
Proof. exact (@lem7149034 _133668 A h1 (@lem1593226)). Qed.
Lemma lem7149036 {A : Type'} (h1 : term10 A) : term18 A.
Proof. exact (@lem7149035 Prop A h1 (@lem7142723 Prop)). Qed.
Lemma lem7149037 {A : Type'} (h1 : term10 A) : False.
Proof. exact (@lem7149036 A h1 (@lem7142739 A)). Qed.
Lemma lem7149038 {A : Type'} (h1 : term10 A) : (term10 A) = False.
Proof. exact (prop_ext (fun h2 : term10 A => @lem7149037 A h1) (fun h2 : False => @lem7142738 A h1)). Qed.
Lemma lem7149039 {A : Type'} (h1 : term10 A) : False.
Proof. exact (EQ_MP (@lem7149038 A h1) (@lem7142738 A h1)). Qed.
Lemma lem7149040 {A : Type'} : term9 A.
Proof. exact (fun h0 : term10 A => @lem7149039 A h0). Qed.
Lemma lem7149041 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem7142737 A) (@lem7149040 A)). Qed.
