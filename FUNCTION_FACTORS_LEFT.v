Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FUNCTION_FACTORS_LEFT_term_abbrevs.
Require Import FUNCTION_FACTORS_LEFT_GEN_spec.
Require Import FUN_EQ_THM_spec.
Require Import o_THM_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3580898 {_91760 _91764 _91768 : Type'} : term0 _91760 _91764 _91768.
Proof. exact (@lem3580897 _91760 _91764 _91768). Qed.
Lemma lem3580899 {_91760 _91764 _91768 : Type'} : term1 _91760 _91764 _91768.
Proof. exact (@lem3580898 _91760 _91764 _91768 (term2 _91768)). Qed.
Lemma lem3580900 {_91760 _91764 _91768 : Type'} : (term1 _91760 _91764 _91768) = (term3 _91760 _91764 _91768).
Proof. exact (eq_refl (term1 _91760 _91764 _91768)). Qed.
Lemma lem3580901 {_91760 _91764 _91768 : Type'} : term3 _91760 _91764 _91768.
Proof. exact (EQ_MP (@lem3580900 _91760 _91764 _91768) (@lem3580899 _91760 _91764 _91768)). Qed.
Lemma lem3580925 {A B : Type'} (f : A -> B) (y : A) : (term4 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3580926 {_91768 : Type'} (f : _91768 -> Prop) (y : _91768) : (term5 _91768 f y) = (f y).
Proof. exact (@lem3580925 _91768 Prop f y). Qed.
Lemma lem3580927 {_91768 : Type'} (x : _91768) : (term6 _91768 x) = (term7 _91768 x).
Proof. exact (@lem3580926 _91768 (term2 _91768) x). Qed.
Lemma lem3580928 {_91768 : Type'} (x : _91768) : (term7 _91768 x) = True.
Proof. exact (eq_refl (term7 _91768 x)). Qed.
Lemma lem3580929 {_91768 : Type'} : (term8 _91768) = (term2 _91768).
Proof. exact (fun_ext (fun x : _91768 => @lem3580928 _91768 x)). Qed.
Lemma lem3580930 {_91768 : Type'} (x : _91768) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3580931 {_91768 : Type'} (x : _91768) : (term6 _91768 x) = (term7 _91768 x).
Proof. exact (MK_COMB (@lem3580929 _91768) (@lem3580930 _91768 x)). Qed.
Lemma lem3580932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3580933 {_91768 : Type'} (x : _91768) : (term9 _91768 x) = (term10 _91768 x).
Proof. exact (MK_COMB (@lem3580932) (@lem3580931 _91768 x)). Qed.
Lemma lem3580934 {_91768 : Type'} (x : _91768) : (term7 _91768 x) = True.
Proof. exact (eq_refl (term7 _91768 x)). Qed.
Lemma lem3580935 {_91768 : Type'} (x : _91768) : ((term6 _91768 x) = (term7 _91768 x)) = ((term7 _91768 x) = True).
Proof. exact (MK_COMB (@lem3580933 _91768 x) (@lem3580934 _91768 x)). Qed.
Lemma lem3580936 {_91768 : Type'} (x : _91768) : (term7 _91768 x) = True.
Proof. exact (EQ_MP (@lem3580935 _91768 x) (@lem3580927 _91768 x)). Qed.
Lemma lem3580937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3580938 {_91768 : Type'} (x : _91768) : (term11 _91768 x) = (and True).
Proof. exact (MK_COMB (@lem3580937) (@lem3580936 _91768 x)). Qed.
Lemma lem3580942 {A B : Type'} (f : A -> B) (y : A) : (term4 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3580943 {_91768 : Type'} (f : _91768 -> Prop) (y : _91768) : (term5 _91768 f y) = (f y).
Proof. exact (@lem3580942 _91768 Prop f y). Qed.
Lemma lem3580944 {_91768 : Type'} (y : _91768) : (term6 _91768 y) = (term7 _91768 y).
Proof. exact (@lem3580943 _91768 (term2 _91768) y). Qed.
Lemma lem3580945 {_91768 : Type'} (x : _91768) : (term7 _91768 x) = True.
Proof. exact (eq_refl (term7 _91768 x)). Qed.
Lemma lem3580946 {_91768 : Type'} : (term8 _91768) = (term2 _91768).
Proof. exact (fun_ext (fun x : _91768 => @lem3580945 _91768 x)). Qed.
Lemma lem3580947 {_91768 : Type'} (y : _91768) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3580948 {_91768 : Type'} (y : _91768) : (term6 _91768 y) = (term7 _91768 y).
Proof. exact (MK_COMB (@lem3580946 _91768) (@lem3580947 _91768 y)). Qed.
Lemma lem3580949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3580950 {_91768 : Type'} (y : _91768) : (term9 _91768 y) = (term10 _91768 y).
Proof. exact (MK_COMB (@lem3580949) (@lem3580948 _91768 y)). Qed.
Lemma lem3580951 {_91768 : Type'} (y : _91768) : (term7 _91768 y) = True.
Proof. exact (eq_refl (term7 _91768 y)). Qed.
Lemma lem3580952 {_91768 : Type'} (y : _91768) : ((term6 _91768 y) = (term7 _91768 y)) = ((term7 _91768 y) = True).
Proof. exact (MK_COMB (@lem3580950 _91768 y) (@lem3580951 _91768 y)). Qed.
Lemma lem3580953 {_91768 : Type'} (y : _91768) : (term7 _91768 y) = True.
Proof. exact (EQ_MP (@lem3580952 _91768 y) (@lem3580944 _91768 y)). Qed.
Lemma lem3580954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3580955 {_91768 : Type'} (y : _91768) : (term11 _91768 y) = (and True).
Proof. exact (MK_COMB (@lem3580954) (@lem3580953 _91768 y)). Qed.
Lemma lem3580958 {_91764 _91768 : Type'} (x : _91768) (g : _91768 -> _91764) (y : _91768) : ((g x) = (g y)) = ((g x) = (g y)).
Proof. exact (eq_refl ((g x) = (g y))). Qed.
Lemma lem3580959 {_91764 _91768 : Type'} (x : _91768) (g : _91768 -> _91764) (y : _91768) : (term12 _91764 _91768 x g y) = (term13 _91764 _91768 x g y).
Proof. exact (MK_COMB (@lem3580955 _91768 y) (@lem3580958 _91764 _91768 x g y)). Qed.
Lemma lem3580961 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3580962 {_91764 _91768 : Type'} (x : _91768) (g : _91768 -> _91764) (y : _91768) : (term13 _91764 _91768 x g y) = ((g x) = (g y)).
Proof. exact (@lem3580961 ((g x) = (g y))). Qed.
Lemma lem3580965 {_91764 _91768 : Type'} (x : _91768) (g : _91768 -> _91764) (y : _91768) : (term12 _91764 _91768 x g y) = ((g x) = (g y)).
Proof. exact (TRANS (@lem3580959 _91764 _91768 x g y) (@lem3580962 _91764 _91768 x g y)). Qed.
Lemma lem3580966 {_91764 _91768 : Type'} (x : _91768) (g : _91768 -> _91764) (y : _91768) : (term14 _91764 _91768 x g y) = (term13 _91764 _91768 x g y).
Proof. exact (MK_COMB (@lem3580938 _91768 x) (@lem3580965 _91764 _91768 x g y)). Qed.
Lemma lem3580968 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3580969 {_91764 _91768 : Type'} (x : _91768) (g : _91768 -> _91764) (y : _91768) : (term13 _91764 _91768 x g y) = ((g x) = (g y)).
Proof. exact (@lem3580968 ((g x) = (g y))). Qed.
Lemma lem3580972 {_91764 _91768 : Type'} (x : _91768) (g : _91768 -> _91764) (y : _91768) : (term14 _91764 _91768 x g y) = ((g x) = (g y)).
Proof. exact (TRANS (@lem3580966 _91764 _91768 x g y) (@lem3580969 _91764 _91768 x g y)). Qed.
Lemma lem3580973 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3580974 {_91764 _91768 : Type'} (x : _91768) (g : _91768 -> _91764) (y : _91768) : (term15 _91764 _91768 x g y) = (term16 _91764 _91768 x g y).
Proof. exact (MK_COMB (@lem3580973) (@lem3580972 _91764 _91768 x g y)). Qed.
Lemma lem3580977 {_91760 _91768 : Type'} (x : _91768) (f : _91768 -> _91760) (y : _91768) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3580978 {_91760 _91764 _91768 : Type'} (g : _91768 -> _91764) (x : _91768) (f : _91768 -> _91760) (y : _91768) : (term17 _91760 _91764 _91768 g x f y) = (term18 _91760 _91764 _91768 g x f y).
Proof. exact (MK_COMB (@lem3580974 _91764 _91768 x g y) (@lem3580977 _91760 _91768 x f y)). Qed.
Lemma lem3580983 {_91760 _91764 _91768 : Type'} (g : _91768 -> _91764) (x : _91768) (f : _91768 -> _91760) : (term19 _91760 _91764 _91768 g x f) = (term20 _91760 _91764 _91768 g x f).
Proof. exact (fun_ext (fun y : _91768 => @lem3580978 _91760 _91764 _91768 g x f y)). Qed.
Lemma lem3580984 {_91768 : Type'} : (@all _91768) = (@all _91768).
Proof. exact (eq_refl (@all _91768)). Qed.
Lemma lem3580985 {_91760 _91764 _91768 : Type'} (g : _91768 -> _91764) (x : _91768) (f : _91768 -> _91760) : (term21 _91760 _91764 _91768 g x f) = (term22 _91760 _91764 _91768 g x f).
Proof. exact (MK_COMB (@lem3580984 _91768) (@lem3580983 _91760 _91764 _91768 g x f)). Qed.
Lemma lem3580990 {_91760 _91764 _91768 : Type'} (g : _91768 -> _91764) (f : _91768 -> _91760) : (term23 _91760 _91764 _91768 g f) = (term24 _91760 _91764 _91768 g f).
Proof. exact (fun_ext (fun x : _91768 => @lem3580985 _91760 _91764 _91768 g x f)). Qed.
Lemma lem3580991 {_91768 : Type'} : (@all _91768) = (@all _91768).
Proof. exact (eq_refl (@all _91768)). Qed.
Lemma lem3580992 {_91760 _91764 _91768 : Type'} (g : _91768 -> _91764) (f : _91768 -> _91760) : (term25 _91760 _91764 _91768 g f) = (term26 _91760 _91764 _91768 g f).
Proof. exact (MK_COMB (@lem3580991 _91768) (@lem3580990 _91760 _91764 _91768 g f)). Qed.
Lemma lem3580997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3580998 {_91760 _91764 _91768 : Type'} (g : _91768 -> _91764) (f : _91768 -> _91760) : (term27 _91760 _91764 _91768 g f) = (term28 _91760 _91764 _91768 g f).
Proof. exact (MK_COMB (@lem3580997) (@lem3580992 _91760 _91764 _91768 g f)). Qed.
Lemma lem3581010 {A B : Type'} (f : A -> B) (y : A) : (term4 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3581011 {_91768 : Type'} (f : _91768 -> Prop) (y : _91768) : (term5 _91768 f y) = (f y).
Proof. exact (@lem3581010 _91768 Prop f y). Qed.
Lemma lem3581012 {_91768 : Type'} (x : _91768) : (term6 _91768 x) = (term7 _91768 x).
Proof. exact (@lem3581011 _91768 (term2 _91768) x). Qed.
Lemma lem3581013 {_91768 : Type'} (x : _91768) : (term7 _91768 x) = True.
Proof. exact (eq_refl (term7 _91768 x)). Qed.
Lemma lem3581014 {_91768 : Type'} : (term8 _91768) = (term2 _91768).
Proof. exact (fun_ext (fun x : _91768 => @lem3581013 _91768 x)). Qed.
Lemma lem3581015 {_91768 : Type'} (x : _91768) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3581016 {_91768 : Type'} (x : _91768) : (term6 _91768 x) = (term7 _91768 x).
Proof. exact (MK_COMB (@lem3581014 _91768) (@lem3581015 _91768 x)). Qed.
Lemma lem3581017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3581018 {_91768 : Type'} (x : _91768) : (term9 _91768 x) = (term10 _91768 x).
Proof. exact (MK_COMB (@lem3581017) (@lem3581016 _91768 x)). Qed.
Lemma lem3581019 {_91768 : Type'} (x : _91768) : (term7 _91768 x) = True.
Proof. exact (eq_refl (term7 _91768 x)). Qed.
Lemma lem3581020 {_91768 : Type'} (x : _91768) : ((term6 _91768 x) = (term7 _91768 x)) = ((term7 _91768 x) = True).
Proof. exact (MK_COMB (@lem3581018 _91768 x) (@lem3581019 _91768 x)). Qed.
Lemma lem3581021 {_91768 : Type'} (x : _91768) : (term7 _91768 x) = True.
Proof. exact (EQ_MP (@lem3581020 _91768 x) (@lem3581012 _91768 x)). Qed.
Lemma lem3581022 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3581023 {_91768 : Type'} (x : _91768) : (term29 _91768 x) = (imp True).
Proof. exact (MK_COMB (@lem3581022) (@lem3581021 _91768 x)). Qed.
Lemma lem3581026 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) (h : _91764 -> _91760) (g : _91768 -> _91764) (x : _91768) : ((f x) = (term30 _91760 _91764 _91768 h g x)) = ((f x) = (term30 _91760 _91764 _91768 h g x)).
Proof. exact (eq_refl ((f x) = (term30 _91760 _91764 _91768 h g x))). Qed.
Lemma lem3581027 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) (h : _91764 -> _91760) (g : _91768 -> _91764) (x : _91768) : (term31 _91760 _91764 _91768 f h g x) = (term32 _91760 _91764 _91768 f h g x).
Proof. exact (MK_COMB (@lem3581023 _91768 x) (@lem3581026 _91760 _91764 _91768 f h g x)). Qed.
Lemma lem3581029 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3581030 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) (h : _91764 -> _91760) (g : _91768 -> _91764) (x : _91768) : (term32 _91760 _91764 _91768 f h g x) = ((f x) = (term30 _91760 _91764 _91768 h g x)).
Proof. exact (@lem3581029 ((f x) = (term30 _91760 _91764 _91768 h g x))). Qed.
Lemma lem3581033 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) (h : _91764 -> _91760) (g : _91768 -> _91764) (x : _91768) : (term31 _91760 _91764 _91768 f h g x) = ((f x) = (term30 _91760 _91764 _91768 h g x)).
Proof. exact (TRANS (@lem3581027 _91760 _91764 _91768 f h g x) (@lem3581030 _91760 _91764 _91768 f h g x)). Qed.
Lemma lem3581034 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) (h : _91764 -> _91760) (g : _91768 -> _91764) : (term33 _91760 _91764 _91768 f h g) = (term34 _91760 _91764 _91768 f h g).
Proof. exact (fun_ext (fun x : _91768 => @lem3581033 _91760 _91764 _91768 f h g x)). Qed.
Lemma lem3581035 {_91768 : Type'} : (@all _91768) = (@all _91768).
Proof. exact (eq_refl (@all _91768)). Qed.
Lemma lem3581036 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) (h : _91764 -> _91760) (g : _91768 -> _91764) : (term35 _91760 _91764 _91768 f h g) = (term36 _91760 _91764 _91768 f h g).
Proof. exact (MK_COMB (@lem3581035 _91768) (@lem3581034 _91760 _91764 _91768 f h g)). Qed.
Lemma lem3581041 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) (g : _91768 -> _91764) : (term37 _91760 _91764 _91768 f g) = (term38 _91760 _91764 _91768 f g).
Proof. exact (fun_ext (fun h : _91764 -> _91760 => @lem3581036 _91760 _91764 _91768 f h g)). Qed.
Lemma lem3581042 {_91760 _91764 : Type'} : (@ex (_91764 -> _91760)) = (@ex (_91764 -> _91760)).
Proof. exact (eq_refl (@ex (_91764 -> _91760))). Qed.
Lemma lem3581043 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) (g : _91768 -> _91764) : (term39 _91760 _91764 _91768 f g) = (term40 _91760 _91764 _91768 f g).
Proof. exact (MK_COMB (@lem3581042 _91760 _91764) (@lem3581041 _91760 _91764 _91768 f g)). Qed.
Lemma lem3581048 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) (g : _91768 -> _91764) : ((term25 _91760 _91764 _91768 g f) = (term39 _91760 _91764 _91768 f g)) = ((term26 _91760 _91764 _91768 g f) = (term40 _91760 _91764 _91768 f g)).
Proof. exact (MK_COMB (@lem3580998 _91760 _91764 _91768 g f) (@lem3581043 _91760 _91764 _91768 f g)). Qed.
Lemma lem3581051 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) : (term41 _91760 _91764 _91768 f) = (term42 _91760 _91764 _91768 f).
Proof. exact (fun_ext (fun g : _91768 -> _91764 => @lem3581048 _91760 _91764 _91768 f g)). Qed.
Lemma lem3581052 {_91764 _91768 : Type'} : (@all (_91768 -> _91764)) = (@all (_91768 -> _91764)).
Proof. exact (eq_refl (@all (_91768 -> _91764))). Qed.
Lemma lem3581053 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) : (term43 _91760 _91764 _91768 f) = (term44 _91760 _91764 _91768 f).
Proof. exact (MK_COMB (@lem3581052 _91764 _91768) (@lem3581051 _91760 _91764 _91768 f)). Qed.
Lemma lem3581058 {_91760 _91764 _91768 : Type'} : (term45 _91760 _91764 _91768) = (term46 _91760 _91764 _91768).
Proof. exact (fun_ext (fun f : _91768 -> _91760 => @lem3581053 _91760 _91764 _91768 f)). Qed.
Lemma lem3581059 {_91760 _91768 : Type'} : (@all (_91768 -> _91760)) = (@all (_91768 -> _91760)).
Proof. exact (eq_refl (@all (_91768 -> _91760))). Qed.
Lemma lem3581060 {_91760 _91764 _91768 : Type'} : (term3 _91760 _91764 _91768) = (term47 _91760 _91764 _91768).
Proof. exact (MK_COMB (@lem3581059 _91760 _91768) (@lem3581058 _91760 _91764 _91768)). Qed.
Lemma lem3581065 {_91760 _91764 _91768 : Type'} : term47 _91760 _91764 _91768.
Proof. exact (EQ_MP (@lem3581060 _91760 _91764 _91768) (@lem3580901 _91760 _91764 _91768)). Qed.
Lemma lem3581068 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) (g : _91768 -> _91764) (h1 : (term26 _91760 _91764 _91768 g f) = (term40 _91760 _91764 _91768 f g)) : (term26 _91760 _91764 _91768 g f) = (term40 _91760 _91764 _91768 f g).
Proof. exact (h1). Qed.
Lemma lem3581069 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) (g : _91768 -> _91764) (h1 : (term26 _91760 _91764 _91768 g f) = (term40 _91760 _91764 _91768 f g)) : (term40 _91760 _91764 _91768 f g) = (term26 _91760 _91764 _91768 g f).
Proof. exact (SYM (@lem3581068 _91760 _91764 _91768 f g h1)). Qed.
Lemma lem3581070 {_91760 _91764 _91768 : Type'} (g : _91768 -> _91764) (f : _91768 -> _91760) (h1 : (term40 _91760 _91764 _91768 f g) = (term26 _91760 _91764 _91768 g f)) : (term40 _91760 _91764 _91768 f g) = (term26 _91760 _91764 _91768 g f).
Proof. exact (h1). Qed.
Lemma lem3581071 {_91760 _91764 _91768 : Type'} (g : _91768 -> _91764) (f : _91768 -> _91760) (h1 : (term40 _91760 _91764 _91768 f g) = (term26 _91760 _91764 _91768 g f)) : (term26 _91760 _91764 _91768 g f) = (term40 _91760 _91764 _91768 f g).
Proof. exact (SYM (@lem3581070 _91760 _91764 _91768 g f h1)). Qed.
Lemma lem3581072 {_91760 _91764 _91768 : Type'} (g : _91768 -> _91764) (f : _91768 -> _91760) : ((term26 _91760 _91764 _91768 g f) = (term40 _91760 _91764 _91768 f g)) = ((term40 _91760 _91764 _91768 f g) = (term26 _91760 _91764 _91768 g f)).
Proof. exact (prop_ext (fun h1 : (term26 _91760 _91764 _91768 g f) = (term40 _91760 _91764 _91768 f g) => @lem3581069 _91760 _91764 _91768 f g h1) (fun h1 : (term40 _91760 _91764 _91768 f g) = (term26 _91760 _91764 _91768 g f) => @lem3581071 _91760 _91764 _91768 g f h1)). Qed.
Lemma lem3581073 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) : (term42 _91760 _91764 _91768 f) = (term48 _91760 _91764 _91768 f).
Proof. exact (fun_ext (fun g : _91768 -> _91764 => @lem3581072 _91760 _91764 _91768 g f)). Qed.
Lemma lem3581074 {_91764 _91768 : Type'} : (@all (_91768 -> _91764)) = (@all (_91768 -> _91764)).
Proof. exact (eq_refl (@all (_91768 -> _91764))). Qed.
Lemma lem3581075 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) : (term44 _91760 _91764 _91768 f) = (term49 _91760 _91764 _91768 f).
Proof. exact (MK_COMB (@lem3581074 _91764 _91768) (@lem3581073 _91760 _91764 _91768 f)). Qed.
Lemma lem3581076 {_91760 _91764 _91768 : Type'} : (term46 _91760 _91764 _91768) = (term50 _91760 _91764 _91768).
Proof. exact (fun_ext (fun f : _91768 -> _91760 => @lem3581075 _91760 _91764 _91768 f)). Qed.
Lemma lem3581077 {_91760 _91768 : Type'} : (@all (_91768 -> _91760)) = (@all (_91768 -> _91760)).
Proof. exact (eq_refl (@all (_91768 -> _91760))). Qed.
Lemma lem3581078 {_91760 _91764 _91768 : Type'} : (term47 _91760 _91764 _91768) = (term51 _91760 _91764 _91768).
Proof. exact (MK_COMB (@lem3581077 _91760 _91768) (@lem3581076 _91760 _91764 _91768)). Qed.
Lemma lem3581079 {_91760 _91764 _91768 : Type'} : term51 _91760 _91764 _91768.
Proof. exact (EQ_MP (@lem3581078 _91760 _91764 _91768) (@lem3581065 _91760 _91764 _91768)). Qed.
Lemma lem3581080 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) : term52 _91760 _91764 _91768 f.
Proof. exact (@lem3581079 _91760 _91764 _91768 f). Qed.
Lemma lem3581081 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) : (term52 _91760 _91764 _91768 f) = (term49 _91760 _91764 _91768 f).
Proof. exact (eq_refl (term52 _91760 _91764 _91768 f)). Qed.
Lemma lem3581082 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) : term49 _91760 _91764 _91768 f.
Proof. exact (EQ_MP (@lem3581081 _91760 _91764 _91768 f) (@lem3581080 _91760 _91764 _91768 f)). Qed.
Lemma lem3581083 {_91760 _91764 _91768 : Type'} (f : _91768 -> _91760) (g : _91768 -> _91764) : term53 _91760 _91764 _91768 f g.
Proof. exact (@lem3581082 _91760 _91764 _91768 f g). Qed.
Lemma lem3581084 {_91760 _91764 _91768 : Type'} (g : _91768 -> _91764) (f : _91768 -> _91760) : (term53 _91760 _91764 _91768 f g) = ((term40 _91760 _91764 _91768 f g) = (term26 _91760 _91764 _91768 g f)).
Proof. exact (eq_refl (term53 _91760 _91764 _91768 f g)). Qed.
Lemma lem3581086 {A B C : Type'} (f : B -> C) : term54 A B C f.
Proof. exact (@lem15456 A B C f). Qed.
Lemma lem3581087 {A B C : Type'} (f : B -> C) : (term54 A B C f) = (term55 A B C f).
Proof. exact (eq_refl (term54 A B C f)). Qed.
Lemma lem3581088 {A B C : Type'} (f : B -> C) : term55 A B C f.
Proof. exact (EQ_MP (@lem3581087 A B C f) (@lem3581086 A B C f)). Qed.
Lemma lem3581089 {A B C : Type'} (f : B -> C) (g : A -> B) : term56 A B C f g.
Proof. exact (@lem3581088 A B C f g). Qed.
Lemma lem3581090 {A B C : Type'} (f : B -> C) (g : A -> B) : (term56 A B C f g) = (term57 A B C f g).
Proof. exact (eq_refl (term56 A B C f g)). Qed.
Lemma lem3581091 {A B C : Type'} (f : B -> C) (g : A -> B) : term57 A B C f g.
Proof. exact (EQ_MP (@lem3581090 A B C f g) (@lem3581089 A B C f g)). Qed.
Lemma lem3581092 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : term58 A B C f g x.
Proof. exact (@lem3581091 A B C f g x). Qed.
Lemma lem3581093 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term58 A B C f g x) = ((@o A B C f g x) = (term59 A B C f g x)).
Proof. exact (eq_refl (term58 A B C f g x)). Qed.
Lemma lem3581095 {A B : Type'} (f : A -> B) : term60 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem3581096 {A B : Type'} (f : A -> B) : (term60 A B f) = (term61 A B f).
Proof. exact (eq_refl (term60 A B f)). Qed.
Lemma lem3581097 {A B : Type'} (f : A -> B) : term61 A B f.
Proof. exact (EQ_MP (@lem3581096 A B f) (@lem3581095 A B f)). Qed.
Lemma lem3581098 {A B : Type'} (f : A -> B) (g : A -> B) : term62 A B f g.
Proof. exact (@lem3581097 A B f g). Qed.
Lemma lem3581099 {A B : Type'} (f : A -> B) (g : A -> B) : (term62 A B f g) = ((f = g) = (term63 A B f g)).
Proof. exact (eq_refl (term62 A B f g)). Qed.
Lemma lem3581140 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term63 A B f g).
Proof. exact (EQ_MP (@lem3581099 A B f g) (@lem3581098 A B f g)). Qed.
Lemma lem3581141 {_91810 _91811 : Type'} (f : _91810 -> _91811) (g : _91810 -> _91811) : (f = g) = (term63 _91810 _91811 f g).
Proof. exact (@lem3581140 _91810 _91811 f g). Qed.
Lemma lem3581142 {_91790 _91810 _91811 : Type'} (f : _91810 -> _91811) (h : _91790 -> _91811) (g : _91810 -> _91790) : (f = (@o _91810 _91790 _91811 h g)) = (term64 _91790 _91810 _91811 f h g).
Proof. exact (@lem3581141 _91810 _91811 f (@o _91810 _91790 _91811 h g)). Qed.
Lemma lem3581152 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term59 A B C f g x).
Proof. exact (EQ_MP (@lem3581093 A B C f g x) (@lem3581092 A B C f g x)). Qed.
Lemma lem3581153 {_91790 _91810 _91811 : Type'} (f : _91790 -> _91811) (g : _91810 -> _91790) (x : _91810) : (@o _91810 _91790 _91811 f g x) = (term65 _91790 _91810 _91811 f g x).
Proof. exact (@lem3581152 _91810 _91790 _91811 f g x). Qed.
Lemma lem3581154 {_91790 _91810 _91811 : Type'} (h : _91790 -> _91811) (g : _91810 -> _91790) (x : _91810) : (@o _91810 _91790 _91811 h g x) = (term65 _91790 _91810 _91811 h g x).
Proof. exact (@lem3581153 _91790 _91810 _91811 h g x). Qed.
Lemma lem3581155 {_91810 _91811 : Type'} (f : _91810 -> _91811) (x : _91810) : (term66 _91810 _91811 f x) = (term66 _91810 _91811 f x).
Proof. exact (eq_refl (term66 _91810 _91811 f x)). Qed.
Lemma lem3581156 {_91790 _91810 _91811 : Type'} (f : _91810 -> _91811) (h : _91790 -> _91811) (g : _91810 -> _91790) (x : _91810) : ((f x) = (@o _91810 _91790 _91811 h g x)) = ((f x) = (term65 _91790 _91810 _91811 h g x)).
Proof. exact (MK_COMB (@lem3581155 _91810 _91811 f x) (@lem3581154 _91790 _91810 _91811 h g x)). Qed.
Lemma lem3581161 {_91790 _91810 _91811 : Type'} (f : _91810 -> _91811) (h : _91790 -> _91811) (g : _91810 -> _91790) : (term67 _91790 _91810 _91811 f h g) = (term68 _91790 _91810 _91811 f h g).
Proof. exact (fun_ext (fun x : _91810 => @lem3581156 _91790 _91810 _91811 f h g x)). Qed.
Lemma lem3581162 {_91810 : Type'} : (@all _91810) = (@all _91810).
Proof. exact (eq_refl (@all _91810)). Qed.
Lemma lem3581163 {_91790 _91810 _91811 : Type'} (f : _91810 -> _91811) (h : _91790 -> _91811) (g : _91810 -> _91790) : (term64 _91790 _91810 _91811 f h g) = (term69 _91790 _91810 _91811 f h g).
Proof. exact (MK_COMB (@lem3581162 _91810) (@lem3581161 _91790 _91810 _91811 f h g)). Qed.
Lemma lem3581168 {_91790 _91810 _91811 : Type'} (f : _91810 -> _91811) (h : _91790 -> _91811) (g : _91810 -> _91790) : (f = (@o _91810 _91790 _91811 h g)) = (term69 _91790 _91810 _91811 f h g).
Proof. exact (TRANS (@lem3581142 _91790 _91810 _91811 f h g) (@lem3581163 _91790 _91810 _91811 f h g)). Qed.
Lemma lem3581169 {_91790 _91810 _91811 : Type'} (f : _91810 -> _91811) (g : _91810 -> _91790) : (term70 _91790 _91810 _91811 f g) = (term71 _91790 _91810 _91811 f g).
Proof. exact (fun_ext (fun h : _91790 -> _91811 => @lem3581168 _91790 _91810 _91811 f h g)). Qed.
Lemma lem3581170 {_91790 _91811 : Type'} : (@ex (_91790 -> _91811)) = (@ex (_91790 -> _91811)).
Proof. exact (eq_refl (@ex (_91790 -> _91811))). Qed.
Lemma lem3581171 {_91790 _91810 _91811 : Type'} (f : _91810 -> _91811) (g : _91810 -> _91790) : (term72 _91790 _91810 _91811 f g) = (term73 _91790 _91810 _91811 f g).
Proof. exact (MK_COMB (@lem3581170 _91790 _91811) (@lem3581169 _91790 _91810 _91811 f g)). Qed.
Lemma lem3581173 {_91760 _91764 _91768 : Type'} (g : _91768 -> _91764) (f : _91768 -> _91760) : (term40 _91760 _91764 _91768 f g) = (term26 _91760 _91764 _91768 g f).
Proof. exact (EQ_MP (@lem3581084 _91760 _91764 _91768 g f) (@lem3581083 _91760 _91764 _91768 f g)). Qed.
Lemma lem3581174 {_91790 _91810 _91811 : Type'} (g : _91810 -> _91790) (f : _91810 -> _91811) : (term73 _91790 _91810 _91811 f g) = (term74 _91790 _91810 _91811 g f).
Proof. exact (@lem3581173 _91811 _91790 _91810 g f). Qed.
Lemma lem3581195 {_91790 _91810 _91811 : Type'} (g : _91810 -> _91790) (f : _91810 -> _91811) : (term72 _91790 _91810 _91811 f g) = (term74 _91790 _91810 _91811 g f).
Proof. exact (TRANS (@lem3581171 _91790 _91810 _91811 f g) (@lem3581174 _91790 _91810 _91811 g f)). Qed.
Lemma lem3581196 {_91790 _91810 _91811 : Type'} (g : _91810 -> _91790) (f : _91810 -> _91811) : (term75 _91790 _91810 _91811 g f) = (term75 _91790 _91810 _91811 g f).
Proof. exact (eq_refl (term75 _91790 _91810 _91811 g f)). Qed.
Lemma lem3581197 {_91790 _91810 _91811 : Type'} (g : _91810 -> _91790) (f : _91810 -> _91811) : ((term74 _91790 _91810 _91811 g f) = (term72 _91790 _91810 _91811 f g)) = ((term74 _91790 _91810 _91811 g f) = (term74 _91790 _91810 _91811 g f)).
Proof. exact (MK_COMB (@lem3581196 _91790 _91810 _91811 g f) (@lem3581195 _91790 _91810 _91811 g f)). Qed.
Lemma lem3581199 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3581200 (x : Prop) : (x = x) = True.
Proof. exact (@lem3581199 Prop x). Qed.
Lemma lem3581201 {_91790 _91810 _91811 : Type'} (g : _91810 -> _91790) (f : _91810 -> _91811) : ((term74 _91790 _91810 _91811 g f) = (term74 _91790 _91810 _91811 g f)) = True.
Proof. exact (@lem3581200 (term74 _91790 _91810 _91811 g f)). Qed.
Lemma lem3581202 {_91790 _91810 _91811 : Type'} (f : _91810 -> _91811) (g : _91810 -> _91790) : ((term74 _91790 _91810 _91811 g f) = (term72 _91790 _91810 _91811 f g)) = True.
Proof. exact (TRANS (@lem3581197 _91790 _91810 _91811 g f) (@lem3581201 _91790 _91810 _91811 g f)). Qed.
Lemma lem3581203 {_91790 _91810 _91811 : Type'} (f : _91810 -> _91811) : (term76 _91790 _91810 _91811 f) = (term77 _91790 _91810).
Proof. exact (fun_ext (fun g : _91810 -> _91790 => @lem3581202 _91790 _91810 _91811 f g)). Qed.
Lemma lem3581204 {_91790 _91810 : Type'} : (@all (_91810 -> _91790)) = (@all (_91810 -> _91790)).
Proof. exact (eq_refl (@all (_91810 -> _91790))). Qed.
Lemma lem3581205 {_91790 _91810 _91811 : Type'} (f : _91810 -> _91811) : (term78 _91790 _91810 _91811 f) = (term79 _91790 _91810).
Proof. exact (MK_COMB (@lem3581204 _91790 _91810) (@lem3581203 _91790 _91810 _91811 f)). Qed.
Lemma lem3581207 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3581208 {_91790 _91810 : Type'} (t : Prop) : (term81 _91790 _91810 t) = t.
Proof. exact (@lem3581207 (_91810 -> _91790) t). Qed.
Lemma lem3581209 {_91790 _91810 : Type'} : (term79 _91790 _91810) = True.
Proof. exact (@lem3581208 _91790 _91810 True). Qed.
Lemma lem3581210 {_91790 _91810 _91811 : Type'} (f : _91810 -> _91811) : (term78 _91790 _91810 _91811 f) = True.
Proof. exact (TRANS (@lem3581205 _91790 _91810 _91811 f) (@lem3581209 _91790 _91810)). Qed.
Lemma lem3581211 {_91790 _91810 _91811 : Type'} : (term82 _91790 _91810 _91811) = (term83 _91810 _91811).
Proof. exact (fun_ext (fun f : _91810 -> _91811 => @lem3581210 _91790 _91810 _91811 f)). Qed.
Lemma lem3581212 {_91810 _91811 : Type'} : (@all (_91810 -> _91811)) = (@all (_91810 -> _91811)).
Proof. exact (eq_refl (@all (_91810 -> _91811))). Qed.
Lemma lem3581213 {_91790 _91810 _91811 : Type'} : (term84 _91790 _91810 _91811) = (term85 _91810 _91811).
Proof. exact (MK_COMB (@lem3581212 _91810 _91811) (@lem3581211 _91790 _91810 _91811)). Qed.
Lemma lem3581215 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3581216 {_91810 _91811 : Type'} (t : Prop) : (term86 _91810 _91811 t) = t.
Proof. exact (@lem3581215 (_91810 -> _91811) t). Qed.
Lemma lem3581217 {_91810 _91811 : Type'} : (term85 _91810 _91811) = True.
Proof. exact (@lem3581216 _91810 _91811 True). Qed.
Lemma lem3581218 {_91790 _91810 _91811 : Type'} : (term84 _91790 _91810 _91811) = True.
Proof. exact (TRANS (@lem3581213 _91790 _91810 _91811) (@lem3581217 _91810 _91811)). Qed.
Lemma lem3581219 {_91790 _91810 _91811 : Type'} : True = (term84 _91790 _91810 _91811).
Proof. exact (SYM (@lem3581218 _91790 _91810 _91811)). Qed.
Lemma lem3581220 {_91790 _91810 _91811 : Type'} : term84 _91790 _91810 _91811.
Proof. exact (EQ_MP (@lem3581219 _91790 _91810 _91811) (@lem0)). Qed.
