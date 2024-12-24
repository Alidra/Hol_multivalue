Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm52067_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Require Import thm51886_spec.
Require Import thm51887_spec.
Require Import thm51892_spec.
Require Import thm51893_spec.
Lemma lem51898 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term0 A B f g).
Proof. exact (EQ_MP (@lem51893 A B f g) (@lem51892 A B f g)). Qed.
Lemma lem51899 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (g : type1228 _5264 _5271 _5272) : (f = g) = (term1 _5264 _5271 _5272 f g).
Proof. exact (@lem51898 (prod _5272 _5271) _5264 f g). Qed.
Lemma lem51900 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : ((term2 _5264 _5271 _5272 f) = f) = (term3 _5264 _5271 _5272 f).
Proof. exact (@lem51899 _5264 _5271 _5272 (term2 _5264 _5271 _5272 f) f). Qed.
Lemma lem51906 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term4 _5106 _5107 P) = (term5 _5106 _5107 P).
Proof. exact (EQ_MP (@lem51887 _5106 _5107 P) (@lem51886 _5106 _5107 P)). Qed.
Lemma lem51907 {_5271 _5272 : Type'} (P : type1223 _5271 _5272) : (term4 _5271 _5272 P) = (term5 _5271 _5272 P).
Proof. exact (@lem51906 _5271 _5272 P). Qed.
Lemma lem51908 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term6 _5264 _5271 _5272 f) = (term7 _5264 _5271 _5272 f).
Proof. exact (@lem51907 _5271 _5272 (term8 _5264 _5271 _5272 f)). Qed.
Lemma lem51909 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : prod _5272 _5271) : (term9 _5264 _5271 _5272 f x) = ((term10 _5264 _5271 _5272 f x) = (f x)).
Proof. exact (eq_refl (term9 _5264 _5271 _5272 f x)). Qed.
Lemma lem51910 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term11 _5264 _5271 _5272 f) = (term8 _5264 _5271 _5272 f).
Proof. exact (fun_ext (fun x : prod _5272 _5271 => @lem51909 _5264 _5271 _5272 f x)). Qed.
Lemma lem51911 {_5271 _5272 : Type'} : (@all (prod _5272 _5271)) = (@all (prod _5272 _5271)).
Proof. exact (eq_refl (@all (prod _5272 _5271))). Qed.
Lemma lem51912 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term6 _5264 _5271 _5272 f) = (term3 _5264 _5271 _5272 f).
Proof. exact (MK_COMB (@lem51911 _5271 _5272) (@lem51910 _5264 _5271 _5272 f)). Qed.
Lemma lem51913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem51914 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term12 _5264 _5271 _5272 f) = (term13 _5264 _5271 _5272 f).
Proof. exact (MK_COMB (@lem51913) (@lem51912 _5264 _5271 _5272 f)). Qed.
Lemma lem51915 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (p1 : _5272) (p2 : _5271) : (term14 _5264 _5271 _5272 f p1 p2) = ((term15 _5264 _5271 _5272 f p1 p2) = (term16 _5264 _5271 _5272 f p1 p2)).
Proof. exact (eq_refl (term14 _5264 _5271 _5272 f p1 p2)). Qed.
Lemma lem51916 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (p1 : _5272) : (term17 _5264 _5271 _5272 f p1) = (term18 _5264 _5271 _5272 f p1).
Proof. exact (fun_ext (fun p2 : _5271 => @lem51915 _5264 _5271 _5272 f p1 p2)). Qed.
Lemma lem51917 {_5271 : Type'} : (@all _5271) = (@all _5271).
Proof. exact (eq_refl (@all _5271)). Qed.
Lemma lem51918 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (p1 : _5272) : (term19 _5264 _5271 _5272 f p1) = (term20 _5264 _5271 _5272 f p1).
Proof. exact (MK_COMB (@lem51917 _5271) (@lem51916 _5264 _5271 _5272 f p1)). Qed.
Lemma lem51919 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term21 _5264 _5271 _5272 f) = (term22 _5264 _5271 _5272 f).
Proof. exact (fun_ext (fun p1 : _5272 => @lem51918 _5264 _5271 _5272 f p1)). Qed.
Lemma lem51920 {_5272 : Type'} : (@all _5272) = (@all _5272).
Proof. exact (eq_refl (@all _5272)). Qed.
Lemma lem51921 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term7 _5264 _5271 _5272 f) = (term23 _5264 _5271 _5272 f).
Proof. exact (MK_COMB (@lem51920 _5272) (@lem51919 _5264 _5271 _5272 f)). Qed.
Lemma lem51922 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : ((term6 _5264 _5271 _5272 f) = (term7 _5264 _5271 _5272 f)) = ((term3 _5264 _5271 _5272 f) = (term23 _5264 _5271 _5272 f)).
Proof. exact (MK_COMB (@lem51914 _5264 _5271 _5272 f) (@lem51921 _5264 _5271 _5272 f)). Qed.
Lemma lem51923 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term3 _5264 _5271 _5272 f) = (term23 _5264 _5271 _5272 f).
Proof. exact (EQ_MP (@lem51922 _5264 _5271 _5272 f) (@lem51908 _5264 _5271 _5272 f)). Qed.
Lemma lem51930 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : ((term2 _5264 _5271 _5272 f) = f) = (term23 _5264 _5271 _5272 f).
Proof. exact (TRANS (@lem51900 _5264 _5271 _5272 f) (@lem51923 _5264 _5271 _5272 f)). Qed.
Lemma lem51941 {_5271 _5272 : Type'} (a0 : _5272) (a1 : _5271) : a0 = (term24 _5271 _5272 a0 a1).
Proof. exact (@lem51128 _5272 _5271 a0 a1). Qed.
Lemma lem51942 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : x = (term24 _5271 _5272 x y).
Proof. exact (@lem51941 _5271 _5272 x y). Qed.
Lemma lem51943 {_5271 _5272 : Type'} (a0 : _5272) (a1 : _5271) : a1 = (term25 _5271 _5272 a0 a1).
Proof. exact (@lem51159 _5272 _5271 a0 a1). Qed.
Lemma lem51944 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : y = (term25 _5271 _5272 x y).
Proof. exact (@lem51943 _5271 _5272 x y). Qed.
Lemma lem51945 {_5272 : Type'} (x : _5272) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem51946 {_5272 : Type'} : (term26 _5272) = (term26 _5272).
Proof. exact (eq_refl (term26 _5272)). Qed.
Lemma lem51947 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : (term27 _5272 x) = (term28 _5271 _5272 x y).
Proof. exact (MK_COMB (@lem51946 _5272) (@lem51942 _5271 _5272 x y)). Qed.
Lemma lem51948 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : (term28 _5271 _5272 x y) = (term24 _5271 _5272 x y).
Proof. exact (eq_refl (term28 _5271 _5272 x y)). Qed.
Lemma lem51949 {_5272 : Type'} (x : _5272) : (term29 _5272 x) = (term29 _5272 x).
Proof. exact (eq_refl (term29 _5272 x)). Qed.
Lemma lem51950 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : ((term27 _5272 x) = (term28 _5271 _5272 x y)) = ((term27 _5272 x) = (term24 _5271 _5272 x y)).
Proof. exact (MK_COMB (@lem51949 _5272 x) (@lem51948 _5271 _5272 x y)). Qed.
Lemma lem51951 {_5272 : Type'} (x : _5272) : (term27 _5272 x) = x.
Proof. exact (eq_refl (term27 _5272 x)). Qed.
Lemma lem51952 {_5272 : Type'} : (@eq _5272) = (@eq _5272).
Proof. exact (eq_refl (@eq _5272)). Qed.
Lemma lem51953 {_5272 : Type'} (x : _5272) : (term29 _5272 x) = (@eq _5272 x).
Proof. exact (MK_COMB (@lem51952 _5272) (@lem51951 _5272 x)). Qed.
Lemma lem51954 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : (term24 _5271 _5272 x y) = (term24 _5271 _5272 x y).
Proof. exact (eq_refl (term24 _5271 _5272 x y)). Qed.
Lemma lem51955 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : ((term27 _5272 x) = (term24 _5271 _5272 x y)) = (x = (term24 _5271 _5272 x y)).
Proof. exact (MK_COMB (@lem51953 _5272 x) (@lem51954 _5271 _5272 x y)). Qed.
Lemma lem51956 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : ((term27 _5272 x) = (term28 _5271 _5272 x y)) = (x = (term24 _5271 _5272 x y)).
Proof. exact (TRANS (@lem51950 _5271 _5272 x y) (@lem51955 _5271 _5272 x y)). Qed.
Lemma lem51957 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : x = (term24 _5271 _5272 x y).
Proof. exact (EQ_MP (@lem51956 _5271 _5272 x y) (@lem51947 _5271 _5272 x y)). Qed.
Lemma lem51958 {_5272 : Type'} (x : _5272) : (@eq _5272 x) = (@eq _5272 x).
Proof. exact (eq_refl (@eq _5272 x)). Qed.
Lemma lem51959 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : (x = x) = (x = (term24 _5271 _5272 x y)).
Proof. exact (MK_COMB (@lem51958 _5272 x) (@lem51957 _5271 _5272 x y)). Qed.
Lemma lem51960 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : x = (term24 _5271 _5272 x y).
Proof. exact (EQ_MP (@lem51959 _5271 _5272 x y) (@lem51945 _5272 x)). Qed.
Lemma lem51961 {_5271 : Type'} (y : _5271) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem51962 {_5271 : Type'} : (term26 _5271) = (term26 _5271).
Proof. exact (eq_refl (term26 _5271)). Qed.
Lemma lem51963 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : (term27 _5271 y) = (term30 _5271 _5272 x y).
Proof. exact (MK_COMB (@lem51962 _5271) (@lem51944 _5271 _5272 x y)). Qed.
Lemma lem51964 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : (term30 _5271 _5272 x y) = (term25 _5271 _5272 x y).
Proof. exact (eq_refl (term30 _5271 _5272 x y)). Qed.
Lemma lem51965 {_5271 : Type'} (y : _5271) : (term29 _5271 y) = (term29 _5271 y).
Proof. exact (eq_refl (term29 _5271 y)). Qed.
Lemma lem51966 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : ((term27 _5271 y) = (term30 _5271 _5272 x y)) = ((term27 _5271 y) = (term25 _5271 _5272 x y)).
Proof. exact (MK_COMB (@lem51965 _5271 y) (@lem51964 _5271 _5272 x y)). Qed.
Lemma lem51967 {_5271 : Type'} (y : _5271) : (term27 _5271 y) = y.
Proof. exact (eq_refl (term27 _5271 y)). Qed.
Lemma lem51968 {_5271 : Type'} : (@eq _5271) = (@eq _5271).
Proof. exact (eq_refl (@eq _5271)). Qed.
Lemma lem51969 {_5271 : Type'} (y : _5271) : (term29 _5271 y) = (@eq _5271 y).
Proof. exact (MK_COMB (@lem51968 _5271) (@lem51967 _5271 y)). Qed.
Lemma lem51970 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : (term25 _5271 _5272 x y) = (term25 _5271 _5272 x y).
Proof. exact (eq_refl (term25 _5271 _5272 x y)). Qed.
Lemma lem51971 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : ((term27 _5271 y) = (term25 _5271 _5272 x y)) = (y = (term25 _5271 _5272 x y)).
Proof. exact (MK_COMB (@lem51969 _5271 y) (@lem51970 _5271 _5272 x y)). Qed.
Lemma lem51972 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : ((term27 _5271 y) = (term30 _5271 _5272 x y)) = (y = (term25 _5271 _5272 x y)).
Proof. exact (TRANS (@lem51966 _5271 _5272 x y) (@lem51971 _5271 _5272 x y)). Qed.
Lemma lem51973 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : y = (term25 _5271 _5272 x y).
Proof. exact (EQ_MP (@lem51972 _5271 _5272 x y) (@lem51963 _5271 _5272 x y)). Qed.
Lemma lem51974 {_5271 : Type'} (y : _5271) : (@eq _5271 y) = (@eq _5271 y).
Proof. exact (eq_refl (@eq _5271 y)). Qed.
Lemma lem51975 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : (y = y) = (y = (term25 _5271 _5272 x y)).
Proof. exact (MK_COMB (@lem51974 _5271 y) (@lem51973 _5271 _5272 x y)). Qed.
Lemma lem51976 {_5271 _5272 : Type'} (x : _5272) (y : _5271) : y = (term25 _5271 _5272 x y).
Proof. exact (EQ_MP (@lem51975 _5271 _5272 x y) (@lem51961 _5271 y)). Qed.
Lemma lem51977 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term31 _5264 _5271 _5272 f) = (term31 _5264 _5271 _5272 f).
Proof. exact (eq_refl (term31 _5264 _5271 _5272 f)). Qed.
Lemma lem51978 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term32 _5264 _5271 _5272 f x) = (term33 _5264 _5271 _5272 f x y).
Proof. exact (MK_COMB (@lem51977 _5264 _5271 _5272 f) (@lem51960 _5271 _5272 x y)). Qed.
Lemma lem51979 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term33 _5264 _5271 _5272 f x y) = (term34 _5264 _5271 _5272 f x y).
Proof. exact (eq_refl (term33 _5264 _5271 _5272 f x y)). Qed.
Lemma lem51980 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) : (term35 _5264 _5271 _5272 f x) = (term35 _5264 _5271 _5272 f x).
Proof. exact (eq_refl (term35 _5264 _5271 _5272 f x)). Qed.
Lemma lem51981 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : ((term32 _5264 _5271 _5272 f x) = (term33 _5264 _5271 _5272 f x y)) = ((term32 _5264 _5271 _5272 f x) = (term34 _5264 _5271 _5272 f x y)).
Proof. exact (MK_COMB (@lem51980 _5264 _5271 _5272 f x) (@lem51979 _5264 _5271 _5272 f x y)). Qed.
Lemma lem51982 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) : (term32 _5264 _5271 _5272 f x) = (term36 _5264 _5271 _5272 f x).
Proof. exact (eq_refl (term32 _5264 _5271 _5272 f x)). Qed.
Lemma lem51983 {_5264 _5271 : Type'} : (@eq (_5271 -> _5264)) = (@eq (_5271 -> _5264)).
Proof. exact (eq_refl (@eq (_5271 -> _5264))). Qed.
Lemma lem51984 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) : (term35 _5264 _5271 _5272 f x) = (term37 _5264 _5271 _5272 f x).
Proof. exact (MK_COMB (@lem51983 _5264 _5271) (@lem51982 _5264 _5271 _5272 f x)). Qed.
Lemma lem51985 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term34 _5264 _5271 _5272 f x y) = (term34 _5264 _5271 _5272 f x y).
Proof. exact (eq_refl (term34 _5264 _5271 _5272 f x y)). Qed.
Lemma lem51986 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : ((term32 _5264 _5271 _5272 f x) = (term34 _5264 _5271 _5272 f x y)) = ((term36 _5264 _5271 _5272 f x) = (term34 _5264 _5271 _5272 f x y)).
Proof. exact (MK_COMB (@lem51984 _5264 _5271 _5272 f x) (@lem51985 _5264 _5271 _5272 f x y)). Qed.
Lemma lem51987 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : ((term32 _5264 _5271 _5272 f x) = (term33 _5264 _5271 _5272 f x y)) = ((term36 _5264 _5271 _5272 f x) = (term34 _5264 _5271 _5272 f x y)).
Proof. exact (TRANS (@lem51981 _5264 _5271 _5272 f x y) (@lem51986 _5264 _5271 _5272 f x y)). Qed.
Lemma lem51988 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term36 _5264 _5271 _5272 f x) = (term34 _5264 _5271 _5272 f x y).
Proof. exact (EQ_MP (@lem51987 _5264 _5271 _5272 f x y) (@lem51978 _5264 _5271 _5272 f x y)). Qed.
Lemma lem51989 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term38 _5264 _5271 _5272 f x y) = (term39 _5264 _5271 _5272 f x y).
Proof. exact (MK_COMB (@lem51988 _5264 _5271 _5272 f x y) (@lem51976 _5271 _5272 x y)). Qed.
Lemma lem51990 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term39 _5264 _5271 _5272 f x y) = (term40 _5264 _5271 _5272 f x y).
Proof. exact (eq_refl (term39 _5264 _5271 _5272 f x y)). Qed.
Lemma lem51991 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term41 _5264 _5271 _5272 f x y) = (term41 _5264 _5271 _5272 f x y).
Proof. exact (eq_refl (term41 _5264 _5271 _5272 f x y)). Qed.
Lemma lem51992 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : ((term38 _5264 _5271 _5272 f x y) = (term39 _5264 _5271 _5272 f x y)) = ((term38 _5264 _5271 _5272 f x y) = (term40 _5264 _5271 _5272 f x y)).
Proof. exact (MK_COMB (@lem51991 _5264 _5271 _5272 f x y) (@lem51990 _5264 _5271 _5272 f x y)). Qed.
Lemma lem51993 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term38 _5264 _5271 _5272 f x y) = (term16 _5264 _5271 _5272 f x y).
Proof. exact (eq_refl (term38 _5264 _5271 _5272 f x y)). Qed.
Lemma lem51994 {_5264 : Type'} : (@eq _5264) = (@eq _5264).
Proof. exact (eq_refl (@eq _5264)). Qed.
Lemma lem51995 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term41 _5264 _5271 _5272 f x y) = (term42 _5264 _5271 _5272 f x y).
Proof. exact (MK_COMB (@lem51994 _5264) (@lem51993 _5264 _5271 _5272 f x y)). Qed.
Lemma lem51996 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term40 _5264 _5271 _5272 f x y) = (term40 _5264 _5271 _5272 f x y).
Proof. exact (eq_refl (term40 _5264 _5271 _5272 f x y)). Qed.
Lemma lem51997 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : ((term38 _5264 _5271 _5272 f x y) = (term40 _5264 _5271 _5272 f x y)) = ((term16 _5264 _5271 _5272 f x y) = (term40 _5264 _5271 _5272 f x y)).
Proof. exact (MK_COMB (@lem51995 _5264 _5271 _5272 f x y) (@lem51996 _5264 _5271 _5272 f x y)). Qed.
Lemma lem51998 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : ((term38 _5264 _5271 _5272 f x y) = (term39 _5264 _5271 _5272 f x y)) = ((term16 _5264 _5271 _5272 f x y) = (term40 _5264 _5271 _5272 f x y)).
Proof. exact (TRANS (@lem51992 _5264 _5271 _5272 f x y) (@lem51997 _5264 _5271 _5272 f x y)). Qed.
Lemma lem51999 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term16 _5264 _5271 _5272 f x y) = (term40 _5264 _5271 _5272 f x y).
Proof. exact (EQ_MP (@lem51998 _5264 _5271 _5272 f x y) (@lem51989 _5264 _5271 _5272 f x y)). Qed.
Lemma lem52000 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term40 _5264 _5271 _5272 f x y) = (term16 _5264 _5271 _5272 f x y).
Proof. exact (SYM (@lem51999 _5264 _5271 _5272 f x y)). Qed.
Lemma lem52001 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term43 _5264 _5271 _5272 f x y) = (term40 _5264 _5271 _5272 f x y).
Proof. exact (eq_refl (term43 _5264 _5271 _5272 f x y)). Qed.
Lemma lem52002 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term43 _5264 _5271 _5272 f x y) = (term16 _5264 _5271 _5272 f x y).
Proof. exact (TRANS (@lem52001 _5264 _5271 _5272 f x y) (@lem52000 _5264 _5271 _5272 f x y)). Qed.
Lemma lem52003 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) : term44 _5264 _5271 _5272 f x.
Proof. exact (fun y : _5271 => @lem52002 _5264 _5271 _5272 f x y). Qed.
Lemma lem52004 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : term45 _5264 _5271 _5272 f.
Proof. exact (fun x : _5272 => @lem52003 _5264 _5271 _5272 f x). Qed.
Lemma lem52005 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : term46 _5264 _5271 _5272 f.
Proof. exact (ex_intro (term47 _5264 _5271 _5272 f) (term48 _5264 _5271 _5272 f) (@lem52004 _5264 _5271 _5272 f)). Qed.
Lemma lem52007 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem52008 {_5264 : Type'} (a : _5264) (b : _5264) : (a = b) = (@GEQ _5264 a b).
Proof. exact (@lem52007 _5264 a b). Qed.
Lemma lem52009 {_5264 _5271 _5272 : Type'} (_1438 : type1228 _5264 _5271 _5272) (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : ((term16 _5264 _5271 _5272 _1438 x y) = (term16 _5264 _5271 _5272 f x y)) = (term49 _5264 _5271 _5272 _1438 f x y).
Proof. exact (@lem52008 _5264 (term16 _5264 _5271 _5272 _1438 x y) (term16 _5264 _5271 _5272 f x y)). Qed.
Lemma lem52010 {_5264 _5271 _5272 : Type'} (_1438 : type1228 _5264 _5271 _5272) (f : type1228 _5264 _5271 _5272) (x : _5272) : (term50 _5264 _5271 _5272 _1438 f x) = (term51 _5264 _5271 _5272 _1438 f x).
Proof. exact (fun_ext (fun y : _5271 => @lem52009 _5264 _5271 _5272 _1438 f x y)). Qed.
Lemma lem52011 {_5271 : Type'} : (@all _5271) = (@all _5271).
Proof. exact (eq_refl (@all _5271)). Qed.
Lemma lem52012 {_5264 _5271 _5272 : Type'} (_1438 : type1228 _5264 _5271 _5272) (f : type1228 _5264 _5271 _5272) (x : _5272) : (term52 _5264 _5271 _5272 _1438 f x) = (term53 _5264 _5271 _5272 _1438 f x).
Proof. exact (MK_COMB (@lem52011 _5271) (@lem52010 _5264 _5271 _5272 _1438 f x)). Qed.
Lemma lem52013 {_5264 _5271 _5272 : Type'} (_1438 : type1228 _5264 _5271 _5272) (f : type1228 _5264 _5271 _5272) : (term54 _5264 _5271 _5272 _1438 f) = (term55 _5264 _5271 _5272 _1438 f).
Proof. exact (fun_ext (fun x : _5272 => @lem52012 _5264 _5271 _5272 _1438 f x)). Qed.
Lemma lem52014 {_5272 : Type'} : (@all _5272) = (@all _5272).
Proof. exact (eq_refl (@all _5272)). Qed.
Lemma lem52015 {_5264 _5271 _5272 : Type'} (_1438 : type1228 _5264 _5271 _5272) (f : type1228 _5264 _5271 _5272) : (term56 _5264 _5271 _5272 _1438 f) = (term57 _5264 _5271 _5272 _1438 f).
Proof. exact (MK_COMB (@lem52014 _5272) (@lem52013 _5264 _5271 _5272 _1438 f)). Qed.
Lemma lem52016 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term47 _5264 _5271 _5272 f) = (term58 _5264 _5271 _5272 f).
Proof. exact (fun_ext (fun _1438 : type1228 _5264 _5271 _5272 => @lem52015 _5264 _5271 _5272 _1438 f)). Qed.
Lemma lem52017 {_5264 _5271 _5272 : Type'} : (@ex ((prod _5272 _5271) -> _5264)) = (@ex ((prod _5272 _5271) -> _5264)).
Proof. exact (eq_refl (@ex ((prod _5272 _5271) -> _5264))). Qed.
Lemma lem52018 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term46 _5264 _5271 _5272 f) = (term59 _5264 _5271 _5272 f).
Proof. exact (MK_COMB (@lem52017 _5264 _5271 _5272) (@lem52016 _5264 _5271 _5272 f)). Qed.
Lemma lem52019 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : term59 _5264 _5271 _5272 f.
Proof. exact (EQ_MP (@lem52018 _5264 _5271 _5272 f) (@lem52005 _5264 _5271 _5272 f)). Qed.
Lemma lem52021 {_5076 : Type'} (P : _5076 -> Prop) : term60 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem52022 {_5264 _5271 _5272 : Type'} (P : type333 _5264 _5271 _5272) : term61 _5264 _5271 _5272 P.
Proof. exact (@lem52021 (type1228 _5264 _5271 _5272) P). Qed.
Lemma lem52023 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : term62 _5264 _5271 _5272 f.
Proof. exact (@lem52022 _5264 _5271 _5272 (term58 _5264 _5271 _5272 f)). Qed.
Lemma lem52024 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : term63 _5264 _5271 _5272 f.
Proof. exact (@lem52023 _5264 _5271 _5272 f (@lem52019 _5264 _5271 _5272 f)). Qed.
Lemma lem52025 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term63 _5264 _5271 _5272 f) = (term64 _5264 _5271 _5272 f).
Proof. exact (eq_refl (term63 _5264 _5271 _5272 f)). Qed.
Lemma lem52026 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : term64 _5264 _5271 _5272 f.
Proof. exact (EQ_MP (@lem52025 _5264 _5271 _5272 f) (@lem52024 _5264 _5271 _5272 f)). Qed.
Lemma lem52027 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) : term65 _5264 _5271 _5272 f x.
Proof. exact (@lem52026 _5264 _5271 _5272 f x). Qed.
Lemma lem52028 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) : (term65 _5264 _5271 _5272 f x) = (term66 _5264 _5271 _5272 f x).
Proof. exact (eq_refl (term65 _5264 _5271 _5272 f x)). Qed.
Lemma lem52029 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) : term66 _5264 _5271 _5272 f x.
Proof. exact (EQ_MP (@lem52028 _5264 _5271 _5272 f x) (@lem52027 _5264 _5271 _5272 f x)). Qed.
Lemma lem52030 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : term67 _5264 _5271 _5272 f x y.
Proof. exact (@lem52029 _5264 _5271 _5272 f x y). Qed.
Lemma lem52031 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term67 _5264 _5271 _5272 f x y) = (term68 _5264 _5271 _5272 f x y).
Proof. exact (eq_refl (term67 _5264 _5271 _5272 f x y)). Qed.
Lemma lem52032 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : term68 _5264 _5271 _5272 f x y.
Proof. exact (EQ_MP (@lem52031 _5264 _5271 _5272 f x y) (@lem52030 _5264 _5271 _5272 f x y)). Qed.
Lemma lem52034 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem52035 {_5264 : Type'} (a : _5264) (b : _5264) : (@GEQ _5264 a b) = (a = b).
Proof. exact (@lem52034 _5264 a b). Qed.
Lemma lem52036 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term68 _5264 _5271 _5272 f x y) = ((term15 _5264 _5271 _5272 f x y) = (term16 _5264 _5271 _5272 f x y)).
Proof. exact (@lem52035 _5264 (term15 _5264 _5271 _5272 f x y) (term16 _5264 _5271 _5272 f x y)). Qed.
Lemma lem52037 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term15 _5264 _5271 _5272 f x y) = (term16 _5264 _5271 _5272 f x y).
Proof. exact (EQ_MP (@lem52036 _5264 _5271 _5272 f x y) (@lem52032 _5264 _5271 _5272 f x y)). Qed.
Lemma lem52038 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (x : _5272) (y : _5271) : (term15 _5264 _5271 _5272 f x y) = (term16 _5264 _5271 _5272 f x y).
Proof. exact (@lem52037 _5264 _5271 _5272 f x y). Qed.
Lemma lem52039 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (p1 : _5272) (p2 : _5271) : (term15 _5264 _5271 _5272 f p1 p2) = (term16 _5264 _5271 _5272 f p1 p2).
Proof. exact (@lem52038 _5264 _5271 _5272 f p1 p2). Qed.
Lemma lem52040 {_5264 : Type'} : (@eq _5264) = (@eq _5264).
Proof. exact (eq_refl (@eq _5264)). Qed.
Lemma lem52041 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (p1 : _5272) (p2 : _5271) : (term69 _5264 _5271 _5272 f p1 p2) = (term42 _5264 _5271 _5272 f p1 p2).
Proof. exact (MK_COMB (@lem52040 _5264) (@lem52039 _5264 _5271 _5272 f p1 p2)). Qed.
Lemma lem52042 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (p1 : _5272) (p2 : _5271) : (term16 _5264 _5271 _5272 f p1 p2) = (term16 _5264 _5271 _5272 f p1 p2).
Proof. exact (eq_refl (term16 _5264 _5271 _5272 f p1 p2)). Qed.
Lemma lem52043 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (p1 : _5272) (p2 : _5271) : ((term15 _5264 _5271 _5272 f p1 p2) = (term16 _5264 _5271 _5272 f p1 p2)) = ((term16 _5264 _5271 _5272 f p1 p2) = (term16 _5264 _5271 _5272 f p1 p2)).
Proof. exact (MK_COMB (@lem52041 _5264 _5271 _5272 f p1 p2) (@lem52042 _5264 _5271 _5272 f p1 p2)). Qed.
Lemma lem52045 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem52046 {_5264 : Type'} (x : _5264) : (x = x) = True.
Proof. exact (@lem52045 _5264 x). Qed.
Lemma lem52047 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (p1 : _5272) (p2 : _5271) : ((term16 _5264 _5271 _5272 f p1 p2) = (term16 _5264 _5271 _5272 f p1 p2)) = True.
Proof. exact (@lem52046 _5264 (term16 _5264 _5271 _5272 f p1 p2)). Qed.
Lemma lem52048 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (p1 : _5272) (p2 : _5271) : ((term15 _5264 _5271 _5272 f p1 p2) = (term16 _5264 _5271 _5272 f p1 p2)) = True.
Proof. exact (TRANS (@lem52043 _5264 _5271 _5272 f p1 p2) (@lem52047 _5264 _5271 _5272 f p1 p2)). Qed.
Lemma lem52049 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (p1 : _5272) : (term18 _5264 _5271 _5272 f p1) = (term70 _5271).
Proof. exact (fun_ext (fun p2 : _5271 => @lem52048 _5264 _5271 _5272 f p1 p2)). Qed.
Lemma lem52050 {_5271 : Type'} : (@all _5271) = (@all _5271).
Proof. exact (eq_refl (@all _5271)). Qed.
Lemma lem52051 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (p1 : _5272) : (term20 _5264 _5271 _5272 f p1) = (term71 _5271).
Proof. exact (MK_COMB (@lem52050 _5271) (@lem52049 _5264 _5271 _5272 f p1)). Qed.
Lemma lem52053 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem52054 {_5271 : Type'} (t : Prop) : (term72 _5271 t) = t.
Proof. exact (@lem52053 _5271 t). Qed.
Lemma lem52055 {_5271 : Type'} : (term71 _5271) = True.
Proof. exact (@lem52054 _5271 True). Qed.
Lemma lem52056 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) (p1 : _5272) : (term20 _5264 _5271 _5272 f p1) = True.
Proof. exact (TRANS (@lem52051 _5264 _5271 _5272 f p1) (@lem52055 _5271)). Qed.
Lemma lem52057 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term22 _5264 _5271 _5272 f) = (term70 _5272).
Proof. exact (fun_ext (fun p1 : _5272 => @lem52056 _5264 _5271 _5272 f p1)). Qed.
Lemma lem52058 {_5272 : Type'} : (@all _5272) = (@all _5272).
Proof. exact (eq_refl (@all _5272)). Qed.
Lemma lem52059 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term23 _5264 _5271 _5272 f) = (term71 _5272).
Proof. exact (MK_COMB (@lem52058 _5272) (@lem52057 _5264 _5271 _5272 f)). Qed.
Lemma lem52061 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem52062 {_5272 : Type'} (t : Prop) : (term72 _5272 t) = t.
Proof. exact (@lem52061 _5272 t). Qed.
Lemma lem52063 {_5272 : Type'} : (term71 _5272) = True.
Proof. exact (@lem52062 _5272 True). Qed.
Lemma lem52064 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term23 _5264 _5271 _5272 f) = True.
Proof. exact (TRANS (@lem52059 _5264 _5271 _5272 f) (@lem52063 _5272)). Qed.
Lemma lem52065 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : ((term2 _5264 _5271 _5272 f) = f) = True.
Proof. exact (TRANS (@lem51930 _5264 _5271 _5272 f) (@lem52064 _5264 _5271 _5272 f)). Qed.
Lemma lem52066 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : True = ((term2 _5264 _5271 _5272 f) = f).
Proof. exact (SYM (@lem52065 _5264 _5271 _5272 f)). Qed.
Lemma lem52067 {_5264 _5271 _5272 : Type'} (f : type1228 _5264 _5271 _5272) : (term2 _5264 _5271 _5272 f) = f.
Proof. exact (EQ_MP (@lem52066 _5264 _5271 _5272 f) (@lem0)). Qed.
