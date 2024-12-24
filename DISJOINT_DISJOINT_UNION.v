Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJOINT_DISJOINT_UNION_term_abbrevs.
Require Import DISJOINT_spec.
Require Import DISJOINT_UNION_EQ_EMPTY_spec.
Require Import INTER_DISJOINT_UNION_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4491920 {A K : Type'} (k : K -> Prop) : term0 A K k.
Proof. exact (@lem4491919 A K k). Qed.
Lemma lem4491921 {A K : Type'} (k : K -> Prop) : (term0 A K k) = (term1 A K k).
Proof. exact (eq_refl (term0 A K k)). Qed.
Lemma lem4491922 {A K : Type'} (k : K -> Prop) : term1 A K k.
Proof. exact (EQ_MP (@lem4491921 A K k) (@lem4491920 A K k)). Qed.
Lemma lem4491923 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term2 A K k s.
Proof. exact (@lem4491922 A K k s). Qed.
Lemma lem4491924 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term2 A K k s) = (((@disjoint_union A K k s) = (@EMPTY (prod K A))) = (term3 A K k s)).
Proof. exact (eq_refl (term2 A K k s)). Qed.
Lemma lem4491926 {A K : Type'} (k : K -> Prop) : term4 A K k.
Proof. exact (@lem4482970 A K k). Qed.
Lemma lem4491927 {A K : Type'} (k : K -> Prop) : (term4 A K k) = (term5 A K k).
Proof. exact (eq_refl (term4 A K k)). Qed.
Lemma lem4491928 {A K : Type'} (k : K -> Prop) : term5 A K k.
Proof. exact (EQ_MP (@lem4491927 A K k) (@lem4491926 A K k)). Qed.
Lemma lem4491929 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term6 A K k s.
Proof. exact (@lem4491928 A K k s). Qed.
Lemma lem4491930 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term6 A K k s) = (term7 A K k s).
Proof. exact (eq_refl (term6 A K k s)). Qed.
Lemma lem4491931 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term7 A K k s.
Proof. exact (EQ_MP (@lem4491930 A K k s) (@lem4491929 A K k s)). Qed.
Lemma lem4491932 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term8 A K k s t.
Proof. exact (@lem4491931 A K k s t). Qed.
Lemma lem4491933 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term8 A K k s t) = ((term9 A K s k t) = (term10 A K k s t)).
Proof. exact (eq_refl (term8 A K k s t)). Qed.
Lemma lem4491935 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (@lem3196110 A s). Qed.
Lemma lem4491936 {A : Type'} (s : A -> Prop) : (term11 A s) = (term12 A s).
Proof. exact (eq_refl (term11 A s)). Qed.
Lemma lem4491937 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (EQ_MP (@lem4491936 A s) (@lem4491935 A s)). Qed.
Lemma lem4491938 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term13 A s t.
Proof. exact (@lem4491937 A s t). Qed.
Lemma lem4491939 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term13 A s t) = ((@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A))).
Proof. exact (eq_refl (term13 A s t)). Qed.
Lemma lem4491944 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem4491939 A s t) (@lem4491938 A s t)). Qed.
Lemma lem4491945 {A K : Type'} (s : type1223 A K) (t : type1223 A K) : (@DISJOINT (prod K A) s t) = ((@INTER (prod K A) s t) = (@EMPTY (prod K A))).
Proof. exact (@lem4491944 (prod K A) s t). Qed.
Lemma lem4491946 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term14 A K s k t) = ((term9 A K s k t) = (@EMPTY (prod K A))).
Proof. exact (@lem4491945 A K (@disjoint_union A K k s) (@disjoint_union A K k t)). Qed.
Lemma lem4491950 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term9 A K s k t) = (term10 A K k s t).
Proof. exact (EQ_MP (@lem4491933 A K k s t) (@lem4491932 A K k s t)). Qed.
Lemma lem4491951 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term9 A K s k t) = (term10 A K k s t).
Proof. exact (@lem4491950 A K k s t). Qed.
Lemma lem4491952 {A K : Type'} : (@eq ((prod K A) -> Prop)) = (@eq ((prod K A) -> Prop)).
Proof. exact (eq_refl (@eq ((prod K A) -> Prop))). Qed.
Lemma lem4491953 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term15 A K s k t) = (term16 A K k s t).
Proof. exact (MK_COMB (@lem4491952 A K) (@lem4491951 A K k s t)). Qed.
Lemma lem4491954 {A K : Type'} : (@EMPTY (prod K A)) = (@EMPTY (prod K A)).
Proof. exact (eq_refl (@EMPTY (prod K A))). Qed.
Lemma lem4491955 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term9 A K s k t) = (@EMPTY (prod K A))) = ((term10 A K k s t) = (@EMPTY (prod K A))).
Proof. exact (MK_COMB (@lem4491953 A K k s t) (@lem4491954 A K)). Qed.
Lemma lem4491957 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@disjoint_union A K k s) = (@EMPTY (prod K A))) = (term3 A K k s).
Proof. exact (EQ_MP (@lem4491924 A K k s) (@lem4491923 A K k s)). Qed.
Lemma lem4491958 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@disjoint_union A K k s) = (@EMPTY (prod K A))) = (term3 A K k s).
Proof. exact (@lem4491957 A K k s). Qed.
Lemma lem4491959 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term10 A K k s t) = (@EMPTY (prod K A))) = (term17 A K k s t).
Proof. exact (@lem4491958 A K k (term18 A K s t)). Qed.
Lemma lem4491969 {A B : Type'} (f : A -> B) (y : A) : (term19 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4491970 {A K : Type'} (f : type1470 A K) (y : K) : (term20 A K f y) = (f y).
Proof. exact (@lem4491969 K (A -> Prop) f y). Qed.
Lemma lem4491971 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term21 A K s t i) = (term22 A K s t i).
Proof. exact (@lem4491970 A K (term18 A K s t) i). Qed.
Lemma lem4491972 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term22 A K s t i) = (term23 A K s t i).
Proof. exact (eq_refl (term22 A K s t i)). Qed.
Lemma lem4491973 {A K : Type'} (s : type1470 A K) (t : type1470 A K) : (term24 A K s t) = (term18 A K s t).
Proof. exact (fun_ext (fun i : K => @lem4491972 A K s t i)). Qed.
Lemma lem4491974 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4491975 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term21 A K s t i) = (term22 A K s t i).
Proof. exact (MK_COMB (@lem4491973 A K s t) (@lem4491974 K i)). Qed.
Lemma lem4491976 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4491977 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term25 A K s t i) = (term26 A K s t i).
Proof. exact (MK_COMB (@lem4491976 A) (@lem4491975 A K s t i)). Qed.
Lemma lem4491978 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term22 A K s t i) = (term23 A K s t i).
Proof. exact (eq_refl (term22 A K s t i)). Qed.
Lemma lem4491979 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : ((term21 A K s t i) = (term22 A K s t i)) = ((term22 A K s t i) = (term23 A K s t i)).
Proof. exact (MK_COMB (@lem4491977 A K s t i) (@lem4491978 A K s t i)). Qed.
Lemma lem4491980 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term22 A K s t i) = (term23 A K s t i).
Proof. exact (EQ_MP (@lem4491979 A K s t i) (@lem4491971 A K s t i)). Qed.
Lemma lem4491981 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4491982 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term26 A K s t i) = (term27 A K s t i).
Proof. exact (MK_COMB (@lem4491981 A) (@lem4491980 A K s t i)). Qed.
Lemma lem4491983 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4491984 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : ((term22 A K s t i) = (@EMPTY A)) = ((term23 A K s t i) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem4491982 A K s t i) (@lem4491983 A)). Qed.
Lemma lem4491987 {K : Type'} (i : K) (k : K -> Prop) : (term28 K i k) = (term28 K i k).
Proof. exact (eq_refl (term28 K i k)). Qed.
Lemma lem4491988 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term29 A K k s t i) = (term30 A K k s t i).
Proof. exact (MK_COMB (@lem4491987 K i k) (@lem4491984 A K s t i)). Qed.
Lemma lem4491991 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term31 A K k s t) = (term32 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4491988 A K k s t i)). Qed.
Lemma lem4491992 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4491993 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term17 A K k s t) = (term33 A K k s t).
Proof. exact (MK_COMB (@lem4491992 K) (@lem4491991 A K k s t)). Qed.
Lemma lem4491998 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term10 A K k s t) = (@EMPTY (prod K A))) = (term33 A K k s t).
Proof. exact (TRANS (@lem4491959 A K k s t) (@lem4491993 A K k s t)). Qed.
Lemma lem4491999 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term9 A K s k t) = (@EMPTY (prod K A))) = (term33 A K k s t).
Proof. exact (TRANS (@lem4491955 A K k s t) (@lem4491998 A K k s t)). Qed.
Lemma lem4492000 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term14 A K s k t) = (term33 A K k s t).
Proof. exact (TRANS (@lem4491946 A K s k t) (@lem4491999 A K k s t)). Qed.
Lemma lem4492001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4492002 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term34 A K s k t) = (term35 A K k s t).
Proof. exact (MK_COMB (@lem4492001) (@lem4492000 A K k s t)). Qed.
Lemma lem4492010 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem4491939 A s t) (@lem4491938 A s t)). Qed.
Lemma lem4492011 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem4492010 A s t). Qed.
Lemma lem4492012 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term36 A K s t i) = ((term23 A K s t i) = (@EMPTY A)).
Proof. exact (@lem4492011 A (s i) (t i)). Qed.
Lemma lem4492015 {K : Type'} (i : K) (k : K -> Prop) : (term28 K i k) = (term28 K i k).
Proof. exact (eq_refl (term28 K i k)). Qed.
Lemma lem4492016 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term37 A K k s t i) = (term30 A K k s t i).
Proof. exact (MK_COMB (@lem4492015 K i k) (@lem4492012 A K s t i)). Qed.
Lemma lem4492019 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term38 A K k s t) = (term32 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4492016 A K k s t i)). Qed.
Lemma lem4492020 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4492021 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term39 A K k s t) = (term33 A K k s t).
Proof. exact (MK_COMB (@lem4492020 K) (@lem4492019 A K k s t)). Qed.
Lemma lem4492026 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term14 A K s k t) = (term39 A K k s t)) = ((term33 A K k s t) = (term33 A K k s t)).
Proof. exact (MK_COMB (@lem4492002 A K k s t) (@lem4492021 A K k s t)). Qed.
Lemma lem4492028 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4492029 (x : Prop) : (x = x) = True.
Proof. exact (@lem4492028 Prop x). Qed.
Lemma lem4492030 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term33 A K k s t) = (term33 A K k s t)) = True.
Proof. exact (@lem4492029 (term33 A K k s t)). Qed.
Lemma lem4492031 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term14 A K s k t) = (term39 A K k s t)) = True.
Proof. exact (TRANS (@lem4492026 A K k s t) (@lem4492030 A K k s t)). Qed.
Lemma lem4492032 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : True = ((term14 A K s k t) = (term39 A K k s t)).
Proof. exact (SYM (@lem4492031 A K k s t)). Qed.
Lemma lem4492033 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term14 A K s k t) = (term39 A K k s t).
Proof. exact (EQ_MP (@lem4492032 A K k s t) (@lem0)). Qed.
Lemma lem4492038 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term40 A K k s.
Proof. exact (fun t : type1470 A K => @lem4492033 A K k s t). Qed.
Lemma lem4492043 {A K : Type'} (k : K -> Prop) : term41 A K k.
Proof. exact (fun s : type1470 A K => @lem4492038 A K k s). Qed.
Lemma lem4492048 {A K : Type'} : term42 A K.
Proof. exact (fun k : K -> Prop => @lem4492043 A K k). Qed.
