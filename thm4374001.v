Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4374001_term_abbrevs.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Lemma lem4373823 {_103718 _103721 : Type'} (x : _103718) : term0 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4373824 {_103718 _103721 : Type'} (x : _103718) : (term0 _103718 _103721 x) = (term1 _103718 _103721 x).
Proof. exact (eq_refl (term0 _103718 _103721 x)). Qed.
Lemma lem4373825 {_103718 _103721 : Type'} (x : _103718) : term1 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4373824 _103718 _103721 x) (@lem4373823 _103718 _103721 x)). Qed.
Lemma lem4373826 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term2 _103718 _103721 x y.
Proof. exact (@lem4373825 _103718 _103721 x y). Qed.
Lemma lem4373827 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term2 _103718 _103721 x y) = (term3 _103718 _103721 x y).
Proof. exact (eq_refl (term2 _103718 _103721 x y)). Qed.
Lemma lem4373828 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term3 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4373827 _103718 _103721 x y) (@lem4373826 _103718 _103721 x y)). Qed.
Lemma lem4373829 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term4 _103718 _103721 x y s.
Proof. exact (@lem4373828 _103718 _103721 x y s). Qed.
Lemma lem4373830 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term4 _103718 _103721 x y s) = (term5 _103718 _103721 x s y).
Proof. exact (eq_refl (term4 _103718 _103721 x y s)). Qed.
Lemma lem4373831 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term5 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4373830 _103718 _103721 x s y) (@lem4373829 _103718 _103721 x y s)). Qed.
Lemma lem4373832 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term6 _103718 _103721 x s y t.
Proof. exact (@lem4373831 _103718 _103721 x s y t). Qed.
Lemma lem4373833 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term6 _103718 _103721 x s y t) = ((term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term6 _103718 _103721 x s y t)). Qed.
Lemma lem4373873 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term9 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4373874 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term9 _5106 _5107 P) = ((term10 _5106 _5107 P) = (term11 _5106 _5107 P)).
Proof. exact (eq_refl (term9 _5106 _5107 P)). Qed.
Lemma lem4373876 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4373877 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem4373878 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (EQ_MP (@lem4373877 A s) (@lem4373876 A s)). Qed.
Lemma lem4373879 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term14 A s t.
Proof. exact (@lem4373878 A s t). Qed.
Lemma lem4373880 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term14 A s t) = ((s = t) = (term15 A s t)).
Proof. exact (eq_refl (term14 A s t)). Qed.
Lemma lem4373907 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term15 A s t).
Proof. exact (EQ_MP (@lem4373880 A s t) (@lem4373879 A s t)). Qed.
Lemma lem4373908 {_105011 _105012 : Type'} (s : type1210 _105011 _105012) (t : type1210 _105011 _105012) : (s = t) = (term16 _105011 _105012 s t).
Proof. exact (@lem4373907 (prod _105011 _105012) s t). Qed.
Lemma lem4373909 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : ((term17 _105011 _105012 f t) = (@CROSS _105012 _105011 (@UNIV _105011) t)) = (term18 _105011 _105012 f t).
Proof. exact (@lem4373908 _105011 _105012 (term17 _105011 _105012 f t) (@CROSS _105012 _105011 (@UNIV _105011) t)). Qed.
Lemma lem4373915 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term10 _5106 _5107 P) = (term11 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4373874 _5106 _5107 P) (@lem4373873 _5106 _5107 P)). Qed.
Lemma lem4373916 {_105011 _105012 : Type'} (P : type1210 _105011 _105012) : (term19 _105011 _105012 P) = (term20 _105011 _105012 P).
Proof. exact (@lem4373915 _105012 _105011 P). Qed.
Lemma lem4373917 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term21 _105011 _105012 f t) = (term22 _105011 _105012 f t).
Proof. exact (@lem4373916 _105011 _105012 (term23 _105011 _105012 f t)). Qed.
Lemma lem4373918 {_105011 _105012 : Type'} (f : type686 _105011) (x : prod _105011 _105012) (t : _105012 -> Prop) : (term24 _105011 _105012 f t x) = ((term25 _105011 _105012 x f t) = (term26 _105011 _105012 x t)).
Proof. exact (eq_refl (term24 _105011 _105012 f t x)). Qed.
Lemma lem4373919 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term27 _105011 _105012 f t) = (term23 _105011 _105012 f t).
Proof. exact (fun_ext (fun x : prod _105011 _105012 => @lem4373918 _105011 _105012 f x t)). Qed.
Lemma lem4373920 {_105011 _105012 : Type'} : (@all (prod _105011 _105012)) = (@all (prod _105011 _105012)).
Proof. exact (eq_refl (@all (prod _105011 _105012))). Qed.
Lemma lem4373921 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term21 _105011 _105012 f t) = (term18 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4373920 _105011 _105012) (@lem4373919 _105011 _105012 f t)). Qed.
Lemma lem4373922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4373923 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term28 _105011 _105012 f t) = (term29 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4373922) (@lem4373921 _105011 _105012 f t)). Qed.
Lemma lem4373924 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) : (term30 _105011 _105012 f t p1 p2) = ((term31 _105011 _105012 p1 p2 f t) = (term32 _105011 _105012 p1 p2 t)).
Proof. exact (eq_refl (term30 _105011 _105012 f t p1 p2)). Qed.
Lemma lem4373925 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) : (term33 _105011 _105012 f t p1) = (term34 _105011 _105012 f p1 t).
Proof. exact (fun_ext (fun p2 : _105012 => @lem4373924 _105011 _105012 f p1 p2 t)). Qed.
Lemma lem4373926 {_105012 : Type'} : (@all _105012) = (@all _105012).
Proof. exact (eq_refl (@all _105012)). Qed.
Lemma lem4373927 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) : (term35 _105011 _105012 f t p1) = (term36 _105011 _105012 f p1 t).
Proof. exact (MK_COMB (@lem4373926 _105012) (@lem4373925 _105011 _105012 f p1 t)). Qed.
Lemma lem4373928 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term37 _105011 _105012 f t) = (term38 _105011 _105012 f t).
Proof. exact (fun_ext (fun p1 : _105011 => @lem4373927 _105011 _105012 f p1 t)). Qed.
Lemma lem4373929 {_105011 : Type'} : (@all _105011) = (@all _105011).
Proof. exact (eq_refl (@all _105011)). Qed.
Lemma lem4373930 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term22 _105011 _105012 f t) = (term39 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4373929 _105011) (@lem4373928 _105011 _105012 f t)). Qed.
Lemma lem4373931 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : ((term21 _105011 _105012 f t) = (term22 _105011 _105012 f t)) = ((term18 _105011 _105012 f t) = (term39 _105011 _105012 f t)).
Proof. exact (MK_COMB (@lem4373923 _105011 _105012 f t) (@lem4373930 _105011 _105012 f t)). Qed.
Lemma lem4373932 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term18 _105011 _105012 f t) = (term39 _105011 _105012 f t).
Proof. exact (EQ_MP (@lem4373931 _105011 _105012 f t) (@lem4373917 _105011 _105012 f t)). Qed.
Lemma lem4373939 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : ((term17 _105011 _105012 f t) = (@CROSS _105012 _105011 (@UNIV _105011) t)) = (term39 _105011 _105012 f t).
Proof. exact (TRANS (@lem4373909 _105011 _105012 f t) (@lem4373932 _105011 _105012 f t)). Qed.
Lemma lem4373951 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4373833 _103718 _103721 x s y t) (@lem4373832 _103718 _103721 x s y t)). Qed.
Lemma lem4373952 {_105011 _105012 : Type'} (x : _105011) (s : _105011 -> Prop) (y : _105012) (t : _105012 -> Prop) : (term7 _105011 _105012 x y s t) = (term8 _105011 _105012 x s y t).
Proof. exact (@lem4373951 _105011 _105012 x s y t). Qed.
Lemma lem4373953 {_105011 _105012 : Type'} (p1 : _105011) (f : type686 _105011) (p2 : _105012) (t : _105012 -> Prop) : (term31 _105011 _105012 p1 p2 f t) = (term40 _105011 _105012 p1 f p2 t).
Proof. exact (@lem4373952 _105011 _105012 p1 (@INTERS _105011 f) p2 t). Qed.
Lemma lem4373957 {_105011 : Type'} (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : f = (@EMPTY (_105011 -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4373958 {_105011 : Type'} : (@INTERS _105011) = (@INTERS _105011).
Proof. exact (eq_refl (@INTERS _105011)). Qed.
Lemma lem4373959 {_105011 : Type'} (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : (@INTERS _105011 f) = (@INTERS _105011 (@EMPTY (_105011 -> Prop))).
Proof. exact (MK_COMB (@lem4373958 _105011) (@lem4373957 _105011 f h1)). Qed.
Lemma lem4373960 {_105011 : Type'} (p1 : _105011) : (@IN _105011 p1) = (@IN _105011 p1).
Proof. exact (eq_refl (@IN _105011 p1)). Qed.
Lemma lem4373961 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : (term41 _105011 p1 f) = (term42 _105011 p1).
Proof. exact (MK_COMB (@lem4373960 _105011 p1) (@lem4373959 _105011 f h1)). Qed.
Lemma lem4373962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4373963 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : (term43 _105011 p1 f) = (term44 _105011 p1).
Proof. exact (MK_COMB (@lem4373962) (@lem4373961 _105011 p1 f h1)). Qed.
Lemma lem4373964 {_105012 : Type'} (p2 : _105012) (t : _105012 -> Prop) : (@IN _105012 p2 t) = (@IN _105012 p2 t).
Proof. exact (eq_refl (@IN _105012 p2 t)). Qed.
Lemma lem4373965 {_105011 _105012 : Type'} (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : (term40 _105011 _105012 p1 f p2 t) = (term45 _105011 _105012 p1 p2 t).
Proof. exact (MK_COMB (@lem4373963 _105011 p1 f h1) (@lem4373964 _105012 p2 t)). Qed.
Lemma lem4373968 {_105011 _105012 : Type'} (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : (term31 _105011 _105012 p1 p2 f t) = (term45 _105011 _105012 p1 p2 t).
Proof. exact (TRANS (@lem4373953 _105011 _105012 p1 f p2 t) (@lem4373965 _105011 _105012 p1 p2 t f h1)). Qed.
Lemma lem4373969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4373970 {_105011 _105012 : Type'} (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : (term46 _105011 _105012 p1 p2 f t) = (term47 _105011 _105012 p1 p2 t).
Proof. exact (MK_COMB (@lem4373969) (@lem4373968 _105011 _105012 p1 p2 t f h1)). Qed.
Lemma lem4373972 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4373833 _103718 _103721 x s y t) (@lem4373832 _103718 _103721 x s y t)). Qed.
Lemma lem4373973 {_105011 _105012 : Type'} (x : _105011) (s : _105011 -> Prop) (y : _105012) (t : _105012 -> Prop) : (term7 _105011 _105012 x y s t) = (term8 _105011 _105012 x s y t).
Proof. exact (@lem4373972 _105011 _105012 x s y t). Qed.
Lemma lem4373974 {_105011 _105012 : Type'} (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) : (term32 _105011 _105012 p1 p2 t) = (term48 _105011 _105012 p1 p2 t).
Proof. exact (@lem4373973 _105011 _105012 p1 (@UNIV _105011) p2 t). Qed.
Lemma lem4373977 {_105011 _105012 : Type'} (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : ((term31 _105011 _105012 p1 p2 f t) = (term32 _105011 _105012 p1 p2 t)) = ((term45 _105011 _105012 p1 p2 t) = (term48 _105011 _105012 p1 p2 t)).
Proof. exact (MK_COMB (@lem4373970 _105011 _105012 p1 p2 t f h1) (@lem4373974 _105011 _105012 p1 p2 t)). Qed.
Lemma lem4373982 {_105011 _105012 : Type'} (p1 : _105011) (t : _105012 -> Prop) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : (term34 _105011 _105012 f p1 t) = (term49 _105011 _105012 p1 t).
Proof. exact (fun_ext (fun p2 : _105012 => @lem4373977 _105011 _105012 p1 p2 t f h1)). Qed.
Lemma lem4373983 {_105012 : Type'} : (@all _105012) = (@all _105012).
Proof. exact (eq_refl (@all _105012)). Qed.
Lemma lem4373984 {_105011 _105012 : Type'} (p1 : _105011) (t : _105012 -> Prop) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : (term36 _105011 _105012 f p1 t) = (term50 _105011 _105012 p1 t).
Proof. exact (MK_COMB (@lem4373983 _105012) (@lem4373982 _105011 _105012 p1 t f h1)). Qed.
Lemma lem4373991 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : (term38 _105011 _105012 f t) = (term51 _105011 _105012 t).
Proof. exact (fun_ext (fun p1 : _105011 => @lem4373984 _105011 _105012 p1 t f h1)). Qed.
Lemma lem4373992 {_105011 : Type'} : (@all _105011) = (@all _105011).
Proof. exact (eq_refl (@all _105011)). Qed.
Lemma lem4373993 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : (term39 _105011 _105012 f t) = (term52 _105011 _105012 t).
Proof. exact (MK_COMB (@lem4373992 _105011) (@lem4373991 _105011 _105012 t f h1)). Qed.
Lemma lem4374000 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : ((term17 _105011 _105012 f t) = (@CROSS _105012 _105011 (@UNIV _105011) t)) = (term52 _105011 _105012 t).
Proof. exact (TRANS (@lem4373939 _105011 _105012 f t) (@lem4373993 _105011 _105012 t f h1)). Qed.
Lemma lem4374001 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : (term52 _105011 _105012 t) = ((term17 _105011 _105012 f t) = (@CROSS _105012 _105011 (@UNIV _105011) t)).
Proof. exact (SYM (@lem4374000 _105011 _105012 t f h1)). Qed.
