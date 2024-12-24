Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJA_INJ_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Require Import INJA_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Lemma lem1055869 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem1055870 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1055871 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1055870 A B f) (@lem1055869 A B f)). Qed.
Lemma lem1055872 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem1055871 A B f g). Qed.
Lemma lem1055873 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = ((f = g) = (term3 A B f g)).
Proof. exact (eq_refl (term2 A B f g)). Qed.
Lemma lem1055875 {A : Type'} (a : A) : term4 A a.
Proof. exact (@lem1055868 A a). Qed.
Lemma lem1055876 {A : Type'} (a : A) : (term4 A a) = ((@INJA A a) = (term5 A a)).
Proof. exact (eq_refl (term4 A a)). Qed.
Lemma lem1055885 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem1055873 A B f g) (@lem1055872 A B f g)). Qed.
Lemma lem1055886 {A : Type'} (f : type1597 A) (g : type1597 A) : (f = g) = (term6 A f g).
Proof. exact (@lem1055885 nat (A -> Prop) f g). Qed.
Lemma lem1055887 {A : Type'} (a1 : A) (a2 : A) : ((@INJA A a1) = (@INJA A a2)) = (term7 A a1 a2).
Proof. exact (@lem1055886 A (@INJA A a1) (@INJA A a2)). Qed.
Lemma lem1055895 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem1055873 A B f g) (@lem1055872 A B f g)). Qed.
Lemma lem1055896 {A : Type'} (f : A -> Prop) (g : A -> Prop) : (f = g) = (term8 A f g).
Proof. exact (@lem1055895 A Prop f g). Qed.
Lemma lem1055897 {A : Type'} (a1 : A) (a2 : A) (x : nat) : ((@INJA A a1 x) = (@INJA A a2 x)) = (term9 A a1 a2 x).
Proof. exact (@lem1055896 A (@INJA A a1 x) (@INJA A a2 x)). Qed.
Lemma lem1055907 {A : Type'} (a : A) : (@INJA A a) = (term5 A a).
Proof. exact (EQ_MP (@lem1055876 A a) (@lem1055875 A a)). Qed.
Lemma lem1055908 {A : Type'} (a : A) : (@INJA A a) = (term5 A a).
Proof. exact (@lem1055907 A a). Qed.
Lemma lem1055909 {A : Type'} (a1 : A) : (@INJA A a1) = (term5 A a1).
Proof. exact (@lem1055908 A a1). Qed.
Lemma lem1055914 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1055915 {A : Type'} (a1 : A) (x : nat) : (@INJA A a1 x) = (term10 A a1 x).
Proof. exact (MK_COMB (@lem1055909 A a1) (@lem1055914 x)). Qed.
Lemma lem1055917 {A B : Type'} (f : A -> B) (y : A) : (term11 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1055918 {A : Type'} (f : type1597 A) (y : nat) : (term12 A f y) = (f y).
Proof. exact (@lem1055917 nat (A -> Prop) f y). Qed.
Lemma lem1055919 {A : Type'} (a1 : A) (x : nat) : (term13 A a1 x) = (term10 A a1 x).
Proof. exact (@lem1055918 A (term5 A a1) x). Qed.
Lemma lem1055920 {A : Type'} (n : nat) (a1 : A) : (term10 A a1 n) = (term14 A a1).
Proof. exact (eq_refl (term10 A a1 n)). Qed.
Lemma lem1055921 {A : Type'} (a1 : A) : (term15 A a1) = (term5 A a1).
Proof. exact (fun_ext (fun n : nat => @lem1055920 A n a1)). Qed.
Lemma lem1055922 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1055923 {A : Type'} (a1 : A) (x : nat) : (term13 A a1 x) = (term10 A a1 x).
Proof. exact (MK_COMB (@lem1055921 A a1) (@lem1055922 x)). Qed.
Lemma lem1055924 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1055925 {A : Type'} (a1 : A) (x : nat) : (term16 A a1 x) = (term17 A a1 x).
Proof. exact (MK_COMB (@lem1055924 A) (@lem1055923 A a1 x)). Qed.
Lemma lem1055926 {A : Type'} (x : nat) (a1 : A) : (term10 A a1 x) = (term14 A a1).
Proof. exact (eq_refl (term10 A a1 x)). Qed.
Lemma lem1055927 {A : Type'} (x : nat) (a1 : A) : ((term13 A a1 x) = (term10 A a1 x)) = ((term10 A a1 x) = (term14 A a1)).
Proof. exact (MK_COMB (@lem1055925 A a1 x) (@lem1055926 A x a1)). Qed.
Lemma lem1055928 {A : Type'} (x : nat) (a1 : A) : (term10 A a1 x) = (term14 A a1).
Proof. exact (EQ_MP (@lem1055927 A x a1) (@lem1055919 A a1 x)). Qed.
Lemma lem1055933 {A : Type'} (x : nat) (a1 : A) : (@INJA A a1 x) = (term14 A a1).
Proof. exact (TRANS (@lem1055915 A a1 x) (@lem1055928 A x a1)). Qed.
Lemma lem1055934 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1055935 {A : Type'} (x : nat) (a1 : A) (x' : A) : (@INJA A a1 x x') = (term18 A a1 x').
Proof. exact (MK_COMB (@lem1055933 A x a1) (@lem1055934 A x')). Qed.
Lemma lem1055937 {A B : Type'} (f : A -> B) (y : A) : (term11 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1055938 {A : Type'} (f : A -> Prop) (y : A) : (term19 A f y) = (f y).
Proof. exact (@lem1055937 A Prop f y). Qed.
Lemma lem1055939 {A : Type'} (a1 : A) (x : A) : (term20 A a1 x) = (term18 A a1 x).
Proof. exact (@lem1055938 A (term14 A a1) x). Qed.
Lemma lem1055940 {A : Type'} (b : A) (a1 : A) : (term18 A a1 b) = (b = a1).
Proof. exact (eq_refl (term18 A a1 b)). Qed.
Lemma lem1055941 {A : Type'} (a1 : A) : (term21 A a1) = (term14 A a1).
Proof. exact (fun_ext (fun b : A => @lem1055940 A b a1)). Qed.
Lemma lem1055942 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1055943 {A : Type'} (a1 : A) (x : A) : (term20 A a1 x) = (term18 A a1 x).
Proof. exact (MK_COMB (@lem1055941 A a1) (@lem1055942 A x)). Qed.
Lemma lem1055944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1055945 {A : Type'} (a1 : A) (x : A) : (term22 A a1 x) = (term23 A a1 x).
Proof. exact (MK_COMB (@lem1055944) (@lem1055943 A a1 x)). Qed.
Lemma lem1055946 {A : Type'} (x : A) (a1 : A) : (term18 A a1 x) = (x = a1).
Proof. exact (eq_refl (term18 A a1 x)). Qed.
Lemma lem1055947 {A : Type'} (x : A) (a1 : A) : ((term20 A a1 x) = (term18 A a1 x)) = ((term18 A a1 x) = (x = a1)).
Proof. exact (MK_COMB (@lem1055945 A a1 x) (@lem1055946 A x a1)). Qed.
Lemma lem1055948 {A : Type'} (x : A) (a1 : A) : (term18 A a1 x) = (x = a1).
Proof. exact (EQ_MP (@lem1055947 A x a1) (@lem1055939 A a1 x)). Qed.
Lemma lem1055953 {A : Type'} (x : nat) (x' : A) (a1 : A) : (@INJA A a1 x x') = (x' = a1).
Proof. exact (TRANS (@lem1055935 A x a1 x') (@lem1055948 A x' a1)). Qed.
Lemma lem1055954 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1055955 {A : Type'} (x : nat) (x' : A) (a1 : A) : (term24 A a1 x x') = (term25 A x' a1).
Proof. exact (MK_COMB (@lem1055954) (@lem1055953 A x x' a1)). Qed.
Lemma lem1055957 {A : Type'} (a : A) : (@INJA A a) = (term5 A a).
Proof. exact (EQ_MP (@lem1055876 A a) (@lem1055875 A a)). Qed.
Lemma lem1055958 {A : Type'} (a : A) : (@INJA A a) = (term5 A a).
Proof. exact (@lem1055957 A a). Qed.
Lemma lem1055959 {A : Type'} (a2 : A) : (@INJA A a2) = (term5 A a2).
Proof. exact (@lem1055958 A a2). Qed.
Lemma lem1055964 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1055965 {A : Type'} (a2 : A) (x : nat) : (@INJA A a2 x) = (term10 A a2 x).
Proof. exact (MK_COMB (@lem1055959 A a2) (@lem1055964 x)). Qed.
Lemma lem1055967 {A B : Type'} (f : A -> B) (y : A) : (term11 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1055968 {A : Type'} (f : type1597 A) (y : nat) : (term12 A f y) = (f y).
Proof. exact (@lem1055967 nat (A -> Prop) f y). Qed.
Lemma lem1055969 {A : Type'} (a2 : A) (x : nat) : (term13 A a2 x) = (term10 A a2 x).
Proof. exact (@lem1055968 A (term5 A a2) x). Qed.
Lemma lem1055970 {A : Type'} (n : nat) (a2 : A) : (term10 A a2 n) = (term14 A a2).
Proof. exact (eq_refl (term10 A a2 n)). Qed.
Lemma lem1055971 {A : Type'} (a2 : A) : (term15 A a2) = (term5 A a2).
Proof. exact (fun_ext (fun n : nat => @lem1055970 A n a2)). Qed.
Lemma lem1055972 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1055973 {A : Type'} (a2 : A) (x : nat) : (term13 A a2 x) = (term10 A a2 x).
Proof. exact (MK_COMB (@lem1055971 A a2) (@lem1055972 x)). Qed.
Lemma lem1055974 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1055975 {A : Type'} (a2 : A) (x : nat) : (term16 A a2 x) = (term17 A a2 x).
Proof. exact (MK_COMB (@lem1055974 A) (@lem1055973 A a2 x)). Qed.
Lemma lem1055976 {A : Type'} (x : nat) (a2 : A) : (term10 A a2 x) = (term14 A a2).
Proof. exact (eq_refl (term10 A a2 x)). Qed.
Lemma lem1055977 {A : Type'} (x : nat) (a2 : A) : ((term13 A a2 x) = (term10 A a2 x)) = ((term10 A a2 x) = (term14 A a2)).
Proof. exact (MK_COMB (@lem1055975 A a2 x) (@lem1055976 A x a2)). Qed.
Lemma lem1055978 {A : Type'} (x : nat) (a2 : A) : (term10 A a2 x) = (term14 A a2).
Proof. exact (EQ_MP (@lem1055977 A x a2) (@lem1055969 A a2 x)). Qed.
Lemma lem1055983 {A : Type'} (x : nat) (a2 : A) : (@INJA A a2 x) = (term14 A a2).
Proof. exact (TRANS (@lem1055965 A a2 x) (@lem1055978 A x a2)). Qed.
Lemma lem1055984 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1055985 {A : Type'} (x : nat) (a2 : A) (x' : A) : (@INJA A a2 x x') = (term18 A a2 x').
Proof. exact (MK_COMB (@lem1055983 A x a2) (@lem1055984 A x')). Qed.
Lemma lem1055987 {A B : Type'} (f : A -> B) (y : A) : (term11 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1055988 {A : Type'} (f : A -> Prop) (y : A) : (term19 A f y) = (f y).
Proof. exact (@lem1055987 A Prop f y). Qed.
Lemma lem1055989 {A : Type'} (a2 : A) (x : A) : (term20 A a2 x) = (term18 A a2 x).
Proof. exact (@lem1055988 A (term14 A a2) x). Qed.
Lemma lem1055990 {A : Type'} (b : A) (a2 : A) : (term18 A a2 b) = (b = a2).
Proof. exact (eq_refl (term18 A a2 b)). Qed.
Lemma lem1055991 {A : Type'} (a2 : A) : (term21 A a2) = (term14 A a2).
Proof. exact (fun_ext (fun b : A => @lem1055990 A b a2)). Qed.
Lemma lem1055992 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1055993 {A : Type'} (a2 : A) (x : A) : (term20 A a2 x) = (term18 A a2 x).
Proof. exact (MK_COMB (@lem1055991 A a2) (@lem1055992 A x)). Qed.
Lemma lem1055994 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1055995 {A : Type'} (a2 : A) (x : A) : (term22 A a2 x) = (term23 A a2 x).
Proof. exact (MK_COMB (@lem1055994) (@lem1055993 A a2 x)). Qed.
Lemma lem1055996 {A : Type'} (x : A) (a2 : A) : (term18 A a2 x) = (x = a2).
Proof. exact (eq_refl (term18 A a2 x)). Qed.
Lemma lem1055997 {A : Type'} (x : A) (a2 : A) : ((term20 A a2 x) = (term18 A a2 x)) = ((term18 A a2 x) = (x = a2)).
Proof. exact (MK_COMB (@lem1055995 A a2 x) (@lem1055996 A x a2)). Qed.
Lemma lem1055998 {A : Type'} (x : A) (a2 : A) : (term18 A a2 x) = (x = a2).
Proof. exact (EQ_MP (@lem1055997 A x a2) (@lem1055989 A a2 x)). Qed.
Lemma lem1056003 {A : Type'} (x : nat) (x' : A) (a2 : A) : (@INJA A a2 x x') = (x' = a2).
Proof. exact (TRANS (@lem1055985 A x a2 x') (@lem1055998 A x' a2)). Qed.
Lemma lem1056004 {A : Type'} (x : nat) (a1 : A) (x' : A) (a2 : A) : ((@INJA A a1 x x') = (@INJA A a2 x x')) = ((x' = a1) = (x' = a2)).
Proof. exact (MK_COMB (@lem1055955 A x x' a1) (@lem1056003 A x x' a2)). Qed.
Lemma lem1056009 {A : Type'} (x : nat) (a1 : A) (a2 : A) : (term26 A a1 a2 x) = (term27 A a1 a2).
Proof. exact (fun_ext (fun x' : A => @lem1056004 A x a1 x' a2)). Qed.
Lemma lem1056010 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1056011 {A : Type'} (x : nat) (a1 : A) (a2 : A) : (term9 A a1 a2 x) = (term28 A a1 a2).
Proof. exact (MK_COMB (@lem1056010 A) (@lem1056009 A x a1 a2)). Qed.
Lemma lem1056016 {A : Type'} (x : nat) (a1 : A) (a2 : A) : ((@INJA A a1 x) = (@INJA A a2 x)) = (term28 A a1 a2).
Proof. exact (TRANS (@lem1055897 A a1 a2 x) (@lem1056011 A x a1 a2)). Qed.
Lemma lem1056017 {A : Type'} (a1 : A) (a2 : A) : (term29 A a1 a2) = (term30 A a1 a2).
Proof. exact (fun_ext (fun x : nat => @lem1056016 A x a1 a2)). Qed.
Lemma lem1056018 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1056019 {A : Type'} (a1 : A) (a2 : A) : (term7 A a1 a2) = (term31 A a1 a2).
Proof. exact (MK_COMB (@lem1056018) (@lem1056017 A a1 a2)). Qed.
Lemma lem1056021 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1056022 (t : Prop) : (term33 t) = t.
Proof. exact (@lem1056021 nat t). Qed.
Lemma lem1056023 {A : Type'} (a1 : A) (a2 : A) : (term31 A a1 a2) = (term28 A a1 a2).
Proof. exact (@lem1056022 (term28 A a1 a2)). Qed.
Lemma lem1056040 {A : Type'} (a1 : A) (a2 : A) : (term7 A a1 a2) = (term28 A a1 a2).
Proof. exact (TRANS (@lem1056019 A a1 a2) (@lem1056023 A a1 a2)). Qed.
Lemma lem1056041 {A : Type'} (a1 : A) (a2 : A) : ((@INJA A a1) = (@INJA A a2)) = (term28 A a1 a2).
Proof. exact (TRANS (@lem1055887 A a1 a2) (@lem1056040 A a1 a2)). Qed.
Lemma lem1056042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1056043 {A : Type'} (a1 : A) (a2 : A) : (term34 A a1 a2) = (term35 A a1 a2).
Proof. exact (MK_COMB (@lem1056042) (@lem1056041 A a1 a2)). Qed.
Lemma lem1056048 {A : Type'} (a1 : A) (a2 : A) : (a1 = a2) = (a1 = a2).
Proof. exact (eq_refl (a1 = a2)). Qed.
Lemma lem1056049 {A : Type'} (a1 : A) (a2 : A) : (((@INJA A a1) = (@INJA A a2)) = (a1 = a2)) = ((term28 A a1 a2) = (a1 = a2)).
Proof. exact (MK_COMB (@lem1056043 A a1 a2) (@lem1056048 A a1 a2)). Qed.
Lemma lem1056054 {A : Type'} (a1 : A) (a2 : A) : ((term28 A a1 a2) = (a1 = a2)) = (((@INJA A a1) = (@INJA A a2)) = (a1 = a2)).
Proof. exact (SYM (@lem1056049 A a1 a2)). Qed.
Lemma lem1056055 {A : Type'} (a1 : A) (a2 : A) (h1 : term28 A a1 a2) : term28 A a1 a2.
Proof. exact (h1). Qed.
Lemma lem1056056 {A : Type'} (a1 : A) (a2 : A) (h1 : term28 A a1 a2) : term36 A a2 a1.
Proof. exact (@lem1056055 A a1 a2 h1 a1). Qed.
Lemma lem1056057 {A : Type'} (a1 : A) (a2 : A) : (term36 A a2 a1) = ((a1 = a1) = (a1 = a2)).
Proof. exact (eq_refl (term36 A a2 a1)). Qed.
Lemma lem1056058 {A : Type'} (a1 : A) (a2 : A) (h1 : term28 A a1 a2) : (a1 = a1) = (a1 = a2).
Proof. exact (EQ_MP (@lem1056057 A a1 a2) (@lem1056056 A a1 a2 h1)). Qed.
Lemma lem1056066 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1056067 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1056066 A x). Qed.
Lemma lem1056068 {A : Type'} (a1 : A) : (a1 = a1) = True.
Proof. exact (@lem1056067 A a1). Qed.
Lemma lem1056069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1056070 {A : Type'} (a1 : A) : (term37 A a1) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1056069) (@lem1056068 A a1)). Qed.
Lemma lem1056073 {A : Type'} (a1 : A) (a2 : A) : (a1 = a2) = (a1 = a2).
Proof. exact (eq_refl (a1 = a2)). Qed.
Lemma lem1056074 {A : Type'} (a1 : A) (a2 : A) : ((a1 = a1) = (a1 = a2)) = (True = (a1 = a2)).
Proof. exact (MK_COMB (@lem1056070 A a1) (@lem1056073 A a1 a2)). Qed.
Lemma lem1056076 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1056077 {A : Type'} (a1 : A) (a2 : A) : (True = (a1 = a2)) = (a1 = a2).
Proof. exact (@lem1056076 (a1 = a2)). Qed.
Lemma lem1056080 {A : Type'} (a1 : A) (a2 : A) : ((a1 = a1) = (a1 = a2)) = (a1 = a2).
Proof. exact (TRANS (@lem1056074 A a1 a2) (@lem1056077 A a1 a2)). Qed.
Lemma lem1056081 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1056082 {A : Type'} (a1 : A) (a2 : A) : (term38 A a1 a2) = (term39 A a1 a2).
Proof. exact (MK_COMB (@lem1056081) (@lem1056080 A a1 a2)). Qed.
Lemma lem1056085 {A : Type'} (a1 : A) (a2 : A) : (a1 = a2) = (a1 = a2).
Proof. exact (eq_refl (a1 = a2)). Qed.
Lemma lem1056086 {A : Type'} (a1 : A) (a2 : A) : (term40 A a1 a2) = (term41 A a1 a2).
Proof. exact (MK_COMB (@lem1056082 A a1 a2) (@lem1056085 A a1 a2)). Qed.
Lemma lem1056090 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1056091 {A : Type'} (a1 : A) (a2 : A) : (term41 A a1 a2) = True.
Proof. exact (@lem1056090 (a1 = a2)). Qed.
Lemma lem1056092 {A : Type'} (a1 : A) (a2 : A) : (term40 A a1 a2) = True.
Proof. exact (TRANS (@lem1056086 A a1 a2) (@lem1056091 A a1 a2)). Qed.
Lemma lem1056093 {A : Type'} (a1 : A) (a2 : A) : True = (term40 A a1 a2).
Proof. exact (SYM (@lem1056092 A a1 a2)). Qed.
Lemma lem1056094 {A : Type'} (a1 : A) (a2 : A) : term40 A a1 a2.
Proof. exact (EQ_MP (@lem1056093 A a1 a2) (@lem0)). Qed.
Lemma lem1056095 {A : Type'} (a1 : A) (a2 : A) (h1 : term28 A a1 a2) : a1 = a2.
Proof. exact (@lem1056094 A a1 a2 (@lem1056058 A a1 a2 h1)). Qed.
Lemma lem1056096 {A : Type'} (a1 : A) (a2 : A) : term42 A a1 a2.
Proof. exact (fun h0 : term28 A a1 a2 => @lem1056095 A a1 a2 h0). Qed.
Lemma lem1056097 {A : Type'} (a1 : A) (a2 : A) (h1 : a1 = a2) : a1 = a2.
Proof. exact (h1). Qed.
Lemma lem1056098 {A : Type'} (a2 : A) : (term43 A a2) = (term43 A a2).
Proof. exact (eq_refl (term43 A a2)). Qed.
Lemma lem1056099 {A : Type'} (a1 : A) (a2 : A) (h1 : a1 = a2) : (term44 A a2 a1) = (term45 A a2).
Proof. exact (MK_COMB (@lem1056098 A a2) (@lem1056097 A a1 a2 h1)). Qed.
Lemma lem1056100 {A : Type'} (a2 : A) : (term45 A a2) = (term46 A a2).
Proof. exact (eq_refl (term45 A a2)). Qed.
Lemma lem1056101 {A : Type'} (a2 : A) (a1 : A) : (term47 A a2 a1) = (term47 A a2 a1).
Proof. exact (eq_refl (term47 A a2 a1)). Qed.
Lemma lem1056102 {A : Type'} (a1 : A) (a2 : A) : ((term44 A a2 a1) = (term45 A a2)) = ((term44 A a2 a1) = (term46 A a2)).
Proof. exact (MK_COMB (@lem1056101 A a2 a1) (@lem1056100 A a2)). Qed.
Lemma lem1056103 {A : Type'} (a1 : A) (a2 : A) : (term44 A a2 a1) = (term28 A a1 a2).
Proof. exact (eq_refl (term44 A a2 a1)). Qed.
Lemma lem1056104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1056105 {A : Type'} (a1 : A) (a2 : A) : (term47 A a2 a1) = (term35 A a1 a2).
Proof. exact (MK_COMB (@lem1056104) (@lem1056103 A a1 a2)). Qed.
Lemma lem1056106 {A : Type'} (a2 : A) : (term46 A a2) = (term46 A a2).
Proof. exact (eq_refl (term46 A a2)). Qed.
Lemma lem1056107 {A : Type'} (a1 : A) (a2 : A) : ((term44 A a2 a1) = (term46 A a2)) = ((term28 A a1 a2) = (term46 A a2)).
Proof. exact (MK_COMB (@lem1056105 A a1 a2) (@lem1056106 A a2)). Qed.
Lemma lem1056108 {A : Type'} (a1 : A) (a2 : A) : ((term44 A a2 a1) = (term45 A a2)) = ((term28 A a1 a2) = (term46 A a2)).
Proof. exact (TRANS (@lem1056102 A a1 a2) (@lem1056107 A a1 a2)). Qed.
Lemma lem1056109 {A : Type'} (a1 : A) (a2 : A) (h1 : a1 = a2) : (term28 A a1 a2) = (term46 A a2).
Proof. exact (EQ_MP (@lem1056108 A a1 a2) (@lem1056099 A a1 a2 h1)). Qed.
Lemma lem1056110 {A : Type'} (a1 : A) (a2 : A) (h1 : a1 = a2) : (term46 A a2) = (term28 A a1 a2).
Proof. exact (SYM (@lem1056109 A a1 a2 h1)). Qed.
Lemma lem1056116 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1056117 (x : Prop) : (x = x) = True.
Proof. exact (@lem1056116 Prop x). Qed.
Lemma lem1056118 {A : Type'} (x : A) (a2 : A) : ((x = a2) = (x = a2)) = True.
Proof. exact (@lem1056117 (x = a2)). Qed.
Lemma lem1056119 {A : Type'} (a2 : A) : (term48 A a2) = (term49 A).
Proof. exact (fun_ext (fun x : A => @lem1056118 A x a2)). Qed.
Lemma lem1056120 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1056121 {A : Type'} (a2 : A) : (term46 A a2) = (term50 A).
Proof. exact (MK_COMB (@lem1056120 A) (@lem1056119 A a2)). Qed.
Lemma lem1056123 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1056124 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (@lem1056123 A t). Qed.
Lemma lem1056125 {A : Type'} : (term50 A) = True.
Proof. exact (@lem1056124 A True). Qed.
Lemma lem1056126 {A : Type'} (a2 : A) : (term46 A a2) = True.
Proof. exact (TRANS (@lem1056121 A a2) (@lem1056125 A)). Qed.
Lemma lem1056127 {A : Type'} (a2 : A) : True = (term46 A a2).
Proof. exact (SYM (@lem1056126 A a2)). Qed.
Lemma lem1056128 {A : Type'} (a2 : A) : term46 A a2.
Proof. exact (EQ_MP (@lem1056127 A a2) (@lem0)). Qed.
Lemma lem1056129 {A : Type'} (a1 : A) (a2 : A) (h1 : a1 = a2) : term28 A a1 a2.
Proof. exact (EQ_MP (@lem1056110 A a1 a2 h1) (@lem1056128 A a2)). Qed.
Lemma lem1056130 {A : Type'} (a1 : A) (a2 : A) : term51 A a1 a2.
Proof. exact (fun h0 : a1 = a2 => @lem1056129 A a1 a2 h0). Qed.
Lemma lem1056131 {A : Type'} (a1 : A) (a2 : A) : term52 A a1 a2.
Proof. exact (conj (@lem1056096 A a1 a2) (@lem1056130 A a1 a2)). Qed.
Lemma lem1056132 {A : Type'} (a1 : A) (a2 : A) : (term52 A a1 a2) = ((term28 A a1 a2) = (a1 = a2)).
Proof. exact (@lem32 (term28 A a1 a2) (a1 = a2)). Qed.
Lemma lem1056133 {A : Type'} (a1 : A) (a2 : A) : (term28 A a1 a2) = (a1 = a2).
Proof. exact (EQ_MP (@lem1056132 A a1 a2) (@lem1056131 A a1 a2)). Qed.
Lemma lem1056134 {A : Type'} (a1 : A) (a2 : A) : ((@INJA A a1) = (@INJA A a2)) = (a1 = a2).
Proof. exact (EQ_MP (@lem1056054 A a1 a2) (@lem1056133 A a1 a2)). Qed.
Lemma lem1056139 {A : Type'} (a1 : A) : term53 A a1.
Proof. exact (fun a2 : A => @lem1056134 A a1 a2). Qed.
Lemma lem1056144 {A : Type'} : term54 A.
Proof. exact (fun a1 : A => @lem1056139 A a1). Qed.
