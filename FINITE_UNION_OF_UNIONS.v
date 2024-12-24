Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_UNION_OF_UNIONS_term_abbrevs.
Require Import FINITE_UNION_OF_IDEMPOT_spec.
Require Import UNION_OF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem4886899 {A : Type'} (P : type180 A) : term0 A P.
Proof. exact (@lem4841086 A P). Qed.
Lemma lem4886900 {A : Type'} (P : type180 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4886901 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (EQ_MP (@lem4886900 A P) (@lem4886899 A P)). Qed.
Lemma lem4886902 {A : Type'} (P : type180 A) (Q : type686 A) : term2 A P Q.
Proof. exact (@lem4886901 A P Q). Qed.
Lemma lem4886903 {A : Type'} (P : type180 A) (Q : type686 A) : (term2 A P Q) = ((@UNION_OF A P Q) = (term3 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem4886906 {A : Type'} (P : type686 A) (h1 : (term4 A P) = (@UNION_OF A (@FINITE (A -> Prop)) P)) : (term4 A P) = (@UNION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (h1). Qed.
Lemma lem4886907 {A : Type'} (P : type686 A) (h1 : (term4 A P) = (@UNION_OF A (@FINITE (A -> Prop)) P)) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term4 A P).
Proof. exact (SYM (@lem4886906 A P h1)). Qed.
Lemma lem4886908 {A : Type'} (P : type686 A) (h1 : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term4 A P)) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term4 A P).
Proof. exact (h1). Qed.
Lemma lem4886909 {A : Type'} (P : type686 A) (h1 : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term4 A P)) : (term4 A P) = (@UNION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (SYM (@lem4886908 A P h1)). Qed.
Lemma lem4886910 {A : Type'} (P : type686 A) : ((term4 A P) = (@UNION_OF A (@FINITE (A -> Prop)) P)) = ((@UNION_OF A (@FINITE (A -> Prop)) P) = (term4 A P)).
Proof. exact (prop_ext (fun h1 : (term4 A P) = (@UNION_OF A (@FINITE (A -> Prop)) P) => @lem4886907 A P h1) (fun h1 : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term4 A P) => @lem4886909 A P h1)). Qed.
Lemma lem4886911 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4886910 A P)). Qed.
Lemma lem4886912 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4886913 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (MK_COMB (@lem4886912 A) (@lem4886911 A)). Qed.
Lemma lem4886914 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem4886913 A) (@lem4886667 A)). Qed.
Lemma lem4886915 {A : Type'} (P : type686 A) : term9 A P.
Proof. exact (@lem4886914 A P). Qed.
Lemma lem4886916 {A : Type'} (P : type686 A) : (term9 A P) = ((@UNION_OF A (@FINITE (A -> Prop)) P) = (term4 A P)).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem4886918 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term10 A u P.
Proof. exact (h1). Qed.
Lemma lem4886919 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term11 A u P) : term11 A u P.
Proof. exact (h1). Qed.
Lemma lem4886920 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : @FINITE (A -> Prop) u.
Proof. exact (h1). Qed.
Lemma lem4886922 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term4 A P).
Proof. exact (EQ_MP (@lem4886916 A P) (@lem4886915 A P)). Qed.
Lemma lem4886923 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term4 A P).
Proof. exact (@lem4886922 A P). Qed.
Lemma lem4886924 {A : Type'} (u : type686 A) : (@UNIONS A u) = (@UNIONS A u).
Proof. exact (eq_refl (@UNIONS A u)). Qed.
Lemma lem4886925 {A : Type'} (P : type686 A) (u : type686 A) : (term12 A P u) = (term13 A P u).
Proof. exact (MK_COMB (@lem4886923 A P) (@lem4886924 A u)). Qed.
Lemma lem4886926 {A : Type'} (P : type686 A) (u : type686 A) : (term13 A P u) = (term12 A P u).
Proof. exact (SYM (@lem4886925 A P u)). Qed.
Lemma lem4886928 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem4886903 A P Q) (@lem4886902 A P Q)). Qed.
Lemma lem4886929 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (@lem4886928 A P Q). Qed.
Lemma lem4886930 {A : Type'} (P : type686 A) : (term4 A P) = (term14 A P).
Proof. exact (@lem4886929 A (@FINITE (A -> Prop)) (@UNION_OF A (@FINITE (A -> Prop)) P)). Qed.
Lemma lem4886931 {A : Type'} (u : type686 A) : (@UNIONS A u) = (@UNIONS A u).
Proof. exact (eq_refl (@UNIONS A u)). Qed.
Lemma lem4886932 {A : Type'} (P : type686 A) (u : type686 A) : (term13 A P u) = (term15 A P u).
Proof. exact (MK_COMB (@lem4886930 A P) (@lem4886931 A u)). Qed.
Lemma lem4886933 {A : Type'} (P : type686 A) (u : type686 A) : (term15 A P u) = (term13 A P u).
Proof. exact (SYM (@lem4886932 A P u)). Qed.
Lemma lem4886935 {A B : Type'} (f : A -> B) (y : A) : (term16 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4886936 {A : Type'} (f : type686 A) (y : A -> Prop) : (term17 A f y) = (f y).
Proof. exact (@lem4886935 (A -> Prop) Prop f y). Qed.
Lemma lem4886937 {A : Type'} (P : type686 A) (u : type686 A) : (term18 A P u) = (term15 A P u).
Proof. exact (@lem4886936 A (term14 A P) (@UNIONS A u)). Qed.
Lemma lem4886938 {A : Type'} (P : type686 A) (s : A -> Prop) : (term19 A P s) = (term20 A P s).
Proof. exact (eq_refl (term19 A P s)). Qed.
Lemma lem4886939 {A : Type'} (P : type686 A) : (term21 A P) = (term14 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4886938 A P s)). Qed.
Lemma lem4886940 {A : Type'} (u : type686 A) : (@UNIONS A u) = (@UNIONS A u).
Proof. exact (eq_refl (@UNIONS A u)). Qed.
Lemma lem4886941 {A : Type'} (P : type686 A) (u : type686 A) : (term18 A P u) = (term15 A P u).
Proof. exact (MK_COMB (@lem4886939 A P) (@lem4886940 A u)). Qed.
Lemma lem4886942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4886943 {A : Type'} (P : type686 A) (u : type686 A) : (term22 A P u) = (term23 A P u).
Proof. exact (MK_COMB (@lem4886942) (@lem4886941 A P u)). Qed.
Lemma lem4886944 {A : Type'} (P : type686 A) (u : type686 A) : (term15 A P u) = (term24 A P u).
Proof. exact (eq_refl (term15 A P u)). Qed.
Lemma lem4886945 {A : Type'} (P : type686 A) (u : type686 A) : ((term18 A P u) = (term15 A P u)) = ((term15 A P u) = (term24 A P u)).
Proof. exact (MK_COMB (@lem4886943 A P u) (@lem4886944 A P u)). Qed.
Lemma lem4886946 {A : Type'} (P : type686 A) (u : type686 A) : (term15 A P u) = (term24 A P u).
Proof. exact (EQ_MP (@lem4886945 A P u) (@lem4886937 A P u)). Qed.
Lemma lem4886963 {A : Type'} (P : type686 A) (u : type686 A) : (term24 A P u) = (term15 A P u).
Proof. exact (SYM (@lem4886946 A P u)). Qed.
Lemma lem4886964 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = ((@FINITE (A -> Prop) u) = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) u)). Qed.
Lemma lem4886966 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term11 A u P) : term25 A u P s.
Proof. exact (@lem4886919 A u P h1 s). Qed.
Lemma lem4886967 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term25 A u P s) = (term26 A u P s).
Proof. exact (eq_refl (term25 A u P s)). Qed.
Lemma lem4886968 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term11 A u P) : term26 A u P s.
Proof. exact (EQ_MP (@lem4886967 A u P s) (@lem4886966 A s u P h1)). Qed.
Lemma lem4886969 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term26 A u P s) = ((term26 A u P s) = True).
Proof. exact (@lem7 (term26 A u P s)). Qed.
Lemma lem4886974 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (@FINITE (A -> Prop) u) = True.
Proof. exact (EQ_MP (@lem4886964 A u) (@lem4886920 A u h1)). Qed.
Lemma lem4886975 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4886976 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (term27 A u) = (and True).
Proof. exact (MK_COMB (@lem4886975) (@lem4886974 A u h1)). Qed.
Lemma lem4886984 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term26 A u P s) = True.
Proof. exact (EQ_MP (@lem4886969 A u P s) (@lem4886968 A s u P h1)). Qed.
Lemma lem4886985 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term26 A u P s) = True.
Proof. exact (@lem4886984 A s u P h1). Qed.
Lemma lem4886986 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term26 A u P c) = True.
Proof. exact (@lem4886985 A c u P h1). Qed.
Lemma lem4886987 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term28 A u P) = (term29 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4886986 A c u P h1)). Qed.
Lemma lem4886988 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4886989 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term11 A u P) = (term30 A).
Proof. exact (MK_COMB (@lem4886988 A) (@lem4886987 A u P h1)). Qed.
Lemma lem4886991 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4886992 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (@lem4886991 (A -> Prop) t). Qed.
Lemma lem4886993 {A : Type'} : (term30 A) = True.
Proof. exact (@lem4886992 A True). Qed.
Lemma lem4886994 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term11 A u P) = True.
Proof. exact (TRANS (@lem4886989 A u P h1) (@lem4886993 A)). Qed.
Lemma lem4886995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4886996 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term33 A u P) = (and True).
Proof. exact (MK_COMB (@lem4886995) (@lem4886994 A u P h1)). Qed.
Lemma lem4886998 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4886999 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4886998 (A -> Prop) x). Qed.
Lemma lem4887000 {A : Type'} (u : type686 A) : ((@UNIONS A u) = (@UNIONS A u)) = True.
Proof. exact (@lem4886999 A (@UNIONS A u)). Qed.
Lemma lem4887001 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term34 A P u) = (True /\ True).
Proof. exact (MK_COMB (@lem4886996 A u P h1) (@lem4887000 A u)). Qed.
Lemma lem4887003 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4887004 : (True /\ True) = True.
Proof. exact (@lem4887003 True). Qed.
Lemma lem4887005 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term34 A P u) = True.
Proof. exact (TRANS (@lem4887001 A u P h1) (@lem4887004)). Qed.
Lemma lem4887006 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : (term35 A P u) = (True /\ True).
Proof. exact (MK_COMB (@lem4886976 A u h2) (@lem4887005 A u P h1)). Qed.
Lemma lem4887008 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4887009 : (True /\ True) = True.
Proof. exact (@lem4887008 True). Qed.
Lemma lem4887010 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : (term35 A P u) = True.
Proof. exact (TRANS (@lem4887006 A P u h1 h2) (@lem4887009)). Qed.
Lemma lem4887011 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : True = (term35 A P u).
Proof. exact (SYM (@lem4887010 A P u h1 h2)). Qed.
Lemma lem4887012 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : term35 A P u.
Proof. exact (EQ_MP (@lem4887011 A P u h1 h2) (@lem0)). Qed.
Lemma lem4887013 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : term24 A P u.
Proof. exact (ex_intro (term36 A P u) u (@lem4887012 A P u h1 h2)). Qed.
Lemma lem4887014 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : term15 A P u.
Proof. exact (EQ_MP (@lem4886963 A P u) (@lem4887013 A P u h1 h2)). Qed.
Lemma lem4887015 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : term13 A P u.
Proof. exact (EQ_MP (@lem4886933 A P u) (@lem4887014 A P u h1 h2)). Qed.
Lemma lem4887016 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : term12 A P u.
Proof. exact (EQ_MP (@lem4886926 A P u) (@lem4887015 A P u h1 h2)). Qed.
Lemma lem4887017 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term11 A u P.
Proof. exact (proj2 (@lem4886918 A u P h1)). Qed.
Lemma lem4887018 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : @FINITE (A -> Prop) u.
Proof. exact (proj1 (@lem4886918 A u P h1)). Qed.
Lemma lem4887019 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : (term11 A u P) = (term12 A P u).
Proof. exact (prop_ext (fun h3 : term11 A u P => @lem4887016 A P u h1 h2) (fun h3 : term12 A P u => @lem4886919 A u P h1)). Qed.
Lemma lem4887020 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : term12 A P u.
Proof. exact (EQ_MP (@lem4887019 A P u h1 h2) (@lem4886919 A u P h1)). Qed.
Lemma lem4887021 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : (@FINITE (A -> Prop) u) = (term12 A P u).
Proof. exact (prop_ext (fun h3 : @FINITE (A -> Prop) u => @lem4887020 A P u h1 h2) (fun h3 : term12 A P u => @lem4886920 A u h2)). Qed.
Lemma lem4887022 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : term12 A P u.
Proof. exact (EQ_MP (@lem4887021 A P u h1 h2) (@lem4886920 A u h2)). Qed.
Lemma lem4887023 {A : Type'} (u : type686 A) (P : type686 A) (h1 : @FINITE (A -> Prop) u) (h2 : term10 A u P) : (term11 A u P) = (term12 A P u).
Proof. exact (prop_ext (fun h3 : term11 A u P => @lem4887022 A P u h3 h1) (fun h3 : term12 A P u => @lem4887017 A u P h2)). Qed.
Lemma lem4887024 {A : Type'} (u : type686 A) (P : type686 A) (h1 : @FINITE (A -> Prop) u) (h2 : term10 A u P) : term12 A P u.
Proof. exact (EQ_MP (@lem4887023 A u P h1 h2) (@lem4887017 A u P h2)). Qed.
Lemma lem4887025 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (@FINITE (A -> Prop) u) = (term12 A P u).
Proof. exact (prop_ext (fun h2 : @FINITE (A -> Prop) u => @lem4887024 A u P h2 h1) (fun h2 : term12 A P u => @lem4887018 A u P h1)). Qed.
Lemma lem4887026 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term12 A P u.
Proof. exact (EQ_MP (@lem4887025 A u P h1) (@lem4887018 A u P h1)). Qed.
Lemma lem4887027 {A : Type'} (P : type686 A) (u : type686 A) : term37 A P u.
Proof. exact (fun h0 : term10 A u P => @lem4887026 A u P h0). Qed.
Lemma lem4887032 {A : Type'} (P : type686 A) : term38 A P.
Proof. exact (fun u : type686 A => @lem4887027 A P u). Qed.
Lemma lem4887037 {A : Type'} : term39 A.
Proof. exact (fun P : type686 A => @lem4887032 A P). Qed.
