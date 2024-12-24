Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_UNDEFINED_term_abbrevs.
Require Import RESTRICTION_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem4386844 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4386845 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4386846 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4386845 A B s) (@lem4386844 A B s)). Qed.
Lemma lem4386847 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem4386846 A B s f). Qed.
Lemma lem4386848 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = (term3 A B s f).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem4386849 {A B : Type'} (s : A -> Prop) (f : A -> B) : term3 A B s f.
Proof. exact (EQ_MP (@lem4386848 A B s f) (@lem4386847 A B s f)). Qed.
Lemma lem4386850 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term4 A B s f x.
Proof. exact (@lem4386849 A B s f x). Qed.
Lemma lem4386851 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term4 A B s f x) = ((@RESTRICTION A B s f x) = (term5 A B s f x)).
Proof. exact (eq_refl (term4 A B s f x)). Qed.
Lemma lem4386868 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term6 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4386869 (p : Prop) (q : Prop) (p' : Prop) : term7 p q p'.
Proof. exact (fun q' : Prop => @lem4386868 p q p' q'). Qed.
Lemma lem4386870 (p : Prop) (q : Prop) : term8 p q.
Proof. exact (fun p' : Prop => @lem4386869 p q p'). Qed.
Lemma lem4386871 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term9 A B s f x.
Proof. exact (@lem4386870 (term10 A x s) ((@RESTRICTION A B s f x) = (@ARB B))). Qed.
Lemma lem4386872 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : term11 A B s f x p'.
Proof. exact (@lem4386871 A B s f x p'). Qed.
Lemma lem4386873 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : (term11 A B s f x p') = (term12 A B s f x p').
Proof. exact (eq_refl (term11 A B s f x p')). Qed.
Lemma lem4386874 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : term12 A B s f x p'.
Proof. exact (EQ_MP (@lem4386873 A B s f x p') (@lem4386872 A B s f x p')). Qed.
Lemma lem4386875 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term13 A B s f x p' q'.
Proof. exact (@lem4386874 A B s f x p' q'). Qed.
Lemma lem4386876 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : (term13 A B s f x p' q') = (term14 A B s f x p' q').
Proof. exact (eq_refl (term13 A B s f x p' q')). Qed.
Lemma lem4386877 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term14 A B s f x p' q'.
Proof. exact (EQ_MP (@lem4386876 A B s f x p' q') (@lem4386875 A B s f x p' q')). Qed.
Lemma lem4386878 {A : Type'} (x : A) (s : A -> Prop) : (term10 A x s) = (term10 A x s).
Proof. exact (eq_refl (term10 A x s)). Qed.
Lemma lem4386879 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term15 A B f x s q'.
Proof. exact (@lem4386877 A B s f x (term10 A x s) q'). Qed.
Lemma lem4386880 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term16 A B f x s q'.
Proof. exact (@lem4386879 A B f x s q' (@lem4386878 A x s)). Qed.
Lemma lem4386881 {A : Type'} (x : A) (s : A -> Prop) (h1 : term10 A x s) : term10 A x s.
Proof. exact (h1). Qed.
Lemma lem4386882 {A : Type'} (x : A) (s : A -> Prop) : term17 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem4386887 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4386851 A B s f x) (@lem4386850 A B s f x)). Qed.
Lemma lem4386888 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (@lem4386887 A B s f x). Qed.
Lemma lem4386890 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term18 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4386891 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term19 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4386890 _2963 g t e g' t' e'). Qed.
Lemma lem4386892 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term20 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4386891 _2963 g t e g' t'). Qed.
Lemma lem4386893 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term21 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4386892 _2963 g t e g'). Qed.
Lemma lem4386894 {B : Type'} (g : Prop) (t : B) (e : B) : term21 B g t e.
Proof. exact (@lem4386893 B g t e). Qed.
Lemma lem4386895 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term22 A B s f x.
Proof. exact (@lem4386894 B (@IN A x s) (f x) (@ARB B)). Qed.
Lemma lem4386896 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : term23 A B s f x g'.
Proof. exact (@lem4386895 A B s f x g'). Qed.
Lemma lem4386897 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : (term23 A B s f x g') = (term24 A B s f x g').
Proof. exact (eq_refl (term23 A B s f x g')). Qed.
Lemma lem4386898 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : term24 A B s f x g'.
Proof. exact (EQ_MP (@lem4386897 A B s f x g') (@lem4386896 A B s f x g')). Qed.
Lemma lem4386899 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) : term25 A B s f x g' t'.
Proof. exact (@lem4386898 A B s f x g' t'). Qed.
Lemma lem4386900 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) : (term25 A B s f x g' t') = (term26 A B s f x g' t').
Proof. exact (eq_refl (term25 A B s f x g' t')). Qed.
Lemma lem4386901 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) : term26 A B s f x g' t'.
Proof. exact (EQ_MP (@lem4386900 A B s f x g' t') (@lem4386899 A B s f x g' t')). Qed.
Lemma lem4386902 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : term27 A B s f x g' t' e'.
Proof. exact (@lem4386901 A B s f x g' t' e'). Qed.
Lemma lem4386903 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : (term27 A B s f x g' t' e') = (term28 A B s f x g' t' e').
Proof. exact (eq_refl (term27 A B s f x g' t' e')). Qed.
Lemma lem4386904 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : term28 A B s f x g' t' e'.
Proof. exact (EQ_MP (@lem4386903 A B s f x g' t' e') (@lem4386902 A B s f x g' t' e')). Qed.
Lemma lem4386906 {A : Type'} (x : A) (s : A -> Prop) (h1 : term10 A x s) : (@IN A x s) = False.
Proof. exact (@lem4386882 A x s (@lem4386881 A x s h1)). Qed.
Lemma lem4386907 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t' : B) (e' : B) : term29 A B s f x t' e'.
Proof. exact (@lem4386904 A B s f x False t' e'). Qed.
Lemma lem4386908 {A B : Type'} (f : A -> B) (t' : B) (e' : B) (x : A) (s : A -> Prop) (h1 : term10 A x s) : term30 A B s f x t' e'.
Proof. exact (@lem4386907 A B s f x t' e' (@lem4386906 A x s h1)). Qed.
Lemma lem4386912 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4386913 {A B : Type'} (f : A -> B) (x : A) : term31 A B f x.
Proof. exact (fun h0 : False => @lem4386912 A B f x). Qed.
Lemma lem4386914 {A B : Type'} (f : A -> B) (e' : B) (x : A) (s : A -> Prop) (h1 : term10 A x s) : term32 A B s f x e'.
Proof. exact (@lem4386908 A B f (f x) e' x s h1). Qed.
Lemma lem4386915 {A B : Type'} (f : A -> B) (e' : B) (x : A) (s : A -> Prop) (h1 : term10 A x s) : term33 A B s f x e'.
Proof. exact (@lem4386914 A B f e' x s h1 (@lem4386913 A B f x)). Qed.
Lemma lem4386921 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4386922 {B : Type'} : term34 B.
Proof. exact (fun h0 : ~ False => @lem4386921 B). Qed.
Lemma lem4386923 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term10 A x s) : term35 A B s f x.
Proof. exact (@lem4386915 A B f (@ARB B) x s h1). Qed.
Lemma lem4386924 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term10 A x s) : (term5 A B s f x) = (term36 A B f x).
Proof. exact (@lem4386923 A B f x s h1 (@lem4386922 B)). Qed.
Lemma lem4386926 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4386927 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem4386926 B t1 t2). Qed.
Lemma lem4386928 {A B : Type'} (f : A -> B) (x : A) : (term36 A B f x) = (@ARB B).
Proof. exact (@lem4386927 B (f x) (@ARB B)). Qed.
Lemma lem4386929 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term10 A x s) : (term5 A B s f x) = (@ARB B).
Proof. exact (TRANS (@lem4386924 A B f x s h1) (@lem4386928 A B f x)). Qed.
Lemma lem4386930 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term10 A x s) : (@RESTRICTION A B s f x) = (@ARB B).
Proof. exact (TRANS (@lem4386888 A B s f x) (@lem4386929 A B f x s h1)). Qed.
Lemma lem4386931 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4386932 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term10 A x s) : (term37 A B s f x) = (@eq B (@ARB B)).
Proof. exact (MK_COMB (@lem4386931 B) (@lem4386930 A B f x s h1)). Qed.
Lemma lem4386933 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4386934 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term10 A x s) : ((@RESTRICTION A B s f x) = (@ARB B)) = ((@ARB B) = (@ARB B)).
Proof. exact (MK_COMB (@lem4386932 A B f x s h1) (@lem4386933 B)). Qed.
Lemma lem4386936 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4386937 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4386936 B x). Qed.
Lemma lem4386938 {B : Type'} : ((@ARB B) = (@ARB B)) = True.
Proof. exact (@lem4386937 B (@ARB B)). Qed.
Lemma lem4386939 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term10 A x s) : ((@RESTRICTION A B s f x) = (@ARB B)) = True.
Proof. exact (TRANS (@lem4386934 A B f x s h1) (@lem4386938 B)). Qed.
Lemma lem4386940 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term38 A B s f x.
Proof. exact (fun h0 : term10 A x s => @lem4386939 A B f x s h0). Qed.
Lemma lem4386941 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : term39 A B f x s.
Proof. exact (@lem4386880 A B f x s True). Qed.
Lemma lem4386942 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term40 A B s f x) = (term41 A x s).
Proof. exact (@lem4386941 A B f x s (@lem4386940 A B s f x)). Qed.
Lemma lem4386944 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4386945 {A : Type'} (x : A) (s : A -> Prop) : (term41 A x s) = True.
Proof. exact (@lem4386944 (term10 A x s)). Qed.
Lemma lem4386946 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term40 A B s f x) = True.
Proof. exact (TRANS (@lem4386942 A B f x s) (@lem4386945 A x s)). Qed.
Lemma lem4386947 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term42 A B s f) = (term43 A).
Proof. exact (fun_ext (fun x : A => @lem4386946 A B s f x)). Qed.
Lemma lem4386948 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4386949 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term44 A B s f) = (term45 A).
Proof. exact (MK_COMB (@lem4386948 A) (@lem4386947 A B s f)). Qed.
Lemma lem4386951 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4386952 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (@lem4386951 A t). Qed.
Lemma lem4386953 {A : Type'} : (term45 A) = True.
Proof. exact (@lem4386952 A True). Qed.
Lemma lem4386954 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term44 A B s f) = True.
Proof. exact (TRANS (@lem4386949 A B s f) (@lem4386953 A)). Qed.
Lemma lem4386955 {A B : Type'} (s : A -> Prop) : (term47 A B s) = (term48 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4386954 A B s f)). Qed.
Lemma lem4386956 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4386957 {A B : Type'} (s : A -> Prop) : (term49 A B s) = (term50 A B).
Proof. exact (MK_COMB (@lem4386956 A B) (@lem4386955 A B s)). Qed.
Lemma lem4386959 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4386960 {A B : Type'} (t : Prop) : (term51 A B t) = t.
Proof. exact (@lem4386959 (A -> B) t). Qed.
Lemma lem4386961 {A B : Type'} : (term50 A B) = True.
Proof. exact (@lem4386960 A B True). Qed.
Lemma lem4386962 {A B : Type'} (s : A -> Prop) : (term49 A B s) = True.
Proof. exact (TRANS (@lem4386957 A B s) (@lem4386961 A B)). Qed.
Lemma lem4386963 {A B : Type'} : (term52 A B) = (term53 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4386962 A B s)). Qed.
Lemma lem4386964 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4386965 {A B : Type'} : (term54 A B) = (term55 A).
Proof. exact (MK_COMB (@lem4386964 A) (@lem4386963 A B)). Qed.
Lemma lem4386967 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4386968 {A : Type'} (t : Prop) : (term56 A t) = t.
Proof. exact (@lem4386967 (A -> Prop) t). Qed.
Lemma lem4386969 {A : Type'} : (term55 A) = True.
Proof. exact (@lem4386968 A True). Qed.
Lemma lem4386970 {A B : Type'} : (term54 A B) = True.
Proof. exact (TRANS (@lem4386965 A B) (@lem4386969 A)). Qed.
Lemma lem4386971 {A B : Type'} : True = (term54 A B).
Proof. exact (SYM (@lem4386970 A B)). Qed.
Lemma lem4386972 {A B : Type'} : term54 A B.
Proof. exact (EQ_MP (@lem4386971 A B) (@lem0)). Qed.
