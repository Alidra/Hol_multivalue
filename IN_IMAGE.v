Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_IMAGE_term_abbrevs.
Require Import CONJ_SYM_spec.
Require Import IMAGE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem3205877 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem3199546 A B s). Qed.
Lemma lem3205878 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem3205879 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem3205878 A B s) (@lem3205877 A B s)). Qed.
Lemma lem3205880 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem3205879 A B s f). Qed.
Lemma lem3205881 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = ((@IMAGE A B f s) = (term3 A B s f)).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem3205907 {_83095 : Type'} : term4 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3205908 {_83095 : Type'} (p : _83095 -> Prop) : term5 _83095 p.
Proof. exact (@lem3205907 _83095 p). Qed.
Lemma lem3205909 {_83095 : Type'} (p : _83095 -> Prop) : (term5 _83095 p) = (term6 _83095 p).
Proof. exact (eq_refl (term5 _83095 p)). Qed.
Lemma lem3205910 {_83095 : Type'} (p : _83095 -> Prop) : term6 _83095 p.
Proof. exact (EQ_MP (@lem3205909 _83095 p) (@lem3205908 _83095 p)). Qed.
Lemma lem3205911 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term7 _83095 p x.
Proof. exact (@lem3205910 _83095 p x). Qed.
Lemma lem3205912 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 p x) = ((term8 _83095 x p) = (p x)).
Proof. exact (eq_refl (term7 _83095 p x)). Qed.
Lemma lem3205921 (t1 : Prop) : term9 t1.
Proof. exact (@lem539 t1). Qed.
Lemma lem3205922 (t1 : Prop) : (term9 t1) = (term10 t1).
Proof. exact (eq_refl (term9 t1)). Qed.
Lemma lem3205923 (t1 : Prop) : term10 t1.
Proof. exact (EQ_MP (@lem3205922 t1) (@lem3205921 t1)). Qed.
Lemma lem3205924 (t1 : Prop) (t2 : Prop) : term11 t1 t2.
Proof. exact (@lem3205923 t1 t2). Qed.
Lemma lem3205925 (t2 : Prop) (t1 : Prop) : (term11 t1 t2) = ((t1 /\ t2) = (t2 /\ t1)).
Proof. exact (eq_refl (term11 t1 t2)). Qed.
Lemma lem3205948 (t2 : Prop) (t1 : Prop) : (t1 /\ t2) = (t2 /\ t1).
Proof. exact (EQ_MP (@lem3205925 t2 t1) (@lem3205924 t1 t2)). Qed.
Lemma lem3205949 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x : A) : (term12 A B y f x s) = (term13 A B s y f x).
Proof. exact (@lem3205948 (@IN A x s) (y = (f x))). Qed.
Lemma lem3205950 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) : (term14 A B y f s) = (term15 A B s y f).
Proof. exact (fun_ext (fun x : A => @lem3205949 A B s y f x)). Qed.
Lemma lem3205951 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3205952 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) : (term16 A B y f s) = (term17 A B s y f).
Proof. exact (MK_COMB (@lem3205951 A) (@lem3205950 A B s y f)). Qed.
Lemma lem3205953 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term18 A B y f s) = (term18 A B y f s).
Proof. exact (eq_refl (term18 A B y f s)). Qed.
Lemma lem3205954 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) : ((term19 A B y f s) = (term16 A B y f s)) = ((term19 A B y f s) = (term17 A B s y f)).
Proof. exact (MK_COMB (@lem3205953 A B y f s) (@lem3205952 A B s y f)). Qed.
Lemma lem3205955 {A B : Type'} (s : A -> Prop) (y : B) : (term20 A B y s) = (term21 A B s y).
Proof. exact (fun_ext (fun f : A -> B => @lem3205954 A B s y f)). Qed.
Lemma lem3205956 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3205957 {A B : Type'} (s : A -> Prop) (y : B) : (term22 A B y s) = (term23 A B s y).
Proof. exact (MK_COMB (@lem3205956 A B) (@lem3205955 A B s y)). Qed.
Lemma lem3205958 {A B : Type'} (y : B) : (term24 A B y) = (term25 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3205957 A B s y)). Qed.
Lemma lem3205959 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3205960 {A B : Type'} (y : B) : (term26 A B y) = (term27 A B y).
Proof. exact (MK_COMB (@lem3205959 A) (@lem3205958 A B y)). Qed.
Lemma lem3205961 {A B : Type'} : (term28 A B) = (term29 A B).
Proof. exact (fun_ext (fun y : B => @lem3205960 A B y)). Qed.
Lemma lem3205962 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3205963 {A B : Type'} : (term30 A B) = (term31 A B).
Proof. exact (MK_COMB (@lem3205962 B) (@lem3205961 A B)). Qed.
Lemma lem3205964 {A B : Type'} : (term31 A B) = (term30 A B).
Proof. exact (SYM (@lem3205963 A B)). Qed.
Lemma lem3205980 {A B : Type'} (s : A -> Prop) (f : A -> B) : (@IMAGE A B f s) = (term3 A B s f).
Proof. exact (EQ_MP (@lem3205881 A B s f) (@lem3205880 A B s f)). Qed.
Lemma lem3205981 {A B : Type'} (s : A -> Prop) (f : A -> B) : (@IMAGE A B f s) = (term3 A B s f).
Proof. exact (@lem3205980 A B s f). Qed.
Lemma lem3205994 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem3205995 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term19 A B y f s) = (term32 A B y s f).
Proof. exact (MK_COMB (@lem3205994 B y) (@lem3205981 A B s f)). Qed.
Lemma lem3205997 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3205912 _83095 p x) (@lem3205911 _83095 p x)). Qed.
Lemma lem3205998 {B : Type'} (p : B -> Prop) (x : B) : (term8 B x p) = (p x).
Proof. exact (@lem3205997 B p x). Qed.
Lemma lem3205999 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term33 A B y s f) = (term34 A B s f y).
Proof. exact (@lem3205998 B (term35 A B s f) y). Qed.
Lemma lem3206000 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) : (term34 A B s f y) = (term17 A B s y f).
Proof. exact (eq_refl (term34 A B s f y)). Qed.
Lemma lem3206001 {B : Type'} (GEN_PVAR_7 : B) : (@SETSPEC B GEN_PVAR_7) = (@SETSPEC B GEN_PVAR_7).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_7)). Qed.
Lemma lem3206002 {A B : Type'} (GEN_PVAR_7 : B) (s : A -> Prop) (y : B) (f : A -> B) : (term36 A B GEN_PVAR_7 s f y) = (term37 A B GEN_PVAR_7 s y f).
Proof. exact (MK_COMB (@lem3206001 B GEN_PVAR_7) (@lem3206000 A B s y f)). Qed.
Lemma lem3206003 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3206004 {A B : Type'} (GEN_PVAR_7 : B) (s : A -> Prop) (f : A -> B) (y : B) : (term38 A B GEN_PVAR_7 s f y) = (term39 A B GEN_PVAR_7 s f y).
Proof. exact (MK_COMB (@lem3206002 A B GEN_PVAR_7 s y f) (@lem3206003 B y)). Qed.
Lemma lem3206005 {A B : Type'} (GEN_PVAR_7 : B) (s : A -> Prop) (f : A -> B) : (term40 A B GEN_PVAR_7 s f) = (term41 A B GEN_PVAR_7 s f).
Proof. exact (fun_ext (fun y : B => @lem3206004 A B GEN_PVAR_7 s f y)). Qed.
Lemma lem3206006 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3206007 {A B : Type'} (GEN_PVAR_7 : B) (s : A -> Prop) (f : A -> B) : (term42 A B GEN_PVAR_7 s f) = (term43 A B GEN_PVAR_7 s f).
Proof. exact (MK_COMB (@lem3206006 B) (@lem3206005 A B GEN_PVAR_7 s f)). Qed.
Lemma lem3206008 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term44 A B s f) = (term45 A B s f).
Proof. exact (fun_ext (fun GEN_PVAR_7 : B => @lem3206007 A B GEN_PVAR_7 s f)). Qed.
Lemma lem3206009 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3206010 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term46 A B s f) = (term3 A B s f).
Proof. exact (MK_COMB (@lem3206009 B) (@lem3206008 A B s f)). Qed.
Lemma lem3206011 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem3206012 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term33 A B y s f) = (term32 A B y s f).
Proof. exact (MK_COMB (@lem3206011 B y) (@lem3206010 A B s f)). Qed.
Lemma lem3206013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3206014 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term47 A B y s f) = (term48 A B y s f).
Proof. exact (MK_COMB (@lem3206013) (@lem3206012 A B y s f)). Qed.
Lemma lem3206015 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) : (term34 A B s f y) = (term17 A B s y f).
Proof. exact (eq_refl (term34 A B s f y)). Qed.
Lemma lem3206016 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) : ((term33 A B y s f) = (term34 A B s f y)) = ((term32 A B y s f) = (term17 A B s y f)).
Proof. exact (MK_COMB (@lem3206014 A B y s f) (@lem3206015 A B s y f)). Qed.
Lemma lem3206017 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) : (term32 A B y s f) = (term17 A B s y f).
Proof. exact (EQ_MP (@lem3206016 A B s y f) (@lem3205999 A B s f y)). Qed.
Lemma lem3206026 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) : (term19 A B y f s) = (term17 A B s y f).
Proof. exact (TRANS (@lem3205995 A B y s f) (@lem3206017 A B s y f)). Qed.
Lemma lem3206027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3206028 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) : (term18 A B y f s) = (term49 A B s y f).
Proof. exact (MK_COMB (@lem3206027) (@lem3206026 A B s y f)). Qed.
Lemma lem3206037 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) : (term17 A B s y f) = (term17 A B s y f).
Proof. exact (eq_refl (term17 A B s y f)). Qed.
Lemma lem3206038 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) : ((term19 A B y f s) = (term17 A B s y f)) = ((term17 A B s y f) = (term17 A B s y f)).
Proof. exact (MK_COMB (@lem3206028 A B s y f) (@lem3206037 A B s y f)). Qed.
Lemma lem3206040 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3206041 (x : Prop) : (x = x) = True.
Proof. exact (@lem3206040 Prop x). Qed.
Lemma lem3206042 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) : ((term17 A B s y f) = (term17 A B s y f)) = True.
Proof. exact (@lem3206041 (term17 A B s y f)). Qed.
Lemma lem3206043 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) : ((term19 A B y f s) = (term17 A B s y f)) = True.
Proof. exact (TRANS (@lem3206038 A B s y f) (@lem3206042 A B s y f)). Qed.
Lemma lem3206044 {A B : Type'} (s : A -> Prop) (y : B) : (term21 A B s y) = (term50 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3206043 A B s y f)). Qed.
Lemma lem3206045 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3206046 {A B : Type'} (s : A -> Prop) (y : B) : (term23 A B s y) = (term51 A B).
Proof. exact (MK_COMB (@lem3206045 A B) (@lem3206044 A B s y)). Qed.
Lemma lem3206048 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3206049 {A B : Type'} (t : Prop) : (term53 A B t) = t.
Proof. exact (@lem3206048 (A -> B) t). Qed.
Lemma lem3206050 {A B : Type'} : (term51 A B) = True.
Proof. exact (@lem3206049 A B True). Qed.
Lemma lem3206051 {A B : Type'} (s : A -> Prop) (y : B) : (term23 A B s y) = True.
Proof. exact (TRANS (@lem3206046 A B s y) (@lem3206050 A B)). Qed.
Lemma lem3206052 {A B : Type'} (y : B) : (term25 A B y) = (term54 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3206051 A B s y)). Qed.
Lemma lem3206053 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3206054 {A B : Type'} (y : B) : (term27 A B y) = (term55 A).
Proof. exact (MK_COMB (@lem3206053 A) (@lem3206052 A B y)). Qed.
Lemma lem3206056 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3206057 {A : Type'} (t : Prop) : (term56 A t) = t.
Proof. exact (@lem3206056 (A -> Prop) t). Qed.
Lemma lem3206058 {A : Type'} : (term55 A) = True.
Proof. exact (@lem3206057 A True). Qed.
Lemma lem3206059 {A B : Type'} (y : B) : (term27 A B y) = True.
Proof. exact (TRANS (@lem3206054 A B y) (@lem3206058 A)). Qed.
Lemma lem3206060 {A B : Type'} : (term29 A B) = (term57 B).
Proof. exact (fun_ext (fun y : B => @lem3206059 A B y)). Qed.
Lemma lem3206061 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3206062 {A B : Type'} : (term31 A B) = (term58 B).
Proof. exact (MK_COMB (@lem3206061 B) (@lem3206060 A B)). Qed.
Lemma lem3206064 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3206065 {B : Type'} (t : Prop) : (term52 B t) = t.
Proof. exact (@lem3206064 B t). Qed.
Lemma lem3206066 {B : Type'} : (term58 B) = True.
Proof. exact (@lem3206065 B True). Qed.
Lemma lem3206067 {A B : Type'} : (term31 A B) = True.
Proof. exact (TRANS (@lem3206062 A B) (@lem3206066 B)). Qed.
Lemma lem3206068 {A B : Type'} : True = (term31 A B).
Proof. exact (SYM (@lem3206067 A B)). Qed.
Lemma lem3206069 {A B : Type'} : term31 A B.
Proof. exact (EQ_MP (@lem3206068 A B) (@lem0)). Qed.
Lemma lem3206070 {A B : Type'} : term30 A B.
Proof. exact (EQ_MP (@lem3205964 A B) (@lem3206069 A B)). Qed.
