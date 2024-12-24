Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_EXTENSIONAL_UNDEFINED_term_abbrevs.
Require Import IN_EXTENSIONAL_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem4382933 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4382932 A B s). Qed.
Lemma lem4382934 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4382935 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4382934 A B s) (@lem4382933 A B s)). Qed.
Lemma lem4382936 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem4382935 A B s f). Qed.
Lemma lem4382937 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = ((term3 A B f s) = (term4 A B s f)).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem4382954 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term5 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4382955 (p : Prop) (q : Prop) (p' : Prop) : term6 p q p'.
Proof. exact (fun q' : Prop => @lem4382954 p q p' q'). Qed.
Lemma lem4382956 (p : Prop) (q : Prop) : term7 p q.
Proof. exact (fun p' : Prop => @lem4382955 p q p'). Qed.
Lemma lem4382957 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term8 A B s f x.
Proof. exact (@lem4382956 (term9 A B f x s) ((f x) = (@ARB B))). Qed.
Lemma lem4382958 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : term10 A B s f x p'.
Proof. exact (@lem4382957 A B s f x p'). Qed.
Lemma lem4382959 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : (term10 A B s f x p') = (term11 A B s f x p').
Proof. exact (eq_refl (term10 A B s f x p')). Qed.
Lemma lem4382960 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : term11 A B s f x p'.
Proof. exact (EQ_MP (@lem4382959 A B s f x p') (@lem4382958 A B s f x p')). Qed.
Lemma lem4382961 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term12 A B s f x p' q'.
Proof. exact (@lem4382960 A B s f x p' q'). Qed.
Lemma lem4382962 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : (term12 A B s f x p' q') = (term13 A B s f x p' q').
Proof. exact (eq_refl (term12 A B s f x p' q')). Qed.
Lemma lem4382963 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term13 A B s f x p' q'.
Proof. exact (EQ_MP (@lem4382962 A B s f x p' q') (@lem4382961 A B s f x p' q')). Qed.
Lemma lem4382967 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term3 A B f s) = (term4 A B s f).
Proof. exact (EQ_MP (@lem4382937 A B s f) (@lem4382936 A B s f)). Qed.
Lemma lem4382968 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term3 A B f s) = (term4 A B s f).
Proof. exact (@lem4382967 A B s f). Qed.
Lemma lem4383000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4383001 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term14 A B f s) = (term15 A B s f).
Proof. exact (MK_COMB (@lem4383000) (@lem4382968 A B s f)). Qed.
Lemma lem4383033 {A : Type'} (x : A) (s : A -> Prop) : (term16 A x s) = (term16 A x s).
Proof. exact (eq_refl (term16 A x s)). Qed.
Lemma lem4383034 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term9 A B f x s) = (term17 A B f x s).
Proof. exact (MK_COMB (@lem4383001 A B s f) (@lem4383033 A x s)). Qed.
Lemma lem4383068 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term18 A B f x s q'.
Proof. exact (@lem4382963 A B s f x (term17 A B f x s) q'). Qed.
Lemma lem4383069 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term19 A B f x s q'.
Proof. exact (@lem4383068 A B f x s q' (@lem4383034 A B f x s)). Qed.
Lemma lem4383070 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : term17 A B f x s.
Proof. exact (h1). Qed.
Lemma lem4383071 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : term16 A x s.
Proof. exact (proj2 (@lem4383070 A B f x s h1)). Qed.
Lemma lem4383072 {A : Type'} (x : A) (s : A -> Prop) : term20 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem4383074 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : term4 A B s f.
Proof. exact (proj1 (@lem4383070 A B f x s h1)). Qed.
Lemma lem4383075 {A B : Type'} (x' : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : term21 A B s f x'.
Proof. exact (@lem4383074 A B f x s h1 x'). Qed.
Lemma lem4383076 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) : (term21 A B s f x') = (term22 A B s f x').
Proof. exact (eq_refl (term21 A B s f x')). Qed.
Lemma lem4383077 {A B : Type'} (x' : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : term22 A B s f x'.
Proof. exact (EQ_MP (@lem4383076 A B s f x') (@lem4383075 A B x' f x s h1)). Qed.
Lemma lem4383078 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term16 A x' s) : term16 A x' s.
Proof. exact (h1). Qed.
Lemma lem4383079 {A B : Type'} (x' : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term16 A x' s) (h2 : term17 A B f x s) : (f x') = (@ARB B).
Proof. exact (@lem4383077 A B x' f x s h2 (@lem4383078 A x' s h1)). Qed.
Lemma lem4383088 {A B : Type'} (x' : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : term22 A B s f x'.
Proof. exact (fun h0 : term16 A x' s => @lem4383079 A B x' f x s h0 h1). Qed.
Lemma lem4383089 {A B : Type'} (x' : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : term22 A B s f x'.
Proof. exact (@lem4383088 A B x' f x s h1). Qed.
Lemma lem4383090 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : term22 A B s f x.
Proof. exact (@lem4383089 A B x f x s h1). Qed.
Lemma lem4383092 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : (@IN A x s) = False.
Proof. exact (@lem4383072 A x s (@lem4383071 A B f x s h1)). Qed.
Lemma lem4383093 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4383094 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : (term16 A x s) = (~ False).
Proof. exact (MK_COMB (@lem4383093) (@lem4383092 A B f x s h1)). Qed.
Lemma lem4383096 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4383097 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : (term16 A x s) = True.
Proof. exact (TRANS (@lem4383094 A B f x s h1) (@lem4383096)). Qed.
Lemma lem4383098 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : True = (term16 A x s).
Proof. exact (SYM (@lem4383097 A B f x s h1)). Qed.
Lemma lem4383099 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : term16 A x s.
Proof. exact (EQ_MP (@lem4383098 A B f x s h1) (@lem0)). Qed.
Lemma lem4383100 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : (f x) = (@ARB B).
Proof. exact (@lem4383090 A B f x s h1 (@lem4383099 A B f x s h1)). Qed.
Lemma lem4383101 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4383102 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : (term23 A B f x) = (@eq B (@ARB B)).
Proof. exact (MK_COMB (@lem4383101 B) (@lem4383100 A B f x s h1)). Qed.
Lemma lem4383103 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4383104 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : ((f x) = (@ARB B)) = ((@ARB B) = (@ARB B)).
Proof. exact (MK_COMB (@lem4383102 A B f x s h1) (@lem4383103 B)). Qed.
Lemma lem4383106 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4383107 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4383106 B x). Qed.
Lemma lem4383108 {B : Type'} : ((@ARB B) = (@ARB B)) = True.
Proof. exact (@lem4383107 B (@ARB B)). Qed.
Lemma lem4383109 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term17 A B f x s) : ((f x) = (@ARB B)) = True.
Proof. exact (TRANS (@lem4383104 A B f x s h1) (@lem4383108 B)). Qed.
Lemma lem4383110 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term24 A B s f x.
Proof. exact (fun h0 : term17 A B f x s => @lem4383109 A B f x s h0). Qed.
Lemma lem4383111 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : term25 A B f x s.
Proof. exact (@lem4383069 A B f x s True). Qed.
Lemma lem4383112 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term26 A B s f x) = (term27 A B f x s).
Proof. exact (@lem4383111 A B f x s (@lem4383110 A B s f x)). Qed.
Lemma lem4383114 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4383115 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term27 A B f x s) = True.
Proof. exact (@lem4383114 (term17 A B f x s)). Qed.
Lemma lem4383116 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term26 A B s f x) = True.
Proof. exact (TRANS (@lem4383112 A B f x s) (@lem4383115 A B f x s)). Qed.
Lemma lem4383117 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term28 A B s f) = (term29 A).
Proof. exact (fun_ext (fun x : A => @lem4383116 A B s f x)). Qed.
Lemma lem4383118 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4383119 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term30 A B s f) = (term31 A).
Proof. exact (MK_COMB (@lem4383118 A) (@lem4383117 A B s f)). Qed.
Lemma lem4383121 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4383122 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (@lem4383121 A t). Qed.
Lemma lem4383123 {A : Type'} : (term31 A) = True.
Proof. exact (@lem4383122 A True). Qed.
Lemma lem4383124 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term30 A B s f) = True.
Proof. exact (TRANS (@lem4383119 A B s f) (@lem4383123 A)). Qed.
Lemma lem4383125 {A B : Type'} (s : A -> Prop) : (term33 A B s) = (term34 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4383124 A B s f)). Qed.
Lemma lem4383126 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4383127 {A B : Type'} (s : A -> Prop) : (term35 A B s) = (term36 A B).
Proof. exact (MK_COMB (@lem4383126 A B) (@lem4383125 A B s)). Qed.
Lemma lem4383129 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4383130 {A B : Type'} (t : Prop) : (term37 A B t) = t.
Proof. exact (@lem4383129 (A -> B) t). Qed.
Lemma lem4383131 {A B : Type'} : (term36 A B) = True.
Proof. exact (@lem4383130 A B True). Qed.
Lemma lem4383132 {A B : Type'} (s : A -> Prop) : (term35 A B s) = True.
Proof. exact (TRANS (@lem4383127 A B s) (@lem4383131 A B)). Qed.
Lemma lem4383133 {A B : Type'} : (term38 A B) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4383132 A B s)). Qed.
Lemma lem4383134 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4383135 {A B : Type'} : (term40 A B) = (term41 A).
Proof. exact (MK_COMB (@lem4383134 A) (@lem4383133 A B)). Qed.
Lemma lem4383137 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4383138 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (@lem4383137 (A -> Prop) t). Qed.
Lemma lem4383139 {A : Type'} : (term41 A) = True.
Proof. exact (@lem4383138 A True). Qed.
Lemma lem4383140 {A B : Type'} : (term40 A B) = True.
Proof. exact (TRANS (@lem4383135 A B) (@lem4383139 A)). Qed.
Lemma lem4383141 {A B : Type'} : True = (term40 A B).
Proof. exact (SYM (@lem4383140 A B)). Qed.
Lemma lem4383142 {A B : Type'} : term40 A B.
Proof. exact (EQ_MP (@lem4383141 A B) (@lem0)). Qed.
