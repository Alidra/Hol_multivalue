Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_RECURSION_term_abbrevs.
Require Import ITSET_spec.
Require Import SET_RECURSION_LEMMA_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Require Import thm9425_spec.
Lemma lem3815974 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem3815975 {A B : Type'} (f : type1411 A B) (h1 : term0 A B) : term1 A B f.
Proof. exact (@lem3815974 A B h1 f). Qed.
Lemma lem3815976 {A B : Type'} (f : type1411 A B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem3815977 {A B : Type'} (f : type1411 A B) (h1 : term0 A B) : term2 A B f.
Proof. exact (EQ_MP (@lem3815976 A B f) (@lem3815975 A B f h1)). Qed.
Lemma lem3815978 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term0 A B) : term3 A B f b.
Proof. exact (@lem3815977 A B f h1 b). Qed.
Lemma lem3815979 {A B : Type'} (b : B) (f : type1411 A B) : (term3 A B f b) = (term4 A B b f).
Proof. exact (eq_refl (term3 A B f b)). Qed.
Lemma lem3815980 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term0 A B) : term4 A B b f.
Proof. exact (EQ_MP (@lem3815979 A B b f) (@lem3815978 A B f b h1)). Qed.
Lemma lem3815981 {A B : Type'} (f : type1411 A B) (h1 : term5 A B f) : term5 A B f.
Proof. exact (h1). Qed.
Lemma lem3815982 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term5 A B f) (h2 : term0 A B) : term6 A B b f.
Proof. exact (@lem3815980 A B b f h2 (@lem3815981 A B f h1)). Qed.
Lemma lem3815983 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term5 A B f) : term7 A B b f.
Proof. exact (fun h0 : term0 A B => @lem3815982 A B b f h1 h0). Qed.
Lemma lem3815984 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem3815985 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term5 A B f) (h2 : term0 A B) : term6 A B b f.
Proof. exact (@lem3815983 A B b f h1 (@lem3815984 A B h2)). Qed.
Lemma lem3815986 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term0 A B) : term4 A B b f.
Proof. exact (fun h0 : term5 A B f => @lem3815985 A B b f h0 h1). Qed.
Lemma lem3815987 {A B : Type'} (b : B) (h1 : term0 A B) : term8 A B b.
Proof. exact (fun f : type1411 A B => @lem3815986 A B b f h1). Qed.
Lemma lem3815988 {A B : Type'} (h1 : term0 A B) : term9 A B.
Proof. exact (fun b : B => @lem3815987 A B b h1). Qed.
Lemma lem3815989 {A B : Type'} : term10 A B.
Proof. exact (fun h0 : term0 A B => @lem3815988 A B h0). Qed.
Lemma lem3815990 {A B : Type'} : term9 A B.
Proof. exact (@lem3815989 A B (@lem3814895 A B)). Qed.
Lemma lem3815991 {A B : Type'} (b : B) : term11 A B b.
Proof. exact (@lem3815990 A B b). Qed.
Lemma lem3815992 {A B : Type'} (b : B) : (term11 A B b) = (term8 A B b).
Proof. exact (eq_refl (term11 A B b)). Qed.
Lemma lem3815993 {A B : Type'} (b : B) : term8 A B b.
Proof. exact (EQ_MP (@lem3815992 A B b) (@lem3815991 A B b)). Qed.
Lemma lem3815994 {A B : Type'} (b : B) (f : type1411 A B) : term12 A B b f.
Proof. exact (@lem3815993 A B b f). Qed.
Lemma lem3815995 {A B : Type'} (b : B) (f : type1411 A B) : (term12 A B b f) = (term4 A B b f).
Proof. exact (eq_refl (term12 A B b f)). Qed.
Lemma lem3815997 {_99240 _99241 : Type'} (b : _99240) : term13 _99240 _99241 b.
Proof. exact (@lem3815973 _99240 _99241 b). Qed.
Lemma lem3815998 {_99240 _99241 : Type'} (b : _99240) : (term13 _99240 _99241 b) = (term14 _99240 _99241 b).
Proof. exact (eq_refl (term13 _99240 _99241 b)). Qed.
Lemma lem3815999 {_99240 _99241 : Type'} (b : _99240) : term14 _99240 _99241 b.
Proof. exact (EQ_MP (@lem3815998 _99240 _99241 b) (@lem3815997 _99240 _99241 b)). Qed.
Lemma lem3816000 {_99240 _99241 : Type'} (b : _99240) (f : type1467 _99240 _99241) : term15 _99240 _99241 b f.
Proof. exact (@lem3815999 _99240 _99241 b f). Qed.
Lemma lem3816001 {_99240 _99241 : Type'} (b : _99240) (f : type1467 _99240 _99241) : (term15 _99240 _99241 b f) = (term16 _99240 _99241 b f).
Proof. exact (eq_refl (term15 _99240 _99241 b f)). Qed.
Lemma lem3816002 {_99240 _99241 : Type'} (b : _99240) (f : type1467 _99240 _99241) : term16 _99240 _99241 b f.
Proof. exact (EQ_MP (@lem3816001 _99240 _99241 b f) (@lem3816000 _99240 _99241 b f)). Qed.
Lemma lem3816003 {_99240 _99241 : Type'} (b : _99240) (f : type1467 _99240 _99241) (s : _99241 -> Prop) : term17 _99240 _99241 b f s.
Proof. exact (@lem3816002 _99240 _99241 b f s). Qed.
Lemma lem3816004 {_99240 _99241 : Type'} (b : _99240) (f : type1467 _99240 _99241) (s : _99241 -> Prop) : (term17 _99240 _99241 b f s) = ((@ITSET _99240 _99241 f s b) = (term18 _99240 _99241 b f s)).
Proof. exact (eq_refl (term17 _99240 _99241 b f s)). Qed.
Lemma lem3816006 {A B : Type'} (f : type1411 A B) (h1 : term5 A B f) : term5 A B f.
Proof. exact (h1). Qed.
Lemma lem3816012 {_99240 _99241 : Type'} (b : _99240) (f : type1467 _99240 _99241) (s : _99241 -> Prop) : (@ITSET _99240 _99241 f s b) = (term18 _99240 _99241 b f s).
Proof. exact (EQ_MP (@lem3816004 _99240 _99241 b f s) (@lem3816003 _99240 _99241 b f s)). Qed.
Lemma lem3816013 {A B : Type'} (b : B) (f : type1411 A B) (s : A -> Prop) : (@ITSET B A f s b) = (term19 A B b f s).
Proof. exact (@lem3816012 B A b f s). Qed.
Lemma lem3816014 {A B : Type'} (b : B) (f : type1411 A B) : (@ITSET B A f (@EMPTY A) b) = (term20 A B b f).
Proof. exact (@lem3816013 A B b f (@EMPTY A)). Qed.
Lemma lem3816031 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3816032 {A B : Type'} (b : B) (f : type1411 A B) : (term21 A B f b) = (term22 A B b f).
Proof. exact (MK_COMB (@lem3816031 B) (@lem3816014 A B b f)). Qed.
Lemma lem3816033 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3816034 {A B : Type'} (f : type1411 A B) (b : B) : ((@ITSET B A f (@EMPTY A) b) = b) = ((term20 A B b f) = b).
Proof. exact (MK_COMB (@lem3816032 A B b f) (@lem3816033 B b)). Qed.
Lemma lem3816037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3816038 {A B : Type'} (f : type1411 A B) (b : B) : (term23 A B f b) = (term24 A B f b).
Proof. exact (MK_COMB (@lem3816037) (@lem3816034 A B f b)). Qed.
Lemma lem3816052 {_99240 _99241 : Type'} (b : _99240) (f : type1467 _99240 _99241) (s : _99241 -> Prop) : (@ITSET _99240 _99241 f s b) = (term18 _99240 _99241 b f s).
Proof. exact (EQ_MP (@lem3816004 _99240 _99241 b f s) (@lem3816003 _99240 _99241 b f s)). Qed.
Lemma lem3816053 {A B : Type'} (b : B) (f : type1411 A B) (s : A -> Prop) : (@ITSET B A f s b) = (term19 A B b f s).
Proof. exact (@lem3816052 B A b f s). Qed.
Lemma lem3816054 {A B : Type'} (b : B) (f : type1411 A B) (x : A) (s : A -> Prop) : (term25 A B f x s b) = (term26 A B b f x s).
Proof. exact (@lem3816053 A B b f (@INSERT A x s)). Qed.
Lemma lem3816071 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3816072 {A B : Type'} (b : B) (f : type1411 A B) (x : A) (s : A -> Prop) : (term27 A B f x s b) = (term28 A B b f x s).
Proof. exact (MK_COMB (@lem3816071 B) (@lem3816054 A B b f x s)). Qed.
Lemma lem3816074 {_99240 _99241 : Type'} (b : _99240) (f : type1467 _99240 _99241) (s : _99241 -> Prop) : (@ITSET _99240 _99241 f s b) = (term18 _99240 _99241 b f s).
Proof. exact (EQ_MP (@lem3816004 _99240 _99241 b f s) (@lem3816003 _99240 _99241 b f s)). Qed.
Lemma lem3816075 {A B : Type'} (b : B) (f : type1411 A B) (s : A -> Prop) : (@ITSET B A f s b) = (term19 A B b f s).
Proof. exact (@lem3816074 B A b f s). Qed.
Lemma lem3816092 {A B : Type'} (x : A) (s : A -> Prop) : (term29 A B x s) = (term29 A B x s).
Proof. exact (eq_refl (term29 A B x s)). Qed.
Lemma lem3816093 {A B : Type'} (x : A) (b : B) (f : type1411 A B) (s : A -> Prop) : (term30 A B x f s b) = (term31 A B x b f s).
Proof. exact (MK_COMB (@lem3816092 A B x s) (@lem3816075 A B b f s)). Qed.
Lemma lem3816095 {_99240 _99241 : Type'} (b : _99240) (f : type1467 _99240 _99241) (s : _99241 -> Prop) : (@ITSET _99240 _99241 f s b) = (term18 _99240 _99241 b f s).
Proof. exact (EQ_MP (@lem3816004 _99240 _99241 b f s) (@lem3816003 _99240 _99241 b f s)). Qed.
Lemma lem3816096 {A B : Type'} (b : B) (f : type1411 A B) (s : A -> Prop) : (@ITSET B A f s b) = (term19 A B b f s).
Proof. exact (@lem3816095 B A b f s). Qed.
Lemma lem3816113 {A B : Type'} (f : type1411 A B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem3816114 {A B : Type'} (x : A) (b : B) (f : type1411 A B) (s : A -> Prop) : (term32 A B x f s b) = (term33 A B x b f s).
Proof. exact (MK_COMB (@lem3816113 A B f x) (@lem3816096 A B b f s)). Qed.
Lemma lem3816115 {A B : Type'} (x : A) (b : B) (f : type1411 A B) (s : A -> Prop) : (term34 A B x f s b) = (term35 A B x b f s).
Proof. exact (MK_COMB (@lem3816093 A B x b f s) (@lem3816114 A B x b f s)). Qed.
Lemma lem3816116 {A B : Type'} (x : A) (b : B) (f : type1411 A B) (s : A -> Prop) : ((term25 A B f x s b) = (term34 A B x f s b)) = ((term26 A B b f x s) = (term35 A B x b f s)).
Proof. exact (MK_COMB (@lem3816072 A B b f x s) (@lem3816115 A B x b f s)). Qed.
Lemma lem3816119 {A : Type'} (s : A -> Prop) : (term36 A s) = (term36 A s).
Proof. exact (eq_refl (term36 A s)). Qed.
Lemma lem3816120 {A B : Type'} (x : A) (b : B) (f : type1411 A B) (s : A -> Prop) : (term37 A B x f s b) = (term38 A B x b f s).
Proof. exact (MK_COMB (@lem3816119 A s) (@lem3816116 A B x b f s)). Qed.
Lemma lem3816123 {A B : Type'} (x : A) (b : B) (f : type1411 A B) : (term39 A B x f b) = (term40 A B x b f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3816120 A B x b f s)). Qed.
Lemma lem3816124 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3816125 {A B : Type'} (x : A) (b : B) (f : type1411 A B) : (term41 A B x f b) = (term42 A B x b f).
Proof. exact (MK_COMB (@lem3816124 A) (@lem3816123 A B x b f)). Qed.
Lemma lem3816130 {A B : Type'} (b : B) (f : type1411 A B) : (term43 A B f b) = (term44 A B b f).
Proof. exact (fun_ext (fun x : A => @lem3816125 A B x b f)). Qed.
Lemma lem3816131 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3816132 {A B : Type'} (b : B) (f : type1411 A B) : (term45 A B f b) = (term46 A B b f).
Proof. exact (MK_COMB (@lem3816131 A) (@lem3816130 A B b f)). Qed.
Lemma lem3816137 {A B : Type'} (b : B) (f : type1411 A B) : (term47 A B f b) = (term48 A B b f).
Proof. exact (MK_COMB (@lem3816038 A B f b) (@lem3816132 A B b f)). Qed.
Lemma lem3816140 {A B : Type'} (f : type1411 A B) (b : B) : (term48 A B b f) = (term47 A B f b).
Proof. exact (SYM (@lem3816137 A B b f)). Qed.
Lemma lem3816141 {A B : Type'} (P : type165 A B) : (term49 A B P) = (ex P).
Proof. exact (@lem9425 (type685 A B) P). Qed.
Lemma lem3816142 {A B : Type'} (b : B) (f : type1411 A B) : (term50 A B b f) = (term6 A B b f).
Proof. exact (@lem3816141 A B (term51 A B b f)). Qed.
Lemma lem3816143 {A B : Type'} (b : B) (f : type1411 A B) : (term50 A B b f) = (term48 A B b f).
Proof. exact (eq_refl (term50 A B b f)). Qed.
Lemma lem3816144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3816145 {A B : Type'} (b : B) (f : type1411 A B) : (term52 A B b f) = (term53 A B b f).
Proof. exact (MK_COMB (@lem3816144) (@lem3816143 A B b f)). Qed.
Lemma lem3816146 {A B : Type'} (b : B) (f : type1411 A B) : (term6 A B b f) = (term6 A B b f).
Proof. exact (eq_refl (term6 A B b f)). Qed.
Lemma lem3816147 {A B : Type'} (b : B) (f : type1411 A B) : ((term50 A B b f) = (term6 A B b f)) = ((term48 A B b f) = (term6 A B b f)).
Proof. exact (MK_COMB (@lem3816145 A B b f) (@lem3816146 A B b f)). Qed.
Lemma lem3816148 {A B : Type'} (b : B) (f : type1411 A B) : (term48 A B b f) = (term6 A B b f).
Proof. exact (EQ_MP (@lem3816147 A B b f) (@lem3816142 A B b f)). Qed.
Lemma lem3816149 {A B : Type'} (b : B) (f : type1411 A B) : (term6 A B b f) = (term48 A B b f).
Proof. exact (SYM (@lem3816148 A B b f)). Qed.
Lemma lem3816151 {A B : Type'} (b : B) (f : type1411 A B) : term4 A B b f.
Proof. exact (EQ_MP (@lem3815995 A B b f) (@lem3815994 A B b f)). Qed.
Lemma lem3816152 {A B : Type'} (b : B) (f : type1411 A B) : term4 A B b f.
Proof. exact (@lem3816151 A B b f). Qed.
Lemma lem3816153 {A B : Type'} (x : A) (f : type1411 A B) (h1 : term5 A B f) : term54 A B f x.
Proof. exact (@lem3816006 A B f h1 x). Qed.
Lemma lem3816154 {A B : Type'} (f : type1411 A B) (x : A) : (term54 A B f x) = (term55 A B f x).
Proof. exact (eq_refl (term54 A B f x)). Qed.
Lemma lem3816155 {A B : Type'} (x : A) (f : type1411 A B) (h1 : term5 A B f) : term55 A B f x.
Proof. exact (EQ_MP (@lem3816154 A B f x) (@lem3816153 A B x f h1)). Qed.
Lemma lem3816156 {A B : Type'} (x : A) (y : A) (f : type1411 A B) (h1 : term5 A B f) : term56 A B f x y.
Proof. exact (@lem3816155 A B x f h1 y). Qed.
Lemma lem3816157 {A B : Type'} (y : A) (f : type1411 A B) (x : A) : (term56 A B f x y) = (term57 A B y f x).
Proof. exact (eq_refl (term56 A B f x y)). Qed.
Lemma lem3816158 {A B : Type'} (y : A) (x : A) (f : type1411 A B) (h1 : term5 A B f) : term57 A B y f x.
Proof. exact (EQ_MP (@lem3816157 A B y f x) (@lem3816156 A B x y f h1)). Qed.
Lemma lem3816159 {A B : Type'} (y : A) (x : A) (s : B) (f : type1411 A B) (h1 : term5 A B f) : term58 A B y f x s.
Proof. exact (@lem3816158 A B y x f h1 s). Qed.
Lemma lem3816160 {A B : Type'} (y : A) (f : type1411 A B) (x : A) (s : B) : (term58 A B y f x s) = (term59 A B y f x s).
Proof. exact (eq_refl (term58 A B y f x s)). Qed.
Lemma lem3816161 {A B : Type'} (y : A) (x : A) (s : B) (f : type1411 A B) (h1 : term5 A B f) : term59 A B y f x s.
Proof. exact (EQ_MP (@lem3816160 A B y f x s) (@lem3816159 A B y x s f h1)). Qed.
Lemma lem3816162 {A B : Type'} (y : A) (f : type1411 A B) (x : A) (s : B) : (term59 A B y f x s) = ((term59 A B y f x s) = True).
Proof. exact (@lem7 (term59 A B y f x s)). Qed.
Lemma lem3816177 {A B : Type'} (y : A) (x : A) (s : B) (f : type1411 A B) (h1 : term5 A B f) : (term59 A B y f x s) = True.
Proof. exact (EQ_MP (@lem3816162 A B y f x s) (@lem3816161 A B y x s f h1)). Qed.
Lemma lem3816178 {A B : Type'} (y : A) (x : A) (s : B) (f : type1411 A B) (h1 : term5 A B f) : (term59 A B y f x s) = True.
Proof. exact (@lem3816177 A B y x s f h1). Qed.
Lemma lem3816179 {A B : Type'} (y : A) (x : A) (f : type1411 A B) (h1 : term5 A B f) : (term60 A B y f x) = (term61 B).
Proof. exact (fun_ext (fun s : B => @lem3816178 A B y x s f h1)). Qed.
Lemma lem3816180 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3816181 {A B : Type'} (y : A) (x : A) (f : type1411 A B) (h1 : term5 A B f) : (term57 A B y f x) = (term62 B).
Proof. exact (MK_COMB (@lem3816180 B) (@lem3816179 A B y x f h1)). Qed.
Lemma lem3816183 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3816184 {B : Type'} (t : Prop) : (term63 B t) = t.
Proof. exact (@lem3816183 B t). Qed.
Lemma lem3816185 {B : Type'} : (term62 B) = True.
Proof. exact (@lem3816184 B True). Qed.
Lemma lem3816186 {A B : Type'} (y : A) (x : A) (f : type1411 A B) (h1 : term5 A B f) : (term57 A B y f x) = True.
Proof. exact (TRANS (@lem3816181 A B y x f h1) (@lem3816185 B)). Qed.
Lemma lem3816187 {A B : Type'} (x : A) (f : type1411 A B) (h1 : term5 A B f) : (term64 A B f x) = (term61 A).
Proof. exact (fun_ext (fun y : A => @lem3816186 A B y x f h1)). Qed.
Lemma lem3816188 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3816189 {A B : Type'} (x : A) (f : type1411 A B) (h1 : term5 A B f) : (term55 A B f x) = (term62 A).
Proof. exact (MK_COMB (@lem3816188 A) (@lem3816187 A B x f h1)). Qed.
Lemma lem3816191 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3816192 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (@lem3816191 A t). Qed.
Lemma lem3816193 {A : Type'} : (term62 A) = True.
Proof. exact (@lem3816192 A True). Qed.
Lemma lem3816194 {A B : Type'} (x : A) (f : type1411 A B) (h1 : term5 A B f) : (term55 A B f x) = True.
Proof. exact (TRANS (@lem3816189 A B x f h1) (@lem3816193 A)). Qed.
Lemma lem3816195 {A B : Type'} (f : type1411 A B) (h1 : term5 A B f) : (term65 A B f) = (term61 A).
Proof. exact (fun_ext (fun x : A => @lem3816194 A B x f h1)). Qed.
Lemma lem3816196 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3816197 {A B : Type'} (f : type1411 A B) (h1 : term5 A B f) : (term5 A B f) = (term62 A).
Proof. exact (MK_COMB (@lem3816196 A) (@lem3816195 A B f h1)). Qed.
Lemma lem3816199 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3816200 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (@lem3816199 A t). Qed.
Lemma lem3816201 {A : Type'} : (term62 A) = True.
Proof. exact (@lem3816200 A True). Qed.
Lemma lem3816202 {A B : Type'} (f : type1411 A B) (h1 : term5 A B f) : (term5 A B f) = True.
Proof. exact (TRANS (@lem3816197 A B f h1) (@lem3816201 A)). Qed.
Lemma lem3816203 {A B : Type'} (f : type1411 A B) (h1 : term5 A B f) : True = (term5 A B f).
Proof. exact (SYM (@lem3816202 A B f h1)). Qed.
Lemma lem3816204 {A B : Type'} (f : type1411 A B) (h1 : term5 A B f) : term5 A B f.
Proof. exact (EQ_MP (@lem3816203 A B f h1) (@lem0)). Qed.
Lemma lem3816205 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term5 A B f) : term6 A B b f.
Proof. exact (@lem3816152 A B b f (@lem3816204 A B f h1)). Qed.
Lemma lem3816206 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term5 A B f) : term48 A B b f.
Proof. exact (EQ_MP (@lem3816149 A B b f) (@lem3816205 A B b f h1)). Qed.
Lemma lem3816207 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term5 A B f) : term47 A B f b.
Proof. exact (EQ_MP (@lem3816140 A B f b) (@lem3816206 A B b f h1)). Qed.
Lemma lem3816208 {A B : Type'} (f : type1411 A B) (b : B) : term66 A B f b.
Proof. exact (fun h0 : term5 A B f => @lem3816207 A B b f h0). Qed.
Lemma lem3816213 {A B : Type'} (f : type1411 A B) : term67 A B f.
Proof. exact (fun b : B => @lem3816208 A B f b). Qed.
Lemma lem3816218 {A B : Type'} : term68 A B.
Proof. exact (fun f : type1411 A B => @lem3816213 A B f). Qed.
