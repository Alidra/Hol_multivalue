Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_SND_CROSS_term_abbrevs.
Require Import CONJ_SYM_spec.
Require Import CROSS_EMPTY_spec.
Require Import EXISTS_IN_CROSS_spec.
Require Import EXTENSION_spec.
Require Import IMAGE_CLAUSES_spec.
Require Import IN_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16439_spec.
Require Import thm16440_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm48213_spec.
Require Import thm48214_spec.
Lemma lem4355958 {_104151 _104152 : Type'} (P : type1223 _104151 _104152) : term0 _104151 _104152 P.
Proof. exact (@lem4334566 _104151 _104152 P). Qed.
Lemma lem4355959 {_104151 _104152 : Type'} (P : type1223 _104151 _104152) : (term0 _104151 _104152 P) = (term1 _104151 _104152 P).
Proof. exact (eq_refl (term0 _104151 _104152 P)). Qed.
Lemma lem4355960 {_104151 _104152 : Type'} (P : type1223 _104151 _104152) : term1 _104151 _104152 P.
Proof. exact (EQ_MP (@lem4355959 _104151 _104152 P) (@lem4355958 _104151 _104152 P)). Qed.
Lemma lem4355961 {_104151 _104152 : Type'} (P : type1223 _104151 _104152) (s : _104152 -> Prop) : term2 _104151 _104152 P s.
Proof. exact (@lem4355960 _104151 _104152 P s). Qed.
Lemma lem4355962 {_104151 _104152 : Type'} (s : _104152 -> Prop) (P : type1223 _104151 _104152) : (term2 _104151 _104152 P s) = (term3 _104151 _104152 s P).
Proof. exact (eq_refl (term2 _104151 _104152 P s)). Qed.
Lemma lem4355963 {_104151 _104152 : Type'} (s : _104152 -> Prop) (P : type1223 _104151 _104152) : term3 _104151 _104152 s P.
Proof. exact (EQ_MP (@lem4355962 _104151 _104152 s P) (@lem4355961 _104151 _104152 P s)). Qed.
Lemma lem4355964 {_104151 _104152 : Type'} (s : _104152 -> Prop) (P : type1223 _104151 _104152) (t : _104151 -> Prop) : term4 _104151 _104152 s P t.
Proof. exact (@lem4355963 _104151 _104152 s P t). Qed.
Lemma lem4355965 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term4 _104151 _104152 s P t) = ((term5 _104151 _104152 s t P) = (term6 _104151 _104152 s t P)).
Proof. exact (eq_refl (term4 _104151 _104152 s P t)). Qed.
Lemma lem4355967 (t1 : Prop) : term7 t1.
Proof. exact (@lem539 t1). Qed.
Lemma lem4355968 (t1 : Prop) : (term7 t1) = (term8 t1).
Proof. exact (eq_refl (term7 t1)). Qed.
Lemma lem4355969 (t1 : Prop) : term8 t1.
Proof. exact (EQ_MP (@lem4355968 t1) (@lem4355967 t1)). Qed.
Lemma lem4355970 (t1 : Prop) (t2 : Prop) : term9 t1 t2.
Proof. exact (@lem4355969 t1 t2). Qed.
Lemma lem4355971 (t2 : Prop) (t1 : Prop) : (term9 t1 t2) = ((t1 /\ t2) = (t2 /\ t1)).
Proof. exact (eq_refl (term9 t1 t2)). Qed.
Lemma lem4355973 {A B : Type'} (y : B) : term10 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4355974 {A B : Type'} (y : B) : (term10 A B y) = (term11 A B y).
Proof. exact (eq_refl (term10 A B y)). Qed.
Lemma lem4355975 {A B : Type'} (y : B) : term11 A B y.
Proof. exact (EQ_MP (@lem4355974 A B y) (@lem4355973 A B y)). Qed.
Lemma lem4355976 {A B : Type'} (y : B) (s : A -> Prop) : term12 A B y s.
Proof. exact (@lem4355975 A B y s). Qed.
Lemma lem4355977 {A B : Type'} (y : B) (s : A -> Prop) : (term12 A B y s) = (term13 A B y s).
Proof. exact (eq_refl (term12 A B y s)). Qed.
Lemma lem4355978 {A B : Type'} (y : B) (s : A -> Prop) : term13 A B y s.
Proof. exact (EQ_MP (@lem4355977 A B y s) (@lem4355976 A B y s)). Qed.
Lemma lem4355979 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term14 A B y s f.
Proof. exact (@lem4355978 A B y s f). Qed.
Lemma lem4355980 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term14 A B y s f) = ((term15 A B y f s) = (term16 A B y f s)).
Proof. exact (eq_refl (term14 A B y s f)). Qed.
Lemma lem4355982 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4355983 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem4355984 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (EQ_MP (@lem4355983 A s) (@lem4355982 A s)). Qed.
Lemma lem4355985 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term19 A s t.
Proof. exact (@lem4355984 A s t). Qed.
Lemma lem4355986 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = ((s = t) = (term20 A s t)).
Proof. exact (eq_refl (term19 A s t)). Qed.
Lemma lem4355988 {B : Type'} (_474 : B -> Prop) (_475 : Prop) (_476 : type686 B) (_477 : B -> Prop) : (term21 B _476 _475 _474 _477) = (term22 B _474 _475 _476 _477).
Proof. exact (@lem13473 (B -> Prop) _474 _475 _476 _477). Qed.
Lemma lem4355989 {A B : Type'} (_474 : B -> Prop) (_475 : Prop) (s : A -> Prop) (t : B -> Prop) (_477 : B -> Prop) : (term23 A B s t _475 _474 _477) = (term24 A B _474 _475 s t _477).
Proof. exact (@lem4355988 B _474 _475 (term25 A B s t) _477). Qed.
Lemma lem4355990 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term26 A B s t) = (term27 A B s t).
Proof. exact (@lem4355989 A B (@EMPTY B) (s = (@EMPTY A)) s t t). Qed.
Lemma lem4355991 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term28 A B s t) = ((term29 A B s t) = t).
Proof. exact (eq_refl (term28 A B s t)). Qed.
Lemma lem4355992 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (eq_refl (term30 A s)). Qed.
Lemma lem4355993 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term31 A B s t) = (term32 A B s t).
Proof. exact (MK_COMB (@lem4355992 A s) (@lem4355991 A B s t)). Qed.
Lemma lem4355994 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term33 A B s t) = ((term29 A B s t) = (@EMPTY B)).
Proof. exact (eq_refl (term33 A B s t)). Qed.
Lemma lem4355995 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (eq_refl (term34 A s)). Qed.
Lemma lem4355996 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term35 A B s t) = (term36 A B s t).
Proof. exact (MK_COMB (@lem4355995 A s) (@lem4355994 A B s t)). Qed.
Lemma lem4355997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4355998 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term37 A B s t) = (term38 A B s t).
Proof. exact (MK_COMB (@lem4355997) (@lem4355996 A B s t)). Qed.
Lemma lem4355999 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term27 A B s t) = (term39 A B s t).
Proof. exact (MK_COMB (@lem4355998 A B s t) (@lem4355993 A B s t)). Qed.
Lemma lem4356000 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term26 A B s t) = ((term29 A B s t) = (term40 A B s t)).
Proof. exact (eq_refl (term26 A B s t)). Qed.
Lemma lem4356001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4356002 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term41 A B s t) = (term42 A B s t).
Proof. exact (MK_COMB (@lem4356001) (@lem4356000 A B s t)). Qed.
Lemma lem4356003 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : ((term26 A B s t) = (term27 A B s t)) = (((term29 A B s t) = (term40 A B s t)) = (term39 A B s t)).
Proof. exact (MK_COMB (@lem4356002 A B s t) (@lem4355999 A B s t)). Qed.
Lemma lem4356004 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : ((term29 A B s t) = (term40 A B s t)) = (term39 A B s t).
Proof. exact (EQ_MP (@lem4356003 A B s t) (@lem4355990 A B s t)). Qed.
Lemma lem4356005 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term39 A B s t) = ((term29 A B s t) = (term40 A B s t)).
Proof. exact (SYM (@lem4356004 A B s t)). Qed.
Lemma lem4356006 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4356023 {A : Type'} (s : A -> Prop) (h1 : term43 A s) : term43 A s.
Proof. exact (h1). Qed.
Lemma lem4356042 {_103872 B : Type'} : term44 _103872 B.
Proof. exact (proj2 (@lem4327078 Prop _103872 Prop B)). Qed.
Lemma lem4356043 {_103872 B : Type'} (t : B -> Prop) : term45 _103872 B t.
Proof. exact (@lem4356042 _103872 B t). Qed.
Lemma lem4356044 {_103872 B : Type'} (t : B -> Prop) : (term45 _103872 B t) = ((@CROSS B _103872 (@EMPTY _103872) t) = (@EMPTY (prod _103872 B))).
Proof. exact (eq_refl (term45 _103872 B t)). Qed.
Lemma lem4356053 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4356054 {A B : Type'} : (@CROSS B A) = (@CROSS B A).
Proof. exact (eq_refl (@CROSS B A)). Qed.
Lemma lem4356055 {A B : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@CROSS B A s) = (@CROSS B A (@EMPTY A)).
Proof. exact (MK_COMB (@lem4356054 A B) (@lem4356053 A s h1)). Qed.
Lemma lem4356056 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4356057 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@CROSS B A s t) = (@CROSS B A (@EMPTY A) t).
Proof. exact (MK_COMB (@lem4356055 A B s h1) (@lem4356056 B t)). Qed.
Lemma lem4356059 {_103872 B : Type'} (t : B -> Prop) : (@CROSS B _103872 (@EMPTY _103872) t) = (@EMPTY (prod _103872 B)).
Proof. exact (EQ_MP (@lem4356044 _103872 B t) (@lem4356043 _103872 B t)). Qed.
Lemma lem4356060 {A B : Type'} (t : B -> Prop) : (@CROSS B A (@EMPTY A) t) = (@EMPTY (prod A B)).
Proof. exact (@lem4356059 A B t). Qed.
Lemma lem4356061 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@CROSS B A s t) = (@EMPTY (prod A B)).
Proof. exact (TRANS (@lem4356057 A B t s h1) (@lem4356060 A B t)). Qed.
Lemma lem4356062 {A B : Type'} : (@IMAGE (prod A B) B (@snd A B)) = (@IMAGE (prod A B) B (@snd A B)).
Proof. exact (eq_refl (@IMAGE (prod A B) B (@snd A B))). Qed.
Lemma lem4356063 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term29 A B s t) = (@IMAGE (prod A B) B (@snd A B) (@EMPTY (prod A B))).
Proof. exact (MK_COMB (@lem4356062 A B) (@lem4356061 A B t s h1)). Qed.
Lemma lem4356065 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481).
Proof. exact (proj1 (@lem3366870 _87477 _87481 (@el _87477) f (@el (_87477 -> Prop)))). Qed.
Lemma lem4356066 {A B : Type'} (f : type1208 A B) : (@IMAGE (prod A B) B f (@EMPTY (prod A B))) = (@EMPTY B).
Proof. exact (@lem4356065 (prod A B) B f). Qed.
Lemma lem4356067 {A B : Type'} : (@IMAGE (prod A B) B (@snd A B) (@EMPTY (prod A B))) = (@EMPTY B).
Proof. exact (@lem4356066 A B (@snd A B)). Qed.
Lemma lem4356068 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term29 A B s t) = (@EMPTY B).
Proof. exact (TRANS (@lem4356063 A B t s h1) (@lem4356067 A B)). Qed.
Lemma lem4356069 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem4356070 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term46 A B s t) = (@eq (B -> Prop) (@EMPTY B)).
Proof. exact (MK_COMB (@lem4356069 B) (@lem4356068 A B t s h1)). Qed.
Lemma lem4356071 {B : Type'} : (@EMPTY B) = (@EMPTY B).
Proof. exact (eq_refl (@EMPTY B)). Qed.
Lemma lem4356072 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : ((term29 A B s t) = (@EMPTY B)) = ((@EMPTY B) = (@EMPTY B)).
Proof. exact (MK_COMB (@lem4356070 A B t s h1) (@lem4356071 B)). Qed.
Lemma lem4356074 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4356075 {B : Type'} (x : B -> Prop) : (x = x) = True.
Proof. exact (@lem4356074 (B -> Prop) x). Qed.
Lemma lem4356076 {B : Type'} : ((@EMPTY B) = (@EMPTY B)) = True.
Proof. exact (@lem4356075 B (@EMPTY B)). Qed.
Lemma lem4356077 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : ((term29 A B s t) = (@EMPTY B)) = True.
Proof. exact (TRANS (@lem4356072 A B t s h1) (@lem4356076 B)). Qed.
Lemma lem4356078 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : True = ((term29 A B s t) = (@EMPTY B)).
Proof. exact (SYM (@lem4356077 A B t s h1)). Qed.
Lemma lem4356110 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem4355986 A s t) (@lem4355985 A s t)). Qed.
Lemma lem4356111 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term20 B s t).
Proof. exact (@lem4356110 B s t). Qed.
Lemma lem4356112 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : ((term29 A B s t) = t) = (term47 A B s t).
Proof. exact (@lem4356111 B (term29 A B s t) t). Qed.
Lemma lem4356122 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem4355980 A B y f s) (@lem4355979 A B y s f)). Qed.
Lemma lem4356123 {A B : Type'} (y : B) (f : type1208 A B) (s : type1210 A B) : (term48 A B y f s) = (term49 A B y f s).
Proof. exact (@lem4356122 (prod A B) B y f s). Qed.
Lemma lem4356124 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term50 A B x s t) = (term51 A B x s t).
Proof. exact (@lem4356123 A B x (@snd A B) (@CROSS B A s t)). Qed.
Lemma lem4356135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4356136 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) : (term52 A B x s t) = (term53 A B x s t).
Proof. exact (MK_COMB (@lem4356135) (@lem4356124 A B x s t)). Qed.
Lemma lem4356137 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (@IN B x t).
Proof. exact (eq_refl (@IN B x t)). Qed.
Lemma lem4356138 {A B : Type'} (s : A -> Prop) (x : B) (t : B -> Prop) : ((term50 A B x s t) = (@IN B x t)) = ((term51 A B x s t) = (@IN B x t)).
Proof. exact (MK_COMB (@lem4356136 A B x s t) (@lem4356137 B x t)). Qed.
Lemma lem4356143 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term54 A B s t) = (term55 A B s t).
Proof. exact (fun_ext (fun x : B => @lem4356138 A B s x t)). Qed.
Lemma lem4356144 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4356145 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term47 A B s t) = (term56 A B s t).
Proof. exact (MK_COMB (@lem4356144 B) (@lem4356143 A B s t)). Qed.
Lemma lem4356150 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : ((term29 A B s t) = t) = (term56 A B s t).
Proof. exact (TRANS (@lem4356112 A B s t) (@lem4356145 A B s t)). Qed.
Lemma lem4356151 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term56 A B s t) = ((term29 A B s t) = t).
Proof. exact (SYM (@lem4356150 A B s t)). Qed.
Lemma lem4356165 (t2 : Prop) (t1 : Prop) : (t1 /\ t2) = (t2 /\ t1).
Proof. exact (EQ_MP (@lem4355971 t2 t1) (@lem4355970 t1 t2)). Qed.
Lemma lem4356166 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (x' : prod A B) : (term57 A B x x' s t) = (term58 A B s t x x').
Proof. exact (@lem4356165 (term59 A B x' s t) (x = (@snd A B x'))). Qed.
Lemma lem4356167 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term60 A B x s t) = (term61 A B s t x).
Proof. exact (fun_ext (fun x' : prod A B => @lem4356166 A B s t x x')). Qed.
Lemma lem4356168 {A B : Type'} : (@ex (prod A B)) = (@ex (prod A B)).
Proof. exact (eq_refl (@ex (prod A B))). Qed.
Lemma lem4356169 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term51 A B x s t) = (term62 A B s t x).
Proof. exact (MK_COMB (@lem4356168 A B) (@lem4356167 A B s t x)). Qed.
Lemma lem4356170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4356171 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term53 A B x s t) = (term63 A B s t x).
Proof. exact (MK_COMB (@lem4356170) (@lem4356169 A B s t x)). Qed.
Lemma lem4356172 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (@IN B x t).
Proof. exact (eq_refl (@IN B x t)). Qed.
Lemma lem4356173 {A B : Type'} (s : A -> Prop) (x : B) (t : B -> Prop) : ((term51 A B x s t) = (@IN B x t)) = ((term62 A B s t x) = (@IN B x t)).
Proof. exact (MK_COMB (@lem4356171 A B s t x) (@lem4356172 B x t)). Qed.
Lemma lem4356174 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term55 A B s t) = (term64 A B s t).
Proof. exact (fun_ext (fun x : B => @lem4356173 A B s x t)). Qed.
Lemma lem4356175 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4356176 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term56 A B s t) = (term65 A B s t).
Proof. exact (MK_COMB (@lem4356175 B) (@lem4356174 A B s t)). Qed.
Lemma lem4356177 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term65 A B s t) = (term56 A B s t).
Proof. exact (SYM (@lem4356176 A B s t)). Qed.
Lemma lem4356185 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term5 _104151 _104152 s t P) = (term6 _104151 _104152 s t P).
Proof. exact (EQ_MP (@lem4355965 _104151 _104152 s t P) (@lem4355964 _104151 _104152 s P t)). Qed.
Lemma lem4356186 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (P : type1210 A B) : (term66 A B s t P) = (term67 A B s t P).
Proof. exact (@lem4356185 B A s t P). Qed.
Lemma lem4356187 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term68 A B s t x) = (term69 A B s t x).
Proof. exact (@lem4356186 A B s t (term70 A B x)). Qed.
Lemma lem4356188 {A B : Type'} (x : B) (x' : prod A B) : (term71 A B x x') = (x = (@snd A B x')).
Proof. exact (eq_refl (term71 A B x x')). Qed.
Lemma lem4356189 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : B -> Prop) : (term72 A B x s t) = (term72 A B x s t).
Proof. exact (eq_refl (term72 A B x s t)). Qed.
Lemma lem4356190 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (x' : prod A B) : (term73 A B s t x x') = (term58 A B s t x x').
Proof. exact (MK_COMB (@lem4356189 A B x' s t) (@lem4356188 A B x x')). Qed.
Lemma lem4356191 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term74 A B s t x) = (term61 A B s t x).
Proof. exact (fun_ext (fun x' : prod A B => @lem4356190 A B s t x x')). Qed.
Lemma lem4356192 {A B : Type'} : (@ex (prod A B)) = (@ex (prod A B)).
Proof. exact (eq_refl (@ex (prod A B))). Qed.
Lemma lem4356193 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term68 A B s t x) = (term62 A B s t x).
Proof. exact (MK_COMB (@lem4356192 A B) (@lem4356191 A B s t x)). Qed.
Lemma lem4356194 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4356195 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term75 A B s t x) = (term63 A B s t x).
Proof. exact (MK_COMB (@lem4356194) (@lem4356193 A B s t x)). Qed.
Lemma lem4356196 {A B : Type'} (x : B) (x' : A) (y : B) : (term76 A B x x' y) = (x = (term77 A B x' y)).
Proof. exact (eq_refl (term76 A B x x' y)). Qed.
Lemma lem4356197 {B : Type'} (y : B) (t : B -> Prop) : (term78 B y t) = (term78 B y t).
Proof. exact (eq_refl (term78 B y t)). Qed.
Lemma lem4356198 {A B : Type'} (t : B -> Prop) (x : B) (x' : A) (y : B) : (term79 A B t x x' y) = (term80 A B t x x' y).
Proof. exact (MK_COMB (@lem4356197 B y t) (@lem4356196 A B x x' y)). Qed.
Lemma lem4356199 {A : Type'} (x : A) (s : A -> Prop) : (term78 A x s) = (term78 A x s).
Proof. exact (eq_refl (term78 A x s)). Qed.
Lemma lem4356200 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (x' : A) (y : B) : (term81 A B s t x x' y) = (term82 A B s t x x' y).
Proof. exact (MK_COMB (@lem4356199 A x' s) (@lem4356198 A B t x x' y)). Qed.
Lemma lem4356201 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (x' : A) : (term83 A B s t x x') = (term84 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4356200 A B s t x x' y)). Qed.
Lemma lem4356202 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4356203 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (x' : A) : (term85 A B s t x x') = (term86 A B s t x x').
Proof. exact (MK_COMB (@lem4356202 B) (@lem4356201 A B s t x x')). Qed.
Lemma lem4356204 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term87 A B s t x) = (term88 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4356203 A B s t x x')). Qed.
Lemma lem4356205 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4356206 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term69 A B s t x) = (term89 A B s t x).
Proof. exact (MK_COMB (@lem4356205 A) (@lem4356204 A B s t x)). Qed.
Lemma lem4356207 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : ((term68 A B s t x) = (term69 A B s t x)) = ((term62 A B s t x) = (term89 A B s t x)).
Proof. exact (MK_COMB (@lem4356195 A B s t x) (@lem4356206 A B s t x)). Qed.
Lemma lem4356208 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term62 A B s t x) = (term89 A B s t x).
Proof. exact (EQ_MP (@lem4356207 A B s t x) (@lem4356187 A B s t x)). Qed.
Lemma lem4356224 {A B : Type'} (x : A) (y : B) : (term77 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem4356225 {A B : Type'} (x : A) (y : B) : (term77 A B x y) = y.
Proof. exact (@lem4356224 A B x y). Qed.
Lemma lem4356226 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem4356227 {A B : Type'} (x : A) (x' : B) (y : B) : (x' = (term77 A B x y)) = (x' = y).
Proof. exact (MK_COMB (@lem4356226 B x') (@lem4356225 A B x y)). Qed.
Lemma lem4356230 {B : Type'} (y : B) (t : B -> Prop) : (term78 B y t) = (term78 B y t).
Proof. exact (eq_refl (term78 B y t)). Qed.
Lemma lem4356231 {A B : Type'} (x : A) (t : B -> Prop) (x' : B) (y : B) : (term80 A B t x' x y) = (term90 B t x' y).
Proof. exact (MK_COMB (@lem4356230 B y t) (@lem4356227 A B x x' y)). Qed.
Lemma lem4356234 {A : Type'} (x : A) (s : A -> Prop) : (term78 A x s) = (term78 A x s).
Proof. exact (eq_refl (term78 A x s)). Qed.
Lemma lem4356235 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (x' : B) (y : B) : (term82 A B s t x' x y) = (term91 A B x s t x' y).
Proof. exact (MK_COMB (@lem4356234 A x s) (@lem4356231 A B x t x' y)). Qed.
Lemma lem4356238 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (x' : B) : (term84 A B s t x' x) = (term92 A B x s t x').
Proof. exact (fun_ext (fun y : B => @lem4356235 A B x s t x' y)). Qed.
Lemma lem4356239 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4356240 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (x' : B) : (term86 A B s t x' x) = (term93 A B x s t x').
Proof. exact (MK_COMB (@lem4356239 B) (@lem4356238 A B x s t x')). Qed.
Lemma lem4356245 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term88 A B s t x) = (term94 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4356240 A B x' s t x)). Qed.
Lemma lem4356246 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4356247 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term89 A B s t x) = (term95 A B s t x).
Proof. exact (MK_COMB (@lem4356246 A) (@lem4356245 A B s t x)). Qed.
Lemma lem4356252 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term62 A B s t x) = (term95 A B s t x).
Proof. exact (TRANS (@lem4356208 A B s t x) (@lem4356247 A B s t x)). Qed.
Lemma lem4356253 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4356254 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term63 A B s t x) = (term96 A B s t x).
Proof. exact (MK_COMB (@lem4356253) (@lem4356252 A B s t x)). Qed.
Lemma lem4356255 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (@IN B x t).
Proof. exact (eq_refl (@IN B x t)). Qed.
Lemma lem4356256 {A B : Type'} (s : A -> Prop) (x : B) (t : B -> Prop) : ((term62 A B s t x) = (@IN B x t)) = ((term95 A B s t x) = (@IN B x t)).
Proof. exact (MK_COMB (@lem4356254 A B s t x) (@lem4356255 B x t)). Qed.
Lemma lem4356259 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term64 A B s t) = (term97 A B s t).
Proof. exact (fun_ext (fun x : B => @lem4356256 A B s x t)). Qed.
Lemma lem4356260 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4356261 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term65 A B s t) = (term98 A B s t).
Proof. exact (MK_COMB (@lem4356260 B) (@lem4356259 A B s t)). Qed.
Lemma lem4356266 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term98 A B s t) = (term65 A B s t).
Proof. exact (SYM (@lem4356261 A B s t)). Qed.
Lemma lem4356282 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4356283 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (@lem4356282 A s t). Qed.
Lemma lem4356284 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term99 A s).
Proof. exact (@lem4356283 A s (@EMPTY A)). Qed.
Lemma lem4356293 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4356294 {A : Type'} (s : A -> Prop) : (term43 A s) = (term100 A s).
Proof. exact (MK_COMB (@lem4356293) (@lem4356284 A s)). Qed.
Lemma lem4356295 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4356296 {A : Type'} (s : A -> Prop) : (term30 A s) = (term101 A s).
Proof. exact (MK_COMB (@lem4356295) (@lem4356294 A s)). Qed.
Lemma lem4356321 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term98 A B s t) = (term98 A B s t).
Proof. exact (eq_refl (term98 A B s t)). Qed.
Lemma lem4356322 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term102 A B s t) = (term103 A B s t).
Proof. exact (MK_COMB (@lem4356296 A s) (@lem4356321 A B s t)). Qed.
Lemma lem4356325 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term103 A B s t) = (term102 A B s t).
Proof. exact (SYM (@lem4356322 A B s t)). Qed.
Lemma lem4356335 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4356336 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4356335 A P x). Qed.
Lemma lem4356337 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4356336 A s x). Qed.
Lemma lem4356338 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4356339 {A : Type'} (s : A -> Prop) (x : A) : (term104 A x s) = (term105 A s x).
Proof. exact (MK_COMB (@lem4356338) (@lem4356337 A s x)). Qed.
Lemma lem4356341 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4356342 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4356341 A x). Qed.
Lemma lem4356343 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = ((s x) = False).
Proof. exact (MK_COMB (@lem4356339 A s x) (@lem4356342 A x)). Qed.
Lemma lem4356345 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4356346 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = False) = (term106 A s x).
Proof. exact (@lem4356345 (s x)). Qed.
Lemma lem4356347 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = (term106 A s x).
Proof. exact (TRANS (@lem4356343 A s x) (@lem4356346 A s x)). Qed.
Lemma lem4356348 {A : Type'} (s : A -> Prop) : (term107 A s) = (term108 A s).
Proof. exact (fun_ext (fun x : A => @lem4356347 A s x)). Qed.
Lemma lem4356349 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4356350 {A : Type'} (s : A -> Prop) : (term99 A s) = (term109 A s).
Proof. exact (MK_COMB (@lem4356349 A) (@lem4356348 A s)). Qed.
Lemma lem4356355 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4356356 {A : Type'} (s : A -> Prop) : (term100 A s) = (term110 A s).
Proof. exact (MK_COMB (@lem4356355) (@lem4356350 A s)). Qed.
Lemma lem4356357 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4356358 {A : Type'} (s : A -> Prop) : (term101 A s) = (term111 A s).
Proof. exact (MK_COMB (@lem4356357) (@lem4356356 A s)). Qed.
Lemma lem4356376 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4356377 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4356376 A P x). Qed.
Lemma lem4356378 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4356377 A s x). Qed.
Lemma lem4356379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4356380 {A : Type'} (s : A -> Prop) (x : A) : (term78 A x s) = (term112 A s x).
Proof. exact (MK_COMB (@lem4356379) (@lem4356378 A s x)). Qed.
Lemma lem4356384 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4356385 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4356384 B P x). Qed.
Lemma lem4356386 {B : Type'} (t : B -> Prop) (y : B) : (@IN B y t) = (t y).
Proof. exact (@lem4356385 B t y). Qed.
Lemma lem4356387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4356388 {B : Type'} (t : B -> Prop) (y : B) : (term78 B y t) = (term112 B t y).
Proof. exact (MK_COMB (@lem4356387) (@lem4356386 B t y)). Qed.
Lemma lem4356391 {B : Type'} (x : B) (y : B) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4356392 {B : Type'} (t : B -> Prop) (x : B) (y : B) : (term90 B t x y) = (term113 B t x y).
Proof. exact (MK_COMB (@lem4356388 B t y) (@lem4356391 B x y)). Qed.
Lemma lem4356395 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (y : B) : (term91 A B x s t x' y) = (term114 A B s x t x' y).
Proof. exact (MK_COMB (@lem4356380 A s x) (@lem4356392 B t x' y)). Qed.
Lemma lem4356398 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term92 A B x s t x') = (term115 A B s x t x').
Proof. exact (fun_ext (fun y : B => @lem4356395 A B s x t x' y)). Qed.
Lemma lem4356399 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4356400 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term93 A B x s t x') = (term116 A B s x t x').
Proof. exact (MK_COMB (@lem4356399 B) (@lem4356398 A B s x t x')). Qed.
Lemma lem4356405 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term94 A B s t x) = (term117 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4356400 A B s x' t x)). Qed.
Lemma lem4356406 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4356407 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term95 A B s t x) = (term118 A B s t x).
Proof. exact (MK_COMB (@lem4356406 A) (@lem4356405 A B s t x)). Qed.
Lemma lem4356412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4356413 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term96 A B s t x) = (term119 A B s t x).
Proof. exact (MK_COMB (@lem4356412) (@lem4356407 A B s t x)). Qed.
Lemma lem4356415 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4356416 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4356415 B P x). Qed.
Lemma lem4356417 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4356416 B t x). Qed.
Lemma lem4356418 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : ((term95 A B s t x) = (@IN B x t)) = ((term118 A B s t x) = (t x)).
Proof. exact (MK_COMB (@lem4356413 A B s t x) (@lem4356417 B t x)). Qed.
Lemma lem4356421 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term97 A B s t) = (term120 A B s t).
Proof. exact (fun_ext (fun x : B => @lem4356418 A B s t x)). Qed.
Lemma lem4356422 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4356423 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term98 A B s t) = (term121 A B s t).
Proof. exact (MK_COMB (@lem4356422 B) (@lem4356421 A B s t)). Qed.
Lemma lem4356428 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term103 A B s t) = (term122 A B s t).
Proof. exact (MK_COMB (@lem4356358 A s) (@lem4356423 A B s t)). Qed.
Lemma lem4356431 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term122 A B s t) = (term103 A B s t).
Proof. exact (SYM (@lem4356428 A B s t)). Qed.
Lemma lem4356433 (p : Prop) : p = (term123 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4356434 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term122 A B s t) = (term124 A B s t).
Proof. exact (@lem4356433 (term122 A B s t)). Qed.
Lemma lem4356435 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term124 A B s t) = (term122 A B s t).
Proof. exact (SYM (@lem4356434 A B s t)). Qed.
Lemma lem4356436 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term125 A B s t) : term125 A B s t.
Proof. exact (h1). Qed.
Lemma lem4356439 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term124 A B s t) : term124 A B s t.
Proof. exact (h1). Qed.
Lemma lem4356440 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term126 A B s t.
Proof. exact (fun h0 : term124 A B s t => @lem4356439 A B s t h0). Qed.
Lemma lem4356441 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term126 A B s t) : term126 A B s t.
Proof. exact (h1). Qed.
Lemma lem4356442 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term124 A B s t) : term124 A B s t.
Proof. exact (h1). Qed.
Lemma lem4356443 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term124 A B s t) (h2 : term126 A B s t) : term124 A B s t.
Proof. exact (@lem4356441 A B s t h2 (@lem4356442 A B s t h1)). Qed.
Lemma lem4356444 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term124 A B s t) : term127 A B s t.
Proof. exact (fun h0 : term126 A B s t => @lem4356443 A B s t h1 h0). Qed.
Lemma lem4356445 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term126 A B s t) : term126 A B s t.
Proof. exact (h1). Qed.
Lemma lem4356446 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term124 A B s t) (h2 : term126 A B s t) : term124 A B s t.
Proof. exact (@lem4356444 A B s t h1 (@lem4356445 A B s t h2)). Qed.
Lemma lem4356447 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term126 A B s t) : term126 A B s t.
Proof. exact (fun h0 : term124 A B s t => @lem4356446 A B s t h0 h1). Qed.
Lemma lem4356448 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term128 A B s t.
Proof. exact (fun h0 : term126 A B s t => @lem4356447 A B s t h0). Qed.
Lemma lem4356451 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term126 A B s t.
Proof. exact (@lem4356448 A B s t (@lem4356440 A B s t)). Qed.
Lemma lem4356452 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term126 A B s t.
Proof. exact (@lem4356451 A B s t). Qed.
Lemma lem4356462 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4356463 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term124 A B s t) = (term129 A B s t).
Proof. exact (@lem4356462 (term125 A B s t)). Qed.
Lemma lem4356465 (t : Prop) : (term130 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4356466 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term129 A B s t) = (term122 A B s t).
Proof. exact (@lem4356465 (term122 A B s t)). Qed.
Lemma lem4356469 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term124 A B s t) = (term122 A B s t).
Proof. exact (TRANS (@lem4356463 A B s t) (@lem4356466 A B s t)). Qed.
Lemma lem4356483 {A : Type'} (P : Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem4356484 {B : Type'} (P : Prop) (Q : B -> Prop) : (term131 B P Q) = (term132 B P Q).
Proof. exact (@lem4356483 B P Q). Qed.
Lemma lem4356485 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term133 A B s x t x') = (term134 A B s x t x').
Proof. exact (@lem4356484 B (s x) (term135 B t x')). Qed.
Lemma lem4356486 {B : Type'} (t : B -> Prop) (x : B) (y : B) : (term136 B t x y) = (term113 B t x y).
Proof. exact (eq_refl (term136 B t x y)). Qed.
Lemma lem4356487 {A : Type'} (s : A -> Prop) (x : A) : (term112 A s x) = (term112 A s x).
Proof. exact (eq_refl (term112 A s x)). Qed.
Lemma lem4356488 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (y : B) : (term137 A B s x t x' y) = (term114 A B s x t x' y).
Proof. exact (MK_COMB (@lem4356487 A s x) (@lem4356486 B t x' y)). Qed.
Lemma lem4356489 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term138 A B s x t x') = (term115 A B s x t x').
Proof. exact (fun_ext (fun y : B => @lem4356488 A B s x t x' y)). Qed.
Lemma lem4356490 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4356491 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term133 A B s x t x') = (term116 A B s x t x').
Proof. exact (MK_COMB (@lem4356490 B) (@lem4356489 A B s x t x')). Qed.
Lemma lem4356492 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4356493 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term139 A B s x t x') = (term140 A B s x t x').
Proof. exact (MK_COMB (@lem4356492) (@lem4356491 A B s x t x')). Qed.
Lemma lem4356494 {B : Type'} (t : B -> Prop) (x : B) (y : B) : (term136 B t x y) = (term113 B t x y).
Proof. exact (eq_refl (term136 B t x y)). Qed.
Lemma lem4356495 {B : Type'} (t : B -> Prop) (x : B) : (term141 B t x) = (term135 B t x).
Proof. exact (fun_ext (fun y : B => @lem4356494 B t x y)). Qed.
Lemma lem4356496 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4356497 {B : Type'} (t : B -> Prop) (x : B) : (term142 B t x) = (term143 B t x).
Proof. exact (MK_COMB (@lem4356496 B) (@lem4356495 B t x)). Qed.
Lemma lem4356498 {A : Type'} (s : A -> Prop) (x : A) : (term112 A s x) = (term112 A s x).
Proof. exact (eq_refl (term112 A s x)). Qed.
Lemma lem4356499 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term134 A B s x t x') = (term144 A B s x t x').
Proof. exact (MK_COMB (@lem4356498 A s x) (@lem4356497 B t x')). Qed.
Lemma lem4356500 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : ((term133 A B s x t x') = (term134 A B s x t x')) = ((term116 A B s x t x') = (term144 A B s x t x')).
Proof. exact (MK_COMB (@lem4356493 A B s x t x') (@lem4356499 A B s x t x')). Qed.
Lemma lem4356501 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term116 A B s x t x') = (term144 A B s x t x').
Proof. exact (EQ_MP (@lem4356500 A B s x t x') (@lem4356485 A B s x t x')). Qed.
Lemma lem4356534 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term117 A B s t x) = (term145 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4356501 A B s x' t x)). Qed.
Lemma lem4356535 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4356536 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term118 A B s t x) = (term146 A B s t x).
Proof. exact (MK_COMB (@lem4356535 A) (@lem4356534 A B s t x)). Qed.
Lemma lem4356558 {A : Type'} (P : A -> Prop) (Q : Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem16440 A P Q) (@lem16439 A P Q)). Qed.
Lemma lem4356559 {A : Type'} (P : A -> Prop) (Q : Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (@lem4356558 A P Q). Qed.
Lemma lem4356560 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term146 A B s t x) = (term149 A B s t x).
Proof. exact (@lem4356559 A s (term143 B t x)). Qed.
Lemma lem4356597 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term118 A B s t x) = (term149 A B s t x).
Proof. exact (TRANS (@lem4356536 A B s t x) (@lem4356560 A B s t x)). Qed.
Lemma lem4356598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4356599 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term119 A B s t x) = (term150 A B s t x).
Proof. exact (MK_COMB (@lem4356598) (@lem4356597 A B s t x)). Qed.
Lemma lem4356600 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4356601 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : ((term118 A B s t x) = (t x)) = ((term149 A B s t x) = (t x)).
Proof. exact (MK_COMB (@lem4356599 A B s t x) (@lem4356600 B t x)). Qed.
Lemma lem4356602 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term120 A B s t) = (term151 A B s t).
Proof. exact (fun_ext (fun x : B => @lem4356601 A B s t x)). Qed.
Lemma lem4356603 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4356604 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term121 A B s t) = (term152 A B s t).
Proof. exact (MK_COMB (@lem4356603 B) (@lem4356602 A B s t)). Qed.
Lemma lem4356609 {A : Type'} (s : A -> Prop) : (term111 A s) = (term111 A s).
Proof. exact (eq_refl (term111 A s)). Qed.
Lemma lem4356610 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term122 A B s t) = (term153 A B s t).
Proof. exact (MK_COMB (@lem4356609 A s) (@lem4356604 A B s t)). Qed.
Lemma lem4356613 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term124 A B s t) = (term153 A B s t).
Proof. exact (TRANS (@lem4356469 A B s t) (@lem4356610 A B s t)). Qed.
Lemma lem4356614 {A B : Type'} (t : B -> Prop) : (term154 A B t) = (term155 A B t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4356613 A B s t)). Qed.
Lemma lem4356615 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4356616 {A B : Type'} (t : B -> Prop) : (term156 A B t) = (term157 A B t).
Proof. exact (MK_COMB (@lem4356615 A) (@lem4356614 A B t)). Qed.
Lemma lem4356621 {A B : Type'} : (term158 A B) = (term159 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4356616 A B t)). Qed.
Lemma lem4356622 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4356631 {A B : Type'} : (term160 A B) = (term161 A B).
Proof. exact (MK_COMB (@lem4356622 B) (@lem4356621 A B)). Qed.
Lemma lem4356632 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4356637 {B : Type'} (t : B -> Prop) (x : B) (y : B) : (term113 B t x y) = (term113 B t x y).
Proof. exact (eq_refl (term113 B t x y)). Qed.
Lemma lem4356638 {B : Type'} (t : B -> Prop) (x : B) : (term135 B t x) = (term135 B t x).
Proof. exact (fun_ext (fun y : B => @lem4356637 B t x y)). Qed.
Lemma lem4356639 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4356640 {B : Type'} (t : B -> Prop) (x : B) : (term143 B t x) = (term143 B t x).
Proof. exact (MK_COMB (@lem4356639 B) (@lem4356638 B t x)). Qed.
Lemma lem4356641 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4356642 {A : Type'} (s : A -> Prop) : (term162 A s) = (term162 A s).
Proof. exact (fun_ext (fun x : A => @lem4356641 A s x)). Qed.
Lemma lem4356643 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4356644 {A : Type'} (s : A -> Prop) : (term163 A s) = (term163 A s).
Proof. exact (MK_COMB (@lem4356643 A) (@lem4356642 A s)). Qed.
Lemma lem4356645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4356646 {A : Type'} (s : A -> Prop) : (term164 A s) = (term164 A s).
Proof. exact (MK_COMB (@lem4356645) (@lem4356644 A s)). Qed.
Lemma lem4356647 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term149 A B s t x) = (term149 A B s t x).
Proof. exact (MK_COMB (@lem4356646 A s) (@lem4356640 B t x)). Qed.
Lemma lem4356648 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4356649 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term150 A B s t x) = (term150 A B s t x).
Proof. exact (MK_COMB (@lem4356648) (@lem4356647 A B s t x)). Qed.
Lemma lem4356650 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : ((term149 A B s t x) = (t x)) = ((term149 A B s t x) = (t x)).
Proof. exact (MK_COMB (@lem4356649 A B s t x) (@lem4356632 B t x)). Qed.
Lemma lem4356651 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term151 A B s t) = (term151 A B s t).
Proof. exact (fun_ext (fun x : B => @lem4356650 A B s t x)). Qed.
Lemma lem4356652 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4356653 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term152 A B s t) = (term152 A B s t).
Proof. exact (MK_COMB (@lem4356652 B) (@lem4356651 A B s t)). Qed.
Lemma lem4356656 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term106 A s x).
Proof. exact (eq_refl (term106 A s x)). Qed.
Lemma lem4356657 {A : Type'} (s : A -> Prop) : (term108 A s) = (term108 A s).
Proof. exact (fun_ext (fun x : A => @lem4356656 A s x)). Qed.
Lemma lem4356658 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4356659 {A : Type'} (s : A -> Prop) : (term109 A s) = (term109 A s).
Proof. exact (MK_COMB (@lem4356658 A) (@lem4356657 A s)). Qed.
Lemma lem4356660 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4356661 {A : Type'} (s : A -> Prop) : (term110 A s) = (term110 A s).
Proof. exact (MK_COMB (@lem4356660) (@lem4356659 A s)). Qed.
Lemma lem4356662 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4356663 {A : Type'} (s : A -> Prop) : (term111 A s) = (term111 A s).
Proof. exact (MK_COMB (@lem4356662) (@lem4356661 A s)). Qed.
Lemma lem4356664 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term153 A B s t) = (term153 A B s t).
Proof. exact (MK_COMB (@lem4356663 A s) (@lem4356653 A B s t)). Qed.
Lemma lem4356665 {A B : Type'} (t : B -> Prop) : (term155 A B t) = (term155 A B t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4356664 A B s t)). Qed.
Lemma lem4356666 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4356667 {A B : Type'} (t : B -> Prop) : (term157 A B t) = (term157 A B t).
Proof. exact (MK_COMB (@lem4356666 A) (@lem4356665 A B t)). Qed.
Lemma lem4356668 {A B : Type'} : (term159 A B) = (term159 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4356667 A B t)). Qed.
Lemma lem4356669 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4356670 {A B : Type'} : (term161 A B) = (term161 A B).
Proof. exact (MK_COMB (@lem4356669 B) (@lem4356668 A B)). Qed.
Lemma lem4356715 {A B : Type'} : (term160 A B) = (term161 A B).
Proof. exact (TRANS (@lem4356631 A B) (@lem4356670 A B)). Qed.
Lemma lem4356716 {A B : Type'} : (term161 A B) = (term160 A B).
Proof. exact (SYM (@lem4356715 A B)). Qed.
Lemma lem4356717 {A : Type'} (s : A -> Prop) (h1 : term110 A s) : term110 A s.
Proof. exact (h1). Qed.
Lemma lem4356719 (p : Prop) : p = (term123 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4356720 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : ((term149 A B s t x) = (t x)) = (term165 A B s t x).
Proof. exact (@lem4356719 ((term149 A B s t x) = (t x))). Qed.
Lemma lem4356721 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term165 A B s t x) = ((term149 A B s t x) = (t x)).
Proof. exact (SYM (@lem4356720 A B s t x)). Qed.
Lemma lem4356722 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term166 A B s t x) : term166 A B s t x.
Proof. exact (h1). Qed.
Lemma lem4356725 {A : Type'} (s : A -> Prop) (x : A) : (term167 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem4356726 {A : Type'} (P : A -> Prop) : (term168 A P) = (term169 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4356727 {A : Type'} (s : A -> Prop) : (term110 A s) = (term170 A s).
Proof. exact (@lem4356726 A (term108 A s)). Qed.
Lemma lem4356728 {A : Type'} (s : A -> Prop) (x : A) : (term171 A s x) = (term106 A s x).
Proof. exact (eq_refl (term171 A s x)). Qed.
Lemma lem4356729 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4356730 {A : Type'} (s : A -> Prop) (x : A) : (term172 A s x) = (term167 A s x).
Proof. exact (MK_COMB (@lem4356729) (@lem4356728 A s x)). Qed.
Lemma lem4356731 {A : Type'} (s : A -> Prop) (x : A) : (term172 A s x) = (s x).
Proof. exact (TRANS (@lem4356730 A s x) (@lem4356725 A s x)). Qed.
Lemma lem4356732 {A : Type'} (s : A -> Prop) : (term173 A s) = (term162 A s).
Proof. exact (fun_ext (fun x : A => @lem4356731 A s x)). Qed.
Lemma lem4356733 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4356734 {A : Type'} (s : A -> Prop) : (term170 A s) = (term163 A s).
Proof. exact (MK_COMB (@lem4356733 A) (@lem4356732 A s)). Qed.
Lemma lem4356743 {A : Type'} (s : A -> Prop) : (term110 A s) = (term163 A s).
Proof. exact (TRANS (@lem4356727 A s) (@lem4356734 A s)). Qed.
Lemma lem4356744 {A : Type'} (s : A -> Prop) (h1 : term110 A s) : term163 A s.
Proof. exact (EQ_MP (@lem4356743 A s) (@lem4356717 A s h1)). Qed.
Lemma lem4356746 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4356747 {A : Type'} (P : A -> Prop) : (term174 A P) = (term109 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4356748 {A : Type'} (s : A -> Prop) : (term175 A s) = (term176 A s).
Proof. exact (@lem4356747 A (term162 A s)). Qed.
Lemma lem4356749 {A : Type'} (s : A -> Prop) (x : A) : (term177 A s x) = (s x).
Proof. exact (eq_refl (term177 A s x)). Qed.
Lemma lem4356750 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4356752 {A : Type'} (s : A -> Prop) (x : A) : (term178 A s x) = (term106 A s x).
Proof. exact (MK_COMB (@lem4356750) (@lem4356749 A s x)). Qed.
Lemma lem4356753 {A : Type'} (s : A -> Prop) : (term179 A s) = (term108 A s).
Proof. exact (fun_ext (fun x : A => @lem4356752 A s x)). Qed.
Lemma lem4356754 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4356755 {A : Type'} (s : A -> Prop) : (term176 A s) = (term109 A s).
Proof. exact (MK_COMB (@lem4356754 A) (@lem4356753 A s)). Qed.
Lemma lem4356756 {A : Type'} (s : A -> Prop) : (term175 A s) = (term109 A s).
Proof. exact (TRANS (@lem4356748 A s) (@lem4356755 A s)). Qed.
Lemma lem4356757 {A : Type'} (s : A -> Prop) : (term162 A s) = (term162 A s).
Proof. exact (fun_ext (fun x : A => @lem4356746 A s x)). Qed.
Lemma lem4356758 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4356759 {A : Type'} (s : A -> Prop) : (term163 A s) = (term163 A s).
Proof. exact (MK_COMB (@lem4356758 A) (@lem4356757 A s)). Qed.
Lemma lem4356768 {B : Type'} (t : B -> Prop) (x : B) (y : B) : (term180 B t x y) = (term181 B t x y).
Proof. exact (@lem17045 (t y) (x = y)). Qed.
Lemma lem4356771 {B : Type'} (t : B -> Prop) (x : B) (y : B) : (term113 B t x y) = (term113 B t x y).
Proof. exact (eq_refl (term113 B t x y)). Qed.
Lemma lem4356772 {B : Type'} (P : B -> Prop) : (term174 B P) = (term109 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem4356773 {B : Type'} (t : B -> Prop) (x : B) : (term182 B t x) = (term183 B t x).
Proof. exact (@lem4356772 B (term135 B t x)). Qed.
Lemma lem4356774 {B : Type'} (t : B -> Prop) (x : B) (y : B) : (term136 B t x y) = (term113 B t x y).
Proof. exact (eq_refl (term136 B t x y)). Qed.
Lemma lem4356775 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4356776 {B : Type'} (t : B -> Prop) (x : B) (y : B) : (term184 B t x y) = (term180 B t x y).
Proof. exact (MK_COMB (@lem4356775) (@lem4356774 B t x y)). Qed.
Lemma lem4356777 {B : Type'} (t : B -> Prop) (x : B) (y : B) : (term184 B t x y) = (term181 B t x y).
Proof. exact (TRANS (@lem4356776 B t x y) (@lem4356768 B t x y)). Qed.
Lemma lem4356778 {B : Type'} (t : B -> Prop) (x : B) : (term185 B t x) = (term186 B t x).
Proof. exact (fun_ext (fun y : B => @lem4356777 B t x y)). Qed.
Lemma lem4356779 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4356780 {B : Type'} (t : B -> Prop) (x : B) : (term183 B t x) = (term187 B t x).
Proof. exact (MK_COMB (@lem4356779 B) (@lem4356778 B t x)). Qed.
Lemma lem4356781 {B : Type'} (t : B -> Prop) (x : B) : (term182 B t x) = (term187 B t x).
Proof. exact (TRANS (@lem4356773 B t x) (@lem4356780 B t x)). Qed.
Lemma lem4356782 {B : Type'} (t : B -> Prop) (x : B) : (term135 B t x) = (term135 B t x).
Proof. exact (fun_ext (fun y : B => @lem4356771 B t x y)). Qed.
Lemma lem4356783 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4356784 {B : Type'} (t : B -> Prop) (x : B) : (term143 B t x) = (term143 B t x).
Proof. exact (MK_COMB (@lem4356783 B) (@lem4356782 B t x)). Qed.
Lemma lem4356785 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4356786 {A : Type'} (s : A -> Prop) : (term188 A s) = (term189 A s).
Proof. exact (MK_COMB (@lem4356785) (@lem4356756 A s)). Qed.
Lemma lem4356787 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term190 A B s t x) = (term191 A B s t x).
Proof. exact (MK_COMB (@lem4356786 A s) (@lem4356781 B t x)). Qed.
Lemma lem4356788 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term192 A B s t x) = (term190 A B s t x).
Proof. exact (@lem17045 (term163 A s) (term143 B t x)). Qed.
Lemma lem4356789 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term192 A B s t x) = (term191 A B s t x).
Proof. exact (TRANS (@lem4356788 A B s t x) (@lem4356787 A B s t x)). Qed.
Lemma lem4356790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4356791 {A : Type'} (s : A -> Prop) : (term164 A s) = (term164 A s).
Proof. exact (MK_COMB (@lem4356790) (@lem4356759 A s)). Qed.
Lemma lem4356792 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term149 A B s t x) = (term149 A B s t x).
Proof. exact (MK_COMB (@lem4356791 A s) (@lem4356784 B t x)). Qed.
Lemma lem4356793 {B : Type'} (t : B -> Prop) (x : B) : (term106 B t x) = (term106 B t x).
Proof. exact (eq_refl (term106 B t x)). Qed.
Lemma lem4356794 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4356795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4356796 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term193 A B s t x) = (term194 A B s t x).
Proof. exact (MK_COMB (@lem4356795) (@lem4356789 A B s t x)). Qed.
Lemma lem4356797 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term195 A B s t x) = (term196 A B s t x).
Proof. exact (MK_COMB (@lem4356796 A B s t x) (@lem4356794 B t x)). Qed.
Lemma lem4356798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4356799 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term197 A B s t x) = (term197 A B s t x).
Proof. exact (MK_COMB (@lem4356798) (@lem4356792 A B s t x)). Qed.
Lemma lem4356800 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term198 A B s t x) = (term198 A B s t x).
Proof. exact (MK_COMB (@lem4356799 A B s t x) (@lem4356793 B t x)). Qed.
Lemma lem4356801 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4356802 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term199 A B s t x) = (term199 A B s t x).
Proof. exact (MK_COMB (@lem4356801) (@lem4356800 A B s t x)). Qed.
Lemma lem4356803 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term200 A B s t x) = (term201 A B s t x).
Proof. exact (MK_COMB (@lem4356802 A B s t x) (@lem4356797 A B s t x)). Qed.
Lemma lem4356804 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term166 A B s t x) = (term200 A B s t x).
Proof. exact (@lem17646 (term149 A B s t x) (t x)). Qed.
Lemma lem4356805 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term166 A B s t x) = (term201 A B s t x).
Proof. exact (TRANS (@lem4356804 A B s t x) (@lem4356803 A B s t x)). Qed.
Lemma lem4356892 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4356893 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term147 A P Q).
Proof. exact (@lem4356892 A P Q). Qed.
Lemma lem4356894 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term149 A B s t x) = (term146 A B s t x).
Proof. exact (@lem4356893 A s (term143 B t x)). Qed.
Lemma lem4356896 {A : Type'} (P : Prop) (Q : A -> Prop) : (term132 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4356897 {B : Type'} (P : Prop) (Q : B -> Prop) : (term132 B P Q) = (term131 B P Q).
Proof. exact (@lem4356896 B P Q). Qed.
Lemma lem4356898 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term134 A B s x t x') = (term133 A B s x t x').
Proof. exact (@lem4356897 B (s x) (term135 B t x')). Qed.
Lemma lem4356899 {B : Type'} (t : B -> Prop) (x : B) (y : B) : (term136 B t x y) = (term113 B t x y).
Proof. exact (eq_refl (term136 B t x y)). Qed.
Lemma lem4356900 {B : Type'} (t : B -> Prop) (x : B) : (term141 B t x) = (term135 B t x).
Proof. exact (fun_ext (fun y : B => @lem4356899 B t x y)). Qed.
Lemma lem4356901 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4356902 {B : Type'} (t : B -> Prop) (x : B) : (term142 B t x) = (term143 B t x).
Proof. exact (MK_COMB (@lem4356901 B) (@lem4356900 B t x)). Qed.
Lemma lem4356903 {A : Type'} (s : A -> Prop) (x : A) : (term112 A s x) = (term112 A s x).
Proof. exact (eq_refl (term112 A s x)). Qed.
Lemma lem4356904 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term134 A B s x t x') = (term144 A B s x t x').
Proof. exact (MK_COMB (@lem4356903 A s x) (@lem4356902 B t x')). Qed.
Lemma lem4356905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4356906 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term202 A B s x t x') = (term203 A B s x t x').
Proof. exact (MK_COMB (@lem4356905) (@lem4356904 A B s x t x')). Qed.
Lemma lem4356907 {B : Type'} (t : B -> Prop) (x : B) (y : B) : (term136 B t x y) = (term113 B t x y).
Proof. exact (eq_refl (term136 B t x y)). Qed.
Lemma lem4356908 {A : Type'} (s : A -> Prop) (x : A) : (term112 A s x) = (term112 A s x).
Proof. exact (eq_refl (term112 A s x)). Qed.
Lemma lem4356909 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (y : B) : (term137 A B s x t x' y) = (term114 A B s x t x' y).
Proof. exact (MK_COMB (@lem4356908 A s x) (@lem4356907 B t x' y)). Qed.
Lemma lem4356910 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term138 A B s x t x') = (term115 A B s x t x').
Proof. exact (fun_ext (fun y : B => @lem4356909 A B s x t x' y)). Qed.
Lemma lem4356911 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4356912 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term133 A B s x t x') = (term116 A B s x t x').
Proof. exact (MK_COMB (@lem4356911 B) (@lem4356910 A B s x t x')). Qed.
Lemma lem4356913 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : ((term134 A B s x t x') = (term133 A B s x t x')) = ((term144 A B s x t x') = (term116 A B s x t x')).
Proof. exact (MK_COMB (@lem4356906 A B s x t x') (@lem4356912 A B s x t x')). Qed.
Lemma lem4356914 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term144 A B s x t x') = (term116 A B s x t x').
Proof. exact (EQ_MP (@lem4356913 A B s x t x') (@lem4356898 A B s x t x')). Qed.
Lemma lem4356915 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term145 A B s t x) = (term117 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4356914 A B s x' t x)). Qed.
Lemma lem4356916 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4356917 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term146 A B s t x) = (term118 A B s t x).
Proof. exact (MK_COMB (@lem4356916 A) (@lem4356915 A B s t x)). Qed.
Lemma lem4356918 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term149 A B s t x) = (term118 A B s t x).
Proof. exact (TRANS (@lem4356894 A B s t x) (@lem4356917 A B s t x)). Qed.
Lemma lem4356919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4356920 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term197 A B s t x) = (term204 A B s t x).
Proof. exact (MK_COMB (@lem4356919) (@lem4356918 A B s t x)). Qed.
Lemma lem4356921 {B : Type'} (t : B -> Prop) (x : B) : (term106 B t x) = (term106 B t x).
Proof. exact (eq_refl (term106 B t x)). Qed.
Lemma lem4356922 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term198 A B s t x) = (term205 A B s t x).
Proof. exact (MK_COMB (@lem4356920 A B s t x) (@lem4356921 B t x)). Qed.
Lemma lem4356924 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4356925 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term147 A P Q).
Proof. exact (@lem4356924 A P Q). Qed.
Lemma lem4356926 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term206 A B s t x) = (term207 A B s t x).
Proof. exact (@lem4356925 A (term117 A B s t x) (term106 B t x)). Qed.
Lemma lem4356927 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term208 A B s t x' x) = (term116 A B s x t x').
Proof. exact (eq_refl (term208 A B s t x' x)). Qed.
Lemma lem4356928 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term209 A B s t x) = (term117 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4356927 A B s x' t x)). Qed.
Lemma lem4356929 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4356930 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term210 A B s t x) = (term118 A B s t x).
Proof. exact (MK_COMB (@lem4356929 A) (@lem4356928 A B s t x)). Qed.
Lemma lem4356931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4356932 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term211 A B s t x) = (term204 A B s t x).
Proof. exact (MK_COMB (@lem4356931) (@lem4356930 A B s t x)). Qed.
Lemma lem4356933 {B : Type'} (t : B -> Prop) (x : B) : (term106 B t x) = (term106 B t x).
Proof. exact (eq_refl (term106 B t x)). Qed.
Lemma lem4356934 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term206 A B s t x) = (term205 A B s t x).
Proof. exact (MK_COMB (@lem4356932 A B s t x) (@lem4356933 B t x)). Qed.
Lemma lem4356935 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4356936 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term212 A B s t x) = (term213 A B s t x).
Proof. exact (MK_COMB (@lem4356935) (@lem4356934 A B s t x)). Qed.
Lemma lem4356937 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term208 A B s t x' x) = (term116 A B s x t x').
Proof. exact (eq_refl (term208 A B s t x' x)). Qed.
Lemma lem4356938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4356939 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term214 A B s t x' x) = (term215 A B s x t x').
Proof. exact (MK_COMB (@lem4356938) (@lem4356937 A B s x t x')). Qed.
Lemma lem4356940 {B : Type'} (t : B -> Prop) (x : B) : (term106 B t x) = (term106 B t x).
Proof. exact (eq_refl (term106 B t x)). Qed.
Lemma lem4356941 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term216 A B s x t x') = (term217 A B s x t x').
Proof. exact (MK_COMB (@lem4356939 A B s x t x') (@lem4356940 B t x')). Qed.
Lemma lem4356942 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term218 A B s t x) = (term219 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4356941 A B s x' t x)). Qed.
Lemma lem4356943 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4356944 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term207 A B s t x) = (term220 A B s t x).
Proof. exact (MK_COMB (@lem4356943 A) (@lem4356942 A B s t x)). Qed.
Lemma lem4356945 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : ((term206 A B s t x) = (term207 A B s t x)) = ((term205 A B s t x) = (term220 A B s t x)).
Proof. exact (MK_COMB (@lem4356936 A B s t x) (@lem4356944 A B s t x)). Qed.
Lemma lem4356946 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term205 A B s t x) = (term220 A B s t x).
Proof. exact (EQ_MP (@lem4356945 A B s t x) (@lem4356926 A B s t x)). Qed.
Lemma lem4356948 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4356949 {B : Type'} (P : B -> Prop) (Q : Prop) : (term148 B P Q) = (term147 B P Q).
Proof. exact (@lem4356948 B P Q). Qed.
Lemma lem4356950 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term221 A B s x t x') = (term222 A B s x t x').
Proof. exact (@lem4356949 B (term115 A B s x t x') (term106 B t x')). Qed.
Lemma lem4356951 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (y : B) : (term223 A B s x t x' y) = (term114 A B s x t x' y).
Proof. exact (eq_refl (term223 A B s x t x' y)). Qed.
Lemma lem4356952 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term224 A B s x t x') = (term115 A B s x t x').
Proof. exact (fun_ext (fun y : B => @lem4356951 A B s x t x' y)). Qed.
Lemma lem4356953 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4356954 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term225 A B s x t x') = (term116 A B s x t x').
Proof. exact (MK_COMB (@lem4356953 B) (@lem4356952 A B s x t x')). Qed.
Lemma lem4356955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4356956 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term226 A B s x t x') = (term215 A B s x t x').
Proof. exact (MK_COMB (@lem4356955) (@lem4356954 A B s x t x')). Qed.
Lemma lem4356957 {B : Type'} (t : B -> Prop) (x : B) : (term106 B t x) = (term106 B t x).
Proof. exact (eq_refl (term106 B t x)). Qed.
Lemma lem4356958 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term221 A B s x t x') = (term217 A B s x t x').
Proof. exact (MK_COMB (@lem4356956 A B s x t x') (@lem4356957 B t x')). Qed.
Lemma lem4356959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4356960 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term227 A B s x t x') = (term228 A B s x t x').
Proof. exact (MK_COMB (@lem4356959) (@lem4356958 A B s x t x')). Qed.
Lemma lem4356961 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (y : B) : (term223 A B s x t x' y) = (term114 A B s x t x' y).
Proof. exact (eq_refl (term223 A B s x t x' y)). Qed.
Lemma lem4356962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4356963 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (y : B) : (term229 A B s x t x' y) = (term230 A B s x t x' y).
Proof. exact (MK_COMB (@lem4356962) (@lem4356961 A B s x t x' y)). Qed.
Lemma lem4356964 {B : Type'} (t : B -> Prop) (x : B) : (term106 B t x) = (term106 B t x).
Proof. exact (eq_refl (term106 B t x)). Qed.
Lemma lem4356965 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (t : B -> Prop) (x' : B) : (term231 A B s x y t x') = (term232 A B s x y t x').
Proof. exact (MK_COMB (@lem4356963 A B s x t x' y) (@lem4356964 B t x')). Qed.
Lemma lem4356966 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term233 A B s x t x') = (term234 A B s x t x').
Proof. exact (fun_ext (fun y : B => @lem4356965 A B s x y t x')). Qed.
Lemma lem4356967 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4356968 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term222 A B s x t x') = (term235 A B s x t x').
Proof. exact (MK_COMB (@lem4356967 B) (@lem4356966 A B s x t x')). Qed.
Lemma lem4356969 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : ((term221 A B s x t x') = (term222 A B s x t x')) = ((term217 A B s x t x') = (term235 A B s x t x')).
Proof. exact (MK_COMB (@lem4356960 A B s x t x') (@lem4356968 A B s x t x')). Qed.
Lemma lem4356970 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term217 A B s x t x') = (term235 A B s x t x').
Proof. exact (EQ_MP (@lem4356969 A B s x t x') (@lem4356950 A B s x t x')). Qed.
Lemma lem4356971 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term219 A B s t x) = (term236 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4356970 A B s x' t x)). Qed.
Lemma lem4356972 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4356973 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term220 A B s t x) = (term237 A B s t x).
Proof. exact (MK_COMB (@lem4356972 A) (@lem4356971 A B s t x)). Qed.
Lemma lem4356974 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term205 A B s t x) = (term237 A B s t x).
Proof. exact (TRANS (@lem4356946 A B s t x) (@lem4356973 A B s t x)). Qed.
Lemma lem4356975 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term198 A B s t x) = (term237 A B s t x).
Proof. exact (TRANS (@lem4356922 A B s t x) (@lem4356974 A B s t x)). Qed.
Lemma lem4356976 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4356977 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term199 A B s t x) = (term238 A B s t x).
Proof. exact (MK_COMB (@lem4356976) (@lem4356975 A B s t x)). Qed.
Lemma lem4356978 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term196 A B s t x) = (term196 A B s t x).
Proof. exact (eq_refl (term196 A B s t x)). Qed.
Lemma lem4356979 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term201 A B s t x) = (term239 A B s t x).
Proof. exact (MK_COMB (@lem4356977 A B s t x) (@lem4356978 A B s t x)). Qed.
Lemma lem4356981 {A : Type'} (P : A -> Prop) (Q : Prop) : (term240 A P Q) = (term241 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4356982 {A : Type'} (P : A -> Prop) (Q : Prop) : (term240 A P Q) = (term241 A P Q).
Proof. exact (@lem4356981 A P Q). Qed.
Lemma lem4356983 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term242 A B s t x) = (term243 A B s t x).
Proof. exact (@lem4356982 A (term236 A B s t x) (term196 A B s t x)). Qed.
Lemma lem4356984 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term244 A B s t x' x) = (term235 A B s x t x').
Proof. exact (eq_refl (term244 A B s t x' x)). Qed.
Lemma lem4356985 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term245 A B s t x) = (term236 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4356984 A B s x' t x)). Qed.
Lemma lem4356986 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4356987 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term246 A B s t x) = (term237 A B s t x).
Proof. exact (MK_COMB (@lem4356986 A) (@lem4356985 A B s t x)). Qed.
Lemma lem4356988 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4356989 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term247 A B s t x) = (term238 A B s t x).
Proof. exact (MK_COMB (@lem4356988) (@lem4356987 A B s t x)). Qed.
Lemma lem4356990 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term196 A B s t x) = (term196 A B s t x).
Proof. exact (eq_refl (term196 A B s t x)). Qed.
Lemma lem4356991 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term242 A B s t x) = (term239 A B s t x).
Proof. exact (MK_COMB (@lem4356989 A B s t x) (@lem4356990 A B s t x)). Qed.
Lemma lem4356992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4356993 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term248 A B s t x) = (term249 A B s t x).
Proof. exact (MK_COMB (@lem4356992) (@lem4356991 A B s t x)). Qed.
Lemma lem4356994 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term244 A B s t x' x) = (term235 A B s x t x').
Proof. exact (eq_refl (term244 A B s t x' x)). Qed.
Lemma lem4356995 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4356996 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term250 A B s t x' x) = (term251 A B s x t x').
Proof. exact (MK_COMB (@lem4356995) (@lem4356994 A B s x t x')). Qed.
Lemma lem4356997 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term196 A B s t x) = (term196 A B s t x).
Proof. exact (eq_refl (term196 A B s t x)). Qed.
Lemma lem4356998 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (x' : B) : (term252 A B x s t x') = (term253 A B x s t x').
Proof. exact (MK_COMB (@lem4356996 A B s x t x') (@lem4356997 A B s t x')). Qed.
Lemma lem4356999 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term254 A B s t x) = (term255 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4356998 A B x' s t x)). Qed.
Lemma lem4357000 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4357001 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term243 A B s t x) = (term256 A B s t x).
Proof. exact (MK_COMB (@lem4357000 A) (@lem4356999 A B s t x)). Qed.
Lemma lem4357002 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : ((term242 A B s t x) = (term243 A B s t x)) = ((term239 A B s t x) = (term256 A B s t x)).
Proof. exact (MK_COMB (@lem4356993 A B s t x) (@lem4357001 A B s t x)). Qed.
Lemma lem4357003 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term239 A B s t x) = (term256 A B s t x).
Proof. exact (EQ_MP (@lem4357002 A B s t x) (@lem4356983 A B s t x)). Qed.
Lemma lem4357005 {A : Type'} (P : A -> Prop) (Q : Prop) : (term240 A P Q) = (term241 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4357006 {B : Type'} (P : B -> Prop) (Q : Prop) : (term240 B P Q) = (term241 B P Q).
Proof. exact (@lem4357005 B P Q). Qed.
Lemma lem4357007 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (x' : B) : (term257 A B x s t x') = (term258 A B x s t x').
Proof. exact (@lem4357006 B (term234 A B s x t x') (term196 A B s t x')). Qed.
Lemma lem4357008 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (t : B -> Prop) (x' : B) : (term259 A B s x t x' y) = (term232 A B s x y t x').
Proof. exact (eq_refl (term259 A B s x t x' y)). Qed.
Lemma lem4357009 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term260 A B s x t x') = (term234 A B s x t x').
Proof. exact (fun_ext (fun y : B => @lem4357008 A B s x y t x')). Qed.
Lemma lem4357010 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4357011 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term261 A B s x t x') = (term235 A B s x t x').
Proof. exact (MK_COMB (@lem4357010 B) (@lem4357009 A B s x t x')). Qed.
Lemma lem4357012 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4357013 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term262 A B s x t x') = (term251 A B s x t x').
Proof. exact (MK_COMB (@lem4357012) (@lem4357011 A B s x t x')). Qed.
Lemma lem4357014 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term196 A B s t x) = (term196 A B s t x).
Proof. exact (eq_refl (term196 A B s t x)). Qed.
Lemma lem4357015 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (x' : B) : (term257 A B x s t x') = (term253 A B x s t x').
Proof. exact (MK_COMB (@lem4357013 A B s x t x') (@lem4357014 A B s t x')). Qed.
Lemma lem4357016 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4357017 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (x' : B) : (term263 A B x s t x') = (term264 A B x s t x').
Proof. exact (MK_COMB (@lem4357016) (@lem4357015 A B x s t x')). Qed.
Lemma lem4357018 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (t : B -> Prop) (x' : B) : (term259 A B s x t x' y) = (term232 A B s x y t x').
Proof. exact (eq_refl (term259 A B s x t x' y)). Qed.
Lemma lem4357019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4357020 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (t : B -> Prop) (x' : B) : (term265 A B s x t x' y) = (term266 A B s x y t x').
Proof. exact (MK_COMB (@lem4357019) (@lem4357018 A B s x y t x')). Qed.
Lemma lem4357021 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term196 A B s t x) = (term196 A B s t x).
Proof. exact (eq_refl (term196 A B s t x)). Qed.
Lemma lem4357022 {A B : Type'} (x : A) (y : B) (s : A -> Prop) (t : B -> Prop) (x' : B) : (term267 A B x y s t x') = (term268 A B x y s t x').
Proof. exact (MK_COMB (@lem4357020 A B s x y t x') (@lem4357021 A B s t x')). Qed.
Lemma lem4357023 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (x' : B) : (term269 A B x s t x') = (term270 A B x s t x').
Proof. exact (fun_ext (fun y : B => @lem4357022 A B x y s t x')). Qed.
Lemma lem4357024 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4357025 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (x' : B) : (term258 A B x s t x') = (term271 A B x s t x').
Proof. exact (MK_COMB (@lem4357024 B) (@lem4357023 A B x s t x')). Qed.
Lemma lem4357026 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (x' : B) : ((term257 A B x s t x') = (term258 A B x s t x')) = ((term253 A B x s t x') = (term271 A B x s t x')).
Proof. exact (MK_COMB (@lem4357017 A B x s t x') (@lem4357025 A B x s t x')). Qed.
Lemma lem4357027 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (x' : B) : (term253 A B x s t x') = (term271 A B x s t x').
Proof. exact (EQ_MP (@lem4357026 A B x s t x') (@lem4357007 A B x s t x')). Qed.
Lemma lem4357028 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term255 A B s t x) = (term272 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4357027 A B x' s t x)). Qed.
Lemma lem4357029 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4357030 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term256 A B s t x) = (term273 A B s t x).
Proof. exact (MK_COMB (@lem4357029 A) (@lem4357028 A B s t x)). Qed.
Lemma lem4357031 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term239 A B s t x) = (term273 A B s t x).
Proof. exact (TRANS (@lem4357003 A B s t x) (@lem4357030 A B s t x)). Qed.
Lemma lem4357033 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term201 A B s t x) = (term273 A B s t x).
Proof. exact (TRANS (@lem4356979 A B s t x) (@lem4357031 A B s t x)). Qed.
Lemma lem4357034 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term166 A B s t x) = (term273 A B s t x).
Proof. exact (TRANS (@lem4356805 A B s t x) (@lem4357033 A B s t x)). Qed.
Lemma lem4357035 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term166 A B s t x) : term273 A B s t x.
Proof. exact (EQ_MP (@lem4357034 A B s t x) (@lem4356722 A B s t x h1)). Qed.
Lemma lem4357036 {A B : Type'} (x' : A) (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term271 A B x' s t x) : term271 A B x' s t x.
Proof. exact (h1). Qed.
Lemma lem4357037 {A B : Type'} (x' : A) (y : B) (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term268 A B x' y s t x) : term268 A B x' y s t x.
Proof. exact (h1). Qed.
Lemma lem4357041 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4357056 {B : Type'} (t : B -> Prop) (x : B) (y : B) : (term181 B t x y) = (term181 B t x y).
Proof. exact (eq_refl (term181 B t x y)). Qed.
Lemma lem4357057 {B : Type'} (t : B -> Prop) (x : B) : (term186 B t x) = (term186 B t x).
Proof. exact (fun_ext (fun y : B => @lem4357056 B t x y)). Qed.
Lemma lem4357058 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4357059 {B : Type'} (t : B -> Prop) (x : B) : (term187 B t x) = (term187 B t x).
Proof. exact (MK_COMB (@lem4357058 B) (@lem4357057 B t x)). Qed.
Lemma lem4357064 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term106 A s x).
Proof. exact (eq_refl (term106 A s x)). Qed.
Lemma lem4357065 {A : Type'} (s : A -> Prop) : (term108 A s) = (term108 A s).
Proof. exact (fun_ext (fun x : A => @lem4357064 A s x)). Qed.
Lemma lem4357066 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4357067 {A : Type'} (s : A -> Prop) : (term109 A s) = (term109 A s).
Proof. exact (MK_COMB (@lem4357066 A) (@lem4357065 A s)). Qed.
Lemma lem4357068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4357069 {A : Type'} (s : A -> Prop) : (term189 A s) = (term189 A s).
Proof. exact (MK_COMB (@lem4357068) (@lem4357067 A s)). Qed.
Lemma lem4357070 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term191 A B s t x) = (term191 A B s t x).
Proof. exact (MK_COMB (@lem4357069 A s) (@lem4357059 B t x)). Qed.
Lemma lem4357071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4357072 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term194 A B s t x) = (term194 A B s t x).
Proof. exact (MK_COMB (@lem4357071) (@lem4357070 A B s t x)). Qed.
Lemma lem4357073 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) : (term196 A B s t x) = (term196 A B s t x).
Proof. exact (MK_COMB (@lem4357072 A B s t x) (@lem4357041 B t x)). Qed.
Lemma lem4357100 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) : (term266 A B s x' y t x) = (term266 A B s x' y t x).
Proof. exact (eq_refl (term266 A B s x' y t x)). Qed.
Lemma lem4357101 {A B : Type'} (x' : A) (y : B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term268 A B x' y s t x) = (term268 A B x' y s t x).
Proof. exact (MK_COMB (@lem4357100 A B s x' y t x) (@lem4357073 A B s t x)). Qed.
Lemma lem4357102 {A B : Type'} (x' : A) (y : B) (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term268 A B x' y s t x) : term268 A B x' y s t x.
Proof. exact (EQ_MP (@lem4357101 A B x' y s t x) (@lem4357037 A B x' y s t x h1)). Qed.
Lemma lem4357106 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : s x'') : s x''.
Proof. exact (h1). Qed.
Lemma lem4357107 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : term232 A B s x' y t x.
Proof. exact (h1). Qed.
Lemma lem4357108 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term196 A B s t x) : term196 A B s t x.
Proof. exact (h1). Qed.
Lemma lem4357110 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : term114 A B s x' t x y.
Proof. exact (proj1 (@lem4357107 A B s x' y t x h1)). Qed.
Lemma lem4357111 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : term113 B t x y.
Proof. exact (proj2 (@lem4357110 A B s x' y t x h1)). Qed.
Lemma lem4357116 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term196 A B s t x) : term191 A B s t x.
Proof. exact (proj1 (@lem4357108 A B s t x h1)). Qed.
Lemma lem4357117 {A : Type'} (s : A -> Prop) (h1 : term109 A s) : term109 A s.
Proof. exact (h1). Qed.
Lemma lem4357118 {B : Type'} (t : B -> Prop) (x : B) (h1 : term187 B t x) : term187 B t x.
Proof. exact (h1). Qed.
Lemma lem4357142 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : s x'') : s x''.
Proof. exact (h1). Qed.
Lemma lem4357148 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term106 A s x).
Proof. exact (eq_refl (term106 A s x)). Qed.
Lemma lem4357149 {A : Type'} (s : A -> Prop) : (term108 A s) = (term108 A s).
Proof. exact (fun_ext (fun x : A => @lem4357148 A s x)). Qed.
Lemma lem4357150 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4357152 {A : Type'} (s : A -> Prop) : (term109 A s) = (term109 A s).
Proof. exact (MK_COMB (@lem4357150 A) (@lem4357149 A s)). Qed.
Lemma lem4357153 {A : Type'} (s : A -> Prop) (h1 : term109 A s) : term109 A s.
Proof. exact (EQ_MP (@lem4357152 A s) (@lem4357117 A s h1)). Qed.
Lemma lem4357169 {B : Type'} (t : B -> Prop) (x : B) (y : B) : (term181 B t x y) = (term181 B t x y).
Proof. exact (eq_refl (term181 B t x y)). Qed.
Lemma lem4357170 {B : Type'} (t : B -> Prop) (x : B) : (term186 B t x) = (term186 B t x).
Proof. exact (fun_ext (fun y : B => @lem4357169 B t x y)). Qed.
Lemma lem4357171 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4357173 {B : Type'} (t : B -> Prop) (x : B) : (term187 B t x) = (term187 B t x).
Proof. exact (MK_COMB (@lem4357171 B) (@lem4357170 B t x)). Qed.
Lemma lem4357174 {B : Type'} (t : B -> Prop) (x : B) (h1 : term187 B t x) : term187 B t x.
Proof. exact (EQ_MP (@lem4357173 B t x) (@lem4357118 B t x h1)). Qed.
Lemma lem4357175 {A : Type'} (_49818 : A) (s : A -> Prop) (h1 : term109 A s) : term171 A s _49818.
Proof. exact (@lem4357153 A s h1 _49818). Qed.
Lemma lem4357176 {A : Type'} (s : A -> Prop) (_49818 : A) : (term171 A s _49818) = (term106 A s _49818).
Proof. exact (eq_refl (term171 A s _49818)). Qed.
Lemma lem4357178 {B : Type'} (_49819 : B) (t : B -> Prop) (x : B) (h1 : term187 B t x) : term274 B t x _49819.
Proof. exact (@lem4357174 B t x h1 _49819). Qed.
Lemma lem4357179 {B : Type'} (t : B -> Prop) (x : B) (_49819 : B) : (term274 B t x _49819) = (term181 B t x _49819).
Proof. exact (eq_refl (term274 B t x _49819)). Qed.
Lemma lem4357184 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : term106 B t x.
Proof. exact (proj2 (@lem4357107 A B s x' y t x h1)). Qed.
Lemma lem4357190 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : x = y.
Proof. exact (proj2 (@lem4357111 A B s x' y t x h1)). Qed.
Lemma lem4357192 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : s x'') : s x''.
Proof. exact (h1). Qed.
Lemma lem4357196 {A : Type'} (_49818 : A) (s : A -> Prop) (h1 : term109 A s) : term106 A s _49818.
Proof. exact (EQ_MP (@lem4357176 A s _49818) (@lem4357175 A _49818 s h1)). Qed.
Lemma lem4357206 {B : Type'} (_49819 : B) (t : B -> Prop) (x : B) (h1 : term187 B t x) : term181 B t x _49819.
Proof. exact (EQ_MP (@lem4357179 B t x _49819) (@lem4357178 B _49819 t x h1)). Qed.
Lemma lem4357235 {B : Type'} (t : B -> Prop) : (term108 B t) = (term108 B t).
Proof. exact (eq_refl (term108 B t)). Qed.
Lemma lem4357236 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : (term171 B t x) = (term171 B t y).
Proof. exact (MK_COMB (@lem4357235 B t) (@lem4357190 A B s x' y t x h1)). Qed.
Lemma lem4357237 {B : Type'} (t : B -> Prop) (y : B) : (term171 B t y) = (term106 B t y).
Proof. exact (eq_refl (term171 B t y)). Qed.
Lemma lem4357238 {B : Type'} (t : B -> Prop) (x : B) : (term275 B t x) = (term275 B t x).
Proof. exact (eq_refl (term275 B t x)). Qed.
Lemma lem4357239 {B : Type'} (x : B) (t : B -> Prop) (y : B) : ((term171 B t x) = (term171 B t y)) = ((term171 B t x) = (term106 B t y)).
Proof. exact (MK_COMB (@lem4357238 B t x) (@lem4357237 B t y)). Qed.
Lemma lem4357240 {B : Type'} (t : B -> Prop) (x : B) : (term171 B t x) = (term106 B t x).
Proof. exact (eq_refl (term171 B t x)). Qed.
Lemma lem4357241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4357242 {B : Type'} (t : B -> Prop) (x : B) : (term275 B t x) = (term276 B t x).
Proof. exact (MK_COMB (@lem4357241) (@lem4357240 B t x)). Qed.
Lemma lem4357243 {B : Type'} (t : B -> Prop) (y : B) : (term106 B t y) = (term106 B t y).
Proof. exact (eq_refl (term106 B t y)). Qed.
Lemma lem4357244 {B : Type'} (x : B) (t : B -> Prop) (y : B) : ((term171 B t x) = (term106 B t y)) = ((term106 B t x) = (term106 B t y)).
Proof. exact (MK_COMB (@lem4357242 B t x) (@lem4357243 B t y)). Qed.
Lemma lem4357245 {B : Type'} (x : B) (t : B -> Prop) (y : B) : ((term171 B t x) = (term171 B t y)) = ((term106 B t x) = (term106 B t y)).
Proof. exact (TRANS (@lem4357239 B x t y) (@lem4357244 B x t y)). Qed.
Lemma lem4357246 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : (term106 B t x) = (term106 B t y).
Proof. exact (EQ_MP (@lem4357245 B x t y) (@lem4357236 A B s x' y t x h1)). Qed.
Lemma lem4357247 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : term106 B t y.
Proof. exact (EQ_MP (@lem4357246 A B s x' y t x h1) (@lem4357184 A B s x' y t x h1)). Qed.
Lemma lem4357277 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : t y.
Proof. exact (proj1 (@lem4357111 A B s x' y t x h1)). Qed.
Lemma lem4357278 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : term277 B t y.
Proof. exact (fun h0 : term106 B t y => @lem4357277 A B s x' y t x h1). Qed.
Lemma lem4357280 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4357281 {B : Type'} (t : B -> Prop) (y : B) : (term277 B t y) = (t y).
Proof. exact (@lem4357280 (t y)). Qed.
Lemma lem4357282 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : t y.
Proof. exact (EQ_MP (@lem4357281 B t y) (@lem4357278 A B s x' y t x h1)). Qed.
Lemma lem4357285 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4357287 {B : Type'} (t : B -> Prop) (y : B) : (term106 B t y) = (term279 B t y).
Proof. exact (@lem4357285 (t y)). Qed.
Lemma lem4357290 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : term279 B t y.
Proof. exact (EQ_MP (@lem4357287 B t y) (@lem4357247 A B s x' y t x h1)). Qed.
Lemma lem4357293 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : False.
Proof. exact (@lem4357290 A B s x' y t x h1 (@lem4357282 A B s x' y t x h1)). Qed.
Lemma lem4357294 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : term280.
Proof. exact (fun h0 : ~ False => @lem4357293 A B s x' y t x h1). Qed.
Lemma lem4357296 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4357297 : term280 = False.
Proof. exact (@lem4357296 False). Qed.
Lemma lem4357300 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : s x'') : s x''.
Proof. exact (h1). Qed.
Lemma lem4357301 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : s x'') : term277 A s x''.
Proof. exact (fun h0 : term106 A s x'' => @lem4357300 A s x'' h1). Qed.
Lemma lem4357303 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4357304 {A : Type'} (s : A -> Prop) (x'' : A) : (term277 A s x'') = (s x'').
Proof. exact (@lem4357303 (s x'')). Qed.
Lemma lem4357305 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : s x'') : s x''.
Proof. exact (EQ_MP (@lem4357304 A s x'') (@lem4357301 A s x'' h1)). Qed.
Lemma lem4357308 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4357310 {A : Type'} (s : A -> Prop) (_49818 : A) : (term106 A s _49818) = (term279 A s _49818).
Proof. exact (@lem4357308 (s _49818)). Qed.
Lemma lem4357313 {A : Type'} (_49818 : A) (s : A -> Prop) (h1 : term109 A s) : term279 A s _49818.
Proof. exact (EQ_MP (@lem4357310 A s _49818) (@lem4357196 A _49818 s h1)). Qed.
Lemma lem4357314 {A : Type'} (_49818 : A) (s : A -> Prop) (h1 : term109 A s) : term279 A s _49818.
Proof. exact (@lem4357313 A _49818 s h1). Qed.
Lemma lem4357315 {A : Type'} (x'' : A) (s : A -> Prop) (h1 : term109 A s) : term279 A s x''.
Proof. exact (@lem4357314 A x'' s h1). Qed.
Lemma lem4357318 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : term109 A s) (h2 : s x'') : False.
Proof. exact (@lem4357315 A x'' s h1 (@lem4357305 A s x'' h2)). Qed.
Lemma lem4357319 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : term109 A s) (h2 : s x'') : term280.
Proof. exact (fun h0 : ~ False => @lem4357318 A s x'' h1 h2). Qed.
Lemma lem4357321 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4357322 : term280 = False.
Proof. exact (@lem4357321 False). Qed.
Lemma lem4357323 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : term109 A s) (h2 : s x'') : False.
Proof. exact (EQ_MP (@lem4357322) (@lem4357319 A s x'' h1 h2)). Qed.
Lemma lem4357353 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term196 A B s t x) : t x.
Proof. exact (proj2 (@lem4357108 A B s t x h1)). Qed.
Lemma lem4357354 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term196 A B s t x) : term277 B t x.
Proof. exact (fun h0 : term106 B t x => @lem4357353 A B s t x h1). Qed.
Lemma lem4357356 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4357357 {B : Type'} (t : B -> Prop) (x : B) : (term277 B t x) = (t x).
Proof. exact (@lem4357356 (t x)). Qed.
Lemma lem4357358 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term196 A B s t x) : t x.
Proof. exact (EQ_MP (@lem4357357 B t x) (@lem4357354 A B s t x h1)). Qed.
Lemma lem4357360 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4357361 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4357360 B x). Qed.
Lemma lem4357362 {B : Type'} (x : B) : term281 B x.
Proof. exact (fun h0 : term282 B x => @lem4357361 B x). Qed.
Lemma lem4357364 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4357365 {B : Type'} (x : B) : (term281 B x) = (x = x).
Proof. exact (@lem4357364 (x = x)). Qed.
Lemma lem4357366 {B : Type'} (x : B) : x = x.
Proof. exact (EQ_MP (@lem4357365 B x) (@lem4357362 B x)). Qed.
Lemma lem4357368 (a : Prop) (b : Prop) : (term283 a b) = (term284 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4357369 {B : Type'} (t : B -> Prop) (x : B) (_49819 : B) : (term181 B t x _49819) = (term180 B t x _49819).
Proof. exact (@lem4357368 (t _49819) (x = _49819)). Qed.
Lemma lem4357371 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4357372 {B : Type'} (t : B -> Prop) (x : B) (_49819 : B) : (term180 B t x _49819) = (term285 B t x _49819).
Proof. exact (@lem4357371 (term113 B t x _49819)). Qed.
Lemma lem4357373 {B : Type'} (t : B -> Prop) (x : B) (_49819 : B) : (term181 B t x _49819) = (term285 B t x _49819).
Proof. exact (TRANS (@lem4357369 B t x _49819) (@lem4357372 B t x _49819)). Qed.
Lemma lem4357375 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term196 A B s t x) : term286 B t x.
Proof. exact (conj (@lem4357358 A B s t x h1) (@lem4357366 B x)). Qed.
Lemma lem4357377 {B : Type'} (_49819 : B) (t : B -> Prop) (x : B) (h1 : term187 B t x) : term285 B t x _49819.
Proof. exact (EQ_MP (@lem4357373 B t x _49819) (@lem4357206 B _49819 t x h1)). Qed.
Lemma lem4357378 {B : Type'} (_49819 : B) (t : B -> Prop) (x : B) (h1 : term187 B t x) : term285 B t x _49819.
Proof. exact (@lem4357377 B _49819 t x h1). Qed.
Lemma lem4357379 {B : Type'} (t : B -> Prop) (x : B) (h1 : term187 B t x) : term287 B t x.
Proof. exact (@lem4357378 B x t x h1). Qed.
Lemma lem4357382 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term187 B t x) (h2 : term196 A B s t x) : False.
Proof. exact (@lem4357379 B t x h1 (@lem4357375 A B s t x h2)). Qed.
Lemma lem4357383 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term187 B t x) (h2 : term196 A B s t x) : term280.
Proof. exact (fun h0 : ~ False => @lem4357382 A B s t x h1 h2). Qed.
Lemma lem4357385 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4357386 : term280 = False.
Proof. exact (@lem4357385 False). Qed.
Lemma lem4357387 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term187 B t x) (h2 : term196 A B s t x) : False.
Proof. exact (EQ_MP (@lem4357386) (@lem4357383 A B s t x h1 h2)). Qed.
Lemma lem4357388 {A B : Type'} (s : A -> Prop) (x' : A) (y : B) (t : B -> Prop) (x : B) (h1 : term232 A B s x' y t x) : False.
Proof. exact (EQ_MP (@lem4357297) (@lem4357294 A B s x' y t x h1)). Qed.
Lemma lem4357389 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : term109 A s) (h2 : s x'') : (s x'') = False.
Proof. exact (prop_ext (fun h3 : s x'' => @lem4357323 A s x'' h1 h2) (fun h3 : False => @lem4357192 A s x'' h2)). Qed.
Lemma lem4357390 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : term109 A s) (h2 : s x'') : False.
Proof. exact (EQ_MP (@lem4357389 A s x'' h1 h2) (@lem4357192 A s x'' h2)). Qed.
Lemma lem4357391 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : term109 A s) (h2 : s x'') : (s x'') = False.
Proof. exact (prop_ext (fun h3 : s x'' => @lem4357390 A s x'' h1 h2) (fun h3 : False => @lem4357142 A s x'' h2)). Qed.
Lemma lem4357392 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : term109 A s) (h2 : s x'') : False.
Proof. exact (EQ_MP (@lem4357391 A s x'' h1 h2) (@lem4357142 A s x'' h2)). Qed.
Lemma lem4357393 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term187 B t x) (h2 : term196 A B s t x) : (term187 B t x) = False.
Proof. exact (prop_ext (fun h3 : term187 B t x => @lem4357387 A B s t x h1 h2) (fun h3 : False => @lem4357174 B t x h1)). Qed.
Lemma lem4357394 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term187 B t x) (h2 : term196 A B s t x) : False.
Proof. exact (EQ_MP (@lem4357393 A B s t x h1 h2) (@lem4357174 B t x h1)). Qed.
Lemma lem4357395 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : term109 A s) (h2 : s x'') : (term109 A s) = False.
Proof. exact (prop_ext (fun h3 : term109 A s => @lem4357392 A s x'' h1 h2) (fun h3 : False => @lem4357153 A s h1)). Qed.
Lemma lem4357396 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : term109 A s) (h2 : s x'') : False.
Proof. exact (EQ_MP (@lem4357395 A s x'' h1 h2) (@lem4357153 A s h1)). Qed.
Lemma lem4357397 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : term109 A s) (h2 : s x'') : (s x'') = False.
Proof. exact (prop_ext (fun h3 : s x'' => @lem4357396 A s x'' h1 h2) (fun h3 : False => @lem4357142 A s x'' h2)). Qed.
Lemma lem4357398 {A : Type'} (s : A -> Prop) (x'' : A) (h1 : term109 A s) (h2 : s x'') : False.
Proof. exact (EQ_MP (@lem4357397 A s x'' h1 h2) (@lem4357142 A s x'' h2)). Qed.
Lemma lem4357399 {A B : Type'} (x'' : A) (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : s x'') (h2 : term196 A B s t x) : False.
Proof. exact (or_elim (@lem4357116 A B s t x h2) (fun h0 : term109 A s => @lem4357398 A s x'' h0 h1) (fun h0 : term187 B t x => @lem4357394 A B s t x h0 h2)). Qed.
Lemma lem4357400 {A B : Type'} (x'' : A) (x' : A) (y : B) (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : s x'') (h2 : term268 A B x' y s t x) : False.
Proof. exact (or_elim (@lem4357102 A B x' y s t x h2) (fun h0 : term232 A B s x' y t x => @lem4357388 A B s x' y t x h0) (fun h0 : term196 A B s t x => @lem4357399 A B x'' s t x h1 h0)). Qed.
Lemma lem4357401 {A B : Type'} (x'' : A) (x' : A) (y : B) (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : s x'') (h2 : term268 A B x' y s t x) : (s x'') = False.
Proof. exact (prop_ext (fun h3 : s x'' => @lem4357400 A B x'' x' y s t x h1 h2) (fun h3 : False => @lem4357106 A s x'' h1)). Qed.
Lemma lem4357402 {A B : Type'} (x'' : A) (x' : A) (y : B) (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : s x'') (h2 : term268 A B x' y s t x) : False.
Proof. exact (EQ_MP (@lem4357401 A B x'' x' y s t x h1 h2) (@lem4357106 A s x'' h1)). Qed.
Lemma lem4357403 {A B : Type'} (x'' : A) (x' : A) (y : B) (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : s x'') (h2 : term268 A B x' y s t x) : (term268 A B x' y s t x) = False.
Proof. exact (prop_ext (fun h3 : term268 A B x' y s t x => @lem4357402 A B x'' x' y s t x h1 h2) (fun h3 : False => @lem4357102 A B x' y s t x h2)). Qed.
Lemma lem4357404 {A B : Type'} (x'' : A) (x' : A) (y : B) (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : s x'') (h2 : term268 A B x' y s t x) : False.
Proof. exact (EQ_MP (@lem4357403 A B x'' x' y s t x h1 h2) (@lem4357102 A B x' y s t x h2)). Qed.
Lemma lem4357405 {A B : Type'} (x' : A) (y : B) (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term110 A s) (h2 : term268 A B x' y s t x) : False.
Proof. exact (ex_elim (@lem4356744 A s h1) (fun x'' : A => fun h0 : term162 A s x'' => @lem4357404 A B x'' x' y s t x h0 h2)). Qed.
Lemma lem4357406 {A B : Type'} (x' : A) (t : B -> Prop) (x : B) (s : A -> Prop) (h1 : term271 A B x' s t x) (h2 : term110 A s) : False.
Proof. exact (ex_elim (@lem4357036 A B x' s t x h1) (fun y : B => fun h0 : term270 A B x' s t x y => @lem4357405 A B x' y s t x h2 h0)). Qed.
Lemma lem4357407 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term110 A s) (h2 : term166 A B s t x) : False.
Proof. exact (ex_elim (@lem4357035 A B s t x h2) (fun x' : A => fun h0 : term272 A B s t x x' => @lem4357406 A B x' t x s h0 h1)). Qed.
Lemma lem4357408 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term110 A s) (h2 : term166 A B s t x) : (term166 A B s t x) = False.
Proof. exact (prop_ext (fun h3 : term166 A B s t x => @lem4357407 A B s t x h1 h2) (fun h3 : False => @lem4356722 A B s t x h2)). Qed.
Lemma lem4357409 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (x : B) (h1 : term110 A s) (h2 : term166 A B s t x) : False.
Proof. exact (EQ_MP (@lem4357408 A B s t x h1 h2) (@lem4356722 A B s t x h2)). Qed.
Lemma lem4357410 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (h1 : term110 A s) : term165 A B s t x.
Proof. exact (fun h0 : term166 A B s t x => @lem4357409 A B s t x h1 h0). Qed.
Lemma lem4357411 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (h1 : term110 A s) : (term149 A B s t x) = (t x).
Proof. exact (EQ_MP (@lem4356721 A B s t x) (@lem4357410 A B t x s h1)). Qed.
Lemma lem4357416 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term110 A s) : term152 A B s t.
Proof. exact (fun x : B => @lem4357411 A B t x s h1). Qed.
Lemma lem4357417 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term153 A B s t.
Proof. exact (fun h0 : term110 A s => @lem4357416 A B t s h0). Qed.
Lemma lem4357422 {A B : Type'} (t : B -> Prop) : term157 A B t.
Proof. exact (fun s : A -> Prop => @lem4357417 A B s t). Qed.
Lemma lem4357427 {A B : Type'} : term161 A B.
Proof. exact (fun t : B -> Prop => @lem4357422 A B t). Qed.
Lemma lem4357428 {A B : Type'} : term160 A B.
Proof. exact (EQ_MP (@lem4356716 A B) (@lem4357427 A B)). Qed.
Lemma lem4357429 {A B : Type'} (t : B -> Prop) : term288 A B t.
Proof. exact (@lem4357428 A B t). Qed.
Lemma lem4357430 {A B : Type'} (t : B -> Prop) : (term288 A B t) = (term156 A B t).
Proof. exact (eq_refl (term288 A B t)). Qed.
Lemma lem4357431 {A B : Type'} (t : B -> Prop) : term156 A B t.
Proof. exact (EQ_MP (@lem4357430 A B t) (@lem4357429 A B t)). Qed.
Lemma lem4357432 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term289 A B t s.
Proof. exact (@lem4357431 A B t s). Qed.
Lemma lem4357433 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term289 A B t s) = (term124 A B s t).
Proof. exact (eq_refl (term289 A B t s)). Qed.
Lemma lem4357434 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term124 A B s t.
Proof. exact (EQ_MP (@lem4357433 A B s t) (@lem4357432 A B t s)). Qed.
Lemma lem4357436 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term124 A B s t.
Proof. exact (@lem4356452 A B s t (@lem4357434 A B s t)). Qed.
Lemma lem4357437 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term125 A B s t) : False.
Proof. exact (@lem4357436 A B s t (@lem4356436 A B s t h1)). Qed.
Lemma lem4357438 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term125 A B s t) : (term125 A B s t) = False.
Proof. exact (prop_ext (fun h2 : term125 A B s t => @lem4357437 A B s t h1) (fun h2 : False => @lem4356436 A B s t h1)). Qed.
Lemma lem4357439 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term125 A B s t) : False.
Proof. exact (EQ_MP (@lem4357438 A B s t h1) (@lem4356436 A B s t h1)). Qed.
Lemma lem4357440 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term124 A B s t.
Proof. exact (fun h0 : term125 A B s t => @lem4357439 A B s t h0). Qed.
Lemma lem4357441 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term122 A B s t.
Proof. exact (EQ_MP (@lem4356435 A B s t) (@lem4357440 A B s t)). Qed.
Lemma lem4357442 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term103 A B s t.
Proof. exact (EQ_MP (@lem4356431 A B s t) (@lem4357441 A B s t)). Qed.
Lemma lem4357443 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term102 A B s t.
Proof. exact (EQ_MP (@lem4356325 A B s t) (@lem4357442 A B s t)). Qed.
Lemma lem4357444 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term43 A s) : term98 A B s t.
Proof. exact (@lem4357443 A B s t (@lem4356023 A s h1)). Qed.
Lemma lem4357445 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term43 A s) : term65 A B s t.
Proof. exact (EQ_MP (@lem4356266 A B s t) (@lem4357444 A B t s h1)). Qed.
Lemma lem4357446 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term43 A s) : term56 A B s t.
Proof. exact (EQ_MP (@lem4356177 A B s t) (@lem4357445 A B t s h1)). Qed.
Lemma lem4357449 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term43 A s) : (term29 A B s t) = t.
Proof. exact (EQ_MP (@lem4356151 A B s t) (@lem4357446 A B t s h1)). Qed.
Lemma lem4357450 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term43 A s) : (term43 A s) = ((term29 A B s t) = t).
Proof. exact (prop_ext (fun h2 : term43 A s => @lem4357449 A B t s h1) (fun h2 : (term29 A B s t) = t => @lem4356023 A s h1)). Qed.
Lemma lem4357451 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term43 A s) : (term29 A B s t) = t.
Proof. exact (EQ_MP (@lem4357450 A B t s h1) (@lem4356023 A s h1)). Qed.
Lemma lem4357452 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term32 A B s t.
Proof. exact (fun h0 : term43 A s => @lem4357451 A B t s h0). Qed.
Lemma lem4357453 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term29 A B s t) = (@EMPTY B).
Proof. exact (EQ_MP (@lem4356078 A B t s h1) (@lem0)). Qed.
Lemma lem4357454 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (s = (@EMPTY A)) = ((term29 A B s t) = (@EMPTY B)).
Proof. exact (prop_ext (fun h2 : s = (@EMPTY A) => @lem4357453 A B t s h1) (fun h2 : (term29 A B s t) = (@EMPTY B) => @lem4356006 A s h1)). Qed.
Lemma lem4357455 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term29 A B s t) = (@EMPTY B).
Proof. exact (EQ_MP (@lem4357454 A B t s h1) (@lem4356006 A s h1)). Qed.
Lemma lem4357456 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term36 A B s t.
Proof. exact (fun h0 : s = (@EMPTY A) => @lem4357455 A B t s h0). Qed.
Lemma lem4357457 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term39 A B s t.
Proof. exact (conj (@lem4357456 A B s t) (@lem4357452 A B s t)). Qed.
Lemma lem4357458 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term29 A B s t) = (term40 A B s t).
Proof. exact (EQ_MP (@lem4356005 A B s t) (@lem4357457 A B s t)). Qed.
Lemma lem4357463 {A B : Type'} (s : A -> Prop) : term290 A B s.
Proof. exact (fun t : B -> Prop => @lem4357458 A B s t). Qed.
Lemma lem4357468 {A B : Type'} : term291 A B.
Proof. exact (fun s : A -> Prop => @lem4357463 A B s). Qed.
