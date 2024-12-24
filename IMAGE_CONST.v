Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_CONST_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IMAGE_CLAUSES_spec.
Require Import IN_IMAGE_spec.
Require Import IN_SING_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem3390947 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem3390948 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3390949 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem3390948 A x) (@lem3390947 A x)). Qed.
Lemma lem3390950 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem3390949 A x y). Qed.
Lemma lem3390951 {A : Type'} (x : A) (y : A) : (term2 A x y) = ((term3 A x y) = (x = y)).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem3390953 {A B : Type'} (y : B) : term4 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3390954 {A B : Type'} (y : B) : (term4 A B y) = (term5 A B y).
Proof. exact (eq_refl (term4 A B y)). Qed.
Lemma lem3390955 {A B : Type'} (y : B) : term5 A B y.
Proof. exact (EQ_MP (@lem3390954 A B y) (@lem3390953 A B y)). Qed.
Lemma lem3390956 {A B : Type'} (y : B) (s : A -> Prop) : term6 A B y s.
Proof. exact (@lem3390955 A B y s). Qed.
Lemma lem3390957 {A B : Type'} (y : B) (s : A -> Prop) : (term6 A B y s) = (term7 A B y s).
Proof. exact (eq_refl (term6 A B y s)). Qed.
Lemma lem3390958 {A B : Type'} (y : B) (s : A -> Prop) : term7 A B y s.
Proof. exact (EQ_MP (@lem3390957 A B y s) (@lem3390956 A B y s)). Qed.
Lemma lem3390959 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term8 A B y s f.
Proof. exact (@lem3390958 A B y s f). Qed.
Lemma lem3390960 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term8 A B y s f) = ((term9 A B y f s) = (term10 A B y f s)).
Proof. exact (eq_refl (term8 A B y s f)). Qed.
Lemma lem3390962 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3390963 {A : Type'} (s : A -> Prop) : (term11 A s) = (term12 A s).
Proof. exact (eq_refl (term11 A s)). Qed.
Lemma lem3390964 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (EQ_MP (@lem3390963 A s) (@lem3390962 A s)). Qed.
Lemma lem3390965 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term13 A s t.
Proof. exact (@lem3390964 A s t). Qed.
Lemma lem3390966 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term13 A s t) = ((s = t) = (term14 A s t)).
Proof. exact (eq_refl (term13 A s t)). Qed.
Lemma lem3390968 {_88100 : Type'} (_474 : _88100 -> Prop) (_475 : Prop) (_476 : type686 _88100) (_477 : _88100 -> Prop) : (term15 _88100 _476 _475 _474 _477) = (term16 _88100 _474 _475 _476 _477).
Proof. exact (@lem13473 (_88100 -> Prop) _474 _475 _476 _477). Qed.
Lemma lem3390969 {_88095 _88100 : Type'} (_474 : _88100 -> Prop) (_475 : Prop) (c : _88100) (s : _88095 -> Prop) (_477 : _88100 -> Prop) : (term17 _88095 _88100 c s _475 _474 _477) = (term18 _88095 _88100 _474 _475 c s _477).
Proof. exact (@lem3390968 _88100 _474 _475 (term19 _88095 _88100 c s) _477). Qed.
Lemma lem3390970 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term20 _88095 _88100 s c) = (term21 _88095 _88100 s c).
Proof. exact (@lem3390969 _88095 _88100 (@EMPTY _88100) (s = (@EMPTY _88095)) c s (@INSERT _88100 c (@EMPTY _88100))). Qed.
Lemma lem3390971 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term22 _88095 _88100 s c) = ((term23 _88095 _88100 c s) = (@INSERT _88100 c (@EMPTY _88100))).
Proof. exact (eq_refl (term22 _88095 _88100 s c)). Qed.
Lemma lem3390972 {_88095 : Type'} (s : _88095 -> Prop) : (term24 _88095 s) = (term24 _88095 s).
Proof. exact (eq_refl (term24 _88095 s)). Qed.
Lemma lem3390973 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term25 _88095 _88100 s c) = (term26 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3390972 _88095 s) (@lem3390971 _88095 _88100 s c)). Qed.
Lemma lem3390974 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) : (term27 _88095 _88100 c s) = ((term23 _88095 _88100 c s) = (@EMPTY _88100)).
Proof. exact (eq_refl (term27 _88095 _88100 c s)). Qed.
Lemma lem3390975 {_88095 : Type'} (s : _88095 -> Prop) : (term28 _88095 s) = (term28 _88095 s).
Proof. exact (eq_refl (term28 _88095 s)). Qed.
Lemma lem3390976 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) : (term29 _88095 _88100 c s) = (term30 _88095 _88100 c s).
Proof. exact (MK_COMB (@lem3390975 _88095 s) (@lem3390974 _88095 _88100 c s)). Qed.
Lemma lem3390977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3390978 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) : (term31 _88095 _88100 c s) = (term32 _88095 _88100 c s).
Proof. exact (MK_COMB (@lem3390977) (@lem3390976 _88095 _88100 c s)). Qed.
Lemma lem3390979 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term21 _88095 _88100 s c) = (term33 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3390978 _88095 _88100 c s) (@lem3390973 _88095 _88100 s c)). Qed.
Lemma lem3390980 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term20 _88095 _88100 s c) = ((term23 _88095 _88100 c s) = (term34 _88095 _88100 s c)).
Proof. exact (eq_refl (term20 _88095 _88100 s c)). Qed.
Lemma lem3390981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3390982 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term35 _88095 _88100 s c) = (term36 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3390981) (@lem3390980 _88095 _88100 s c)). Qed.
Lemma lem3390983 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : ((term20 _88095 _88100 s c) = (term21 _88095 _88100 s c)) = (((term23 _88095 _88100 c s) = (term34 _88095 _88100 s c)) = (term33 _88095 _88100 s c)).
Proof. exact (MK_COMB (@lem3390982 _88095 _88100 s c) (@lem3390979 _88095 _88100 s c)). Qed.
Lemma lem3390984 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : ((term23 _88095 _88100 c s) = (term34 _88095 _88100 s c)) = (term33 _88095 _88100 s c).
Proof. exact (EQ_MP (@lem3390983 _88095 _88100 s c) (@lem3390970 _88095 _88100 s c)). Qed.
Lemma lem3390985 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term33 _88095 _88100 s c) = ((term23 _88095 _88100 c s) = (term34 _88095 _88100 s c)).
Proof. exact (SYM (@lem3390984 _88095 _88100 s c)). Qed.
Lemma lem3390986 {_88095 : Type'} (s : _88095 -> Prop) (h1 : s = (@EMPTY _88095)) : s = (@EMPTY _88095).
Proof. exact (h1). Qed.
Lemma lem3391003 {_88095 : Type'} (s : _88095 -> Prop) (h1 : term37 _88095 s) : term37 _88095 s.
Proof. exact (h1). Qed.
Lemma lem3391025 {_88095 : Type'} (s : _88095 -> Prop) (h1 : s = (@EMPTY _88095)) : s = (@EMPTY _88095).
Proof. exact (h1). Qed.
Lemma lem3391026 {_88095 _88100 : Type'} (c : _88100) : (term38 _88095 _88100 c) = (term38 _88095 _88100 c).
Proof. exact (eq_refl (term38 _88095 _88100 c)). Qed.
Lemma lem3391027 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : s = (@EMPTY _88095)) : (term23 _88095 _88100 c s) = (term39 _88095 _88100 c).
Proof. exact (MK_COMB (@lem3391026 _88095 _88100 c) (@lem3391025 _88095 s h1)). Qed.
Lemma lem3391029 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481).
Proof. exact (proj1 (@lem3366870 _87477 _87481 (@el _87477) f (@el (_87477 -> Prop)))). Qed.
Lemma lem3391030 {_88095 _88100 : Type'} (f : _88095 -> _88100) : (@IMAGE _88095 _88100 f (@EMPTY _88095)) = (@EMPTY _88100).
Proof. exact (@lem3391029 _88095 _88100 f). Qed.
Lemma lem3391031 {_88095 _88100 : Type'} (c : _88100) : (term39 _88095 _88100 c) = (@EMPTY _88100).
Proof. exact (@lem3391030 _88095 _88100 (term40 _88095 _88100 c)). Qed.
Lemma lem3391032 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : s = (@EMPTY _88095)) : (term23 _88095 _88100 c s) = (@EMPTY _88100).
Proof. exact (TRANS (@lem3391027 _88095 _88100 c s h1) (@lem3391031 _88095 _88100 c)). Qed.
Lemma lem3391033 {_88100 : Type'} : (@eq (_88100 -> Prop)) = (@eq (_88100 -> Prop)).
Proof. exact (eq_refl (@eq (_88100 -> Prop))). Qed.
Lemma lem3391034 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : s = (@EMPTY _88095)) : (term41 _88095 _88100 c s) = (@eq (_88100 -> Prop) (@EMPTY _88100)).
Proof. exact (MK_COMB (@lem3391033 _88100) (@lem3391032 _88095 _88100 c s h1)). Qed.
Lemma lem3391035 {_88100 : Type'} : (@EMPTY _88100) = (@EMPTY _88100).
Proof. exact (eq_refl (@EMPTY _88100)). Qed.
Lemma lem3391036 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : s = (@EMPTY _88095)) : ((term23 _88095 _88100 c s) = (@EMPTY _88100)) = ((@EMPTY _88100) = (@EMPTY _88100)).
Proof. exact (MK_COMB (@lem3391034 _88095 _88100 c s h1) (@lem3391035 _88100)). Qed.
Lemma lem3391038 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3391039 {_88100 : Type'} (x : _88100 -> Prop) : (x = x) = True.
Proof. exact (@lem3391038 (_88100 -> Prop) x). Qed.
Lemma lem3391040 {_88100 : Type'} : ((@EMPTY _88100) = (@EMPTY _88100)) = True.
Proof. exact (@lem3391039 _88100 (@EMPTY _88100)). Qed.
Lemma lem3391041 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : s = (@EMPTY _88095)) : ((term23 _88095 _88100 c s) = (@EMPTY _88100)) = True.
Proof. exact (TRANS (@lem3391036 _88095 _88100 c s h1) (@lem3391040 _88100)). Qed.
Lemma lem3391042 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : s = (@EMPTY _88095)) : True = ((term23 _88095 _88100 c s) = (@EMPTY _88100)).
Proof. exact (SYM (@lem3391041 _88095 _88100 c s h1)). Qed.
Lemma lem3391066 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term14 A s t).
Proof. exact (EQ_MP (@lem3390966 A s t) (@lem3390965 A s t)). Qed.
Lemma lem3391067 {_88100 : Type'} (s : _88100 -> Prop) (t : _88100 -> Prop) : (s = t) = (term14 _88100 s t).
Proof. exact (@lem3391066 _88100 s t). Qed.
Lemma lem3391068 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : ((term23 _88095 _88100 c s) = (@INSERT _88100 c (@EMPTY _88100))) = (term42 _88095 _88100 s c).
Proof. exact (@lem3391067 _88100 (term23 _88095 _88100 c s) (@INSERT _88100 c (@EMPTY _88100))). Qed.
Lemma lem3391078 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term9 A B y f s) = (term10 A B y f s).
Proof. exact (EQ_MP (@lem3390960 A B y f s) (@lem3390959 A B y s f)). Qed.
Lemma lem3391079 {_88095 _88100 : Type'} (y : _88100) (f : _88095 -> _88100) (s : _88095 -> Prop) : (term9 _88095 _88100 y f s) = (term10 _88095 _88100 y f s).
Proof. exact (@lem3391078 _88095 _88100 y f s). Qed.
Lemma lem3391080 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term43 _88095 _88100 x c s) = (term44 _88095 _88100 x c s).
Proof. exact (@lem3391079 _88095 _88100 x (term40 _88095 _88100 c) s). Qed.
Lemma lem3391092 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3391093 {_88095 _88100 : Type'} (f : _88095 -> _88100) (y : _88095) : (term45 _88095 _88100 f y) = (f y).
Proof. exact (@lem3391092 _88095 _88100 f y). Qed.
Lemma lem3391094 {_88095 _88100 : Type'} (c : _88100) (x : _88095) : (term46 _88095 _88100 c x) = (term47 _88095 _88100 c x).
Proof. exact (@lem3391093 _88095 _88100 (term40 _88095 _88100 c) x). Qed.
Lemma lem3391095 {_88095 _88100 : Type'} (x : _88095) (c : _88100) : (term47 _88095 _88100 c x) = c.
Proof. exact (eq_refl (term47 _88095 _88100 c x)). Qed.
Lemma lem3391096 {_88095 _88100 : Type'} (c : _88100) : (term48 _88095 _88100 c) = (term40 _88095 _88100 c).
Proof. exact (fun_ext (fun x : _88095 => @lem3391095 _88095 _88100 x c)). Qed.
Lemma lem3391097 {_88095 : Type'} (x : _88095) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3391098 {_88095 _88100 : Type'} (c : _88100) (x : _88095) : (term46 _88095 _88100 c x) = (term47 _88095 _88100 c x).
Proof. exact (MK_COMB (@lem3391096 _88095 _88100 c) (@lem3391097 _88095 x)). Qed.
Lemma lem3391099 {_88100 : Type'} : (@eq _88100) = (@eq _88100).
Proof. exact (eq_refl (@eq _88100)). Qed.
Lemma lem3391100 {_88095 _88100 : Type'} (c : _88100) (x : _88095) : (term49 _88095 _88100 c x) = (term50 _88095 _88100 c x).
Proof. exact (MK_COMB (@lem3391099 _88100) (@lem3391098 _88095 _88100 c x)). Qed.
Lemma lem3391101 {_88095 _88100 : Type'} (x : _88095) (c : _88100) : (term47 _88095 _88100 c x) = c.
Proof. exact (eq_refl (term47 _88095 _88100 c x)). Qed.
Lemma lem3391102 {_88095 _88100 : Type'} (x : _88095) (c : _88100) : ((term46 _88095 _88100 c x) = (term47 _88095 _88100 c x)) = ((term47 _88095 _88100 c x) = c).
Proof. exact (MK_COMB (@lem3391100 _88095 _88100 c x) (@lem3391101 _88095 _88100 x c)). Qed.
Lemma lem3391103 {_88095 _88100 : Type'} (x : _88095) (c : _88100) : (term47 _88095 _88100 c x) = c.
Proof. exact (EQ_MP (@lem3391102 _88095 _88100 x c) (@lem3391094 _88095 _88100 c x)). Qed.
Lemma lem3391104 {_88100 : Type'} (x : _88100) : (@eq _88100 x) = (@eq _88100 x).
Proof. exact (eq_refl (@eq _88100 x)). Qed.
Lemma lem3391105 {_88095 _88100 : Type'} (x : _88095) (x' : _88100) (c : _88100) : (x' = (term47 _88095 _88100 c x)) = (x' = c).
Proof. exact (MK_COMB (@lem3391104 _88100 x') (@lem3391103 _88095 _88100 x c)). Qed.
Lemma lem3391110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3391111 {_88095 _88100 : Type'} (x : _88095) (x' : _88100) (c : _88100) : (term51 _88095 _88100 x' c x) = (term52 _88100 x' c).
Proof. exact (MK_COMB (@lem3391110) (@lem3391105 _88095 _88100 x x' c)). Qed.
Lemma lem3391112 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (@IN _88095 x s) = (@IN _88095 x s).
Proof. exact (eq_refl (@IN _88095 x s)). Qed.
Lemma lem3391113 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (x' : _88095) (s : _88095 -> Prop) : (term53 _88095 _88100 x c x' s) = (term54 _88095 _88100 x c x' s).
Proof. exact (MK_COMB (@lem3391111 _88095 _88100 x' x c) (@lem3391112 _88095 x' s)). Qed.
Lemma lem3391116 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term55 _88095 _88100 x c s) = (term56 _88095 _88100 x c s).
Proof. exact (fun_ext (fun x' : _88095 => @lem3391113 _88095 _88100 x c x' s)). Qed.
Lemma lem3391117 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391118 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term44 _88095 _88100 x c s) = (term57 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391117 _88095) (@lem3391116 _88095 _88100 x c s)). Qed.
Lemma lem3391123 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term43 _88095 _88100 x c s) = (term57 _88095 _88100 x c s).
Proof. exact (TRANS (@lem3391080 _88095 _88100 x c s) (@lem3391118 _88095 _88100 x c s)). Qed.
Lemma lem3391124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3391125 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term58 _88095 _88100 x c s) = (term59 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391124) (@lem3391123 _88095 _88100 x c s)). Qed.
Lemma lem3391127 {A : Type'} (x : A) (y : A) : (term3 A x y) = (x = y).
Proof. exact (EQ_MP (@lem3390951 A x y) (@lem3390950 A x y)). Qed.
Lemma lem3391128 {_88100 : Type'} (x : _88100) (y : _88100) : (term3 _88100 x y) = (x = y).
Proof. exact (@lem3391127 _88100 x y). Qed.
Lemma lem3391129 {_88100 : Type'} (x : _88100) (c : _88100) : (term3 _88100 x c) = (x = c).
Proof. exact (@lem3391128 _88100 x c). Qed.
Lemma lem3391134 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : ((term43 _88095 _88100 x c s) = (term3 _88100 x c)) = ((term57 _88095 _88100 x c s) = (x = c)).
Proof. exact (MK_COMB (@lem3391125 _88095 _88100 x c s) (@lem3391129 _88100 x c)). Qed.
Lemma lem3391139 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term60 _88095 _88100 s c) = (term61 _88095 _88100 s c).
Proof. exact (fun_ext (fun x : _88100 => @lem3391134 _88095 _88100 s x c)). Qed.
Lemma lem3391140 {_88100 : Type'} : (@all _88100) = (@all _88100).
Proof. exact (eq_refl (@all _88100)). Qed.
Lemma lem3391141 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term42 _88095 _88100 s c) = (term62 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391140 _88100) (@lem3391139 _88095 _88100 s c)). Qed.
Lemma lem3391146 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : ((term23 _88095 _88100 c s) = (@INSERT _88100 c (@EMPTY _88100))) = (term62 _88095 _88100 s c).
Proof. exact (TRANS (@lem3391068 _88095 _88100 s c) (@lem3391141 _88095 _88100 s c)). Qed.
Lemma lem3391147 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term62 _88095 _88100 s c) = ((term23 _88095 _88100 c s) = (@INSERT _88100 c (@EMPTY _88100))).
Proof. exact (SYM (@lem3391146 _88095 _88100 s c)). Qed.
Lemma lem3391149 (p : Prop) : p = (term63 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3391150 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term62 _88095 _88100 s c) = (term64 _88095 _88100 s c).
Proof. exact (@lem3391149 (term62 _88095 _88100 s c)). Qed.
Lemma lem3391151 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term64 _88095 _88100 s c) = (term62 _88095 _88100 s c).
Proof. exact (SYM (@lem3391150 _88095 _88100 s c)). Qed.
Lemma lem3391152 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) (h1 : term65 _88095 _88100 s c) : term65 _88095 _88100 s c.
Proof. exact (h1). Qed.
Lemma lem3391153 {_88095 : Type'} : term66 _88095.
Proof. exact (@lem3216368 _88095). Qed.
Lemma lem3391158 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) (h1 : term67 _88095 _88100 s c) : term67 _88095 _88100 s c.
Proof. exact (h1). Qed.
Lemma lem3391159 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : term68 _88095 _88100 s c.
Proof. exact (fun h0 : term67 _88095 _88100 s c => @lem3391158 _88095 _88100 s c h0). Qed.
Lemma lem3391160 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) (h1 : term68 _88095 _88100 s c) : term68 _88095 _88100 s c.
Proof. exact (h1). Qed.
Lemma lem3391161 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) (h1 : term67 _88095 _88100 s c) : term67 _88095 _88100 s c.
Proof. exact (h1). Qed.
Lemma lem3391162 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) (h1 : term67 _88095 _88100 s c) (h2 : term68 _88095 _88100 s c) : term67 _88095 _88100 s c.
Proof. exact (@lem3391160 _88095 _88100 s c h2 (@lem3391161 _88095 _88100 s c h1)). Qed.
Lemma lem3391163 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) (h1 : term67 _88095 _88100 s c) : term69 _88095 _88100 s c.
Proof. exact (fun h0 : term68 _88095 _88100 s c => @lem3391162 _88095 _88100 s c h1 h0). Qed.
Lemma lem3391164 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) (h1 : term68 _88095 _88100 s c) : term68 _88095 _88100 s c.
Proof. exact (h1). Qed.
Lemma lem3391165 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) (h1 : term67 _88095 _88100 s c) (h2 : term68 _88095 _88100 s c) : term67 _88095 _88100 s c.
Proof. exact (@lem3391163 _88095 _88100 s c h1 (@lem3391164 _88095 _88100 s c h2)). Qed.
Lemma lem3391166 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) (h1 : term68 _88095 _88100 s c) : term68 _88095 _88100 s c.
Proof. exact (fun h0 : term67 _88095 _88100 s c => @lem3391165 _88095 _88100 s c h0 h1). Qed.
Lemma lem3391167 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : term70 _88095 _88100 s c.
Proof. exact (fun h0 : term68 _88095 _88100 s c => @lem3391166 _88095 _88100 s c h0). Qed.
Lemma lem3391170 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : term68 _88095 _88100 s c.
Proof. exact (@lem3391167 _88095 _88100 s c (@lem3391159 _88095 _88100 s c)). Qed.
Lemma lem3391171 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : term68 _88095 _88100 s c.
Proof. exact (@lem3391170 _88095 _88100 s c). Qed.
Lemma lem3391189 {A : Type'} (P : Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem3391190 {_88095 : Type'} (P : Prop) (Q : _88095 -> Prop) : (term71 _88095 P Q) = (term72 _88095 P Q).
Proof. exact (@lem3391189 _88095 P Q). Qed.
Lemma lem3391191 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term73 _88095 _88100 x c s) = (term74 _88095 _88100 x c s).
Proof. exact (@lem3391190 _88095 (x = c) (term75 _88095 s)). Qed.
Lemma lem3391192 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term76 _88095 s x) = (@IN _88095 x s).
Proof. exact (eq_refl (term76 _88095 s x)). Qed.
Lemma lem3391193 {_88100 : Type'} (x : _88100) (c : _88100) : (term52 _88100 x c) = (term52 _88100 x c).
Proof. exact (eq_refl (term52 _88100 x c)). Qed.
Lemma lem3391194 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (x' : _88095) (s : _88095 -> Prop) : (term77 _88095 _88100 x c s x') = (term54 _88095 _88100 x c x' s).
Proof. exact (MK_COMB (@lem3391193 _88100 x c) (@lem3391192 _88095 x' s)). Qed.
Lemma lem3391195 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term78 _88095 _88100 x c s) = (term56 _88095 _88100 x c s).
Proof. exact (fun_ext (fun x' : _88095 => @lem3391194 _88095 _88100 x c x' s)). Qed.
Lemma lem3391196 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391197 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term73 _88095 _88100 x c s) = (term57 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391196 _88095) (@lem3391195 _88095 _88100 x c s)). Qed.
Lemma lem3391198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3391199 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term79 _88095 _88100 x c s) = (term59 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391198) (@lem3391197 _88095 _88100 x c s)). Qed.
Lemma lem3391200 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term76 _88095 s x) = (@IN _88095 x s).
Proof. exact (eq_refl (term76 _88095 s x)). Qed.
Lemma lem3391201 {_88095 : Type'} (s : _88095 -> Prop) : (term80 _88095 s) = (term75 _88095 s).
Proof. exact (fun_ext (fun x : _88095 => @lem3391200 _88095 x s)). Qed.
Lemma lem3391202 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391203 {_88095 : Type'} (s : _88095 -> Prop) : (term81 _88095 s) = (term82 _88095 s).
Proof. exact (MK_COMB (@lem3391202 _88095) (@lem3391201 _88095 s)). Qed.
Lemma lem3391204 {_88100 : Type'} (x : _88100) (c : _88100) : (term52 _88100 x c) = (term52 _88100 x c).
Proof. exact (eq_refl (term52 _88100 x c)). Qed.
Lemma lem3391205 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term74 _88095 _88100 x c s) = (term83 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391204 _88100 x c) (@lem3391203 _88095 s)). Qed.
Lemma lem3391206 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : ((term73 _88095 _88100 x c s) = (term74 _88095 _88100 x c s)) = ((term57 _88095 _88100 x c s) = (term83 _88095 _88100 x c s)).
Proof. exact (MK_COMB (@lem3391199 _88095 _88100 x c s) (@lem3391205 _88095 _88100 x c s)). Qed.
Lemma lem3391207 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term57 _88095 _88100 x c s) = (term83 _88095 _88100 x c s).
Proof. exact (EQ_MP (@lem3391206 _88095 _88100 x c s) (@lem3391191 _88095 _88100 x c s)). Qed.
Lemma lem3391214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3391215 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term59 _88095 _88100 x c s) = (term84 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391214) (@lem3391207 _88095 _88100 x c s)). Qed.
Lemma lem3391216 {_88100 : Type'} (x : _88100) (c : _88100) : (x = c) = (x = c).
Proof. exact (eq_refl (x = c)). Qed.
Lemma lem3391217 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : ((term57 _88095 _88100 x c s) = (x = c)) = ((term83 _88095 _88100 x c s) = (x = c)).
Proof. exact (MK_COMB (@lem3391215 _88095 _88100 x c s) (@lem3391216 _88100 x c)). Qed.
Lemma lem3391218 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term61 _88095 _88100 s c) = (term85 _88095 _88100 s c).
Proof. exact (fun_ext (fun x : _88100 => @lem3391217 _88095 _88100 s x c)). Qed.
Lemma lem3391219 {_88100 : Type'} : (@all _88100) = (@all _88100).
Proof. exact (eq_refl (@all _88100)). Qed.
Lemma lem3391220 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term62 _88095 _88100 s c) = (term86 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391219 _88100) (@lem3391218 _88095 _88100 s c)). Qed.
Lemma lem3391225 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3391226 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term65 _88095 _88100 s c) = (term87 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391225) (@lem3391220 _88095 _88100 s c)). Qed.
Lemma lem3391227 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3391228 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term88 _88095 _88100 s c) = (term89 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391227) (@lem3391226 _88095 _88100 s c)). Qed.
Lemma lem3391230 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3391231 {_88095 : Type'} : (term90 _88095) = (term91 _88095).
Proof. exact (@lem3391230 (term66 _88095)). Qed.
Lemma lem3391240 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term92 _88095 _88100 s c) = (term93 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391228 _88095 _88100 s c) (@lem3391231 _88095)). Qed.
Lemma lem3391243 {_88095 : Type'} (s : _88095 -> Prop) : (term24 _88095 s) = (term24 _88095 s).
Proof. exact (eq_refl (term24 _88095 s)). Qed.
Lemma lem3391244 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term67 _88095 _88100 s c) = (term94 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391243 _88095 s) (@lem3391240 _88095 _88100 s c)). Qed.
Lemma lem3391247 {_88095 _88100 : Type'} (c : _88100) : (term95 _88095 _88100 c) = (term96 _88095 _88100 c).
Proof. exact (fun_ext (fun s : _88095 -> Prop => @lem3391244 _88095 _88100 s c)). Qed.
Lemma lem3391248 {_88095 : Type'} : (@all (_88095 -> Prop)) = (@all (_88095 -> Prop)).
Proof. exact (eq_refl (@all (_88095 -> Prop))). Qed.
Lemma lem3391249 {_88095 _88100 : Type'} (c : _88100) : (term97 _88095 _88100 c) = (term98 _88095 _88100 c).
Proof. exact (MK_COMB (@lem3391248 _88095) (@lem3391247 _88095 _88100 c)). Qed.
Lemma lem3391254 {_88095 _88100 : Type'} : (term99 _88095 _88100) = (term100 _88095 _88100).
Proof. exact (fun_ext (fun c : _88100 => @lem3391249 _88095 _88100 c)). Qed.
Lemma lem3391255 {_88100 : Type'} : (@all _88100) = (@all _88100).
Proof. exact (eq_refl (@all _88100)). Qed.
Lemma lem3391264 {_88095 _88100 : Type'} : (term101 _88095 _88100) = (term102 _88095 _88100).
Proof. exact (MK_COMB (@lem3391255 _88100) (@lem3391254 _88095 _88100)). Qed.
Lemma lem3391267 {_88095 : Type'} (s : _88095 -> Prop) : (term37 _88095 s) = (term37 _88095 s).
Proof. exact (eq_refl (term37 _88095 s)). Qed.
Lemma lem3391268 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (@IN _88095 x s) = (@IN _88095 x s).
Proof. exact (eq_refl (@IN _88095 x s)). Qed.
Lemma lem3391269 {_88095 : Type'} (s : _88095 -> Prop) : (term75 _88095 s) = (term75 _88095 s).
Proof. exact (fun_ext (fun x : _88095 => @lem3391268 _88095 x s)). Qed.
Lemma lem3391270 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391271 {_88095 : Type'} (s : _88095 -> Prop) : (term82 _88095 s) = (term82 _88095 s).
Proof. exact (MK_COMB (@lem3391270 _88095) (@lem3391269 _88095 s)). Qed.
Lemma lem3391272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3391273 {_88095 : Type'} (s : _88095 -> Prop) : (term103 _88095 s) = (term103 _88095 s).
Proof. exact (MK_COMB (@lem3391272) (@lem3391271 _88095 s)). Qed.
Lemma lem3391274 {_88095 : Type'} (s : _88095 -> Prop) : ((term82 _88095 s) = (term37 _88095 s)) = ((term82 _88095 s) = (term37 _88095 s)).
Proof. exact (MK_COMB (@lem3391273 _88095 s) (@lem3391267 _88095 s)). Qed.
Lemma lem3391275 {_88095 : Type'} : (term104 _88095) = (term104 _88095).
Proof. exact (fun_ext (fun s : _88095 -> Prop => @lem3391274 _88095 s)). Qed.
Lemma lem3391276 {_88095 : Type'} : (@all (_88095 -> Prop)) = (@all (_88095 -> Prop)).
Proof. exact (eq_refl (@all (_88095 -> Prop))). Qed.
Lemma lem3391277 {_88095 : Type'} : (term66 _88095) = (term66 _88095).
Proof. exact (MK_COMB (@lem3391276 _88095) (@lem3391275 _88095)). Qed.
Lemma lem3391278 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3391279 {_88095 : Type'} : (term91 _88095) = (term91 _88095).
Proof. exact (MK_COMB (@lem3391278) (@lem3391277 _88095)). Qed.
Lemma lem3391280 {_88100 : Type'} (x : _88100) (c : _88100) : (x = c) = (x = c).
Proof. exact (eq_refl (x = c)). Qed.
Lemma lem3391281 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (@IN _88095 x s) = (@IN _88095 x s).
Proof. exact (eq_refl (@IN _88095 x s)). Qed.
Lemma lem3391282 {_88095 : Type'} (s : _88095 -> Prop) : (term75 _88095 s) = (term75 _88095 s).
Proof. exact (fun_ext (fun x : _88095 => @lem3391281 _88095 x s)). Qed.
Lemma lem3391283 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391284 {_88095 : Type'} (s : _88095 -> Prop) : (term82 _88095 s) = (term82 _88095 s).
Proof. exact (MK_COMB (@lem3391283 _88095) (@lem3391282 _88095 s)). Qed.
Lemma lem3391287 {_88100 : Type'} (x : _88100) (c : _88100) : (term52 _88100 x c) = (term52 _88100 x c).
Proof. exact (eq_refl (term52 _88100 x c)). Qed.
Lemma lem3391288 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term83 _88095 _88100 x c s) = (term83 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391287 _88100 x c) (@lem3391284 _88095 s)). Qed.
Lemma lem3391289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3391290 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term84 _88095 _88100 x c s) = (term84 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391289) (@lem3391288 _88095 _88100 x c s)). Qed.
Lemma lem3391291 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : ((term83 _88095 _88100 x c s) = (x = c)) = ((term83 _88095 _88100 x c s) = (x = c)).
Proof. exact (MK_COMB (@lem3391290 _88095 _88100 x c s) (@lem3391280 _88100 x c)). Qed.
Lemma lem3391292 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term85 _88095 _88100 s c) = (term85 _88095 _88100 s c).
Proof. exact (fun_ext (fun x : _88100 => @lem3391291 _88095 _88100 s x c)). Qed.
Lemma lem3391293 {_88100 : Type'} : (@all _88100) = (@all _88100).
Proof. exact (eq_refl (@all _88100)). Qed.
Lemma lem3391294 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term86 _88095 _88100 s c) = (term86 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391293 _88100) (@lem3391292 _88095 _88100 s c)). Qed.
Lemma lem3391295 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3391296 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term87 _88095 _88100 s c) = (term87 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391295) (@lem3391294 _88095 _88100 s c)). Qed.
Lemma lem3391297 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3391298 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term89 _88095 _88100 s c) = (term89 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391297) (@lem3391296 _88095 _88100 s c)). Qed.
Lemma lem3391299 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term93 _88095 _88100 s c) = (term93 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391298 _88095 _88100 s c) (@lem3391279 _88095)). Qed.
Lemma lem3391304 {_88095 : Type'} (s : _88095 -> Prop) : (term24 _88095 s) = (term24 _88095 s).
Proof. exact (eq_refl (term24 _88095 s)). Qed.
Lemma lem3391305 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term94 _88095 _88100 s c) = (term94 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391304 _88095 s) (@lem3391299 _88095 _88100 s c)). Qed.
Lemma lem3391306 {_88095 _88100 : Type'} (c : _88100) : (term96 _88095 _88100 c) = (term96 _88095 _88100 c).
Proof. exact (fun_ext (fun s : _88095 -> Prop => @lem3391305 _88095 _88100 s c)). Qed.
Lemma lem3391307 {_88095 : Type'} : (@all (_88095 -> Prop)) = (@all (_88095 -> Prop)).
Proof. exact (eq_refl (@all (_88095 -> Prop))). Qed.
Lemma lem3391308 {_88095 _88100 : Type'} (c : _88100) : (term98 _88095 _88100 c) = (term98 _88095 _88100 c).
Proof. exact (MK_COMB (@lem3391307 _88095) (@lem3391306 _88095 _88100 c)). Qed.
Lemma lem3391309 {_88095 _88100 : Type'} : (term100 _88095 _88100) = (term100 _88095 _88100).
Proof. exact (fun_ext (fun c : _88100 => @lem3391308 _88095 _88100 c)). Qed.
Lemma lem3391310 {_88100 : Type'} : (@all _88100) = (@all _88100).
Proof. exact (eq_refl (@all _88100)). Qed.
Lemma lem3391311 {_88095 _88100 : Type'} : (term102 _88095 _88100) = (term102 _88095 _88100).
Proof. exact (MK_COMB (@lem3391310 _88100) (@lem3391309 _88095 _88100)). Qed.
Lemma lem3391356 {_88095 _88100 : Type'} : (term101 _88095 _88100) = (term102 _88095 _88100).
Proof. exact (TRANS (@lem3391264 _88095 _88100) (@lem3391311 _88095 _88100)). Qed.
Lemma lem3391357 {_88095 _88100 : Type'} : (term102 _88095 _88100) = (term101 _88095 _88100).
Proof. exact (SYM (@lem3391356 _88095 _88100)). Qed.
Lemma lem3391359 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) (h1 : term87 _88095 _88100 s c) : term87 _88095 _88100 s c.
Proof. exact (h1). Qed.
Lemma lem3391360 {_88095 : Type'} (h1 : term66 _88095) : term66 _88095.
Proof. exact (h1). Qed.
Lemma lem3391366 {_88095 : Type'} (s : _88095 -> Prop) (h1 : term37 _88095 s) : term37 _88095 s.
Proof. exact (h1). Qed.
Lemma lem3391370 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (@IN _88095 x s) = (@IN _88095 x s).
Proof. exact (eq_refl (@IN _88095 x s)). Qed.
Lemma lem3391371 {_88095 : Type'} (P : _88095 -> Prop) : (term105 _88095 P) = (term106 _88095 P).
Proof. exact (@lem18394 _88095 P). Qed.
Lemma lem3391372 {_88095 : Type'} (s : _88095 -> Prop) : (term107 _88095 s) = (term108 _88095 s).
Proof. exact (@lem3391371 _88095 (term75 _88095 s)). Qed.
Lemma lem3391373 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term76 _88095 s x) = (@IN _88095 x s).
Proof. exact (eq_refl (term76 _88095 s x)). Qed.
Lemma lem3391374 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3391376 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term109 _88095 s x) = (term110 _88095 x s).
Proof. exact (MK_COMB (@lem3391374) (@lem3391373 _88095 x s)). Qed.
Lemma lem3391377 {_88095 : Type'} (s : _88095 -> Prop) : (term111 _88095 s) = (term112 _88095 s).
Proof. exact (fun_ext (fun x : _88095 => @lem3391376 _88095 x s)). Qed.
Lemma lem3391378 {_88095 : Type'} : (@all _88095) = (@all _88095).
Proof. exact (eq_refl (@all _88095)). Qed.
Lemma lem3391379 {_88095 : Type'} (s : _88095 -> Prop) : (term108 _88095 s) = (term113 _88095 s).
Proof. exact (MK_COMB (@lem3391378 _88095) (@lem3391377 _88095 s)). Qed.
Lemma lem3391380 {_88095 : Type'} (s : _88095 -> Prop) : (term107 _88095 s) = (term113 _88095 s).
Proof. exact (TRANS (@lem3391372 _88095 s) (@lem3391379 _88095 s)). Qed.
Lemma lem3391381 {_88095 : Type'} (s : _88095 -> Prop) : (term75 _88095 s) = (term75 _88095 s).
Proof. exact (fun_ext (fun x : _88095 => @lem3391370 _88095 x s)). Qed.
Lemma lem3391382 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391383 {_88095 : Type'} (s : _88095 -> Prop) : (term82 _88095 s) = (term82 _88095 s).
Proof. exact (MK_COMB (@lem3391382 _88095) (@lem3391381 _88095 s)). Qed.
Lemma lem3391385 {_88100 : Type'} (x : _88100) (c : _88100) : (term114 _88100 x c) = (term114 _88100 x c).
Proof. exact (eq_refl (term114 _88100 x c)). Qed.
Lemma lem3391386 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term115 _88095 _88100 x c s) = (term116 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391385 _88100 x c) (@lem3391380 _88095 s)). Qed.
Lemma lem3391387 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term117 _88095 _88100 x c s) = (term115 _88095 _88100 x c s).
Proof. exact (@lem17045 (x = c) (term82 _88095 s)). Qed.
Lemma lem3391388 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term117 _88095 _88100 x c s) = (term116 _88095 _88100 x c s).
Proof. exact (TRANS (@lem3391387 _88095 _88100 x c s) (@lem3391386 _88095 _88100 x c s)). Qed.
Lemma lem3391390 {_88100 : Type'} (x : _88100) (c : _88100) : (term52 _88100 x c) = (term52 _88100 x c).
Proof. exact (eq_refl (term52 _88100 x c)). Qed.
Lemma lem3391391 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term83 _88095 _88100 x c s) = (term83 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391390 _88100 x c) (@lem3391383 _88095 s)). Qed.
Lemma lem3391392 {_88100 : Type'} (x : _88100) (c : _88100) : (term118 _88100 x c) = (term118 _88100 x c).
Proof. exact (eq_refl (term118 _88100 x c)). Qed.
Lemma lem3391393 {_88100 : Type'} (x : _88100) (c : _88100) : (x = c) = (x = c).
Proof. exact (eq_refl (x = c)). Qed.
Lemma lem3391394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3391395 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term119 _88095 _88100 x c s) = (term120 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391394) (@lem3391388 _88095 _88100 x c s)). Qed.
Lemma lem3391396 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term121 _88095 _88100 s x c) = (term122 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391395 _88095 _88100 x c s) (@lem3391393 _88100 x c)). Qed.
Lemma lem3391397 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3391398 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term123 _88095 _88100 x c s) = (term123 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391397) (@lem3391391 _88095 _88100 x c s)). Qed.
Lemma lem3391399 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term124 _88095 _88100 s x c) = (term124 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391398 _88095 _88100 x c s) (@lem3391392 _88100 x c)). Qed.
Lemma lem3391400 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3391401 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term125 _88095 _88100 s x c) = (term125 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391400) (@lem3391399 _88095 _88100 s x c)). Qed.
Lemma lem3391402 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term126 _88095 _88100 s x c) = (term127 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391401 _88095 _88100 s x c) (@lem3391396 _88095 _88100 s x c)). Qed.
Lemma lem3391403 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term128 _88095 _88100 s x c) = (term126 _88095 _88100 s x c).
Proof. exact (@lem17646 (term83 _88095 _88100 x c s) (x = c)). Qed.
Lemma lem3391404 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term128 _88095 _88100 s x c) = (term127 _88095 _88100 s x c).
Proof. exact (TRANS (@lem3391403 _88095 _88100 s x c) (@lem3391402 _88095 _88100 s x c)). Qed.
Lemma lem3391405 {_88100 : Type'} (P : _88100 -> Prop) : (term129 _88100 P) = (term130 _88100 P).
Proof. exact (@lem18392 _88100 P). Qed.
Lemma lem3391406 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term87 _88095 _88100 s c) = (term131 _88095 _88100 s c).
Proof. exact (@lem3391405 _88100 (term85 _88095 _88100 s c)). Qed.
Lemma lem3391407 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term132 _88095 _88100 s c x) = ((term83 _88095 _88100 x c s) = (x = c)).
Proof. exact (eq_refl (term132 _88095 _88100 s c x)). Qed.
Lemma lem3391408 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3391409 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term133 _88095 _88100 s c x) = (term128 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391408) (@lem3391407 _88095 _88100 s x c)). Qed.
Lemma lem3391410 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term133 _88095 _88100 s c x) = (term127 _88095 _88100 s x c).
Proof. exact (TRANS (@lem3391409 _88095 _88100 s x c) (@lem3391404 _88095 _88100 s x c)). Qed.
Lemma lem3391411 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term134 _88095 _88100 s c) = (term135 _88095 _88100 s c).
Proof. exact (fun_ext (fun x : _88100 => @lem3391410 _88095 _88100 s x c)). Qed.
Lemma lem3391412 {_88100 : Type'} : (@ex _88100) = (@ex _88100).
Proof. exact (eq_refl (@ex _88100)). Qed.
Lemma lem3391413 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term131 _88095 _88100 s c) = (term136 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391412 _88100) (@lem3391411 _88095 _88100 s c)). Qed.
Lemma lem3391414 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term87 _88095 _88100 s c) = (term136 _88095 _88100 s c).
Proof. exact (TRANS (@lem3391406 _88095 _88100 s c) (@lem3391413 _88095 _88100 s c)). Qed.
Lemma lem3391416 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3391417 {_88100 : Type'} (P : _88100 -> Prop) (Q : _88100 -> Prop) : (term137 _88100 P Q) = (term138 _88100 P Q).
Proof. exact (@lem3391416 _88100 P Q). Qed.
Lemma lem3391418 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term139 _88095 _88100 s c) = (term140 _88095 _88100 s c).
Proof. exact (@lem3391417 _88100 (term141 _88095 _88100 s c) (term142 _88095 _88100 s c)). Qed.
Lemma lem3391419 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term143 _88095 _88100 s c x) = (term124 _88095 _88100 s x c).
Proof. exact (eq_refl (term143 _88095 _88100 s c x)). Qed.
Lemma lem3391420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3391421 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term144 _88095 _88100 s c x) = (term125 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391420) (@lem3391419 _88095 _88100 s x c)). Qed.
Lemma lem3391422 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term145 _88095 _88100 s c x) = (term122 _88095 _88100 s x c).
Proof. exact (eq_refl (term145 _88095 _88100 s c x)). Qed.
Lemma lem3391423 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term146 _88095 _88100 s c x) = (term127 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391421 _88095 _88100 s x c) (@lem3391422 _88095 _88100 s x c)). Qed.
Lemma lem3391424 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term147 _88095 _88100 s c) = (term135 _88095 _88100 s c).
Proof. exact (fun_ext (fun x : _88100 => @lem3391423 _88095 _88100 s x c)). Qed.
Lemma lem3391425 {_88100 : Type'} : (@ex _88100) = (@ex _88100).
Proof. exact (eq_refl (@ex _88100)). Qed.
Lemma lem3391426 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term139 _88095 _88100 s c) = (term136 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391425 _88100) (@lem3391424 _88095 _88100 s c)). Qed.
Lemma lem3391427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3391428 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term148 _88095 _88100 s c) = (term149 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391427) (@lem3391426 _88095 _88100 s c)). Qed.
Lemma lem3391429 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term143 _88095 _88100 s c x) = (term124 _88095 _88100 s x c).
Proof. exact (eq_refl (term143 _88095 _88100 s c x)). Qed.
Lemma lem3391430 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term150 _88095 _88100 s c) = (term141 _88095 _88100 s c).
Proof. exact (fun_ext (fun x : _88100 => @lem3391429 _88095 _88100 s x c)). Qed.
Lemma lem3391431 {_88100 : Type'} : (@ex _88100) = (@ex _88100).
Proof. exact (eq_refl (@ex _88100)). Qed.
Lemma lem3391432 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term151 _88095 _88100 s c) = (term152 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391431 _88100) (@lem3391430 _88095 _88100 s c)). Qed.
Lemma lem3391433 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3391434 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term153 _88095 _88100 s c) = (term154 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391433) (@lem3391432 _88095 _88100 s c)). Qed.
Lemma lem3391435 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term145 _88095 _88100 s c x) = (term122 _88095 _88100 s x c).
Proof. exact (eq_refl (term145 _88095 _88100 s c x)). Qed.
Lemma lem3391436 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term155 _88095 _88100 s c) = (term142 _88095 _88100 s c).
Proof. exact (fun_ext (fun x : _88100 => @lem3391435 _88095 _88100 s x c)). Qed.
Lemma lem3391437 {_88100 : Type'} : (@ex _88100) = (@ex _88100).
Proof. exact (eq_refl (@ex _88100)). Qed.
Lemma lem3391438 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term156 _88095 _88100 s c) = (term157 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391437 _88100) (@lem3391436 _88095 _88100 s c)). Qed.
Lemma lem3391439 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term140 _88095 _88100 s c) = (term158 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391434 _88095 _88100 s c) (@lem3391438 _88095 _88100 s c)). Qed.
Lemma lem3391440 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : ((term139 _88095 _88100 s c) = (term140 _88095 _88100 s c)) = ((term136 _88095 _88100 s c) = (term158 _88095 _88100 s c)).
Proof. exact (MK_COMB (@lem3391428 _88095 _88100 s c) (@lem3391439 _88095 _88100 s c)). Qed.
Lemma lem3391441 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term136 _88095 _88100 s c) = (term158 _88095 _88100 s c).
Proof. exact (EQ_MP (@lem3391440 _88095 _88100 s c) (@lem3391418 _88095 _88100 s c)). Qed.
Lemma lem3391547 {A : Type'} (P : Prop) (Q : A -> Prop) : (term72 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3391548 {_88095 : Type'} (P : Prop) (Q : _88095 -> Prop) : (term72 _88095 P Q) = (term71 _88095 P Q).
Proof. exact (@lem3391547 _88095 P Q). Qed.
Lemma lem3391549 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term74 _88095 _88100 x c s) = (term73 _88095 _88100 x c s).
Proof. exact (@lem3391548 _88095 (x = c) (term75 _88095 s)). Qed.
Lemma lem3391550 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term76 _88095 s x) = (@IN _88095 x s).
Proof. exact (eq_refl (term76 _88095 s x)). Qed.
Lemma lem3391551 {_88095 : Type'} (s : _88095 -> Prop) : (term80 _88095 s) = (term75 _88095 s).
Proof. exact (fun_ext (fun x : _88095 => @lem3391550 _88095 x s)). Qed.
Lemma lem3391552 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391553 {_88095 : Type'} (s : _88095 -> Prop) : (term81 _88095 s) = (term82 _88095 s).
Proof. exact (MK_COMB (@lem3391552 _88095) (@lem3391551 _88095 s)). Qed.
Lemma lem3391554 {_88100 : Type'} (x : _88100) (c : _88100) : (term52 _88100 x c) = (term52 _88100 x c).
Proof. exact (eq_refl (term52 _88100 x c)). Qed.
Lemma lem3391555 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term74 _88095 _88100 x c s) = (term83 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391554 _88100 x c) (@lem3391553 _88095 s)). Qed.
Lemma lem3391556 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3391557 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term159 _88095 _88100 x c s) = (term84 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391556) (@lem3391555 _88095 _88100 x c s)). Qed.
Lemma lem3391558 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term76 _88095 s x) = (@IN _88095 x s).
Proof. exact (eq_refl (term76 _88095 s x)). Qed.
Lemma lem3391559 {_88100 : Type'} (x : _88100) (c : _88100) : (term52 _88100 x c) = (term52 _88100 x c).
Proof. exact (eq_refl (term52 _88100 x c)). Qed.
Lemma lem3391560 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (x' : _88095) (s : _88095 -> Prop) : (term77 _88095 _88100 x c s x') = (term54 _88095 _88100 x c x' s).
Proof. exact (MK_COMB (@lem3391559 _88100 x c) (@lem3391558 _88095 x' s)). Qed.
Lemma lem3391561 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term78 _88095 _88100 x c s) = (term56 _88095 _88100 x c s).
Proof. exact (fun_ext (fun x' : _88095 => @lem3391560 _88095 _88100 x c x' s)). Qed.
Lemma lem3391562 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391563 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term73 _88095 _88100 x c s) = (term57 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391562 _88095) (@lem3391561 _88095 _88100 x c s)). Qed.
Lemma lem3391564 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : ((term74 _88095 _88100 x c s) = (term73 _88095 _88100 x c s)) = ((term83 _88095 _88100 x c s) = (term57 _88095 _88100 x c s)).
Proof. exact (MK_COMB (@lem3391557 _88095 _88100 x c s) (@lem3391563 _88095 _88100 x c s)). Qed.
Lemma lem3391565 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term83 _88095 _88100 x c s) = (term57 _88095 _88100 x c s).
Proof. exact (EQ_MP (@lem3391564 _88095 _88100 x c s) (@lem3391549 _88095 _88100 x c s)). Qed.
Lemma lem3391566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3391567 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term123 _88095 _88100 x c s) = (term160 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391566) (@lem3391565 _88095 _88100 x c s)). Qed.
Lemma lem3391568 {_88100 : Type'} (x : _88100) (c : _88100) : (term118 _88100 x c) = (term118 _88100 x c).
Proof. exact (eq_refl (term118 _88100 x c)). Qed.
Lemma lem3391569 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term124 _88095 _88100 s x c) = (term161 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391567 _88095 _88100 x c s) (@lem3391568 _88100 x c)). Qed.
Lemma lem3391571 {A : Type'} (P : A -> Prop) (Q : Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3391572 {_88095 : Type'} (P : _88095 -> Prop) (Q : Prop) : (term162 _88095 P Q) = (term163 _88095 P Q).
Proof. exact (@lem3391571 _88095 P Q). Qed.
Lemma lem3391573 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term164 _88095 _88100 s x c) = (term165 _88095 _88100 s x c).
Proof. exact (@lem3391572 _88095 (term56 _88095 _88100 x c s) (term118 _88100 x c)). Qed.
Lemma lem3391574 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (x' : _88095) (s : _88095 -> Prop) : (term166 _88095 _88100 x c s x') = (term54 _88095 _88100 x c x' s).
Proof. exact (eq_refl (term166 _88095 _88100 x c s x')). Qed.
Lemma lem3391575 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term167 _88095 _88100 x c s) = (term56 _88095 _88100 x c s).
Proof. exact (fun_ext (fun x' : _88095 => @lem3391574 _88095 _88100 x c x' s)). Qed.
Lemma lem3391576 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391577 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term168 _88095 _88100 x c s) = (term57 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391576 _88095) (@lem3391575 _88095 _88100 x c s)). Qed.
Lemma lem3391578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3391579 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (s : _88095 -> Prop) : (term169 _88095 _88100 x c s) = (term160 _88095 _88100 x c s).
Proof. exact (MK_COMB (@lem3391578) (@lem3391577 _88095 _88100 x c s)). Qed.
Lemma lem3391580 {_88100 : Type'} (x : _88100) (c : _88100) : (term118 _88100 x c) = (term118 _88100 x c).
Proof. exact (eq_refl (term118 _88100 x c)). Qed.
Lemma lem3391581 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term164 _88095 _88100 s x c) = (term161 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391579 _88095 _88100 x c s) (@lem3391580 _88100 x c)). Qed.
Lemma lem3391582 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3391583 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term170 _88095 _88100 s x c) = (term171 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391582) (@lem3391581 _88095 _88100 s x c)). Qed.
Lemma lem3391584 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (x' : _88095) (s : _88095 -> Prop) : (term166 _88095 _88100 x c s x') = (term54 _88095 _88100 x c x' s).
Proof. exact (eq_refl (term166 _88095 _88100 x c s x')). Qed.
Lemma lem3391585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3391586 {_88095 _88100 : Type'} (x : _88100) (c : _88100) (x' : _88095) (s : _88095 -> Prop) : (term172 _88095 _88100 x c s x') = (term173 _88095 _88100 x c x' s).
Proof. exact (MK_COMB (@lem3391585) (@lem3391584 _88095 _88100 x c x' s)). Qed.
Lemma lem3391587 {_88100 : Type'} (x : _88100) (c : _88100) : (term118 _88100 x c) = (term118 _88100 x c).
Proof. exact (eq_refl (term118 _88100 x c)). Qed.
Lemma lem3391588 {_88095 _88100 : Type'} (x : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) : (term174 _88095 _88100 s x x' c) = (term175 _88095 _88100 x s x' c).
Proof. exact (MK_COMB (@lem3391586 _88095 _88100 x' c x s) (@lem3391587 _88100 x' c)). Qed.
Lemma lem3391589 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term176 _88095 _88100 s x c) = (term177 _88095 _88100 s x c).
Proof. exact (fun_ext (fun x' : _88095 => @lem3391588 _88095 _88100 x' s x c)). Qed.
Lemma lem3391590 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391591 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term165 _88095 _88100 s x c) = (term178 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391590 _88095) (@lem3391589 _88095 _88100 s x c)). Qed.
Lemma lem3391592 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : ((term164 _88095 _88100 s x c) = (term165 _88095 _88100 s x c)) = ((term161 _88095 _88100 s x c) = (term178 _88095 _88100 s x c)).
Proof. exact (MK_COMB (@lem3391583 _88095 _88100 s x c) (@lem3391591 _88095 _88100 s x c)). Qed.
Lemma lem3391593 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term161 _88095 _88100 s x c) = (term178 _88095 _88100 s x c).
Proof. exact (EQ_MP (@lem3391592 _88095 _88100 s x c) (@lem3391573 _88095 _88100 s x c)). Qed.
Lemma lem3391594 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term124 _88095 _88100 s x c) = (term178 _88095 _88100 s x c).
Proof. exact (TRANS (@lem3391569 _88095 _88100 s x c) (@lem3391593 _88095 _88100 s x c)). Qed.
Lemma lem3391595 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term141 _88095 _88100 s c) = (term179 _88095 _88100 s c).
Proof. exact (fun_ext (fun x : _88100 => @lem3391594 _88095 _88100 s x c)). Qed.
Lemma lem3391596 {_88100 : Type'} : (@ex _88100) = (@ex _88100).
Proof. exact (eq_refl (@ex _88100)). Qed.
Lemma lem3391597 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term152 _88095 _88100 s c) = (term180 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391596 _88100) (@lem3391595 _88095 _88100 s c)). Qed.
Lemma lem3391598 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3391599 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term154 _88095 _88100 s c) = (term181 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391598) (@lem3391597 _88095 _88100 s c)). Qed.
Lemma lem3391600 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term157 _88095 _88100 s c) = (term157 _88095 _88100 s c).
Proof. exact (eq_refl (term157 _88095 _88100 s c)). Qed.
Lemma lem3391601 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term158 _88095 _88100 s c) = (term182 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391599 _88095 _88100 s c) (@lem3391600 _88095 _88100 s c)). Qed.
Lemma lem3391603 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term138 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3391604 {_88100 : Type'} (P : _88100 -> Prop) (Q : _88100 -> Prop) : (term138 _88100 P Q) = (term137 _88100 P Q).
Proof. exact (@lem3391603 _88100 P Q). Qed.
Lemma lem3391605 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term183 _88095 _88100 s c) = (term184 _88095 _88100 s c).
Proof. exact (@lem3391604 _88100 (term179 _88095 _88100 s c) (term142 _88095 _88100 s c)). Qed.
Lemma lem3391606 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term185 _88095 _88100 s c x) = (term178 _88095 _88100 s x c).
Proof. exact (eq_refl (term185 _88095 _88100 s c x)). Qed.
Lemma lem3391607 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term186 _88095 _88100 s c) = (term179 _88095 _88100 s c).
Proof. exact (fun_ext (fun x : _88100 => @lem3391606 _88095 _88100 s x c)). Qed.
Lemma lem3391608 {_88100 : Type'} : (@ex _88100) = (@ex _88100).
Proof. exact (eq_refl (@ex _88100)). Qed.
Lemma lem3391609 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term187 _88095 _88100 s c) = (term180 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391608 _88100) (@lem3391607 _88095 _88100 s c)). Qed.
Lemma lem3391610 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3391611 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term188 _88095 _88100 s c) = (term181 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391610) (@lem3391609 _88095 _88100 s c)). Qed.
Lemma lem3391612 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term145 _88095 _88100 s c x) = (term122 _88095 _88100 s x c).
Proof. exact (eq_refl (term145 _88095 _88100 s c x)). Qed.
Lemma lem3391613 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term155 _88095 _88100 s c) = (term142 _88095 _88100 s c).
Proof. exact (fun_ext (fun x : _88100 => @lem3391612 _88095 _88100 s x c)). Qed.
Lemma lem3391614 {_88100 : Type'} : (@ex _88100) = (@ex _88100).
Proof. exact (eq_refl (@ex _88100)). Qed.
Lemma lem3391615 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term156 _88095 _88100 s c) = (term157 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391614 _88100) (@lem3391613 _88095 _88100 s c)). Qed.
Lemma lem3391616 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term183 _88095 _88100 s c) = (term182 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391611 _88095 _88100 s c) (@lem3391615 _88095 _88100 s c)). Qed.
Lemma lem3391617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3391618 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term189 _88095 _88100 s c) = (term190 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391617) (@lem3391616 _88095 _88100 s c)). Qed.
Lemma lem3391619 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term185 _88095 _88100 s c x) = (term178 _88095 _88100 s x c).
Proof. exact (eq_refl (term185 _88095 _88100 s c x)). Qed.
Lemma lem3391620 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3391621 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term191 _88095 _88100 s c x) = (term192 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391620) (@lem3391619 _88095 _88100 s x c)). Qed.
Lemma lem3391622 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term145 _88095 _88100 s c x) = (term122 _88095 _88100 s x c).
Proof. exact (eq_refl (term145 _88095 _88100 s c x)). Qed.
Lemma lem3391623 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term193 _88095 _88100 s c x) = (term194 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391621 _88095 _88100 s x c) (@lem3391622 _88095 _88100 s x c)). Qed.
Lemma lem3391624 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term195 _88095 _88100 s c) = (term196 _88095 _88100 s c).
Proof. exact (fun_ext (fun x : _88100 => @lem3391623 _88095 _88100 s x c)). Qed.
Lemma lem3391625 {_88100 : Type'} : (@ex _88100) = (@ex _88100).
Proof. exact (eq_refl (@ex _88100)). Qed.
Lemma lem3391626 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term184 _88095 _88100 s c) = (term197 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391625 _88100) (@lem3391624 _88095 _88100 s c)). Qed.
Lemma lem3391627 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : ((term183 _88095 _88100 s c) = (term184 _88095 _88100 s c)) = ((term182 _88095 _88100 s c) = (term197 _88095 _88100 s c)).
Proof. exact (MK_COMB (@lem3391618 _88095 _88100 s c) (@lem3391626 _88095 _88100 s c)). Qed.
Lemma lem3391628 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term182 _88095 _88100 s c) = (term197 _88095 _88100 s c).
Proof. exact (EQ_MP (@lem3391627 _88095 _88100 s c) (@lem3391605 _88095 _88100 s c)). Qed.
Lemma lem3391630 {A : Type'} (P : A -> Prop) (Q : Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3391631 {_88095 : Type'} (P : _88095 -> Prop) (Q : Prop) : (term198 _88095 P Q) = (term199 _88095 P Q).
Proof. exact (@lem3391630 _88095 P Q). Qed.
Lemma lem3391632 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term200 _88095 _88100 s x c) = (term201 _88095 _88100 s x c).
Proof. exact (@lem3391631 _88095 (term177 _88095 _88100 s x c) (term122 _88095 _88100 s x c)). Qed.
Lemma lem3391633 {_88095 _88100 : Type'} (x : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) : (term202 _88095 _88100 s x' c x) = (term175 _88095 _88100 x s x' c).
Proof. exact (eq_refl (term202 _88095 _88100 s x' c x)). Qed.
Lemma lem3391634 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term203 _88095 _88100 s x c) = (term177 _88095 _88100 s x c).
Proof. exact (fun_ext (fun x' : _88095 => @lem3391633 _88095 _88100 x' s x c)). Qed.
Lemma lem3391635 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391636 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term204 _88095 _88100 s x c) = (term178 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391635 _88095) (@lem3391634 _88095 _88100 s x c)). Qed.
Lemma lem3391637 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3391638 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term205 _88095 _88100 s x c) = (term192 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391637) (@lem3391636 _88095 _88100 s x c)). Qed.
Lemma lem3391639 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term122 _88095 _88100 s x c) = (term122 _88095 _88100 s x c).
Proof. exact (eq_refl (term122 _88095 _88100 s x c)). Qed.
Lemma lem3391640 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term200 _88095 _88100 s x c) = (term194 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391638 _88095 _88100 s x c) (@lem3391639 _88095 _88100 s x c)). Qed.
Lemma lem3391641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3391642 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term206 _88095 _88100 s x c) = (term207 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391641) (@lem3391640 _88095 _88100 s x c)). Qed.
Lemma lem3391643 {_88095 _88100 : Type'} (x : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) : (term202 _88095 _88100 s x' c x) = (term175 _88095 _88100 x s x' c).
Proof. exact (eq_refl (term202 _88095 _88100 s x' c x)). Qed.
Lemma lem3391644 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3391645 {_88095 _88100 : Type'} (x : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) : (term208 _88095 _88100 s x' c x) = (term209 _88095 _88100 x s x' c).
Proof. exact (MK_COMB (@lem3391644) (@lem3391643 _88095 _88100 x s x' c)). Qed.
Lemma lem3391646 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term122 _88095 _88100 s x c) = (term122 _88095 _88100 s x c).
Proof. exact (eq_refl (term122 _88095 _88100 s x c)). Qed.
Lemma lem3391647 {_88095 _88100 : Type'} (x : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) : (term210 _88095 _88100 x s x' c) = (term211 _88095 _88100 x s x' c).
Proof. exact (MK_COMB (@lem3391645 _88095 _88100 x s x' c) (@lem3391646 _88095 _88100 s x' c)). Qed.
Lemma lem3391648 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term212 _88095 _88100 s x c) = (term213 _88095 _88100 s x c).
Proof. exact (fun_ext (fun x' : _88095 => @lem3391647 _88095 _88100 x' s x c)). Qed.
Lemma lem3391649 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391650 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term201 _88095 _88100 s x c) = (term214 _88095 _88100 s x c).
Proof. exact (MK_COMB (@lem3391649 _88095) (@lem3391648 _88095 _88100 s x c)). Qed.
Lemma lem3391651 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : ((term200 _88095 _88100 s x c) = (term201 _88095 _88100 s x c)) = ((term194 _88095 _88100 s x c) = (term214 _88095 _88100 s x c)).
Proof. exact (MK_COMB (@lem3391642 _88095 _88100 s x c) (@lem3391650 _88095 _88100 s x c)). Qed.
Lemma lem3391652 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x : _88100) (c : _88100) : (term194 _88095 _88100 s x c) = (term214 _88095 _88100 s x c).
Proof. exact (EQ_MP (@lem3391651 _88095 _88100 s x c) (@lem3391632 _88095 _88100 s x c)). Qed.
Lemma lem3391653 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term196 _88095 _88100 s c) = (term215 _88095 _88100 s c).
Proof. exact (fun_ext (fun x : _88100 => @lem3391652 _88095 _88100 s x c)). Qed.
Lemma lem3391654 {_88100 : Type'} : (@ex _88100) = (@ex _88100).
Proof. exact (eq_refl (@ex _88100)). Qed.
Lemma lem3391655 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term197 _88095 _88100 s c) = (term216 _88095 _88100 s c).
Proof. exact (MK_COMB (@lem3391654 _88100) (@lem3391653 _88095 _88100 s c)). Qed.
Lemma lem3391656 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term182 _88095 _88100 s c) = (term216 _88095 _88100 s c).
Proof. exact (TRANS (@lem3391628 _88095 _88100 s c) (@lem3391655 _88095 _88100 s c)). Qed.
Lemma lem3391657 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term158 _88095 _88100 s c) = (term216 _88095 _88100 s c).
Proof. exact (TRANS (@lem3391601 _88095 _88100 s c) (@lem3391656 _88095 _88100 s c)). Qed.
Lemma lem3391658 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term136 _88095 _88100 s c) = (term216 _88095 _88100 s c).
Proof. exact (TRANS (@lem3391441 _88095 _88100 s c) (@lem3391657 _88095 _88100 s c)). Qed.
Lemma lem3391659 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term87 _88095 _88100 s c) = (term216 _88095 _88100 s c).
Proof. exact (TRANS (@lem3391414 _88095 _88100 s c) (@lem3391658 _88095 _88100 s c)). Qed.
Lemma lem3391660 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) (h1 : term87 _88095 _88100 s c) : term216 _88095 _88100 s c.
Proof. exact (EQ_MP (@lem3391659 _88095 _88100 s c) (@lem3391359 _88095 _88100 s c h1)). Qed.
Lemma lem3391662 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (@IN _88095 x s) = (@IN _88095 x s).
Proof. exact (eq_refl (@IN _88095 x s)). Qed.
Lemma lem3391663 {_88095 : Type'} (P : _88095 -> Prop) : (term105 _88095 P) = (term106 _88095 P).
Proof. exact (@lem18394 _88095 P). Qed.
Lemma lem3391664 {_88095 : Type'} (s : _88095 -> Prop) : (term107 _88095 s) = (term108 _88095 s).
Proof. exact (@lem3391663 _88095 (term75 _88095 s)). Qed.
Lemma lem3391665 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term76 _88095 s x) = (@IN _88095 x s).
Proof. exact (eq_refl (term76 _88095 s x)). Qed.
Lemma lem3391666 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3391668 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term109 _88095 s x) = (term110 _88095 x s).
Proof. exact (MK_COMB (@lem3391666) (@lem3391665 _88095 x s)). Qed.
Lemma lem3391669 {_88095 : Type'} (s : _88095 -> Prop) : (term111 _88095 s) = (term112 _88095 s).
Proof. exact (fun_ext (fun x : _88095 => @lem3391668 _88095 x s)). Qed.
Lemma lem3391670 {_88095 : Type'} : (@all _88095) = (@all _88095).
Proof. exact (eq_refl (@all _88095)). Qed.
Lemma lem3391671 {_88095 : Type'} (s : _88095 -> Prop) : (term108 _88095 s) = (term113 _88095 s).
Proof. exact (MK_COMB (@lem3391670 _88095) (@lem3391669 _88095 s)). Qed.
Lemma lem3391672 {_88095 : Type'} (s : _88095 -> Prop) : (term107 _88095 s) = (term113 _88095 s).
Proof. exact (TRANS (@lem3391664 _88095 s) (@lem3391671 _88095 s)). Qed.
Lemma lem3391673 {_88095 : Type'} (s : _88095 -> Prop) : (term75 _88095 s) = (term75 _88095 s).
Proof. exact (fun_ext (fun x : _88095 => @lem3391662 _88095 x s)). Qed.
Lemma lem3391674 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391675 {_88095 : Type'} (s : _88095 -> Prop) : (term82 _88095 s) = (term82 _88095 s).
Proof. exact (MK_COMB (@lem3391674 _88095) (@lem3391673 _88095 s)). Qed.
Lemma lem3391676 {_88095 : Type'} (s : _88095 -> Prop) : (term37 _88095 s) = (term37 _88095 s).
Proof. exact (eq_refl (term37 _88095 s)). Qed.
Lemma lem3391679 {_88095 : Type'} (s : _88095 -> Prop) : (term217 _88095 s) = (s = (@EMPTY _88095)).
Proof. exact (@lem16933 (s = (@EMPTY _88095))). Qed.
Lemma lem3391680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3391681 {_88095 : Type'} (s : _88095 -> Prop) : (term218 _88095 s) = (term219 _88095 s).
Proof. exact (MK_COMB (@lem3391680) (@lem3391672 _88095 s)). Qed.
Lemma lem3391682 {_88095 : Type'} (s : _88095 -> Prop) : (term220 _88095 s) = (term221 _88095 s).
Proof. exact (MK_COMB (@lem3391681 _88095 s) (@lem3391676 _88095 s)). Qed.
Lemma lem3391683 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3391684 {_88095 : Type'} (s : _88095 -> Prop) : (term222 _88095 s) = (term222 _88095 s).
Proof. exact (MK_COMB (@lem3391683) (@lem3391675 _88095 s)). Qed.
Lemma lem3391685 {_88095 : Type'} (s : _88095 -> Prop) : (term223 _88095 s) = (term224 _88095 s).
Proof. exact (MK_COMB (@lem3391684 _88095 s) (@lem3391679 _88095 s)). Qed.
Lemma lem3391686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3391687 {_88095 : Type'} (s : _88095 -> Prop) : (term225 _88095 s) = (term226 _88095 s).
Proof. exact (MK_COMB (@lem3391686) (@lem3391685 _88095 s)). Qed.
Lemma lem3391688 {_88095 : Type'} (s : _88095 -> Prop) : (term227 _88095 s) = (term228 _88095 s).
Proof. exact (MK_COMB (@lem3391687 _88095 s) (@lem3391682 _88095 s)). Qed.
Lemma lem3391689 {_88095 : Type'} (s : _88095 -> Prop) : ((term82 _88095 s) = (term37 _88095 s)) = (term227 _88095 s).
Proof. exact (@lem17784 (term82 _88095 s) (term37 _88095 s)). Qed.
Lemma lem3391690 {_88095 : Type'} (s : _88095 -> Prop) : ((term82 _88095 s) = (term37 _88095 s)) = (term228 _88095 s).
Proof. exact (TRANS (@lem3391689 _88095 s) (@lem3391688 _88095 s)). Qed.
Lemma lem3391691 {_88095 : Type'} : (term104 _88095) = (term229 _88095).
Proof. exact (fun_ext (fun s : _88095 -> Prop => @lem3391690 _88095 s)). Qed.
Lemma lem3391692 {_88095 : Type'} : (@all (_88095 -> Prop)) = (@all (_88095 -> Prop)).
Proof. exact (eq_refl (@all (_88095 -> Prop))). Qed.
Lemma lem3391693 {_88095 : Type'} : (term66 _88095) = (term230 _88095).
Proof. exact (MK_COMB (@lem3391692 _88095) (@lem3391691 _88095)). Qed.
Lemma lem3391695 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term231 A P Q) = (term232 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3391696 {_88095 : Type'} (P : type686 _88095) (Q : type686 _88095) : (term233 _88095 P Q) = (term234 _88095 P Q).
Proof. exact (@lem3391695 (_88095 -> Prop) P Q). Qed.
Lemma lem3391697 {_88095 : Type'} : (term235 _88095) = (term236 _88095).
Proof. exact (@lem3391696 _88095 (term237 _88095) (term238 _88095)). Qed.
Lemma lem3391698 {_88095 : Type'} (s : _88095 -> Prop) : (term239 _88095 s) = (term224 _88095 s).
Proof. exact (eq_refl (term239 _88095 s)). Qed.
Lemma lem3391699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3391700 {_88095 : Type'} (s : _88095 -> Prop) : (term240 _88095 s) = (term226 _88095 s).
Proof. exact (MK_COMB (@lem3391699) (@lem3391698 _88095 s)). Qed.
Lemma lem3391701 {_88095 : Type'} (s : _88095 -> Prop) : (term241 _88095 s) = (term221 _88095 s).
Proof. exact (eq_refl (term241 _88095 s)). Qed.
Lemma lem3391702 {_88095 : Type'} (s : _88095 -> Prop) : (term242 _88095 s) = (term228 _88095 s).
Proof. exact (MK_COMB (@lem3391700 _88095 s) (@lem3391701 _88095 s)). Qed.
Lemma lem3391703 {_88095 : Type'} : (term243 _88095) = (term229 _88095).
Proof. exact (fun_ext (fun s : _88095 -> Prop => @lem3391702 _88095 s)). Qed.
Lemma lem3391704 {_88095 : Type'} : (@all (_88095 -> Prop)) = (@all (_88095 -> Prop)).
Proof. exact (eq_refl (@all (_88095 -> Prop))). Qed.
Lemma lem3391705 {_88095 : Type'} : (term235 _88095) = (term230 _88095).
Proof. exact (MK_COMB (@lem3391704 _88095) (@lem3391703 _88095)). Qed.
Lemma lem3391706 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3391707 {_88095 : Type'} : (term244 _88095) = (term245 _88095).
Proof. exact (MK_COMB (@lem3391706) (@lem3391705 _88095)). Qed.
Lemma lem3391708 {_88095 : Type'} (s : _88095 -> Prop) : (term239 _88095 s) = (term224 _88095 s).
Proof. exact (eq_refl (term239 _88095 s)). Qed.
Lemma lem3391709 {_88095 : Type'} : (term246 _88095) = (term237 _88095).
Proof. exact (fun_ext (fun s : _88095 -> Prop => @lem3391708 _88095 s)). Qed.
Lemma lem3391710 {_88095 : Type'} : (@all (_88095 -> Prop)) = (@all (_88095 -> Prop)).
Proof. exact (eq_refl (@all (_88095 -> Prop))). Qed.
Lemma lem3391711 {_88095 : Type'} : (term247 _88095) = (term248 _88095).
Proof. exact (MK_COMB (@lem3391710 _88095) (@lem3391709 _88095)). Qed.
Lemma lem3391712 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3391713 {_88095 : Type'} : (term249 _88095) = (term250 _88095).
Proof. exact (MK_COMB (@lem3391712) (@lem3391711 _88095)). Qed.
Lemma lem3391714 {_88095 : Type'} (s : _88095 -> Prop) : (term241 _88095 s) = (term221 _88095 s).
Proof. exact (eq_refl (term241 _88095 s)). Qed.
Lemma lem3391715 {_88095 : Type'} : (term251 _88095) = (term238 _88095).
Proof. exact (fun_ext (fun s : _88095 -> Prop => @lem3391714 _88095 s)). Qed.
Lemma lem3391716 {_88095 : Type'} : (@all (_88095 -> Prop)) = (@all (_88095 -> Prop)).
Proof. exact (eq_refl (@all (_88095 -> Prop))). Qed.
Lemma lem3391717 {_88095 : Type'} : (term252 _88095) = (term253 _88095).
Proof. exact (MK_COMB (@lem3391716 _88095) (@lem3391715 _88095)). Qed.
Lemma lem3391718 {_88095 : Type'} : (term236 _88095) = (term254 _88095).
Proof. exact (MK_COMB (@lem3391713 _88095) (@lem3391717 _88095)). Qed.
Lemma lem3391719 {_88095 : Type'} : ((term235 _88095) = (term236 _88095)) = ((term230 _88095) = (term254 _88095)).
Proof. exact (MK_COMB (@lem3391707 _88095) (@lem3391718 _88095)). Qed.
Lemma lem3391720 {_88095 : Type'} : (term230 _88095) = (term254 _88095).
Proof. exact (EQ_MP (@lem3391719 _88095) (@lem3391697 _88095)). Qed.
Lemma lem3391826 {A : Type'} (P : A -> Prop) (Q : Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3391827 {_88095 : Type'} (P : _88095 -> Prop) (Q : Prop) : (term198 _88095 P Q) = (term199 _88095 P Q).
Proof. exact (@lem3391826 _88095 P Q). Qed.
Lemma lem3391828 {_88095 : Type'} (s : _88095 -> Prop) : (term255 _88095 s) = (term256 _88095 s).
Proof. exact (@lem3391827 _88095 (term75 _88095 s) (s = (@EMPTY _88095))). Qed.
Lemma lem3391829 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term76 _88095 s x) = (@IN _88095 x s).
Proof. exact (eq_refl (term76 _88095 s x)). Qed.
Lemma lem3391830 {_88095 : Type'} (s : _88095 -> Prop) : (term80 _88095 s) = (term75 _88095 s).
Proof. exact (fun_ext (fun x : _88095 => @lem3391829 _88095 x s)). Qed.
Lemma lem3391831 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391832 {_88095 : Type'} (s : _88095 -> Prop) : (term81 _88095 s) = (term82 _88095 s).
Proof. exact (MK_COMB (@lem3391831 _88095) (@lem3391830 _88095 s)). Qed.
Lemma lem3391833 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3391834 {_88095 : Type'} (s : _88095 -> Prop) : (term257 _88095 s) = (term222 _88095 s).
Proof. exact (MK_COMB (@lem3391833) (@lem3391832 _88095 s)). Qed.
Lemma lem3391835 {_88095 : Type'} (s : _88095 -> Prop) : (s = (@EMPTY _88095)) = (s = (@EMPTY _88095)).
Proof. exact (eq_refl (s = (@EMPTY _88095))). Qed.
Lemma lem3391836 {_88095 : Type'} (s : _88095 -> Prop) : (term255 _88095 s) = (term224 _88095 s).
Proof. exact (MK_COMB (@lem3391834 _88095 s) (@lem3391835 _88095 s)). Qed.
Lemma lem3391837 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3391838 {_88095 : Type'} (s : _88095 -> Prop) : (term258 _88095 s) = (term259 _88095 s).
Proof. exact (MK_COMB (@lem3391837) (@lem3391836 _88095 s)). Qed.
Lemma lem3391839 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term76 _88095 s x) = (@IN _88095 x s).
Proof. exact (eq_refl (term76 _88095 s x)). Qed.
Lemma lem3391840 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3391841 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term260 _88095 s x) = (term261 _88095 x s).
Proof. exact (MK_COMB (@lem3391840) (@lem3391839 _88095 x s)). Qed.
Lemma lem3391842 {_88095 : Type'} (s : _88095 -> Prop) : (s = (@EMPTY _88095)) = (s = (@EMPTY _88095)).
Proof. exact (eq_refl (s = (@EMPTY _88095))). Qed.
Lemma lem3391843 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term262 _88095 x s) = (term263 _88095 x s).
Proof. exact (MK_COMB (@lem3391841 _88095 x s) (@lem3391842 _88095 s)). Qed.
Lemma lem3391844 {_88095 : Type'} (s : _88095 -> Prop) : (term264 _88095 s) = (term265 _88095 s).
Proof. exact (fun_ext (fun x : _88095 => @lem3391843 _88095 x s)). Qed.
Lemma lem3391845 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391846 {_88095 : Type'} (s : _88095 -> Prop) : (term256 _88095 s) = (term266 _88095 s).
Proof. exact (MK_COMB (@lem3391845 _88095) (@lem3391844 _88095 s)). Qed.
Lemma lem3391847 {_88095 : Type'} (s : _88095 -> Prop) : ((term255 _88095 s) = (term256 _88095 s)) = ((term224 _88095 s) = (term266 _88095 s)).
Proof. exact (MK_COMB (@lem3391838 _88095 s) (@lem3391846 _88095 s)). Qed.
Lemma lem3391848 {_88095 : Type'} (s : _88095 -> Prop) : (term224 _88095 s) = (term266 _88095 s).
Proof. exact (EQ_MP (@lem3391847 _88095 s) (@lem3391828 _88095 s)). Qed.
Lemma lem3391849 {_88095 : Type'} : (term237 _88095) = (term267 _88095).
Proof. exact (fun_ext (fun s : _88095 -> Prop => @lem3391848 _88095 s)). Qed.
Lemma lem3391850 {_88095 : Type'} : (@all (_88095 -> Prop)) = (@all (_88095 -> Prop)).
Proof. exact (eq_refl (@all (_88095 -> Prop))). Qed.
Lemma lem3391851 {_88095 : Type'} : (term248 _88095) = (term268 _88095).
Proof. exact (MK_COMB (@lem3391850 _88095) (@lem3391849 _88095)). Qed.
Lemma lem3391853 {A B : Type'} (P : type1413 A B) : (term269 A B P) = (term270 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3391854 {_88095 : Type'} (P : type672 _88095) : (term271 _88095 P) = (term272 _88095 P).
Proof. exact (@lem3391853 (_88095 -> Prop) _88095 P). Qed.
Lemma lem3391855 {_88095 : Type'} : (term273 _88095) = (term274 _88095).
Proof. exact (@lem3391854 _88095 (term275 _88095)). Qed.
Lemma lem3391856 {_88095 : Type'} (s : _88095 -> Prop) : (term276 _88095 s) = (term265 _88095 s).
Proof. exact (eq_refl (term276 _88095 s)). Qed.
Lemma lem3391857 {_88095 : Type'} (x : _88095) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3391858 {_88095 : Type'} (s : _88095 -> Prop) (x : _88095) : (term277 _88095 s x) = (term278 _88095 s x).
Proof. exact (MK_COMB (@lem3391856 _88095 s) (@lem3391857 _88095 x)). Qed.
Lemma lem3391859 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term278 _88095 s x) = (term263 _88095 x s).
Proof. exact (eq_refl (term278 _88095 s x)). Qed.
Lemma lem3391860 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term277 _88095 s x) = (term263 _88095 x s).
Proof. exact (TRANS (@lem3391858 _88095 s x) (@lem3391859 _88095 x s)). Qed.
Lemma lem3391861 {_88095 : Type'} (s : _88095 -> Prop) : (term279 _88095 s) = (term265 _88095 s).
Proof. exact (fun_ext (fun x : _88095 => @lem3391860 _88095 x s)). Qed.
Lemma lem3391862 {_88095 : Type'} : (@ex _88095) = (@ex _88095).
Proof. exact (eq_refl (@ex _88095)). Qed.
Lemma lem3391863 {_88095 : Type'} (s : _88095 -> Prop) : (term280 _88095 s) = (term266 _88095 s).
Proof. exact (MK_COMB (@lem3391862 _88095) (@lem3391861 _88095 s)). Qed.
Lemma lem3391864 {_88095 : Type'} : (term281 _88095) = (term267 _88095).
Proof. exact (fun_ext (fun s : _88095 -> Prop => @lem3391863 _88095 s)). Qed.
Lemma lem3391865 {_88095 : Type'} : (@all (_88095 -> Prop)) = (@all (_88095 -> Prop)).
Proof. exact (eq_refl (@all (_88095 -> Prop))). Qed.
Lemma lem3391866 {_88095 : Type'} : (term273 _88095) = (term268 _88095).
Proof. exact (MK_COMB (@lem3391865 _88095) (@lem3391864 _88095)). Qed.
Lemma lem3391867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3391868 {_88095 : Type'} : (term282 _88095) = (term283 _88095).
Proof. exact (MK_COMB (@lem3391867) (@lem3391866 _88095)). Qed.
Lemma lem3391869 {_88095 : Type'} (s : _88095 -> Prop) : (term276 _88095 s) = (term265 _88095 s).
Proof. exact (eq_refl (term276 _88095 s)). Qed.
Lemma lem3391870 {_88095 : Type'} (x : type684 _88095) (s : _88095 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3391871 {_88095 : Type'} (x : type684 _88095) (s : _88095 -> Prop) : (term284 _88095 x s) = (term285 _88095 x s).
Proof. exact (MK_COMB (@lem3391869 _88095 s) (@lem3391870 _88095 x s)). Qed.
Lemma lem3391872 {_88095 : Type'} (x : type684 _88095) (s : _88095 -> Prop) : (term285 _88095 x s) = (term286 _88095 x s).
Proof. exact (eq_refl (term285 _88095 x s)). Qed.
Lemma lem3391873 {_88095 : Type'} (x : type684 _88095) (s : _88095 -> Prop) : (term284 _88095 x s) = (term286 _88095 x s).
Proof. exact (TRANS (@lem3391871 _88095 x s) (@lem3391872 _88095 x s)). Qed.
Lemma lem3391874 {_88095 : Type'} (x : type684 _88095) : (term287 _88095 x) = (term288 _88095 x).
Proof. exact (fun_ext (fun s : _88095 -> Prop => @lem3391873 _88095 x s)). Qed.
Lemma lem3391875 {_88095 : Type'} : (@all (_88095 -> Prop)) = (@all (_88095 -> Prop)).
Proof. exact (eq_refl (@all (_88095 -> Prop))). Qed.
Lemma lem3391876 {_88095 : Type'} (x : type684 _88095) : (term289 _88095 x) = (term290 _88095 x).
Proof. exact (MK_COMB (@lem3391875 _88095) (@lem3391874 _88095 x)). Qed.
Lemma lem3391877 {_88095 : Type'} : (term291 _88095) = (term292 _88095).
Proof. exact (fun_ext (fun x : type684 _88095 => @lem3391876 _88095 x)). Qed.
Lemma lem3391878 {_88095 : Type'} : (@ex ((_88095 -> Prop) -> _88095)) = (@ex ((_88095 -> Prop) -> _88095)).
Proof. exact (eq_refl (@ex ((_88095 -> Prop) -> _88095))). Qed.
Lemma lem3391879 {_88095 : Type'} : (term274 _88095) = (term293 _88095).
Proof. exact (MK_COMB (@lem3391878 _88095) (@lem3391877 _88095)). Qed.
Lemma lem3391880 {_88095 : Type'} : ((term273 _88095) = (term274 _88095)) = ((term268 _88095) = (term293 _88095)).
Proof. exact (MK_COMB (@lem3391868 _88095) (@lem3391879 _88095)). Qed.
Lemma lem3391881 {_88095 : Type'} : (term268 _88095) = (term293 _88095).
Proof. exact (EQ_MP (@lem3391880 _88095) (@lem3391855 _88095)). Qed.
Lemma lem3391882 {_88095 : Type'} : (term248 _88095) = (term293 _88095).
Proof. exact (TRANS (@lem3391851 _88095) (@lem3391881 _88095)). Qed.
Lemma lem3391883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3391884 {_88095 : Type'} : (term250 _88095) = (term294 _88095).
Proof. exact (MK_COMB (@lem3391883) (@lem3391882 _88095)). Qed.
Lemma lem3391885 {_88095 : Type'} : (term253 _88095) = (term253 _88095).
Proof. exact (eq_refl (term253 _88095)). Qed.
Lemma lem3391886 {_88095 : Type'} : (term254 _88095) = (term295 _88095).
Proof. exact (MK_COMB (@lem3391884 _88095) (@lem3391885 _88095)). Qed.
Lemma lem3391888 {A : Type'} (P : A -> Prop) (Q : Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3391889 {_88095 : Type'} (P : type162 _88095) (Q : Prop) : (term296 _88095 P Q) = (term297 _88095 P Q).
Proof. exact (@lem3391888 (type684 _88095) P Q). Qed.
Lemma lem3391890 {_88095 : Type'} : (term298 _88095) = (term299 _88095).
Proof. exact (@lem3391889 _88095 (term292 _88095) (term253 _88095)). Qed.
Lemma lem3391891 {_88095 : Type'} (x : type684 _88095) : (term300 _88095 x) = (term290 _88095 x).
Proof. exact (eq_refl (term300 _88095 x)). Qed.
Lemma lem3391892 {_88095 : Type'} : (term301 _88095) = (term292 _88095).
Proof. exact (fun_ext (fun x : type684 _88095 => @lem3391891 _88095 x)). Qed.
Lemma lem3391893 {_88095 : Type'} : (@ex ((_88095 -> Prop) -> _88095)) = (@ex ((_88095 -> Prop) -> _88095)).
Proof. exact (eq_refl (@ex ((_88095 -> Prop) -> _88095))). Qed.
Lemma lem3391894 {_88095 : Type'} : (term302 _88095) = (term293 _88095).
Proof. exact (MK_COMB (@lem3391893 _88095) (@lem3391892 _88095)). Qed.
Lemma lem3391895 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3391896 {_88095 : Type'} : (term303 _88095) = (term294 _88095).
Proof. exact (MK_COMB (@lem3391895) (@lem3391894 _88095)). Qed.
Lemma lem3391897 {_88095 : Type'} : (term253 _88095) = (term253 _88095).
Proof. exact (eq_refl (term253 _88095)). Qed.
Lemma lem3391898 {_88095 : Type'} : (term298 _88095) = (term295 _88095).
Proof. exact (MK_COMB (@lem3391896 _88095) (@lem3391897 _88095)). Qed.
Lemma lem3391899 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3391900 {_88095 : Type'} : (term304 _88095) = (term305 _88095).
Proof. exact (MK_COMB (@lem3391899) (@lem3391898 _88095)). Qed.
Lemma lem3391901 {_88095 : Type'} (x : type684 _88095) : (term300 _88095 x) = (term290 _88095 x).
Proof. exact (eq_refl (term300 _88095 x)). Qed.
Lemma lem3391902 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3391903 {_88095 : Type'} (x : type684 _88095) : (term306 _88095 x) = (term307 _88095 x).
Proof. exact (MK_COMB (@lem3391902) (@lem3391901 _88095 x)). Qed.
Lemma lem3391904 {_88095 : Type'} : (term253 _88095) = (term253 _88095).
Proof. exact (eq_refl (term253 _88095)). Qed.
Lemma lem3391905 {_88095 : Type'} (x : type684 _88095) : (term308 _88095 x) = (term309 _88095 x).
Proof. exact (MK_COMB (@lem3391903 _88095 x) (@lem3391904 _88095)). Qed.
Lemma lem3391906 {_88095 : Type'} : (term310 _88095) = (term311 _88095).
Proof. exact (fun_ext (fun x : type684 _88095 => @lem3391905 _88095 x)). Qed.
Lemma lem3391907 {_88095 : Type'} : (@ex ((_88095 -> Prop) -> _88095)) = (@ex ((_88095 -> Prop) -> _88095)).
Proof. exact (eq_refl (@ex ((_88095 -> Prop) -> _88095))). Qed.
Lemma lem3391908 {_88095 : Type'} : (term299 _88095) = (term312 _88095).
Proof. exact (MK_COMB (@lem3391907 _88095) (@lem3391906 _88095)). Qed.
Lemma lem3391909 {_88095 : Type'} : ((term298 _88095) = (term299 _88095)) = ((term295 _88095) = (term312 _88095)).
Proof. exact (MK_COMB (@lem3391900 _88095) (@lem3391908 _88095)). Qed.
Lemma lem3391910 {_88095 : Type'} : (term295 _88095) = (term312 _88095).
Proof. exact (EQ_MP (@lem3391909 _88095) (@lem3391890 _88095)). Qed.
Lemma lem3391911 {_88095 : Type'} : (term254 _88095) = (term312 _88095).
Proof. exact (TRANS (@lem3391886 _88095) (@lem3391910 _88095)). Qed.
Lemma lem3391912 {_88095 : Type'} : (term230 _88095) = (term312 _88095).
Proof. exact (TRANS (@lem3391720 _88095) (@lem3391911 _88095)). Qed.
Lemma lem3391913 {_88095 : Type'} : (term66 _88095) = (term312 _88095).
Proof. exact (TRANS (@lem3391693 _88095) (@lem3391912 _88095)). Qed.
Lemma lem3391914 {_88095 : Type'} (h1 : term66 _88095) : term312 _88095.
Proof. exact (EQ_MP (@lem3391913 _88095) (@lem3391360 _88095 h1)). Qed.
Lemma lem3391915 {_88095 : Type'} (x : type684 _88095) (h1 : term309 _88095 x) : term309 _88095 x.
Proof. exact (h1). Qed.
Lemma lem3391916 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term214 _88095 _88100 s x' c) : term214 _88095 _88100 s x' c.
Proof. exact (h1). Qed.
Lemma lem3391917 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term211 _88095 _88100 x'' s x' c) : term211 _88095 _88100 x'' s x' c.
Proof. exact (h1). Qed.
Lemma lem3391925 {_88095 : Type'} (s : _88095 -> Prop) (h1 : term37 _88095 s) : term37 _88095 s.
Proof. exact (h1). Qed.
Lemma lem3391932 {_88095 : Type'} (s : _88095 -> Prop) : (term37 _88095 s) = (term37 _88095 s).
Proof. exact (eq_refl (term37 _88095 s)). Qed.
Lemma lem3391939 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term110 _88095 x s) = (term110 _88095 x s).
Proof. exact (eq_refl (term110 _88095 x s)). Qed.
Lemma lem3391940 {_88095 : Type'} (s : _88095 -> Prop) : (term112 _88095 s) = (term112 _88095 s).
Proof. exact (fun_ext (fun x : _88095 => @lem3391939 _88095 x s)). Qed.
Lemma lem3391941 {_88095 : Type'} : (@all _88095) = (@all _88095).
Proof. exact (eq_refl (@all _88095)). Qed.
Lemma lem3391942 {_88095 : Type'} (s : _88095 -> Prop) : (term113 _88095 s) = (term113 _88095 s).
Proof. exact (MK_COMB (@lem3391941 _88095) (@lem3391940 _88095 s)). Qed.
Lemma lem3391943 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3391944 {_88095 : Type'} (s : _88095 -> Prop) : (term219 _88095 s) = (term219 _88095 s).
Proof. exact (MK_COMB (@lem3391943) (@lem3391942 _88095 s)). Qed.
Lemma lem3391945 {_88095 : Type'} (s : _88095 -> Prop) : (term221 _88095 s) = (term221 _88095 s).
Proof. exact (MK_COMB (@lem3391944 _88095 s) (@lem3391932 _88095 s)). Qed.
Lemma lem3391946 {_88095 : Type'} : (term238 _88095) = (term238 _88095).
Proof. exact (fun_ext (fun s : _88095 -> Prop => @lem3391945 _88095 s)). Qed.
Lemma lem3391947 {_88095 : Type'} : (@all (_88095 -> Prop)) = (@all (_88095 -> Prop)).
Proof. exact (eq_refl (@all (_88095 -> Prop))). Qed.
Lemma lem3391948 {_88095 : Type'} : (term253 _88095) = (term253 _88095).
Proof. exact (MK_COMB (@lem3391947 _88095) (@lem3391946 _88095)). Qed.
Lemma lem3391963 {_88095 : Type'} (x : type684 _88095) (s : _88095 -> Prop) : (term286 _88095 x s) = (term286 _88095 x s).
Proof. exact (eq_refl (term286 _88095 x s)). Qed.
Lemma lem3391964 {_88095 : Type'} (x : type684 _88095) : (term288 _88095 x) = (term288 _88095 x).
Proof. exact (fun_ext (fun s : _88095 -> Prop => @lem3391963 _88095 x s)). Qed.
Lemma lem3391965 {_88095 : Type'} : (@all (_88095 -> Prop)) = (@all (_88095 -> Prop)).
Proof. exact (eq_refl (@all (_88095 -> Prop))). Qed.
Lemma lem3391966 {_88095 : Type'} (x : type684 _88095) : (term290 _88095 x) = (term290 _88095 x).
Proof. exact (MK_COMB (@lem3391965 _88095) (@lem3391964 _88095 x)). Qed.
Lemma lem3391967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3391968 {_88095 : Type'} (x : type684 _88095) : (term307 _88095 x) = (term307 _88095 x).
Proof. exact (MK_COMB (@lem3391967) (@lem3391966 _88095 x)). Qed.
Lemma lem3391969 {_88095 : Type'} (x : type684 _88095) : (term309 _88095 x) = (term309 _88095 x).
Proof. exact (MK_COMB (@lem3391968 _88095 x) (@lem3391948 _88095)). Qed.
Lemma lem3391970 {_88095 : Type'} (x : type684 _88095) (h1 : term309 _88095 x) : term309 _88095 x.
Proof. exact (EQ_MP (@lem3391969 _88095 x) (@lem3391915 _88095 x h1)). Qed.
Lemma lem3391975 {_88100 : Type'} (x' : _88100) (c : _88100) : (x' = c) = (x' = c).
Proof. exact (eq_refl (x' = c)). Qed.
Lemma lem3391982 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term110 _88095 x s) = (term110 _88095 x s).
Proof. exact (eq_refl (term110 _88095 x s)). Qed.
Lemma lem3391983 {_88095 : Type'} (s : _88095 -> Prop) : (term112 _88095 s) = (term112 _88095 s).
Proof. exact (fun_ext (fun x : _88095 => @lem3391982 _88095 x s)). Qed.
Lemma lem3391984 {_88095 : Type'} : (@all _88095) = (@all _88095).
Proof. exact (eq_refl (@all _88095)). Qed.
Lemma lem3391985 {_88095 : Type'} (s : _88095 -> Prop) : (term113 _88095 s) = (term113 _88095 s).
Proof. exact (MK_COMB (@lem3391984 _88095) (@lem3391983 _88095 s)). Qed.
Lemma lem3391994 {_88100 : Type'} (x' : _88100) (c : _88100) : (term114 _88100 x' c) = (term114 _88100 x' c).
Proof. exact (eq_refl (term114 _88100 x' c)). Qed.
Lemma lem3391995 {_88095 _88100 : Type'} (x' : _88100) (c : _88100) (s : _88095 -> Prop) : (term116 _88095 _88100 x' c s) = (term116 _88095 _88100 x' c s).
Proof. exact (MK_COMB (@lem3391994 _88100 x' c) (@lem3391985 _88095 s)). Qed.
Lemma lem3391996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3391997 {_88095 _88100 : Type'} (x' : _88100) (c : _88100) (s : _88095 -> Prop) : (term120 _88095 _88100 x' c s) = (term120 _88095 _88100 x' c s).
Proof. exact (MK_COMB (@lem3391996) (@lem3391995 _88095 _88100 x' c s)). Qed.
Lemma lem3391998 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) : (term122 _88095 _88100 s x' c) = (term122 _88095 _88100 s x' c).
Proof. exact (MK_COMB (@lem3391997 _88095 _88100 x' c s) (@lem3391975 _88100 x' c)). Qed.
Lemma lem3392023 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) : (term209 _88095 _88100 x'' s x' c) = (term209 _88095 _88100 x'' s x' c).
Proof. exact (eq_refl (term209 _88095 _88100 x'' s x' c)). Qed.
Lemma lem3392024 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) : (term211 _88095 _88100 x'' s x' c) = (term211 _88095 _88100 x'' s x' c).
Proof. exact (MK_COMB (@lem3392023 _88095 _88100 x'' s x' c) (@lem3391998 _88095 _88100 s x' c)). Qed.
Lemma lem3392025 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term211 _88095 _88100 x'' s x' c) : term211 _88095 _88100 x'' s x' c.
Proof. exact (EQ_MP (@lem3392024 _88095 _88100 x'' s x' c) (@lem3391917 _88095 _88100 x'' s x' c h1)). Qed.
Lemma lem3392027 {_88095 : Type'} (x : type684 _88095) (h1 : term309 _88095 x) : term290 _88095 x.
Proof. exact (proj1 (@lem3391970 _88095 x h1)). Qed.
Lemma lem3392028 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term175 _88095 _88100 x'' s x' c) : term175 _88095 _88100 x'' s x' c.
Proof. exact (h1). Qed.
Lemma lem3392029 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term122 _88095 _88100 s x' c) : term122 _88095 _88100 s x' c.
Proof. exact (h1). Qed.
Lemma lem3392031 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term175 _88095 _88100 x'' s x' c) : term54 _88095 _88100 x' c x'' s.
Proof. exact (proj1 (@lem3392028 _88095 _88100 x'' s x' c h1)). Qed.
Lemma lem3392035 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term122 _88095 _88100 s x' c) : term116 _88095 _88100 x' c s.
Proof. exact (proj1 (@lem3392029 _88095 _88100 s x' c h1)). Qed.
Lemma lem3392037 {_88095 : Type'} (s : _88095 -> Prop) (h1 : term113 _88095 s) : term113 _88095 s.
Proof. exact (h1). Qed.
Lemma lem3392175 {_88100 : Type'} (x' : _88100) (c : _88100) (h1 : term118 _88100 x' c) : term118 _88100 x' c.
Proof. exact (h1). Qed.
Lemma lem3392179 {_88095 : Type'} (s : _88095 -> Prop) (h1 : term37 _88095 s) : term37 _88095 s.
Proof. exact (h1). Qed.
Lemma lem3392187 {_88095 : Type'} (x : type684 _88095) (s : _88095 -> Prop) : (term286 _88095 x s) = (term286 _88095 x s).
Proof. exact (eq_refl (term286 _88095 x s)). Qed.
Lemma lem3392188 {_88095 : Type'} (x : type684 _88095) : (term288 _88095 x) = (term288 _88095 x).
Proof. exact (fun_ext (fun s : _88095 -> Prop => @lem3392187 _88095 x s)). Qed.
Lemma lem3392189 {_88095 : Type'} : (@all (_88095 -> Prop)) = (@all (_88095 -> Prop)).
Proof. exact (eq_refl (@all (_88095 -> Prop))). Qed.
Lemma lem3392191 {_88095 : Type'} (x : type684 _88095) : (term290 _88095 x) = (term290 _88095 x).
Proof. exact (MK_COMB (@lem3392189 _88095) (@lem3392188 _88095 x)). Qed.
Lemma lem3392192 {_88095 : Type'} (x : type684 _88095) (h1 : term309 _88095 x) : term290 _88095 x.
Proof. exact (EQ_MP (@lem3392191 _88095 x) (@lem3392027 _88095 x h1)). Qed.
Lemma lem3392240 {_88095 : Type'} (x : _88095) (s : _88095 -> Prop) : (term110 _88095 x s) = (term110 _88095 x s).
Proof. exact (eq_refl (term110 _88095 x s)). Qed.
Lemma lem3392241 {_88095 : Type'} (s : _88095 -> Prop) : (term112 _88095 s) = (term112 _88095 s).
Proof. exact (fun_ext (fun x : _88095 => @lem3392240 _88095 x s)). Qed.
Lemma lem3392242 {_88095 : Type'} : (@all _88095) = (@all _88095).
Proof. exact (eq_refl (@all _88095)). Qed.
Lemma lem3392244 {_88095 : Type'} (s : _88095 -> Prop) : (term113 _88095 s) = (term113 _88095 s).
Proof. exact (MK_COMB (@lem3392242 _88095) (@lem3392241 _88095 s)). Qed.
Lemma lem3392245 {_88095 : Type'} (s : _88095 -> Prop) (h1 : term113 _88095 s) : term113 _88095 s.
Proof. exact (EQ_MP (@lem3392244 _88095 s) (@lem3392037 _88095 s h1)). Qed.
Lemma lem3392264 {_88095 : Type'} (_35650 : _88095 -> Prop) (x : type684 _88095) (h1 : term309 _88095 x) : term313 _88095 x _35650.
Proof. exact (@lem3392192 _88095 x h1 _35650). Qed.
Lemma lem3392265 {_88095 : Type'} (x : type684 _88095) (_35650 : _88095 -> Prop) : (term313 _88095 x _35650) = (term286 _88095 x _35650).
Proof. exact (eq_refl (term313 _88095 x _35650)). Qed.
Lemma lem3392273 {_88095 : Type'} (_35653 : _88095) (s : _88095 -> Prop) (h1 : term113 _88095 s) : term314 _88095 s _35653.
Proof. exact (@lem3392245 _88095 s h1 _35653). Qed.
Lemma lem3392274 {_88095 : Type'} (_35653 : _88095) (s : _88095 -> Prop) : (term314 _88095 s _35653) = (term110 _88095 _35653 s).
Proof. exact (eq_refl (term314 _88095 s _35653)). Qed.
Lemma lem3392291 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term175 _88095 _88100 x'' s x' c) : term118 _88100 x' c.
Proof. exact (proj2 (@lem3392028 _88095 _88100 x'' s x' c h1)). Qed.
Lemma lem3392293 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term175 _88095 _88100 x'' s x' c) : x' = c.
Proof. exact (proj1 (@lem3392031 _88095 _88100 x'' s x' c h1)). Qed.
Lemma lem3392311 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term122 _88095 _88100 s x' c) : x' = c.
Proof. exact (proj2 (@lem3392029 _88095 _88100 s x' c h1)). Qed.
Lemma lem3392313 {_88100 : Type'} (x' : _88100) (c : _88100) (h1 : term118 _88100 x' c) : term118 _88100 x' c.
Proof. exact (h1). Qed.
Lemma lem3392315 {_88095 : Type'} (s : _88095 -> Prop) (h1 : term37 _88095 s) : term37 _88095 s.
Proof. exact (h1). Qed.
Lemma lem3392388 {_88100 : Type'} (c : _88100) : (term315 _88100 c) = (term315 _88100 c).
Proof. exact (eq_refl (term315 _88100 c)). Qed.
Lemma lem3392389 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term175 _88095 _88100 x'' s x' c) : (term316 _88100 c x') = (term317 _88100 c).
Proof. exact (MK_COMB (@lem3392388 _88100 c) (@lem3392293 _88095 _88100 x'' s x' c h1)). Qed.
Lemma lem3392390 {_88100 : Type'} (c : _88100) : (term317 _88100 c) = (term318 _88100 c).
Proof. exact (eq_refl (term317 _88100 c)). Qed.
Lemma lem3392391 {_88100 : Type'} (c : _88100) (x' : _88100) : (term319 _88100 c x') = (term319 _88100 c x').
Proof. exact (eq_refl (term319 _88100 c x')). Qed.
Lemma lem3392392 {_88100 : Type'} (x' : _88100) (c : _88100) : ((term316 _88100 c x') = (term317 _88100 c)) = ((term316 _88100 c x') = (term318 _88100 c)).
Proof. exact (MK_COMB (@lem3392391 _88100 c x') (@lem3392390 _88100 c)). Qed.
Lemma lem3392393 {_88100 : Type'} (x' : _88100) (c : _88100) : (term316 _88100 c x') = (term118 _88100 x' c).
Proof. exact (eq_refl (term316 _88100 c x')). Qed.
Lemma lem3392394 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3392395 {_88100 : Type'} (x' : _88100) (c : _88100) : (term319 _88100 c x') = (term320 _88100 x' c).
Proof. exact (MK_COMB (@lem3392394) (@lem3392393 _88100 x' c)). Qed.
Lemma lem3392396 {_88100 : Type'} (c : _88100) : (term318 _88100 c) = (term318 _88100 c).
Proof. exact (eq_refl (term318 _88100 c)). Qed.
Lemma lem3392397 {_88100 : Type'} (x' : _88100) (c : _88100) : ((term316 _88100 c x') = (term318 _88100 c)) = ((term118 _88100 x' c) = (term318 _88100 c)).
Proof. exact (MK_COMB (@lem3392395 _88100 x' c) (@lem3392396 _88100 c)). Qed.
Lemma lem3392398 {_88100 : Type'} (x' : _88100) (c : _88100) : ((term316 _88100 c x') = (term317 _88100 c)) = ((term118 _88100 x' c) = (term318 _88100 c)).
Proof. exact (TRANS (@lem3392392 _88100 x' c) (@lem3392397 _88100 x' c)). Qed.
Lemma lem3392399 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term175 _88095 _88100 x'' s x' c) : (term118 _88100 x' c) = (term318 _88100 c).
Proof. exact (EQ_MP (@lem3392398 _88100 x' c) (@lem3392389 _88095 _88100 x'' s x' c h1)). Qed.
Lemma lem3392400 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term175 _88095 _88100 x'' s x' c) : term318 _88100 c.
Proof. exact (EQ_MP (@lem3392399 _88095 _88100 x'' s x' c h1) (@lem3392291 _88095 _88100 x'' s x' c h1)). Qed.
Lemma lem3392471 {_88100 : Type'} (c : _88100) : (term315 _88100 c) = (term315 _88100 c).
Proof. exact (eq_refl (term315 _88100 c)). Qed.
Lemma lem3392472 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term122 _88095 _88100 s x' c) : (term316 _88100 c x') = (term317 _88100 c).
Proof. exact (MK_COMB (@lem3392471 _88100 c) (@lem3392311 _88095 _88100 s x' c h1)). Qed.
Lemma lem3392473 {_88100 : Type'} (c : _88100) : (term317 _88100 c) = (term318 _88100 c).
Proof. exact (eq_refl (term317 _88100 c)). Qed.
Lemma lem3392474 {_88100 : Type'} (c : _88100) (x' : _88100) : (term319 _88100 c x') = (term319 _88100 c x').
Proof. exact (eq_refl (term319 _88100 c x')). Qed.
Lemma lem3392475 {_88100 : Type'} (x' : _88100) (c : _88100) : ((term316 _88100 c x') = (term317 _88100 c)) = ((term316 _88100 c x') = (term318 _88100 c)).
Proof. exact (MK_COMB (@lem3392474 _88100 c x') (@lem3392473 _88100 c)). Qed.
Lemma lem3392476 {_88100 : Type'} (x' : _88100) (c : _88100) : (term316 _88100 c x') = (term118 _88100 x' c).
Proof. exact (eq_refl (term316 _88100 c x')). Qed.
Lemma lem3392477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3392478 {_88100 : Type'} (x' : _88100) (c : _88100) : (term319 _88100 c x') = (term320 _88100 x' c).
Proof. exact (MK_COMB (@lem3392477) (@lem3392476 _88100 x' c)). Qed.
Lemma lem3392479 {_88100 : Type'} (c : _88100) : (term318 _88100 c) = (term318 _88100 c).
Proof. exact (eq_refl (term318 _88100 c)). Qed.
Lemma lem3392480 {_88100 : Type'} (x' : _88100) (c : _88100) : ((term316 _88100 c x') = (term318 _88100 c)) = ((term118 _88100 x' c) = (term318 _88100 c)).
Proof. exact (MK_COMB (@lem3392478 _88100 x' c) (@lem3392479 _88100 c)). Qed.
Lemma lem3392481 {_88100 : Type'} (x' : _88100) (c : _88100) : ((term316 _88100 c x') = (term317 _88100 c)) = ((term118 _88100 x' c) = (term318 _88100 c)).
Proof. exact (TRANS (@lem3392475 _88100 x' c) (@lem3392480 _88100 x' c)). Qed.
Lemma lem3392482 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term122 _88095 _88100 s x' c) : (term118 _88100 x' c) = (term318 _88100 c).
Proof. exact (EQ_MP (@lem3392481 _88100 x' c) (@lem3392472 _88095 _88100 s x' c h1)). Qed.
Lemma lem3392483 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term118 _88100 x' c) (h2 : term122 _88095 _88100 s x' c) : term318 _88100 c.
Proof. exact (EQ_MP (@lem3392482 _88095 _88100 s x' c h2) (@lem3392313 _88100 x' c h1)). Qed.
Lemma lem3392511 {_88095 : Type'} (s : _88095 -> Prop) (h1 : term37 _88095 s) : term37 _88095 s.
Proof. exact (h1). Qed.
Lemma lem3392525 {_88095 : Type'} (_35650 : _88095 -> Prop) (x : type684 _88095) (h1 : term309 _88095 x) : term286 _88095 x _35650.
Proof. exact (EQ_MP (@lem3392265 _88095 x _35650) (@lem3392264 _88095 _35650 x h1)). Qed.
Lemma lem3392553 {_88095 : Type'} (_35653 : _88095) (s : _88095 -> Prop) (h1 : term113 _88095 s) : term110 _88095 _35653 s.
Proof. exact (EQ_MP (@lem3392274 _88095 _35653 s) (@lem3392273 _88095 _35653 s h1)). Qed.
Lemma lem3392588 {_88100 : Type'} (x : _88100) : x = x.
Proof. exact (@lem21386 _88100 x). Qed.
Lemma lem3392589 {_88100 : Type'} (x : _88100) : x = x.
Proof. exact (@lem3392588 _88100 x). Qed.
Lemma lem3392590 {_88100 : Type'} (c : _88100) : c = c.
Proof. exact (@lem3392589 _88100 c). Qed.
Lemma lem3392591 {_88100 : Type'} (c : _88100) : term321 _88100 c.
Proof. exact (fun h0 : term318 _88100 c => @lem3392590 _88100 c). Qed.
Lemma lem3392593 (p : Prop) : (term322 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3392594 {_88100 : Type'} (c : _88100) : (term321 _88100 c) = (c = c).
Proof. exact (@lem3392593 (c = c)). Qed.
Lemma lem3392595 {_88100 : Type'} (c : _88100) : c = c.
Proof. exact (EQ_MP (@lem3392594 _88100 c) (@lem3392591 _88100 c)). Qed.
Lemma lem3392598 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3392600 {_88100 : Type'} (c : _88100) : (term318 _88100 c) = (term323 _88100 c).
Proof. exact (@lem3392598 (c = c)). Qed.
Lemma lem3392603 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term175 _88095 _88100 x'' s x' c) : term323 _88100 c.
Proof. exact (EQ_MP (@lem3392600 _88100 c) (@lem3392400 _88095 _88100 x'' s x' c h1)). Qed.
Lemma lem3392606 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term175 _88095 _88100 x'' s x' c) : False.
Proof. exact (@lem3392603 _88095 _88100 x'' s x' c h1 (@lem3392595 _88100 c)). Qed.
Lemma lem3392607 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term175 _88095 _88100 x'' s x' c) : term324.
Proof. exact (fun h0 : ~ False => @lem3392606 _88095 _88100 x'' s x' c h1). Qed.
Lemma lem3392609 (p : Prop) : (term322 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3392610 : term324 = False.
Proof. exact (@lem3392609 False). Qed.
Lemma lem3392646 {_88100 : Type'} (x : _88100) : x = x.
Proof. exact (@lem21386 _88100 x). Qed.
Lemma lem3392647 {_88100 : Type'} (x : _88100) : x = x.
Proof. exact (@lem3392646 _88100 x). Qed.
Lemma lem3392648 {_88100 : Type'} (c : _88100) : c = c.
Proof. exact (@lem3392647 _88100 c). Qed.
Lemma lem3392649 {_88100 : Type'} (c : _88100) : term321 _88100 c.
Proof. exact (fun h0 : term318 _88100 c => @lem3392648 _88100 c). Qed.
Lemma lem3392651 (p : Prop) : (term322 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3392652 {_88100 : Type'} (c : _88100) : (term321 _88100 c) = (c = c).
Proof. exact (@lem3392651 (c = c)). Qed.
Lemma lem3392653 {_88100 : Type'} (c : _88100) : c = c.
Proof. exact (EQ_MP (@lem3392652 _88100 c) (@lem3392649 _88100 c)). Qed.
Lemma lem3392656 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3392658 {_88100 : Type'} (c : _88100) : (term318 _88100 c) = (term323 _88100 c).
Proof. exact (@lem3392656 (c = c)). Qed.
Lemma lem3392661 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term118 _88100 x' c) (h2 : term122 _88095 _88100 s x' c) : term323 _88100 c.
Proof. exact (EQ_MP (@lem3392658 _88100 c) (@lem3392483 _88095 _88100 s x' c h1 h2)). Qed.
Lemma lem3392664 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term118 _88100 x' c) (h2 : term122 _88095 _88100 s x' c) : False.
Proof. exact (@lem3392661 _88095 _88100 s x' c h1 h2 (@lem3392653 _88100 c)). Qed.
Lemma lem3392665 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term118 _88100 x' c) (h2 : term122 _88095 _88100 s x' c) : term324.
Proof. exact (fun h0 : ~ False => @lem3392664 _88095 _88100 s x' c h1 h2). Qed.
Lemma lem3392667 (p : Prop) : (term322 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3392668 : term324 = False.
Proof. exact (@lem3392667 False). Qed.
Lemma lem3392702 {_88095 : Type'} (s : _88095 -> Prop) (h1 : term37 _88095 s) : term37 _88095 s.
Proof. exact (h1). Qed.
Lemma lem3392703 {_88095 : Type'} (s : _88095 -> Prop) (h1 : term37 _88095 s) : term325 _88095 s.
Proof. exact (fun h0 : s = (@EMPTY _88095) => @lem3392702 _88095 s h1). Qed.
Lemma lem3392705 (p : Prop) : (term326 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3392706 {_88095 : Type'} (s : _88095 -> Prop) : (term325 _88095 s) = (term37 _88095 s).
Proof. exact (@lem3392705 (s = (@EMPTY _88095))). Qed.
Lemma lem3392707 {_88095 : Type'} (s : _88095 -> Prop) (h1 : term37 _88095 s) : term37 _88095 s.
Proof. exact (EQ_MP (@lem3392706 _88095 s) (@lem3392703 _88095 s h1)). Qed.
Lemma lem3392709 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3392712 {_88095 : Type'} (x : type684 _88095) (_35650 : _88095 -> Prop) : (term286 _88095 x _35650) = (term328 _88095 x _35650).
Proof. exact (@lem3392709 (_35650 = (@EMPTY _88095)) (term329 _88095 x _35650)). Qed.
Lemma lem3392715 {_88095 : Type'} (_35650 : _88095 -> Prop) (x : type684 _88095) (h1 : term309 _88095 x) : term328 _88095 x _35650.
Proof. exact (EQ_MP (@lem3392712 _88095 x _35650) (@lem3392525 _88095 _35650 x h1)). Qed.
Lemma lem3392716 {_88095 : Type'} (_35650 : _88095 -> Prop) (x : type684 _88095) (h1 : term309 _88095 x) : term328 _88095 x _35650.
Proof. exact (@lem3392715 _88095 _35650 x h1). Qed.
Lemma lem3392717 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term309 _88095 x) : term328 _88095 x s.
Proof. exact (@lem3392716 _88095 s x h1). Qed.
Lemma lem3392720 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term37 _88095 s) (h2 : term309 _88095 x) : term329 _88095 x s.
Proof. exact (@lem3392717 _88095 s x h2 (@lem3392707 _88095 s h1)). Qed.
Lemma lem3392721 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term37 _88095 s) (h2 : term309 _88095 x) : term330 _88095 x s.
Proof. exact (fun h0 : term331 _88095 x s => @lem3392720 _88095 s x h1 h2). Qed.
Lemma lem3392723 (p : Prop) : (term322 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3392724 {_88095 : Type'} (x : type684 _88095) (s : _88095 -> Prop) : (term330 _88095 x s) = (term329 _88095 x s).
Proof. exact (@lem3392723 (term329 _88095 x s)). Qed.
Lemma lem3392725 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term37 _88095 s) (h2 : term309 _88095 x) : term329 _88095 x s.
Proof. exact (EQ_MP (@lem3392724 _88095 x s) (@lem3392721 _88095 s x h1 h2)). Qed.
Lemma lem3392728 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3392730 {_88095 : Type'} (_35653 : _88095) (s : _88095 -> Prop) : (term110 _88095 _35653 s) = (term332 _88095 _35653 s).
Proof. exact (@lem3392728 (@IN _88095 _35653 s)). Qed.
Lemma lem3392733 {_88095 : Type'} (_35653 : _88095) (s : _88095 -> Prop) (h1 : term113 _88095 s) : term332 _88095 _35653 s.
Proof. exact (EQ_MP (@lem3392730 _88095 _35653 s) (@lem3392553 _88095 _35653 s h1)). Qed.
Lemma lem3392734 {_88095 : Type'} (_35653 : _88095) (s : _88095 -> Prop) (h1 : term113 _88095 s) : term332 _88095 _35653 s.
Proof. exact (@lem3392733 _88095 _35653 s h1). Qed.
Lemma lem3392735 {_88095 : Type'} (x : type684 _88095) (s : _88095 -> Prop) (h1 : term113 _88095 s) : term333 _88095 x s.
Proof. exact (@lem3392734 _88095 (x s) s h1). Qed.
Lemma lem3392738 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term113 _88095 s) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : False.
Proof. exact (@lem3392735 _88095 x s h1 (@lem3392725 _88095 s x h2 h3)). Qed.
Lemma lem3392739 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term113 _88095 s) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : term324.
Proof. exact (fun h0 : ~ False => @lem3392738 _88095 s x h1 h2 h3). Qed.
Lemma lem3392741 (p : Prop) : (term322 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3392742 : term324 = False.
Proof. exact (@lem3392741 False). Qed.
Lemma lem3392743 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term113 _88095 s) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : False.
Proof. exact (EQ_MP (@lem3392742) (@lem3392739 _88095 s x h1 h2 h3)). Qed.
Lemma lem3392744 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term113 _88095 s) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : (term37 _88095 s) = False.
Proof. exact (prop_ext (fun h4 : term37 _88095 s => @lem3392743 _88095 s x h1 h2 h3) (fun h4 : False => @lem3392511 _88095 s h2)). Qed.
Lemma lem3392746 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term113 _88095 s) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : False.
Proof. exact (EQ_MP (@lem3392744 _88095 s x h1 h2 h3) (@lem3392511 _88095 s h2)). Qed.
Lemma lem3392747 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term118 _88100 x' c) (h2 : term122 _88095 _88100 s x' c) : False.
Proof. exact (EQ_MP (@lem3392668) (@lem3392665 _88095 _88100 s x' c h1 h2)). Qed.
Lemma lem3392748 {_88095 _88100 : Type'} (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term175 _88095 _88100 x'' s x' c) : False.
Proof. exact (EQ_MP (@lem3392610) (@lem3392607 _88095 _88100 x'' s x' c h1)). Qed.
Lemma lem3392749 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term113 _88095 s) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : (term37 _88095 s) = False.
Proof. exact (prop_ext (fun h4 : term37 _88095 s => @lem3392746 _88095 s x h1 h2 h3) (fun h4 : False => @lem3392315 _88095 s h2)). Qed.
Lemma lem3392750 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term113 _88095 s) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : False.
Proof. exact (EQ_MP (@lem3392749 _88095 s x h1 h2 h3) (@lem3392315 _88095 s h2)). Qed.
Lemma lem3392751 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term118 _88100 x' c) (h2 : term122 _88095 _88100 s x' c) : (term118 _88100 x' c) = False.
Proof. exact (prop_ext (fun h3 : term118 _88100 x' c => @lem3392747 _88095 _88100 s x' c h1 h2) (fun h3 : False => @lem3392313 _88100 x' c h1)). Qed.
Lemma lem3392752 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term118 _88100 x' c) (h2 : term122 _88095 _88100 s x' c) : False.
Proof. exact (EQ_MP (@lem3392751 _88095 _88100 s x' c h1 h2) (@lem3392313 _88100 x' c h1)). Qed.
Lemma lem3392753 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term113 _88095 s) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : (term37 _88095 s) = False.
Proof. exact (prop_ext (fun h4 : term37 _88095 s => @lem3392750 _88095 s x h1 h2 h3) (fun h4 : False => @lem3392179 _88095 s h2)). Qed.
Lemma lem3392754 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term113 _88095 s) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : False.
Proof. exact (EQ_MP (@lem3392753 _88095 s x h1 h2 h3) (@lem3392179 _88095 s h2)). Qed.
Lemma lem3392755 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term118 _88100 x' c) (h2 : term122 _88095 _88100 s x' c) : (term118 _88100 x' c) = False.
Proof. exact (prop_ext (fun h3 : term118 _88100 x' c => @lem3392752 _88095 _88100 s x' c h1 h2) (fun h3 : False => @lem3392175 _88100 x' c h1)). Qed.
Lemma lem3392756 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term118 _88100 x' c) (h2 : term122 _88095 _88100 s x' c) : False.
Proof. exact (EQ_MP (@lem3392755 _88095 _88100 s x' c h1 h2) (@lem3392175 _88100 x' c h1)). Qed.
Lemma lem3392757 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term113 _88095 s) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : (term113 _88095 s) = False.
Proof. exact (prop_ext (fun h4 : term113 _88095 s => @lem3392754 _88095 s x h1 h2 h3) (fun h4 : False => @lem3392245 _88095 s h1)). Qed.
Lemma lem3392758 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term113 _88095 s) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : False.
Proof. exact (EQ_MP (@lem3392757 _88095 s x h1 h2 h3) (@lem3392245 _88095 s h1)). Qed.
Lemma lem3392759 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term113 _88095 s) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : (term37 _88095 s) = False.
Proof. exact (prop_ext (fun h4 : term37 _88095 s => @lem3392758 _88095 s x h1 h2 h3) (fun h4 : False => @lem3392179 _88095 s h2)). Qed.
Lemma lem3392760 {_88095 : Type'} (s : _88095 -> Prop) (x : type684 _88095) (h1 : term113 _88095 s) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : False.
Proof. exact (EQ_MP (@lem3392759 _88095 s x h1 h2 h3) (@lem3392179 _88095 s h2)). Qed.
Lemma lem3392761 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term118 _88100 x' c) (h2 : term122 _88095 _88100 s x' c) : (term118 _88100 x' c) = False.
Proof. exact (prop_ext (fun h3 : term118 _88100 x' c => @lem3392756 _88095 _88100 s x' c h1 h2) (fun h3 : False => @lem3392175 _88100 x' c h1)). Qed.
Lemma lem3392762 {_88095 _88100 : Type'} (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term118 _88100 x' c) (h2 : term122 _88095 _88100 s x' c) : False.
Proof. exact (EQ_MP (@lem3392761 _88095 _88100 s x' c h1 h2) (@lem3392175 _88100 x' c h1)). Qed.
Lemma lem3392763 {_88095 _88100 : Type'} (x : type684 _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term37 _88095 s) (h2 : term309 _88095 x) (h3 : term122 _88095 _88100 s x' c) : False.
Proof. exact (or_elim (@lem3392035 _88095 _88100 s x' c h3) (fun h0 : term118 _88100 x' c => @lem3392762 _88095 _88100 s x' c h0 h3) (fun h0 : term113 _88095 s => @lem3392760 _88095 s x h0 h1 h2)). Qed.
Lemma lem3392764 {_88095 _88100 : Type'} (x : type684 _88095) (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term37 _88095 s) (h2 : term309 _88095 x) (h3 : term211 _88095 _88100 x'' s x' c) : False.
Proof. exact (or_elim (@lem3392025 _88095 _88100 x'' s x' c h3) (fun h0 : term175 _88095 _88100 x'' s x' c => @lem3392748 _88095 _88100 x'' s x' c h0) (fun h0 : term122 _88095 _88100 s x' c => @lem3392763 _88095 _88100 x s x' c h1 h2 h0)). Qed.
Lemma lem3392765 {_88095 _88100 : Type'} (x : type684 _88095) (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term37 _88095 s) (h2 : term309 _88095 x) (h3 : term211 _88095 _88100 x'' s x' c) : (term211 _88095 _88100 x'' s x' c) = False.
Proof. exact (prop_ext (fun h4 : term211 _88095 _88100 x'' s x' c => @lem3392764 _88095 _88100 x x'' s x' c h1 h2 h3) (fun h4 : False => @lem3392025 _88095 _88100 x'' s x' c h3)). Qed.
Lemma lem3392766 {_88095 _88100 : Type'} (x : type684 _88095) (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term37 _88095 s) (h2 : term309 _88095 x) (h3 : term211 _88095 _88100 x'' s x' c) : False.
Proof. exact (EQ_MP (@lem3392765 _88095 _88100 x x'' s x' c h1 h2 h3) (@lem3392025 _88095 _88100 x'' s x' c h3)). Qed.
Lemma lem3392767 {_88095 _88100 : Type'} (x : type684 _88095) (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term37 _88095 s) (h2 : term309 _88095 x) (h3 : term211 _88095 _88100 x'' s x' c) : (term309 _88095 x) = False.
Proof. exact (prop_ext (fun h4 : term309 _88095 x => @lem3392766 _88095 _88100 x x'' s x' c h1 h2 h3) (fun h4 : False => @lem3391970 _88095 x h2)). Qed.
Lemma lem3392768 {_88095 _88100 : Type'} (x : type684 _88095) (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term37 _88095 s) (h2 : term309 _88095 x) (h3 : term211 _88095 _88100 x'' s x' c) : False.
Proof. exact (EQ_MP (@lem3392767 _88095 _88100 x x'' s x' c h1 h2 h3) (@lem3391970 _88095 x h2)). Qed.
Lemma lem3392769 {_88095 _88100 : Type'} (x : type684 _88095) (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term37 _88095 s) (h2 : term309 _88095 x) (h3 : term211 _88095 _88100 x'' s x' c) : (term37 _88095 s) = False.
Proof. exact (prop_ext (fun h4 : term37 _88095 s => @lem3392768 _88095 _88100 x x'' s x' c h1 h2 h3) (fun h4 : False => @lem3391925 _88095 s h1)). Qed.
Lemma lem3392770 {_88095 _88100 : Type'} (x : type684 _88095) (x'' : _88095) (s : _88095 -> Prop) (x' : _88100) (c : _88100) (h1 : term37 _88095 s) (h2 : term309 _88095 x) (h3 : term211 _88095 _88100 x'' s x' c) : False.
Proof. exact (EQ_MP (@lem3392769 _88095 _88100 x x'' s x' c h1 h2 h3) (@lem3391925 _88095 s h1)). Qed.
Lemma lem3392771 {_88095 _88100 : Type'} (x' : _88100) (c : _88100) (s : _88095 -> Prop) (x : type684 _88095) (h1 : term214 _88095 _88100 s x' c) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : False.
Proof. exact (ex_elim (@lem3391916 _88095 _88100 s x' c h1) (fun x'' : _88095 => fun h0 : term213 _88095 _88100 s x' c x'' => @lem3392770 _88095 _88100 x x'' s x' c h2 h3 h0)). Qed.
Lemma lem3392772 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (x : type684 _88095) (h1 : term87 _88095 _88100 s c) (h2 : term37 _88095 s) (h3 : term309 _88095 x) : False.
Proof. exact (ex_elim (@lem3391660 _88095 _88100 s c h1) (fun x' : _88100 => fun h0 : term215 _88095 _88100 s c x' => @lem3392771 _88095 _88100 x' c s x h0 h2 h3)). Qed.
Lemma lem3392773 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term66 _88095) (h2 : term87 _88095 _88100 s c) (h3 : term37 _88095 s) : False.
Proof. exact (ex_elim (@lem3391914 _88095 h1) (fun x : type684 _88095 => fun h0 : term311 _88095 x => @lem3392772 _88095 _88100 c s x h2 h3 h0)). Qed.
Lemma lem3392774 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term66 _88095) (h2 : term87 _88095 _88100 s c) (h3 : term37 _88095 s) : (term37 _88095 s) = False.
Proof. exact (prop_ext (fun h4 : term37 _88095 s => @lem3392773 _88095 _88100 c s h1 h2 h3) (fun h4 : False => @lem3391366 _88095 s h3)). Qed.
Lemma lem3392775 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term66 _88095) (h2 : term87 _88095 _88100 s c) (h3 : term37 _88095 s) : False.
Proof. exact (EQ_MP (@lem3392774 _88095 _88100 c s h1 h2 h3) (@lem3391366 _88095 s h3)). Qed.
Lemma lem3392776 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term87 _88095 _88100 s c) (h2 : term37 _88095 s) : term90 _88095.
Proof. exact (fun h0 : term66 _88095 => @lem3392775 _88095 _88100 c s h0 h1 h2). Qed.
Lemma lem3392777 {_88095 : Type'} : (term90 _88095) = (term91 _88095).
Proof. exact (@lem69 (term66 _88095)). Qed.
Lemma lem3392778 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term87 _88095 _88100 s c) (h2 : term37 _88095 s) : term91 _88095.
Proof. exact (EQ_MP (@lem3392777 _88095) (@lem3392776 _88095 _88100 c s h1 h2)). Qed.
Lemma lem3392779 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term37 _88095 s) : term93 _88095 _88100 s c.
Proof. exact (fun h0 : term87 _88095 _88100 s c => @lem3392778 _88095 _88100 c s h0 h1). Qed.
Lemma lem3392780 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : term94 _88095 _88100 s c.
Proof. exact (fun h0 : term37 _88095 s => @lem3392779 _88095 _88100 c s h0). Qed.
Lemma lem3392785 {_88095 _88100 : Type'} (c : _88100) : term98 _88095 _88100 c.
Proof. exact (fun s : _88095 -> Prop => @lem3392780 _88095 _88100 s c). Qed.
Lemma lem3392790 {_88095 _88100 : Type'} : term102 _88095 _88100.
Proof. exact (fun c : _88100 => @lem3392785 _88095 _88100 c). Qed.
Lemma lem3392791 {_88095 _88100 : Type'} : term101 _88095 _88100.
Proof. exact (EQ_MP (@lem3391357 _88095 _88100) (@lem3392790 _88095 _88100)). Qed.
Lemma lem3392792 {_88095 _88100 : Type'} (c : _88100) : term334 _88095 _88100 c.
Proof. exact (@lem3392791 _88095 _88100 c). Qed.
Lemma lem3392793 {_88095 _88100 : Type'} (c : _88100) : (term334 _88095 _88100 c) = (term97 _88095 _88100 c).
Proof. exact (eq_refl (term334 _88095 _88100 c)). Qed.
Lemma lem3392794 {_88095 _88100 : Type'} (c : _88100) : term97 _88095 _88100 c.
Proof. exact (EQ_MP (@lem3392793 _88095 _88100 c) (@lem3392792 _88095 _88100 c)). Qed.
Lemma lem3392795 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) : term335 _88095 _88100 c s.
Proof. exact (@lem3392794 _88095 _88100 c s). Qed.
Lemma lem3392796 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term335 _88095 _88100 c s) = (term67 _88095 _88100 s c).
Proof. exact (eq_refl (term335 _88095 _88100 c s)). Qed.
Lemma lem3392797 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : term67 _88095 _88100 s c.
Proof. exact (EQ_MP (@lem3392796 _88095 _88100 s c) (@lem3392795 _88095 _88100 c s)). Qed.
Lemma lem3392799 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : term67 _88095 _88100 s c.
Proof. exact (@lem3391171 _88095 _88100 s c (@lem3392797 _88095 _88100 s c)). Qed.
Lemma lem3392800 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term37 _88095 s) : term92 _88095 _88100 s c.
Proof. exact (@lem3392799 _88095 _88100 s c (@lem3391003 _88095 s h1)). Qed.
Lemma lem3392801 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term65 _88095 _88100 s c) (h2 : term37 _88095 s) : term90 _88095.
Proof. exact (@lem3392800 _88095 _88100 c s h2 (@lem3391152 _88095 _88100 s c h1)). Qed.
Lemma lem3392802 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term65 _88095 _88100 s c) (h2 : term37 _88095 s) : False.
Proof. exact (@lem3392801 _88095 _88100 c s h1 h2 (@lem3391153 _88095)). Qed.
Lemma lem3392803 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term65 _88095 _88100 s c) (h2 : term37 _88095 s) : (term65 _88095 _88100 s c) = False.
Proof. exact (prop_ext (fun h3 : term65 _88095 _88100 s c => @lem3392802 _88095 _88100 c s h1 h2) (fun h3 : False => @lem3391152 _88095 _88100 s c h1)). Qed.
Lemma lem3392804 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term65 _88095 _88100 s c) (h2 : term37 _88095 s) : False.
Proof. exact (EQ_MP (@lem3392803 _88095 _88100 c s h1 h2) (@lem3391152 _88095 _88100 s c h1)). Qed.
Lemma lem3392805 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term37 _88095 s) : term64 _88095 _88100 s c.
Proof. exact (fun h0 : term65 _88095 _88100 s c => @lem3392804 _88095 _88100 c s h0 h1). Qed.
Lemma lem3392806 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term37 _88095 s) : term62 _88095 _88100 s c.
Proof. exact (EQ_MP (@lem3391151 _88095 _88100 s c) (@lem3392805 _88095 _88100 c s h1)). Qed.
Lemma lem3392809 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term37 _88095 s) : (term23 _88095 _88100 c s) = (@INSERT _88100 c (@EMPTY _88100)).
Proof. exact (EQ_MP (@lem3391147 _88095 _88100 s c) (@lem3392806 _88095 _88100 c s h1)). Qed.
Lemma lem3392810 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term37 _88095 s) : (term37 _88095 s) = ((term23 _88095 _88100 c s) = (@INSERT _88100 c (@EMPTY _88100))).
Proof. exact (prop_ext (fun h2 : term37 _88095 s => @lem3392809 _88095 _88100 c s h1) (fun h2 : (term23 _88095 _88100 c s) = (@INSERT _88100 c (@EMPTY _88100)) => @lem3391003 _88095 s h1)). Qed.
Lemma lem3392811 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : term37 _88095 s) : (term23 _88095 _88100 c s) = (@INSERT _88100 c (@EMPTY _88100)).
Proof. exact (EQ_MP (@lem3392810 _88095 _88100 c s h1) (@lem3391003 _88095 s h1)). Qed.
Lemma lem3392812 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : term26 _88095 _88100 s c.
Proof. exact (fun h0 : term37 _88095 s => @lem3392811 _88095 _88100 c s h0). Qed.
Lemma lem3392813 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : s = (@EMPTY _88095)) : (term23 _88095 _88100 c s) = (@EMPTY _88100).
Proof. exact (EQ_MP (@lem3391042 _88095 _88100 c s h1) (@lem0)). Qed.
Lemma lem3392814 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : s = (@EMPTY _88095)) : (s = (@EMPTY _88095)) = ((term23 _88095 _88100 c s) = (@EMPTY _88100)).
Proof. exact (prop_ext (fun h2 : s = (@EMPTY _88095) => @lem3392813 _88095 _88100 c s h1) (fun h2 : (term23 _88095 _88100 c s) = (@EMPTY _88100) => @lem3390986 _88095 s h1)). Qed.
Lemma lem3392815 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) (h1 : s = (@EMPTY _88095)) : (term23 _88095 _88100 c s) = (@EMPTY _88100).
Proof. exact (EQ_MP (@lem3392814 _88095 _88100 c s h1) (@lem3390986 _88095 s h1)). Qed.
Lemma lem3392816 {_88095 _88100 : Type'} (c : _88100) (s : _88095 -> Prop) : term30 _88095 _88100 c s.
Proof. exact (fun h0 : s = (@EMPTY _88095) => @lem3392815 _88095 _88100 c s h0). Qed.
Lemma lem3392817 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : term33 _88095 _88100 s c.
Proof. exact (conj (@lem3392816 _88095 _88100 c s) (@lem3392812 _88095 _88100 s c)). Qed.
Lemma lem3392818 {_88095 _88100 : Type'} (s : _88095 -> Prop) (c : _88100) : (term23 _88095 _88100 c s) = (term34 _88095 _88100 s c).
Proof. exact (EQ_MP (@lem3390985 _88095 _88100 s c) (@lem3392817 _88095 _88100 s c)). Qed.
Lemma lem3392823 {_88095 _88100 : Type'} (s : _88095 -> Prop) : term336 _88095 _88100 s.
Proof. exact (fun c : _88100 => @lem3392818 _88095 _88100 s c). Qed.
Lemma lem3392828 {_88095 _88100 : Type'} : term337 _88095 _88100.
Proof. exact (fun s : _88095 -> Prop => @lem3392823 _88095 _88100 s). Qed.
