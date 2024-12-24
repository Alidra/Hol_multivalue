Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_ABS_BOUND_term_abbrevs.
Require Import SUM_ABS_spec.
Require Import SUM_BOUND_spec.
Require Import thm0_spec.
Require Import thm1339577_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7136924 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem7136925 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem7136924 h1 x). Qed.
Lemma lem7136926 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem7136927 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem7136926 x) (@lem7136925 x h1)). Qed.
Lemma lem7136928 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem7136927 x h1 y). Qed.
Lemma lem7136929 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem7136930 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem7136929 y x) (@lem7136928 x y h1)). Qed.
Lemma lem7136931 (y : real) (x : real) (z : real) (h1 : term0) : term5 y x z.
Proof. exact (@lem7136930 y x h1 z). Qed.
Lemma lem7136932 (y : real) (x : real) (z : real) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem7136933 (y : real) (x : real) (z : real) (h1 : term0) : term6 y x z.
Proof. exact (EQ_MP (@lem7136932 y x z) (@lem7136931 y x z h1)). Qed.
Lemma lem7136934 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term7 x y z.
Proof. exact (h1). Qed.
Lemma lem7136935 (x : real) (y : real) (z : real) (h1 : term0) (h2 : term7 x y z) : real_le x z.
Proof. exact (@lem7136933 y x z h1 (@lem7136934 x y z h2)). Qed.
Lemma lem7136936 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term8 x z.
Proof. exact (fun h0 : term0 => @lem7136935 x y z h0 h1). Qed.
Lemma lem7136937 (x : real) (z : real) (h1 : term9 x z) : term9 x z.
Proof. exact (h1). Qed.
Lemma lem7136938 (x : real) (z : real) (h1 : term9 x z) : term8 x z.
Proof. exact (ex_elim (@lem7136937 x z h1) (fun y : real => fun h0 : term10 x z y => @lem7136936 x y z h0)). Qed.
Lemma lem7136939 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem7136940 (x : real) (z : real) (h1 : term0) (h2 : term9 x z) : real_le x z.
Proof. exact (@lem7136938 x z h2 (@lem7136939 h1)). Qed.
Lemma lem7136941 (x : real) (z : real) (h1 : term0) : term11 x z.
Proof. exact (fun h0 : term9 x z => @lem7136940 x z h1 h0). Qed.
Lemma lem7136942 (x : real) (h1 : term0) : term12 x.
Proof. exact (fun z : real => @lem7136941 x z h1). Qed.
Lemma lem7136943 (h1 : term0) : term13.
Proof. exact (fun x : real => @lem7136942 x h1). Qed.
Lemma lem7136944 : term14.
Proof. exact (fun h0 : term0 => @lem7136943 h0). Qed.
Lemma lem7136945 : term13.
Proof. exact (@lem7136944 (@lem1339577)). Qed.
Lemma lem7136946 (x : real) : term15 x.
Proof. exact (@lem7136945 x). Qed.
Lemma lem7136947 (x : real) : (term15 x) = (term12 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem7136948 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem7136947 x) (@lem7136946 x)). Qed.
Lemma lem7136949 (x : real) (z : real) : term16 x z.
Proof. exact (@lem7136948 x z). Qed.
Lemma lem7136950 (x : real) (z : real) : (term16 x z) = (term11 x z).
Proof. exact (eq_refl (term16 x z)). Qed.
Lemma lem7136952 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term17 A s f b) : term17 A s f b.
Proof. exact (h1). Qed.
Lemma lem7136953 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term18 A s f b) : term18 A s f b.
Proof. exact (h1). Qed.
Lemma lem7136954 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7136956 (x : real) (z : real) : term11 x z.
Proof. exact (EQ_MP (@lem7136950 x z) (@lem7136949 x z)). Qed.
Lemma lem7136957 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term19 A f s b.
Proof. exact (@lem7136956 (term20 A s f) (term21 A s b)). Qed.
Lemma lem7136958 {_132408 : Type'} (f : _132408 -> real) : term22 _132408 f.
Proof. exact (@lem7083749 _132408 f). Qed.
Lemma lem7136959 {_132408 : Type'} (f : _132408 -> real) : (term22 _132408 f) = (term23 _132408 f).
Proof. exact (eq_refl (term22 _132408 f)). Qed.
Lemma lem7136960 {_132408 : Type'} (f : _132408 -> real) : term23 _132408 f.
Proof. exact (EQ_MP (@lem7136959 _132408 f) (@lem7136958 _132408 f)). Qed.
Lemma lem7136961 {_132408 : Type'} (f : _132408 -> real) (s : _132408 -> Prop) : term24 _132408 f s.
Proof. exact (@lem7136960 _132408 f s). Qed.
Lemma lem7136962 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : (term24 _132408 f s) = (term25 _132408 s f).
Proof. exact (eq_refl (term24 _132408 f s)). Qed.
Lemma lem7136963 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : term25 _132408 s f.
Proof. exact (EQ_MP (@lem7136962 _132408 s f) (@lem7136961 _132408 f s)). Qed.
Lemma lem7136964 {_132408 : Type'} (s : _132408 -> Prop) (h1 : @FINITE _132408 s) : @FINITE _132408 s.
Proof. exact (h1). Qed.
Lemma lem7136965 {_132408 : Type'} (f : _132408 -> real) (s : _132408 -> Prop) (h1 : @FINITE _132408 s) : term26 _132408 s f.
Proof. exact (@lem7136963 _132408 s f (@lem7136964 _132408 s h1)). Qed.
Lemma lem7136966 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : (term26 _132408 s f) = ((term26 _132408 s f) = True).
Proof. exact (@lem7 (term26 _132408 s f)). Qed.
Lemma lem7136967 {_132408 : Type'} (f : _132408 -> real) (s : _132408 -> Prop) (h1 : @FINITE _132408 s) : (term26 _132408 s f) = True.
Proof. exact (EQ_MP (@lem7136966 _132408 s f) (@lem7136965 _132408 f s h1)). Qed.
Lemma lem7136973 {A : Type'} (s : A -> Prop) : term27 A s.
Proof. exact (@lem7132622 A s). Qed.
Lemma lem7136974 {A : Type'} (s : A -> Prop) : (term27 A s) = (term28 A s).
Proof. exact (eq_refl (term27 A s)). Qed.
Lemma lem7136975 {A : Type'} (s : A -> Prop) : term28 A s.
Proof. exact (EQ_MP (@lem7136974 A s) (@lem7136973 A s)). Qed.
Lemma lem7136976 {A : Type'} (s : A -> Prop) (f : A -> real) : term29 A s f.
Proof. exact (@lem7136975 A s f). Qed.
Lemma lem7136977 {A : Type'} (f : A -> real) (s : A -> Prop) : (term29 A s f) = (term30 A f s).
Proof. exact (eq_refl (term29 A s f)). Qed.
Lemma lem7136978 {A : Type'} (f : A -> real) (s : A -> Prop) : term30 A f s.
Proof. exact (EQ_MP (@lem7136977 A f s) (@lem7136976 A s f)). Qed.
Lemma lem7136979 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term31 A f s b.
Proof. exact (@lem7136978 A f s b). Qed.
Lemma lem7136980 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term31 A f s b) = (term32 A f s b).
Proof. exact (eq_refl (term31 A f s b)). Qed.
Lemma lem7136981 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term32 A f s b.
Proof. exact (EQ_MP (@lem7136980 A f s b) (@lem7136979 A f s b)). Qed.
Lemma lem7136982 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term33 A s f b) : term33 A s f b.
Proof. exact (h1). Qed.
Lemma lem7136983 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term33 A s f b) : term34 A f s b.
Proof. exact (@lem7136981 A f s b (@lem7136982 A s f b h1)). Qed.
Lemma lem7136984 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term34 A f s b) = ((term34 A f s b) = True).
Proof. exact (@lem7 (term34 A f s b)). Qed.
Lemma lem7136985 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term33 A s f b) : (term34 A f s b) = True.
Proof. exact (EQ_MP (@lem7136984 A f s b) (@lem7136983 A s f b h1)). Qed.
Lemma lem7136991 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7136993 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term18 A s f b) : term35 A s f b x.
Proof. exact (@lem7136953 A s f b h1 x). Qed.
Lemma lem7136994 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term35 A s f b x) = (term36 A s f x b).
Proof. exact (eq_refl (term35 A s f b x)). Qed.
Lemma lem7136995 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term18 A s f b) : term36 A s f x b.
Proof. exact (EQ_MP (@lem7136994 A s f x b) (@lem7136993 A x s f b h1)). Qed.
Lemma lem7136996 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7136997 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @IN A x s) : term37 A f x b.
Proof. exact (@lem7136995 A x s f b h1 (@lem7136996 A x s h2)). Qed.
Lemma lem7136998 {A : Type'} (f : A -> real) (x : A) (b : real) : (term37 A f x b) = ((term37 A f x b) = True).
Proof. exact (@lem7 (term37 A f x b)). Qed.
Lemma lem7136999 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @IN A x s) : (term37 A f x b) = True.
Proof. exact (EQ_MP (@lem7136998 A f x b) (@lem7136997 A f b x s h1 h2)). Qed.
Lemma lem7137008 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : term38 _132408 s f.
Proof. exact (fun h0 : @FINITE _132408 s => @lem7136967 _132408 f s h0). Qed.
Lemma lem7137009 {A : Type'} (s : A -> Prop) (f : A -> real) : term38 A s f.
Proof. exact (@lem7137008 A s f). Qed.
Lemma lem7137011 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7136991 A s) (@lem7136954 A s h1)). Qed.
Lemma lem7137012 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem7137011 A s h1)). Qed.
Lemma lem7137013 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem7137012 A s h1) (@lem0)). Qed.
Lemma lem7137014 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term26 A s f) = True.
Proof. exact (@lem7137009 A s f (@lem7137013 A s h1)). Qed.
Lemma lem7137015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7137016 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term39 A s f) = (and True).
Proof. exact (MK_COMB (@lem7137015) (@lem7137014 A f s h1)). Qed.
Lemma lem7137018 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term40 A f s b.
Proof. exact (fun h0 : term33 A s f b => @lem7136985 A s f b h0). Qed.
Lemma lem7137019 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term40 A f s b.
Proof. exact (@lem7137018 A f s b). Qed.
Lemma lem7137020 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term41 A f s b.
Proof. exact (@lem7137019 A (term42 A f) s b). Qed.
Lemma lem7137024 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7136991 A s) (@lem7136954 A s h1)). Qed.
Lemma lem7137025 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7137026 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term43 A s) = (and True).
Proof. exact (MK_COMB (@lem7137025) (@lem7137024 A s h1)). Qed.
Lemma lem7137034 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term44 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7137035 (p : Prop) (q : Prop) (p' : Prop) : term45 p q p'.
Proof. exact (fun q' : Prop => @lem7137034 p q p' q'). Qed.
Lemma lem7137036 (p : Prop) (q : Prop) : term46 p q.
Proof. exact (fun p' : Prop => @lem7137035 p q p'). Qed.
Lemma lem7137037 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : term47 A s f x b.
Proof. exact (@lem7137036 (@IN A x s) (term48 A f x b)). Qed.
Lemma lem7137038 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (p' : Prop) : term49 A s f x b p'.
Proof. exact (@lem7137037 A s f x b p'). Qed.
Lemma lem7137039 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (p' : Prop) : (term49 A s f x b p') = (term50 A s f x b p').
Proof. exact (eq_refl (term49 A s f x b p')). Qed.
Lemma lem7137040 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (p' : Prop) : term50 A s f x b p'.
Proof. exact (EQ_MP (@lem7137039 A s f x b p') (@lem7137038 A s f x b p')). Qed.
Lemma lem7137041 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (p' : Prop) (q' : Prop) : term51 A s f x b p' q'.
Proof. exact (@lem7137040 A s f x b p' q'). Qed.
Lemma lem7137042 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (p' : Prop) (q' : Prop) : (term51 A s f x b p' q') = (term52 A s f x b p' q').
Proof. exact (eq_refl (term51 A s f x b p' q')). Qed.
Lemma lem7137043 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (p' : Prop) (q' : Prop) : term52 A s f x b p' q'.
Proof. exact (EQ_MP (@lem7137042 A s f x b p' q') (@lem7137041 A s f x b p' q')). Qed.
Lemma lem7137044 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem7137045 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (q' : Prop) : term53 A f b x s q'.
Proof. exact (@lem7137043 A s f x b (@IN A x s) q'). Qed.
Lemma lem7137046 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (q' : Prop) : term54 A f b x s q'.
Proof. exact (@lem7137045 A f b x s q' (@lem7137044 A x s)). Qed.
Lemma lem7137047 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7137048 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem7137051 {A B : Type'} (f : A -> B) (y : A) : (term55 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7137052 {A : Type'} (f : A -> real) (y : A) : (term56 A f y) = (f y).
Proof. exact (@lem7137051 A real f y). Qed.
Lemma lem7137053 {A : Type'} (f : A -> real) (x : A) : (term57 A f x) = (term58 A f x).
Proof. exact (@lem7137052 A (term42 A f) x). Qed.
Lemma lem7137054 {A : Type'} (f : A -> real) (x : A) : (term58 A f x) = (term59 A f x).
Proof. exact (eq_refl (term58 A f x)). Qed.
Lemma lem7137055 {A : Type'} (f : A -> real) : (term60 A f) = (term42 A f).
Proof. exact (fun_ext (fun x : A => @lem7137054 A f x)). Qed.
Lemma lem7137056 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7137057 {A : Type'} (f : A -> real) (x : A) : (term57 A f x) = (term58 A f x).
Proof. exact (MK_COMB (@lem7137055 A f) (@lem7137056 A x)). Qed.
Lemma lem7137058 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7137059 {A : Type'} (f : A -> real) (x : A) : (term61 A f x) = (term62 A f x).
Proof. exact (MK_COMB (@lem7137058) (@lem7137057 A f x)). Qed.
Lemma lem7137060 {A : Type'} (f : A -> real) (x : A) : (term58 A f x) = (term59 A f x).
Proof. exact (eq_refl (term58 A f x)). Qed.
Lemma lem7137061 {A : Type'} (f : A -> real) (x : A) : ((term57 A f x) = (term58 A f x)) = ((term58 A f x) = (term59 A f x)).
Proof. exact (MK_COMB (@lem7137059 A f x) (@lem7137060 A f x)). Qed.
Lemma lem7137062 {A : Type'} (f : A -> real) (x : A) : (term58 A f x) = (term59 A f x).
Proof. exact (EQ_MP (@lem7137061 A f x) (@lem7137053 A f x)). Qed.
Lemma lem7137063 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7137064 {A : Type'} (f : A -> real) (x : A) : (term63 A f x) = (term64 A f x).
Proof. exact (MK_COMB (@lem7137063) (@lem7137062 A f x)). Qed.
Lemma lem7137065 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7137066 {A : Type'} (f : A -> real) (x : A) (b : real) : (term48 A f x b) = (term37 A f x b).
Proof. exact (MK_COMB (@lem7137064 A f x) (@lem7137065 b)). Qed.
Lemma lem7137068 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term18 A s f b) : term65 A s f x b.
Proof. exact (fun h0 : @IN A x s => @lem7136999 A f b x s h1 h0). Qed.
Lemma lem7137069 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term18 A s f b) : term65 A s f x b.
Proof. exact (@lem7137068 A x s f b h1). Qed.
Lemma lem7137071 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem7137048 A x s) (@lem7137047 A x s h1)). Qed.
Lemma lem7137072 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : True = (@IN A x s).
Proof. exact (SYM (@lem7137071 A x s h1)). Qed.
Lemma lem7137073 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem7137072 A x s h1) (@lem0)). Qed.
Lemma lem7137074 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @IN A x s) : (term37 A f x b) = True.
Proof. exact (@lem7137069 A x s f b h1 (@lem7137073 A x s h2)). Qed.
Lemma lem7137075 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @IN A x s) : (term48 A f x b) = True.
Proof. exact (TRANS (@lem7137066 A f x b) (@lem7137074 A f b x s h1 h2)). Qed.
Lemma lem7137076 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term18 A s f b) : term66 A s f x b.
Proof. exact (fun h0 : @IN A x s => @lem7137075 A f b x s h1 h0). Qed.
Lemma lem7137077 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : term67 A f b x s.
Proof. exact (@lem7137046 A f b x s True). Qed.
Lemma lem7137078 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term18 A s f b) : (term68 A s f x b) = (term69 A x s).
Proof. exact (@lem7137077 A f b x s (@lem7137076 A x s f b h1)). Qed.
Lemma lem7137080 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7137081 {A : Type'} (x : A) (s : A -> Prop) : (term69 A x s) = True.
Proof. exact (@lem7137080 (@IN A x s)). Qed.
Lemma lem7137082 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term18 A s f b) : (term68 A s f x b) = True.
Proof. exact (TRANS (@lem7137078 A x s f b h1) (@lem7137081 A x s)). Qed.
Lemma lem7137083 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term18 A s f b) : (term70 A s f b) = (term71 A).
Proof. exact (fun_ext (fun x : A => @lem7137082 A x s f b h1)). Qed.
Lemma lem7137084 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7137085 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term18 A s f b) : (term72 A s f b) = (term73 A).
Proof. exact (MK_COMB (@lem7137084 A) (@lem7137083 A s f b h1)). Qed.
Lemma lem7137087 {A : Type'} (t : Prop) : (term74 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7137088 {A : Type'} (t : Prop) : (term74 A t) = t.
Proof. exact (@lem7137087 A t). Qed.
Lemma lem7137089 {A : Type'} : (term73 A) = True.
Proof. exact (@lem7137088 A True). Qed.
Lemma lem7137090 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term18 A s f b) : (term72 A s f b) = True.
Proof. exact (TRANS (@lem7137085 A s f b h1) (@lem7137089 A)). Qed.
Lemma lem7137091 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : (term75 A s f b) = (True /\ True).
Proof. exact (MK_COMB (@lem7137026 A s h2) (@lem7137090 A s f b h1)). Qed.
Lemma lem7137093 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7137094 : (True /\ True) = True.
Proof. exact (@lem7137093 True). Qed.
Lemma lem7137095 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : (term75 A s f b) = True.
Proof. exact (TRANS (@lem7137091 A f b s h1 h2) (@lem7137094)). Qed.
Lemma lem7137096 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : True = (term75 A s f b).
Proof. exact (SYM (@lem7137095 A f b s h1 h2)). Qed.
Lemma lem7137097 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : term75 A s f b.
Proof. exact (EQ_MP (@lem7137096 A f b s h1 h2) (@lem0)). Qed.
Lemma lem7137098 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : (term76 A f s b) = True.
Proof. exact (@lem7137020 A f s b (@lem7137097 A f b s h1 h2)). Qed.
Lemma lem7137099 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : (term77 A f s b) = (True /\ True).
Proof. exact (MK_COMB (@lem7137016 A f s h2) (@lem7137098 A f b s h1 h2)). Qed.
Lemma lem7137101 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7137102 : (True /\ True) = True.
Proof. exact (@lem7137101 True). Qed.
Lemma lem7137103 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : (term77 A f s b) = True.
Proof. exact (TRANS (@lem7137099 A f b s h1 h2) (@lem7137102)). Qed.
Lemma lem7137104 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : True = (term77 A f s b).
Proof. exact (SYM (@lem7137103 A f b s h1 h2)). Qed.
Lemma lem7137105 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : term77 A f s b.
Proof. exact (EQ_MP (@lem7137104 A f b s h1 h2) (@lem0)). Qed.
Lemma lem7137106 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : term78 A f s b.
Proof. exact (ex_intro (term79 A f s b) (term80 A s f) (@lem7137105 A f b s h1 h2)). Qed.
Lemma lem7137107 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : term81 A f s b.
Proof. exact (@lem7136957 A f s b (@lem7137106 A f b s h1 h2)). Qed.
Lemma lem7137108 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term17 A s f b) : term18 A s f b.
Proof. exact (proj2 (@lem7136952 A s f b h1)). Qed.
Lemma lem7137109 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term17 A s f b) : @FINITE A s.
Proof. exact (proj1 (@lem7136952 A s f b h1)). Qed.
Lemma lem7137110 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : (term18 A s f b) = (term81 A f s b).
Proof. exact (prop_ext (fun h3 : term18 A s f b => @lem7137107 A f b s h1 h2) (fun h3 : term81 A f s b => @lem7136953 A s f b h1)). Qed.
Lemma lem7137111 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : term81 A f s b.
Proof. exact (EQ_MP (@lem7137110 A f b s h1 h2) (@lem7136953 A s f b h1)). Qed.
Lemma lem7137112 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : (@FINITE A s) = (term81 A f s b).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7137111 A f b s h1 h2) (fun h3 : term81 A f s b => @lem7136954 A s h2)). Qed.
Lemma lem7137113 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term18 A s f b) (h2 : @FINITE A s) : term81 A f s b.
Proof. exact (EQ_MP (@lem7137112 A f b s h1 h2) (@lem7136954 A s h2)). Qed.
Lemma lem7137114 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : @FINITE A s) (h2 : term17 A s f b) : (term18 A s f b) = (term81 A f s b).
Proof. exact (prop_ext (fun h3 : term18 A s f b => @lem7137113 A f b s h3 h1) (fun h3 : term81 A f s b => @lem7137108 A s f b h2)). Qed.
Lemma lem7137115 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : @FINITE A s) (h2 : term17 A s f b) : term81 A f s b.
Proof. exact (EQ_MP (@lem7137114 A s f b h1 h2) (@lem7137108 A s f b h2)). Qed.
Lemma lem7137116 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term17 A s f b) : (@FINITE A s) = (term81 A f s b).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7137115 A s f b h2 h1) (fun h2 : term81 A f s b => @lem7137109 A s f b h1)). Qed.
Lemma lem7137117 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term17 A s f b) : term81 A f s b.
Proof. exact (EQ_MP (@lem7137116 A s f b h1) (@lem7137109 A s f b h1)). Qed.
Lemma lem7137118 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term82 A f s b.
Proof. exact (fun h0 : term17 A s f b => @lem7137117 A s f b h0). Qed.
Lemma lem7137123 {A : Type'} (f : A -> real) (s : A -> Prop) : term83 A f s.
Proof. exact (fun b : real => @lem7137118 A f s b). Qed.
Lemma lem7137128 {A : Type'} (s : A -> Prop) : term84 A s.
Proof. exact (fun f : A -> real => @lem7137123 A f s). Qed.
Lemma lem7137133 {A : Type'} : term85 A.
Proof. exact (fun s : A -> Prop => @lem7137128 A s). Qed.
