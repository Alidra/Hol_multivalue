Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_CLAUSES_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IMAGE_spec.
Require Import IN_INSERT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm82_spec.
Lemma lem3364907 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3364908 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3364909 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3364908 A s) (@lem3364907 A s)). Qed.
Lemma lem3364910 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3364909 A s t). Qed.
Lemma lem3364911 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = ((s = t) = (term3 A s t)).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3364913 {A : Type'} (x : A) : term4 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3364914 {A : Type'} (x : A) : (term4 A x) = (term5 A x).
Proof. exact (eq_refl (term4 A x)). Qed.
Lemma lem3364915 {A : Type'} (x : A) : term5 A x.
Proof. exact (EQ_MP (@lem3364914 A x) (@lem3364913 A x)). Qed.
Lemma lem3364916 {A : Type'} (x : A) (y : A) : term6 A x y.
Proof. exact (@lem3364915 A x y). Qed.
Lemma lem3364917 {A : Type'} (y : A) (x : A) : (term6 A x y) = (term7 A y x).
Proof. exact (eq_refl (term6 A x y)). Qed.
Lemma lem3364918 {A : Type'} (y : A) (x : A) : term7 A y x.
Proof. exact (EQ_MP (@lem3364917 A y x) (@lem3364916 A x y)). Qed.
Lemma lem3364919 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term8 A y x s.
Proof. exact (@lem3364918 A y x s). Qed.
Lemma lem3364920 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A y x s) = ((term9 A x y s) = (term10 A y x s)).
Proof. exact (eq_refl (term8 A y x s)). Qed.
Lemma lem3364922 {A : Type'} (x : A) : term11 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3364923 {A : Type'} (x : A) : (term11 A x) = (term12 A x).
Proof. exact (eq_refl (term11 A x)). Qed.
Lemma lem3364924 {A : Type'} (x : A) : term12 A x.
Proof. exact (EQ_MP (@lem3364923 A x) (@lem3364922 A x)). Qed.
Lemma lem3364925 {A : Type'} (x : A) : term13 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3364951 {_83095 : Type'} : term14 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3364952 {_83095 : Type'} (p : _83095 -> Prop) : term15 _83095 p.
Proof. exact (@lem3364951 _83095 p). Qed.
Lemma lem3364953 {_83095 : Type'} (p : _83095 -> Prop) : (term15 _83095 p) = (term16 _83095 p).
Proof. exact (eq_refl (term15 _83095 p)). Qed.
Lemma lem3364954 {_83095 : Type'} (p : _83095 -> Prop) : term16 _83095 p.
Proof. exact (EQ_MP (@lem3364953 _83095 p) (@lem3364952 _83095 p)). Qed.
Lemma lem3364955 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term17 _83095 p x.
Proof. exact (@lem3364954 _83095 p x). Qed.
Lemma lem3364956 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term17 _83095 p x) = ((term18 _83095 x p) = (p x)).
Proof. exact (eq_refl (term17 _83095 p x)). Qed.
Lemma lem3364965 {A B : Type'} (s : A -> Prop) : term19 A B s.
Proof. exact (@lem3199546 A B s). Qed.
Lemma lem3364966 {A B : Type'} (s : A -> Prop) : (term19 A B s) = (term20 A B s).
Proof. exact (eq_refl (term19 A B s)). Qed.
Lemma lem3364967 {A B : Type'} (s : A -> Prop) : term20 A B s.
Proof. exact (EQ_MP (@lem3364966 A B s) (@lem3364965 A B s)). Qed.
Lemma lem3364968 {A B : Type'} (s : A -> Prop) (f : A -> B) : term21 A B s f.
Proof. exact (@lem3364967 A B s f). Qed.
Lemma lem3364969 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term21 A B s f) = ((@IMAGE A B f s) = (term22 A B s f)).
Proof. exact (eq_refl (term21 A B s f)). Qed.
Lemma lem3364976 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3364911 A s t) (@lem3364910 A s t)). Qed.
Lemma lem3364977 {_87481 : Type'} (s : _87481 -> Prop) (t : _87481 -> Prop) : (s = t) = (term3 _87481 s t).
Proof. exact (@lem3364976 _87481 s t). Qed.
Lemma lem3364978 {_87477 _87481 : Type'} (f : _87477 -> _87481) : ((@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481)) = (term23 _87477 _87481 f).
Proof. exact (@lem3364977 _87481 (@IMAGE _87477 _87481 f (@EMPTY _87477)) (@EMPTY _87481)). Qed.
Lemma lem3364988 {A B : Type'} (s : A -> Prop) (f : A -> B) : (@IMAGE A B f s) = (term22 A B s f).
Proof. exact (EQ_MP (@lem3364969 A B s f) (@lem3364968 A B s f)). Qed.
Lemma lem3364989 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f s) = (term22 _87477 _87481 s f).
Proof. exact (@lem3364988 _87477 _87481 s f). Qed.
Lemma lem3364990 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (term24 _87477 _87481 f).
Proof. exact (@lem3364989 _87477 _87481 (@EMPTY _87477) f). Qed.
Lemma lem3365002 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3364925 A x (@lem3364924 A x)). Qed.
Lemma lem3365003 {_87477 : Type'} (x : _87477) : (@IN _87477 x (@EMPTY _87477)) = False.
Proof. exact (@lem3365002 _87477 x). Qed.
Lemma lem3365004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3365005 {_87477 : Type'} (x : _87477) : (term25 _87477 x) = (and False).
Proof. exact (MK_COMB (@lem3365004) (@lem3365003 _87477 x)). Qed.
Lemma lem3365010 {_87477 _87481 : Type'} (y : _87481) (f : _87477 -> _87481) (x : _87477) : (y = (f x)) = (y = (f x)).
Proof. exact (eq_refl (y = (f x))). Qed.
Lemma lem3365011 {_87477 _87481 : Type'} (y : _87481) (f : _87477 -> _87481) (x : _87477) : (term26 _87477 _87481 y f x) = (term27 _87477 _87481 y f x).
Proof. exact (MK_COMB (@lem3365005 _87477 x) (@lem3365010 _87477 _87481 y f x)). Qed.
Lemma lem3365013 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3365014 {_87477 _87481 : Type'} (y : _87481) (f : _87477 -> _87481) (x : _87477) : (term27 _87477 _87481 y f x) = False.
Proof. exact (@lem3365013 (y = (f x))). Qed.
Lemma lem3365015 {_87477 _87481 : Type'} (y : _87481) (f : _87477 -> _87481) (x : _87477) : (term26 _87477 _87481 y f x) = False.
Proof. exact (TRANS (@lem3365011 _87477 _87481 y f x) (@lem3365014 _87477 _87481 y f x)). Qed.
Lemma lem3365016 {_87477 _87481 : Type'} (y : _87481) (f : _87477 -> _87481) : (term28 _87477 _87481 y f) = (term29 _87477).
Proof. exact (fun_ext (fun x : _87477 => @lem3365015 _87477 _87481 y f x)). Qed.
Lemma lem3365017 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365018 {_87477 _87481 : Type'} (y : _87481) (f : _87477 -> _87481) : (term30 _87477 _87481 y f) = (term31 _87477).
Proof. exact (MK_COMB (@lem3365017 _87477) (@lem3365016 _87477 _87481 y f)). Qed.
Lemma lem3365020 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem3365021 {_87477 : Type'} (t : Prop) : (term32 _87477 t) = t.
Proof. exact (@lem3365020 _87477 t). Qed.
Lemma lem3365022 {_87477 : Type'} : (term31 _87477) = False.
Proof. exact (@lem3365021 _87477 False). Qed.
Lemma lem3365023 {_87477 _87481 : Type'} (y : _87481) (f : _87477 -> _87481) : (term30 _87477 _87481 y f) = False.
Proof. exact (TRANS (@lem3365018 _87477 _87481 y f) (@lem3365022 _87477)). Qed.
Lemma lem3365024 {_87481 : Type'} (GEN_PVAR_7 : _87481) : (@SETSPEC _87481 GEN_PVAR_7) = (@SETSPEC _87481 GEN_PVAR_7).
Proof. exact (eq_refl (@SETSPEC _87481 GEN_PVAR_7)). Qed.
Lemma lem3365025 {_87477 _87481 : Type'} (y : _87481) (f : _87477 -> _87481) (GEN_PVAR_7 : _87481) : (term33 _87477 _87481 GEN_PVAR_7 y f) = (@SETSPEC _87481 GEN_PVAR_7 False).
Proof. exact (MK_COMB (@lem3365024 _87481 GEN_PVAR_7) (@lem3365023 _87477 _87481 y f)). Qed.
Lemma lem3365026 {_87481 : Type'} (y : _87481) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3365027 {_87477 _87481 : Type'} (f : _87477 -> _87481) (GEN_PVAR_7 : _87481) (y : _87481) : (term34 _87477 _87481 GEN_PVAR_7 f y) = (@SETSPEC _87481 GEN_PVAR_7 False y).
Proof. exact (MK_COMB (@lem3365025 _87477 _87481 y f GEN_PVAR_7) (@lem3365026 _87481 y)). Qed.
Lemma lem3365028 {_87477 _87481 : Type'} (f : _87477 -> _87481) (GEN_PVAR_7 : _87481) : (term35 _87477 _87481 GEN_PVAR_7 f) = (term36 _87481 GEN_PVAR_7).
Proof. exact (fun_ext (fun y : _87481 => @lem3365027 _87477 _87481 f GEN_PVAR_7 y)). Qed.
Lemma lem3365029 {_87481 : Type'} : (@ex _87481) = (@ex _87481).
Proof. exact (eq_refl (@ex _87481)). Qed.
Lemma lem3365030 {_87477 _87481 : Type'} (f : _87477 -> _87481) (GEN_PVAR_7 : _87481) : (term37 _87477 _87481 GEN_PVAR_7 f) = (term38 _87481 GEN_PVAR_7).
Proof. exact (MK_COMB (@lem3365029 _87481) (@lem3365028 _87477 _87481 f GEN_PVAR_7)). Qed.
Lemma lem3365035 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (term39 _87477 _87481 f) = (term40 _87481).
Proof. exact (fun_ext (fun GEN_PVAR_7 : _87481 => @lem3365030 _87477 _87481 f GEN_PVAR_7)). Qed.
Lemma lem3365036 {_87481 : Type'} : (@GSPEC _87481) = (@GSPEC _87481).
Proof. exact (eq_refl (@GSPEC _87481)). Qed.
Lemma lem3365037 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (term24 _87477 _87481 f) = (term41 _87481).
Proof. exact (MK_COMB (@lem3365036 _87481) (@lem3365035 _87477 _87481 f)). Qed.
Lemma lem3365038 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (term41 _87481).
Proof. exact (TRANS (@lem3364990 _87477 _87481 f) (@lem3365037 _87477 _87481 f)). Qed.
Lemma lem3365039 {_87481 : Type'} (x : _87481) : (@IN _87481 x) = (@IN _87481 x).
Proof. exact (eq_refl (@IN _87481 x)). Qed.
Lemma lem3365040 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87481) : (term42 _87477 _87481 x f) = (term43 _87481 x).
Proof. exact (MK_COMB (@lem3365039 _87481 x) (@lem3365038 _87477 _87481 f)). Qed.
Lemma lem3365042 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term18 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3364956 _83095 p x) (@lem3364955 _83095 p x)). Qed.
Lemma lem3365043 {_87481 : Type'} (p : _87481 -> Prop) (x : _87481) : (term18 _87481 x p) = (p x).
Proof. exact (@lem3365042 _87481 p x). Qed.
Lemma lem3365044 {_87481 : Type'} (x : _87481) : (term44 _87481 x) = (term45 _87481 x).
Proof. exact (@lem3365043 _87481 (term29 _87481) x). Qed.
Lemma lem3365045 {_87481 : Type'} (y : _87481) : (term45 _87481 y) = False.
Proof. exact (eq_refl (term45 _87481 y)). Qed.
Lemma lem3365046 {_87481 : Type'} (GEN_PVAR_7 : _87481) : (@SETSPEC _87481 GEN_PVAR_7) = (@SETSPEC _87481 GEN_PVAR_7).
Proof. exact (eq_refl (@SETSPEC _87481 GEN_PVAR_7)). Qed.
Lemma lem3365047 {_87481 : Type'} (y : _87481) (GEN_PVAR_7 : _87481) : (term46 _87481 GEN_PVAR_7 y) = (@SETSPEC _87481 GEN_PVAR_7 False).
Proof. exact (MK_COMB (@lem3365046 _87481 GEN_PVAR_7) (@lem3365045 _87481 y)). Qed.
Lemma lem3365048 {_87481 : Type'} (y : _87481) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3365049 {_87481 : Type'} (GEN_PVAR_7 : _87481) (y : _87481) : (term47 _87481 GEN_PVAR_7 y) = (@SETSPEC _87481 GEN_PVAR_7 False y).
Proof. exact (MK_COMB (@lem3365047 _87481 y GEN_PVAR_7) (@lem3365048 _87481 y)). Qed.
Lemma lem3365050 {_87481 : Type'} (GEN_PVAR_7 : _87481) : (term48 _87481 GEN_PVAR_7) = (term36 _87481 GEN_PVAR_7).
Proof. exact (fun_ext (fun y : _87481 => @lem3365049 _87481 GEN_PVAR_7 y)). Qed.
Lemma lem3365051 {_87481 : Type'} : (@ex _87481) = (@ex _87481).
Proof. exact (eq_refl (@ex _87481)). Qed.
Lemma lem3365052 {_87481 : Type'} (GEN_PVAR_7 : _87481) : (term49 _87481 GEN_PVAR_7) = (term38 _87481 GEN_PVAR_7).
Proof. exact (MK_COMB (@lem3365051 _87481) (@lem3365050 _87481 GEN_PVAR_7)). Qed.
Lemma lem3365053 {_87481 : Type'} : (term50 _87481) = (term40 _87481).
Proof. exact (fun_ext (fun GEN_PVAR_7 : _87481 => @lem3365052 _87481 GEN_PVAR_7)). Qed.
Lemma lem3365054 {_87481 : Type'} : (@GSPEC _87481) = (@GSPEC _87481).
Proof. exact (eq_refl (@GSPEC _87481)). Qed.
Lemma lem3365055 {_87481 : Type'} : (term51 _87481) = (term41 _87481).
Proof. exact (MK_COMB (@lem3365054 _87481) (@lem3365053 _87481)). Qed.
Lemma lem3365056 {_87481 : Type'} (x : _87481) : (@IN _87481 x) = (@IN _87481 x).
Proof. exact (eq_refl (@IN _87481 x)). Qed.
Lemma lem3365057 {_87481 : Type'} (x : _87481) : (term44 _87481 x) = (term43 _87481 x).
Proof. exact (MK_COMB (@lem3365056 _87481 x) (@lem3365055 _87481)). Qed.
Lemma lem3365058 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3365059 {_87481 : Type'} (x : _87481) : (term52 _87481 x) = (term53 _87481 x).
Proof. exact (MK_COMB (@lem3365058) (@lem3365057 _87481 x)). Qed.
Lemma lem3365060 {_87481 : Type'} (x : _87481) : (term45 _87481 x) = False.
Proof. exact (eq_refl (term45 _87481 x)). Qed.
Lemma lem3365061 {_87481 : Type'} (x : _87481) : ((term44 _87481 x) = (term45 _87481 x)) = ((term43 _87481 x) = False).
Proof. exact (MK_COMB (@lem3365059 _87481 x) (@lem3365060 _87481 x)). Qed.
Lemma lem3365062 {_87481 : Type'} (x : _87481) : (term43 _87481 x) = False.
Proof. exact (EQ_MP (@lem3365061 _87481 x) (@lem3365044 _87481 x)). Qed.
Lemma lem3365063 {_87477 _87481 : Type'} (x : _87481) (f : _87477 -> _87481) : (term42 _87477 _87481 x f) = False.
Proof. exact (TRANS (@lem3365040 _87477 _87481 f x) (@lem3365062 _87481 x)). Qed.
Lemma lem3365064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3365065 {_87477 _87481 : Type'} (x : _87481) (f : _87477 -> _87481) : (term54 _87477 _87481 x f) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3365064) (@lem3365063 _87477 _87481 x f)). Qed.
Lemma lem3365067 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3364925 A x (@lem3364924 A x)). Qed.
Lemma lem3365068 {_87481 : Type'} (x : _87481) : (@IN _87481 x (@EMPTY _87481)) = False.
Proof. exact (@lem3365067 _87481 x). Qed.
Lemma lem3365069 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87481) : ((term42 _87477 _87481 x f) = (@IN _87481 x (@EMPTY _87481))) = (False = False).
Proof. exact (MK_COMB (@lem3365065 _87477 _87481 x f) (@lem3365068 _87481 x)). Qed.
Lemma lem3365071 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3365072 : (False = False) = (~ False).
Proof. exact (@lem3365071 False). Qed.
Lemma lem3365074 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3365075 : (False = False) = True.
Proof. exact (TRANS (@lem3365072) (@lem3365074)). Qed.
Lemma lem3365076 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87481) : ((term42 _87477 _87481 x f) = (@IN _87481 x (@EMPTY _87481))) = True.
Proof. exact (TRANS (@lem3365069 _87477 _87481 f x) (@lem3365075)). Qed.
Lemma lem3365077 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (term55 _87477 _87481 f) = (term56 _87481).
Proof. exact (fun_ext (fun x : _87481 => @lem3365076 _87477 _87481 f x)). Qed.
Lemma lem3365078 {_87481 : Type'} : (@all _87481) = (@all _87481).
Proof. exact (eq_refl (@all _87481)). Qed.
Lemma lem3365079 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (term23 _87477 _87481 f) = (term57 _87481).
Proof. exact (MK_COMB (@lem3365078 _87481) (@lem3365077 _87477 _87481 f)). Qed.
Lemma lem3365081 {A : Type'} (t : Prop) : (term58 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3365082 {_87481 : Type'} (t : Prop) : (term58 _87481 t) = t.
Proof. exact (@lem3365081 _87481 t). Qed.
Lemma lem3365083 {_87481 : Type'} : (term57 _87481) = True.
Proof. exact (@lem3365082 _87481 True). Qed.
Lemma lem3365084 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (term23 _87477 _87481 f) = True.
Proof. exact (TRANS (@lem3365079 _87477 _87481 f) (@lem3365083 _87481)). Qed.
Lemma lem3365085 {_87477 _87481 : Type'} (f : _87477 -> _87481) : ((@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481)) = True.
Proof. exact (TRANS (@lem3364978 _87477 _87481 f) (@lem3365084 _87477 _87481 f)). Qed.
Lemma lem3365086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3365087 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (term59 _87477 _87481 f) = (and True).
Proof. exact (MK_COMB (@lem3365086) (@lem3365085 _87477 _87481 f)). Qed.
Lemma lem3365091 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3364911 A s t) (@lem3364910 A s t)). Qed.
Lemma lem3365092 {_87481 : Type'} (s : _87481 -> Prop) (t : _87481 -> Prop) : (s = t) = (term3 _87481 s t).
Proof. exact (@lem3365091 _87481 s t). Qed.
Lemma lem3365093 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (s : _87477 -> Prop) : ((term60 _87477 _87481 f x s) = (term61 _87477 _87481 x f s)) = (term62 _87477 _87481 x f s).
Proof. exact (@lem3365092 _87481 (term60 _87477 _87481 f x s) (term61 _87477 _87481 x f s)). Qed.
Lemma lem3365103 {A B : Type'} (s : A -> Prop) (f : A -> B) : (@IMAGE A B f s) = (term22 A B s f).
Proof. exact (EQ_MP (@lem3364969 A B s f) (@lem3364968 A B s f)). Qed.
Lemma lem3365104 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f s) = (term22 _87477 _87481 s f).
Proof. exact (@lem3365103 _87477 _87481 s f). Qed.
Lemma lem3365105 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term60 _87477 _87481 f x s) = (term63 _87477 _87481 x s f).
Proof. exact (@lem3365104 _87477 _87481 (@INSERT _87477 x s) f). Qed.
Lemma lem3365117 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term9 A x y s) = (term10 A y x s).
Proof. exact (EQ_MP (@lem3364920 A y x s) (@lem3364919 A y x s)). Qed.
Lemma lem3365118 {_87477 : Type'} (y : _87477) (x : _87477) (s : _87477 -> Prop) : (term9 _87477 x y s) = (term10 _87477 y x s).
Proof. exact (@lem3365117 _87477 y x s). Qed.
Lemma lem3365119 {_87477 : Type'} (x : _87477) (x' : _87477) (s : _87477 -> Prop) : (term9 _87477 x' x s) = (term10 _87477 x x' s).
Proof. exact (@lem3365118 _87477 x x' s). Qed.
Lemma lem3365126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3365127 {_87477 : Type'} (x : _87477) (x' : _87477) (s : _87477 -> Prop) : (term64 _87477 x' x s) = (term65 _87477 x x' s).
Proof. exact (MK_COMB (@lem3365126) (@lem3365119 _87477 x x' s)). Qed.
Lemma lem3365132 {_87477 _87481 : Type'} (y : _87481) (f : _87477 -> _87481) (x' : _87477) : (y = (f x')) = (y = (f x')).
Proof. exact (eq_refl (y = (f x'))). Qed.
Lemma lem3365133 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (y : _87481) (f : _87477 -> _87481) (x' : _87477) : (term66 _87477 _87481 x s y f x') = (term67 _87477 _87481 x s y f x').
Proof. exact (MK_COMB (@lem3365127 _87477 x x' s) (@lem3365132 _87477 _87481 y f x')). Qed.
Lemma lem3365136 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (y : _87481) (f : _87477 -> _87481) : (term68 _87477 _87481 x s y f) = (term69 _87477 _87481 x s y f).
Proof. exact (fun_ext (fun x' : _87477 => @lem3365133 _87477 _87481 x s y f x')). Qed.
Lemma lem3365137 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365138 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (y : _87481) (f : _87477 -> _87481) : (term70 _87477 _87481 x s y f) = (term71 _87477 _87481 x s y f).
Proof. exact (MK_COMB (@lem3365137 _87477) (@lem3365136 _87477 _87481 x s y f)). Qed.
Lemma lem3365143 {_87481 : Type'} (GEN_PVAR_7 : _87481) : (@SETSPEC _87481 GEN_PVAR_7) = (@SETSPEC _87481 GEN_PVAR_7).
Proof. exact (eq_refl (@SETSPEC _87481 GEN_PVAR_7)). Qed.
Lemma lem3365144 {_87477 _87481 : Type'} (GEN_PVAR_7 : _87481) (x : _87477) (s : _87477 -> Prop) (y : _87481) (f : _87477 -> _87481) : (term72 _87477 _87481 GEN_PVAR_7 x s y f) = (term73 _87477 _87481 GEN_PVAR_7 x s y f).
Proof. exact (MK_COMB (@lem3365143 _87481 GEN_PVAR_7) (@lem3365138 _87477 _87481 x s y f)). Qed.
Lemma lem3365145 {_87481 : Type'} (y : _87481) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3365146 {_87477 _87481 : Type'} (GEN_PVAR_7 : _87481) (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (y : _87481) : (term74 _87477 _87481 GEN_PVAR_7 x s f y) = (term75 _87477 _87481 GEN_PVAR_7 x s f y).
Proof. exact (MK_COMB (@lem3365144 _87477 _87481 GEN_PVAR_7 x s y f) (@lem3365145 _87481 y)). Qed.
Lemma lem3365147 {_87477 _87481 : Type'} (GEN_PVAR_7 : _87481) (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term76 _87477 _87481 GEN_PVAR_7 x s f) = (term77 _87477 _87481 GEN_PVAR_7 x s f).
Proof. exact (fun_ext (fun y : _87481 => @lem3365146 _87477 _87481 GEN_PVAR_7 x s f y)). Qed.
Lemma lem3365148 {_87481 : Type'} : (@ex _87481) = (@ex _87481).
Proof. exact (eq_refl (@ex _87481)). Qed.
Lemma lem3365149 {_87477 _87481 : Type'} (GEN_PVAR_7 : _87481) (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term78 _87477 _87481 GEN_PVAR_7 x s f) = (term79 _87477 _87481 GEN_PVAR_7 x s f).
Proof. exact (MK_COMB (@lem3365148 _87481) (@lem3365147 _87477 _87481 GEN_PVAR_7 x s f)). Qed.
Lemma lem3365154 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term80 _87477 _87481 x s f) = (term81 _87477 _87481 x s f).
Proof. exact (fun_ext (fun GEN_PVAR_7 : _87481 => @lem3365149 _87477 _87481 GEN_PVAR_7 x s f)). Qed.
Lemma lem3365155 {_87481 : Type'} : (@GSPEC _87481) = (@GSPEC _87481).
Proof. exact (eq_refl (@GSPEC _87481)). Qed.
Lemma lem3365156 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term63 _87477 _87481 x s f) = (term82 _87477 _87481 x s f).
Proof. exact (MK_COMB (@lem3365155 _87481) (@lem3365154 _87477 _87481 x s f)). Qed.
Lemma lem3365157 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term60 _87477 _87481 f x s) = (term82 _87477 _87481 x s f).
Proof. exact (TRANS (@lem3365105 _87477 _87481 x s f) (@lem3365156 _87477 _87481 x s f)). Qed.
Lemma lem3365158 {_87481 : Type'} (x : _87481) : (@IN _87481 x) = (@IN _87481 x).
Proof. exact (eq_refl (@IN _87481 x)). Qed.
Lemma lem3365159 {_87477 _87481 : Type'} (x : _87481) (x' : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term83 _87477 _87481 x f x' s) = (term84 _87477 _87481 x x' s f).
Proof. exact (MK_COMB (@lem3365158 _87481 x) (@lem3365157 _87477 _87481 x' s f)). Qed.
Lemma lem3365161 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term18 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3364956 _83095 p x) (@lem3364955 _83095 p x)). Qed.
Lemma lem3365162 {_87481 : Type'} (p : _87481 -> Prop) (x : _87481) : (term18 _87481 x p) = (p x).
Proof. exact (@lem3365161 _87481 p x). Qed.
Lemma lem3365163 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (x' : _87481) : (term85 _87477 _87481 x' x s f) = (term86 _87477 _87481 x s f x').
Proof. exact (@lem3365162 _87481 (term87 _87477 _87481 x s f) x'). Qed.
Lemma lem3365164 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (y : _87481) (f : _87477 -> _87481) : (term86 _87477 _87481 x s f y) = (term71 _87477 _87481 x s y f).
Proof. exact (eq_refl (term86 _87477 _87481 x s f y)). Qed.
Lemma lem3365165 {_87481 : Type'} (GEN_PVAR_7 : _87481) : (@SETSPEC _87481 GEN_PVAR_7) = (@SETSPEC _87481 GEN_PVAR_7).
Proof. exact (eq_refl (@SETSPEC _87481 GEN_PVAR_7)). Qed.
Lemma lem3365166 {_87477 _87481 : Type'} (GEN_PVAR_7 : _87481) (x : _87477) (s : _87477 -> Prop) (y : _87481) (f : _87477 -> _87481) : (term88 _87477 _87481 GEN_PVAR_7 x s f y) = (term73 _87477 _87481 GEN_PVAR_7 x s y f).
Proof. exact (MK_COMB (@lem3365165 _87481 GEN_PVAR_7) (@lem3365164 _87477 _87481 x s y f)). Qed.
Lemma lem3365167 {_87481 : Type'} (y : _87481) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3365168 {_87477 _87481 : Type'} (GEN_PVAR_7 : _87481) (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (y : _87481) : (term89 _87477 _87481 GEN_PVAR_7 x s f y) = (term75 _87477 _87481 GEN_PVAR_7 x s f y).
Proof. exact (MK_COMB (@lem3365166 _87477 _87481 GEN_PVAR_7 x s y f) (@lem3365167 _87481 y)). Qed.
Lemma lem3365169 {_87477 _87481 : Type'} (GEN_PVAR_7 : _87481) (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term90 _87477 _87481 GEN_PVAR_7 x s f) = (term77 _87477 _87481 GEN_PVAR_7 x s f).
Proof. exact (fun_ext (fun y : _87481 => @lem3365168 _87477 _87481 GEN_PVAR_7 x s f y)). Qed.
Lemma lem3365170 {_87481 : Type'} : (@ex _87481) = (@ex _87481).
Proof. exact (eq_refl (@ex _87481)). Qed.
Lemma lem3365171 {_87477 _87481 : Type'} (GEN_PVAR_7 : _87481) (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term91 _87477 _87481 GEN_PVAR_7 x s f) = (term79 _87477 _87481 GEN_PVAR_7 x s f).
Proof. exact (MK_COMB (@lem3365170 _87481) (@lem3365169 _87477 _87481 GEN_PVAR_7 x s f)). Qed.
Lemma lem3365172 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term92 _87477 _87481 x s f) = (term81 _87477 _87481 x s f).
Proof. exact (fun_ext (fun GEN_PVAR_7 : _87481 => @lem3365171 _87477 _87481 GEN_PVAR_7 x s f)). Qed.
Lemma lem3365173 {_87481 : Type'} : (@GSPEC _87481) = (@GSPEC _87481).
Proof. exact (eq_refl (@GSPEC _87481)). Qed.
Lemma lem3365174 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term93 _87477 _87481 x s f) = (term82 _87477 _87481 x s f).
Proof. exact (MK_COMB (@lem3365173 _87481) (@lem3365172 _87477 _87481 x s f)). Qed.
Lemma lem3365175 {_87481 : Type'} (x : _87481) : (@IN _87481 x) = (@IN _87481 x).
Proof. exact (eq_refl (@IN _87481 x)). Qed.
Lemma lem3365176 {_87477 _87481 : Type'} (x : _87481) (x' : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term85 _87477 _87481 x x' s f) = (term84 _87477 _87481 x x' s f).
Proof. exact (MK_COMB (@lem3365175 _87481 x) (@lem3365174 _87477 _87481 x' s f)). Qed.
Lemma lem3365177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3365178 {_87477 _87481 : Type'} (x : _87481) (x' : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term94 _87477 _87481 x x' s f) = (term95 _87477 _87481 x x' s f).
Proof. exact (MK_COMB (@lem3365177) (@lem3365176 _87477 _87481 x x' s f)). Qed.
Lemma lem3365179 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term86 _87477 _87481 x s f x') = (term71 _87477 _87481 x s x' f).
Proof. exact (eq_refl (term86 _87477 _87481 x s f x')). Qed.
Lemma lem3365180 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : ((term85 _87477 _87481 x' x s f) = (term86 _87477 _87481 x s f x')) = ((term84 _87477 _87481 x' x s f) = (term71 _87477 _87481 x s x' f)).
Proof. exact (MK_COMB (@lem3365178 _87477 _87481 x' x s f) (@lem3365179 _87477 _87481 x s x' f)). Qed.
Lemma lem3365181 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term84 _87477 _87481 x' x s f) = (term71 _87477 _87481 x s x' f).
Proof. exact (EQ_MP (@lem3365180 _87477 _87481 x s x' f) (@lem3365163 _87477 _87481 x s f x')). Qed.
Lemma lem3365198 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term83 _87477 _87481 x' f x s) = (term71 _87477 _87481 x s x' f).
Proof. exact (TRANS (@lem3365159 _87477 _87481 x' x s f) (@lem3365181 _87477 _87481 x s x' f)). Qed.
Lemma lem3365199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3365200 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term96 _87477 _87481 x' f x s) = (term97 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365199) (@lem3365198 _87477 _87481 x s x' f)). Qed.
Lemma lem3365202 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term9 A x y s) = (term10 A y x s).
Proof. exact (EQ_MP (@lem3364920 A y x s) (@lem3364919 A y x s)). Qed.
Lemma lem3365203 {_87481 : Type'} (y : _87481) (x : _87481) (s : _87481 -> Prop) : (term9 _87481 x y s) = (term10 _87481 y x s).
Proof. exact (@lem3365202 _87481 y x s). Qed.
Lemma lem3365204 {_87477 _87481 : Type'} (x : _87477) (x' : _87481) (f : _87477 -> _87481) (s : _87477 -> Prop) : (term98 _87477 _87481 x' x f s) = (term99 _87477 _87481 x x' f s).
Proof. exact (@lem3365203 _87481 (f x) x' (@IMAGE _87477 _87481 f s)). Qed.
Lemma lem3365212 {A B : Type'} (s : A -> Prop) (f : A -> B) : (@IMAGE A B f s) = (term22 A B s f).
Proof. exact (EQ_MP (@lem3364969 A B s f) (@lem3364968 A B s f)). Qed.
Lemma lem3365213 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f s) = (term22 _87477 _87481 s f).
Proof. exact (@lem3365212 _87477 _87481 s f). Qed.
Lemma lem3365228 {_87481 : Type'} (x : _87481) : (@IN _87481 x) = (@IN _87481 x).
Proof. exact (eq_refl (@IN _87481 x)). Qed.
Lemma lem3365229 {_87477 _87481 : Type'} (x : _87481) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term100 _87477 _87481 x f s) = (term101 _87477 _87481 x s f).
Proof. exact (MK_COMB (@lem3365228 _87481 x) (@lem3365213 _87477 _87481 s f)). Qed.
Lemma lem3365231 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term18 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3364956 _83095 p x) (@lem3364955 _83095 p x)). Qed.
Lemma lem3365232 {_87481 : Type'} (p : _87481 -> Prop) (x : _87481) : (term18 _87481 x p) = (p x).
Proof. exact (@lem3365231 _87481 p x). Qed.
Lemma lem3365233 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) (x : _87481) : (term102 _87477 _87481 x s f) = (term103 _87477 _87481 s f x).
Proof. exact (@lem3365232 _87481 (term104 _87477 _87481 s f) x). Qed.
Lemma lem3365234 {_87477 _87481 : Type'} (s : _87477 -> Prop) (y : _87481) (f : _87477 -> _87481) : (term103 _87477 _87481 s f y) = (term105 _87477 _87481 s y f).
Proof. exact (eq_refl (term103 _87477 _87481 s f y)). Qed.
Lemma lem3365235 {_87481 : Type'} (GEN_PVAR_7 : _87481) : (@SETSPEC _87481 GEN_PVAR_7) = (@SETSPEC _87481 GEN_PVAR_7).
Proof. exact (eq_refl (@SETSPEC _87481 GEN_PVAR_7)). Qed.
Lemma lem3365236 {_87477 _87481 : Type'} (GEN_PVAR_7 : _87481) (s : _87477 -> Prop) (y : _87481) (f : _87477 -> _87481) : (term106 _87477 _87481 GEN_PVAR_7 s f y) = (term107 _87477 _87481 GEN_PVAR_7 s y f).
Proof. exact (MK_COMB (@lem3365235 _87481 GEN_PVAR_7) (@lem3365234 _87477 _87481 s y f)). Qed.
Lemma lem3365237 {_87481 : Type'} (y : _87481) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3365238 {_87477 _87481 : Type'} (GEN_PVAR_7 : _87481) (s : _87477 -> Prop) (f : _87477 -> _87481) (y : _87481) : (term108 _87477 _87481 GEN_PVAR_7 s f y) = (term109 _87477 _87481 GEN_PVAR_7 s f y).
Proof. exact (MK_COMB (@lem3365236 _87477 _87481 GEN_PVAR_7 s y f) (@lem3365237 _87481 y)). Qed.
Lemma lem3365239 {_87477 _87481 : Type'} (GEN_PVAR_7 : _87481) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term110 _87477 _87481 GEN_PVAR_7 s f) = (term111 _87477 _87481 GEN_PVAR_7 s f).
Proof. exact (fun_ext (fun y : _87481 => @lem3365238 _87477 _87481 GEN_PVAR_7 s f y)). Qed.
Lemma lem3365240 {_87481 : Type'} : (@ex _87481) = (@ex _87481).
Proof. exact (eq_refl (@ex _87481)). Qed.
Lemma lem3365241 {_87477 _87481 : Type'} (GEN_PVAR_7 : _87481) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term112 _87477 _87481 GEN_PVAR_7 s f) = (term113 _87477 _87481 GEN_PVAR_7 s f).
Proof. exact (MK_COMB (@lem3365240 _87481) (@lem3365239 _87477 _87481 GEN_PVAR_7 s f)). Qed.
Lemma lem3365242 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) : (term114 _87477 _87481 s f) = (term115 _87477 _87481 s f).
Proof. exact (fun_ext (fun GEN_PVAR_7 : _87481 => @lem3365241 _87477 _87481 GEN_PVAR_7 s f)). Qed.
Lemma lem3365243 {_87481 : Type'} : (@GSPEC _87481) = (@GSPEC _87481).
Proof. exact (eq_refl (@GSPEC _87481)). Qed.
Lemma lem3365244 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) : (term116 _87477 _87481 s f) = (term22 _87477 _87481 s f).
Proof. exact (MK_COMB (@lem3365243 _87481) (@lem3365242 _87477 _87481 s f)). Qed.
Lemma lem3365245 {_87481 : Type'} (x : _87481) : (@IN _87481 x) = (@IN _87481 x).
Proof. exact (eq_refl (@IN _87481 x)). Qed.
Lemma lem3365246 {_87477 _87481 : Type'} (x : _87481) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term102 _87477 _87481 x s f) = (term101 _87477 _87481 x s f).
Proof. exact (MK_COMB (@lem3365245 _87481 x) (@lem3365244 _87477 _87481 s f)). Qed.
Lemma lem3365247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3365248 {_87477 _87481 : Type'} (x : _87481) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term117 _87477 _87481 x s f) = (term118 _87477 _87481 x s f).
Proof. exact (MK_COMB (@lem3365247) (@lem3365246 _87477 _87481 x s f)). Qed.
Lemma lem3365249 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x : _87481) (f : _87477 -> _87481) : (term103 _87477 _87481 s f x) = (term105 _87477 _87481 s x f).
Proof. exact (eq_refl (term103 _87477 _87481 s f x)). Qed.
Lemma lem3365250 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x : _87481) (f : _87477 -> _87481) : ((term102 _87477 _87481 x s f) = (term103 _87477 _87481 s f x)) = ((term101 _87477 _87481 x s f) = (term105 _87477 _87481 s x f)).
Proof. exact (MK_COMB (@lem3365248 _87477 _87481 x s f) (@lem3365249 _87477 _87481 s x f)). Qed.
Lemma lem3365251 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x : _87481) (f : _87477 -> _87481) : (term101 _87477 _87481 x s f) = (term105 _87477 _87481 s x f).
Proof. exact (EQ_MP (@lem3365250 _87477 _87481 s x f) (@lem3365233 _87477 _87481 s f x)). Qed.
Lemma lem3365262 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x : _87481) (f : _87477 -> _87481) : (term100 _87477 _87481 x f s) = (term105 _87477 _87481 s x f).
Proof. exact (TRANS (@lem3365229 _87477 _87481 x s f) (@lem3365251 _87477 _87481 s x f)). Qed.
Lemma lem3365263 {_87477 _87481 : Type'} (x : _87481) (f : _87477 -> _87481) (x' : _87477) : (term119 _87477 _87481 x f x') = (term119 _87477 _87481 x f x').
Proof. exact (eq_refl (term119 _87477 _87481 x f x')). Qed.
Lemma lem3365264 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term99 _87477 _87481 x x' f s) = (term120 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365263 _87477 _87481 x' f x) (@lem3365262 _87477 _87481 s x' f)). Qed.
Lemma lem3365267 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term98 _87477 _87481 x' x f s) = (term120 _87477 _87481 x s x' f).
Proof. exact (TRANS (@lem3365204 _87477 _87481 x x' f s) (@lem3365264 _87477 _87481 x s x' f)). Qed.
Lemma lem3365268 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : ((term83 _87477 _87481 x' f x s) = (term98 _87477 _87481 x' x f s)) = ((term71 _87477 _87481 x s x' f) = (term120 _87477 _87481 x s x' f)).
Proof. exact (MK_COMB (@lem3365200 _87477 _87481 x s x' f) (@lem3365267 _87477 _87481 x s x' f)). Qed.
Lemma lem3365273 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term121 _87477 _87481 x f s) = (term122 _87477 _87481 x s f).
Proof. exact (fun_ext (fun x' : _87481 => @lem3365268 _87477 _87481 x s x' f)). Qed.
Lemma lem3365274 {_87481 : Type'} : (@all _87481) = (@all _87481).
Proof. exact (eq_refl (@all _87481)). Qed.
Lemma lem3365275 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term62 _87477 _87481 x f s) = (term123 _87477 _87481 x s f).
Proof. exact (MK_COMB (@lem3365274 _87481) (@lem3365273 _87477 _87481 x s f)). Qed.
Lemma lem3365280 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : ((term60 _87477 _87481 f x s) = (term61 _87477 _87481 x f s)) = (term123 _87477 _87481 x s f).
Proof. exact (TRANS (@lem3365093 _87477 _87481 x f s) (@lem3365275 _87477 _87481 x s f)). Qed.
Lemma lem3365281 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term124 _87477 _87481 x f s) = (term125 _87477 _87481 x s f).
Proof. exact (MK_COMB (@lem3365087 _87477 _87481 f) (@lem3365280 _87477 _87481 x s f)). Qed.
Lemma lem3365283 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3365284 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term125 _87477 _87481 x s f) = (term123 _87477 _87481 x s f).
Proof. exact (@lem3365283 (term123 _87477 _87481 x s f)). Qed.
Lemma lem3365325 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term124 _87477 _87481 x f s) = (term123 _87477 _87481 x s f).
Proof. exact (TRANS (@lem3365281 _87477 _87481 x s f) (@lem3365284 _87477 _87481 x s f)). Qed.
Lemma lem3365326 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (s : _87477 -> Prop) : (term123 _87477 _87481 x s f) = (term124 _87477 _87481 x f s).
Proof. exact (SYM (@lem3365325 _87477 _87481 x s f)). Qed.
Lemma lem3365328 (p : Prop) : p = (term126 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3365329 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term123 _87477 _87481 x s f) = (term127 _87477 _87481 x s f).
Proof. exact (@lem3365328 (term123 _87477 _87481 x s f)). Qed.
Lemma lem3365330 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term127 _87477 _87481 x s f) = (term123 _87477 _87481 x s f).
Proof. exact (SYM (@lem3365329 _87477 _87481 x s f)). Qed.
Lemma lem3365331 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (h1 : term128 _87477 _87481 x s f) : term128 _87477 _87481 x s f.
Proof. exact (h1). Qed.
Lemma lem3365334 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (h1 : term127 _87477 _87481 x s f) : term127 _87477 _87481 x s f.
Proof. exact (h1). Qed.
Lemma lem3365335 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : term129 _87477 _87481 x s f.
Proof. exact (fun h0 : term127 _87477 _87481 x s f => @lem3365334 _87477 _87481 x s f h0). Qed.
Lemma lem3365336 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (h1 : term129 _87477 _87481 x s f) : term129 _87477 _87481 x s f.
Proof. exact (h1). Qed.
Lemma lem3365337 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (h1 : term127 _87477 _87481 x s f) : term127 _87477 _87481 x s f.
Proof. exact (h1). Qed.
Lemma lem3365338 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (h1 : term127 _87477 _87481 x s f) (h2 : term129 _87477 _87481 x s f) : term127 _87477 _87481 x s f.
Proof. exact (@lem3365336 _87477 _87481 x s f h2 (@lem3365337 _87477 _87481 x s f h1)). Qed.
Lemma lem3365339 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (h1 : term127 _87477 _87481 x s f) : term130 _87477 _87481 x s f.
Proof. exact (fun h0 : term129 _87477 _87481 x s f => @lem3365338 _87477 _87481 x s f h1 h0). Qed.
Lemma lem3365340 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (h1 : term129 _87477 _87481 x s f) : term129 _87477 _87481 x s f.
Proof. exact (h1). Qed.
Lemma lem3365341 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (h1 : term127 _87477 _87481 x s f) (h2 : term129 _87477 _87481 x s f) : term127 _87477 _87481 x s f.
Proof. exact (@lem3365339 _87477 _87481 x s f h1 (@lem3365340 _87477 _87481 x s f h2)). Qed.
Lemma lem3365342 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (h1 : term129 _87477 _87481 x s f) : term129 _87477 _87481 x s f.
Proof. exact (fun h0 : term127 _87477 _87481 x s f => @lem3365341 _87477 _87481 x s f h0 h1). Qed.
Lemma lem3365343 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : term131 _87477 _87481 x s f.
Proof. exact (fun h0 : term129 _87477 _87481 x s f => @lem3365342 _87477 _87481 x s f h0). Qed.
Lemma lem3365346 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : term129 _87477 _87481 x s f.
Proof. exact (@lem3365343 _87477 _87481 x s f (@lem3365335 _87477 _87481 x s f)). Qed.
Lemma lem3365347 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : term129 _87477 _87481 x s f.
Proof. exact (@lem3365346 _87477 _87481 x s f). Qed.
Lemma lem3365361 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3365362 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term127 _87477 _87481 x s f) = (term132 _87477 _87481 x s f).
Proof. exact (@lem3365361 (term128 _87477 _87481 x s f)). Qed.
Lemma lem3365364 (t : Prop) : (term133 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3365365 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term132 _87477 _87481 x s f) = (term123 _87477 _87481 x s f).
Proof. exact (@lem3365364 (term123 _87477 _87481 x s f)). Qed.
Lemma lem3365370 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term127 _87477 _87481 x s f) = (term123 _87477 _87481 x s f).
Proof. exact (TRANS (@lem3365362 _87477 _87481 x s f) (@lem3365365 _87477 _87481 x s f)). Qed.
Lemma lem3365475 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) : (term134 _87477 _87481 s f) = (term135 _87477 _87481 s f).
Proof. exact (fun_ext (fun x : _87477 => @lem3365370 _87477 _87481 x s f)). Qed.
Lemma lem3365476 {_87477 : Type'} : (@all _87477) = (@all _87477).
Proof. exact (eq_refl (@all _87477)). Qed.
Lemma lem3365477 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) : (term136 _87477 _87481 s f) = (term137 _87477 _87481 s f).
Proof. exact (MK_COMB (@lem3365476 _87477) (@lem3365475 _87477 _87481 s f)). Qed.
Lemma lem3365482 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (term138 _87477 _87481 f) = (term139 _87477 _87481 f).
Proof. exact (fun_ext (fun s : _87477 -> Prop => @lem3365477 _87477 _87481 s f)). Qed.
Lemma lem3365483 {_87477 : Type'} : (@all (_87477 -> Prop)) = (@all (_87477 -> Prop)).
Proof. exact (eq_refl (@all (_87477 -> Prop))). Qed.
Lemma lem3365484 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (term140 _87477 _87481 f) = (term141 _87477 _87481 f).
Proof. exact (MK_COMB (@lem3365483 _87477) (@lem3365482 _87477 _87481 f)). Qed.
Lemma lem3365489 {_87477 _87481 : Type'} : (term142 _87477 _87481) = (term143 _87477 _87481).
Proof. exact (fun_ext (fun f : _87477 -> _87481 => @lem3365484 _87477 _87481 f)). Qed.
Lemma lem3365490 {_87477 _87481 : Type'} : (@all (_87477 -> _87481)) = (@all (_87477 -> _87481)).
Proof. exact (eq_refl (@all (_87477 -> _87481))). Qed.
Lemma lem3365499 {_87477 _87481 : Type'} : (term144 _87477 _87481) = (term145 _87477 _87481).
Proof. exact (MK_COMB (@lem3365490 _87477 _87481) (@lem3365489 _87477 _87481)). Qed.
Lemma lem3365504 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x : _87481) (f : _87477 -> _87481) (x' : _87477) : (term146 _87477 _87481 s x f x') = (term146 _87477 _87481 s x f x').
Proof. exact (eq_refl (term146 _87477 _87481 s x f x')). Qed.
Lemma lem3365505 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x : _87481) (f : _87477 -> _87481) : (term147 _87477 _87481 s x f) = (term147 _87477 _87481 s x f).
Proof. exact (fun_ext (fun x' : _87477 => @lem3365504 _87477 _87481 s x f x')). Qed.
Lemma lem3365506 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365507 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x : _87481) (f : _87477 -> _87481) : (term105 _87477 _87481 s x f) = (term105 _87477 _87481 s x f).
Proof. exact (MK_COMB (@lem3365506 _87477) (@lem3365505 _87477 _87481 s x f)). Qed.
Lemma lem3365510 {_87477 _87481 : Type'} (x : _87481) (f : _87477 -> _87481) (x' : _87477) : (term119 _87477 _87481 x f x') = (term119 _87477 _87481 x f x').
Proof. exact (eq_refl (term119 _87477 _87481 x f x')). Qed.
Lemma lem3365511 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term120 _87477 _87481 x s x' f) = (term120 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365510 _87477 _87481 x' f x) (@lem3365507 _87477 _87481 s x' f)). Qed.
Lemma lem3365520 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term67 _87477 _87481 x s x' f x'') = (term67 _87477 _87481 x s x' f x'').
Proof. exact (eq_refl (term67 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365521 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term69 _87477 _87481 x s x' f) = (term69 _87477 _87481 x s x' f).
Proof. exact (fun_ext (fun x'' : _87477 => @lem3365520 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365522 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365523 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term71 _87477 _87481 x s x' f) = (term71 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365522 _87477) (@lem3365521 _87477 _87481 x s x' f)). Qed.
Lemma lem3365524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3365525 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term97 _87477 _87481 x s x' f) = (term97 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365524) (@lem3365523 _87477 _87481 x s x' f)). Qed.
Lemma lem3365526 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : ((term71 _87477 _87481 x s x' f) = (term120 _87477 _87481 x s x' f)) = ((term71 _87477 _87481 x s x' f) = (term120 _87477 _87481 x s x' f)).
Proof. exact (MK_COMB (@lem3365525 _87477 _87481 x s x' f) (@lem3365511 _87477 _87481 x s x' f)). Qed.
Lemma lem3365527 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term122 _87477 _87481 x s f) = (term122 _87477 _87481 x s f).
Proof. exact (fun_ext (fun x' : _87481 => @lem3365526 _87477 _87481 x s x' f)). Qed.
Lemma lem3365528 {_87481 : Type'} : (@all _87481) = (@all _87481).
Proof. exact (eq_refl (@all _87481)). Qed.
Lemma lem3365529 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term123 _87477 _87481 x s f) = (term123 _87477 _87481 x s f).
Proof. exact (MK_COMB (@lem3365528 _87481) (@lem3365527 _87477 _87481 x s f)). Qed.
Lemma lem3365530 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) : (term135 _87477 _87481 s f) = (term135 _87477 _87481 s f).
Proof. exact (fun_ext (fun x : _87477 => @lem3365529 _87477 _87481 x s f)). Qed.
Lemma lem3365531 {_87477 : Type'} : (@all _87477) = (@all _87477).
Proof. exact (eq_refl (@all _87477)). Qed.
Lemma lem3365532 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) : (term137 _87477 _87481 s f) = (term137 _87477 _87481 s f).
Proof. exact (MK_COMB (@lem3365531 _87477) (@lem3365530 _87477 _87481 s f)). Qed.
Lemma lem3365533 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (term139 _87477 _87481 f) = (term139 _87477 _87481 f).
Proof. exact (fun_ext (fun s : _87477 -> Prop => @lem3365532 _87477 _87481 s f)). Qed.
Lemma lem3365534 {_87477 : Type'} : (@all (_87477 -> Prop)) = (@all (_87477 -> Prop)).
Proof. exact (eq_refl (@all (_87477 -> Prop))). Qed.
Lemma lem3365535 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (term141 _87477 _87481 f) = (term141 _87477 _87481 f).
Proof. exact (MK_COMB (@lem3365534 _87477) (@lem3365533 _87477 _87481 f)). Qed.
Lemma lem3365536 {_87477 _87481 : Type'} : (term143 _87477 _87481) = (term143 _87477 _87481).
Proof. exact (fun_ext (fun f : _87477 -> _87481 => @lem3365535 _87477 _87481 f)). Qed.
Lemma lem3365537 {_87477 _87481 : Type'} : (@all (_87477 -> _87481)) = (@all (_87477 -> _87481)).
Proof. exact (eq_refl (@all (_87477 -> _87481))). Qed.
Lemma lem3365538 {_87477 _87481 : Type'} : (term145 _87477 _87481) = (term145 _87477 _87481).
Proof. exact (MK_COMB (@lem3365537 _87477 _87481) (@lem3365536 _87477 _87481)). Qed.
Lemma lem3365585 {_87477 _87481 : Type'} : (term144 _87477 _87481) = (term145 _87477 _87481).
Proof. exact (TRANS (@lem3365499 _87477 _87481) (@lem3365538 _87477 _87481)). Qed.
Lemma lem3365586 {_87477 _87481 : Type'} : (term145 _87477 _87481) = (term144 _87477 _87481).
Proof. exact (SYM (@lem3365585 _87477 _87481)). Qed.
Lemma lem3365588 (p : Prop) : p = (term126 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3365589 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : ((term71 _87477 _87481 x s x' f) = (term120 _87477 _87481 x s x' f)) = (term148 _87477 _87481 x s x' f).
Proof. exact (@lem3365588 ((term71 _87477 _87481 x s x' f) = (term120 _87477 _87481 x s x' f))). Qed.
Lemma lem3365590 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term148 _87477 _87481 x s x' f) = ((term71 _87477 _87481 x s x' f) = (term120 _87477 _87481 x s x' f)).
Proof. exact (SYM (@lem3365589 _87477 _87481 x s x' f)). Qed.
Lemma lem3365591 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term149 _87477 _87481 x s x' f) : term149 _87477 _87481 x s x' f.
Proof. exact (h1). Qed.
Lemma lem3365600 {_87477 : Type'} (x : _87477) (x' : _87477) (s : _87477 -> Prop) : (term150 _87477 x x' s) = (term151 _87477 x x' s).
Proof. exact (@lem17160 (x' = x) (@IN _87477 x' s)). Qed.
Lemma lem3365604 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term152 _87477 _87481 x' f x'') = (term152 _87477 _87481 x' f x'').
Proof. exact (eq_refl (term152 _87477 _87481 x' f x'')). Qed.
Lemma lem3365606 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3365607 {_87477 : Type'} (x : _87477) (x' : _87477) (s : _87477 -> Prop) : (term153 _87477 x x' s) = (term154 _87477 x x' s).
Proof. exact (MK_COMB (@lem3365606) (@lem3365600 _87477 x x' s)). Qed.
Lemma lem3365608 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term155 _87477 _87481 x s x' f x'') = (term156 _87477 _87481 x s x' f x'').
Proof. exact (MK_COMB (@lem3365607 _87477 x x'' s) (@lem3365604 _87477 _87481 x' f x'')). Qed.
Lemma lem3365609 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term157 _87477 _87481 x s x' f x'') = (term155 _87477 _87481 x s x' f x'').
Proof. exact (@lem17045 (term10 _87477 x x'' s) (x' = (f x''))). Qed.
Lemma lem3365610 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term157 _87477 _87481 x s x' f x'') = (term156 _87477 _87481 x s x' f x'').
Proof. exact (TRANS (@lem3365609 _87477 _87481 x s x' f x'') (@lem3365608 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365613 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term67 _87477 _87481 x s x' f x'') = (term67 _87477 _87481 x s x' f x'').
Proof. exact (eq_refl (term67 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365614 {_87477 : Type'} (P : _87477 -> Prop) : (term158 _87477 P) = (term159 _87477 P).
Proof. exact (@lem18394 _87477 P). Qed.
Lemma lem3365615 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term160 _87477 _87481 x s x' f) = (term161 _87477 _87481 x s x' f).
Proof. exact (@lem3365614 _87477 (term69 _87477 _87481 x s x' f)). Qed.
Lemma lem3365616 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term162 _87477 _87481 x s x' f x'') = (term67 _87477 _87481 x s x' f x'').
Proof. exact (eq_refl (term162 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365617 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3365618 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term163 _87477 _87481 x s x' f x'') = (term157 _87477 _87481 x s x' f x'').
Proof. exact (MK_COMB (@lem3365617) (@lem3365616 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365619 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term163 _87477 _87481 x s x' f x'') = (term156 _87477 _87481 x s x' f x'').
Proof. exact (TRANS (@lem3365618 _87477 _87481 x s x' f x'') (@lem3365610 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365620 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term164 _87477 _87481 x s x' f) = (term165 _87477 _87481 x s x' f).
Proof. exact (fun_ext (fun x'' : _87477 => @lem3365619 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365621 {_87477 : Type'} : (@all _87477) = (@all _87477).
Proof. exact (eq_refl (@all _87477)). Qed.
Lemma lem3365622 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term161 _87477 _87481 x s x' f) = (term166 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365621 _87477) (@lem3365620 _87477 _87481 x s x' f)). Qed.
Lemma lem3365623 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term160 _87477 _87481 x s x' f) = (term166 _87477 _87481 x s x' f).
Proof. exact (TRANS (@lem3365615 _87477 _87481 x s x' f) (@lem3365622 _87477 _87481 x s x' f)). Qed.
Lemma lem3365624 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term69 _87477 _87481 x s x' f) = (term69 _87477 _87481 x s x' f).
Proof. exact (fun_ext (fun x'' : _87477 => @lem3365613 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365625 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365626 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term71 _87477 _87481 x s x' f) = (term71 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365625 _87477) (@lem3365624 _87477 _87481 x s x' f)). Qed.
Lemma lem3365637 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term167 _87477 _87481 s x' f x) = (term168 _87477 _87481 s x' f x).
Proof. exact (@lem17045 (@IN _87477 x s) (x' = (f x))). Qed.
Lemma lem3365640 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term146 _87477 _87481 s x' f x) = (term146 _87477 _87481 s x' f x).
Proof. exact (eq_refl (term146 _87477 _87481 s x' f x)). Qed.
Lemma lem3365641 {_87477 : Type'} (P : _87477 -> Prop) : (term158 _87477 P) = (term159 _87477 P).
Proof. exact (@lem18394 _87477 P). Qed.
Lemma lem3365642 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term169 _87477 _87481 s x' f) = (term170 _87477 _87481 s x' f).
Proof. exact (@lem3365641 _87477 (term147 _87477 _87481 s x' f)). Qed.
Lemma lem3365643 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term171 _87477 _87481 s x' f x) = (term146 _87477 _87481 s x' f x).
Proof. exact (eq_refl (term171 _87477 _87481 s x' f x)). Qed.
Lemma lem3365644 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3365645 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term172 _87477 _87481 s x' f x) = (term167 _87477 _87481 s x' f x).
Proof. exact (MK_COMB (@lem3365644) (@lem3365643 _87477 _87481 s x' f x)). Qed.
Lemma lem3365646 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term172 _87477 _87481 s x' f x) = (term168 _87477 _87481 s x' f x).
Proof. exact (TRANS (@lem3365645 _87477 _87481 s x' f x) (@lem3365637 _87477 _87481 s x' f x)). Qed.
Lemma lem3365647 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term173 _87477 _87481 s x' f) = (term174 _87477 _87481 s x' f).
Proof. exact (fun_ext (fun x : _87477 => @lem3365646 _87477 _87481 s x' f x)). Qed.
Lemma lem3365648 {_87477 : Type'} : (@all _87477) = (@all _87477).
Proof. exact (eq_refl (@all _87477)). Qed.
Lemma lem3365649 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term170 _87477 _87481 s x' f) = (term175 _87477 _87481 s x' f).
Proof. exact (MK_COMB (@lem3365648 _87477) (@lem3365647 _87477 _87481 s x' f)). Qed.
Lemma lem3365650 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term169 _87477 _87481 s x' f) = (term175 _87477 _87481 s x' f).
Proof. exact (TRANS (@lem3365642 _87477 _87481 s x' f) (@lem3365649 _87477 _87481 s x' f)). Qed.
Lemma lem3365651 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term147 _87477 _87481 s x' f) = (term147 _87477 _87481 s x' f).
Proof. exact (fun_ext (fun x : _87477 => @lem3365640 _87477 _87481 s x' f x)). Qed.
Lemma lem3365652 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365653 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term105 _87477 _87481 s x' f) = (term105 _87477 _87481 s x' f).
Proof. exact (MK_COMB (@lem3365652 _87477) (@lem3365651 _87477 _87481 s x' f)). Qed.
Lemma lem3365655 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term176 _87477 _87481 x' f x) = (term176 _87477 _87481 x' f x).
Proof. exact (eq_refl (term176 _87477 _87481 x' f x)). Qed.
Lemma lem3365656 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term177 _87477 _87481 x s x' f) = (term178 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365655 _87477 _87481 x' f x) (@lem3365650 _87477 _87481 s x' f)). Qed.
Lemma lem3365657 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term179 _87477 _87481 x s x' f) = (term177 _87477 _87481 x s x' f).
Proof. exact (@lem17160 (x' = (f x)) (term105 _87477 _87481 s x' f)). Qed.
Lemma lem3365658 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term179 _87477 _87481 x s x' f) = (term178 _87477 _87481 x s x' f).
Proof. exact (TRANS (@lem3365657 _87477 _87481 x s x' f) (@lem3365656 _87477 _87481 x s x' f)). Qed.
Lemma lem3365660 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term119 _87477 _87481 x' f x) = (term119 _87477 _87481 x' f x).
Proof. exact (eq_refl (term119 _87477 _87481 x' f x)). Qed.
Lemma lem3365661 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term120 _87477 _87481 x s x' f) = (term120 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365660 _87477 _87481 x' f x) (@lem3365653 _87477 _87481 s x' f)). Qed.
Lemma lem3365662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3365663 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term180 _87477 _87481 x s x' f) = (term181 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365662) (@lem3365623 _87477 _87481 x s x' f)). Qed.
Lemma lem3365664 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term182 _87477 _87481 x s x' f) = (term183 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365663 _87477 _87481 x s x' f) (@lem3365661 _87477 _87481 x s x' f)). Qed.
Lemma lem3365665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3365666 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term184 _87477 _87481 x s x' f) = (term184 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365665) (@lem3365626 _87477 _87481 x s x' f)). Qed.
Lemma lem3365667 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term185 _87477 _87481 x s x' f) = (term186 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365666 _87477 _87481 x s x' f) (@lem3365658 _87477 _87481 x s x' f)). Qed.
Lemma lem3365668 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3365669 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term187 _87477 _87481 x s x' f) = (term188 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365668) (@lem3365667 _87477 _87481 x s x' f)). Qed.
Lemma lem3365670 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term189 _87477 _87481 x s x' f) = (term190 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365669 _87477 _87481 x s x' f) (@lem3365664 _87477 _87481 x s x' f)). Qed.
Lemma lem3365671 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term149 _87477 _87481 x s x' f) = (term189 _87477 _87481 x s x' f).
Proof. exact (@lem17646 (term71 _87477 _87481 x s x' f) (term120 _87477 _87481 x s x' f)). Qed.
Lemma lem3365672 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term149 _87477 _87481 x s x' f) = (term190 _87477 _87481 x s x' f).
Proof. exact (TRANS (@lem3365671 _87477 _87481 x s x' f) (@lem3365670 _87477 _87481 x s x' f)). Qed.
Lemma lem3365867 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3365868 {_87477 : Type'} (P : _87477 -> Prop) (Q : Prop) : (term191 _87477 P Q) = (term192 _87477 P Q).
Proof. exact (@lem3365867 _87477 P Q). Qed.
Lemma lem3365869 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term193 _87477 _87481 x s x' f) = (term194 _87477 _87481 x s x' f).
Proof. exact (@lem3365868 _87477 (term69 _87477 _87481 x s x' f) (term178 _87477 _87481 x s x' f)). Qed.
Lemma lem3365870 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term162 _87477 _87481 x s x' f x'') = (term67 _87477 _87481 x s x' f x'').
Proof. exact (eq_refl (term162 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365871 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term195 _87477 _87481 x s x' f) = (term69 _87477 _87481 x s x' f).
Proof. exact (fun_ext (fun x'' : _87477 => @lem3365870 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365872 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365873 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term196 _87477 _87481 x s x' f) = (term71 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365872 _87477) (@lem3365871 _87477 _87481 x s x' f)). Qed.
Lemma lem3365874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3365875 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term197 _87477 _87481 x s x' f) = (term184 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365874) (@lem3365873 _87477 _87481 x s x' f)). Qed.
Lemma lem3365876 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term178 _87477 _87481 x s x' f) = (term178 _87477 _87481 x s x' f).
Proof. exact (eq_refl (term178 _87477 _87481 x s x' f)). Qed.
Lemma lem3365877 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term193 _87477 _87481 x s x' f) = (term186 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365875 _87477 _87481 x s x' f) (@lem3365876 _87477 _87481 x s x' f)). Qed.
Lemma lem3365878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3365879 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term198 _87477 _87481 x s x' f) = (term199 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365878) (@lem3365877 _87477 _87481 x s x' f)). Qed.
Lemma lem3365880 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term162 _87477 _87481 x s x' f x'') = (term67 _87477 _87481 x s x' f x'').
Proof. exact (eq_refl (term162 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3365882 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term200 _87477 _87481 x s x' f x'') = (term201 _87477 _87481 x s x' f x'').
Proof. exact (MK_COMB (@lem3365881) (@lem3365880 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365883 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term178 _87477 _87481 x s x' f) = (term178 _87477 _87481 x s x' f).
Proof. exact (eq_refl (term178 _87477 _87481 x s x' f)). Qed.
Lemma lem3365884 {_87477 _87481 : Type'} (x' : _87477) (x : _87477) (s : _87477 -> Prop) (x'' : _87481) (f : _87477 -> _87481) : (term202 _87477 _87481 x' x s x'' f) = (term203 _87477 _87481 x' x s x'' f).
Proof. exact (MK_COMB (@lem3365882 _87477 _87481 x s x'' f x') (@lem3365883 _87477 _87481 x s x'' f)). Qed.
Lemma lem3365885 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term204 _87477 _87481 x s x' f) = (term205 _87477 _87481 x s x' f).
Proof. exact (fun_ext (fun x'' : _87477 => @lem3365884 _87477 _87481 x'' x s x' f)). Qed.
Lemma lem3365886 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365887 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term194 _87477 _87481 x s x' f) = (term206 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365886 _87477) (@lem3365885 _87477 _87481 x s x' f)). Qed.
Lemma lem3365888 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : ((term193 _87477 _87481 x s x' f) = (term194 _87477 _87481 x s x' f)) = ((term186 _87477 _87481 x s x' f) = (term206 _87477 _87481 x s x' f)).
Proof. exact (MK_COMB (@lem3365879 _87477 _87481 x s x' f) (@lem3365887 _87477 _87481 x s x' f)). Qed.
Lemma lem3365889 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term186 _87477 _87481 x s x' f) = (term206 _87477 _87481 x s x' f).
Proof. exact (EQ_MP (@lem3365888 _87477 _87481 x s x' f) (@lem3365869 _87477 _87481 x s x' f)). Qed.
Lemma lem3365890 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3365891 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term188 _87477 _87481 x s x' f) = (term207 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365890) (@lem3365889 _87477 _87481 x s x' f)). Qed.
Lemma lem3365893 {A : Type'} (P : Prop) (Q : A -> Prop) : (term208 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3365894 {_87477 : Type'} (P : Prop) (Q : _87477 -> Prop) : (term208 _87477 P Q) = (term209 _87477 P Q).
Proof. exact (@lem3365893 _87477 P Q). Qed.
Lemma lem3365895 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term210 _87477 _87481 x s x' f) = (term211 _87477 _87481 x s x' f).
Proof. exact (@lem3365894 _87477 (x' = (f x)) (term147 _87477 _87481 s x' f)). Qed.
Lemma lem3365896 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term171 _87477 _87481 s x' f x) = (term146 _87477 _87481 s x' f x).
Proof. exact (eq_refl (term171 _87477 _87481 s x' f x)). Qed.
Lemma lem3365897 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term212 _87477 _87481 s x' f) = (term147 _87477 _87481 s x' f).
Proof. exact (fun_ext (fun x : _87477 => @lem3365896 _87477 _87481 s x' f x)). Qed.
Lemma lem3365898 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365899 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term213 _87477 _87481 s x' f) = (term105 _87477 _87481 s x' f).
Proof. exact (MK_COMB (@lem3365898 _87477) (@lem3365897 _87477 _87481 s x' f)). Qed.
Lemma lem3365900 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term119 _87477 _87481 x' f x) = (term119 _87477 _87481 x' f x).
Proof. exact (eq_refl (term119 _87477 _87481 x' f x)). Qed.
Lemma lem3365901 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term210 _87477 _87481 x s x' f) = (term120 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365900 _87477 _87481 x' f x) (@lem3365899 _87477 _87481 s x' f)). Qed.
Lemma lem3365902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3365903 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term214 _87477 _87481 x s x' f) = (term215 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365902) (@lem3365901 _87477 _87481 x s x' f)). Qed.
Lemma lem3365904 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term171 _87477 _87481 s x' f x'') = (term146 _87477 _87481 s x' f x'').
Proof. exact (eq_refl (term171 _87477 _87481 s x' f x'')). Qed.
Lemma lem3365905 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term119 _87477 _87481 x' f x) = (term119 _87477 _87481 x' f x).
Proof. exact (eq_refl (term119 _87477 _87481 x' f x)). Qed.
Lemma lem3365906 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term216 _87477 _87481 x s x' f x'') = (term217 _87477 _87481 x s x' f x'').
Proof. exact (MK_COMB (@lem3365905 _87477 _87481 x' f x) (@lem3365904 _87477 _87481 s x' f x'')). Qed.
Lemma lem3365907 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term218 _87477 _87481 x s x' f) = (term219 _87477 _87481 x s x' f).
Proof. exact (fun_ext (fun x'' : _87477 => @lem3365906 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365908 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365909 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term211 _87477 _87481 x s x' f) = (term220 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365908 _87477) (@lem3365907 _87477 _87481 x s x' f)). Qed.
Lemma lem3365910 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : ((term210 _87477 _87481 x s x' f) = (term211 _87477 _87481 x s x' f)) = ((term120 _87477 _87481 x s x' f) = (term220 _87477 _87481 x s x' f)).
Proof. exact (MK_COMB (@lem3365903 _87477 _87481 x s x' f) (@lem3365909 _87477 _87481 x s x' f)). Qed.
Lemma lem3365911 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term120 _87477 _87481 x s x' f) = (term220 _87477 _87481 x s x' f).
Proof. exact (EQ_MP (@lem3365910 _87477 _87481 x s x' f) (@lem3365895 _87477 _87481 x s x' f)). Qed.
Lemma lem3365912 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term181 _87477 _87481 x s x' f) = (term181 _87477 _87481 x s x' f).
Proof. exact (eq_refl (term181 _87477 _87481 x s x' f)). Qed.
Lemma lem3365913 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term183 _87477 _87481 x s x' f) = (term221 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365912 _87477 _87481 x s x' f) (@lem3365911 _87477 _87481 x s x' f)). Qed.
Lemma lem3365915 {A : Type'} (P : Prop) (Q : A -> Prop) : (term222 A P Q) = (term223 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3365916 {_87477 : Type'} (P : Prop) (Q : _87477 -> Prop) : (term222 _87477 P Q) = (term223 _87477 P Q).
Proof. exact (@lem3365915 _87477 P Q). Qed.
Lemma lem3365917 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term224 _87477 _87481 x s x' f) = (term225 _87477 _87481 x s x' f).
Proof. exact (@lem3365916 _87477 (term166 _87477 _87481 x s x' f) (term219 _87477 _87481 x s x' f)). Qed.
Lemma lem3365918 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term226 _87477 _87481 x s x' f x'') = (term217 _87477 _87481 x s x' f x'').
Proof. exact (eq_refl (term226 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365919 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term227 _87477 _87481 x s x' f) = (term219 _87477 _87481 x s x' f).
Proof. exact (fun_ext (fun x'' : _87477 => @lem3365918 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365920 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365921 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term228 _87477 _87481 x s x' f) = (term220 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365920 _87477) (@lem3365919 _87477 _87481 x s x' f)). Qed.
Lemma lem3365922 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term181 _87477 _87481 x s x' f) = (term181 _87477 _87481 x s x' f).
Proof. exact (eq_refl (term181 _87477 _87481 x s x' f)). Qed.
Lemma lem3365923 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term224 _87477 _87481 x s x' f) = (term221 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365922 _87477 _87481 x s x' f) (@lem3365921 _87477 _87481 x s x' f)). Qed.
Lemma lem3365924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3365925 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term229 _87477 _87481 x s x' f) = (term230 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365924) (@lem3365923 _87477 _87481 x s x' f)). Qed.
Lemma lem3365926 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term226 _87477 _87481 x s x' f x'') = (term217 _87477 _87481 x s x' f x'').
Proof. exact (eq_refl (term226 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365927 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term181 _87477 _87481 x s x' f) = (term181 _87477 _87481 x s x' f).
Proof. exact (eq_refl (term181 _87477 _87481 x s x' f)). Qed.
Lemma lem3365928 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term231 _87477 _87481 x s x' f x'') = (term232 _87477 _87481 x s x' f x'').
Proof. exact (MK_COMB (@lem3365927 _87477 _87481 x s x' f) (@lem3365926 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365929 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term233 _87477 _87481 x s x' f) = (term234 _87477 _87481 x s x' f).
Proof. exact (fun_ext (fun x'' : _87477 => @lem3365928 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365930 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365931 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term225 _87477 _87481 x s x' f) = (term235 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365930 _87477) (@lem3365929 _87477 _87481 x s x' f)). Qed.
Lemma lem3365932 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : ((term224 _87477 _87481 x s x' f) = (term225 _87477 _87481 x s x' f)) = ((term221 _87477 _87481 x s x' f) = (term235 _87477 _87481 x s x' f)).
Proof. exact (MK_COMB (@lem3365925 _87477 _87481 x s x' f) (@lem3365931 _87477 _87481 x s x' f)). Qed.
Lemma lem3365933 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term221 _87477 _87481 x s x' f) = (term235 _87477 _87481 x s x' f).
Proof. exact (EQ_MP (@lem3365932 _87477 _87481 x s x' f) (@lem3365917 _87477 _87481 x s x' f)). Qed.
Lemma lem3365934 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term183 _87477 _87481 x s x' f) = (term235 _87477 _87481 x s x' f).
Proof. exact (TRANS (@lem3365913 _87477 _87481 x s x' f) (@lem3365933 _87477 _87481 x s x' f)). Qed.
Lemma lem3365935 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term190 _87477 _87481 x s x' f) = (term236 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365891 _87477 _87481 x s x' f) (@lem3365934 _87477 _87481 x s x' f)). Qed.
Lemma lem3365937 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3365938 {_87477 : Type'} (P : _87477 -> Prop) (Q : _87477 -> Prop) : (term237 _87477 P Q) = (term238 _87477 P Q).
Proof. exact (@lem3365937 _87477 P Q). Qed.
Lemma lem3365939 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term239 _87477 _87481 x s x' f) = (term240 _87477 _87481 x s x' f).
Proof. exact (@lem3365938 _87477 (term205 _87477 _87481 x s x' f) (term234 _87477 _87481 x s x' f)). Qed.
Lemma lem3365940 {_87477 _87481 : Type'} (x' : _87477) (x : _87477) (s : _87477 -> Prop) (x'' : _87481) (f : _87477 -> _87481) : (term241 _87477 _87481 x s x'' f x') = (term203 _87477 _87481 x' x s x'' f).
Proof. exact (eq_refl (term241 _87477 _87481 x s x'' f x')). Qed.
Lemma lem3365941 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term242 _87477 _87481 x s x' f) = (term205 _87477 _87481 x s x' f).
Proof. exact (fun_ext (fun x'' : _87477 => @lem3365940 _87477 _87481 x'' x s x' f)). Qed.
Lemma lem3365942 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365943 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term243 _87477 _87481 x s x' f) = (term206 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365942 _87477) (@lem3365941 _87477 _87481 x s x' f)). Qed.
Lemma lem3365944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3365945 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term244 _87477 _87481 x s x' f) = (term207 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365944) (@lem3365943 _87477 _87481 x s x' f)). Qed.
Lemma lem3365946 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term245 _87477 _87481 x s x' f x'') = (term232 _87477 _87481 x s x' f x'').
Proof. exact (eq_refl (term245 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365947 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term246 _87477 _87481 x s x' f) = (term234 _87477 _87481 x s x' f).
Proof. exact (fun_ext (fun x'' : _87477 => @lem3365946 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365948 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365949 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term247 _87477 _87481 x s x' f) = (term235 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365948 _87477) (@lem3365947 _87477 _87481 x s x' f)). Qed.
Lemma lem3365950 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term239 _87477 _87481 x s x' f) = (term236 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365945 _87477 _87481 x s x' f) (@lem3365949 _87477 _87481 x s x' f)). Qed.
Lemma lem3365951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3365952 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term248 _87477 _87481 x s x' f) = (term249 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365951) (@lem3365950 _87477 _87481 x s x' f)). Qed.
Lemma lem3365953 {_87477 _87481 : Type'} (x' : _87477) (x : _87477) (s : _87477 -> Prop) (x'' : _87481) (f : _87477 -> _87481) : (term241 _87477 _87481 x s x'' f x') = (term203 _87477 _87481 x' x s x'' f).
Proof. exact (eq_refl (term241 _87477 _87481 x s x'' f x')). Qed.
Lemma lem3365954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3365955 {_87477 _87481 : Type'} (x' : _87477) (x : _87477) (s : _87477 -> Prop) (x'' : _87481) (f : _87477 -> _87481) : (term250 _87477 _87481 x s x'' f x') = (term251 _87477 _87481 x' x s x'' f).
Proof. exact (MK_COMB (@lem3365954) (@lem3365953 _87477 _87481 x' x s x'' f)). Qed.
Lemma lem3365956 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term245 _87477 _87481 x s x' f x'') = (term232 _87477 _87481 x s x' f x'').
Proof. exact (eq_refl (term245 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365957 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term252 _87477 _87481 x s x' f x'') = (term253 _87477 _87481 x s x' f x'').
Proof. exact (MK_COMB (@lem3365955 _87477 _87481 x'' x s x' f) (@lem3365956 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365958 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term254 _87477 _87481 x s x' f) = (term255 _87477 _87481 x s x' f).
Proof. exact (fun_ext (fun x'' : _87477 => @lem3365957 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3365959 {_87477 : Type'} : (@ex _87477) = (@ex _87477).
Proof. exact (eq_refl (@ex _87477)). Qed.
Lemma lem3365960 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term240 _87477 _87481 x s x' f) = (term256 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3365959 _87477) (@lem3365958 _87477 _87481 x s x' f)). Qed.
Lemma lem3365961 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : ((term239 _87477 _87481 x s x' f) = (term240 _87477 _87481 x s x' f)) = ((term236 _87477 _87481 x s x' f) = (term256 _87477 _87481 x s x' f)).
Proof. exact (MK_COMB (@lem3365952 _87477 _87481 x s x' f) (@lem3365960 _87477 _87481 x s x' f)). Qed.
Lemma lem3365962 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term236 _87477 _87481 x s x' f) = (term256 _87477 _87481 x s x' f).
Proof. exact (EQ_MP (@lem3365961 _87477 _87481 x s x' f) (@lem3365939 _87477 _87481 x s x' f)). Qed.
Lemma lem3365964 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term190 _87477 _87481 x s x' f) = (term256 _87477 _87481 x s x' f).
Proof. exact (TRANS (@lem3365935 _87477 _87481 x s x' f) (@lem3365962 _87477 _87481 x s x' f)). Qed.
Lemma lem3365965 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term149 _87477 _87481 x s x' f) = (term256 _87477 _87481 x s x' f).
Proof. exact (TRANS (@lem3365672 _87477 _87481 x s x' f) (@lem3365964 _87477 _87481 x s x' f)). Qed.
Lemma lem3365966 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term149 _87477 _87481 x s x' f) : term256 _87477 _87481 x s x' f.
Proof. exact (EQ_MP (@lem3365965 _87477 _87481 x s x' f) (@lem3365591 _87477 _87481 x s x' f h1)). Qed.
Lemma lem3365967 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term253 _87477 _87481 x s x' f x'') : term253 _87477 _87481 x s x' f x''.
Proof. exact (h1). Qed.
Lemma lem3365992 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term217 _87477 _87481 x s x' f x'') = (term217 _87477 _87481 x s x' f x'').
Proof. exact (eq_refl (term217 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3366021 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term156 _87477 _87481 x s x' f x'') = (term156 _87477 _87481 x s x' f x'').
Proof. exact (eq_refl (term156 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3366022 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term165 _87477 _87481 x s x' f) = (term165 _87477 _87481 x s x' f).
Proof. exact (fun_ext (fun x'' : _87477 => @lem3366021 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3366023 {_87477 : Type'} : (@all _87477) = (@all _87477).
Proof. exact (eq_refl (@all _87477)). Qed.
Lemma lem3366024 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term166 _87477 _87481 x s x' f) = (term166 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3366023 _87477) (@lem3366022 _87477 _87481 x s x' f)). Qed.
Lemma lem3366025 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3366026 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term181 _87477 _87481 x s x' f) = (term181 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3366025) (@lem3366024 _87477 _87481 x s x' f)). Qed.
Lemma lem3366027 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term232 _87477 _87481 x s x' f x'') = (term232 _87477 _87481 x s x' f x'').
Proof. exact (MK_COMB (@lem3366026 _87477 _87481 x s x' f) (@lem3365992 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3366046 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term168 _87477 _87481 s x' f x) = (term168 _87477 _87481 s x' f x).
Proof. exact (eq_refl (term168 _87477 _87481 s x' f x)). Qed.
Lemma lem3366047 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term174 _87477 _87481 s x' f) = (term174 _87477 _87481 s x' f).
Proof. exact (fun_ext (fun x : _87477 => @lem3366046 _87477 _87481 s x' f x)). Qed.
Lemma lem3366048 {_87477 : Type'} : (@all _87477) = (@all _87477).
Proof. exact (eq_refl (@all _87477)). Qed.
Lemma lem3366049 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term175 _87477 _87481 s x' f) = (term175 _87477 _87481 s x' f).
Proof. exact (MK_COMB (@lem3366048 _87477) (@lem3366047 _87477 _87481 s x' f)). Qed.
Lemma lem3366060 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term176 _87477 _87481 x' f x) = (term176 _87477 _87481 x' f x).
Proof. exact (eq_refl (term176 _87477 _87481 x' f x)). Qed.
Lemma lem3366061 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term178 _87477 _87481 x s x' f) = (term178 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3366060 _87477 _87481 x' f x) (@lem3366049 _87477 _87481 s x' f)). Qed.
Lemma lem3366086 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term201 _87477 _87481 x s x' f x'') = (term201 _87477 _87481 x s x' f x'').
Proof. exact (eq_refl (term201 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3366087 {_87477 _87481 : Type'} (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term203 _87477 _87481 x'' x s x' f) = (term203 _87477 _87481 x'' x s x' f).
Proof. exact (MK_COMB (@lem3366086 _87477 _87481 x s x' f x'') (@lem3366061 _87477 _87481 x s x' f)). Qed.
Lemma lem3366088 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3366089 {_87477 _87481 : Type'} (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term251 _87477 _87481 x'' x s x' f) = (term251 _87477 _87481 x'' x s x' f).
Proof. exact (MK_COMB (@lem3366088) (@lem3366087 _87477 _87481 x'' x s x' f)). Qed.
Lemma lem3366090 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term253 _87477 _87481 x s x' f x'') = (term253 _87477 _87481 x s x' f x'').
Proof. exact (MK_COMB (@lem3366089 _87477 _87481 x'' x s x' f) (@lem3366027 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3366091 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term253 _87477 _87481 x s x' f x'') : term253 _87477 _87481 x s x' f x''.
Proof. exact (EQ_MP (@lem3366090 _87477 _87481 x s x' f x'') (@lem3365967 _87477 _87481 x s x' f x'' h1)). Qed.
Lemma lem3366092 {_87477 _87481 : Type'} (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : term203 _87477 _87481 x'' x s x' f.
Proof. exact (h1). Qed.
Lemma lem3366093 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') : term232 _87477 _87481 x s x' f x''.
Proof. exact (h1). Qed.
Lemma lem3366094 {_87477 _87481 : Type'} (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : term178 _87477 _87481 x s x' f.
Proof. exact (proj2 (@lem3366092 _87477 _87481 x'' x s x' f h1)). Qed.
Lemma lem3366095 {_87477 _87481 : Type'} (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : term67 _87477 _87481 x s x' f x''.
Proof. exact (proj1 (@lem3366092 _87477 _87481 x'' x s x' f h1)). Qed.
Lemma lem3366096 {_87477 _87481 : Type'} (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : term175 _87477 _87481 s x' f.
Proof. exact (proj2 (@lem3366094 _87477 _87481 x'' x s x' f h1)). Qed.
Lemma lem3366099 {_87477 _87481 : Type'} (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : term10 _87477 x x'' s.
Proof. exact (proj1 (@lem3366095 _87477 _87481 x'' x s x' f h1)). Qed.
Lemma lem3366102 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') : term217 _87477 _87481 x s x' f x''.
Proof. exact (proj2 (@lem3366093 _87477 _87481 x s x' f x'' h1)). Qed.
Lemma lem3366103 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') : term166 _87477 _87481 x s x' f.
Proof. exact (proj1 (@lem3366093 _87477 _87481 x s x' f x'' h1)). Qed.
Lemma lem3366105 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term146 _87477 _87481 s x' f x'') : term146 _87477 _87481 s x' f x''.
Proof. exact (h1). Qed.
Lemma lem3366132 {_87477 : Type'} (x'' : _87477) (x : _87477) (h1 : x'' = x) : x'' = x.
Proof. exact (h1). Qed.
Lemma lem3366144 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term168 _87477 _87481 s x' f x) = (term168 _87477 _87481 s x' f x).
Proof. exact (eq_refl (term168 _87477 _87481 s x' f x)). Qed.
Lemma lem3366145 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term174 _87477 _87481 s x' f) = (term174 _87477 _87481 s x' f).
Proof. exact (fun_ext (fun x : _87477 => @lem3366144 _87477 _87481 s x' f x)). Qed.
Lemma lem3366146 {_87477 : Type'} : (@all _87477) = (@all _87477).
Proof. exact (eq_refl (@all _87477)). Qed.
Lemma lem3366148 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term175 _87477 _87481 s x' f) = (term175 _87477 _87481 s x' f).
Proof. exact (MK_COMB (@lem3366146 _87477) (@lem3366145 _87477 _87481 s x' f)). Qed.
Lemma lem3366149 {_87477 _87481 : Type'} (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : term175 _87477 _87481 s x' f.
Proof. exact (EQ_MP (@lem3366148 _87477 _87481 s x' f) (@lem3366096 _87477 _87481 x'' x s x' f h1)). Qed.
Lemma lem3366157 {_87477 : Type'} (x'' : _87477) (s : _87477 -> Prop) (h1 : @IN _87477 x'' s) : @IN _87477 x'' s.
Proof. exact (h1). Qed.
Lemma lem3366175 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term156 _87477 _87481 x s x' f x'') = (term257 _87477 _87481 x s x' f x'').
Proof. exact (@lem19699 (term258 _87477 x'' x) (term259 _87477 x'' s) (term152 _87477 _87481 x' f x'')). Qed.
Lemma lem3366176 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term165 _87477 _87481 x s x' f) = (term260 _87477 _87481 x s x' f).
Proof. exact (fun_ext (fun x'' : _87477 => @lem3366175 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3366177 {_87477 : Type'} : (@all _87477) = (@all _87477).
Proof. exact (eq_refl (@all _87477)). Qed.
Lemma lem3366179 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term166 _87477 _87481 x s x' f) = (term261 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3366177 _87477) (@lem3366176 _87477 _87481 x s x' f)). Qed.
Lemma lem3366180 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') : term261 _87477 _87481 x s x' f.
Proof. exact (EQ_MP (@lem3366179 _87477 _87481 x s x' f) (@lem3366103 _87477 _87481 x s x' f x'' h1)). Qed.
Lemma lem3366184 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : x' = (f x)) : x' = (f x).
Proof. exact (h1). Qed.
Lemma lem3366202 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term156 _87477 _87481 x s x' f x'') = (term257 _87477 _87481 x s x' f x'').
Proof. exact (@lem19699 (term258 _87477 x'' x) (term259 _87477 x'' s) (term152 _87477 _87481 x' f x'')). Qed.
Lemma lem3366203 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term165 _87477 _87481 x s x' f) = (term260 _87477 _87481 x s x' f).
Proof. exact (fun_ext (fun x'' : _87477 => @lem3366202 _87477 _87481 x s x' f x'')). Qed.
Lemma lem3366204 {_87477 : Type'} : (@all _87477) = (@all _87477).
Proof. exact (eq_refl (@all _87477)). Qed.
Lemma lem3366206 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term166 _87477 _87481 x s x' f) = (term261 _87477 _87481 x s x' f).
Proof. exact (MK_COMB (@lem3366204 _87477) (@lem3366203 _87477 _87481 x s x' f)). Qed.
Lemma lem3366207 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') : term261 _87477 _87481 x s x' f.
Proof. exact (EQ_MP (@lem3366206 _87477 _87481 x s x' f) (@lem3366103 _87477 _87481 x s x' f x'' h1)). Qed.
Lemma lem3366219 {_87477 _87481 : Type'} (_35080 : _87477) (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : term262 _87477 _87481 s x' f _35080.
Proof. exact (@lem3366149 _87477 _87481 x'' x s x' f h1 _35080). Qed.
Lemma lem3366220 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (_35080 : _87477) : (term262 _87477 _87481 s x' f _35080) = (term168 _87477 _87481 s x' f _35080).
Proof. exact (eq_refl (term262 _87477 _87481 s x' f _35080)). Qed.
Lemma lem3366222 {_87477 _87481 : Type'} (_35081 : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') : term263 _87477 _87481 x s x' f _35081.
Proof. exact (@lem3366180 _87477 _87481 x s x' f x'' h1 _35081). Qed.
Lemma lem3366223 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (_35081 : _87477) : (term263 _87477 _87481 x s x' f _35081) = (term257 _87477 _87481 x s x' f _35081).
Proof. exact (eq_refl (term263 _87477 _87481 x s x' f _35081)). Qed.
Lemma lem3366224 {_87477 _87481 : Type'} (_35081 : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') : term257 _87477 _87481 x s x' f _35081.
Proof. exact (EQ_MP (@lem3366223 _87477 _87481 x s x' f _35081) (@lem3366222 _87477 _87481 _35081 x s x' f x'' h1)). Qed.
Lemma lem3366225 {_87477 _87481 : Type'} (_35082 : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') : term263 _87477 _87481 x s x' f _35082.
Proof. exact (@lem3366207 _87477 _87481 x s x' f x'' h1 _35082). Qed.
Lemma lem3366226 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (_35082 : _87477) : (term263 _87477 _87481 x s x' f _35082) = (term257 _87477 _87481 x s x' f _35082).
Proof. exact (eq_refl (term263 _87477 _87481 x s x' f _35082)). Qed.
Lemma lem3366227 {_87477 _87481 : Type'} (_35082 : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') : term257 _87477 _87481 x s x' f _35082.
Proof. exact (EQ_MP (@lem3366226 _87477 _87481 x s x' f _35082) (@lem3366225 _87477 _87481 _35082 x s x' f x'' h1)). Qed.
Lemma lem3366241 {_87477 _87481 : Type'} (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : x' = (f x'').
Proof. exact (proj2 (@lem3366095 _87477 _87481 x'' x s x' f h1)). Qed.
Lemma lem3366243 {_87477 : Type'} (x'' : _87477) (x : _87477) (h1 : x'' = x) : x'' = x.
Proof. exact (h1). Qed.
Lemma lem3366251 {_87477 _87481 : Type'} (_35080 : _87477) (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : term168 _87477 _87481 s x' f _35080.
Proof. exact (EQ_MP (@lem3366220 _87477 _87481 s x' f _35080) (@lem3366219 _87477 _87481 _35080 x'' x s x' f h1)). Qed.
Lemma lem3366253 {_87477 _87481 : Type'} (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : x' = (f x'').
Proof. exact (proj2 (@lem3366095 _87477 _87481 x'' x s x' f h1)). Qed.
Lemma lem3366255 {_87477 : Type'} (x'' : _87477) (s : _87477 -> Prop) (h1 : @IN _87477 x'' s) : @IN _87477 x'' s.
Proof. exact (h1). Qed.
Lemma lem3366257 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : x' = (f x)) : x' = (f x).
Proof. exact (h1). Qed.
Lemma lem3366263 {_87477 _87481 : Type'} (_35081 : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') : term264 _87477 _87481 x x' f _35081.
Proof. exact (proj1 (@lem3366224 _87477 _87481 _35081 x s x' f x'' h1)). Qed.
Lemma lem3366273 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term146 _87477 _87481 s x' f x'') : x' = (f x'').
Proof. exact (proj2 (@lem3366105 _87477 _87481 s x' f x'' h1)). Qed.
Lemma lem3366285 {_87477 _87481 : Type'} (_35082 : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') : term168 _87477 _87481 s x' f _35082.
Proof. exact (proj2 (@lem3366227 _87477 _87481 _35082 x s x' f x'' h1)). Qed.
Lemma lem3366313 {_87477 _87481 : Type'} (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : term152 _87477 _87481 x' f x.
Proof. exact (proj1 (@lem3366094 _87477 _87481 x'' x s x' f h1)). Qed.
Lemma lem3366328 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) : (term265 _87477 _87481 x' f) = (term265 _87477 _87481 x' f).
Proof. exact (eq_refl (term265 _87477 _87481 x' f)). Qed.
Lemma lem3366329 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : x'' = x) : (term266 _87477 _87481 x' f x'') = (term266 _87477 _87481 x' f x).
Proof. exact (MK_COMB (@lem3366328 _87477 _87481 x' f) (@lem3366243 _87477 x'' x h1)). Qed.
Lemma lem3366330 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term266 _87477 _87481 x' f x) = (x' = (f x)).
Proof. exact (eq_refl (term266 _87477 _87481 x' f x)). Qed.
Lemma lem3366331 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term267 _87477 _87481 x' f x'') = (term267 _87477 _87481 x' f x'').
Proof. exact (eq_refl (term267 _87477 _87481 x' f x'')). Qed.
Lemma lem3366332 {_87477 _87481 : Type'} (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) : ((term266 _87477 _87481 x' f x'') = (term266 _87477 _87481 x' f x)) = ((term266 _87477 _87481 x' f x'') = (x' = (f x))).
Proof. exact (MK_COMB (@lem3366331 _87477 _87481 x' f x'') (@lem3366330 _87477 _87481 x' f x)). Qed.
Lemma lem3366333 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term266 _87477 _87481 x' f x'') = (x' = (f x'')).
Proof. exact (eq_refl (term266 _87477 _87481 x' f x'')). Qed.
Lemma lem3366334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3366335 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) : (term267 _87477 _87481 x' f x'') = (term268 _87477 _87481 x' f x'').
Proof. exact (MK_COMB (@lem3366334) (@lem3366333 _87477 _87481 x' f x'')). Qed.
Lemma lem3366336 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (x' = (f x)) = (x' = (f x)).
Proof. exact (eq_refl (x' = (f x))). Qed.
Lemma lem3366337 {_87477 _87481 : Type'} (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) : ((term266 _87477 _87481 x' f x'') = (x' = (f x))) = ((x' = (f x'')) = (x' = (f x))).
Proof. exact (MK_COMB (@lem3366335 _87477 _87481 x' f x'') (@lem3366336 _87477 _87481 x' f x)). Qed.
Lemma lem3366338 {_87477 _87481 : Type'} (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) : ((term266 _87477 _87481 x' f x'') = (term266 _87477 _87481 x' f x)) = ((x' = (f x'')) = (x' = (f x))).
Proof. exact (TRANS (@lem3366332 _87477 _87481 x'' x' f x) (@lem3366337 _87477 _87481 x'' x' f x)). Qed.
Lemma lem3366339 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : x'' = x) : (x' = (f x'')) = (x' = (f x)).
Proof. exact (EQ_MP (@lem3366338 _87477 _87481 x'' x' f x) (@lem3366329 _87477 _87481 x' f x'' x h1)). Qed.
Lemma lem3366340 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : x'' = x) : x' = (f x).
Proof. exact (EQ_MP (@lem3366339 _87477 _87481 x' f x'' x h2) (@lem3366241 _87477 _87481 x'' x s x' f h1)). Qed.
Lemma lem3366355 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87477) : (term269 _87477 _87481 f x) = (term269 _87477 _87481 f x).
Proof. exact (eq_refl (term269 _87477 _87481 f x)). Qed.
Lemma lem3366356 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : x'' = x) : (term270 _87477 _87481 f x x') = (term271 _87477 _87481 f x).
Proof. exact (MK_COMB (@lem3366355 _87477 _87481 f x) (@lem3366340 _87477 _87481 s x' f x'' x h1 h2)). Qed.
Lemma lem3366357 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87477) : (term271 _87477 _87481 f x) = (term272 _87477 _87481 f x).
Proof. exact (eq_refl (term271 _87477 _87481 f x)). Qed.
Lemma lem3366358 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87477) (x' : _87481) : (term273 _87477 _87481 f x x') = (term273 _87477 _87481 f x x').
Proof. exact (eq_refl (term273 _87477 _87481 f x x')). Qed.
Lemma lem3366359 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x : _87477) : ((term270 _87477 _87481 f x x') = (term271 _87477 _87481 f x)) = ((term270 _87477 _87481 f x x') = (term272 _87477 _87481 f x)).
Proof. exact (MK_COMB (@lem3366358 _87477 _87481 f x x') (@lem3366357 _87477 _87481 f x)). Qed.
Lemma lem3366360 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term270 _87477 _87481 f x x') = (term152 _87477 _87481 x' f x).
Proof. exact (eq_refl (term270 _87477 _87481 f x x')). Qed.
Lemma lem3366361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3366362 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x : _87477) : (term273 _87477 _87481 f x x') = (term274 _87477 _87481 x' f x).
Proof. exact (MK_COMB (@lem3366361) (@lem3366360 _87477 _87481 x' f x)). Qed.
Lemma lem3366363 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87477) : (term272 _87477 _87481 f x) = (term272 _87477 _87481 f x).
Proof. exact (eq_refl (term272 _87477 _87481 f x)). Qed.
Lemma lem3366364 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x : _87477) : ((term270 _87477 _87481 f x x') = (term272 _87477 _87481 f x)) = ((term152 _87477 _87481 x' f x) = (term272 _87477 _87481 f x)).
Proof. exact (MK_COMB (@lem3366362 _87477 _87481 x' f x) (@lem3366363 _87477 _87481 f x)). Qed.
Lemma lem3366365 {_87477 _87481 : Type'} (x' : _87481) (f : _87477 -> _87481) (x : _87477) : ((term270 _87477 _87481 f x x') = (term271 _87477 _87481 f x)) = ((term152 _87477 _87481 x' f x) = (term272 _87477 _87481 f x)).
Proof. exact (TRANS (@lem3366359 _87477 _87481 x' f x) (@lem3366364 _87477 _87481 x' f x)). Qed.
Lemma lem3366366 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : x'' = x) : (term152 _87477 _87481 x' f x) = (term272 _87477 _87481 f x).
Proof. exact (EQ_MP (@lem3366365 _87477 _87481 x' f x) (@lem3366356 _87477 _87481 s x' f x'' x h1 h2)). Qed.
Lemma lem3366367 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : x'' = x) : term272 _87477 _87481 f x.
Proof. exact (EQ_MP (@lem3366366 _87477 _87481 s x' f x'' x h1 h2) (@lem3366313 _87477 _87481 x'' x s x' f h1)). Qed.
Lemma lem3366408 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) (_35080 : _87477) : (term275 _87477 _87481 s f _35080) = (term275 _87477 _87481 s f _35080).
Proof. exact (eq_refl (term275 _87477 _87481 s f _35080)). Qed.
Lemma lem3366409 {_87477 _87481 : Type'} (_35080 : _87477) (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : (term276 _87477 _87481 s f _35080 x') = (term277 _87477 _87481 s _35080 f x'').
Proof. exact (MK_COMB (@lem3366408 _87477 _87481 s f _35080) (@lem3366253 _87477 _87481 x'' x s x' f h1)). Qed.
Lemma lem3366410 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35080 : _87477) : (term277 _87477 _87481 s _35080 f x'') = (term278 _87477 _87481 s x'' f _35080).
Proof. exact (eq_refl (term277 _87477 _87481 s _35080 f x'')). Qed.
Lemma lem3366411 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) (_35080 : _87477) (x' : _87481) : (term279 _87477 _87481 s f _35080 x') = (term279 _87477 _87481 s f _35080 x').
Proof. exact (eq_refl (term279 _87477 _87481 s f _35080 x')). Qed.
Lemma lem3366412 {_87477 _87481 : Type'} (x' : _87481) (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35080 : _87477) : ((term276 _87477 _87481 s f _35080 x') = (term277 _87477 _87481 s _35080 f x'')) = ((term276 _87477 _87481 s f _35080 x') = (term278 _87477 _87481 s x'' f _35080)).
Proof. exact (MK_COMB (@lem3366411 _87477 _87481 s f _35080 x') (@lem3366410 _87477 _87481 s x'' f _35080)). Qed.
Lemma lem3366413 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (_35080 : _87477) : (term276 _87477 _87481 s f _35080 x') = (term168 _87477 _87481 s x' f _35080).
Proof. exact (eq_refl (term276 _87477 _87481 s f _35080 x')). Qed.
Lemma lem3366414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3366415 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (_35080 : _87477) : (term279 _87477 _87481 s f _35080 x') = (term280 _87477 _87481 s x' f _35080).
Proof. exact (MK_COMB (@lem3366414) (@lem3366413 _87477 _87481 s x' f _35080)). Qed.
Lemma lem3366416 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35080 : _87477) : (term278 _87477 _87481 s x'' f _35080) = (term278 _87477 _87481 s x'' f _35080).
Proof. exact (eq_refl (term278 _87477 _87481 s x'' f _35080)). Qed.
Lemma lem3366417 {_87477 _87481 : Type'} (x' : _87481) (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35080 : _87477) : ((term276 _87477 _87481 s f _35080 x') = (term278 _87477 _87481 s x'' f _35080)) = ((term168 _87477 _87481 s x' f _35080) = (term278 _87477 _87481 s x'' f _35080)).
Proof. exact (MK_COMB (@lem3366415 _87477 _87481 s x' f _35080) (@lem3366416 _87477 _87481 s x'' f _35080)). Qed.
Lemma lem3366418 {_87477 _87481 : Type'} (x' : _87481) (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35080 : _87477) : ((term276 _87477 _87481 s f _35080 x') = (term277 _87477 _87481 s _35080 f x'')) = ((term168 _87477 _87481 s x' f _35080) = (term278 _87477 _87481 s x'' f _35080)).
Proof. exact (TRANS (@lem3366412 _87477 _87481 x' s x'' f _35080) (@lem3366417 _87477 _87481 x' s x'' f _35080)). Qed.
Lemma lem3366419 {_87477 _87481 : Type'} (_35080 : _87477) (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : (term168 _87477 _87481 s x' f _35080) = (term278 _87477 _87481 s x'' f _35080).
Proof. exact (EQ_MP (@lem3366418 _87477 _87481 x' s x'' f _35080) (@lem3366409 _87477 _87481 _35080 x'' x s x' f h1)). Qed.
Lemma lem3366420 {_87477 _87481 : Type'} (_35080 : _87477) (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : term278 _87477 _87481 s x'' f _35080.
Proof. exact (EQ_MP (@lem3366419 _87477 _87481 _35080 x'' x s x' f h1) (@lem3366251 _87477 _87481 _35080 x'' x s x' f h1)). Qed.
Lemma lem3366434 {_87477 : Type'} (x'' : _87477) (s : _87477 -> Prop) (h1 : @IN _87477 x'' s) : @IN _87477 x'' s.
Proof. exact (h1). Qed.
Lemma lem3366449 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (_35081 : _87477) : (term281 _87477 _87481 x f _35081) = (term281 _87477 _87481 x f _35081).
Proof. exact (eq_refl (term281 _87477 _87481 x f _35081)). Qed.
Lemma lem3366450 {_87477 _87481 : Type'} (_35081 : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : x' = (f x)) : (term282 _87477 _87481 x f _35081 x') = (term283 _87477 _87481 _35081 f x).
Proof. exact (MK_COMB (@lem3366449 _87477 _87481 x f _35081) (@lem3366257 _87477 _87481 x' f x h1)). Qed.
Lemma lem3366451 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (_35081 : _87477) : (term283 _87477 _87481 _35081 f x) = (term284 _87477 _87481 x f _35081).
Proof. exact (eq_refl (term283 _87477 _87481 _35081 f x)). Qed.
Lemma lem3366452 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (_35081 : _87477) (x' : _87481) : (term285 _87477 _87481 x f _35081 x') = (term285 _87477 _87481 x f _35081 x').
Proof. exact (eq_refl (term285 _87477 _87481 x f _35081 x')). Qed.
Lemma lem3366453 {_87477 _87481 : Type'} (x' : _87481) (x : _87477) (f : _87477 -> _87481) (_35081 : _87477) : ((term282 _87477 _87481 x f _35081 x') = (term283 _87477 _87481 _35081 f x)) = ((term282 _87477 _87481 x f _35081 x') = (term284 _87477 _87481 x f _35081)).
Proof. exact (MK_COMB (@lem3366452 _87477 _87481 x f _35081 x') (@lem3366451 _87477 _87481 x f _35081)). Qed.
Lemma lem3366454 {_87477 _87481 : Type'} (x : _87477) (x' : _87481) (f : _87477 -> _87481) (_35081 : _87477) : (term282 _87477 _87481 x f _35081 x') = (term264 _87477 _87481 x x' f _35081).
Proof. exact (eq_refl (term282 _87477 _87481 x f _35081 x')). Qed.
Lemma lem3366455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3366456 {_87477 _87481 : Type'} (x : _87477) (x' : _87481) (f : _87477 -> _87481) (_35081 : _87477) : (term285 _87477 _87481 x f _35081 x') = (term286 _87477 _87481 x x' f _35081).
Proof. exact (MK_COMB (@lem3366455) (@lem3366454 _87477 _87481 x x' f _35081)). Qed.
Lemma lem3366457 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (_35081 : _87477) : (term284 _87477 _87481 x f _35081) = (term284 _87477 _87481 x f _35081).
Proof. exact (eq_refl (term284 _87477 _87481 x f _35081)). Qed.
Lemma lem3366458 {_87477 _87481 : Type'} (x' : _87481) (x : _87477) (f : _87477 -> _87481) (_35081 : _87477) : ((term282 _87477 _87481 x f _35081 x') = (term284 _87477 _87481 x f _35081)) = ((term264 _87477 _87481 x x' f _35081) = (term284 _87477 _87481 x f _35081)).
Proof. exact (MK_COMB (@lem3366456 _87477 _87481 x x' f _35081) (@lem3366457 _87477 _87481 x f _35081)). Qed.
Lemma lem3366459 {_87477 _87481 : Type'} (x' : _87481) (x : _87477) (f : _87477 -> _87481) (_35081 : _87477) : ((term282 _87477 _87481 x f _35081 x') = (term283 _87477 _87481 _35081 f x)) = ((term264 _87477 _87481 x x' f _35081) = (term284 _87477 _87481 x f _35081)).
Proof. exact (TRANS (@lem3366453 _87477 _87481 x' x f _35081) (@lem3366458 _87477 _87481 x' x f _35081)). Qed.
Lemma lem3366460 {_87477 _87481 : Type'} (_35081 : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : x' = (f x)) : (term264 _87477 _87481 x x' f _35081) = (term284 _87477 _87481 x f _35081).
Proof. exact (EQ_MP (@lem3366459 _87477 _87481 x' x f _35081) (@lem3366450 _87477 _87481 _35081 x' f x h1)). Qed.
Lemma lem3366461 {_87477 _87481 : Type'} (_35081 : _87477) (s : _87477 -> Prop) (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : x' = (f x)) : term284 _87477 _87481 x f _35081.
Proof. exact (EQ_MP (@lem3366460 _87477 _87481 _35081 x' f x h2) (@lem3366263 _87477 _87481 _35081 x s x' f x'' h1)). Qed.
Lemma lem3366516 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) (_35082 : _87477) : (term275 _87477 _87481 s f _35082) = (term275 _87477 _87481 s f _35082).
Proof. exact (eq_refl (term275 _87477 _87481 s f _35082)). Qed.
Lemma lem3366517 {_87477 _87481 : Type'} (_35082 : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term146 _87477 _87481 s x' f x'') : (term276 _87477 _87481 s f _35082 x') = (term277 _87477 _87481 s _35082 f x'').
Proof. exact (MK_COMB (@lem3366516 _87477 _87481 s f _35082) (@lem3366273 _87477 _87481 s x' f x'' h1)). Qed.
Lemma lem3366518 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35082 : _87477) : (term277 _87477 _87481 s _35082 f x'') = (term278 _87477 _87481 s x'' f _35082).
Proof. exact (eq_refl (term277 _87477 _87481 s _35082 f x'')). Qed.
Lemma lem3366519 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) (_35082 : _87477) (x' : _87481) : (term279 _87477 _87481 s f _35082 x') = (term279 _87477 _87481 s f _35082 x').
Proof. exact (eq_refl (term279 _87477 _87481 s f _35082 x')). Qed.
Lemma lem3366520 {_87477 _87481 : Type'} (x' : _87481) (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35082 : _87477) : ((term276 _87477 _87481 s f _35082 x') = (term277 _87477 _87481 s _35082 f x'')) = ((term276 _87477 _87481 s f _35082 x') = (term278 _87477 _87481 s x'' f _35082)).
Proof. exact (MK_COMB (@lem3366519 _87477 _87481 s f _35082 x') (@lem3366518 _87477 _87481 s x'' f _35082)). Qed.
Lemma lem3366521 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (_35082 : _87477) : (term276 _87477 _87481 s f _35082 x') = (term168 _87477 _87481 s x' f _35082).
Proof. exact (eq_refl (term276 _87477 _87481 s f _35082 x')). Qed.
Lemma lem3366522 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3366523 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (_35082 : _87477) : (term279 _87477 _87481 s f _35082 x') = (term280 _87477 _87481 s x' f _35082).
Proof. exact (MK_COMB (@lem3366522) (@lem3366521 _87477 _87481 s x' f _35082)). Qed.
Lemma lem3366524 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35082 : _87477) : (term278 _87477 _87481 s x'' f _35082) = (term278 _87477 _87481 s x'' f _35082).
Proof. exact (eq_refl (term278 _87477 _87481 s x'' f _35082)). Qed.
Lemma lem3366525 {_87477 _87481 : Type'} (x' : _87481) (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35082 : _87477) : ((term276 _87477 _87481 s f _35082 x') = (term278 _87477 _87481 s x'' f _35082)) = ((term168 _87477 _87481 s x' f _35082) = (term278 _87477 _87481 s x'' f _35082)).
Proof. exact (MK_COMB (@lem3366523 _87477 _87481 s x' f _35082) (@lem3366524 _87477 _87481 s x'' f _35082)). Qed.
Lemma lem3366526 {_87477 _87481 : Type'} (x' : _87481) (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35082 : _87477) : ((term276 _87477 _87481 s f _35082 x') = (term277 _87477 _87481 s _35082 f x'')) = ((term168 _87477 _87481 s x' f _35082) = (term278 _87477 _87481 s x'' f _35082)).
Proof. exact (TRANS (@lem3366520 _87477 _87481 x' s x'' f _35082) (@lem3366525 _87477 _87481 x' s x'' f _35082)). Qed.
Lemma lem3366527 {_87477 _87481 : Type'} (_35082 : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term146 _87477 _87481 s x' f x'') : (term168 _87477 _87481 s x' f _35082) = (term278 _87477 _87481 s x'' f _35082).
Proof. exact (EQ_MP (@lem3366526 _87477 _87481 x' s x'' f _35082) (@lem3366517 _87477 _87481 _35082 s x' f x'' h1)). Qed.
Lemma lem3366528 {_87477 _87481 : Type'} (_35082 : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : term146 _87477 _87481 s x' f x'') : term278 _87477 _87481 s x'' f _35082.
Proof. exact (EQ_MP (@lem3366527 _87477 _87481 _35082 s x' f x'' h2) (@lem3366285 _87477 _87481 _35082 x s x' f x'' h1)). Qed.
Lemma lem3366563 {_87481 : Type'} (x : _87481) : x = x.
Proof. exact (@lem21386 _87481 x). Qed.
Lemma lem3366564 {_87481 : Type'} (x : _87481) : x = x.
Proof. exact (@lem3366563 _87481 x). Qed.
Lemma lem3366565 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87477) : (f x) = (f x).
Proof. exact (@lem3366564 _87481 (f x)). Qed.
Lemma lem3366566 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87477) : term287 _87477 _87481 f x.
Proof. exact (fun h0 : term272 _87477 _87481 f x => @lem3366565 _87477 _87481 f x). Qed.
Lemma lem3366568 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3366569 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87477) : (term287 _87477 _87481 f x) = ((f x) = (f x)).
Proof. exact (@lem3366568 ((f x) = (f x))). Qed.
Lemma lem3366570 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87477) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3366569 _87477 _87481 f x) (@lem3366566 _87477 _87481 f x)). Qed.
Lemma lem3366573 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3366575 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87477) : (term272 _87477 _87481 f x) = (term289 _87477 _87481 f x).
Proof. exact (@lem3366573 ((f x) = (f x))). Qed.
Lemma lem3366578 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : x'' = x) : term289 _87477 _87481 f x.
Proof. exact (EQ_MP (@lem3366575 _87477 _87481 f x) (@lem3366367 _87477 _87481 s x' f x'' x h1 h2)). Qed.
Lemma lem3366581 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : x'' = x) : False.
Proof. exact (@lem3366578 _87477 _87481 s x' f x'' x h1 h2 (@lem3366570 _87477 _87481 f x)). Qed.
Lemma lem3366582 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : x'' = x) : term290.
Proof. exact (fun h0 : ~ False => @lem3366581 _87477 _87481 s x' f x'' x h1 h2). Qed.
Lemma lem3366584 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3366585 : term290 = False.
Proof. exact (@lem3366584 False). Qed.
Lemma lem3366621 {_87477 : Type'} (x'' : _87477) (s : _87477 -> Prop) (h1 : @IN _87477 x'' s) : @IN _87477 x'' s.
Proof. exact (h1). Qed.
Lemma lem3366622 {_87477 : Type'} (x'' : _87477) (s : _87477 -> Prop) (h1 : @IN _87477 x'' s) : term291 _87477 x'' s.
Proof. exact (fun h0 : term259 _87477 x'' s => @lem3366621 _87477 x'' s h1). Qed.
Lemma lem3366624 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3366625 {_87477 : Type'} (x'' : _87477) (s : _87477 -> Prop) : (term291 _87477 x'' s) = (@IN _87477 x'' s).
Proof. exact (@lem3366624 (@IN _87477 x'' s)). Qed.
Lemma lem3366626 {_87477 : Type'} (x'' : _87477) (s : _87477 -> Prop) (h1 : @IN _87477 x'' s) : @IN _87477 x'' s.
Proof. exact (EQ_MP (@lem3366625 _87477 x'' s) (@lem3366622 _87477 x'' s h1)). Qed.
Lemma lem3366628 {_87481 : Type'} (x : _87481) : x = x.
Proof. exact (@lem21386 _87481 x). Qed.
Lemma lem3366629 {_87481 : Type'} (x : _87481) : x = x.
Proof. exact (@lem3366628 _87481 x). Qed.
Lemma lem3366630 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x'' : _87477) : (f x'') = (f x'').
Proof. exact (@lem3366629 _87481 (f x'')). Qed.
Lemma lem3366631 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x'' : _87477) : term287 _87477 _87481 f x''.
Proof. exact (fun h0 : term272 _87477 _87481 f x'' => @lem3366630 _87477 _87481 f x''). Qed.
Lemma lem3366633 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3366634 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x'' : _87477) : (term287 _87477 _87481 f x'') = ((f x'') = (f x'')).
Proof. exact (@lem3366633 ((f x'') = (f x''))). Qed.
Lemma lem3366635 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x'' : _87477) : (f x'') = (f x'').
Proof. exact (EQ_MP (@lem3366634 _87477 _87481 f x'') (@lem3366631 _87477 _87481 f x'')). Qed.
Lemma lem3366637 (a : Prop) (b : Prop) : (term292 a b) = (term293 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3366638 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35080 : _87477) : (term278 _87477 _87481 s x'' f _35080) = (term294 _87477 _87481 s x'' f _35080).
Proof. exact (@lem3366637 (@IN _87477 _35080 s) ((f x'') = (f _35080))). Qed.
Lemma lem3366640 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3366641 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35080 : _87477) : (term294 _87477 _87481 s x'' f _35080) = (term295 _87477 _87481 s x'' f _35080).
Proof. exact (@lem3366640 (term296 _87477 _87481 s x'' f _35080)). Qed.
Lemma lem3366642 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35080 : _87477) : (term278 _87477 _87481 s x'' f _35080) = (term295 _87477 _87481 s x'' f _35080).
Proof. exact (TRANS (@lem3366638 _87477 _87481 s x'' f _35080) (@lem3366641 _87477 _87481 s x'' f _35080)). Qed.
Lemma lem3366644 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x'' : _87477) (s : _87477 -> Prop) (h1 : @IN _87477 x'' s) : term297 _87477 _87481 s f x''.
Proof. exact (conj (@lem3366626 _87477 x'' s h1) (@lem3366635 _87477 _87481 f x'')). Qed.
Lemma lem3366646 {_87477 _87481 : Type'} (_35080 : _87477) (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : term295 _87477 _87481 s x'' f _35080.
Proof. exact (EQ_MP (@lem3366642 _87477 _87481 s x'' f _35080) (@lem3366420 _87477 _87481 _35080 x'' x s x' f h1)). Qed.
Lemma lem3366647 {_87477 _87481 : Type'} (_35080 : _87477) (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : term295 _87477 _87481 s x'' f _35080.
Proof. exact (@lem3366646 _87477 _87481 _35080 x'' x s x' f h1). Qed.
Lemma lem3366648 {_87477 _87481 : Type'} (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : term298 _87477 _87481 s f x''.
Proof. exact (@lem3366647 _87477 _87481 x'' x'' x s x' f h1). Qed.
Lemma lem3366651 {_87477 _87481 : Type'} (x : _87477) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (s : _87477 -> Prop) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : @IN _87477 x'' s) : False.
Proof. exact (@lem3366648 _87477 _87481 x'' x s x' f h1 (@lem3366644 _87477 _87481 f x'' s h2)). Qed.
Lemma lem3366652 {_87477 _87481 : Type'} (x : _87477) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (s : _87477 -> Prop) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : @IN _87477 x'' s) : term290.
Proof. exact (fun h0 : ~ False => @lem3366651 _87477 _87481 x x' f x'' s h1 h2). Qed.
Lemma lem3366654 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3366655 : term290 = False.
Proof. exact (@lem3366654 False). Qed.
Lemma lem3366656 {_87477 _87481 : Type'} (x : _87477) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (s : _87477 -> Prop) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : @IN _87477 x'' s) : False.
Proof. exact (EQ_MP (@lem3366655) (@lem3366652 _87477 _87481 x x' f x'' s h1 h2)). Qed.
Lemma lem3366691 {_87477 : Type'} (x : _87477) : x = x.
Proof. exact (@lem21386 _87477 x). Qed.
Lemma lem3366692 {_87477 : Type'} (x : _87477) : x = x.
Proof. exact (@lem3366691 _87477 x). Qed.
Lemma lem3366693 {_87477 : Type'} (x : _87477) : term299 _87477 x.
Proof. exact (fun h0 : term300 _87477 x => @lem3366692 _87477 x). Qed.
Lemma lem3366695 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3366696 {_87477 : Type'} (x : _87477) : (term299 _87477 x) = (x = x).
Proof. exact (@lem3366695 (x = x)). Qed.
Lemma lem3366697 {_87477 : Type'} (x : _87477) : x = x.
Proof. exact (EQ_MP (@lem3366696 _87477 x) (@lem3366693 _87477 x)). Qed.
Lemma lem3366699 {_87481 : Type'} (x : _87481) : x = x.
Proof. exact (@lem21386 _87481 x). Qed.
Lemma lem3366700 {_87481 : Type'} (x : _87481) : x = x.
Proof. exact (@lem3366699 _87481 x). Qed.
Lemma lem3366701 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87477) : (f x) = (f x).
Proof. exact (@lem3366700 _87481 (f x)). Qed.
Lemma lem3366702 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87477) : term287 _87477 _87481 f x.
Proof. exact (fun h0 : term272 _87477 _87481 f x => @lem3366701 _87477 _87481 f x). Qed.
Lemma lem3366704 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3366705 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87477) : (term287 _87477 _87481 f x) = ((f x) = (f x)).
Proof. exact (@lem3366704 ((f x) = (f x))). Qed.
Lemma lem3366706 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87477) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3366705 _87477 _87481 f x) (@lem3366702 _87477 _87481 f x)). Qed.
Lemma lem3366708 (a : Prop) (b : Prop) : (term292 a b) = (term293 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3366709 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (_35081 : _87477) : (term284 _87477 _87481 x f _35081) = (term301 _87477 _87481 x f _35081).
Proof. exact (@lem3366708 (_35081 = x) ((f x) = (f _35081))). Qed.
Lemma lem3366711 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3366712 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (_35081 : _87477) : (term301 _87477 _87481 x f _35081) = (term302 _87477 _87481 x f _35081).
Proof. exact (@lem3366711 (term303 _87477 _87481 x f _35081)). Qed.
Lemma lem3366713 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (_35081 : _87477) : (term284 _87477 _87481 x f _35081) = (term302 _87477 _87481 x f _35081).
Proof. exact (TRANS (@lem3366709 _87477 _87481 x f _35081) (@lem3366712 _87477 _87481 x f _35081)). Qed.
Lemma lem3366715 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x : _87477) : term304 _87477 _87481 f x.
Proof. exact (conj (@lem3366697 _87477 x) (@lem3366706 _87477 _87481 f x)). Qed.
Lemma lem3366717 {_87477 _87481 : Type'} (_35081 : _87477) (s : _87477 -> Prop) (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : x' = (f x)) : term302 _87477 _87481 x f _35081.
Proof. exact (EQ_MP (@lem3366713 _87477 _87481 x f _35081) (@lem3366461 _87477 _87481 _35081 s x'' x' f x h1 h2)). Qed.
Lemma lem3366718 {_87477 _87481 : Type'} (_35081 : _87477) (s : _87477 -> Prop) (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : x' = (f x)) : term302 _87477 _87481 x f _35081.
Proof. exact (@lem3366717 _87477 _87481 _35081 s x'' x' f x h1 h2). Qed.
Lemma lem3366719 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : x' = (f x)) : term305 _87477 _87481 f x.
Proof. exact (@lem3366718 _87477 _87481 x s x'' x' f x h1 h2). Qed.
Lemma lem3366722 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : x' = (f x)) : False.
Proof. exact (@lem3366719 _87477 _87481 s x'' x' f x h1 h2 (@lem3366715 _87477 _87481 f x)). Qed.
Lemma lem3366723 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : x' = (f x)) : term290.
Proof. exact (fun h0 : ~ False => @lem3366722 _87477 _87481 s x'' x' f x h1 h2). Qed.
Lemma lem3366725 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3366726 : term290 = False.
Proof. exact (@lem3366725 False). Qed.
Lemma lem3366762 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term146 _87477 _87481 s x' f x'') : @IN _87477 x'' s.
Proof. exact (proj1 (@lem3366105 _87477 _87481 s x' f x'' h1)). Qed.
Lemma lem3366763 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term146 _87477 _87481 s x' f x'') : term291 _87477 x'' s.
Proof. exact (fun h0 : term259 _87477 x'' s => @lem3366762 _87477 _87481 s x' f x'' h1). Qed.
Lemma lem3366765 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3366766 {_87477 : Type'} (x'' : _87477) (s : _87477 -> Prop) : (term291 _87477 x'' s) = (@IN _87477 x'' s).
Proof. exact (@lem3366765 (@IN _87477 x'' s)). Qed.
Lemma lem3366767 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term146 _87477 _87481 s x' f x'') : @IN _87477 x'' s.
Proof. exact (EQ_MP (@lem3366766 _87477 x'' s) (@lem3366763 _87477 _87481 s x' f x'' h1)). Qed.
Lemma lem3366769 {_87481 : Type'} (x : _87481) : x = x.
Proof. exact (@lem21386 _87481 x). Qed.
Lemma lem3366770 {_87481 : Type'} (x : _87481) : x = x.
Proof. exact (@lem3366769 _87481 x). Qed.
Lemma lem3366771 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x'' : _87477) : (f x'') = (f x'').
Proof. exact (@lem3366770 _87481 (f x'')). Qed.
Lemma lem3366772 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x'' : _87477) : term287 _87477 _87481 f x''.
Proof. exact (fun h0 : term272 _87477 _87481 f x'' => @lem3366771 _87477 _87481 f x''). Qed.
Lemma lem3366774 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3366775 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x'' : _87477) : (term287 _87477 _87481 f x'') = ((f x'') = (f x'')).
Proof. exact (@lem3366774 ((f x'') = (f x''))). Qed.
Lemma lem3366776 {_87477 _87481 : Type'} (f : _87477 -> _87481) (x'' : _87477) : (f x'') = (f x'').
Proof. exact (EQ_MP (@lem3366775 _87477 _87481 f x'') (@lem3366772 _87477 _87481 f x'')). Qed.
Lemma lem3366778 (a : Prop) (b : Prop) : (term292 a b) = (term293 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3366779 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35082 : _87477) : (term278 _87477 _87481 s x'' f _35082) = (term294 _87477 _87481 s x'' f _35082).
Proof. exact (@lem3366778 (@IN _87477 _35082 s) ((f x'') = (f _35082))). Qed.
Lemma lem3366781 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3366782 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35082 : _87477) : (term294 _87477 _87481 s x'' f _35082) = (term295 _87477 _87481 s x'' f _35082).
Proof. exact (@lem3366781 (term296 _87477 _87481 s x'' f _35082)). Qed.
Lemma lem3366783 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (f : _87477 -> _87481) (_35082 : _87477) : (term278 _87477 _87481 s x'' f _35082) = (term295 _87477 _87481 s x'' f _35082).
Proof. exact (TRANS (@lem3366779 _87477 _87481 s x'' f _35082) (@lem3366782 _87477 _87481 s x'' f _35082)). Qed.
Lemma lem3366785 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term146 _87477 _87481 s x' f x'') : term297 _87477 _87481 s f x''.
Proof. exact (conj (@lem3366767 _87477 _87481 s x' f x'' h1) (@lem3366776 _87477 _87481 f x'')). Qed.
Lemma lem3366787 {_87477 _87481 : Type'} (_35082 : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : term146 _87477 _87481 s x' f x'') : term295 _87477 _87481 s x'' f _35082.
Proof. exact (EQ_MP (@lem3366783 _87477 _87481 s x'' f _35082) (@lem3366528 _87477 _87481 _35082 x s x' f x'' h1 h2)). Qed.
Lemma lem3366788 {_87477 _87481 : Type'} (_35082 : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : term146 _87477 _87481 s x' f x'') : term295 _87477 _87481 s x'' f _35082.
Proof. exact (@lem3366787 _87477 _87481 _35082 x s x' f x'' h1 h2). Qed.
Lemma lem3366789 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : term146 _87477 _87481 s x' f x'') : term298 _87477 _87481 s f x''.
Proof. exact (@lem3366788 _87477 _87481 x'' x s x' f x'' h1 h2). Qed.
Lemma lem3366792 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : term146 _87477 _87481 s x' f x'') : False.
Proof. exact (@lem3366789 _87477 _87481 x s x' f x'' h1 h2 (@lem3366785 _87477 _87481 s x' f x'' h2)). Qed.
Lemma lem3366793 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : term146 _87477 _87481 s x' f x'') : term290.
Proof. exact (fun h0 : ~ False => @lem3366792 _87477 _87481 x s x' f x'' h1 h2). Qed.
Lemma lem3366795 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3366796 : term290 = False.
Proof. exact (@lem3366795 False). Qed.
Lemma lem3366798 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : term146 _87477 _87481 s x' f x'') : False.
Proof. exact (EQ_MP (@lem3366796) (@lem3366793 _87477 _87481 x s x' f x'' h1 h2)). Qed.
Lemma lem3366799 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : x' = (f x)) : False.
Proof. exact (EQ_MP (@lem3366726) (@lem3366723 _87477 _87481 s x'' x' f x h1 h2)). Qed.
Lemma lem3366800 {_87477 _87481 : Type'} (x : _87477) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (s : _87477 -> Prop) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : @IN _87477 x'' s) : (@IN _87477 x'' s) = False.
Proof. exact (prop_ext (fun h3 : @IN _87477 x'' s => @lem3366656 _87477 _87481 x x' f x'' s h1 h2) (fun h3 : False => @lem3366434 _87477 x'' s h2)). Qed.
Lemma lem3366802 {_87477 _87481 : Type'} (x : _87477) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (s : _87477 -> Prop) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : @IN _87477 x'' s) : False.
Proof. exact (EQ_MP (@lem3366800 _87477 _87481 x x' f x'' s h1 h2) (@lem3366434 _87477 x'' s h2)). Qed.
Lemma lem3366804 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : x'' = x) : False.
Proof. exact (EQ_MP (@lem3366585) (@lem3366582 _87477 _87481 s x' f x'' x h1 h2)). Qed.
Lemma lem3366805 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : x' = (f x)) : (x' = (f x)) = False.
Proof. exact (prop_ext (fun h3 : x' = (f x) => @lem3366799 _87477 _87481 s x'' x' f x h1 h2) (fun h3 : False => @lem3366257 _87477 _87481 x' f x h2)). Qed.
Lemma lem3366806 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : x' = (f x)) : False.
Proof. exact (EQ_MP (@lem3366805 _87477 _87481 s x'' x' f x h1 h2) (@lem3366257 _87477 _87481 x' f x h2)). Qed.
Lemma lem3366807 {_87477 _87481 : Type'} (x : _87477) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (s : _87477 -> Prop) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : @IN _87477 x'' s) : (@IN _87477 x'' s) = False.
Proof. exact (prop_ext (fun h3 : @IN _87477 x'' s => @lem3366802 _87477 _87481 x x' f x'' s h1 h2) (fun h3 : False => @lem3366255 _87477 x'' s h2)). Qed.
Lemma lem3366808 {_87477 _87481 : Type'} (x : _87477) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (s : _87477 -> Prop) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : @IN _87477 x'' s) : False.
Proof. exact (EQ_MP (@lem3366807 _87477 _87481 x x' f x'' s h1 h2) (@lem3366255 _87477 x'' s h2)). Qed.
Lemma lem3366809 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : x'' = x) : (x'' = x) = False.
Proof. exact (prop_ext (fun h3 : x'' = x => @lem3366804 _87477 _87481 s x' f x'' x h1 h2) (fun h3 : False => @lem3366243 _87477 x'' x h2)). Qed.
Lemma lem3366810 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : x'' = x) : False.
Proof. exact (EQ_MP (@lem3366809 _87477 _87481 s x' f x'' x h1 h2) (@lem3366243 _87477 x'' x h2)). Qed.
Lemma lem3366811 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : x' = (f x)) : (x' = (f x)) = False.
Proof. exact (prop_ext (fun h3 : x' = (f x) => @lem3366806 _87477 _87481 s x'' x' f x h1 h2) (fun h3 : False => @lem3366184 _87477 _87481 x' f x h2)). Qed.
Lemma lem3366812 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : x' = (f x)) : False.
Proof. exact (EQ_MP (@lem3366811 _87477 _87481 s x'' x' f x h1 h2) (@lem3366184 _87477 _87481 x' f x h2)). Qed.
Lemma lem3366813 {_87477 _87481 : Type'} (x : _87477) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (s : _87477 -> Prop) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : @IN _87477 x'' s) : (@IN _87477 x'' s) = False.
Proof. exact (prop_ext (fun h3 : @IN _87477 x'' s => @lem3366808 _87477 _87481 x x' f x'' s h1 h2) (fun h3 : False => @lem3366157 _87477 x'' s h2)). Qed.
Lemma lem3366814 {_87477 _87481 : Type'} (x : _87477) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (s : _87477 -> Prop) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : @IN _87477 x'' s) : False.
Proof. exact (EQ_MP (@lem3366813 _87477 _87481 x x' f x'' s h1 h2) (@lem3366157 _87477 x'' s h2)). Qed.
Lemma lem3366815 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : x'' = x) : (x'' = x) = False.
Proof. exact (prop_ext (fun h3 : x'' = x => @lem3366810 _87477 _87481 s x' f x'' x h1 h2) (fun h3 : False => @lem3366132 _87477 x'' x h2)). Qed.
Lemma lem3366816 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : x'' = x) : False.
Proof. exact (EQ_MP (@lem3366815 _87477 _87481 s x' f x'' x h1 h2) (@lem3366132 _87477 x'' x h2)). Qed.
Lemma lem3366817 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : x' = (f x)) : (x' = (f x)) = False.
Proof. exact (prop_ext (fun h3 : x' = (f x) => @lem3366812 _87477 _87481 s x'' x' f x h1 h2) (fun h3 : False => @lem3366184 _87477 _87481 x' f x h2)). Qed.
Lemma lem3366818 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x'' : _87477) (x' : _87481) (f : _87477 -> _87481) (x : _87477) (h1 : term232 _87477 _87481 x s x' f x'') (h2 : x' = (f x)) : False.
Proof. exact (EQ_MP (@lem3366817 _87477 _87481 s x'' x' f x h1 h2) (@lem3366184 _87477 _87481 x' f x h2)). Qed.
Lemma lem3366819 {_87477 _87481 : Type'} (x : _87477) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (s : _87477 -> Prop) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : @IN _87477 x'' s) : (@IN _87477 x'' s) = False.
Proof. exact (prop_ext (fun h3 : @IN _87477 x'' s => @lem3366814 _87477 _87481 x x' f x'' s h1 h2) (fun h3 : False => @lem3366157 _87477 x'' s h2)). Qed.
Lemma lem3366820 {_87477 _87481 : Type'} (x : _87477) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (s : _87477 -> Prop) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : @IN _87477 x'' s) : False.
Proof. exact (EQ_MP (@lem3366819 _87477 _87481 x x' f x'' s h1 h2) (@lem3366157 _87477 x'' s h2)). Qed.
Lemma lem3366821 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : x'' = x) : (x'' = x) = False.
Proof. exact (prop_ext (fun h3 : x'' = x => @lem3366816 _87477 _87481 s x' f x'' x h1 h2) (fun h3 : False => @lem3366132 _87477 x'' x h2)). Qed.
Lemma lem3366822 {_87477 _87481 : Type'} (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (x : _87477) (h1 : term203 _87477 _87481 x'' x s x' f) (h2 : x'' = x) : False.
Proof. exact (EQ_MP (@lem3366821 _87477 _87481 s x' f x'' x h1 h2) (@lem3366132 _87477 x'' x h2)). Qed.
Lemma lem3366823 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term232 _87477 _87481 x s x' f x'') : False.
Proof. exact (or_elim (@lem3366102 _87477 _87481 x s x' f x'' h1) (fun h0 : x' = (f x) => @lem3366818 _87477 _87481 s x'' x' f x h1 h0) (fun h0 : term146 _87477 _87481 s x' f x'' => @lem3366798 _87477 _87481 x s x' f x'' h1 h0)). Qed.
Lemma lem3366824 {_87477 _87481 : Type'} (x'' : _87477) (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term203 _87477 _87481 x'' x s x' f) : False.
Proof. exact (or_elim (@lem3366099 _87477 _87481 x'' x s x' f h1) (fun h0 : x'' = x => @lem3366822 _87477 _87481 s x' f x'' x h1 h0) (fun h0 : @IN _87477 x'' s => @lem3366820 _87477 _87481 x x' f x'' s h1 h0)). Qed.
Lemma lem3366825 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term253 _87477 _87481 x s x' f x'') : False.
Proof. exact (or_elim (@lem3366091 _87477 _87481 x s x' f x'' h1) (fun h0 : term203 _87477 _87481 x'' x s x' f => @lem3366824 _87477 _87481 x'' x s x' f h0) (fun h0 : term232 _87477 _87481 x s x' f x'' => @lem3366823 _87477 _87481 x s x' f x'' h0)). Qed.
Lemma lem3366826 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term253 _87477 _87481 x s x' f x'') : (term253 _87477 _87481 x s x' f x'') = False.
Proof. exact (prop_ext (fun h2 : term253 _87477 _87481 x s x' f x'' => @lem3366825 _87477 _87481 x s x' f x'' h1) (fun h2 : False => @lem3366091 _87477 _87481 x s x' f x'' h1)). Qed.
Lemma lem3366827 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (x'' : _87477) (h1 : term253 _87477 _87481 x s x' f x'') : False.
Proof. exact (EQ_MP (@lem3366826 _87477 _87481 x s x' f x'' h1) (@lem3366091 _87477 _87481 x s x' f x'' h1)). Qed.
Lemma lem3366828 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term149 _87477 _87481 x s x' f) : False.
Proof. exact (ex_elim (@lem3365966 _87477 _87481 x s x' f h1) (fun x'' : _87477 => fun h0 : term255 _87477 _87481 x s x' f x'' => @lem3366827 _87477 _87481 x s x' f x'' h0)). Qed.
Lemma lem3366829 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term149 _87477 _87481 x s x' f) : (term149 _87477 _87481 x s x' f) = False.
Proof. exact (prop_ext (fun h2 : term149 _87477 _87481 x s x' f => @lem3366828 _87477 _87481 x s x' f h1) (fun h2 : False => @lem3365591 _87477 _87481 x s x' f h1)). Qed.
Lemma lem3366830 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) (h1 : term149 _87477 _87481 x s x' f) : False.
Proof. exact (EQ_MP (@lem3366829 _87477 _87481 x s x' f h1) (@lem3365591 _87477 _87481 x s x' f h1)). Qed.
Lemma lem3366831 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : term148 _87477 _87481 x s x' f.
Proof. exact (fun h0 : term149 _87477 _87481 x s x' f => @lem3366830 _87477 _87481 x s x' f h0). Qed.
Lemma lem3366832 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (x' : _87481) (f : _87477 -> _87481) : (term71 _87477 _87481 x s x' f) = (term120 _87477 _87481 x s x' f).
Proof. exact (EQ_MP (@lem3365590 _87477 _87481 x s x' f) (@lem3366831 _87477 _87481 x s x' f)). Qed.
Lemma lem3366837 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : term123 _87477 _87481 x s f.
Proof. exact (fun x' : _87481 => @lem3366832 _87477 _87481 x s x' f). Qed.
Lemma lem3366842 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) : term137 _87477 _87481 s f.
Proof. exact (fun x : _87477 => @lem3366837 _87477 _87481 x s f). Qed.
Lemma lem3366847 {_87477 _87481 : Type'} (f : _87477 -> _87481) : term141 _87477 _87481 f.
Proof. exact (fun s : _87477 -> Prop => @lem3366842 _87477 _87481 s f). Qed.
Lemma lem3366852 {_87477 _87481 : Type'} : term145 _87477 _87481.
Proof. exact (fun f : _87477 -> _87481 => @lem3366847 _87477 _87481 f). Qed.
Lemma lem3366853 {_87477 _87481 : Type'} : term144 _87477 _87481.
Proof. exact (EQ_MP (@lem3365586 _87477 _87481) (@lem3366852 _87477 _87481)). Qed.
Lemma lem3366854 {_87477 _87481 : Type'} (f : _87477 -> _87481) : term306 _87477 _87481 f.
Proof. exact (@lem3366853 _87477 _87481 f). Qed.
Lemma lem3366855 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (term306 _87477 _87481 f) = (term140 _87477 _87481 f).
Proof. exact (eq_refl (term306 _87477 _87481 f)). Qed.
Lemma lem3366856 {_87477 _87481 : Type'} (f : _87477 -> _87481) : term140 _87477 _87481 f.
Proof. exact (EQ_MP (@lem3366855 _87477 _87481 f) (@lem3366854 _87477 _87481 f)). Qed.
Lemma lem3366857 {_87477 _87481 : Type'} (f : _87477 -> _87481) (s : _87477 -> Prop) : term307 _87477 _87481 f s.
Proof. exact (@lem3366856 _87477 _87481 f s). Qed.
Lemma lem3366858 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) : (term307 _87477 _87481 f s) = (term136 _87477 _87481 s f).
Proof. exact (eq_refl (term307 _87477 _87481 f s)). Qed.
Lemma lem3366859 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) : term136 _87477 _87481 s f.
Proof. exact (EQ_MP (@lem3366858 _87477 _87481 s f) (@lem3366857 _87477 _87481 f s)). Qed.
Lemma lem3366860 {_87477 _87481 : Type'} (s : _87477 -> Prop) (f : _87477 -> _87481) (x : _87477) : term308 _87477 _87481 s f x.
Proof. exact (@lem3366859 _87477 _87481 s f x). Qed.
Lemma lem3366861 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : (term308 _87477 _87481 s f x) = (term127 _87477 _87481 x s f).
Proof. exact (eq_refl (term308 _87477 _87481 s f x)). Qed.
Lemma lem3366862 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : term127 _87477 _87481 x s f.
Proof. exact (EQ_MP (@lem3366861 _87477 _87481 x s f) (@lem3366860 _87477 _87481 s f x)). Qed.
Lemma lem3366864 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : term127 _87477 _87481 x s f.
Proof. exact (@lem3365347 _87477 _87481 x s f (@lem3366862 _87477 _87481 x s f)). Qed.
Lemma lem3366865 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (h1 : term128 _87477 _87481 x s f) : False.
Proof. exact (@lem3366864 _87477 _87481 x s f (@lem3365331 _87477 _87481 x s f h1)). Qed.
Lemma lem3366866 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (h1 : term128 _87477 _87481 x s f) : (term128 _87477 _87481 x s f) = False.
Proof. exact (prop_ext (fun h2 : term128 _87477 _87481 x s f => @lem3366865 _87477 _87481 x s f h1) (fun h2 : False => @lem3365331 _87477 _87481 x s f h1)). Qed.
Lemma lem3366867 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) (h1 : term128 _87477 _87481 x s f) : False.
Proof. exact (EQ_MP (@lem3366866 _87477 _87481 x s f h1) (@lem3365331 _87477 _87481 x s f h1)). Qed.
Lemma lem3366868 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : term127 _87477 _87481 x s f.
Proof. exact (fun h0 : term128 _87477 _87481 x s f => @lem3366867 _87477 _87481 x s f h0). Qed.
Lemma lem3366869 {_87477 _87481 : Type'} (x : _87477) (s : _87477 -> Prop) (f : _87477 -> _87481) : term123 _87477 _87481 x s f.
Proof. exact (EQ_MP (@lem3365330 _87477 _87481 x s f) (@lem3366868 _87477 _87481 x s f)). Qed.
Lemma lem3366870 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (s : _87477 -> Prop) : term124 _87477 _87481 x f s.
Proof. exact (EQ_MP (@lem3365326 _87477 _87481 x f s) (@lem3366869 _87477 _87481 x s f)). Qed.
