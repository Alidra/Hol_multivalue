Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARTESIAN_PRODUCT_EMPTY_term_abbrevs.
Require Import CARTESIAN_PRODUCT_spec.
Require Import EXTENSION_spec.
Require Import FUN_EQ_THM_spec.
Require Import IN_SING_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm82_spec.
Lemma lem4408930 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4408931 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem4408932 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem4408931 A B f) (@lem4408930 A B f)). Qed.
Lemma lem4408933 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem4408932 A B f g). Qed.
Lemma lem4408934 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = ((f = g) = (term3 A B f g)).
Proof. exact (eq_refl (term2 A B f g)). Qed.
Lemma lem4408936 {A : Type'} (x : A) : term4 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem4408937 {A : Type'} (x : A) : (term4 A x) = (term5 A x).
Proof. exact (eq_refl (term4 A x)). Qed.
Lemma lem4408938 {A : Type'} (x : A) : term5 A x.
Proof. exact (EQ_MP (@lem4408937 A x) (@lem4408936 A x)). Qed.
Lemma lem4408939 {A : Type'} (x : A) (y : A) : term6 A x y.
Proof. exact (@lem4408938 A x y). Qed.
Lemma lem4408940 {A : Type'} (x : A) (y : A) : (term6 A x y) = ((term7 A x y) = (x = y)).
Proof. exact (eq_refl (term6 A x y)). Qed.
Lemma lem4408966 {_83095 : Type'} : term8 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4408967 {_83095 : Type'} (p : _83095 -> Prop) : term9 _83095 p.
Proof. exact (@lem4408966 _83095 p). Qed.
Lemma lem4408968 {_83095 : Type'} (p : _83095 -> Prop) : (term9 _83095 p) = (term10 _83095 p).
Proof. exact (eq_refl (term9 _83095 p)). Qed.
Lemma lem4408969 {_83095 : Type'} (p : _83095 -> Prop) : term10 _83095 p.
Proof. exact (EQ_MP (@lem4408968 _83095 p) (@lem4408967 _83095 p)). Qed.
Lemma lem4408970 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term11 _83095 p x.
Proof. exact (@lem4408969 _83095 p x). Qed.
Lemma lem4408971 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term11 _83095 p x) = ((term12 _83095 x p) = (p x)).
Proof. exact (eq_refl (term11 _83095 p x)). Qed.
Lemma lem4408980 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4408981 {A : Type'} (s : A -> Prop) : (term13 A s) = (term14 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem4408982 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (EQ_MP (@lem4408981 A s) (@lem4408980 A s)). Qed.
Lemma lem4408983 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term15 A s t.
Proof. exact (@lem4408982 A s t). Qed.
Lemma lem4408984 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term15 A s t) = ((s = t) = (term16 A s t)).
Proof. exact (eq_refl (term15 A s t)). Qed.
Lemma lem4408986 {A : Type'} (x : A) : term17 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4408987 {A : Type'} (x : A) : (term17 A x) = (term18 A x).
Proof. exact (eq_refl (term17 A x)). Qed.
Lemma lem4408988 {A : Type'} (x : A) : term18 A x.
Proof. exact (EQ_MP (@lem4408987 A x) (@lem4408986 A x)). Qed.
Lemma lem4408989 {A : Type'} (x : A) : term19 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4408991 {A K : Type'} (k : K -> Prop) : term20 A K k.
Proof. exact (@lem4403516 A K k). Qed.
Lemma lem4408992 {A K : Type'} (k : K -> Prop) : (term20 A K k) = (term21 A K k).
Proof. exact (eq_refl (term20 A K k)). Qed.
Lemma lem4408993 {A K : Type'} (k : K -> Prop) : term21 A K k.
Proof. exact (EQ_MP (@lem4408992 A K k) (@lem4408991 A K k)). Qed.
Lemma lem4408994 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term22 A K k s.
Proof. exact (@lem4408993 A K k s). Qed.
Lemma lem4408995 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term22 A K k s) = ((@cartesian_product A K k s) = (term23 A K k s)).
Proof. exact (eq_refl (term22 A K k s)). Qed.
Lemma lem4409004 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term16 A s t).
Proof. exact (EQ_MP (@lem4408984 A s t) (@lem4408983 A s t)). Qed.
Lemma lem4409005 {_106081 _106082 : Type'} (s : type805 _106081 _106082) (t : type805 _106081 _106082) : (s = t) = (term24 _106081 _106082 s t).
Proof. exact (@lem4409004 (_106082 -> _106081) s t). Qed.
Lemma lem4409006 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) : ((@cartesian_product _106081 _106082 (@EMPTY _106082) s) = (term25 _106081 _106082)) = (term26 _106081 _106082 s).
Proof. exact (@lem4409005 _106081 _106082 (@cartesian_product _106081 _106082 (@EMPTY _106082) s) (term25 _106081 _106082)). Qed.
Lemma lem4409016 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term23 A K k s).
Proof. exact (EQ_MP (@lem4408995 A K k s) (@lem4408994 A K k s)). Qed.
Lemma lem4409017 {_106081 _106082 : Type'} (k : _106082 -> Prop) (s : type1470 _106081 _106082) : (@cartesian_product _106081 _106082 k s) = (term23 _106081 _106082 k s).
Proof. exact (@lem4409016 _106081 _106082 k s). Qed.
Lemma lem4409018 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) : (@cartesian_product _106081 _106082 (@EMPTY _106082) s) = (term27 _106081 _106082 s).
Proof. exact (@lem4409017 _106081 _106082 (@EMPTY _106082) s). Qed.
Lemma lem4409028 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4408989 A x (@lem4408988 A x)). Qed.
Lemma lem4409029 {_106082 : Type'} (x : _106082) : (@IN _106082 x (@EMPTY _106082)) = False.
Proof. exact (@lem4409028 _106082 x). Qed.
Lemma lem4409030 {_106082 : Type'} (i : _106082) : (@IN _106082 i (@EMPTY _106082)) = False.
Proof. exact (@lem4409029 _106082 i). Qed.
Lemma lem4409031 {_106081 : Type'} : (@COND (_106081 -> Prop)) = (@COND (_106081 -> Prop)).
Proof. exact (eq_refl (@COND (_106081 -> Prop))). Qed.
Lemma lem4409032 {_106081 _106082 : Type'} (i : _106082) : (term28 _106081 _106082 i) = (@COND (_106081 -> Prop) False).
Proof. exact (MK_COMB (@lem4409031 _106081) (@lem4409030 _106082 i)). Qed.
Lemma lem4409033 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (i : _106082) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4409034 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (i : _106082) : (term29 _106081 _106082 s i) = (term30 _106081 _106082 s i).
Proof. exact (MK_COMB (@lem4409032 _106081 _106082 i) (@lem4409033 _106081 _106082 s i)). Qed.
Lemma lem4409035 {_106081 : Type'} : (@INSERT _106081 (@ARB _106081) (@EMPTY _106081)) = (@INSERT _106081 (@ARB _106081) (@EMPTY _106081)).
Proof. exact (eq_refl (@INSERT _106081 (@ARB _106081) (@EMPTY _106081))). Qed.
Lemma lem4409036 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (i : _106082) : (term31 _106081 _106082 s i) = (term32 _106081 _106082 s i).
Proof. exact (MK_COMB (@lem4409034 _106081 _106082 s i) (@lem4409035 _106081)). Qed.
Lemma lem4409038 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4409039 {_106081 : Type'} (t1 : _106081 -> Prop) (t2 : _106081 -> Prop) : (@COND (_106081 -> Prop) False t1 t2) = t2.
Proof. exact (@lem4409038 (_106081 -> Prop) t1 t2). Qed.
Lemma lem4409040 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (i : _106082) : (term32 _106081 _106082 s i) = (@INSERT _106081 (@ARB _106081) (@EMPTY _106081)).
Proof. exact (@lem4409039 _106081 (s i) (@INSERT _106081 (@ARB _106081) (@EMPTY _106081))). Qed.
Lemma lem4409041 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (i : _106082) : (term31 _106081 _106082 s i) = (@INSERT _106081 (@ARB _106081) (@EMPTY _106081)).
Proof. exact (TRANS (@lem4409036 _106081 _106082 s i) (@lem4409040 _106081 _106082 s i)). Qed.
Lemma lem4409042 {_106081 _106082 : Type'} (f : _106082 -> _106081) (i : _106082) : (term33 _106081 _106082 f i) = (term33 _106081 _106082 f i).
Proof. exact (eq_refl (term33 _106081 _106082 f i)). Qed.
Lemma lem4409043 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (f : _106082 -> _106081) (i : _106082) : (term34 _106081 _106082 f s i) = (term35 _106081 _106082 f i).
Proof. exact (MK_COMB (@lem4409042 _106081 _106082 f i) (@lem4409041 _106081 _106082 s i)). Qed.
Lemma lem4409044 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (f : _106082 -> _106081) : (term36 _106081 _106082 f s) = (term37 _106081 _106082 f).
Proof. exact (fun_ext (fun i : _106082 => @lem4409043 _106081 _106082 s f i)). Qed.
Lemma lem4409045 {_106082 : Type'} : (@all _106082) = (@all _106082).
Proof. exact (eq_refl (@all _106082)). Qed.
Lemma lem4409046 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (f : _106082 -> _106081) : (term38 _106081 _106082 f s) = (term39 _106081 _106082 f).
Proof. exact (MK_COMB (@lem4409045 _106082) (@lem4409044 _106081 _106082 s f)). Qed.
Lemma lem4409051 {_106081 _106082 : Type'} (GEN_PVAR_141 : _106082 -> _106081) : (@SETSPEC (_106082 -> _106081) GEN_PVAR_141) = (@SETSPEC (_106082 -> _106081) GEN_PVAR_141).
Proof. exact (eq_refl (@SETSPEC (_106082 -> _106081) GEN_PVAR_141)). Qed.
Lemma lem4409052 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (GEN_PVAR_141 : _106082 -> _106081) (f : _106082 -> _106081) : (term40 _106081 _106082 GEN_PVAR_141 f s) = (term41 _106081 _106082 GEN_PVAR_141 f).
Proof. exact (MK_COMB (@lem4409051 _106081 _106082 GEN_PVAR_141) (@lem4409046 _106081 _106082 s f)). Qed.
Lemma lem4409053 {_106081 _106082 : Type'} (f : _106082 -> _106081) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4409054 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (GEN_PVAR_141 : _106082 -> _106081) (f : _106082 -> _106081) : (term42 _106081 _106082 GEN_PVAR_141 s f) = (term43 _106081 _106082 GEN_PVAR_141 f).
Proof. exact (MK_COMB (@lem4409052 _106081 _106082 s GEN_PVAR_141 f) (@lem4409053 _106081 _106082 f)). Qed.
Lemma lem4409055 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (GEN_PVAR_141 : _106082 -> _106081) : (term44 _106081 _106082 GEN_PVAR_141 s) = (term45 _106081 _106082 GEN_PVAR_141).
Proof. exact (fun_ext (fun f : _106082 -> _106081 => @lem4409054 _106081 _106082 s GEN_PVAR_141 f)). Qed.
Lemma lem4409056 {_106081 _106082 : Type'} : (@ex (_106082 -> _106081)) = (@ex (_106082 -> _106081)).
Proof. exact (eq_refl (@ex (_106082 -> _106081))). Qed.
Lemma lem4409057 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (GEN_PVAR_141 : _106082 -> _106081) : (term46 _106081 _106082 GEN_PVAR_141 s) = (term47 _106081 _106082 GEN_PVAR_141).
Proof. exact (MK_COMB (@lem4409056 _106081 _106082) (@lem4409055 _106081 _106082 s GEN_PVAR_141)). Qed.
Lemma lem4409062 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) : (term48 _106081 _106082 s) = (term49 _106081 _106082).
Proof. exact (fun_ext (fun GEN_PVAR_141 : _106082 -> _106081 => @lem4409057 _106081 _106082 s GEN_PVAR_141)). Qed.
Lemma lem4409063 {_106081 _106082 : Type'} : (@GSPEC (_106082 -> _106081)) = (@GSPEC (_106082 -> _106081)).
Proof. exact (eq_refl (@GSPEC (_106082 -> _106081))). Qed.
Lemma lem4409064 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) : (term27 _106081 _106082 s) = (term50 _106081 _106082).
Proof. exact (MK_COMB (@lem4409063 _106081 _106082) (@lem4409062 _106081 _106082 s)). Qed.
Lemma lem4409065 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) : (@cartesian_product _106081 _106082 (@EMPTY _106082) s) = (term50 _106081 _106082).
Proof. exact (TRANS (@lem4409018 _106081 _106082 s) (@lem4409064 _106081 _106082 s)). Qed.
Lemma lem4409066 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (@IN (_106082 -> _106081) x) = (@IN (_106082 -> _106081) x).
Proof. exact (eq_refl (@IN (_106082 -> _106081) x)). Qed.
Lemma lem4409067 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (x : _106082 -> _106081) : (term51 _106081 _106082 x s) = (term52 _106081 _106082 x).
Proof. exact (MK_COMB (@lem4409066 _106081 _106082 x) (@lem4409065 _106081 _106082 s)). Qed.
Lemma lem4409068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4409069 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (x : _106082 -> _106081) : (term53 _106081 _106082 x s) = (term54 _106081 _106082 x).
Proof. exact (MK_COMB (@lem4409068) (@lem4409067 _106081 _106082 s x)). Qed.
Lemma lem4409070 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term55 _106081 _106082 x) = (term55 _106081 _106082 x).
Proof. exact (eq_refl (term55 _106081 _106082 x)). Qed.
Lemma lem4409071 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) (x : _106082 -> _106081) : ((term51 _106081 _106082 x s) = (term55 _106081 _106082 x)) = ((term52 _106081 _106082 x) = (term55 _106081 _106082 x)).
Proof. exact (MK_COMB (@lem4409069 _106081 _106082 s x) (@lem4409070 _106081 _106082 x)). Qed.
Lemma lem4409076 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) : (term56 _106081 _106082 s) = (term57 _106081 _106082).
Proof. exact (fun_ext (fun x : _106082 -> _106081 => @lem4409071 _106081 _106082 s x)). Qed.
Lemma lem4409077 {_106081 _106082 : Type'} : (@all (_106082 -> _106081)) = (@all (_106082 -> _106081)).
Proof. exact (eq_refl (@all (_106082 -> _106081))). Qed.
Lemma lem4409078 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) : (term26 _106081 _106082 s) = (term58 _106081 _106082).
Proof. exact (MK_COMB (@lem4409077 _106081 _106082) (@lem4409076 _106081 _106082 s)). Qed.
Lemma lem4409083 {_106081 _106082 : Type'} (s : type1470 _106081 _106082) : ((@cartesian_product _106081 _106082 (@EMPTY _106082) s) = (term25 _106081 _106082)) = (term58 _106081 _106082).
Proof. exact (TRANS (@lem4409006 _106081 _106082 s) (@lem4409078 _106081 _106082 s)). Qed.
Lemma lem4409084 {_106081 _106082 : Type'} : (term59 _106081 _106082) = (term60 _106081 _106082).
Proof. exact (fun_ext (fun s : type1470 _106081 _106082 => @lem4409083 _106081 _106082 s)). Qed.
Lemma lem4409085 {_106081 _106082 : Type'} : (@all (_106082 -> _106081 -> Prop)) = (@all (_106082 -> _106081 -> Prop)).
Proof. exact (eq_refl (@all (_106082 -> _106081 -> Prop))). Qed.
Lemma lem4409086 {_106081 _106082 : Type'} : (term61 _106081 _106082) = (term62 _106081 _106082).
Proof. exact (MK_COMB (@lem4409085 _106081 _106082) (@lem4409084 _106081 _106082)). Qed.
Lemma lem4409088 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4409089 {_106081 _106082 : Type'} (t : Prop) : (term64 _106081 _106082 t) = t.
Proof. exact (@lem4409088 (type1470 _106081 _106082) t). Qed.
Lemma lem4409090 {_106081 _106082 : Type'} : (term62 _106081 _106082) = (term58 _106081 _106082).
Proof. exact (@lem4409089 _106081 _106082 (term58 _106081 _106082)). Qed.
Lemma lem4409107 {_106081 _106082 : Type'} : (term61 _106081 _106082) = (term58 _106081 _106082).
Proof. exact (TRANS (@lem4409086 _106081 _106082) (@lem4409090 _106081 _106082)). Qed.
Lemma lem4409108 {_106081 _106082 : Type'} : (term58 _106081 _106082) = (term61 _106081 _106082).
Proof. exact (SYM (@lem4409107 _106081 _106082)). Qed.
Lemma lem4409116 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term12 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4408971 _83095 p x) (@lem4408970 _83095 p x)). Qed.
Lemma lem4409117 {_106081 _106082 : Type'} (p : type805 _106081 _106082) (x : _106082 -> _106081) : (term65 _106081 _106082 x p) = (p x).
Proof. exact (@lem4409116 (_106082 -> _106081) p x). Qed.
Lemma lem4409118 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term66 _106081 _106082 x) = (term67 _106081 _106082 x).
Proof. exact (@lem4409117 _106081 _106082 (term68 _106081 _106082) x). Qed.
Lemma lem4409119 {_106081 _106082 : Type'} (f : _106082 -> _106081) : (term67 _106081 _106082 f) = (term39 _106081 _106082 f).
Proof. exact (eq_refl (term67 _106081 _106082 f)). Qed.
Lemma lem4409120 {_106081 _106082 : Type'} (GEN_PVAR_141 : _106082 -> _106081) : (@SETSPEC (_106082 -> _106081) GEN_PVAR_141) = (@SETSPEC (_106082 -> _106081) GEN_PVAR_141).
Proof. exact (eq_refl (@SETSPEC (_106082 -> _106081) GEN_PVAR_141)). Qed.
Lemma lem4409121 {_106081 _106082 : Type'} (GEN_PVAR_141 : _106082 -> _106081) (f : _106082 -> _106081) : (term69 _106081 _106082 GEN_PVAR_141 f) = (term41 _106081 _106082 GEN_PVAR_141 f).
Proof. exact (MK_COMB (@lem4409120 _106081 _106082 GEN_PVAR_141) (@lem4409119 _106081 _106082 f)). Qed.
Lemma lem4409122 {_106081 _106082 : Type'} (f : _106082 -> _106081) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4409123 {_106081 _106082 : Type'} (GEN_PVAR_141 : _106082 -> _106081) (f : _106082 -> _106081) : (term70 _106081 _106082 GEN_PVAR_141 f) = (term43 _106081 _106082 GEN_PVAR_141 f).
Proof. exact (MK_COMB (@lem4409121 _106081 _106082 GEN_PVAR_141 f) (@lem4409122 _106081 _106082 f)). Qed.
Lemma lem4409124 {_106081 _106082 : Type'} (GEN_PVAR_141 : _106082 -> _106081) : (term71 _106081 _106082 GEN_PVAR_141) = (term45 _106081 _106082 GEN_PVAR_141).
Proof. exact (fun_ext (fun f : _106082 -> _106081 => @lem4409123 _106081 _106082 GEN_PVAR_141 f)). Qed.
Lemma lem4409125 {_106081 _106082 : Type'} : (@ex (_106082 -> _106081)) = (@ex (_106082 -> _106081)).
Proof. exact (eq_refl (@ex (_106082 -> _106081))). Qed.
Lemma lem4409126 {_106081 _106082 : Type'} (GEN_PVAR_141 : _106082 -> _106081) : (term72 _106081 _106082 GEN_PVAR_141) = (term47 _106081 _106082 GEN_PVAR_141).
Proof. exact (MK_COMB (@lem4409125 _106081 _106082) (@lem4409124 _106081 _106082 GEN_PVAR_141)). Qed.
Lemma lem4409127 {_106081 _106082 : Type'} : (term73 _106081 _106082) = (term49 _106081 _106082).
Proof. exact (fun_ext (fun GEN_PVAR_141 : _106082 -> _106081 => @lem4409126 _106081 _106082 GEN_PVAR_141)). Qed.
Lemma lem4409128 {_106081 _106082 : Type'} : (@GSPEC (_106082 -> _106081)) = (@GSPEC (_106082 -> _106081)).
Proof. exact (eq_refl (@GSPEC (_106082 -> _106081))). Qed.
Lemma lem4409129 {_106081 _106082 : Type'} : (term74 _106081 _106082) = (term50 _106081 _106082).
Proof. exact (MK_COMB (@lem4409128 _106081 _106082) (@lem4409127 _106081 _106082)). Qed.
Lemma lem4409130 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (@IN (_106082 -> _106081) x) = (@IN (_106082 -> _106081) x).
Proof. exact (eq_refl (@IN (_106082 -> _106081) x)). Qed.
Lemma lem4409131 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term66 _106081 _106082 x) = (term52 _106081 _106082 x).
Proof. exact (MK_COMB (@lem4409130 _106081 _106082 x) (@lem4409129 _106081 _106082)). Qed.
Lemma lem4409132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4409133 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term75 _106081 _106082 x) = (term54 _106081 _106082 x).
Proof. exact (MK_COMB (@lem4409132) (@lem4409131 _106081 _106082 x)). Qed.
Lemma lem4409134 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term67 _106081 _106082 x) = (term39 _106081 _106082 x).
Proof. exact (eq_refl (term67 _106081 _106082 x)). Qed.
Lemma lem4409135 {_106081 _106082 : Type'} (x : _106082 -> _106081) : ((term66 _106081 _106082 x) = (term67 _106081 _106082 x)) = ((term52 _106081 _106082 x) = (term39 _106081 _106082 x)).
Proof. exact (MK_COMB (@lem4409133 _106081 _106082 x) (@lem4409134 _106081 _106082 x)). Qed.
Lemma lem4409136 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term52 _106081 _106082 x) = (term39 _106081 _106082 x).
Proof. exact (EQ_MP (@lem4409135 _106081 _106082 x) (@lem4409118 _106081 _106082 x)). Qed.
Lemma lem4409142 {A : Type'} (x : A) (y : A) : (term7 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4408940 A x y) (@lem4408939 A x y)). Qed.
Lemma lem4409143 {_106081 : Type'} (x : _106081) (y : _106081) : (term7 _106081 x y) = (x = y).
Proof. exact (@lem4409142 _106081 x y). Qed.
Lemma lem4409144 {_106081 _106082 : Type'} (x : _106082 -> _106081) (i : _106082) : (term35 _106081 _106082 x i) = ((x i) = (@ARB _106081)).
Proof. exact (@lem4409143 _106081 (x i) (@ARB _106081)). Qed.
Lemma lem4409147 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term37 _106081 _106082 x) = (term76 _106081 _106082 x).
Proof. exact (fun_ext (fun i : _106082 => @lem4409144 _106081 _106082 x i)). Qed.
Lemma lem4409148 {_106082 : Type'} : (@all _106082) = (@all _106082).
Proof. exact (eq_refl (@all _106082)). Qed.
Lemma lem4409149 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term39 _106081 _106082 x) = (term77 _106081 _106082 x).
Proof. exact (MK_COMB (@lem4409148 _106082) (@lem4409147 _106081 _106082 x)). Qed.
Lemma lem4409154 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term52 _106081 _106082 x) = (term77 _106081 _106082 x).
Proof. exact (TRANS (@lem4409136 _106081 _106082 x) (@lem4409149 _106081 _106082 x)). Qed.
Lemma lem4409155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4409156 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term54 _106081 _106082 x) = (term78 _106081 _106082 x).
Proof. exact (MK_COMB (@lem4409155) (@lem4409154 _106081 _106082 x)). Qed.
Lemma lem4409158 {A : Type'} (x : A) (y : A) : (term7 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4408940 A x y) (@lem4408939 A x y)). Qed.
Lemma lem4409159 {_106081 _106082 : Type'} (x : _106082 -> _106081) (y : _106082 -> _106081) : (term79 _106081 _106082 x y) = (x = y).
Proof. exact (@lem4409158 (_106082 -> _106081) x y). Qed.
Lemma lem4409160 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term55 _106081 _106082 x) = (x = (term80 _106081 _106082)).
Proof. exact (@lem4409159 _106081 _106082 x (term80 _106081 _106082)). Qed.
Lemma lem4409163 {_106081 _106082 : Type'} (x : _106082 -> _106081) : ((term52 _106081 _106082 x) = (term55 _106081 _106082 x)) = ((term77 _106081 _106082 x) = (x = (term80 _106081 _106082))).
Proof. exact (MK_COMB (@lem4409156 _106081 _106082 x) (@lem4409160 _106081 _106082 x)). Qed.
Lemma lem4409166 {_106081 _106082 : Type'} : (term57 _106081 _106082) = (term81 _106081 _106082).
Proof. exact (fun_ext (fun x : _106082 -> _106081 => @lem4409163 _106081 _106082 x)). Qed.
Lemma lem4409167 {_106081 _106082 : Type'} : (@all (_106082 -> _106081)) = (@all (_106082 -> _106081)).
Proof. exact (eq_refl (@all (_106082 -> _106081))). Qed.
Lemma lem4409168 {_106081 _106082 : Type'} : (term58 _106081 _106082) = (term82 _106081 _106082).
Proof. exact (MK_COMB (@lem4409167 _106081 _106082) (@lem4409166 _106081 _106082)). Qed.
Lemma lem4409173 {_106081 _106082 : Type'} : (term82 _106081 _106082) = (term58 _106081 _106082).
Proof. exact (SYM (@lem4409168 _106081 _106082)). Qed.
Lemma lem4409193 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem4408934 A B f g) (@lem4408933 A B f g)). Qed.
Lemma lem4409194 {_106081 _106082 : Type'} (f : _106082 -> _106081) (g : _106082 -> _106081) : (f = g) = (term83 _106081 _106082 f g).
Proof. exact (@lem4409193 _106082 _106081 f g). Qed.
Lemma lem4409195 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (x = (term80 _106081 _106082)) = (term84 _106081 _106082 x).
Proof. exact (@lem4409194 _106081 _106082 x (term80 _106081 _106082)). Qed.
Lemma lem4409205 {A B : Type'} (f : A -> B) (y : A) : (term85 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4409206 {_106081 _106082 : Type'} (f : _106082 -> _106081) (y : _106082) : (term86 _106081 _106082 f y) = (f y).
Proof. exact (@lem4409205 _106082 _106081 f y). Qed.
Lemma lem4409207 {_106081 _106082 : Type'} (x : _106082) : (term87 _106081 _106082 x) = (term88 _106081 _106082 x).
Proof. exact (@lem4409206 _106081 _106082 (term80 _106081 _106082) x). Qed.
Lemma lem4409208 {_106081 _106082 : Type'} (i : _106082) : (term88 _106081 _106082 i) = (@ARB _106081).
Proof. exact (eq_refl (term88 _106081 _106082 i)). Qed.
Lemma lem4409209 {_106081 _106082 : Type'} : (term89 _106081 _106082) = (term80 _106081 _106082).
Proof. exact (fun_ext (fun i : _106082 => @lem4409208 _106081 _106082 i)). Qed.
Lemma lem4409210 {_106082 : Type'} (x : _106082) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4409211 {_106081 _106082 : Type'} (x : _106082) : (term87 _106081 _106082 x) = (term88 _106081 _106082 x).
Proof. exact (MK_COMB (@lem4409209 _106081 _106082) (@lem4409210 _106082 x)). Qed.
Lemma lem4409212 {_106081 : Type'} : (@eq _106081) = (@eq _106081).
Proof. exact (eq_refl (@eq _106081)). Qed.
Lemma lem4409213 {_106081 _106082 : Type'} (x : _106082) : (term90 _106081 _106082 x) = (term91 _106081 _106082 x).
Proof. exact (MK_COMB (@lem4409212 _106081) (@lem4409211 _106081 _106082 x)). Qed.
Lemma lem4409214 {_106081 _106082 : Type'} (x : _106082) : (term88 _106081 _106082 x) = (@ARB _106081).
Proof. exact (eq_refl (term88 _106081 _106082 x)). Qed.
Lemma lem4409215 {_106081 _106082 : Type'} (x : _106082) : ((term87 _106081 _106082 x) = (term88 _106081 _106082 x)) = ((term88 _106081 _106082 x) = (@ARB _106081)).
Proof. exact (MK_COMB (@lem4409213 _106081 _106082 x) (@lem4409214 _106081 _106082 x)). Qed.
Lemma lem4409216 {_106081 _106082 : Type'} (x : _106082) : (term88 _106081 _106082 x) = (@ARB _106081).
Proof. exact (EQ_MP (@lem4409215 _106081 _106082 x) (@lem4409207 _106081 _106082 x)). Qed.
Lemma lem4409217 {_106081 _106082 : Type'} (x : _106082 -> _106081) (x' : _106082) : (term92 _106081 _106082 x x') = (term92 _106081 _106082 x x').
Proof. exact (eq_refl (term92 _106081 _106082 x x')). Qed.
Lemma lem4409218 {_106081 _106082 : Type'} (x : _106082 -> _106081) (x' : _106082) : ((x x') = (term88 _106081 _106082 x')) = ((x x') = (@ARB _106081)).
Proof. exact (MK_COMB (@lem4409217 _106081 _106082 x x') (@lem4409216 _106081 _106082 x')). Qed.
Lemma lem4409223 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term93 _106081 _106082 x) = (term76 _106081 _106082 x).
Proof. exact (fun_ext (fun x' : _106082 => @lem4409218 _106081 _106082 x x')). Qed.
Lemma lem4409224 {_106082 : Type'} : (@all _106082) = (@all _106082).
Proof. exact (eq_refl (@all _106082)). Qed.
Lemma lem4409225 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term84 _106081 _106082 x) = (term77 _106081 _106082 x).
Proof. exact (MK_COMB (@lem4409224 _106082) (@lem4409223 _106081 _106082 x)). Qed.
Lemma lem4409230 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (x = (term80 _106081 _106082)) = (term77 _106081 _106082 x).
Proof. exact (TRANS (@lem4409195 _106081 _106082 x) (@lem4409225 _106081 _106082 x)). Qed.
Lemma lem4409231 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term78 _106081 _106082 x) = (term78 _106081 _106082 x).
Proof. exact (eq_refl (term78 _106081 _106082 x)). Qed.
Lemma lem4409232 {_106081 _106082 : Type'} (x : _106082 -> _106081) : ((term77 _106081 _106082 x) = (x = (term80 _106081 _106082))) = ((term77 _106081 _106082 x) = (term77 _106081 _106082 x)).
Proof. exact (MK_COMB (@lem4409231 _106081 _106082 x) (@lem4409230 _106081 _106082 x)). Qed.
Lemma lem4409234 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4409235 (x : Prop) : (x = x) = True.
Proof. exact (@lem4409234 Prop x). Qed.
Lemma lem4409236 {_106081 _106082 : Type'} (x : _106082 -> _106081) : ((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True.
Proof. exact (@lem4409235 (term77 _106081 _106082 x)). Qed.
Lemma lem4409239 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term94 _106081 _106082 x) = (term94 _106081 _106082 x).
Proof. exact (eq_refl (term94 _106081 _106082 x)). Qed.
Lemma lem4409240 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term94 _106081 _106082 x) = (((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True).
Proof. exact (eq_refl (term94 _106081 _106082 x)). Qed.
Lemma lem4409241 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term95 _106081 _106082 x) = (term95 _106081 _106082 x).
Proof. exact (eq_refl (term95 _106081 _106082 x)). Qed.
Lemma lem4409242 {_106081 _106082 : Type'} (x : _106082 -> _106081) : ((term94 _106081 _106082 x) = (term94 _106081 _106082 x)) = ((term94 _106081 _106082 x) = (((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True)).
Proof. exact (MK_COMB (@lem4409241 _106081 _106082 x) (@lem4409240 _106081 _106082 x)). Qed.
Lemma lem4409243 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term94 _106081 _106082 x) = (((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True).
Proof. exact (eq_refl (term94 _106081 _106082 x)). Qed.
Lemma lem4409244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4409245 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (term95 _106081 _106082 x) = (term96 _106081 _106082 x).
Proof. exact (MK_COMB (@lem4409244) (@lem4409243 _106081 _106082 x)). Qed.
Lemma lem4409246 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True) = (((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True).
Proof. exact (eq_refl (((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True)). Qed.
Lemma lem4409247 {_106081 _106082 : Type'} (x : _106082 -> _106081) : ((term94 _106081 _106082 x) = (((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True)) = ((((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True) = (((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True)).
Proof. exact (MK_COMB (@lem4409245 _106081 _106082 x) (@lem4409246 _106081 _106082 x)). Qed.
Lemma lem4409248 {_106081 _106082 : Type'} (x : _106082 -> _106081) : ((term94 _106081 _106082 x) = (term94 _106081 _106082 x)) = ((((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True) = (((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True)).
Proof. exact (TRANS (@lem4409242 _106081 _106082 x) (@lem4409247 _106081 _106082 x)). Qed.
Lemma lem4409249 {_106081 _106082 : Type'} (x : _106082 -> _106081) : (((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True) = (((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True).
Proof. exact (EQ_MP (@lem4409248 _106081 _106082 x) (@lem4409239 _106081 _106082 x)). Qed.
Lemma lem4409250 {_106081 _106082 : Type'} (x : _106082 -> _106081) : ((term77 _106081 _106082 x) = (term77 _106081 _106082 x)) = True.
Proof. exact (EQ_MP (@lem4409249 _106081 _106082 x) (@lem4409236 _106081 _106082 x)). Qed.
Lemma lem4409251 {_106081 _106082 : Type'} (x : _106082 -> _106081) : ((term77 _106081 _106082 x) = (x = (term80 _106081 _106082))) = True.
Proof. exact (TRANS (@lem4409232 _106081 _106082 x) (@lem4409250 _106081 _106082 x)). Qed.
Lemma lem4409252 {_106081 _106082 : Type'} : (term81 _106081 _106082) = (term97 _106081 _106082).
Proof. exact (fun_ext (fun x : _106082 -> _106081 => @lem4409251 _106081 _106082 x)). Qed.
Lemma lem4409253 {_106081 _106082 : Type'} : (@all (_106082 -> _106081)) = (@all (_106082 -> _106081)).
Proof. exact (eq_refl (@all (_106082 -> _106081))). Qed.
Lemma lem4409254 {_106081 _106082 : Type'} : (term82 _106081 _106082) = (term98 _106081 _106082).
Proof. exact (MK_COMB (@lem4409253 _106081 _106082) (@lem4409252 _106081 _106082)). Qed.
Lemma lem4409256 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4409257 {_106081 _106082 : Type'} (t : Prop) : (term99 _106081 _106082 t) = t.
Proof. exact (@lem4409256 (_106082 -> _106081) t). Qed.
Lemma lem4409258 {_106081 _106082 : Type'} : (term98 _106081 _106082) = True.
Proof. exact (@lem4409257 _106081 _106082 True). Qed.
Lemma lem4409259 {_106081 _106082 : Type'} : (term82 _106081 _106082) = True.
Proof. exact (TRANS (@lem4409254 _106081 _106082) (@lem4409258 _106081 _106082)). Qed.
Lemma lem4409260 {_106081 _106082 : Type'} : True = (term82 _106081 _106082).
Proof. exact (SYM (@lem4409259 _106081 _106082)). Qed.
Lemma lem4409261 {_106081 _106082 : Type'} : term82 _106081 _106082.
Proof. exact (EQ_MP (@lem4409260 _106081 _106082) (@lem0)). Qed.
Lemma lem4409262 {_106081 _106082 : Type'} : term58 _106081 _106082.
Proof. exact (EQ_MP (@lem4409173 _106081 _106082) (@lem4409261 _106081 _106082)). Qed.
Lemma lem4409263 {_106081 _106082 : Type'} : term61 _106081 _106082.
Proof. exact (EQ_MP (@lem4409108 _106081 _106082) (@lem4409262 _106081 _106082)). Qed.
