Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_CASES_term_abbrevs.
Require Import EQ_TRANS_spec.
Require Import FINITE_RESTRICT_spec.
Require Import ITERATE_EQ_spec.
Require Import ITERATE_UNION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211738_spec.
Require Import thm3211739_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem6158424 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem6158425 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem6158424 _83095 p). Qed.
Lemma lem6158426 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem6158427 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem6158426 _83095 p) (@lem6158425 _83095 p)). Qed.
Lemma lem6158428 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem6158427 _83095 p x). Qed.
Lemma lem6158429 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem6158438 {A B : Type'} (op : type1400 B) : term5 A B op.
Proof. exact (@lem5985778 A B op). Qed.
Lemma lem6158439 {A B : Type'} (op : type1400 B) : (term5 A B op) = (term6 A B op).
Proof. exact (eq_refl (term5 A B op)). Qed.
Lemma lem6158451 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem6158452 {A : Type'} (x : A) (h1 : term7 A) : term8 A x.
Proof. exact (@lem6158451 A h1 x). Qed.
Lemma lem6158453 {A : Type'} (x : A) : (term8 A x) = (term9 A x).
Proof. exact (eq_refl (term8 A x)). Qed.
Lemma lem6158454 {A : Type'} (x : A) (h1 : term7 A) : term9 A x.
Proof. exact (EQ_MP (@lem6158453 A x) (@lem6158452 A x h1)). Qed.
Lemma lem6158455 {A : Type'} (x : A) (y : A) (h1 : term7 A) : term10 A x y.
Proof. exact (@lem6158454 A x h1 y). Qed.
Lemma lem6158456 {A : Type'} (y : A) (x : A) : (term10 A x y) = (term11 A y x).
Proof. exact (eq_refl (term10 A x y)). Qed.
Lemma lem6158457 {A : Type'} (y : A) (x : A) (h1 : term7 A) : term11 A y x.
Proof. exact (EQ_MP (@lem6158456 A y x) (@lem6158455 A x y h1)). Qed.
Lemma lem6158458 {A : Type'} (y : A) (x : A) (z : A) (h1 : term7 A) : term12 A y x z.
Proof. exact (@lem6158457 A y x h1 z). Qed.
Lemma lem6158459 {A : Type'} (y : A) (x : A) (z : A) : (term12 A y x z) = (term13 A y x z).
Proof. exact (eq_refl (term12 A y x z)). Qed.
Lemma lem6158460 {A : Type'} (y : A) (x : A) (z : A) (h1 : term7 A) : term13 A y x z.
Proof. exact (EQ_MP (@lem6158459 A y x z) (@lem6158458 A y x z h1)). Qed.
Lemma lem6158461 {A : Type'} (x : A) (y : A) (z : A) (h1 : term14 A x y z) : term14 A x y z.
Proof. exact (h1). Qed.
Lemma lem6158462 {A : Type'} (x : A) (y : A) (z : A) (h1 : term7 A) (h2 : term14 A x y z) : x = z.
Proof. exact (@lem6158460 A y x z h1 (@lem6158461 A x y z h2)). Qed.
Lemma lem6158463 {A : Type'} (x : A) (y : A) (z : A) (h1 : term14 A x y z) : term15 A x z.
Proof. exact (fun h0 : term7 A => @lem6158462 A x y z h0 h1). Qed.
Lemma lem6158464 {A : Type'} (x : A) (z : A) (h1 : term16 A x z) : term16 A x z.
Proof. exact (h1). Qed.
Lemma lem6158465 {A : Type'} (x : A) (z : A) (h1 : term16 A x z) : term15 A x z.
Proof. exact (ex_elim (@lem6158464 A x z h1) (fun y : A => fun h0 : term17 A x z y => @lem6158463 A x y z h0)). Qed.
Lemma lem6158466 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem6158467 {A : Type'} (x : A) (z : A) (h1 : term7 A) (h2 : term16 A x z) : x = z.
Proof. exact (@lem6158465 A x z h2 (@lem6158466 A h1)). Qed.
Lemma lem6158468 {A : Type'} (x : A) (z : A) (h1 : term7 A) : term18 A x z.
Proof. exact (fun h0 : term16 A x z => @lem6158467 A x z h1 h0). Qed.
Lemma lem6158469 {A : Type'} (x : A) (h1 : term7 A) : term19 A x.
Proof. exact (fun z : A => @lem6158468 A x z h1). Qed.
Lemma lem6158470 {A : Type'} (h1 : term7 A) : term20 A.
Proof. exact (fun x : A => @lem6158469 A x h1). Qed.
Lemma lem6158471 {A : Type'} : term21 A.
Proof. exact (fun h0 : term7 A => @lem6158470 A h0). Qed.
Lemma lem6158472 {A : Type'} : term20 A.
Proof. exact (@lem6158471 A (@lem403 A)). Qed.
Lemma lem6158473 {A : Type'} (x : A) : term22 A x.
Proof. exact (@lem6158472 A x). Qed.
Lemma lem6158474 {A : Type'} (x : A) : (term22 A x) = (term19 A x).
Proof. exact (eq_refl (term22 A x)). Qed.
Lemma lem6158475 {A : Type'} (x : A) : term19 A x.
Proof. exact (EQ_MP (@lem6158474 A x) (@lem6158473 A x)). Qed.
Lemma lem6158476 {A : Type'} (x : A) (z : A) : term23 A x z.
Proof. exact (@lem6158475 A x z). Qed.
Lemma lem6158477 {A : Type'} (x : A) (z : A) : (term23 A x z) = (term18 A x z).
Proof. exact (eq_refl (term23 A x z)). Qed.
Lemma lem6158479 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6158480 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6158482 {A : Type'} (x : A) (z : A) : term18 A x z.
Proof. exact (EQ_MP (@lem6158477 A x z) (@lem6158476 A x z)). Qed.
Lemma lem6158483 {B : Type'} (x : B) (z : B) : term18 B x z.
Proof. exact (@lem6158482 B x z). Qed.
Lemma lem6158484 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) : term24 A B f op s P g.
Proof. exact (@lem6158483 B (term25 A B op s P f g) (term26 A B f op s P g)). Qed.
Lemma lem6158907 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem6158908 {_123260 : Type'} (s : _123260 -> Prop) (t : _123260 -> Prop) : (@DISJOINT _123260 s t) = ((@INTER _123260 s t) = (@EMPTY _123260)).
Proof. exact (@lem6158907 _123260 s t). Qed.
Lemma lem6158909 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term27 _123260 s P) = ((term28 _123260 s P) = (@EMPTY _123260)).
Proof. exact (@lem6158908 _123260 (term29 _123260 s P) (term30 _123260 s P)). Qed.
Lemma lem6158913 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term31 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem6158914 {_123260 : Type'} (s : _123260 -> Prop) (t : _123260 -> Prop) : (s = t) = (term31 _123260 s t).
Proof. exact (@lem6158913 _123260 s t). Qed.
Lemma lem6158915 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : ((term28 _123260 s P) = (@EMPTY _123260)) = (term32 _123260 s P).
Proof. exact (@lem6158914 _123260 (term28 _123260 s P) (@EMPTY _123260)). Qed.
Lemma lem6158920 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term27 _123260 s P) = (term32 _123260 s P).
Proof. exact (TRANS (@lem6158909 _123260 s P) (@lem6158915 _123260 s P)). Qed.
Lemma lem6158937 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term32 _123260 s P) = (term27 _123260 s P).
Proof. exact (SYM (@lem6158920 _123260 s P)). Qed.
Lemma lem6158945 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term33 A x s t) = (term34 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem6158946 {_123260 : Type'} (s : _123260 -> Prop) (x : _123260) (t : _123260 -> Prop) : (term33 _123260 x s t) = (term34 _123260 s x t).
Proof. exact (@lem6158945 _123260 s x t). Qed.
Lemma lem6158947 {_123260 : Type'} (x : _123260) (s : _123260 -> Prop) (P : _123260 -> Prop) : (term35 _123260 x s P) = (term36 _123260 x s P).
Proof. exact (@lem6158946 _123260 (term29 _123260 s P) x (term30 _123260 s P)). Qed.
Lemma lem6158951 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem6158952 {_123260 : Type'} (p : _123260 -> Prop) (x : _123260) : (term4 _123260 x p) = (p x).
Proof. exact (@lem6158951 _123260 p x). Qed.
Lemma lem6158953 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term37 _123260 x s P) = (term38 _123260 s P x).
Proof. exact (@lem6158952 _123260 (term39 _123260 s P) x). Qed.
Lemma lem6158954 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term38 _123260 s P x) = (term40 _123260 s P x).
Proof. exact (eq_refl (term38 _123260 s P x)). Qed.
Lemma lem6158955 {_123260 : Type'} (GEN_PVAR_252 : _123260) : (@SETSPEC _123260 GEN_PVAR_252) = (@SETSPEC _123260 GEN_PVAR_252).
Proof. exact (eq_refl (@SETSPEC _123260 GEN_PVAR_252)). Qed.
Lemma lem6158956 {_123260 : Type'} (GEN_PVAR_252 : _123260) (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term41 _123260 GEN_PVAR_252 s P x) = (term42 _123260 GEN_PVAR_252 s P x).
Proof. exact (MK_COMB (@lem6158955 _123260 GEN_PVAR_252) (@lem6158954 _123260 s P x)). Qed.
Lemma lem6158957 {_123260 : Type'} (x : _123260) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6158958 {_123260 : Type'} (GEN_PVAR_252 : _123260) (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term43 _123260 GEN_PVAR_252 s P x) = (term44 _123260 GEN_PVAR_252 s P x).
Proof. exact (MK_COMB (@lem6158956 _123260 GEN_PVAR_252 s P x) (@lem6158957 _123260 x)). Qed.
Lemma lem6158959 {_123260 : Type'} (GEN_PVAR_252 : _123260) (s : _123260 -> Prop) (P : _123260 -> Prop) : (term45 _123260 GEN_PVAR_252 s P) = (term46 _123260 GEN_PVAR_252 s P).
Proof. exact (fun_ext (fun x : _123260 => @lem6158958 _123260 GEN_PVAR_252 s P x)). Qed.
Lemma lem6158960 {_123260 : Type'} : (@ex _123260) = (@ex _123260).
Proof. exact (eq_refl (@ex _123260)). Qed.
Lemma lem6158961 {_123260 : Type'} (GEN_PVAR_252 : _123260) (s : _123260 -> Prop) (P : _123260 -> Prop) : (term47 _123260 GEN_PVAR_252 s P) = (term48 _123260 GEN_PVAR_252 s P).
Proof. exact (MK_COMB (@lem6158960 _123260) (@lem6158959 _123260 GEN_PVAR_252 s P)). Qed.
Lemma lem6158962 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term49 _123260 s P) = (term50 _123260 s P).
Proof. exact (fun_ext (fun GEN_PVAR_252 : _123260 => @lem6158961 _123260 GEN_PVAR_252 s P)). Qed.
Lemma lem6158963 {_123260 : Type'} : (@GSPEC _123260) = (@GSPEC _123260).
Proof. exact (eq_refl (@GSPEC _123260)). Qed.
Lemma lem6158964 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term51 _123260 s P) = (term29 _123260 s P).
Proof. exact (MK_COMB (@lem6158963 _123260) (@lem6158962 _123260 s P)). Qed.
Lemma lem6158965 {_123260 : Type'} (x : _123260) : (@IN _123260 x) = (@IN _123260 x).
Proof. exact (eq_refl (@IN _123260 x)). Qed.
Lemma lem6158966 {_123260 : Type'} (x : _123260) (s : _123260 -> Prop) (P : _123260 -> Prop) : (term37 _123260 x s P) = (term52 _123260 x s P).
Proof. exact (MK_COMB (@lem6158965 _123260 x) (@lem6158964 _123260 s P)). Qed.
Lemma lem6158967 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6158968 {_123260 : Type'} (x : _123260) (s : _123260 -> Prop) (P : _123260 -> Prop) : (term53 _123260 x s P) = (term54 _123260 x s P).
Proof. exact (MK_COMB (@lem6158967) (@lem6158966 _123260 x s P)). Qed.
Lemma lem6158969 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term38 _123260 s P x) = (term40 _123260 s P x).
Proof. exact (eq_refl (term38 _123260 s P x)). Qed.
Lemma lem6158970 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : ((term37 _123260 x s P) = (term38 _123260 s P x)) = ((term52 _123260 x s P) = (term40 _123260 s P x)).
Proof. exact (MK_COMB (@lem6158968 _123260 x s P) (@lem6158969 _123260 s P x)). Qed.
Lemma lem6158971 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term52 _123260 x s P) = (term40 _123260 s P x).
Proof. exact (EQ_MP (@lem6158970 _123260 s P x) (@lem6158953 _123260 s P x)). Qed.
Lemma lem6158975 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6158976 {_123260 : Type'} (P : _123260 -> Prop) (x : _123260) : (@IN _123260 x P) = (P x).
Proof. exact (@lem6158975 _123260 P x). Qed.
Lemma lem6158977 {_123260 : Type'} (s : _123260 -> Prop) (x : _123260) : (@IN _123260 x s) = (s x).
Proof. exact (@lem6158976 _123260 s x). Qed.
Lemma lem6158978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6158979 {_123260 : Type'} (s : _123260 -> Prop) (x : _123260) : (term55 _123260 x s) = (term56 _123260 s x).
Proof. exact (MK_COMB (@lem6158978) (@lem6158977 _123260 s x)). Qed.
Lemma lem6158980 {_123260 : Type'} (P : _123260 -> Prop) (x : _123260) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem6158981 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term40 _123260 s P x) = (term57 _123260 s P x).
Proof. exact (MK_COMB (@lem6158979 _123260 s x) (@lem6158980 _123260 P x)). Qed.
Lemma lem6158984 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term52 _123260 x s P) = (term57 _123260 s P x).
Proof. exact (TRANS (@lem6158971 _123260 s P x) (@lem6158981 _123260 s P x)). Qed.
Lemma lem6158985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6158986 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term58 _123260 x s P) = (term59 _123260 s P x).
Proof. exact (MK_COMB (@lem6158985) (@lem6158984 _123260 s P x)). Qed.
Lemma lem6158988 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem6158989 {_123260 : Type'} (p : _123260 -> Prop) (x : _123260) : (term4 _123260 x p) = (p x).
Proof. exact (@lem6158988 _123260 p x). Qed.
Lemma lem6158990 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term60 _123260 x s P) = (term61 _123260 s P x).
Proof. exact (@lem6158989 _123260 (term62 _123260 s P) x). Qed.
Lemma lem6158991 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term61 _123260 s P x) = (term63 _123260 s P x).
Proof. exact (eq_refl (term61 _123260 s P x)). Qed.
Lemma lem6158992 {_123260 : Type'} (GEN_PVAR_253 : _123260) : (@SETSPEC _123260 GEN_PVAR_253) = (@SETSPEC _123260 GEN_PVAR_253).
Proof. exact (eq_refl (@SETSPEC _123260 GEN_PVAR_253)). Qed.
Lemma lem6158993 {_123260 : Type'} (GEN_PVAR_253 : _123260) (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term64 _123260 GEN_PVAR_253 s P x) = (term65 _123260 GEN_PVAR_253 s P x).
Proof. exact (MK_COMB (@lem6158992 _123260 GEN_PVAR_253) (@lem6158991 _123260 s P x)). Qed.
Lemma lem6158994 {_123260 : Type'} (x : _123260) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6158995 {_123260 : Type'} (GEN_PVAR_253 : _123260) (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term66 _123260 GEN_PVAR_253 s P x) = (term67 _123260 GEN_PVAR_253 s P x).
Proof. exact (MK_COMB (@lem6158993 _123260 GEN_PVAR_253 s P x) (@lem6158994 _123260 x)). Qed.
Lemma lem6158996 {_123260 : Type'} (GEN_PVAR_253 : _123260) (s : _123260 -> Prop) (P : _123260 -> Prop) : (term68 _123260 GEN_PVAR_253 s P) = (term69 _123260 GEN_PVAR_253 s P).
Proof. exact (fun_ext (fun x : _123260 => @lem6158995 _123260 GEN_PVAR_253 s P x)). Qed.
Lemma lem6158997 {_123260 : Type'} : (@ex _123260) = (@ex _123260).
Proof. exact (eq_refl (@ex _123260)). Qed.
Lemma lem6158998 {_123260 : Type'} (GEN_PVAR_253 : _123260) (s : _123260 -> Prop) (P : _123260 -> Prop) : (term70 _123260 GEN_PVAR_253 s P) = (term71 _123260 GEN_PVAR_253 s P).
Proof. exact (MK_COMB (@lem6158997 _123260) (@lem6158996 _123260 GEN_PVAR_253 s P)). Qed.
Lemma lem6158999 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term72 _123260 s P) = (term73 _123260 s P).
Proof. exact (fun_ext (fun GEN_PVAR_253 : _123260 => @lem6158998 _123260 GEN_PVAR_253 s P)). Qed.
Lemma lem6159000 {_123260 : Type'} : (@GSPEC _123260) = (@GSPEC _123260).
Proof. exact (eq_refl (@GSPEC _123260)). Qed.
Lemma lem6159001 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term74 _123260 s P) = (term30 _123260 s P).
Proof. exact (MK_COMB (@lem6159000 _123260) (@lem6158999 _123260 s P)). Qed.
Lemma lem6159002 {_123260 : Type'} (x : _123260) : (@IN _123260 x) = (@IN _123260 x).
Proof. exact (eq_refl (@IN _123260 x)). Qed.
Lemma lem6159003 {_123260 : Type'} (x : _123260) (s : _123260 -> Prop) (P : _123260 -> Prop) : (term60 _123260 x s P) = (term75 _123260 x s P).
Proof. exact (MK_COMB (@lem6159002 _123260 x) (@lem6159001 _123260 s P)). Qed.
Lemma lem6159004 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6159005 {_123260 : Type'} (x : _123260) (s : _123260 -> Prop) (P : _123260 -> Prop) : (term76 _123260 x s P) = (term77 _123260 x s P).
Proof. exact (MK_COMB (@lem6159004) (@lem6159003 _123260 x s P)). Qed.
Lemma lem6159006 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term61 _123260 s P x) = (term63 _123260 s P x).
Proof. exact (eq_refl (term61 _123260 s P x)). Qed.
Lemma lem6159007 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : ((term60 _123260 x s P) = (term61 _123260 s P x)) = ((term75 _123260 x s P) = (term63 _123260 s P x)).
Proof. exact (MK_COMB (@lem6159005 _123260 x s P) (@lem6159006 _123260 s P x)). Qed.
Lemma lem6159008 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term75 _123260 x s P) = (term63 _123260 s P x).
Proof. exact (EQ_MP (@lem6159007 _123260 s P x) (@lem6158990 _123260 s P x)). Qed.
Lemma lem6159012 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6159013 {_123260 : Type'} (P : _123260 -> Prop) (x : _123260) : (@IN _123260 x P) = (P x).
Proof. exact (@lem6159012 _123260 P x). Qed.
Lemma lem6159014 {_123260 : Type'} (s : _123260 -> Prop) (x : _123260) : (@IN _123260 x s) = (s x).
Proof. exact (@lem6159013 _123260 s x). Qed.
Lemma lem6159015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6159016 {_123260 : Type'} (s : _123260 -> Prop) (x : _123260) : (term55 _123260 x s) = (term56 _123260 s x).
Proof. exact (MK_COMB (@lem6159015) (@lem6159014 _123260 s x)). Qed.
Lemma lem6159017 {_123260 : Type'} (P : _123260 -> Prop) (x : _123260) : (term78 _123260 P x) = (term78 _123260 P x).
Proof. exact (eq_refl (term78 _123260 P x)). Qed.
Lemma lem6159018 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term63 _123260 s P x) = (term79 _123260 s P x).
Proof. exact (MK_COMB (@lem6159016 _123260 s x) (@lem6159017 _123260 P x)). Qed.
Lemma lem6159021 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term75 _123260 x s P) = (term79 _123260 s P x).
Proof. exact (TRANS (@lem6159008 _123260 s P x) (@lem6159018 _123260 s P x)). Qed.
Lemma lem6159022 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term36 _123260 x s P) = (term80 _123260 s P x).
Proof. exact (MK_COMB (@lem6158986 _123260 s P x) (@lem6159021 _123260 s P x)). Qed.
Lemma lem6159025 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term35 _123260 x s P) = (term80 _123260 s P x).
Proof. exact (TRANS (@lem6158947 _123260 x s P) (@lem6159022 _123260 s P x)). Qed.
Lemma lem6159026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6159027 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term81 _123260 x s P) = (term82 _123260 s P x).
Proof. exact (MK_COMB (@lem6159026) (@lem6159025 _123260 s P x)). Qed.
Lemma lem6159029 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem6159030 {_123260 : Type'} (x : _123260) : (@IN _123260 x (@EMPTY _123260)) = False.
Proof. exact (@lem6159029 _123260 x). Qed.
Lemma lem6159031 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : ((term35 _123260 x s P) = (@IN _123260 x (@EMPTY _123260))) = ((term80 _123260 s P x) = False).
Proof. exact (MK_COMB (@lem6159027 _123260 s P x) (@lem6159030 _123260 x)). Qed.
Lemma lem6159033 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem6159034 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : ((term80 _123260 s P x) = False) = (term83 _123260 s P x).
Proof. exact (@lem6159033 (term80 _123260 s P x)). Qed.
Lemma lem6159041 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : ((term35 _123260 x s P) = (@IN _123260 x (@EMPTY _123260))) = (term83 _123260 s P x).
Proof. exact (TRANS (@lem6159031 _123260 s P x) (@lem6159034 _123260 s P x)). Qed.
Lemma lem6159042 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term84 _123260 s P) = (term85 _123260 s P).
Proof. exact (fun_ext (fun x : _123260 => @lem6159041 _123260 s P x)). Qed.
Lemma lem6159043 {_123260 : Type'} : (@all _123260) = (@all _123260).
Proof. exact (eq_refl (@all _123260)). Qed.
Lemma lem6159044 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term32 _123260 s P) = (term86 _123260 s P).
Proof. exact (MK_COMB (@lem6159043 _123260) (@lem6159042 _123260 s P)). Qed.
Lemma lem6159049 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term86 _123260 s P) = (term32 _123260 s P).
Proof. exact (SYM (@lem6159044 _123260 s P)). Qed.
Lemma lem6159051 (p : Prop) : p = (term87 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6159052 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term86 _123260 s P) = (term88 _123260 s P).
Proof. exact (@lem6159051 (term86 _123260 s P)). Qed.
Lemma lem6159053 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term88 _123260 s P) = (term86 _123260 s P).
Proof. exact (SYM (@lem6159052 _123260 s P)). Qed.
Lemma lem6159054 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (h1 : term89 _123260 s P) : term89 _123260 s P.
Proof. exact (h1). Qed.
Lemma lem6159057 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (h1 : term88 _123260 s P) : term88 _123260 s P.
Proof. exact (h1). Qed.
Lemma lem6159058 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : term90 _123260 s P.
Proof. exact (fun h0 : term88 _123260 s P => @lem6159057 _123260 s P h0). Qed.
Lemma lem6159059 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (h1 : term90 _123260 s P) : term90 _123260 s P.
Proof. exact (h1). Qed.
Lemma lem6159060 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (h1 : term88 _123260 s P) : term88 _123260 s P.
Proof. exact (h1). Qed.
Lemma lem6159061 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (h1 : term88 _123260 s P) (h2 : term90 _123260 s P) : term88 _123260 s P.
Proof. exact (@lem6159059 _123260 s P h2 (@lem6159060 _123260 s P h1)). Qed.
Lemma lem6159062 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (h1 : term88 _123260 s P) : term91 _123260 s P.
Proof. exact (fun h0 : term90 _123260 s P => @lem6159061 _123260 s P h1 h0). Qed.
Lemma lem6159063 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (h1 : term90 _123260 s P) : term90 _123260 s P.
Proof. exact (h1). Qed.
Lemma lem6159064 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (h1 : term88 _123260 s P) (h2 : term90 _123260 s P) : term88 _123260 s P.
Proof. exact (@lem6159062 _123260 s P h1 (@lem6159063 _123260 s P h2)). Qed.
Lemma lem6159065 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (h1 : term90 _123260 s P) : term90 _123260 s P.
Proof. exact (fun h0 : term88 _123260 s P => @lem6159064 _123260 s P h0 h1). Qed.
Lemma lem6159066 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : term92 _123260 s P.
Proof. exact (fun h0 : term90 _123260 s P => @lem6159065 _123260 s P h0). Qed.
Lemma lem6159069 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : term90 _123260 s P.
Proof. exact (@lem6159066 _123260 s P (@lem6159058 _123260 s P)). Qed.
Lemma lem6159070 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : term90 _123260 s P.
Proof. exact (@lem6159069 _123260 s P). Qed.
Lemma lem6159080 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6159081 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term88 _123260 s P) = (term93 _123260 s P).
Proof. exact (@lem6159080 (term89 _123260 s P)). Qed.
Lemma lem6159083 (t : Prop) : (term94 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6159084 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term93 _123260 s P) = (term86 _123260 s P).
Proof. exact (@lem6159083 (term86 _123260 s P)). Qed.
Lemma lem6159089 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term88 _123260 s P) = (term86 _123260 s P).
Proof. exact (TRANS (@lem6159081 _123260 s P) (@lem6159084 _123260 s P)). Qed.
Lemma lem6159096 {_123260 : Type'} (P : _123260 -> Prop) : (term95 _123260 P) = (term96 _123260 P).
Proof. exact (fun_ext (fun s : _123260 -> Prop => @lem6159089 _123260 s P)). Qed.
Lemma lem6159097 {_123260 : Type'} : (@all (_123260 -> Prop)) = (@all (_123260 -> Prop)).
Proof. exact (eq_refl (@all (_123260 -> Prop))). Qed.
Lemma lem6159098 {_123260 : Type'} (P : _123260 -> Prop) : (term97 _123260 P) = (term98 _123260 P).
Proof. exact (MK_COMB (@lem6159097 _123260) (@lem6159096 _123260 P)). Qed.
Lemma lem6159103 {_123260 : Type'} : (term99 _123260) = (term100 _123260).
Proof. exact (fun_ext (fun P : _123260 -> Prop => @lem6159098 _123260 P)). Qed.
Lemma lem6159104 {_123260 : Type'} : (@all (_123260 -> Prop)) = (@all (_123260 -> Prop)).
Proof. exact (eq_refl (@all (_123260 -> Prop))). Qed.
Lemma lem6159113 {_123260 : Type'} : (term101 _123260) = (term102 _123260).
Proof. exact (MK_COMB (@lem6159104 _123260) (@lem6159103 _123260)). Qed.
Lemma lem6159130 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term83 _123260 s P x) = (term83 _123260 s P x).
Proof. exact (eq_refl (term83 _123260 s P x)). Qed.
Lemma lem6159131 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term85 _123260 s P) = (term85 _123260 s P).
Proof. exact (fun_ext (fun x : _123260 => @lem6159130 _123260 s P x)). Qed.
Lemma lem6159132 {_123260 : Type'} : (@all _123260) = (@all _123260).
Proof. exact (eq_refl (@all _123260)). Qed.
Lemma lem6159133 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term86 _123260 s P) = (term86 _123260 s P).
Proof. exact (MK_COMB (@lem6159132 _123260) (@lem6159131 _123260 s P)). Qed.
Lemma lem6159134 {_123260 : Type'} (P : _123260 -> Prop) : (term96 _123260 P) = (term96 _123260 P).
Proof. exact (fun_ext (fun s : _123260 -> Prop => @lem6159133 _123260 s P)). Qed.
Lemma lem6159135 {_123260 : Type'} : (@all (_123260 -> Prop)) = (@all (_123260 -> Prop)).
Proof. exact (eq_refl (@all (_123260 -> Prop))). Qed.
Lemma lem6159136 {_123260 : Type'} (P : _123260 -> Prop) : (term98 _123260 P) = (term98 _123260 P).
Proof. exact (MK_COMB (@lem6159135 _123260) (@lem6159134 _123260 P)). Qed.
Lemma lem6159137 {_123260 : Type'} : (term100 _123260) = (term100 _123260).
Proof. exact (fun_ext (fun P : _123260 -> Prop => @lem6159136 _123260 P)). Qed.
Lemma lem6159138 {_123260 : Type'} : (@all (_123260 -> Prop)) = (@all (_123260 -> Prop)).
Proof. exact (eq_refl (@all (_123260 -> Prop))). Qed.
Lemma lem6159139 {_123260 : Type'} : (term102 _123260) = (term102 _123260).
Proof. exact (MK_COMB (@lem6159138 _123260) (@lem6159137 _123260)). Qed.
Lemma lem6159166 {_123260 : Type'} : (term101 _123260) = (term102 _123260).
Proof. exact (TRANS (@lem6159113 _123260) (@lem6159139 _123260)). Qed.
Lemma lem6159167 {_123260 : Type'} : (term102 _123260) = (term101 _123260).
Proof. exact (SYM (@lem6159166 _123260)). Qed.
Lemma lem6159186 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : term80 _123260 s P x.
Proof. exact (h1). Qed.
Lemma lem6159210 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : term80 _123260 s P x.
Proof. exact (h1). Qed.
Lemma lem6159211 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : term79 _123260 s P x.
Proof. exact (proj2 (@lem6159210 _123260 s P x h1)). Qed.
Lemma lem6159212 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : term57 _123260 s P x.
Proof. exact (proj1 (@lem6159210 _123260 s P x h1)). Qed.
Lemma lem6159236 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : term78 _123260 P x.
Proof. exact (proj2 (@lem6159211 _123260 s P x h1)). Qed.
Lemma lem6159242 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : P x.
Proof. exact (proj2 (@lem6159212 _123260 s P x h1)). Qed.
Lemma lem6159243 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : term103 _123260 P x.
Proof. exact (fun h0 : term78 _123260 P x => @lem6159242 _123260 s P x h1). Qed.
Lemma lem6159245 (p : Prop) : (term104 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6159246 {_123260 : Type'} (P : _123260 -> Prop) (x : _123260) : (term103 _123260 P x) = (P x).
Proof. exact (@lem6159245 (P x)). Qed.
Lemma lem6159247 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : P x.
Proof. exact (EQ_MP (@lem6159246 _123260 P x) (@lem6159243 _123260 s P x h1)). Qed.
Lemma lem6159250 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6159252 {_123260 : Type'} (P : _123260 -> Prop) (x : _123260) : (term78 _123260 P x) = (term105 _123260 P x).
Proof. exact (@lem6159250 (P x)). Qed.
Lemma lem6159255 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : term105 _123260 P x.
Proof. exact (EQ_MP (@lem6159252 _123260 P x) (@lem6159236 _123260 s P x h1)). Qed.
Lemma lem6159258 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : False.
Proof. exact (@lem6159255 _123260 s P x h1 (@lem6159247 _123260 s P x h1)). Qed.
Lemma lem6159259 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : term106.
Proof. exact (fun h0 : ~ False => @lem6159258 _123260 s P x h1). Qed.
Lemma lem6159261 (p : Prop) : (term104 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6159262 : term106 = False.
Proof. exact (@lem6159261 False). Qed.
Lemma lem6159263 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : False.
Proof. exact (EQ_MP (@lem6159262) (@lem6159259 _123260 s P x h1)). Qed.
Lemma lem6159264 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : (term80 _123260 s P x) = False.
Proof. exact (prop_ext (fun h2 : term80 _123260 s P x => @lem6159263 _123260 s P x h1) (fun h2 : False => @lem6159210 _123260 s P x h1)). Qed.
Lemma lem6159265 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : False.
Proof. exact (EQ_MP (@lem6159264 _123260 s P x h1) (@lem6159210 _123260 s P x h1)). Qed.
Lemma lem6159266 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : (term80 _123260 s P x) = False.
Proof. exact (prop_ext (fun h2 : term80 _123260 s P x => @lem6159265 _123260 s P x h1) (fun h2 : False => @lem6159186 _123260 s P x h1)). Qed.
Lemma lem6159267 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) (h1 : term80 _123260 s P x) : False.
Proof. exact (EQ_MP (@lem6159266 _123260 s P x h1) (@lem6159186 _123260 s P x h1)). Qed.
Lemma lem6159268 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : term107 _123260 s P x.
Proof. exact (fun h0 : term80 _123260 s P x => @lem6159267 _123260 s P x h0). Qed.
Lemma lem6159269 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : (term107 _123260 s P x) = (term83 _123260 s P x).
Proof. exact (@lem69 (term80 _123260 s P x)). Qed.
Lemma lem6159270 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (x : _123260) : term83 _123260 s P x.
Proof. exact (EQ_MP (@lem6159269 _123260 s P x) (@lem6159268 _123260 s P x)). Qed.
Lemma lem6159275 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : term86 _123260 s P.
Proof. exact (fun x : _123260 => @lem6159270 _123260 s P x). Qed.
Lemma lem6159280 {_123260 : Type'} (P : _123260 -> Prop) : term98 _123260 P.
Proof. exact (fun s : _123260 -> Prop => @lem6159275 _123260 s P). Qed.
Lemma lem6159285 {_123260 : Type'} : term102 _123260.
Proof. exact (fun P : _123260 -> Prop => @lem6159280 _123260 P). Qed.
Lemma lem6159286 {_123260 : Type'} : term101 _123260.
Proof. exact (EQ_MP (@lem6159167 _123260) (@lem6159285 _123260)). Qed.
Lemma lem6159287 {_123260 : Type'} (P : _123260 -> Prop) : term108 _123260 P.
Proof. exact (@lem6159286 _123260 P). Qed.
Lemma lem6159288 {_123260 : Type'} (P : _123260 -> Prop) : (term108 _123260 P) = (term97 _123260 P).
Proof. exact (eq_refl (term108 _123260 P)). Qed.
Lemma lem6159289 {_123260 : Type'} (P : _123260 -> Prop) : term97 _123260 P.
Proof. exact (EQ_MP (@lem6159288 _123260 P) (@lem6159287 _123260 P)). Qed.
Lemma lem6159290 {_123260 : Type'} (P : _123260 -> Prop) (s : _123260 -> Prop) : term109 _123260 P s.
Proof. exact (@lem6159289 _123260 P s). Qed.
Lemma lem6159291 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term109 _123260 P s) = (term88 _123260 s P).
Proof. exact (eq_refl (term109 _123260 P s)). Qed.
Lemma lem6159292 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : term88 _123260 s P.
Proof. exact (EQ_MP (@lem6159291 _123260 s P) (@lem6159290 _123260 P s)). Qed.
Lemma lem6159294 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : term88 _123260 s P.
Proof. exact (@lem6159070 _123260 s P (@lem6159292 _123260 s P)). Qed.
Lemma lem6159295 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (h1 : term89 _123260 s P) : False.
Proof. exact (@lem6159294 _123260 s P (@lem6159054 _123260 s P h1)). Qed.
Lemma lem6159296 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (h1 : term89 _123260 s P) : (term89 _123260 s P) = False.
Proof. exact (prop_ext (fun h2 : term89 _123260 s P => @lem6159295 _123260 s P h1) (fun h2 : False => @lem6159054 _123260 s P h1)). Qed.
Lemma lem6159297 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) (h1 : term89 _123260 s P) : False.
Proof. exact (EQ_MP (@lem6159296 _123260 s P h1) (@lem6159054 _123260 s P h1)). Qed.
Lemma lem6159298 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : term88 _123260 s P.
Proof. exact (fun h0 : term89 _123260 s P => @lem6159297 _123260 s P h0). Qed.
Lemma lem6159299 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : term86 _123260 s P.
Proof. exact (EQ_MP (@lem6159053 _123260 s P) (@lem6159298 _123260 s P)). Qed.
Lemma lem6159300 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : term32 _123260 s P.
Proof. exact (EQ_MP (@lem6159049 _123260 s P) (@lem6159299 _123260 s P)). Qed.
Lemma lem6159301 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : term27 _123260 s P.
Proof. exact (EQ_MP (@lem6158937 _123260 s P) (@lem6159300 _123260 s P)). Qed.
Lemma lem6159302 {_120592 _120607 : Type'} (op : type1400 _120607) : term110 _120592 _120607 op.
Proof. exact (@lem5764203 _120592 _120607 op). Qed.
Lemma lem6159303 {_120592 _120607 : Type'} (op : type1400 _120607) : (term110 _120592 _120607 op) = (term111 _120592 _120607 op).
Proof. exact (eq_refl (term110 _120592 _120607 op)). Qed.
Lemma lem6159306 {_120592 _120607 : Type'} (op : type1400 _120607) : term111 _120592 _120607 op.
Proof. exact (EQ_MP (@lem6159303 _120592 _120607 op) (@lem6159302 _120592 _120607 op)). Qed.
Lemma lem6159307 {_120592 B : Type'} (op : type1400 B) : term111 _120592 B op.
Proof. exact (@lem6159306 _120592 B op). Qed.
Lemma lem6159308 {_120592 B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term112 _120592 B op.
Proof. exact (@lem6159307 _120592 B op (@lem6158479 B op h1)). Qed.
Lemma lem6159318 {_120592 B : Type'} (s : _120592 -> Prop) (op : type1400 B) (t : _120592 -> Prop) (f : _120592 -> B) (h1 : (term113 _120592 B op s t f) = (term114 _120592 B s op t f)) : (term113 _120592 B op s t f) = (term114 _120592 B s op t f).
Proof. exact (h1). Qed.
Lemma lem6159319 {_120592 B : Type'} (s : _120592 -> Prop) (op : type1400 B) (t : _120592 -> Prop) (f : _120592 -> B) (h1 : (term113 _120592 B op s t f) = (term114 _120592 B s op t f)) : (term114 _120592 B s op t f) = (term113 _120592 B op s t f).
Proof. exact (SYM (@lem6159318 _120592 B s op t f h1)). Qed.
Lemma lem6159320 {_120592 B : Type'} (op : type1400 B) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> B) (h1 : (term114 _120592 B s op t f) = (term113 _120592 B op s t f)) : (term114 _120592 B s op t f) = (term113 _120592 B op s t f).
Proof. exact (h1). Qed.
Lemma lem6159321 {_120592 B : Type'} (op : type1400 B) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> B) (h1 : (term114 _120592 B s op t f) = (term113 _120592 B op s t f)) : (term113 _120592 B op s t f) = (term114 _120592 B s op t f).
Proof. exact (SYM (@lem6159320 _120592 B op s t f h1)). Qed.
Lemma lem6159322 {_120592 B : Type'} (op : type1400 B) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> B) : ((term113 _120592 B op s t f) = (term114 _120592 B s op t f)) = ((term114 _120592 B s op t f) = (term113 _120592 B op s t f)).
Proof. exact (prop_ext (fun h1 : (term113 _120592 B op s t f) = (term114 _120592 B s op t f) => @lem6159319 _120592 B s op t f h1) (fun h1 : (term114 _120592 B s op t f) = (term113 _120592 B op s t f) => @lem6159321 _120592 B op s t f h1)). Qed.
Lemma lem6159323 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) : (term115 _120592 s t) = (term115 _120592 s t).
Proof. exact (eq_refl (term115 _120592 s t)). Qed.
Lemma lem6159324 {_120592 B : Type'} (op : type1400 B) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> B) : (term116 _120592 B s op t f) = (term117 _120592 B op s t f).
Proof. exact (MK_COMB (@lem6159323 _120592 s t) (@lem6159322 _120592 B op s t f)). Qed.
Lemma lem6159325 {_120592 B : Type'} (op : type1400 B) (s : _120592 -> Prop) (f : _120592 -> B) : (term118 _120592 B s op f) = (term119 _120592 B op s f).
Proof. exact (fun_ext (fun t : _120592 -> Prop => @lem6159324 _120592 B op s t f)). Qed.
Lemma lem6159326 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem6159327 {_120592 B : Type'} (op : type1400 B) (s : _120592 -> Prop) (f : _120592 -> B) : (term120 _120592 B s op f) = (term121 _120592 B op s f).
Proof. exact (MK_COMB (@lem6159326 _120592) (@lem6159325 _120592 B op s f)). Qed.
Lemma lem6159328 {_120592 B : Type'} (op : type1400 B) (f : _120592 -> B) : (term122 _120592 B op f) = (term123 _120592 B op f).
Proof. exact (fun_ext (fun s : _120592 -> Prop => @lem6159327 _120592 B op s f)). Qed.
Lemma lem6159329 {_120592 : Type'} : (@all (_120592 -> Prop)) = (@all (_120592 -> Prop)).
Proof. exact (eq_refl (@all (_120592 -> Prop))). Qed.
Lemma lem6159330 {_120592 B : Type'} (op : type1400 B) (f : _120592 -> B) : (term124 _120592 B op f) = (term125 _120592 B op f).
Proof. exact (MK_COMB (@lem6159329 _120592) (@lem6159328 _120592 B op f)). Qed.
Lemma lem6159331 {_120592 B : Type'} (op : type1400 B) : (term126 _120592 B op) = (term127 _120592 B op).
Proof. exact (fun_ext (fun f : _120592 -> B => @lem6159330 _120592 B op f)). Qed.
Lemma lem6159332 {_120592 B : Type'} : (@all (_120592 -> B)) = (@all (_120592 -> B)).
Proof. exact (eq_refl (@all (_120592 -> B))). Qed.
Lemma lem6159333 {_120592 B : Type'} (op : type1400 B) : (term112 _120592 B op) = (term128 _120592 B op).
Proof. exact (MK_COMB (@lem6159332 _120592 B) (@lem6159331 _120592 B op)). Qed.
Lemma lem6159334 {_120592 B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term128 _120592 B op.
Proof. exact (EQ_MP (@lem6159333 _120592 B op) (@lem6159308 _120592 B op h1)). Qed.
Lemma lem6159335 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term27 _123260 s P) = ((term27 _123260 s P) = True).
Proof. exact (@lem7 (term27 _123260 s P)). Qed.
Lemma lem6159337 {A : Type'} (s : A -> Prop) : term129 A s.
Proof. exact (@lem3603906 A s). Qed.
Lemma lem6159338 {A : Type'} (s : A -> Prop) : (term129 A s) = (term130 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem6159339 {A : Type'} (s : A -> Prop) : term130 A s.
Proof. exact (EQ_MP (@lem6159338 A s) (@lem6159337 A s)). Qed.
Lemma lem6159340 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term131 A s P.
Proof. exact (@lem6159339 A s P). Qed.
Lemma lem6159341 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term131 A s P) = (term132 A s P).
Proof. exact (eq_refl (term131 A s P)). Qed.
Lemma lem6159342 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term132 A s P.
Proof. exact (EQ_MP (@lem6159341 A s P) (@lem6159340 A s P)). Qed.
Lemma lem6159343 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6159344 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term133 A s P.
Proof. exact (@lem6159342 A s P (@lem6159343 A s h1)). Qed.
Lemma lem6159345 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term133 A s P) = ((term133 A s P) = True).
Proof. exact (@lem7 (term133 A s P)). Qed.
Lemma lem6159346 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term133 A s P) = True.
Proof. exact (EQ_MP (@lem6159345 A s P) (@lem6159344 A P s h1)). Qed.
Lemma lem6159352 {_120592 B : Type'} (f : _120592 -> B) (op : type1400 B) (h1 : @monoidal B op) : term134 _120592 B op f.
Proof. exact (@lem6159334 _120592 B op h1 f). Qed.
Lemma lem6159353 {_120592 B : Type'} (op : type1400 B) (f : _120592 -> B) : (term134 _120592 B op f) = (term125 _120592 B op f).
Proof. exact (eq_refl (term134 _120592 B op f)). Qed.
Lemma lem6159354 {_120592 B : Type'} (f : _120592 -> B) (op : type1400 B) (h1 : @monoidal B op) : term125 _120592 B op f.
Proof. exact (EQ_MP (@lem6159353 _120592 B op f) (@lem6159352 _120592 B f op h1)). Qed.
Lemma lem6159355 {_120592 B : Type'} (f : _120592 -> B) (s : _120592 -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term135 _120592 B op f s.
Proof. exact (@lem6159354 _120592 B f op h1 s). Qed.
Lemma lem6159356 {_120592 B : Type'} (op : type1400 B) (s : _120592 -> Prop) (f : _120592 -> B) : (term135 _120592 B op f s) = (term121 _120592 B op s f).
Proof. exact (eq_refl (term135 _120592 B op f s)). Qed.
Lemma lem6159357 {_120592 B : Type'} (s : _120592 -> Prop) (f : _120592 -> B) (op : type1400 B) (h1 : @monoidal B op) : term121 _120592 B op s f.
Proof. exact (EQ_MP (@lem6159356 _120592 B op s f) (@lem6159355 _120592 B f s op h1)). Qed.
Lemma lem6159358 {_120592 B : Type'} (s : _120592 -> Prop) (f : _120592 -> B) (t : _120592 -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term136 _120592 B op s f t.
Proof. exact (@lem6159357 _120592 B s f op h1 t). Qed.
Lemma lem6159359 {_120592 B : Type'} (op : type1400 B) (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> B) : (term136 _120592 B op s f t) = (term117 _120592 B op s t f).
Proof. exact (eq_refl (term136 _120592 B op s f t)). Qed.
Lemma lem6159360 {_120592 B : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> B) (op : type1400 B) (h1 : @monoidal B op) : term117 _120592 B op s t f.
Proof. exact (EQ_MP (@lem6159359 _120592 B op s t f) (@lem6159358 _120592 B s f t op h1)). Qed.
Lemma lem6159361 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term137 _120592 s t) : term137 _120592 s t.
Proof. exact (h1). Qed.
Lemma lem6159362 {_120592 B : Type'} (f : _120592 -> B) (op : type1400 B) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : @monoidal B op) (h2 : term137 _120592 s t) : (term114 _120592 B s op t f) = (term113 _120592 B op s t f).
Proof. exact (@lem6159360 _120592 B s t f op h1 (@lem6159361 _120592 s t h2)). Qed.
Lemma lem6159370 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6159408 {_120592 B : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> B) (op : type1400 B) (h1 : @monoidal B op) : term117 _120592 B op s t f.
Proof. exact (fun h0 : term137 _120592 s t => @lem6159362 _120592 B f op s t h1 h0). Qed.
Lemma lem6159409 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term117 A B op s t f.
Proof. exact (@lem6159408 A B s t f op h1). Qed.
Lemma lem6159410 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term138 A B op s P f g.
Proof. exact (@lem6159409 A B (term29 A s P) (term30 A s P) (term139 A B P f g) op h1). Qed.
Lemma lem6159414 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term140 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem6159346 A P s h0). Qed.
Lemma lem6159415 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term140 A s P.
Proof. exact (@lem6159414 A s P). Qed.
Lemma lem6159417 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6159370 A s) (@lem6158480 A s h1)). Qed.
Lemma lem6159418 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem6159417 A s h1)). Qed.
Lemma lem6159419 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem6159418 A s h1) (@lem0)). Qed.
Lemma lem6159420 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term133 A s P) = True.
Proof. exact (@lem6159415 A s P (@lem6159419 A s h1)). Qed.
Lemma lem6159421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6159422 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term141 A s P) = (and True).
Proof. exact (MK_COMB (@lem6159421) (@lem6159420 A P s h1)). Qed.
Lemma lem6159426 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term140 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem6159346 A P s h0). Qed.
Lemma lem6159427 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term140 A s P.
Proof. exact (@lem6159426 A s P). Qed.
Lemma lem6159428 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term142 A s P.
Proof. exact (@lem6159427 A s (term143 A P)). Qed.
Lemma lem6159429 {A : Type'} (P : A -> Prop) (x : A) : (term144 A P x) = (term78 A P x).
Proof. exact (eq_refl (term144 A P x)). Qed.
Lemma lem6159430 {A : Type'} (x : A) (s : A -> Prop) : (term55 A x s) = (term55 A x s).
Proof. exact (eq_refl (term55 A x s)). Qed.
Lemma lem6159431 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term145 A s P x) = (term63 A s P x).
Proof. exact (MK_COMB (@lem6159430 A x s) (@lem6159429 A P x)). Qed.
Lemma lem6159432 {A : Type'} (GEN_PVAR_247 : A) : (@SETSPEC A GEN_PVAR_247) = (@SETSPEC A GEN_PVAR_247).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_247)). Qed.
Lemma lem6159433 {A : Type'} (GEN_PVAR_247 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term146 A GEN_PVAR_247 s P x) = (term65 A GEN_PVAR_247 s P x).
Proof. exact (MK_COMB (@lem6159432 A GEN_PVAR_247) (@lem6159431 A s P x)). Qed.
Lemma lem6159434 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6159435 {A : Type'} (GEN_PVAR_247 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term147 A GEN_PVAR_247 s P x) = (term67 A GEN_PVAR_247 s P x).
Proof. exact (MK_COMB (@lem6159433 A GEN_PVAR_247 s P x) (@lem6159434 A x)). Qed.
Lemma lem6159436 {A : Type'} (GEN_PVAR_247 : A) (s : A -> Prop) (P : A -> Prop) : (term148 A GEN_PVAR_247 s P) = (term69 A GEN_PVAR_247 s P).
Proof. exact (fun_ext (fun x : A => @lem6159435 A GEN_PVAR_247 s P x)). Qed.
Lemma lem6159437 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6159438 {A : Type'} (GEN_PVAR_247 : A) (s : A -> Prop) (P : A -> Prop) : (term149 A GEN_PVAR_247 s P) = (term71 A GEN_PVAR_247 s P).
Proof. exact (MK_COMB (@lem6159437 A) (@lem6159436 A GEN_PVAR_247 s P)). Qed.
Lemma lem6159439 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term150 A s P) = (term73 A s P).
Proof. exact (fun_ext (fun GEN_PVAR_247 : A => @lem6159438 A GEN_PVAR_247 s P)). Qed.
Lemma lem6159440 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6159441 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term151 A s P) = (term30 A s P).
Proof. exact (MK_COMB (@lem6159440 A) (@lem6159439 A s P)). Qed.
Lemma lem6159442 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem6159443 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term152 A s P) = (term153 A s P).
Proof. exact (MK_COMB (@lem6159442 A) (@lem6159441 A s P)). Qed.
Lemma lem6159444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6159445 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term154 A s P) = (term155 A s P).
Proof. exact (MK_COMB (@lem6159444) (@lem6159443 A s P)). Qed.
Lemma lem6159446 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem6159447 {A : Type'} (s : A -> Prop) (P : A -> Prop) : ((term152 A s P) = True) = ((term153 A s P) = True).
Proof. exact (MK_COMB (@lem6159445 A s P) (@lem6159446)). Qed.
Lemma lem6159448 {A : Type'} (s : A -> Prop) : (term156 A s) = (term156 A s).
Proof. exact (eq_refl (term156 A s)). Qed.
Lemma lem6159449 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term142 A s P) = (term157 A s P).
Proof. exact (MK_COMB (@lem6159448 A s) (@lem6159447 A s P)). Qed.
Lemma lem6159450 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term157 A s P.
Proof. exact (EQ_MP (@lem6159449 A s P) (@lem6159428 A s P)). Qed.
Lemma lem6159452 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6159370 A s) (@lem6158480 A s h1)). Qed.
Lemma lem6159453 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem6159452 A s h1)). Qed.
Lemma lem6159454 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem6159453 A s h1) (@lem0)). Qed.
Lemma lem6159455 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term153 A s P) = True.
Proof. exact (@lem6159450 A s P (@lem6159454 A s h1)). Qed.
Lemma lem6159456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6159457 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term158 A s P) = (and True).
Proof. exact (MK_COMB (@lem6159456) (@lem6159455 A P s h1)). Qed.
Lemma lem6159459 {_123260 : Type'} (s : _123260 -> Prop) (P : _123260 -> Prop) : (term27 _123260 s P) = True.
Proof. exact (EQ_MP (@lem6159335 _123260 s P) (@lem6159301 _123260 s P)). Qed.
Lemma lem6159460 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term27 A s P) = True.
Proof. exact (@lem6159459 A s P). Qed.
Lemma lem6159461 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term159 A s P) = (True /\ True).
Proof. exact (MK_COMB (@lem6159457 A P s h1) (@lem6159460 A s P)). Qed.
Lemma lem6159463 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6159464 : (True /\ True) = True.
Proof. exact (@lem6159463 True). Qed.
Lemma lem6159465 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term159 A s P) = True.
Proof. exact (TRANS (@lem6159461 A P s h1) (@lem6159464)). Qed.
Lemma lem6159466 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term160 A s P) = (True /\ True).
Proof. exact (MK_COMB (@lem6159422 A P s h1) (@lem6159465 A P s h1)). Qed.
Lemma lem6159468 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6159469 : (True /\ True) = True.
Proof. exact (@lem6159468 True). Qed.
Lemma lem6159470 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term160 A s P) = True.
Proof. exact (TRANS (@lem6159466 A P s h1) (@lem6159469)). Qed.
Lemma lem6159471 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : True = (term160 A s P).
Proof. exact (SYM (@lem6159470 A P s h1)). Qed.
Lemma lem6159472 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term160 A s P.
Proof. exact (EQ_MP (@lem6159471 A P s h1) (@lem0)). Qed.
Lemma lem6159473 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) : (term161 A B op s P f g) = (term162 A B op s P f g).
Proof. exact (@lem6159410 A B s P f g op h2 (@lem6159472 A P s h1)). Qed.
Lemma lem6159519 {A B : Type'} (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) : (term163 A B op s P f g) = (term163 A B op s P f g).
Proof. exact (eq_refl (term163 A B op s P f g)). Qed.
Lemma lem6159520 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) : ((term25 A B op s P f g) = (term161 A B op s P f g)) = ((term25 A B op s P f g) = (term162 A B op s P f g)).
Proof. exact (MK_COMB (@lem6159519 A B op s P f g) (@lem6159473 A B P f g s op h1 h2)). Qed.
Lemma lem6159601 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) : ((term25 A B op s P f g) = (term162 A B op s P f g)) = ((term25 A B op s P f g) = (term161 A B op s P f g)).
Proof. exact (SYM (@lem6159520 A B P f g s op h1 h2)). Qed.
Lemma lem6159602 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) : (term139 A B P f g) = (term139 A B P f g).
Proof. exact (eq_refl (term139 A B P f g)). Qed.
Lemma lem6159603 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem6159607 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term31 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem6159608 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term31 A s t).
Proof. exact (@lem6159607 A s t). Qed.
Lemma lem6159609 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (s = (term164 A s P)) = (term165 A s P).
Proof. exact (@lem6159608 A s (term164 A s P)). Qed.
Lemma lem6159630 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term165 A s P) = (s = (term164 A s P)).
Proof. exact (SYM (@lem6159609 A s P)). Qed.
Lemma lem6159638 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6159639 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6159638 A P x). Qed.
Lemma lem6159640 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6159639 A s x). Qed.
Lemma lem6159641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6159642 {A : Type'} (s : A -> Prop) (x : A) : (term166 A x s) = (term167 A s x).
Proof. exact (MK_COMB (@lem6159641) (@lem6159640 A s x)). Qed.
Lemma lem6159644 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term168 A x s t) = (term169 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem6159645 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term168 A x s t) = (term169 A s x t).
Proof. exact (@lem6159644 A s x t). Qed.
Lemma lem6159646 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term170 A x s P) = (term171 A x s P).
Proof. exact (@lem6159645 A (term29 A s P) x (term30 A s P)). Qed.
Lemma lem6159650 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem6159651 {A : Type'} (p : A -> Prop) (x : A) : (term4 A x p) = (p x).
Proof. exact (@lem6159650 A p x). Qed.
Lemma lem6159652 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term37 A x s P) = (term38 A s P x).
Proof. exact (@lem6159651 A (term39 A s P) x). Qed.
Lemma lem6159653 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term38 A s P x) = (term40 A s P x).
Proof. exact (eq_refl (term38 A s P x)). Qed.
Lemma lem6159654 {A : Type'} (GEN_PVAR_246 : A) : (@SETSPEC A GEN_PVAR_246) = (@SETSPEC A GEN_PVAR_246).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_246)). Qed.
Lemma lem6159655 {A : Type'} (GEN_PVAR_246 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term41 A GEN_PVAR_246 s P x) = (term42 A GEN_PVAR_246 s P x).
Proof. exact (MK_COMB (@lem6159654 A GEN_PVAR_246) (@lem6159653 A s P x)). Qed.
Lemma lem6159656 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6159657 {A : Type'} (GEN_PVAR_246 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term43 A GEN_PVAR_246 s P x) = (term44 A GEN_PVAR_246 s P x).
Proof. exact (MK_COMB (@lem6159655 A GEN_PVAR_246 s P x) (@lem6159656 A x)). Qed.
Lemma lem6159658 {A : Type'} (GEN_PVAR_246 : A) (s : A -> Prop) (P : A -> Prop) : (term45 A GEN_PVAR_246 s P) = (term46 A GEN_PVAR_246 s P).
Proof. exact (fun_ext (fun x : A => @lem6159657 A GEN_PVAR_246 s P x)). Qed.
Lemma lem6159659 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6159660 {A : Type'} (GEN_PVAR_246 : A) (s : A -> Prop) (P : A -> Prop) : (term47 A GEN_PVAR_246 s P) = (term48 A GEN_PVAR_246 s P).
Proof. exact (MK_COMB (@lem6159659 A) (@lem6159658 A GEN_PVAR_246 s P)). Qed.
Lemma lem6159661 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term49 A s P) = (term50 A s P).
Proof. exact (fun_ext (fun GEN_PVAR_246 : A => @lem6159660 A GEN_PVAR_246 s P)). Qed.
Lemma lem6159662 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6159663 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term51 A s P) = (term29 A s P).
Proof. exact (MK_COMB (@lem6159662 A) (@lem6159661 A s P)). Qed.
Lemma lem6159664 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6159665 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term37 A x s P) = (term52 A x s P).
Proof. exact (MK_COMB (@lem6159664 A x) (@lem6159663 A s P)). Qed.
Lemma lem6159666 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6159667 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term53 A x s P) = (term54 A x s P).
Proof. exact (MK_COMB (@lem6159666) (@lem6159665 A x s P)). Qed.
Lemma lem6159668 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term38 A s P x) = (term40 A s P x).
Proof. exact (eq_refl (term38 A s P x)). Qed.
Lemma lem6159669 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : ((term37 A x s P) = (term38 A s P x)) = ((term52 A x s P) = (term40 A s P x)).
Proof. exact (MK_COMB (@lem6159667 A x s P) (@lem6159668 A s P x)). Qed.
Lemma lem6159670 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term52 A x s P) = (term40 A s P x).
Proof. exact (EQ_MP (@lem6159669 A s P x) (@lem6159652 A s P x)). Qed.
Lemma lem6159674 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6159675 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6159674 A P x). Qed.
Lemma lem6159676 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6159675 A s x). Qed.
Lemma lem6159677 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6159678 {A : Type'} (s : A -> Prop) (x : A) : (term55 A x s) = (term56 A s x).
Proof. exact (MK_COMB (@lem6159677) (@lem6159676 A s x)). Qed.
Lemma lem6159679 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem6159680 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term40 A s P x) = (term57 A s P x).
Proof. exact (MK_COMB (@lem6159678 A s x) (@lem6159679 A P x)). Qed.
Lemma lem6159683 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term52 A x s P) = (term57 A s P x).
Proof. exact (TRANS (@lem6159670 A s P x) (@lem6159680 A s P x)). Qed.
Lemma lem6159684 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6159685 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term172 A x s P) = (term173 A s P x).
Proof. exact (MK_COMB (@lem6159684) (@lem6159683 A s P x)). Qed.
Lemma lem6159687 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem6159688 {A : Type'} (p : A -> Prop) (x : A) : (term4 A x p) = (p x).
Proof. exact (@lem6159687 A p x). Qed.
Lemma lem6159689 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term60 A x s P) = (term61 A s P x).
Proof. exact (@lem6159688 A (term62 A s P) x). Qed.
Lemma lem6159690 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term61 A s P x) = (term63 A s P x).
Proof. exact (eq_refl (term61 A s P x)). Qed.
Lemma lem6159691 {A : Type'} (GEN_PVAR_247 : A) : (@SETSPEC A GEN_PVAR_247) = (@SETSPEC A GEN_PVAR_247).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_247)). Qed.
Lemma lem6159692 {A : Type'} (GEN_PVAR_247 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term64 A GEN_PVAR_247 s P x) = (term65 A GEN_PVAR_247 s P x).
Proof. exact (MK_COMB (@lem6159691 A GEN_PVAR_247) (@lem6159690 A s P x)). Qed.
Lemma lem6159693 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6159694 {A : Type'} (GEN_PVAR_247 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term66 A GEN_PVAR_247 s P x) = (term67 A GEN_PVAR_247 s P x).
Proof. exact (MK_COMB (@lem6159692 A GEN_PVAR_247 s P x) (@lem6159693 A x)). Qed.
Lemma lem6159695 {A : Type'} (GEN_PVAR_247 : A) (s : A -> Prop) (P : A -> Prop) : (term68 A GEN_PVAR_247 s P) = (term69 A GEN_PVAR_247 s P).
Proof. exact (fun_ext (fun x : A => @lem6159694 A GEN_PVAR_247 s P x)). Qed.
Lemma lem6159696 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6159697 {A : Type'} (GEN_PVAR_247 : A) (s : A -> Prop) (P : A -> Prop) : (term70 A GEN_PVAR_247 s P) = (term71 A GEN_PVAR_247 s P).
Proof. exact (MK_COMB (@lem6159696 A) (@lem6159695 A GEN_PVAR_247 s P)). Qed.
Lemma lem6159698 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term72 A s P) = (term73 A s P).
Proof. exact (fun_ext (fun GEN_PVAR_247 : A => @lem6159697 A GEN_PVAR_247 s P)). Qed.
Lemma lem6159699 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6159700 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term74 A s P) = (term30 A s P).
Proof. exact (MK_COMB (@lem6159699 A) (@lem6159698 A s P)). Qed.
Lemma lem6159701 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6159702 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term60 A x s P) = (term75 A x s P).
Proof. exact (MK_COMB (@lem6159701 A x) (@lem6159700 A s P)). Qed.
Lemma lem6159703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6159704 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term76 A x s P) = (term77 A x s P).
Proof. exact (MK_COMB (@lem6159703) (@lem6159702 A x s P)). Qed.
Lemma lem6159705 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term61 A s P x) = (term63 A s P x).
Proof. exact (eq_refl (term61 A s P x)). Qed.
Lemma lem6159706 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : ((term60 A x s P) = (term61 A s P x)) = ((term75 A x s P) = (term63 A s P x)).
Proof. exact (MK_COMB (@lem6159704 A x s P) (@lem6159705 A s P x)). Qed.
Lemma lem6159707 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term75 A x s P) = (term63 A s P x).
Proof. exact (EQ_MP (@lem6159706 A s P x) (@lem6159689 A s P x)). Qed.
Lemma lem6159711 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6159712 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6159711 A P x). Qed.
Lemma lem6159713 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6159712 A s x). Qed.
Lemma lem6159714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6159715 {A : Type'} (s : A -> Prop) (x : A) : (term55 A x s) = (term56 A s x).
Proof. exact (MK_COMB (@lem6159714) (@lem6159713 A s x)). Qed.
Lemma lem6159716 {A : Type'} (P : A -> Prop) (x : A) : (term78 A P x) = (term78 A P x).
Proof. exact (eq_refl (term78 A P x)). Qed.
Lemma lem6159717 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term63 A s P x) = (term79 A s P x).
Proof. exact (MK_COMB (@lem6159715 A s x) (@lem6159716 A P x)). Qed.
Lemma lem6159720 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term75 A x s P) = (term79 A s P x).
Proof. exact (TRANS (@lem6159707 A s P x) (@lem6159717 A s P x)). Qed.
Lemma lem6159721 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term171 A x s P) = (term174 A s P x).
Proof. exact (MK_COMB (@lem6159685 A s P x) (@lem6159720 A s P x)). Qed.
Lemma lem6159724 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term170 A x s P) = (term174 A s P x).
Proof. exact (TRANS (@lem6159646 A x s P) (@lem6159721 A s P x)). Qed.
Lemma lem6159725 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : ((@IN A x s) = (term170 A x s P)) = ((s x) = (term174 A s P x)).
Proof. exact (MK_COMB (@lem6159642 A s x) (@lem6159724 A s P x)). Qed.
Lemma lem6159728 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term175 A s P) = (term176 A s P).
Proof. exact (fun_ext (fun x : A => @lem6159725 A s P x)). Qed.
Lemma lem6159729 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6159730 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term165 A s P) = (term177 A s P).
Proof. exact (MK_COMB (@lem6159729 A) (@lem6159728 A s P)). Qed.
Lemma lem6159735 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term177 A s P) = (term165 A s P).
Proof. exact (SYM (@lem6159730 A s P)). Qed.
Lemma lem6159737 (p : Prop) : p = (term87 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6159738 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term177 A s P) = (term178 A s P).
Proof. exact (@lem6159737 (term177 A s P)). Qed.
Lemma lem6159739 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term178 A s P) = (term177 A s P).
Proof. exact (SYM (@lem6159738 A s P)). Qed.
Lemma lem6159740 {A : Type'} (s : A -> Prop) (P : A -> Prop) (h1 : term179 A s P) : term179 A s P.
Proof. exact (h1). Qed.
Lemma lem6159743 {A : Type'} (s : A -> Prop) (P : A -> Prop) (h1 : term178 A s P) : term178 A s P.
Proof. exact (h1). Qed.
Lemma lem6159744 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term180 A s P.
Proof. exact (fun h0 : term178 A s P => @lem6159743 A s P h0). Qed.
Lemma lem6159745 {A : Type'} (s : A -> Prop) (P : A -> Prop) (h1 : term180 A s P) : term180 A s P.
Proof. exact (h1). Qed.
Lemma lem6159746 {A : Type'} (s : A -> Prop) (P : A -> Prop) (h1 : term178 A s P) : term178 A s P.
Proof. exact (h1). Qed.
Lemma lem6159747 {A : Type'} (s : A -> Prop) (P : A -> Prop) (h1 : term178 A s P) (h2 : term180 A s P) : term178 A s P.
Proof. exact (@lem6159745 A s P h2 (@lem6159746 A s P h1)). Qed.
Lemma lem6159748 {A : Type'} (s : A -> Prop) (P : A -> Prop) (h1 : term178 A s P) : term181 A s P.
Proof. exact (fun h0 : term180 A s P => @lem6159747 A s P h1 h0). Qed.
Lemma lem6159749 {A : Type'} (s : A -> Prop) (P : A -> Prop) (h1 : term180 A s P) : term180 A s P.
Proof. exact (h1). Qed.
Lemma lem6159750 {A : Type'} (s : A -> Prop) (P : A -> Prop) (h1 : term178 A s P) (h2 : term180 A s P) : term178 A s P.
Proof. exact (@lem6159748 A s P h1 (@lem6159749 A s P h2)). Qed.
Lemma lem6159751 {A : Type'} (s : A -> Prop) (P : A -> Prop) (h1 : term180 A s P) : term180 A s P.
Proof. exact (fun h0 : term178 A s P => @lem6159750 A s P h0 h1). Qed.
Lemma lem6159752 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term182 A s P.
Proof. exact (fun h0 : term180 A s P => @lem6159751 A s P h0). Qed.
Lemma lem6159755 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term180 A s P.
Proof. exact (@lem6159752 A s P (@lem6159744 A s P)). Qed.
Lemma lem6159756 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term180 A s P.
Proof. exact (@lem6159755 A s P). Qed.
Lemma lem6159766 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6159767 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term178 A s P) = (term183 A s P).
Proof. exact (@lem6159766 (term179 A s P)). Qed.
Lemma lem6159769 (t : Prop) : (term94 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6159770 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term183 A s P) = (term177 A s P).
Proof. exact (@lem6159769 (term177 A s P)). Qed.
Lemma lem6159775 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term178 A s P) = (term177 A s P).
Proof. exact (TRANS (@lem6159767 A s P) (@lem6159770 A s P)). Qed.
Lemma lem6159782 {A : Type'} (P : A -> Prop) : (term184 A P) = (term185 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6159775 A s P)). Qed.
Lemma lem6159783 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6159784 {A : Type'} (P : A -> Prop) : (term186 A P) = (term187 A P).
Proof. exact (MK_COMB (@lem6159783 A) (@lem6159782 A P)). Qed.
Lemma lem6159789 {A : Type'} : (term188 A) = (term189 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem6159784 A P)). Qed.
Lemma lem6159790 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6159799 {A : Type'} : (term190 A) = (term191 A).
Proof. exact (MK_COMB (@lem6159790 A) (@lem6159789 A)). Qed.
Lemma lem6159818 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : ((s x) = (term174 A s P x)) = ((s x) = (term174 A s P x)).
Proof. exact (eq_refl ((s x) = (term174 A s P x))). Qed.
Lemma lem6159819 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term176 A s P) = (term176 A s P).
Proof. exact (fun_ext (fun x : A => @lem6159818 A s P x)). Qed.
Lemma lem6159820 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6159821 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term177 A s P) = (term177 A s P).
Proof. exact (MK_COMB (@lem6159820 A) (@lem6159819 A s P)). Qed.
Lemma lem6159822 {A : Type'} (P : A -> Prop) : (term185 A P) = (term185 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6159821 A s P)). Qed.
Lemma lem6159823 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6159824 {A : Type'} (P : A -> Prop) : (term187 A P) = (term187 A P).
Proof. exact (MK_COMB (@lem6159823 A) (@lem6159822 A P)). Qed.
Lemma lem6159825 {A : Type'} : (term189 A) = (term189 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem6159824 A P)). Qed.
Lemma lem6159826 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6159827 {A : Type'} : (term191 A) = (term191 A).
Proof. exact (MK_COMB (@lem6159826 A) (@lem6159825 A)). Qed.
Lemma lem6159854 {A : Type'} : (term190 A) = (term191 A).
Proof. exact (TRANS (@lem6159799 A) (@lem6159827 A)). Qed.
Lemma lem6159855 {A : Type'} : (term191 A) = (term190 A).
Proof. exact (SYM (@lem6159854 A)). Qed.
Lemma lem6159857 (p : Prop) : p = (term87 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6159858 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : ((s x) = (term174 A s P x)) = (term192 A s P x).
Proof. exact (@lem6159857 ((s x) = (term174 A s P x))). Qed.
Lemma lem6159859 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term192 A s P x) = ((s x) = (term174 A s P x)).
Proof. exact (SYM (@lem6159858 A s P x)). Qed.
Lemma lem6159860 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term193 A s P x) : term193 A s P x.
Proof. exact (h1). Qed.
Lemma lem6159871 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term194 A s P x) = (term195 A s P x).
Proof. exact (@lem17045 (s x) (P x)). Qed.
Lemma lem6159880 {A : Type'} (P : A -> Prop) (x : A) : (term196 A P x) = (P x).
Proof. exact (@lem16933 (P x)). Qed.
Lemma lem6159882 {A : Type'} (s : A -> Prop) (x : A) : (term197 A s x) = (term197 A s x).
Proof. exact (eq_refl (term197 A s x)). Qed.
Lemma lem6159883 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term198 A s P x) = (term199 A s P x).
Proof. exact (MK_COMB (@lem6159882 A s x) (@lem6159880 A P x)). Qed.
Lemma lem6159884 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term200 A s P x) = (term198 A s P x).
Proof. exact (@lem17045 (s x) (term78 A P x)). Qed.
Lemma lem6159885 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term200 A s P x) = (term199 A s P x).
Proof. exact (TRANS (@lem6159884 A s P x) (@lem6159883 A s P x)). Qed.
Lemma lem6159889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6159890 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term201 A s P x) = (term202 A s P x).
Proof. exact (MK_COMB (@lem6159889) (@lem6159871 A s P x)). Qed.
Lemma lem6159891 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term203 A s P x) = (term204 A s P x).
Proof. exact (MK_COMB (@lem6159890 A s P x) (@lem6159885 A s P x)). Qed.
Lemma lem6159892 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term205 A s P x) = (term203 A s P x).
Proof. exact (@lem17160 (term57 A s P x) (term79 A s P x)). Qed.
Lemma lem6159893 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term205 A s P x) = (term204 A s P x).
Proof. exact (TRANS (@lem6159892 A s P x) (@lem6159891 A s P x)). Qed.
Lemma lem6159899 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term206 A s P x) = (term206 A s P x).
Proof. exact (eq_refl (term206 A s P x)). Qed.
Lemma lem6159901 {A : Type'} (s : A -> Prop) (x : A) : (term56 A s x) = (term56 A s x).
Proof. exact (eq_refl (term56 A s x)). Qed.
Lemma lem6159902 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term207 A s P x) = (term208 A s P x).
Proof. exact (MK_COMB (@lem6159901 A s x) (@lem6159893 A s P x)). Qed.
Lemma lem6159903 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6159904 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term209 A s P x) = (term210 A s P x).
Proof. exact (MK_COMB (@lem6159903) (@lem6159902 A s P x)). Qed.
Lemma lem6159905 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term211 A s P x) = (term212 A s P x).
Proof. exact (MK_COMB (@lem6159904 A s P x) (@lem6159899 A s P x)). Qed.
Lemma lem6159906 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term193 A s P x) = (term211 A s P x).
Proof. exact (@lem17646 (s x) (term174 A s P x)). Qed.
Lemma lem6159911 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term193 A s P x) = (term212 A s P x).
Proof. exact (TRANS (@lem6159906 A s P x) (@lem6159905 A s P x)). Qed.
Lemma lem6159980 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term193 A s P x) : term212 A s P x.
Proof. exact (EQ_MP (@lem6159911 A s P x) (@lem6159860 A s P x h1)). Qed.
Lemma lem6159981 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term208 A s P x) : term208 A s P x.
Proof. exact (h1). Qed.
Lemma lem6159982 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term206 A s P x) : term206 A s P x.
Proof. exact (h1). Qed.
Lemma lem6159983 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term208 A s P x) : term204 A s P x.
Proof. exact (proj2 (@lem6159981 A s P x h1)). Qed.
Lemma lem6159985 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term208 A s P x) : term199 A s P x.
Proof. exact (proj2 (@lem6159983 A s P x h1)). Qed.
Lemma lem6159986 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term208 A s P x) : term195 A s P x.
Proof. exact (proj1 (@lem6159983 A s P x h1)). Qed.
Lemma lem6159993 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term206 A s P x) : term174 A s P x.
Proof. exact (proj2 (@lem6159982 A s P x h1)). Qed.
Lemma lem6159995 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term57 A s P x) : term57 A s P x.
Proof. exact (h1). Qed.
Lemma lem6159996 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term79 A s P x) : term79 A s P x.
Proof. exact (h1). Qed.
Lemma lem6160008 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term78 A s x.
Proof. exact (h1). Qed.
Lemma lem6160012 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term78 A s x.
Proof. exact (h1). Qed.
Lemma lem6160020 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term78 A s x.
Proof. exact (h1). Qed.
Lemma lem6160036 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term78 A s x.
Proof. exact (h1). Qed.
Lemma lem6160044 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem6160048 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) : term78 A P x.
Proof. exact (h1). Qed.
Lemma lem6160076 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term78 A s x.
Proof. exact (h1). Qed.
Lemma lem6160078 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term78 A s x.
Proof. exact (h1). Qed.
Lemma lem6160082 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term78 A s x.
Proof. exact (h1). Qed.
Lemma lem6160090 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term78 A s x.
Proof. exact (h1). Qed.
Lemma lem6160094 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem6160096 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) : term78 A P x.
Proof. exact (h1). Qed.
Lemma lem6160098 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term206 A s P x) : term78 A s x.
Proof. exact (proj1 (@lem6159982 A s P x h1)). Qed.
Lemma lem6160104 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term206 A s P x) : term78 A s x.
Proof. exact (proj1 (@lem6159982 A s P x h1)). Qed.
Lemma lem6160110 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term208 A s P x) : s x.
Proof. exact (proj1 (@lem6159981 A s P x h1)). Qed.
Lemma lem6160111 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term208 A s P x) : term103 A s x.
Proof. exact (fun h0 : term78 A s x => @lem6160110 A s P x h1). Qed.
Lemma lem6160113 (p : Prop) : (term104 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6160114 {A : Type'} (s : A -> Prop) (x : A) : (term103 A s x) = (s x).
Proof. exact (@lem6160113 (s x)). Qed.
Lemma lem6160115 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term208 A s P x) : s x.
Proof. exact (EQ_MP (@lem6160114 A s x) (@lem6160111 A s P x h1)). Qed.
Lemma lem6160118 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6160120 {A : Type'} (s : A -> Prop) (x : A) : (term78 A s x) = (term105 A s x).
Proof. exact (@lem6160118 (s x)). Qed.
Lemma lem6160123 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term105 A s x.
Proof. exact (EQ_MP (@lem6160120 A s x) (@lem6160076 A s x h1)). Qed.
Lemma lem6160126 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (@lem6160123 A s x h1 (@lem6160115 A s P x h2)). Qed.
Lemma lem6160127 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : term106.
Proof. exact (fun h0 : ~ False => @lem6160126 A s P x h1 h2). Qed.
Lemma lem6160129 (p : Prop) : (term104 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6160130 : term106 = False.
Proof. exact (@lem6160129 False). Qed.
Lemma lem6160131 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160130) (@lem6160127 A s P x h1 h2)). Qed.
Lemma lem6160133 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term208 A s P x) : s x.
Proof. exact (proj1 (@lem6159981 A s P x h1)). Qed.
Lemma lem6160134 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term208 A s P x) : term103 A s x.
Proof. exact (fun h0 : term78 A s x => @lem6160133 A s P x h1). Qed.
Lemma lem6160136 (p : Prop) : (term104 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6160137 {A : Type'} (s : A -> Prop) (x : A) : (term103 A s x) = (s x).
Proof. exact (@lem6160136 (s x)). Qed.
Lemma lem6160138 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term208 A s P x) : s x.
Proof. exact (EQ_MP (@lem6160137 A s x) (@lem6160134 A s P x h1)). Qed.
Lemma lem6160141 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6160143 {A : Type'} (s : A -> Prop) (x : A) : (term78 A s x) = (term105 A s x).
Proof. exact (@lem6160141 (s x)). Qed.
Lemma lem6160146 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term105 A s x.
Proof. exact (EQ_MP (@lem6160143 A s x) (@lem6160082 A s x h1)). Qed.
Lemma lem6160149 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (@lem6160146 A s x h1 (@lem6160138 A s P x h2)). Qed.
Lemma lem6160150 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : term106.
Proof. exact (fun h0 : ~ False => @lem6160149 A s P x h1 h2). Qed.
Lemma lem6160152 (p : Prop) : (term104 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6160153 : term106 = False.
Proof. exact (@lem6160152 False). Qed.
Lemma lem6160154 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160153) (@lem6160150 A s P x h1 h2)). Qed.
Lemma lem6160156 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term208 A s P x) : s x.
Proof. exact (proj1 (@lem6159981 A s P x h1)). Qed.
Lemma lem6160157 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term208 A s P x) : term103 A s x.
Proof. exact (fun h0 : term78 A s x => @lem6160156 A s P x h1). Qed.
Lemma lem6160159 (p : Prop) : (term104 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6160160 {A : Type'} (s : A -> Prop) (x : A) : (term103 A s x) = (s x).
Proof. exact (@lem6160159 (s x)). Qed.
Lemma lem6160161 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term208 A s P x) : s x.
Proof. exact (EQ_MP (@lem6160160 A s x) (@lem6160157 A s P x h1)). Qed.
Lemma lem6160164 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6160166 {A : Type'} (s : A -> Prop) (x : A) : (term78 A s x) = (term105 A s x).
Proof. exact (@lem6160164 (s x)). Qed.
Lemma lem6160169 {A : Type'} (s : A -> Prop) (x : A) (h1 : term78 A s x) : term105 A s x.
Proof. exact (EQ_MP (@lem6160166 A s x) (@lem6160090 A s x h1)). Qed.
Lemma lem6160172 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (@lem6160169 A s x h1 (@lem6160161 A s P x h2)). Qed.
Lemma lem6160173 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : term106.
Proof. exact (fun h0 : ~ False => @lem6160172 A s P x h1 h2). Qed.
Lemma lem6160175 (p : Prop) : (term104 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6160176 : term106 = False.
Proof. exact (@lem6160175 False). Qed.
Lemma lem6160177 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160176) (@lem6160173 A s P x h1 h2)). Qed.
Lemma lem6160179 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem6160180 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : term103 A P x.
Proof. exact (fun h0 : term78 A P x => @lem6160179 A P x h1). Qed.
Lemma lem6160182 (p : Prop) : (term104 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6160183 {A : Type'} (P : A -> Prop) (x : A) : (term103 A P x) = (P x).
Proof. exact (@lem6160182 (P x)). Qed.
Lemma lem6160184 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (EQ_MP (@lem6160183 A P x) (@lem6160180 A P x h1)). Qed.
Lemma lem6160187 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6160189 {A : Type'} (P : A -> Prop) (x : A) : (term78 A P x) = (term105 A P x).
Proof. exact (@lem6160187 (P x)). Qed.
Lemma lem6160192 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) : term105 A P x.
Proof. exact (EQ_MP (@lem6160189 A P x) (@lem6160096 A P x h1)). Qed.
Lemma lem6160195 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : False.
Proof. exact (@lem6160192 A P x h1 (@lem6160184 A P x h2)). Qed.
Lemma lem6160196 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : term106.
Proof. exact (fun h0 : ~ False => @lem6160195 A P x h1 h2). Qed.
Lemma lem6160198 (p : Prop) : (term104 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6160199 : term106 = False.
Proof. exact (@lem6160198 False). Qed.
Lemma lem6160200 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : False.
Proof. exact (EQ_MP (@lem6160199) (@lem6160196 A P x h1 h2)). Qed.
Lemma lem6160202 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term57 A s P x) : s x.
Proof. exact (proj1 (@lem6159995 A s P x h1)). Qed.
Lemma lem6160203 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term57 A s P x) : term103 A s x.
Proof. exact (fun h0 : term78 A s x => @lem6160202 A s P x h1). Qed.
Lemma lem6160205 (p : Prop) : (term104 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6160206 {A : Type'} (s : A -> Prop) (x : A) : (term103 A s x) = (s x).
Proof. exact (@lem6160205 (s x)). Qed.
Lemma lem6160207 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term57 A s P x) : s x.
Proof. exact (EQ_MP (@lem6160206 A s x) (@lem6160203 A s P x h1)). Qed.
Lemma lem6160210 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6160212 {A : Type'} (s : A -> Prop) (x : A) : (term78 A s x) = (term105 A s x).
Proof. exact (@lem6160210 (s x)). Qed.
Lemma lem6160215 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term206 A s P x) : term105 A s x.
Proof. exact (EQ_MP (@lem6160212 A s x) (@lem6160098 A s P x h1)). Qed.
Lemma lem6160218 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term206 A s P x) (h2 : term57 A s P x) : False.
Proof. exact (@lem6160215 A s P x h1 (@lem6160207 A s P x h2)). Qed.
Lemma lem6160219 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term206 A s P x) (h2 : term57 A s P x) : term106.
Proof. exact (fun h0 : ~ False => @lem6160218 A s P x h1 h2). Qed.
Lemma lem6160221 (p : Prop) : (term104 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6160222 : term106 = False.
Proof. exact (@lem6160221 False). Qed.
Lemma lem6160223 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term206 A s P x) (h2 : term57 A s P x) : False.
Proof. exact (EQ_MP (@lem6160222) (@lem6160219 A s P x h1 h2)). Qed.
Lemma lem6160225 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term79 A s P x) : s x.
Proof. exact (proj1 (@lem6159996 A s P x h1)). Qed.
Lemma lem6160226 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term79 A s P x) : term103 A s x.
Proof. exact (fun h0 : term78 A s x => @lem6160225 A s P x h1). Qed.
Lemma lem6160228 (p : Prop) : (term104 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6160229 {A : Type'} (s : A -> Prop) (x : A) : (term103 A s x) = (s x).
Proof. exact (@lem6160228 (s x)). Qed.
Lemma lem6160230 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term79 A s P x) : s x.
Proof. exact (EQ_MP (@lem6160229 A s x) (@lem6160226 A s P x h1)). Qed.
Lemma lem6160233 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6160235 {A : Type'} (s : A -> Prop) (x : A) : (term78 A s x) = (term105 A s x).
Proof. exact (@lem6160233 (s x)). Qed.
Lemma lem6160238 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term206 A s P x) : term105 A s x.
Proof. exact (EQ_MP (@lem6160235 A s x) (@lem6160104 A s P x h1)). Qed.
Lemma lem6160241 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term206 A s P x) (h2 : term79 A s P x) : False.
Proof. exact (@lem6160238 A s P x h1 (@lem6160230 A s P x h2)). Qed.
Lemma lem6160242 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term206 A s P x) (h2 : term79 A s P x) : term106.
Proof. exact (fun h0 : ~ False => @lem6160241 A s P x h1 h2). Qed.
Lemma lem6160244 (p : Prop) : (term104 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6160245 : term106 = False.
Proof. exact (@lem6160244 False). Qed.
Lemma lem6160246 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term206 A s P x) (h2 : term79 A s P x) : False.
Proof. exact (EQ_MP (@lem6160245) (@lem6160242 A s P x h1 h2)). Qed.
Lemma lem6160247 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : (term78 A P x) = False.
Proof. exact (prop_ext (fun h3 : term78 A P x => @lem6160200 A P x h1 h2) (fun h3 : False => @lem6160096 A P x h1)). Qed.
Lemma lem6160248 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : False.
Proof. exact (EQ_MP (@lem6160247 A P x h1 h2) (@lem6160096 A P x h1)). Qed.
Lemma lem6160249 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : (P x) = False.
Proof. exact (prop_ext (fun h3 : P x => @lem6160248 A P x h1 h2) (fun h3 : False => @lem6160094 A P x h2)). Qed.
Lemma lem6160250 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : False.
Proof. exact (EQ_MP (@lem6160249 A P x h1 h2) (@lem6160094 A P x h2)). Qed.
Lemma lem6160251 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : (term78 A s x) = False.
Proof. exact (prop_ext (fun h3 : term78 A s x => @lem6160177 A s P x h1 h2) (fun h3 : False => @lem6160090 A s x h1)). Qed.
Lemma lem6160252 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160251 A s P x h1 h2) (@lem6160090 A s x h1)). Qed.
Lemma lem6160253 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : (term78 A s x) = False.
Proof. exact (prop_ext (fun h3 : term78 A s x => @lem6160154 A s P x h1 h2) (fun h3 : False => @lem6160082 A s x h1)). Qed.
Lemma lem6160254 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160253 A s P x h1 h2) (@lem6160082 A s x h1)). Qed.
Lemma lem6160255 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : (term78 A s x) = False.
Proof. exact (prop_ext (fun h3 : term78 A s x => @lem6160131 A s P x h1 h2) (fun h3 : False => @lem6160078 A s x h1)). Qed.
Lemma lem6160256 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160255 A s P x h1 h2) (@lem6160078 A s x h1)). Qed.
Lemma lem6160257 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : (term78 A s x) = False.
Proof. exact (prop_ext (fun h3 : term78 A s x => @lem6160256 A s P x h1 h2) (fun h3 : False => @lem6160076 A s x h1)). Qed.
Lemma lem6160258 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160257 A s P x h1 h2) (@lem6160076 A s x h1)). Qed.
Lemma lem6160259 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : (term78 A P x) = False.
Proof. exact (prop_ext (fun h3 : term78 A P x => @lem6160250 A P x h1 h2) (fun h3 : False => @lem6160048 A P x h1)). Qed.
Lemma lem6160260 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : False.
Proof. exact (EQ_MP (@lem6160259 A P x h1 h2) (@lem6160048 A P x h1)). Qed.
Lemma lem6160261 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : (P x) = False.
Proof. exact (prop_ext (fun h3 : P x => @lem6160260 A P x h1 h2) (fun h3 : False => @lem6160044 A P x h2)). Qed.
Lemma lem6160262 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : False.
Proof. exact (EQ_MP (@lem6160261 A P x h1 h2) (@lem6160044 A P x h2)). Qed.
Lemma lem6160263 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : (term78 A s x) = False.
Proof. exact (prop_ext (fun h3 : term78 A s x => @lem6160252 A s P x h1 h2) (fun h3 : False => @lem6160036 A s x h1)). Qed.
Lemma lem6160264 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160263 A s P x h1 h2) (@lem6160036 A s x h1)). Qed.
Lemma lem6160265 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : (term78 A s x) = False.
Proof. exact (prop_ext (fun h3 : term78 A s x => @lem6160254 A s P x h1 h2) (fun h3 : False => @lem6160020 A s x h1)). Qed.
Lemma lem6160266 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160265 A s P x h1 h2) (@lem6160020 A s x h1)). Qed.
Lemma lem6160267 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : (term78 A s x) = False.
Proof. exact (prop_ext (fun h3 : term78 A s x => @lem6160258 A s P x h1 h2) (fun h3 : False => @lem6160012 A s x h1)). Qed.
Lemma lem6160268 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160267 A s P x h1 h2) (@lem6160012 A s x h1)). Qed.
Lemma lem6160269 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : (term78 A s x) = False.
Proof. exact (prop_ext (fun h3 : term78 A s x => @lem6160268 A s P x h1 h2) (fun h3 : False => @lem6160008 A s x h1)). Qed.
Lemma lem6160270 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160269 A s P x h1 h2) (@lem6160008 A s x h1)). Qed.
Lemma lem6160271 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : (term78 A P x) = False.
Proof. exact (prop_ext (fun h3 : term78 A P x => @lem6160262 A P x h1 h2) (fun h3 : False => @lem6160048 A P x h1)). Qed.
Lemma lem6160272 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : False.
Proof. exact (EQ_MP (@lem6160271 A P x h1 h2) (@lem6160048 A P x h1)). Qed.
Lemma lem6160273 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : (P x) = False.
Proof. exact (prop_ext (fun h3 : P x => @lem6160272 A P x h1 h2) (fun h3 : False => @lem6160044 A P x h2)). Qed.
Lemma lem6160274 {A : Type'} (P : A -> Prop) (x : A) (h1 : term78 A P x) (h2 : P x) : False.
Proof. exact (EQ_MP (@lem6160273 A P x h1 h2) (@lem6160044 A P x h2)). Qed.
Lemma lem6160275 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : (term78 A s x) = False.
Proof. exact (prop_ext (fun h3 : term78 A s x => @lem6160264 A s P x h1 h2) (fun h3 : False => @lem6160036 A s x h1)). Qed.
Lemma lem6160276 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160275 A s P x h1 h2) (@lem6160036 A s x h1)). Qed.
Lemma lem6160277 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : (term78 A s x) = False.
Proof. exact (prop_ext (fun h3 : term78 A s x => @lem6160266 A s P x h1 h2) (fun h3 : False => @lem6160020 A s x h1)). Qed.
Lemma lem6160278 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160277 A s P x h1 h2) (@lem6160020 A s x h1)). Qed.
Lemma lem6160279 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : (term78 A s x) = False.
Proof. exact (prop_ext (fun h3 : term78 A s x => @lem6160270 A s P x h1 h2) (fun h3 : False => @lem6160012 A s x h1)). Qed.
Lemma lem6160280 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160279 A s P x h1 h2) (@lem6160012 A s x h1)). Qed.
Lemma lem6160281 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : (term78 A s x) = False.
Proof. exact (prop_ext (fun h3 : term78 A s x => @lem6160280 A s P x h1 h2) (fun h3 : False => @lem6160008 A s x h1)). Qed.
Lemma lem6160282 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (EQ_MP (@lem6160281 A s P x h1 h2) (@lem6160008 A s x h1)). Qed.
Lemma lem6160283 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term206 A s P x) : False.
Proof. exact (or_elim (@lem6159993 A s P x h1) (fun h0 : term57 A s P x => @lem6160223 A s P x h1 h0) (fun h0 : term79 A s P x => @lem6160246 A s P x h1 h0)). Qed.
Lemma lem6160284 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : P x) (h2 : term208 A s P x) : False.
Proof. exact (or_elim (@lem6159986 A s P x h2) (fun h0 : term78 A s x => @lem6160276 A s P x h0 h2) (fun h0 : term78 A P x => @lem6160274 A P x h0 h1)). Qed.
Lemma lem6160285 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term78 A s x) (h2 : term208 A s P x) : False.
Proof. exact (or_elim (@lem6159986 A s P x h2) (fun h0 : term78 A s x => @lem6160282 A s P x h1 h2) (fun h0 : term78 A P x => @lem6160278 A s P x h1 h2)). Qed.
Lemma lem6160286 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term208 A s P x) : False.
Proof. exact (or_elim (@lem6159985 A s P x h1) (fun h0 : term78 A s x => @lem6160285 A s P x h0 h1) (fun h0 : P x => @lem6160284 A s P x h0 h1)). Qed.
Lemma lem6160287 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term193 A s P x) : False.
Proof. exact (or_elim (@lem6159980 A s P x h1) (fun h0 : term208 A s P x => @lem6160286 A s P x h0) (fun h0 : term206 A s P x => @lem6160283 A s P x h0)). Qed.
Lemma lem6160288 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term193 A s P x) : (term193 A s P x) = False.
Proof. exact (prop_ext (fun h2 : term193 A s P x => @lem6160287 A s P x h1) (fun h2 : False => @lem6159860 A s P x h1)). Qed.
Lemma lem6160289 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term193 A s P x) : False.
Proof. exact (EQ_MP (@lem6160288 A s P x h1) (@lem6159860 A s P x h1)). Qed.
Lemma lem6160290 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : term192 A s P x.
Proof. exact (fun h0 : term193 A s P x => @lem6160289 A s P x h0). Qed.
Lemma lem6160291 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (s x) = (term174 A s P x).
Proof. exact (EQ_MP (@lem6159859 A s P x) (@lem6160290 A s P x)). Qed.
Lemma lem6160296 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term177 A s P.
Proof. exact (fun x : A => @lem6160291 A s P x). Qed.
Lemma lem6160301 {A : Type'} (P : A -> Prop) : term187 A P.
Proof. exact (fun s : A -> Prop => @lem6160296 A s P). Qed.
Lemma lem6160306 {A : Type'} : term191 A.
Proof. exact (fun P : A -> Prop => @lem6160301 A P). Qed.
Lemma lem6160307 {A : Type'} : term190 A.
Proof. exact (EQ_MP (@lem6159855 A) (@lem6160306 A)). Qed.
Lemma lem6160308 {A : Type'} (P : A -> Prop) : term213 A P.
Proof. exact (@lem6160307 A P). Qed.
Lemma lem6160309 {A : Type'} (P : A -> Prop) : (term213 A P) = (term186 A P).
Proof. exact (eq_refl (term213 A P)). Qed.
Lemma lem6160310 {A : Type'} (P : A -> Prop) : term186 A P.
Proof. exact (EQ_MP (@lem6160309 A P) (@lem6160308 A P)). Qed.
Lemma lem6160311 {A : Type'} (P : A -> Prop) (s : A -> Prop) : term214 A P s.
Proof. exact (@lem6160310 A P s). Qed.
Lemma lem6160312 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term214 A P s) = (term178 A s P).
Proof. exact (eq_refl (term214 A P s)). Qed.
Lemma lem6160313 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term178 A s P.
Proof. exact (EQ_MP (@lem6160312 A s P) (@lem6160311 A P s)). Qed.
Lemma lem6160315 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term178 A s P.
Proof. exact (@lem6159756 A s P (@lem6160313 A s P)). Qed.
Lemma lem6160316 {A : Type'} (s : A -> Prop) (P : A -> Prop) (h1 : term179 A s P) : False.
Proof. exact (@lem6160315 A s P (@lem6159740 A s P h1)). Qed.
Lemma lem6160317 {A : Type'} (s : A -> Prop) (P : A -> Prop) (h1 : term179 A s P) : (term179 A s P) = False.
Proof. exact (prop_ext (fun h2 : term179 A s P => @lem6160316 A s P h1) (fun h2 : False => @lem6159740 A s P h1)). Qed.
Lemma lem6160318 {A : Type'} (s : A -> Prop) (P : A -> Prop) (h1 : term179 A s P) : False.
Proof. exact (EQ_MP (@lem6160317 A s P h1) (@lem6159740 A s P h1)). Qed.
Lemma lem6160319 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term178 A s P.
Proof. exact (fun h0 : term179 A s P => @lem6160318 A s P h0). Qed.
Lemma lem6160320 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term177 A s P.
Proof. exact (EQ_MP (@lem6159739 A s P) (@lem6160319 A s P)). Qed.
Lemma lem6160321 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term165 A s P.
Proof. exact (EQ_MP (@lem6159735 A s P) (@lem6160320 A s P)). Qed.
Lemma lem6160322 {A : Type'} (s : A -> Prop) (P : A -> Prop) : s = (term164 A s P).
Proof. exact (EQ_MP (@lem6159630 A s P) (@lem6160321 A s P)). Qed.
Lemma lem6160323 {A B : Type'} (op : type1400 B) (s : A -> Prop) (P : A -> Prop) : (@iterate B A op s) = (term215 A B op s P).
Proof. exact (MK_COMB (@lem6159603 A B op) (@lem6160322 A s P)). Qed.
Lemma lem6160324 {A B : Type'} (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) : (term25 A B op s P f g) = (term162 A B op s P f g).
Proof. exact (MK_COMB (@lem6160323 A B op s P) (@lem6159602 A B P f g)). Qed.
Lemma lem6160325 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) : (term25 A B op s P f g) = (term161 A B op s P f g).
Proof. exact (EQ_MP (@lem6159601 A B P f g s op h1 h2) (@lem6160324 A B op s P f g)). Qed.
Lemma lem6160326 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6160330 {A B : Type'} (op : type1400 B) : term6 A B op.
Proof. exact (EQ_MP (@lem6158439 A B op) (@lem6158438 A B op)). Qed.
Lemma lem6160331 {A B : Type'} (op : type1400 B) : term6 A B op.
Proof. exact (@lem6160330 A B op). Qed.
Lemma lem6160332 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term216 A B op.
Proof. exact (@lem6160331 A B op (@lem6158479 B op h1)). Qed.
Lemma lem6160333 {A B : Type'} (op : type1400 B) (h1 : term216 A B op) : term216 A B op.
Proof. exact (h1). Qed.
Lemma lem6160334 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term216 A B op) : term217 A B op f.
Proof. exact (@lem6160333 A B op h1 f). Qed.
Lemma lem6160335 {A B : Type'} (f : A -> B) (op : type1400 B) : (term217 A B op f) = (term218 A B f op).
Proof. exact (eq_refl (term217 A B op f)). Qed.
Lemma lem6160336 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term216 A B op) : term218 A B f op.
Proof. exact (EQ_MP (@lem6160335 A B f op) (@lem6160334 A B f op h1)). Qed.
Lemma lem6160337 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term216 A B op) : term219 A B f op g.
Proof. exact (@lem6160336 A B f op h1 g). Qed.
Lemma lem6160338 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term219 A B f op g) = (term220 A B f op g).
Proof. exact (eq_refl (term219 A B f op g)). Qed.
Lemma lem6160339 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term216 A B op) : term220 A B f op g.
Proof. exact (EQ_MP (@lem6160338 A B f op g) (@lem6160337 A B f g op h1)). Qed.
Lemma lem6160340 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term216 A B op) : term221 A B f op g s.
Proof. exact (@lem6160339 A B f g op h1 s). Qed.
Lemma lem6160341 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term221 A B f op g s) = (term222 A B f op s g).
Proof. exact (eq_refl (term221 A B f op g s)). Qed.
Lemma lem6160342 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term216 A B op) : term222 A B f op s g.
Proof. exact (EQ_MP (@lem6160341 A B f op s g) (@lem6160340 A B f g s op h1)). Qed.
Lemma lem6160343 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term223 A B s f g) : term223 A B s f g.
Proof. exact (h1). Qed.
Lemma lem6160344 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term223 A B s f g) (h2 : term216 A B op) : (@iterate B A op s f) = (@iterate B A op s g).
Proof. exact (@lem6160342 A B f s g op h2 (@lem6160343 A B s f g h1)). Qed.
Lemma lem6160345 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term223 A B s f g) : term224 A B f op s g.
Proof. exact (fun h0 : term216 A B op => @lem6160344 A B s f g op h1 h0). Qed.
Lemma lem6160346 {A B : Type'} (op : type1400 B) (h1 : term216 A B op) : term216 A B op.
Proof. exact (h1). Qed.
Lemma lem6160347 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term223 A B s f g) (h2 : term216 A B op) : (@iterate B A op s f) = (@iterate B A op s g).
Proof. exact (@lem6160345 A B op s f g h1 (@lem6160346 A B op h2)). Qed.
Lemma lem6160348 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term216 A B op) : term222 A B f op s g.
Proof. exact (fun h0 : term223 A B s f g => @lem6160347 A B s f g op h0 h1). Qed.
Lemma lem6160349 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term216 A B op) : term225 A B f op s.
Proof. exact (fun g : A -> B => @lem6160348 A B f s g op h1). Qed.
Lemma lem6160350 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term216 A B op) : term226 A B f op.
Proof. exact (fun s : A -> Prop => @lem6160349 A B f s op h1). Qed.
Lemma lem6160351 {A B : Type'} (op : type1400 B) (h1 : term216 A B op) : term227 A B op.
Proof. exact (fun f : A -> B => @lem6160350 A B f op h1). Qed.
Lemma lem6160352 {A B : Type'} (op : type1400 B) : term228 A B op.
Proof. exact (fun h0 : term216 A B op => @lem6160351 A B op h0). Qed.
Lemma lem6160353 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term227 A B op.
Proof. exact (@lem6160352 A B op (@lem6160332 A B op h1)). Qed.
Lemma lem6160354 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term229 A B op f.
Proof. exact (@lem6160353 A B op h1 f). Qed.
Lemma lem6160355 {A B : Type'} (f : A -> B) (op : type1400 B) : (term229 A B op f) = (term226 A B f op).
Proof. exact (eq_refl (term229 A B op f)). Qed.
Lemma lem6160356 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term226 A B f op.
Proof. exact (EQ_MP (@lem6160355 A B f op) (@lem6160354 A B f op h1)). Qed.
Lemma lem6160357 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term230 A B f op s.
Proof. exact (@lem6160356 A B f op h1 s). Qed.
Lemma lem6160358 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term230 A B f op s) = (term225 A B f op s).
Proof. exact (eq_refl (term230 A B f op s)). Qed.
Lemma lem6160359 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term225 A B f op s.
Proof. exact (EQ_MP (@lem6160358 A B f op s) (@lem6160357 A B f s op h1)). Qed.
Lemma lem6160360 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term231 A B f op s g.
Proof. exact (@lem6160359 A B f s op h1 g). Qed.
Lemma lem6160361 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term231 A B f op s g) = (term222 A B f op s g).
Proof. exact (eq_refl (term231 A B f op s g)). Qed.
Lemma lem6160364 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term222 A B f op s g.
Proof. exact (EQ_MP (@lem6160361 A B f op s g) (@lem6160360 A B f s g op h1)). Qed.
Lemma lem6160365 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term222 A B f op s g.
Proof. exact (@lem6160364 A B f s g op h1). Qed.
Lemma lem6160366 {A B : Type'} (g : A -> B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term232 A B g op s P f.
Proof. exact (@lem6160365 A B (term139 A B P f g) (term29 A s P) f op h1). Qed.
Lemma lem6160369 {A B : Type'} (g : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) : (term233 A B g op s P f) = (term233 A B g op s P f).
Proof. exact (eq_refl (term233 A B g op s P f)). Qed.
Lemma lem6160370 {A B : Type'} (g : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) : (term233 A B g op s P f) = (term232 A B g op s P f).
Proof. exact (eq_refl (term233 A B g op s P f)). Qed.
Lemma lem6160371 {A B : Type'} (g : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) : (term234 A B g op s P f) = (term234 A B g op s P f).
Proof. exact (eq_refl (term234 A B g op s P f)). Qed.
Lemma lem6160372 {A B : Type'} (g : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) : ((term233 A B g op s P f) = (term233 A B g op s P f)) = ((term233 A B g op s P f) = (term232 A B g op s P f)).
Proof. exact (MK_COMB (@lem6160371 A B g op s P f) (@lem6160370 A B g op s P f)). Qed.
Lemma lem6160373 {A B : Type'} (g : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) : (term233 A B g op s P f) = (term232 A B g op s P f).
Proof. exact (eq_refl (term233 A B g op s P f)). Qed.
Lemma lem6160374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6160375 {A B : Type'} (g : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) : (term234 A B g op s P f) = (term235 A B g op s P f).
Proof. exact (MK_COMB (@lem6160374) (@lem6160373 A B g op s P f)). Qed.
Lemma lem6160376 {A B : Type'} (g : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) : (term232 A B g op s P f) = (term232 A B g op s P f).
Proof. exact (eq_refl (term232 A B g op s P f)). Qed.
Lemma lem6160377 {A B : Type'} (g : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) : ((term233 A B g op s P f) = (term232 A B g op s P f)) = ((term232 A B g op s P f) = (term232 A B g op s P f)).
Proof. exact (MK_COMB (@lem6160375 A B g op s P f) (@lem6160376 A B g op s P f)). Qed.
Lemma lem6160378 {A B : Type'} (g : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) : ((term233 A B g op s P f) = (term233 A B g op s P f)) = ((term232 A B g op s P f) = (term232 A B g op s P f)).
Proof. exact (TRANS (@lem6160372 A B g op s P f) (@lem6160377 A B g op s P f)). Qed.
Lemma lem6160379 {A B : Type'} (g : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) : (term232 A B g op s P f) = (term232 A B g op s P f).
Proof. exact (EQ_MP (@lem6160378 A B g op s P f) (@lem6160369 A B g op s P f)). Qed.
Lemma lem6160380 {A B : Type'} (g : A -> B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term232 A B g op s P f.
Proof. exact (EQ_MP (@lem6160379 A B g op s P f) (@lem6160366 A B g s P f op h1)). Qed.
Lemma lem6160384 {A B : Type'} (op : type1400 B) : term6 A B op.
Proof. exact (EQ_MP (@lem6158439 A B op) (@lem6158438 A B op)). Qed.
Lemma lem6160385 {A B : Type'} (op : type1400 B) : term6 A B op.
Proof. exact (@lem6160384 A B op). Qed.
Lemma lem6160386 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term216 A B op.
Proof. exact (@lem6160385 A B op (@lem6158479 B op h1)). Qed.
Lemma lem6160387 {A B : Type'} (op : type1400 B) (h1 : term216 A B op) : term216 A B op.
Proof. exact (h1). Qed.
Lemma lem6160388 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term216 A B op) : term217 A B op f.
Proof. exact (@lem6160387 A B op h1 f). Qed.
Lemma lem6160389 {A B : Type'} (f : A -> B) (op : type1400 B) : (term217 A B op f) = (term218 A B f op).
Proof. exact (eq_refl (term217 A B op f)). Qed.
Lemma lem6160390 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term216 A B op) : term218 A B f op.
Proof. exact (EQ_MP (@lem6160389 A B f op) (@lem6160388 A B f op h1)). Qed.
Lemma lem6160391 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term216 A B op) : term219 A B f op g.
Proof. exact (@lem6160390 A B f op h1 g). Qed.
Lemma lem6160392 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term219 A B f op g) = (term220 A B f op g).
Proof. exact (eq_refl (term219 A B f op g)). Qed.
Lemma lem6160393 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term216 A B op) : term220 A B f op g.
Proof. exact (EQ_MP (@lem6160392 A B f op g) (@lem6160391 A B f g op h1)). Qed.
Lemma lem6160394 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term216 A B op) : term221 A B f op g s.
Proof. exact (@lem6160393 A B f g op h1 s). Qed.
Lemma lem6160395 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term221 A B f op g s) = (term222 A B f op s g).
Proof. exact (eq_refl (term221 A B f op g s)). Qed.
Lemma lem6160396 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term216 A B op) : term222 A B f op s g.
Proof. exact (EQ_MP (@lem6160395 A B f op s g) (@lem6160394 A B f g s op h1)). Qed.
Lemma lem6160397 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term223 A B s f g) : term223 A B s f g.
Proof. exact (h1). Qed.
Lemma lem6160398 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term223 A B s f g) (h2 : term216 A B op) : (@iterate B A op s f) = (@iterate B A op s g).
Proof. exact (@lem6160396 A B f s g op h2 (@lem6160397 A B s f g h1)). Qed.
Lemma lem6160399 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term223 A B s f g) : term224 A B f op s g.
Proof. exact (fun h0 : term216 A B op => @lem6160398 A B s f g op h1 h0). Qed.
Lemma lem6160400 {A B : Type'} (op : type1400 B) (h1 : term216 A B op) : term216 A B op.
Proof. exact (h1). Qed.
Lemma lem6160401 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term223 A B s f g) (h2 : term216 A B op) : (@iterate B A op s f) = (@iterate B A op s g).
Proof. exact (@lem6160399 A B op s f g h1 (@lem6160400 A B op h2)). Qed.
Lemma lem6160402 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term216 A B op) : term222 A B f op s g.
Proof. exact (fun h0 : term223 A B s f g => @lem6160401 A B s f g op h0 h1). Qed.
Lemma lem6160403 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term216 A B op) : term225 A B f op s.
Proof. exact (fun g : A -> B => @lem6160402 A B f s g op h1). Qed.
Lemma lem6160404 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term216 A B op) : term226 A B f op.
Proof. exact (fun s : A -> Prop => @lem6160403 A B f s op h1). Qed.
Lemma lem6160405 {A B : Type'} (op : type1400 B) (h1 : term216 A B op) : term227 A B op.
Proof. exact (fun f : A -> B => @lem6160404 A B f op h1). Qed.
Lemma lem6160406 {A B : Type'} (op : type1400 B) : term228 A B op.
Proof. exact (fun h0 : term216 A B op => @lem6160405 A B op h0). Qed.
Lemma lem6160407 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term227 A B op.
Proof. exact (@lem6160406 A B op (@lem6160386 A B op h1)). Qed.
Lemma lem6160408 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term229 A B op f.
Proof. exact (@lem6160407 A B op h1 f). Qed.
Lemma lem6160409 {A B : Type'} (f : A -> B) (op : type1400 B) : (term229 A B op f) = (term226 A B f op).
Proof. exact (eq_refl (term229 A B op f)). Qed.
Lemma lem6160410 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term226 A B f op.
Proof. exact (EQ_MP (@lem6160409 A B f op) (@lem6160408 A B f op h1)). Qed.
Lemma lem6160411 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term230 A B f op s.
Proof. exact (@lem6160410 A B f op h1 s). Qed.
Lemma lem6160412 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term230 A B f op s) = (term225 A B f op s).
Proof. exact (eq_refl (term230 A B f op s)). Qed.
Lemma lem6160413 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term225 A B f op s.
Proof. exact (EQ_MP (@lem6160412 A B f op s) (@lem6160411 A B f s op h1)). Qed.
Lemma lem6160414 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term231 A B f op s g.
Proof. exact (@lem6160413 A B f s op h1 g). Qed.
Lemma lem6160415 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term231 A B f op s g) = (term222 A B f op s g).
Proof. exact (eq_refl (term231 A B f op s g)). Qed.
Lemma lem6160418 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term222 A B f op s g.
Proof. exact (EQ_MP (@lem6160415 A B f op s g) (@lem6160414 A B f s g op h1)). Qed.
Lemma lem6160419 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term222 A B f op s g.
Proof. exact (@lem6160418 A B f s g op h1). Qed.
Lemma lem6160420 {A B : Type'} (f : A -> B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term236 A B f op s P g.
Proof. exact (@lem6160419 A B (term139 A B P f g) (term30 A s P) g op h1). Qed.
Lemma lem6160423 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) : (term237 A B f op s P g) = (term237 A B f op s P g).
Proof. exact (eq_refl (term237 A B f op s P g)). Qed.
Lemma lem6160424 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) : (term237 A B f op s P g) = (term236 A B f op s P g).
Proof. exact (eq_refl (term237 A B f op s P g)). Qed.
Lemma lem6160425 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) : (term238 A B f op s P g) = (term238 A B f op s P g).
Proof. exact (eq_refl (term238 A B f op s P g)). Qed.
Lemma lem6160426 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) : ((term237 A B f op s P g) = (term237 A B f op s P g)) = ((term237 A B f op s P g) = (term236 A B f op s P g)).
Proof. exact (MK_COMB (@lem6160425 A B f op s P g) (@lem6160424 A B f op s P g)). Qed.
Lemma lem6160427 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) : (term237 A B f op s P g) = (term236 A B f op s P g).
Proof. exact (eq_refl (term237 A B f op s P g)). Qed.
Lemma lem6160428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6160429 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) : (term238 A B f op s P g) = (term239 A B f op s P g).
Proof. exact (MK_COMB (@lem6160428) (@lem6160427 A B f op s P g)). Qed.
Lemma lem6160430 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) : (term236 A B f op s P g) = (term236 A B f op s P g).
Proof. exact (eq_refl (term236 A B f op s P g)). Qed.
Lemma lem6160431 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) : ((term237 A B f op s P g) = (term236 A B f op s P g)) = ((term236 A B f op s P g) = (term236 A B f op s P g)).
Proof. exact (MK_COMB (@lem6160429 A B f op s P g) (@lem6160430 A B f op s P g)). Qed.
Lemma lem6160432 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) : ((term237 A B f op s P g) = (term237 A B f op s P g)) = ((term236 A B f op s P g) = (term236 A B f op s P g)).
Proof. exact (TRANS (@lem6160426 A B f op s P g) (@lem6160431 A B f op s P g)). Qed.
Lemma lem6160433 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) : (term236 A B f op s P g) = (term236 A B f op s P g).
Proof. exact (EQ_MP (@lem6160432 A B f op s P g) (@lem6160423 A B f op s P g)). Qed.
Lemma lem6160434 {A B : Type'} (f : A -> B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term236 A B f op s P g.
Proof. exact (EQ_MP (@lem6160433 A B f op s P g) (@lem6160420 A B f s P g op h1)). Qed.
Lemma lem6160442 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term240 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6160443 (p : Prop) (q : Prop) (p' : Prop) : term241 p q p'.
Proof. exact (fun q' : Prop => @lem6160442 p q p' q'). Qed.
Lemma lem6160444 (p : Prop) (q : Prop) : term242 p q.
Proof. exact (fun p' : Prop => @lem6160443 p q p'). Qed.
Lemma lem6160445 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> B) (f : A -> B) (x : A) : term243 A B s P g f x.
Proof. exact (@lem6160444 (term52 A x s P) ((term244 A B P f g x) = (f x))). Qed.
Lemma lem6160446 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> B) (f : A -> B) (x : A) (p' : Prop) : term245 A B s P g f x p'.
Proof. exact (@lem6160445 A B s P g f x p'). Qed.
Lemma lem6160447 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> B) (f : A -> B) (x : A) (p' : Prop) : (term245 A B s P g f x p') = (term246 A B s P g f x p').
Proof. exact (eq_refl (term245 A B s P g f x p')). Qed.
Lemma lem6160448 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> B) (f : A -> B) (x : A) (p' : Prop) : term246 A B s P g f x p'.
Proof. exact (EQ_MP (@lem6160447 A B s P g f x p') (@lem6160446 A B s P g f x p')). Qed.
Lemma lem6160449 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> B) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term247 A B s P g f x p' q'.
Proof. exact (@lem6160448 A B s P g f x p' q'). Qed.
Lemma lem6160450 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> B) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : (term247 A B s P g f x p' q') = (term248 A B s P g f x p' q').
Proof. exact (eq_refl (term247 A B s P g f x p' q')). Qed.
Lemma lem6160451 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> B) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term248 A B s P g f x p' q'.
Proof. exact (EQ_MP (@lem6160450 A B s P g f x p' q') (@lem6160449 A B s P g f x p' q')). Qed.
Lemma lem6160453 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6158429 _83095 p x) (@lem6158428 _83095 p x)). Qed.
Lemma lem6160454 {A : Type'} (p : A -> Prop) (x : A) : (term4 A x p) = (p x).
Proof. exact (@lem6160453 A p x). Qed.
Lemma lem6160455 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term37 A x s P) = (term38 A s P x).
Proof. exact (@lem6160454 A (term39 A s P) x). Qed.
Lemma lem6160456 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term38 A s P x) = (term40 A s P x).
Proof. exact (eq_refl (term38 A s P x)). Qed.
Lemma lem6160457 {A : Type'} (GEN_PVAR_246 : A) : (@SETSPEC A GEN_PVAR_246) = (@SETSPEC A GEN_PVAR_246).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_246)). Qed.
Lemma lem6160458 {A : Type'} (GEN_PVAR_246 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term41 A GEN_PVAR_246 s P x) = (term42 A GEN_PVAR_246 s P x).
Proof. exact (MK_COMB (@lem6160457 A GEN_PVAR_246) (@lem6160456 A s P x)). Qed.
Lemma lem6160459 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6160460 {A : Type'} (GEN_PVAR_246 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term43 A GEN_PVAR_246 s P x) = (term44 A GEN_PVAR_246 s P x).
Proof. exact (MK_COMB (@lem6160458 A GEN_PVAR_246 s P x) (@lem6160459 A x)). Qed.
Lemma lem6160461 {A : Type'} (GEN_PVAR_246 : A) (s : A -> Prop) (P : A -> Prop) : (term45 A GEN_PVAR_246 s P) = (term46 A GEN_PVAR_246 s P).
Proof. exact (fun_ext (fun x : A => @lem6160460 A GEN_PVAR_246 s P x)). Qed.
Lemma lem6160462 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6160463 {A : Type'} (GEN_PVAR_246 : A) (s : A -> Prop) (P : A -> Prop) : (term47 A GEN_PVAR_246 s P) = (term48 A GEN_PVAR_246 s P).
Proof. exact (MK_COMB (@lem6160462 A) (@lem6160461 A GEN_PVAR_246 s P)). Qed.
Lemma lem6160464 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term49 A s P) = (term50 A s P).
Proof. exact (fun_ext (fun GEN_PVAR_246 : A => @lem6160463 A GEN_PVAR_246 s P)). Qed.
Lemma lem6160465 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6160466 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term51 A s P) = (term29 A s P).
Proof. exact (MK_COMB (@lem6160465 A) (@lem6160464 A s P)). Qed.
Lemma lem6160467 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6160468 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term37 A x s P) = (term52 A x s P).
Proof. exact (MK_COMB (@lem6160467 A x) (@lem6160466 A s P)). Qed.
Lemma lem6160469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6160470 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term53 A x s P) = (term54 A x s P).
Proof. exact (MK_COMB (@lem6160469) (@lem6160468 A x s P)). Qed.
Lemma lem6160471 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term38 A s P x) = (term40 A s P x).
Proof. exact (eq_refl (term38 A s P x)). Qed.
Lemma lem6160472 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : ((term37 A x s P) = (term38 A s P x)) = ((term52 A x s P) = (term40 A s P x)).
Proof. exact (MK_COMB (@lem6160470 A x s P) (@lem6160471 A s P x)). Qed.
Lemma lem6160473 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term52 A x s P) = (term40 A s P x).
Proof. exact (EQ_MP (@lem6160472 A s P x) (@lem6160455 A s P x)). Qed.
Lemma lem6160476 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (q' : Prop) : term249 A B g f s P x q'.
Proof. exact (@lem6160451 A B s P g f x (term40 A s P x) q'). Qed.
Lemma lem6160477 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (q' : Prop) : term250 A B g f s P x q'.
Proof. exact (@lem6160476 A B g f s P x q' (@lem6160473 A s P x)). Qed.
Lemma lem6160478 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term40 A s P x) : term40 A s P x.
Proof. exact (h1). Qed.
Lemma lem6160479 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term40 A s P x) : P x.
Proof. exact (proj2 (@lem6160478 A s P x h1)). Qed.
Lemma lem6160480 {A : Type'} (P : A -> Prop) (x : A) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem6160488 {A B : Type'} (f : A -> B) (y : A) : (term251 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6160489 {A B : Type'} (f : A -> B) (y : A) : (term251 A B f y) = (f y).
Proof. exact (@lem6160488 A B f y). Qed.
Lemma lem6160490 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term252 A B P f g x) = (term244 A B P f g x).
Proof. exact (@lem6160489 A B (term139 A B P f g) x). Qed.
Lemma lem6160491 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term244 A B P f g x) = (term253 A B P f g x).
Proof. exact (eq_refl (term244 A B P f g x)). Qed.
Lemma lem6160492 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) : (term254 A B P f g) = (term139 A B P f g).
Proof. exact (fun_ext (fun x : A => @lem6160491 A B P f g x)). Qed.
Lemma lem6160493 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6160494 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term252 A B P f g x) = (term244 A B P f g x).
Proof. exact (MK_COMB (@lem6160492 A B P f g) (@lem6160493 A x)). Qed.
Lemma lem6160495 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6160496 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term255 A B P f g x) = (term256 A B P f g x).
Proof. exact (MK_COMB (@lem6160495 B) (@lem6160494 A B P f g x)). Qed.
Lemma lem6160497 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term244 A B P f g x) = (term253 A B P f g x).
Proof. exact (eq_refl (term244 A B P f g x)). Qed.
Lemma lem6160498 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : ((term252 A B P f g x) = (term244 A B P f g x)) = ((term244 A B P f g x) = (term253 A B P f g x)).
Proof. exact (MK_COMB (@lem6160496 A B P f g x) (@lem6160497 A B P f g x)). Qed.
Lemma lem6160499 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term244 A B P f g x) = (term253 A B P f g x).
Proof. exact (EQ_MP (@lem6160498 A B P f g x) (@lem6160490 A B P f g x)). Qed.
Lemma lem6160501 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term257 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6160502 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term258 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6160501 _2963 g t e g' t' e'). Qed.
Lemma lem6160503 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term259 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6160502 _2963 g t e g' t'). Qed.
Lemma lem6160504 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term260 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6160503 _2963 g t e g'). Qed.
Lemma lem6160505 {B : Type'} (g : Prop) (t : B) (e : B) : term260 B g t e.
Proof. exact (@lem6160504 B g t e). Qed.
Lemma lem6160506 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term261 A B P f g x.
Proof. exact (@lem6160505 B (P x) (f x) (g x)). Qed.
Lemma lem6160507 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) : term262 A B P f g x g'.
Proof. exact (@lem6160506 A B P f g x g'). Qed.
Lemma lem6160508 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) : (term262 A B P f g x g') = (term263 A B P f g x g').
Proof. exact (eq_refl (term262 A B P f g x g')). Qed.
Lemma lem6160509 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) : term263 A B P f g x g'.
Proof. exact (EQ_MP (@lem6160508 A B P f g x g') (@lem6160507 A B P f g x g')). Qed.
Lemma lem6160510 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) (t' : B) : term264 A B P f g x g' t'.
Proof. exact (@lem6160509 A B P f g x g' t'). Qed.
Lemma lem6160511 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) (t' : B) : (term264 A B P f g x g' t') = (term265 A B P f g x g' t').
Proof. exact (eq_refl (term264 A B P f g x g' t')). Qed.
Lemma lem6160512 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) (t' : B) : term265 A B P f g x g' t'.
Proof. exact (EQ_MP (@lem6160511 A B P f g x g' t') (@lem6160510 A B P f g x g' t')). Qed.
Lemma lem6160513 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : term266 A B P f g x g' t' e'.
Proof. exact (@lem6160512 A B P f g x g' t' e'). Qed.
Lemma lem6160514 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : (term266 A B P f g x g' t' e') = (term267 A B P f g x g' t' e').
Proof. exact (eq_refl (term266 A B P f g x g' t' e')). Qed.
Lemma lem6160515 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : term267 A B P f g x g' t' e'.
Proof. exact (EQ_MP (@lem6160514 A B P f g x g' t' e') (@lem6160513 A B P f g x g' t' e')). Qed.
Lemma lem6160517 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term40 A s P x) : (P x) = True.
Proof. exact (EQ_MP (@lem6160480 A P x) (@lem6160479 A s P x h1)). Qed.
Lemma lem6160518 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (t' : B) (e' : B) : term268 A B P f g x t' e'.
Proof. exact (@lem6160515 A B P f g x True t' e'). Qed.
Lemma lem6160519 {A B : Type'} (f : A -> B) (g : A -> B) (t' : B) (e' : B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term40 A s P x) : term269 A B P f g x t' e'.
Proof. exact (@lem6160518 A B P f g x t' e' (@lem6160517 A s P x h1)). Qed.
Lemma lem6160525 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem6160526 {A B : Type'} (f : A -> B) (x : A) : term270 A B f x.
Proof. exact (fun h0 : True => @lem6160525 A B f x). Qed.
Lemma lem6160527 {A B : Type'} (g : A -> B) (f : A -> B) (e' : B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term40 A s P x) : term271 A B P g f x e'.
Proof. exact (@lem6160519 A B f g (f x) e' s P x h1). Qed.
Lemma lem6160528 {A B : Type'} (g : A -> B) (f : A -> B) (e' : B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term40 A s P x) : term272 A B P g f x e'.
Proof. exact (@lem6160527 A B g f e' s P x h1 (@lem6160526 A B f x)). Qed.
Lemma lem6160532 {A B : Type'} (g : A -> B) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem6160533 {A B : Type'} (g : A -> B) (x : A) : term273 A B g x.
Proof. exact (fun h0 : ~ True => @lem6160532 A B g x). Qed.
Lemma lem6160534 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term40 A s P x) : term274 A B P f g x.
Proof. exact (@lem6160528 A B g f (g x) s P x h1). Qed.
Lemma lem6160535 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term40 A s P x) : (term253 A B P f g x) = (term275 A B f g x).
Proof. exact (@lem6160534 A B f g s P x h1 (@lem6160533 A B g x)). Qed.
Lemma lem6160537 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem6160538 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem6160537 B t2 t1). Qed.
Lemma lem6160539 {A B : Type'} (g : A -> B) (f : A -> B) (x : A) : (term275 A B f g x) = (f x).
Proof. exact (@lem6160538 B (g x) (f x)). Qed.
Lemma lem6160540 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term40 A s P x) : (term253 A B P f g x) = (f x).
Proof. exact (TRANS (@lem6160535 A B f g s P x h1) (@lem6160539 A B g f x)). Qed.
Lemma lem6160541 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term40 A s P x) : (term244 A B P f g x) = (f x).
Proof. exact (TRANS (@lem6160499 A B P f g x) (@lem6160540 A B g f s P x h1)). Qed.
Lemma lem6160542 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6160543 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term40 A s P x) : (term256 A B P f g x) = (term276 A B f x).
Proof. exact (MK_COMB (@lem6160542 B) (@lem6160541 A B g f s P x h1)). Qed.
Lemma lem6160544 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem6160545 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term40 A s P x) : ((term244 A B P f g x) = (f x)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem6160543 A B g f s P x h1) (@lem6160544 A B f x)). Qed.
Lemma lem6160547 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6160548 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem6160547 B x). Qed.
Lemma lem6160549 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (f x)) = True.
Proof. exact (@lem6160548 B (f x)). Qed.
Lemma lem6160550 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term40 A s P x) : ((term244 A B P f g x) = (f x)) = True.
Proof. exact (TRANS (@lem6160545 A B g f s P x h1) (@lem6160549 A B f x)). Qed.
Lemma lem6160551 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> B) (f : A -> B) (x : A) : term277 A B s P g f x.
Proof. exact (fun h0 : term40 A s P x => @lem6160550 A B g f s P x h0). Qed.
Lemma lem6160552 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) : term278 A B g f s P x.
Proof. exact (@lem6160477 A B g f s P x True). Qed.
Lemma lem6160553 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) : (term279 A B s P g f x) = (term280 A s P x).
Proof. exact (@lem6160552 A B g f s P x (@lem6160551 A B s P g f x)). Qed.
Lemma lem6160555 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6160556 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term280 A s P x) = True.
Proof. exact (@lem6160555 (term40 A s P x)). Qed.
Lemma lem6160557 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> B) (f : A -> B) (x : A) : (term279 A B s P g f x) = True.
Proof. exact (TRANS (@lem6160553 A B g f s P x) (@lem6160556 A s P x)). Qed.
Lemma lem6160558 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> B) (f : A -> B) : (term281 A B s P g f) = (term282 A).
Proof. exact (fun_ext (fun x : A => @lem6160557 A B s P g f x)). Qed.
Lemma lem6160559 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6160560 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> B) (f : A -> B) : (term283 A B s P g f) = (term284 A).
Proof. exact (MK_COMB (@lem6160559 A) (@lem6160558 A B s P g f)). Qed.
Lemma lem6160562 {A : Type'} (t : Prop) : (term285 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6160563 {A : Type'} (t : Prop) : (term285 A t) = t.
Proof. exact (@lem6160562 A t). Qed.
Lemma lem6160564 {A : Type'} : (term284 A) = True.
Proof. exact (@lem6160563 A True). Qed.
Lemma lem6160565 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> B) (f : A -> B) : (term283 A B s P g f) = True.
Proof. exact (TRANS (@lem6160560 A B s P g f) (@lem6160564 A)). Qed.
Lemma lem6160566 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> B) (f : A -> B) : True = (term283 A B s P g f).
Proof. exact (SYM (@lem6160565 A B s P g f)). Qed.
Lemma lem6160567 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> B) (f : A -> B) : term283 A B s P g f.
Proof. exact (EQ_MP (@lem6160566 A B s P g f) (@lem0)). Qed.
Lemma lem6160575 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term240 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6160576 (p : Prop) (q : Prop) (p' : Prop) : term241 p q p'.
Proof. exact (fun q' : Prop => @lem6160575 p q p' q'). Qed.
Lemma lem6160577 (p : Prop) (q : Prop) : term242 p q.
Proof. exact (fun p' : Prop => @lem6160576 p q p'). Qed.
Lemma lem6160578 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term286 A B s P f g x.
Proof. exact (@lem6160577 (term75 A x s P) ((term244 A B P f g x) = (g x))). Qed.
Lemma lem6160579 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) : term287 A B s P f g x p'.
Proof. exact (@lem6160578 A B s P f g x p'). Qed.
Lemma lem6160580 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) : (term287 A B s P f g x p') = (term288 A B s P f g x p').
Proof. exact (eq_refl (term287 A B s P f g x p')). Qed.
Lemma lem6160581 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) : term288 A B s P f g x p'.
Proof. exact (EQ_MP (@lem6160580 A B s P f g x p') (@lem6160579 A B s P f g x p')). Qed.
Lemma lem6160582 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) (q' : Prop) : term289 A B s P f g x p' q'.
Proof. exact (@lem6160581 A B s P f g x p' q'). Qed.
Lemma lem6160583 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) (q' : Prop) : (term289 A B s P f g x p' q') = (term290 A B s P f g x p' q').
Proof. exact (eq_refl (term289 A B s P f g x p' q')). Qed.
Lemma lem6160584 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) (q' : Prop) : term290 A B s P f g x p' q'.
Proof. exact (EQ_MP (@lem6160583 A B s P f g x p' q') (@lem6160582 A B s P f g x p' q')). Qed.
Lemma lem6160586 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6158429 _83095 p x) (@lem6158428 _83095 p x)). Qed.
Lemma lem6160587 {A : Type'} (p : A -> Prop) (x : A) : (term4 A x p) = (p x).
Proof. exact (@lem6160586 A p x). Qed.
Lemma lem6160588 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term60 A x s P) = (term61 A s P x).
Proof. exact (@lem6160587 A (term62 A s P) x). Qed.
Lemma lem6160589 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term61 A s P x) = (term63 A s P x).
Proof. exact (eq_refl (term61 A s P x)). Qed.
Lemma lem6160590 {A : Type'} (GEN_PVAR_247 : A) : (@SETSPEC A GEN_PVAR_247) = (@SETSPEC A GEN_PVAR_247).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_247)). Qed.
Lemma lem6160591 {A : Type'} (GEN_PVAR_247 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term64 A GEN_PVAR_247 s P x) = (term65 A GEN_PVAR_247 s P x).
Proof. exact (MK_COMB (@lem6160590 A GEN_PVAR_247) (@lem6160589 A s P x)). Qed.
Lemma lem6160592 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6160593 {A : Type'} (GEN_PVAR_247 : A) (s : A -> Prop) (P : A -> Prop) (x : A) : (term66 A GEN_PVAR_247 s P x) = (term67 A GEN_PVAR_247 s P x).
Proof. exact (MK_COMB (@lem6160591 A GEN_PVAR_247 s P x) (@lem6160592 A x)). Qed.
Lemma lem6160594 {A : Type'} (GEN_PVAR_247 : A) (s : A -> Prop) (P : A -> Prop) : (term68 A GEN_PVAR_247 s P) = (term69 A GEN_PVAR_247 s P).
Proof. exact (fun_ext (fun x : A => @lem6160593 A GEN_PVAR_247 s P x)). Qed.
Lemma lem6160595 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6160596 {A : Type'} (GEN_PVAR_247 : A) (s : A -> Prop) (P : A -> Prop) : (term70 A GEN_PVAR_247 s P) = (term71 A GEN_PVAR_247 s P).
Proof. exact (MK_COMB (@lem6160595 A) (@lem6160594 A GEN_PVAR_247 s P)). Qed.
Lemma lem6160597 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term72 A s P) = (term73 A s P).
Proof. exact (fun_ext (fun GEN_PVAR_247 : A => @lem6160596 A GEN_PVAR_247 s P)). Qed.
Lemma lem6160598 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6160599 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term74 A s P) = (term30 A s P).
Proof. exact (MK_COMB (@lem6160598 A) (@lem6160597 A s P)). Qed.
Lemma lem6160600 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6160601 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term60 A x s P) = (term75 A x s P).
Proof. exact (MK_COMB (@lem6160600 A x) (@lem6160599 A s P)). Qed.
Lemma lem6160602 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6160603 {A : Type'} (x : A) (s : A -> Prop) (P : A -> Prop) : (term76 A x s P) = (term77 A x s P).
Proof. exact (MK_COMB (@lem6160602) (@lem6160601 A x s P)). Qed.
Lemma lem6160604 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term61 A s P x) = (term63 A s P x).
Proof. exact (eq_refl (term61 A s P x)). Qed.
Lemma lem6160605 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : ((term60 A x s P) = (term61 A s P x)) = ((term75 A x s P) = (term63 A s P x)).
Proof. exact (MK_COMB (@lem6160603 A x s P) (@lem6160604 A s P x)). Qed.
Lemma lem6160606 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term75 A x s P) = (term63 A s P x).
Proof. exact (EQ_MP (@lem6160605 A s P x) (@lem6160588 A s P x)). Qed.
Lemma lem6160609 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (q' : Prop) : term291 A B f g s P x q'.
Proof. exact (@lem6160584 A B s P f g x (term63 A s P x) q'). Qed.
Lemma lem6160610 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (q' : Prop) : term292 A B f g s P x q'.
Proof. exact (@lem6160609 A B f g s P x q' (@lem6160606 A s P x)). Qed.
Lemma lem6160611 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term63 A s P x) : term63 A s P x.
Proof. exact (h1). Qed.
Lemma lem6160612 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term63 A s P x) : term78 A P x.
Proof. exact (proj2 (@lem6160611 A s P x h1)). Qed.
Lemma lem6160613 {A : Type'} (P : A -> Prop) (x : A) : term293 A P x.
Proof. exact (@lem82 (P x)). Qed.
Lemma lem6160621 {A B : Type'} (f : A -> B) (y : A) : (term251 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6160622 {A B : Type'} (f : A -> B) (y : A) : (term251 A B f y) = (f y).
Proof. exact (@lem6160621 A B f y). Qed.
Lemma lem6160623 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term252 A B P f g x) = (term244 A B P f g x).
Proof. exact (@lem6160622 A B (term139 A B P f g) x). Qed.
Lemma lem6160624 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term244 A B P f g x) = (term253 A B P f g x).
Proof. exact (eq_refl (term244 A B P f g x)). Qed.
Lemma lem6160625 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) : (term254 A B P f g) = (term139 A B P f g).
Proof. exact (fun_ext (fun x : A => @lem6160624 A B P f g x)). Qed.
Lemma lem6160626 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6160627 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term252 A B P f g x) = (term244 A B P f g x).
Proof. exact (MK_COMB (@lem6160625 A B P f g) (@lem6160626 A x)). Qed.
Lemma lem6160628 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6160629 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term255 A B P f g x) = (term256 A B P f g x).
Proof. exact (MK_COMB (@lem6160628 B) (@lem6160627 A B P f g x)). Qed.
Lemma lem6160630 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term244 A B P f g x) = (term253 A B P f g x).
Proof. exact (eq_refl (term244 A B P f g x)). Qed.
Lemma lem6160631 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : ((term252 A B P f g x) = (term244 A B P f g x)) = ((term244 A B P f g x) = (term253 A B P f g x)).
Proof. exact (MK_COMB (@lem6160629 A B P f g x) (@lem6160630 A B P f g x)). Qed.
Lemma lem6160632 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term244 A B P f g x) = (term253 A B P f g x).
Proof. exact (EQ_MP (@lem6160631 A B P f g x) (@lem6160623 A B P f g x)). Qed.
Lemma lem6160634 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term257 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6160635 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term258 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6160634 _2963 g t e g' t' e'). Qed.
Lemma lem6160636 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term259 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6160635 _2963 g t e g' t'). Qed.
Lemma lem6160637 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term260 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6160636 _2963 g t e g'). Qed.
Lemma lem6160638 {B : Type'} (g : Prop) (t : B) (e : B) : term260 B g t e.
Proof. exact (@lem6160637 B g t e). Qed.
Lemma lem6160639 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term261 A B P f g x.
Proof. exact (@lem6160638 B (P x) (f x) (g x)). Qed.
Lemma lem6160640 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) : term262 A B P f g x g'.
Proof. exact (@lem6160639 A B P f g x g'). Qed.
Lemma lem6160641 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) : (term262 A B P f g x g') = (term263 A B P f g x g').
Proof. exact (eq_refl (term262 A B P f g x g')). Qed.
Lemma lem6160642 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) : term263 A B P f g x g'.
Proof. exact (EQ_MP (@lem6160641 A B P f g x g') (@lem6160640 A B P f g x g')). Qed.
Lemma lem6160643 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) (t' : B) : term264 A B P f g x g' t'.
Proof. exact (@lem6160642 A B P f g x g' t'). Qed.
Lemma lem6160644 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) (t' : B) : (term264 A B P f g x g' t') = (term265 A B P f g x g' t').
Proof. exact (eq_refl (term264 A B P f g x g' t')). Qed.
Lemma lem6160645 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) (t' : B) : term265 A B P f g x g' t'.
Proof. exact (EQ_MP (@lem6160644 A B P f g x g' t') (@lem6160643 A B P f g x g' t')). Qed.
Lemma lem6160646 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : term266 A B P f g x g' t' e'.
Proof. exact (@lem6160645 A B P f g x g' t' e'). Qed.
Lemma lem6160647 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : (term266 A B P f g x g' t' e') = (term267 A B P f g x g' t' e').
Proof. exact (eq_refl (term266 A B P f g x g' t' e')). Qed.
Lemma lem6160648 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : term267 A B P f g x g' t' e'.
Proof. exact (EQ_MP (@lem6160647 A B P f g x g' t' e') (@lem6160646 A B P f g x g' t' e')). Qed.
Lemma lem6160650 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term63 A s P x) : (P x) = False.
Proof. exact (@lem6160613 A P x (@lem6160612 A s P x h1)). Qed.
Lemma lem6160651 {A B : Type'} (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (t' : B) (e' : B) : term294 A B P f g x t' e'.
Proof. exact (@lem6160648 A B P f g x False t' e'). Qed.
Lemma lem6160652 {A B : Type'} (f : A -> B) (g : A -> B) (t' : B) (e' : B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term63 A s P x) : term295 A B P f g x t' e'.
Proof. exact (@lem6160651 A B P f g x t' e' (@lem6160650 A s P x h1)). Qed.
Lemma lem6160656 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem6160657 {A B : Type'} (f : A -> B) (x : A) : term296 A B f x.
Proof. exact (fun h0 : False => @lem6160656 A B f x). Qed.
Lemma lem6160658 {A B : Type'} (g : A -> B) (f : A -> B) (e' : B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term63 A s P x) : term297 A B P g f x e'.
Proof. exact (@lem6160652 A B f g (f x) e' s P x h1). Qed.
Lemma lem6160659 {A B : Type'} (g : A -> B) (f : A -> B) (e' : B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term63 A s P x) : term298 A B P g f x e'.
Proof. exact (@lem6160658 A B g f e' s P x h1 (@lem6160657 A B f x)). Qed.
Lemma lem6160665 {A B : Type'} (g : A -> B) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem6160666 {A B : Type'} (g : A -> B) (x : A) : term299 A B g x.
Proof. exact (fun h0 : ~ False => @lem6160665 A B g x). Qed.
Lemma lem6160667 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term63 A s P x) : term300 A B P f g x.
Proof. exact (@lem6160659 A B g f (g x) s P x h1). Qed.
Lemma lem6160668 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term63 A s P x) : (term253 A B P f g x) = (term301 A B f g x).
Proof. exact (@lem6160667 A B f g s P x h1 (@lem6160666 A B g x)). Qed.
Lemma lem6160670 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6160671 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem6160670 B t1 t2). Qed.
Lemma lem6160672 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term301 A B f g x) = (g x).
Proof. exact (@lem6160671 B (f x) (g x)). Qed.
Lemma lem6160673 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term63 A s P x) : (term253 A B P f g x) = (g x).
Proof. exact (TRANS (@lem6160668 A B f g s P x h1) (@lem6160672 A B f g x)). Qed.
Lemma lem6160674 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term63 A s P x) : (term244 A B P f g x) = (g x).
Proof. exact (TRANS (@lem6160632 A B P f g x) (@lem6160673 A B f g s P x h1)). Qed.
Lemma lem6160675 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6160676 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term63 A s P x) : (term256 A B P f g x) = (term276 A B g x).
Proof. exact (MK_COMB (@lem6160675 B) (@lem6160674 A B f g s P x h1)). Qed.
Lemma lem6160677 {A B : Type'} (g : A -> B) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem6160678 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term63 A s P x) : ((term244 A B P f g x) = (g x)) = ((g x) = (g x)).
Proof. exact (MK_COMB (@lem6160676 A B f g s P x h1) (@lem6160677 A B g x)). Qed.
Lemma lem6160680 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6160681 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem6160680 B x). Qed.
Lemma lem6160682 {A B : Type'} (g : A -> B) (x : A) : ((g x) = (g x)) = True.
Proof. exact (@lem6160681 B (g x)). Qed.
Lemma lem6160683 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term63 A s P x) : ((term244 A B P f g x) = (g x)) = True.
Proof. exact (TRANS (@lem6160678 A B f g s P x h1) (@lem6160682 A B g x)). Qed.
Lemma lem6160684 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term302 A B s P f g x.
Proof. exact (fun h0 : term63 A s P x => @lem6160683 A B f g s P x h0). Qed.
Lemma lem6160685 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) : term303 A B f g s P x.
Proof. exact (@lem6160610 A B f g s P x True). Qed.
Lemma lem6160686 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) (P : A -> Prop) (x : A) : (term304 A B s P f g x) = (term305 A s P x).
Proof. exact (@lem6160685 A B f g s P x (@lem6160684 A B s P f g x)). Qed.
Lemma lem6160688 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6160689 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term305 A s P x) = True.
Proof. exact (@lem6160688 (term63 A s P x)). Qed.
Lemma lem6160690 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term304 A B s P f g x) = True.
Proof. exact (TRANS (@lem6160686 A B f g s P x) (@lem6160689 A s P x)). Qed.
Lemma lem6160691 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) : (term306 A B s P f g) = (term282 A).
Proof. exact (fun_ext (fun x : A => @lem6160690 A B s P f g x)). Qed.
Lemma lem6160692 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6160693 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) : (term307 A B s P f g) = (term284 A).
Proof. exact (MK_COMB (@lem6160692 A) (@lem6160691 A B s P f g)). Qed.
Lemma lem6160695 {A : Type'} (t : Prop) : (term285 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6160696 {A : Type'} (t : Prop) : (term285 A t) = t.
Proof. exact (@lem6160695 A t). Qed.
Lemma lem6160697 {A : Type'} : (term284 A) = True.
Proof. exact (@lem6160696 A True). Qed.
Lemma lem6160698 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) : (term307 A B s P f g) = True.
Proof. exact (TRANS (@lem6160693 A B s P f g) (@lem6160697 A)). Qed.
Lemma lem6160699 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) : True = (term307 A B s P f g).
Proof. exact (SYM (@lem6160698 A B s P f g)). Qed.
Lemma lem6160700 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (g : A -> B) : term307 A B s P f g.
Proof. exact (EQ_MP (@lem6160699 A B s P f g) (@lem0)). Qed.
Lemma lem6160701 {A B : Type'} (f : A -> B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term308 A B op s P f g) = (term309 A B op s P g).
Proof. exact (@lem6160434 A B f s P g op h1 (@lem6160700 A B s P f g)). Qed.
Lemma lem6160702 {A B : Type'} (g : A -> B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term310 A B op s P f g) = (term311 A B op s P f).
Proof. exact (@lem6160380 A B g s P f op h1 (@lem6160567 A B s P g f)). Qed.
Lemma lem6160703 {A B : Type'} (g : A -> B) (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term312 A B op s P f g) = (term313 A B op s P f).
Proof. exact (MK_COMB (@lem6160326 B op) (@lem6160702 A B g s P f op h1)). Qed.
Lemma lem6160704 {A B : Type'} (f : A -> B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term161 A B op s P f g) = (term26 A B f op s P g).
Proof. exact (MK_COMB (@lem6160703 A B g s P f op h1) (@lem6160701 A B f s P g op h1)). Qed.
Lemma lem6160705 {A B : Type'} (f : A -> B) (P : A -> Prop) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) : term314 A B f op s P g.
Proof. exact (conj (@lem6160325 A B P f g s op h1 h2) (@lem6160704 A B f s P g op h2)). Qed.
Lemma lem6160706 {A B : Type'} (f : A -> B) (P : A -> Prop) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) : term315 A B f op s P g.
Proof. exact (ex_intro (term316 A B f op s P g) (term161 A B op s P f g) (@lem6160705 A B f P g s op h1 h2)). Qed.
Lemma lem6160707 {A B : Type'} (f : A -> B) (P : A -> Prop) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) : (term25 A B op s P f g) = (term26 A B f op s P g).
Proof. exact (@lem6158484 A B f op s P g (@lem6160706 A B f P g s op h1 h2)). Qed.
Lemma lem6160708 {A B : Type'} (f : A -> B) (P : A -> Prop) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) : (@FINITE A s) = ((term25 A B op s P f g) = (term26 A B f op s P g)).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem6160707 A B f P g s op h1 h2) (fun h3 : (term25 A B op s P f g) = (term26 A B f op s P g) => @lem6158480 A s h1)). Qed.
Lemma lem6160709 {A B : Type'} (f : A -> B) (P : A -> Prop) (g : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) : (term25 A B op s P f g) = (term26 A B f op s P g).
Proof. exact (EQ_MP (@lem6160708 A B f P g s op h1 h2) (@lem6158480 A s h1)). Qed.
Lemma lem6160710 {A B : Type'} (f : A -> B) (s : A -> Prop) (P : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term317 A B f op s P g.
Proof. exact (fun h0 : @FINITE A s => @lem6160709 A B f P g s op h0 h1). Qed.
Lemma lem6160715 {A B : Type'} (f : A -> B) (s : A -> Prop) (P : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term318 A B f op s P.
Proof. exact (fun g : A -> B => @lem6160710 A B f s P g op h1). Qed.
Lemma lem6160720 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term319 A B op s P.
Proof. exact (fun f : A -> B => @lem6160715 A B f s P op h1). Qed.
Lemma lem6160725 {A B : Type'} (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term320 A B op s.
Proof. exact (fun P : A -> Prop => @lem6160720 A B s P op h1). Qed.
Lemma lem6160730 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term321 A B op.
Proof. exact (fun s : A -> Prop => @lem6160725 A B s op h1). Qed.
Lemma lem6160731 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = (term321 A B op).
Proof. exact (prop_ext (fun h2 : @monoidal B op => @lem6160730 A B op h1) (fun h2 : term321 A B op => @lem6158479 B op h1)). Qed.
Lemma lem6160732 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term321 A B op.
Proof. exact (EQ_MP (@lem6160731 A B op h1) (@lem6158479 B op h1)). Qed.
Lemma lem6160733 {A B : Type'} (op : type1400 B) : term322 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem6160732 A B op h0). Qed.
Lemma lem6160738 {A B : Type'} : term323 A B.
Proof. exact (fun op : type1400 B => @lem6160733 A B op). Qed.
