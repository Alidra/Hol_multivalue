Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_NSUM_RESTRICT_term_abbrevs.
Require Import NSUM_RESTRICT_SET_spec.
Require Import NSUM_SWAP_spec.
Require Import thm0_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Lemma lem6990945 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem6990944 A P). Qed.
Lemma lem6990946 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem6990947 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem6990946 A P) (@lem6990945 A P)). Qed.
Lemma lem6990948 {A : Type'} (P : A -> Prop) (s : A -> Prop) : term2 A P s.
Proof. exact (@lem6990947 A P s). Qed.
Lemma lem6990949 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term2 A P s) = (term3 A s P).
Proof. exact (eq_refl (term2 A P s)). Qed.
Lemma lem6990950 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term3 A s P.
Proof. exact (EQ_MP (@lem6990949 A s P) (@lem6990948 A P s)). Qed.
Lemma lem6990951 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> nat) : term4 A s P f.
Proof. exact (@lem6990950 A s P f). Qed.
Lemma lem6990952 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> nat) : (term4 A s P f) = ((term5 A s P f) = (term6 A s P f)).
Proof. exact (eq_refl (term4 A s P f)). Qed.
Lemma lem6990957 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term7 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6990958 (p : Prop) (q : Prop) (p' : Prop) : term8 p q p'.
Proof. exact (fun q' : Prop => @lem6990957 p q p' q'). Qed.
Lemma lem6990959 (p : Prop) (q : Prop) : term9 p q.
Proof. exact (fun p' : Prop => @lem6990958 p q p'). Qed.
Lemma lem6990960 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : term10 _128402 _128403 t s R f.
Proof. exact (@lem6990959 (term11 _128402 _128403 s t) ((term12 _128402 _128403 s t R f) = (term13 _128402 _128403 t s R f))). Qed.
Lemma lem6990961 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (p' : Prop) : term14 _128402 _128403 t s R f p'.
Proof. exact (@lem6990960 _128402 _128403 t s R f p'). Qed.
Lemma lem6990962 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (p' : Prop) : (term14 _128402 _128403 t s R f p') = (term15 _128402 _128403 t s R f p').
Proof. exact (eq_refl (term14 _128402 _128403 t s R f p')). Qed.
Lemma lem6990963 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (p' : Prop) : term15 _128402 _128403 t s R f p'.
Proof. exact (EQ_MP (@lem6990962 _128402 _128403 t s R f p') (@lem6990961 _128402 _128403 t s R f p')). Qed.
Lemma lem6990964 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (p' : Prop) (q' : Prop) : term16 _128402 _128403 t s R f p' q'.
Proof. exact (@lem6990963 _128402 _128403 t s R f p' q'). Qed.
Lemma lem6990965 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (p' : Prop) (q' : Prop) : (term16 _128402 _128403 t s R f p' q') = (term17 _128402 _128403 t s R f p' q').
Proof. exact (eq_refl (term16 _128402 _128403 t s R f p' q')). Qed.
Lemma lem6990966 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (p' : Prop) (q' : Prop) : term17 _128402 _128403 t s R f p' q'.
Proof. exact (EQ_MP (@lem6990965 _128402 _128403 t s R f p' q') (@lem6990964 _128402 _128403 t s R f p' q')). Qed.
Lemma lem6990969 {_128402 _128403 : Type'} (s : _128403 -> Prop) (t : _128402 -> Prop) : (term11 _128402 _128403 s t) = (term11 _128402 _128403 s t).
Proof. exact (eq_refl (term11 _128402 _128403 s t)). Qed.
Lemma lem6990970 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (q' : Prop) : term18 _128402 _128403 R f s t q'.
Proof. exact (@lem6990966 _128402 _128403 t s R f (term11 _128402 _128403 s t) q'). Qed.
Lemma lem6990971 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (q' : Prop) : term19 _128402 _128403 R f s t q'.
Proof. exact (@lem6990970 _128402 _128403 R f s t q' (@lem6990969 _128402 _128403 s t)). Qed.
Lemma lem6990982 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> nat) : (term5 A s P f) = (term6 A s P f).
Proof. exact (EQ_MP (@lem6990952 A s P f) (@lem6990951 A s P f)). Qed.
Lemma lem6990983 {_128402 : Type'} (s : _128402 -> Prop) (P : _128402 -> Prop) (f : _128402 -> nat) : (term5 _128402 s P f) = (term6 _128402 s P f).
Proof. exact (@lem6990982 _128402 s P f). Qed.
Lemma lem6990984 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) : (term20 _128402 _128403 t R f x) = (term21 _128402 _128403 t R f x).
Proof. exact (@lem6990983 _128402 t (term22 _128402 _128403 R x) (term23 _128402 _128403 f x)). Qed.
Lemma lem6990985 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : (term24 _128402 _128403 R x y) = (R x y).
Proof. exact (eq_refl (term24 _128402 _128403 R x y)). Qed.
Lemma lem6990986 {_128402 : Type'} (y : _128402) (t : _128402 -> Prop) : (term25 _128402 y t) = (term25 _128402 y t).
Proof. exact (eq_refl (term25 _128402 y t)). Qed.
Lemma lem6990987 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : (term26 _128402 _128403 t R x y) = (term27 _128402 _128403 t R x y).
Proof. exact (MK_COMB (@lem6990986 _128402 y t) (@lem6990985 _128402 _128403 R x y)). Qed.
Lemma lem6990988 {_128402 : Type'} (GEN_PVAR_288 : _128402) : (@SETSPEC _128402 GEN_PVAR_288) = (@SETSPEC _128402 GEN_PVAR_288).
Proof. exact (eq_refl (@SETSPEC _128402 GEN_PVAR_288)). Qed.
Lemma lem6990989 {_128402 _128403 : Type'} (GEN_PVAR_288 : _128402) (t : _128402 -> Prop) (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : (term28 _128402 _128403 GEN_PVAR_288 t R x y) = (term29 _128402 _128403 GEN_PVAR_288 t R x y).
Proof. exact (MK_COMB (@lem6990988 _128402 GEN_PVAR_288) (@lem6990987 _128402 _128403 t R x y)). Qed.
Lemma lem6990990 {_128402 : Type'} (y : _128402) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6990991 {_128402 _128403 : Type'} (GEN_PVAR_288 : _128402) (t : _128402 -> Prop) (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : (term30 _128402 _128403 GEN_PVAR_288 t R x y) = (term31 _128402 _128403 GEN_PVAR_288 t R x y).
Proof. exact (MK_COMB (@lem6990989 _128402 _128403 GEN_PVAR_288 t R x y) (@lem6990990 _128402 y)). Qed.
Lemma lem6990992 {_128402 _128403 : Type'} (GEN_PVAR_288 : _128402) (t : _128402 -> Prop) (R : type1470 _128402 _128403) (x : _128403) : (term32 _128402 _128403 GEN_PVAR_288 t R x) = (term33 _128402 _128403 GEN_PVAR_288 t R x).
Proof. exact (fun_ext (fun y : _128402 => @lem6990991 _128402 _128403 GEN_PVAR_288 t R x y)). Qed.
Lemma lem6990993 {_128402 : Type'} : (@ex _128402) = (@ex _128402).
Proof. exact (eq_refl (@ex _128402)). Qed.
Lemma lem6990994 {_128402 _128403 : Type'} (GEN_PVAR_288 : _128402) (t : _128402 -> Prop) (R : type1470 _128402 _128403) (x : _128403) : (term34 _128402 _128403 GEN_PVAR_288 t R x) = (term35 _128402 _128403 GEN_PVAR_288 t R x).
Proof. exact (MK_COMB (@lem6990993 _128402) (@lem6990992 _128402 _128403 GEN_PVAR_288 t R x)). Qed.
Lemma lem6990995 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (x : _128403) : (term36 _128402 _128403 t R x) = (term37 _128402 _128403 t R x).
Proof. exact (fun_ext (fun GEN_PVAR_288 : _128402 => @lem6990994 _128402 _128403 GEN_PVAR_288 t R x)). Qed.
Lemma lem6990996 {_128402 : Type'} : (@GSPEC _128402) = (@GSPEC _128402).
Proof. exact (eq_refl (@GSPEC _128402)). Qed.
Lemma lem6990997 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (x : _128403) : (term38 _128402 _128403 t R x) = (term39 _128402 _128403 t R x).
Proof. exact (MK_COMB (@lem6990996 _128402) (@lem6990995 _128402 _128403 t R x)). Qed.
Lemma lem6990998 {_128402 : Type'} : (@nsum _128402) = (@nsum _128402).
Proof. exact (eq_refl (@nsum _128402)). Qed.
Lemma lem6990999 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (x : _128403) : (term40 _128402 _128403 t R x) = (term41 _128402 _128403 t R x).
Proof. exact (MK_COMB (@lem6990998 _128402) (@lem6990997 _128402 _128403 t R x)). Qed.
Lemma lem6991000 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (x : _128403) : (term23 _128402 _128403 f x) = (term23 _128402 _128403 f x).
Proof. exact (eq_refl (term23 _128402 _128403 f x)). Qed.
Lemma lem6991001 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) : (term20 _128402 _128403 t R f x) = (term42 _128402 _128403 t R f x).
Proof. exact (MK_COMB (@lem6990999 _128402 _128403 t R x) (@lem6991000 _128402 _128403 f x)). Qed.
Lemma lem6991002 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6991003 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) : (term43 _128402 _128403 t R f x) = (term44 _128402 _128403 t R f x).
Proof. exact (MK_COMB (@lem6991002) (@lem6991001 _128402 _128403 t R f x)). Qed.
Lemma lem6991004 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : (term24 _128402 _128403 R x y) = (R x y).
Proof. exact (eq_refl (term24 _128402 _128403 R x y)). Qed.
Lemma lem6991005 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem6991006 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : (term45 _128402 _128403 R x y) = (term46 _128402 _128403 R x y).
Proof. exact (MK_COMB (@lem6991005) (@lem6991004 _128402 _128403 R x y)). Qed.
Lemma lem6991007 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term47 _128402 _128403 f x y) = (term47 _128402 _128403 f x y).
Proof. exact (eq_refl (term47 _128402 _128403 f x y)). Qed.
Lemma lem6991008 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term48 _128402 _128403 R f x y) = (term49 _128402 _128403 R f x y).
Proof. exact (MK_COMB (@lem6991006 _128402 _128403 R x y) (@lem6991007 _128402 _128403 f x y)). Qed.
Lemma lem6991009 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem6991010 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term50 _128402 _128403 R f x y) = (term51 _128402 _128403 R f x y).
Proof. exact (MK_COMB (@lem6991008 _128402 _128403 R f x y) (@lem6991009)). Qed.
Lemma lem6991011 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) : (term52 _128402 _128403 R f x) = (term53 _128402 _128403 R f x).
Proof. exact (fun_ext (fun y : _128402 => @lem6991010 _128402 _128403 R f x y)). Qed.
Lemma lem6991012 {_128402 : Type'} (t : _128402 -> Prop) : (@nsum _128402 t) = (@nsum _128402 t).
Proof. exact (eq_refl (@nsum _128402 t)). Qed.
Lemma lem6991013 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) : (term21 _128402 _128403 t R f x) = (term54 _128402 _128403 t R f x).
Proof. exact (MK_COMB (@lem6991012 _128402 t) (@lem6991011 _128402 _128403 R f x)). Qed.
Lemma lem6991014 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) : ((term20 _128402 _128403 t R f x) = (term21 _128402 _128403 t R f x)) = ((term42 _128402 _128403 t R f x) = (term54 _128402 _128403 t R f x)).
Proof. exact (MK_COMB (@lem6991003 _128402 _128403 t R f x) (@lem6991013 _128402 _128403 t R f x)). Qed.
Lemma lem6991015 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) : (term42 _128402 _128403 t R f x) = (term54 _128402 _128403 t R f x).
Proof. exact (EQ_MP (@lem6991014 _128402 _128403 t R f x) (@lem6990984 _128402 _128403 t R f x)). Qed.
Lemma lem6991017 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term55 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6991018 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term56 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6991017 _2963 g t e g' t' e'). Qed.
Lemma lem6991019 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term57 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6991018 _2963 g t e g' t'). Qed.
Lemma lem6991020 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term58 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6991019 _2963 g t e g'). Qed.
Lemma lem6991021 (g : Prop) (t : nat) (e : nat) : term59 g t e.
Proof. exact (@lem6991020 nat g t e). Qed.
Lemma lem6991022 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : term60 _128402 _128403 R f x y.
Proof. exact (@lem6991021 (R x y) (term47 _128402 _128403 f x y) (NUMERAL 0)). Qed.
Lemma lem6991023 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) (g' : Prop) : term61 _128402 _128403 R f x y g'.
Proof. exact (@lem6991022 _128402 _128403 R f x y g'). Qed.
Lemma lem6991024 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) (g' : Prop) : (term61 _128402 _128403 R f x y g') = (term62 _128402 _128403 R f x y g').
Proof. exact (eq_refl (term61 _128402 _128403 R f x y g')). Qed.
Lemma lem6991025 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) (g' : Prop) : term62 _128402 _128403 R f x y g'.
Proof. exact (EQ_MP (@lem6991024 _128402 _128403 R f x y g') (@lem6991023 _128402 _128403 R f x y g')). Qed.
Lemma lem6991026 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) (g' : Prop) (t' : nat) : term63 _128402 _128403 R f x y g' t'.
Proof. exact (@lem6991025 _128402 _128403 R f x y g' t'). Qed.
Lemma lem6991027 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) (g' : Prop) (t' : nat) : (term63 _128402 _128403 R f x y g' t') = (term64 _128402 _128403 R f x y g' t').
Proof. exact (eq_refl (term63 _128402 _128403 R f x y g' t')). Qed.
Lemma lem6991028 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) (g' : Prop) (t' : nat) : term64 _128402 _128403 R f x y g' t'.
Proof. exact (EQ_MP (@lem6991027 _128402 _128403 R f x y g' t') (@lem6991026 _128402 _128403 R f x y g' t')). Qed.
Lemma lem6991029 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) (g' : Prop) (t' : nat) (e' : nat) : term65 _128402 _128403 R f x y g' t' e'.
Proof. exact (@lem6991028 _128402 _128403 R f x y g' t' e'). Qed.
Lemma lem6991030 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) (g' : Prop) (t' : nat) (e' : nat) : (term65 _128402 _128403 R f x y g' t' e') = (term66 _128402 _128403 R f x y g' t' e').
Proof. exact (eq_refl (term65 _128402 _128403 R f x y g' t' e')). Qed.
Lemma lem6991031 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) (g' : Prop) (t' : nat) (e' : nat) : term66 _128402 _128403 R f x y g' t' e'.
Proof. exact (EQ_MP (@lem6991030 _128402 _128403 R f x y g' t' e') (@lem6991029 _128402 _128403 R f x y g' t' e')). Qed.
Lemma lem6991032 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem6991033 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (R : type1470 _128402 _128403) (x : _128403) (y : _128402) (t' : nat) (e' : nat) : term67 _128402 _128403 f R x y t' e'.
Proof. exact (@lem6991031 _128402 _128403 R f x y (R x y) t' e'). Qed.
Lemma lem6991034 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (R : type1470 _128402 _128403) (x : _128403) (y : _128402) (t' : nat) (e' : nat) : term68 _128402 _128403 f R x y t' e'.
Proof. exact (@lem6991033 _128402 _128403 f R x y t' e' (@lem6991032 _128402 _128403 R x y)). Qed.
Lemma lem6991039 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6991040 {_128402 : Type'} (f : _128402 -> nat) (y : _128402) : (term70 _128402 f y) = (f y).
Proof. exact (@lem6991039 _128402 nat f y). Qed.
Lemma lem6991041 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term71 _128402 _128403 f x y) = (term47 _128402 _128403 f x y).
Proof. exact (@lem6991040 _128402 (term23 _128402 _128403 f x) y). Qed.
Lemma lem6991042 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term47 _128402 _128403 f x y) = (f x y).
Proof. exact (eq_refl (term47 _128402 _128403 f x y)). Qed.
Lemma lem6991043 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (x : _128403) : (term72 _128402 _128403 f x) = (term23 _128402 _128403 f x).
Proof. exact (fun_ext (fun y : _128402 => @lem6991042 _128402 _128403 f x y)). Qed.
Lemma lem6991044 {_128402 : Type'} (y : _128402) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6991045 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term71 _128402 _128403 f x y) = (term47 _128402 _128403 f x y).
Proof. exact (MK_COMB (@lem6991043 _128402 _128403 f x) (@lem6991044 _128402 y)). Qed.
Lemma lem6991046 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6991047 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term73 _128402 _128403 f x y) = (term74 _128402 _128403 f x y).
Proof. exact (MK_COMB (@lem6991046) (@lem6991045 _128402 _128403 f x y)). Qed.
Lemma lem6991048 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term47 _128402 _128403 f x y) = (f x y).
Proof. exact (eq_refl (term47 _128402 _128403 f x y)). Qed.
Lemma lem6991049 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : ((term71 _128402 _128403 f x y) = (term47 _128402 _128403 f x y)) = ((term47 _128402 _128403 f x y) = (f x y)).
Proof. exact (MK_COMB (@lem6991047 _128402 _128403 f x y) (@lem6991048 _128402 _128403 f x y)). Qed.
Lemma lem6991050 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term47 _128402 _128403 f x y) = (f x y).
Proof. exact (EQ_MP (@lem6991049 _128402 _128403 f x y) (@lem6991041 _128402 _128403 f x y)). Qed.
Lemma lem6991051 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : term75 _128402 _128403 R f x y.
Proof. exact (fun h0 : R x y => @lem6991050 _128402 _128403 f x y). Qed.
Lemma lem6991052 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) (e' : nat) : term76 _128402 _128403 R f x y e'.
Proof. exact (@lem6991034 _128402 _128403 f R x y (f x y) e'). Qed.
Lemma lem6991053 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) (e' : nat) : term77 _128402 _128403 R f x y e'.
Proof. exact (@lem6991052 _128402 _128403 R f x y e' (@lem6991051 _128402 _128403 R f x y)). Qed.
Lemma lem6991057 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem6991058 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : term78 _128402 _128403 R x y.
Proof. exact (fun h0 : term79 _128402 _128403 R x y => @lem6991057). Qed.
Lemma lem6991059 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : term80 _128402 _128403 R f x y.
Proof. exact (@lem6991053 _128402 _128403 R f x y (NUMERAL 0)). Qed.
Lemma lem6991060 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term51 _128402 _128403 R f x y) = (term81 _128402 _128403 R f x y).
Proof. exact (@lem6991059 _128402 _128403 R f x y (@lem6991058 _128402 _128403 R x y)). Qed.
Lemma lem6991094 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) : (term53 _128402 _128403 R f x) = (term82 _128402 _128403 R f x).
Proof. exact (fun_ext (fun y : _128402 => @lem6991060 _128402 _128403 R f x y)). Qed.
Lemma lem6991128 {_128402 : Type'} (t : _128402 -> Prop) : (@nsum _128402 t) = (@nsum _128402 t).
Proof. exact (eq_refl (@nsum _128402 t)). Qed.
Lemma lem6991129 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) : (term54 _128402 _128403 t R f x) = (term83 _128402 _128403 t R f x).
Proof. exact (MK_COMB (@lem6991128 _128402 t) (@lem6991094 _128402 _128403 R f x)). Qed.
Lemma lem6991163 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) : (term42 _128402 _128403 t R f x) = (term83 _128402 _128403 t R f x).
Proof. exact (TRANS (@lem6991015 _128402 _128403 t R f x) (@lem6991129 _128402 _128403 t R f x)). Qed.
Lemma lem6991164 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term84 _128402 _128403 t R f) = (term85 _128402 _128403 t R f).
Proof. exact (fun_ext (fun x : _128403 => @lem6991163 _128402 _128403 t R f x)). Qed.
Lemma lem6991198 {_128403 : Type'} (s : _128403 -> Prop) : (@nsum _128403 s) = (@nsum _128403 s).
Proof. exact (eq_refl (@nsum _128403 s)). Qed.
Lemma lem6991199 {_128402 _128403 : Type'} (s : _128403 -> Prop) (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term12 _128402 _128403 s t R f) = (term86 _128402 _128403 s t R f).
Proof. exact (MK_COMB (@lem6991198 _128403 s) (@lem6991164 _128402 _128403 t R f)). Qed.
Lemma lem6991233 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6991234 {_128402 _128403 : Type'} (s : _128403 -> Prop) (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term87 _128402 _128403 s t R f) = (term88 _128402 _128403 s t R f).
Proof. exact (MK_COMB (@lem6991233) (@lem6991199 _128402 _128403 s t R f)). Qed.
Lemma lem6991269 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> nat) : (term5 A s P f) = (term6 A s P f).
Proof. exact (EQ_MP (@lem6990952 A s P f) (@lem6990951 A s P f)). Qed.
Lemma lem6991270 {_128403 : Type'} (s : _128403 -> Prop) (P : _128403 -> Prop) (f : _128403 -> nat) : (term5 _128403 s P f) = (term6 _128403 s P f).
Proof. exact (@lem6991269 _128403 s P f). Qed.
Lemma lem6991271 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) : (term89 _128402 _128403 s R f y) = (term90 _128402 _128403 s R f y).
Proof. exact (@lem6991270 _128403 s (term91 _128402 _128403 R y) (term92 _128402 _128403 f y)). Qed.
Lemma lem6991272 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : (term93 _128402 _128403 R y x) = (R x y).
Proof. exact (eq_refl (term93 _128402 _128403 R y x)). Qed.
Lemma lem6991273 {_128403 : Type'} (x : _128403) (s : _128403 -> Prop) : (term25 _128403 x s) = (term25 _128403 x s).
Proof. exact (eq_refl (term25 _128403 x s)). Qed.
Lemma lem6991274 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : (term94 _128402 _128403 s R y x) = (term95 _128402 _128403 s R x y).
Proof. exact (MK_COMB (@lem6991273 _128403 x s) (@lem6991272 _128402 _128403 R x y)). Qed.
Lemma lem6991275 {_128403 : Type'} (GEN_PVAR_289 : _128403) : (@SETSPEC _128403 GEN_PVAR_289) = (@SETSPEC _128403 GEN_PVAR_289).
Proof. exact (eq_refl (@SETSPEC _128403 GEN_PVAR_289)). Qed.
Lemma lem6991276 {_128402 _128403 : Type'} (GEN_PVAR_289 : _128403) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : (term96 _128402 _128403 GEN_PVAR_289 s R y x) = (term97 _128402 _128403 GEN_PVAR_289 s R x y).
Proof. exact (MK_COMB (@lem6991275 _128403 GEN_PVAR_289) (@lem6991274 _128402 _128403 s R x y)). Qed.
Lemma lem6991277 {_128403 : Type'} (x : _128403) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6991278 {_128402 _128403 : Type'} (GEN_PVAR_289 : _128403) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (y : _128402) (x : _128403) : (term98 _128402 _128403 GEN_PVAR_289 s R y x) = (term99 _128402 _128403 GEN_PVAR_289 s R y x).
Proof. exact (MK_COMB (@lem6991276 _128402 _128403 GEN_PVAR_289 s R x y) (@lem6991277 _128403 x)). Qed.
Lemma lem6991279 {_128402 _128403 : Type'} (GEN_PVAR_289 : _128403) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (y : _128402) : (term100 _128402 _128403 GEN_PVAR_289 s R y) = (term101 _128402 _128403 GEN_PVAR_289 s R y).
Proof. exact (fun_ext (fun x : _128403 => @lem6991278 _128402 _128403 GEN_PVAR_289 s R y x)). Qed.
Lemma lem6991280 {_128403 : Type'} : (@ex _128403) = (@ex _128403).
Proof. exact (eq_refl (@ex _128403)). Qed.
Lemma lem6991281 {_128402 _128403 : Type'} (GEN_PVAR_289 : _128403) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (y : _128402) : (term102 _128402 _128403 GEN_PVAR_289 s R y) = (term103 _128402 _128403 GEN_PVAR_289 s R y).
Proof. exact (MK_COMB (@lem6991280 _128403) (@lem6991279 _128402 _128403 GEN_PVAR_289 s R y)). Qed.
Lemma lem6991282 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (y : _128402) : (term104 _128402 _128403 s R y) = (term105 _128402 _128403 s R y).
Proof. exact (fun_ext (fun GEN_PVAR_289 : _128403 => @lem6991281 _128402 _128403 GEN_PVAR_289 s R y)). Qed.
Lemma lem6991283 {_128403 : Type'} : (@GSPEC _128403) = (@GSPEC _128403).
Proof. exact (eq_refl (@GSPEC _128403)). Qed.
Lemma lem6991284 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (y : _128402) : (term106 _128402 _128403 s R y) = (term107 _128402 _128403 s R y).
Proof. exact (MK_COMB (@lem6991283 _128403) (@lem6991282 _128402 _128403 s R y)). Qed.
Lemma lem6991285 {_128403 : Type'} : (@nsum _128403) = (@nsum _128403).
Proof. exact (eq_refl (@nsum _128403)). Qed.
Lemma lem6991286 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (y : _128402) : (term108 _128402 _128403 s R y) = (term109 _128402 _128403 s R y).
Proof. exact (MK_COMB (@lem6991285 _128403) (@lem6991284 _128402 _128403 s R y)). Qed.
Lemma lem6991287 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (y : _128402) : (term92 _128402 _128403 f y) = (term92 _128402 _128403 f y).
Proof. exact (eq_refl (term92 _128402 _128403 f y)). Qed.
Lemma lem6991288 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) : (term89 _128402 _128403 s R f y) = (term110 _128402 _128403 s R f y).
Proof. exact (MK_COMB (@lem6991286 _128402 _128403 s R y) (@lem6991287 _128402 _128403 f y)). Qed.
Lemma lem6991289 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6991290 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) : (term111 _128402 _128403 s R f y) = (term112 _128402 _128403 s R f y).
Proof. exact (MK_COMB (@lem6991289) (@lem6991288 _128402 _128403 s R f y)). Qed.
Lemma lem6991291 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : (term93 _128402 _128403 R y x) = (R x y).
Proof. exact (eq_refl (term93 _128402 _128403 R y x)). Qed.
Lemma lem6991292 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem6991293 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : (term113 _128402 _128403 R y x) = (term46 _128402 _128403 R x y).
Proof. exact (MK_COMB (@lem6991292) (@lem6991291 _128402 _128403 R x y)). Qed.
Lemma lem6991294 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (y : _128402) (x : _128403) : (term114 _128402 _128403 f y x) = (term114 _128402 _128403 f y x).
Proof. exact (eq_refl (term114 _128402 _128403 f y x)). Qed.
Lemma lem6991295 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) (x : _128403) : (term115 _128402 _128403 R f y x) = (term116 _128402 _128403 R f y x).
Proof. exact (MK_COMB (@lem6991293 _128402 _128403 R x y) (@lem6991294 _128402 _128403 f y x)). Qed.
Lemma lem6991296 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem6991297 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) (x : _128403) : (term117 _128402 _128403 R f y x) = (term118 _128402 _128403 R f y x).
Proof. exact (MK_COMB (@lem6991295 _128402 _128403 R f y x) (@lem6991296)). Qed.
Lemma lem6991298 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) : (term119 _128402 _128403 R f y) = (term120 _128402 _128403 R f y).
Proof. exact (fun_ext (fun x : _128403 => @lem6991297 _128402 _128403 R f y x)). Qed.
Lemma lem6991299 {_128403 : Type'} (s : _128403 -> Prop) : (@nsum _128403 s) = (@nsum _128403 s).
Proof. exact (eq_refl (@nsum _128403 s)). Qed.
Lemma lem6991300 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) : (term90 _128402 _128403 s R f y) = (term121 _128402 _128403 s R f y).
Proof. exact (MK_COMB (@lem6991299 _128403 s) (@lem6991298 _128402 _128403 R f y)). Qed.
Lemma lem6991301 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) : ((term89 _128402 _128403 s R f y) = (term90 _128402 _128403 s R f y)) = ((term110 _128402 _128403 s R f y) = (term121 _128402 _128403 s R f y)).
Proof. exact (MK_COMB (@lem6991290 _128402 _128403 s R f y) (@lem6991300 _128402 _128403 s R f y)). Qed.
Lemma lem6991302 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) : (term110 _128402 _128403 s R f y) = (term121 _128402 _128403 s R f y).
Proof. exact (EQ_MP (@lem6991301 _128402 _128403 s R f y) (@lem6991271 _128402 _128403 s R f y)). Qed.
Lemma lem6991304 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term55 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6991305 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term56 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6991304 _2963 g t e g' t' e'). Qed.
Lemma lem6991306 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term57 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6991305 _2963 g t e g' t'). Qed.
Lemma lem6991307 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term58 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6991306 _2963 g t e g'). Qed.
Lemma lem6991308 (g : Prop) (t : nat) (e : nat) : term59 g t e.
Proof. exact (@lem6991307 nat g t e). Qed.
Lemma lem6991309 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) (x : _128403) : term122 _128402 _128403 R f y x.
Proof. exact (@lem6991308 (R x y) (term114 _128402 _128403 f y x) (NUMERAL 0)). Qed.
Lemma lem6991310 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) (x : _128403) (g' : Prop) : term123 _128402 _128403 R f y x g'.
Proof. exact (@lem6991309 _128402 _128403 R f y x g'). Qed.
Lemma lem6991311 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) (x : _128403) (g' : Prop) : (term123 _128402 _128403 R f y x g') = (term124 _128402 _128403 R f y x g').
Proof. exact (eq_refl (term123 _128402 _128403 R f y x g')). Qed.
Lemma lem6991312 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) (x : _128403) (g' : Prop) : term124 _128402 _128403 R f y x g'.
Proof. exact (EQ_MP (@lem6991311 _128402 _128403 R f y x g') (@lem6991310 _128402 _128403 R f y x g')). Qed.
Lemma lem6991313 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) (x : _128403) (g' : Prop) (t' : nat) : term125 _128402 _128403 R f y x g' t'.
Proof. exact (@lem6991312 _128402 _128403 R f y x g' t'). Qed.
Lemma lem6991314 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) (x : _128403) (g' : Prop) (t' : nat) : (term125 _128402 _128403 R f y x g' t') = (term126 _128402 _128403 R f y x g' t').
Proof. exact (eq_refl (term125 _128402 _128403 R f y x g' t')). Qed.
Lemma lem6991315 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) (x : _128403) (g' : Prop) (t' : nat) : term126 _128402 _128403 R f y x g' t'.
Proof. exact (EQ_MP (@lem6991314 _128402 _128403 R f y x g' t') (@lem6991313 _128402 _128403 R f y x g' t')). Qed.
Lemma lem6991316 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) (x : _128403) (g' : Prop) (t' : nat) (e' : nat) : term127 _128402 _128403 R f y x g' t' e'.
Proof. exact (@lem6991315 _128402 _128403 R f y x g' t' e'). Qed.
Lemma lem6991317 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) (x : _128403) (g' : Prop) (t' : nat) (e' : nat) : (term127 _128402 _128403 R f y x g' t' e') = (term128 _128402 _128403 R f y x g' t' e').
Proof. exact (eq_refl (term127 _128402 _128403 R f y x g' t' e')). Qed.
Lemma lem6991318 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) (x : _128403) (g' : Prop) (t' : nat) (e' : nat) : term128 _128402 _128403 R f y x g' t' e'.
Proof. exact (EQ_MP (@lem6991317 _128402 _128403 R f y x g' t' e') (@lem6991316 _128402 _128403 R f y x g' t' e')). Qed.
Lemma lem6991319 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem6991320 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (R : type1470 _128402 _128403) (x : _128403) (y : _128402) (t' : nat) (e' : nat) : term129 _128402 _128403 f R x y t' e'.
Proof. exact (@lem6991318 _128402 _128403 R f y x (R x y) t' e'). Qed.
Lemma lem6991321 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (R : type1470 _128402 _128403) (x : _128403) (y : _128402) (t' : nat) (e' : nat) : term130 _128402 _128403 f R x y t' e'.
Proof. exact (@lem6991320 _128402 _128403 f R x y t' e' (@lem6991319 _128402 _128403 R x y)). Qed.
Lemma lem6991326 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6991327 {_128403 : Type'} (f : _128403 -> nat) (y : _128403) : (term70 _128403 f y) = (f y).
Proof. exact (@lem6991326 _128403 nat f y). Qed.
Lemma lem6991328 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (y : _128402) (x : _128403) : (term131 _128402 _128403 f y x) = (term114 _128402 _128403 f y x).
Proof. exact (@lem6991327 _128403 (term92 _128402 _128403 f y) x). Qed.
Lemma lem6991329 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term114 _128402 _128403 f y x) = (f x y).
Proof. exact (eq_refl (term114 _128402 _128403 f y x)). Qed.
Lemma lem6991330 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (y : _128402) : (term132 _128402 _128403 f y) = (term92 _128402 _128403 f y).
Proof. exact (fun_ext (fun x : _128403 => @lem6991329 _128402 _128403 f x y)). Qed.
Lemma lem6991331 {_128403 : Type'} (x : _128403) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6991332 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (y : _128402) (x : _128403) : (term131 _128402 _128403 f y x) = (term114 _128402 _128403 f y x).
Proof. exact (MK_COMB (@lem6991330 _128402 _128403 f y) (@lem6991331 _128403 x)). Qed.
Lemma lem6991333 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6991334 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (y : _128402) (x : _128403) : (term133 _128402 _128403 f y x) = (term134 _128402 _128403 f y x).
Proof. exact (MK_COMB (@lem6991333) (@lem6991332 _128402 _128403 f y x)). Qed.
Lemma lem6991335 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term114 _128402 _128403 f y x) = (f x y).
Proof. exact (eq_refl (term114 _128402 _128403 f y x)). Qed.
Lemma lem6991336 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : ((term131 _128402 _128403 f y x) = (term114 _128402 _128403 f y x)) = ((term114 _128402 _128403 f y x) = (f x y)).
Proof. exact (MK_COMB (@lem6991334 _128402 _128403 f y x) (@lem6991335 _128402 _128403 f x y)). Qed.
Lemma lem6991337 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term114 _128402 _128403 f y x) = (f x y).
Proof. exact (EQ_MP (@lem6991336 _128402 _128403 f x y) (@lem6991328 _128402 _128403 f y x)). Qed.
Lemma lem6991338 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : term135 _128402 _128403 R f x y.
Proof. exact (fun h0 : R x y => @lem6991337 _128402 _128403 f x y). Qed.
Lemma lem6991339 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) (e' : nat) : term136 _128402 _128403 R f x y e'.
Proof. exact (@lem6991321 _128402 _128403 f R x y (f x y) e'). Qed.
Lemma lem6991340 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) (e' : nat) : term137 _128402 _128403 R f x y e'.
Proof. exact (@lem6991339 _128402 _128403 R f x y e' (@lem6991338 _128402 _128403 R f x y)). Qed.
Lemma lem6991344 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem6991345 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (x : _128403) (y : _128402) : term78 _128402 _128403 R x y.
Proof. exact (fun h0 : term79 _128402 _128403 R x y => @lem6991344). Qed.
Lemma lem6991346 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : term138 _128402 _128403 R f x y.
Proof. exact (@lem6991340 _128402 _128403 R f x y (NUMERAL 0)). Qed.
Lemma lem6991347 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term118 _128402 _128403 R f y x) = (term81 _128402 _128403 R f x y).
Proof. exact (@lem6991346 _128402 _128403 R f x y (@lem6991345 _128402 _128403 R x y)). Qed.
Lemma lem6991381 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) : (term120 _128402 _128403 R f y) = (term139 _128402 _128403 R f y).
Proof. exact (fun_ext (fun x : _128403 => @lem6991347 _128402 _128403 R f x y)). Qed.
Lemma lem6991415 {_128403 : Type'} (s : _128403 -> Prop) : (@nsum _128403 s) = (@nsum _128403 s).
Proof. exact (eq_refl (@nsum _128403 s)). Qed.
Lemma lem6991416 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) : (term121 _128402 _128403 s R f y) = (term140 _128402 _128403 s R f y).
Proof. exact (MK_COMB (@lem6991415 _128403 s) (@lem6991381 _128402 _128403 R f y)). Qed.
Lemma lem6991450 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (y : _128402) : (term110 _128402 _128403 s R f y) = (term140 _128402 _128403 s R f y).
Proof. exact (TRANS (@lem6991302 _128402 _128403 s R f y) (@lem6991416 _128402 _128403 s R f y)). Qed.
Lemma lem6991451 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term141 _128402 _128403 s R f) = (term142 _128402 _128403 s R f).
Proof. exact (fun_ext (fun y : _128402 => @lem6991450 _128402 _128403 s R f y)). Qed.
Lemma lem6991485 {_128402 : Type'} (t : _128402 -> Prop) : (@nsum _128402 t) = (@nsum _128402 t).
Proof. exact (eq_refl (@nsum _128402 t)). Qed.
Lemma lem6991486 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term13 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f).
Proof. exact (MK_COMB (@lem6991485 _128402 t) (@lem6991451 _128402 _128403 s R f)). Qed.
Lemma lem6991520 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : ((term12 _128402 _128403 s t R f) = (term13 _128402 _128403 t s R f)) = ((term86 _128402 _128403 s t R f) = (term143 _128402 _128403 t s R f)).
Proof. exact (MK_COMB (@lem6991234 _128402 _128403 s t R f) (@lem6991486 _128402 _128403 t s R f)). Qed.
Lemma lem6991589 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : term144 _128402 _128403 t s R f.
Proof. exact (fun h0 : term11 _128402 _128403 s t => @lem6991520 _128402 _128403 t s R f). Qed.
Lemma lem6991590 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : term145 _128402 _128403 t s R f.
Proof. exact (@lem6990971 _128402 _128403 R f s t ((term86 _128402 _128403 s t R f) = (term143 _128402 _128403 t s R f))). Qed.
Lemma lem6991591 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term146 _128402 _128403 t s R f) = (term147 _128402 _128403 t s R f).
Proof. exact (@lem6991590 _128402 _128403 t s R f (@lem6991589 _128402 _128403 t s R f)). Qed.
Lemma lem6991759 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term147 _128402 _128403 t s R f) = (term146 _128402 _128403 t s R f).
Proof. exact (SYM (@lem6991591 _128402 _128403 t s R f)). Qed.
Lemma lem6991760 {_128402 _128403 : Type'} (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term11 _128402 _128403 s t) : term11 _128402 _128403 s t.
Proof. exact (h1). Qed.
Lemma lem6991761 {A B : Type'} (h1 : term148 A B) : term148 A B.
Proof. exact (h1). Qed.
Lemma lem6991762 {A B : Type'} (f : type1415 A B) (h1 : term148 A B) : term149 A B f.
Proof. exact (@lem6991761 A B h1 f). Qed.
Lemma lem6991763 {A B : Type'} (f : type1415 A B) : (term149 A B f) = (term150 A B f).
Proof. exact (eq_refl (term149 A B f)). Qed.
Lemma lem6991764 {A B : Type'} (f : type1415 A B) (h1 : term148 A B) : term150 A B f.
Proof. exact (EQ_MP (@lem6991763 A B f) (@lem6991762 A B f h1)). Qed.
Lemma lem6991765 {A B : Type'} (f : type1415 A B) (s : A -> Prop) (h1 : term148 A B) : term151 A B f s.
Proof. exact (@lem6991764 A B f h1 s). Qed.
Lemma lem6991766 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term151 A B f s) = (term152 A B s f).
Proof. exact (eq_refl (term151 A B f s)). Qed.
Lemma lem6991767 {A B : Type'} (s : A -> Prop) (f : type1415 A B) (h1 : term148 A B) : term152 A B s f.
Proof. exact (EQ_MP (@lem6991766 A B s f) (@lem6991765 A B f s h1)). Qed.
Lemma lem6991768 {A B : Type'} (s : A -> Prop) (f : type1415 A B) (t : B -> Prop) (h1 : term148 A B) : term153 A B s f t.
Proof. exact (@lem6991767 A B s f h1 t). Qed.
Lemma lem6991769 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : (term153 A B s f t) = (term154 A B t s f).
Proof. exact (eq_refl (term153 A B s f t)). Qed.
Lemma lem6991770 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) (h1 : term148 A B) : term154 A B t s f.
Proof. exact (EQ_MP (@lem6991769 A B t s f) (@lem6991768 A B s f t h1)). Qed.
Lemma lem6991771 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term155 A B s t) : term155 A B s t.
Proof. exact (h1). Qed.
Lemma lem6991772 {A B : Type'} (f : type1415 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term148 A B) (h2 : term155 A B s t) : (term156 A B s t f) = (term157 A B t s f).
Proof. exact (@lem6991770 A B t s f h1 (@lem6991771 A B s t h2)). Qed.
Lemma lem6991773 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term148 A B) (h2 : term155 A B s t) : term158 A B t s.
Proof. exact (fun f : type1415 A B => @lem6991772 A B f s t h1 h2). Qed.
Lemma lem6991774 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term148 A B) : term159 A B t s.
Proof. exact (fun h0 : term155 A B s t => @lem6991773 A B s t h1 h0). Qed.
Lemma lem6991775 {A B : Type'} (s : A -> Prop) (h1 : term148 A B) : term160 A B s.
Proof. exact (fun t : B -> Prop => @lem6991774 A B t s h1). Qed.
Lemma lem6991776 {A B : Type'} (h1 : term148 A B) : term161 A B.
Proof. exact (fun s : A -> Prop => @lem6991775 A B s h1). Qed.
Lemma lem6991777 {A B : Type'} : term162 A B.
Proof. exact (fun h0 : term148 A B => @lem6991776 A B h0). Qed.
Lemma lem6991778 {A B : Type'} : term161 A B.
Proof. exact (@lem6991777 A B (@lem6961567 A B)). Qed.
Lemma lem6991779 {A B : Type'} (s : A -> Prop) : term163 A B s.
Proof. exact (@lem6991778 A B s). Qed.
Lemma lem6991780 {A B : Type'} (s : A -> Prop) : (term163 A B s) = (term160 A B s).
Proof. exact (eq_refl (term163 A B s)). Qed.
Lemma lem6991781 {A B : Type'} (s : A -> Prop) : term160 A B s.
Proof. exact (EQ_MP (@lem6991780 A B s) (@lem6991779 A B s)). Qed.
Lemma lem6991782 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term164 A B s t.
Proof. exact (@lem6991781 A B s t). Qed.
Lemma lem6991783 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term164 A B s t) = (term159 A B t s).
Proof. exact (eq_refl (term164 A B s t)). Qed.
Lemma lem6991786 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term159 A B t s.
Proof. exact (EQ_MP (@lem6991783 A B t s) (@lem6991782 A B s t)). Qed.
Lemma lem6991787 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) : term165 _128402 _128403 t s.
Proof. exact (@lem6991786 _128403 _128402 t s). Qed.
Lemma lem6991788 {_128402 _128403 : Type'} (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term11 _128402 _128403 s t) : term166 _128402 _128403 t s.
Proof. exact (@lem6991787 _128402 _128403 t s (@lem6991760 _128402 _128403 s t h1)). Qed.
Lemma lem6991789 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term11 _128402 _128403 s t) : term167 _128402 _128403 t s f.
Proof. exact (@lem6991788 _128402 _128403 s t h1 f). Qed.
Lemma lem6991790 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (f : type1471 _128402 _128403) : (term167 _128402 _128403 t s f) = ((term168 _128402 _128403 s t f) = (term169 _128402 _128403 t s f)).
Proof. exact (eq_refl (term167 _128402 _128403 t s f)). Qed.
Lemma lem6991795 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term11 _128402 _128403 s t) : (term168 _128402 _128403 s t f) = (term169 _128402 _128403 t s f).
Proof. exact (EQ_MP (@lem6991790 _128402 _128403 t s f) (@lem6991789 _128402 _128403 f s t h1)). Qed.
Lemma lem6991796 {_128402 _128403 : Type'} (f : type1471 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term11 _128402 _128403 s t) : (term168 _128402 _128403 s t f) = (term169 _128402 _128403 t s f).
Proof. exact (@lem6991795 _128402 _128403 f s t h1). Qed.
Lemma lem6991797 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term11 _128402 _128403 s t) : (term170 _128402 _128403 s t R f) = (term171 _128402 _128403 t s R f).
Proof. exact (@lem6991796 _128402 _128403 (term172 _128402 _128403 R f) s t h1). Qed.
Lemma lem6991798 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) : (term173 _128402 _128403 R f x) = (term82 _128402 _128403 R f x).
Proof. exact (eq_refl (term173 _128402 _128403 R f x)). Qed.
Lemma lem6991799 {_128402 : Type'} (t : _128402 -> Prop) : (@nsum _128402 t) = (@nsum _128402 t).
Proof. exact (eq_refl (@nsum _128402 t)). Qed.
Lemma lem6991800 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) : (term174 _128402 _128403 t R f x) = (term83 _128402 _128403 t R f x).
Proof. exact (MK_COMB (@lem6991799 _128402 t) (@lem6991798 _128402 _128403 R f x)). Qed.
Lemma lem6991801 {_128402 _128403 : Type'} (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term175 _128402 _128403 t R f) = (term85 _128402 _128403 t R f).
Proof. exact (fun_ext (fun x : _128403 => @lem6991800 _128402 _128403 t R f x)). Qed.
Lemma lem6991802 {_128403 : Type'} (s : _128403 -> Prop) : (@nsum _128403 s) = (@nsum _128403 s).
Proof. exact (eq_refl (@nsum _128403 s)). Qed.
Lemma lem6991803 {_128402 _128403 : Type'} (s : _128403 -> Prop) (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term170 _128402 _128403 s t R f) = (term86 _128402 _128403 s t R f).
Proof. exact (MK_COMB (@lem6991802 _128403 s) (@lem6991801 _128402 _128403 t R f)). Qed.
Lemma lem6991804 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6991805 {_128402 _128403 : Type'} (s : _128403 -> Prop) (t : _128402 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term176 _128402 _128403 s t R f) = (term88 _128402 _128403 s t R f).
Proof. exact (MK_COMB (@lem6991804) (@lem6991803 _128402 _128403 s t R f)). Qed.
Lemma lem6991806 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) : (term173 _128402 _128403 R f x) = (term82 _128402 _128403 R f x).
Proof. exact (eq_refl (term173 _128402 _128403 R f x)). Qed.
Lemma lem6991807 {_128402 : Type'} (j : _128402) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem6991808 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (j : _128402) : (term177 _128402 _128403 R f x j) = (term178 _128402 _128403 R f x j).
Proof. exact (MK_COMB (@lem6991806 _128402 _128403 R f x) (@lem6991807 _128402 j)). Qed.
Lemma lem6991809 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (j : _128402) : (term179 _128402 _128403 R f j) = (term180 _128402 _128403 R f j).
Proof. exact (fun_ext (fun x : _128403 => @lem6991808 _128402 _128403 R f x j)). Qed.
Lemma lem6991810 {_128403 : Type'} (s : _128403 -> Prop) : (@nsum _128403 s) = (@nsum _128403 s).
Proof. exact (eq_refl (@nsum _128403 s)). Qed.
Lemma lem6991811 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (j : _128402) : (term181 _128402 _128403 s R f j) = (term182 _128402 _128403 s R f j).
Proof. exact (MK_COMB (@lem6991810 _128403 s) (@lem6991809 _128402 _128403 R f j)). Qed.
Lemma lem6991812 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term183 _128402 _128403 s R f) = (term184 _128402 _128403 s R f).
Proof. exact (fun_ext (fun j : _128402 => @lem6991811 _128402 _128403 s R f j)). Qed.
Lemma lem6991813 {_128402 : Type'} (t : _128402 -> Prop) : (@nsum _128402 t) = (@nsum _128402 t).
Proof. exact (eq_refl (@nsum _128402 t)). Qed.
Lemma lem6991814 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term171 _128402 _128403 t s R f) = (term185 _128402 _128403 t s R f).
Proof. exact (MK_COMB (@lem6991813 _128402 t) (@lem6991812 _128402 _128403 s R f)). Qed.
Lemma lem6991815 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : ((term170 _128402 _128403 s t R f) = (term171 _128402 _128403 t s R f)) = ((term86 _128402 _128403 s t R f) = (term185 _128402 _128403 t s R f)).
Proof. exact (MK_COMB (@lem6991805 _128402 _128403 s t R f) (@lem6991814 _128402 _128403 t s R f)). Qed.
Lemma lem6991816 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term11 _128402 _128403 s t) : (term86 _128402 _128403 s t R f) = (term185 _128402 _128403 t s R f).
Proof. exact (EQ_MP (@lem6991815 _128402 _128403 t s R f) (@lem6991797 _128402 _128403 R f s t h1)). Qed.
Lemma lem6991818 {A B : Type'} (f : A -> B) (y : A) : (term69 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6991819 {_128402 : Type'} (f : _128402 -> nat) (y : _128402) : (term70 _128402 f y) = (f y).
Proof. exact (@lem6991818 _128402 nat f y). Qed.
Lemma lem6991820 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (j : _128402) : (term186 _128402 _128403 R f x j) = (term178 _128402 _128403 R f x j).
Proof. exact (@lem6991819 _128402 (term82 _128402 _128403 R f x) j). Qed.
Lemma lem6991821 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (y : _128402) : (term178 _128402 _128403 R f x y) = (term81 _128402 _128403 R f x y).
Proof. exact (eq_refl (term178 _128402 _128403 R f x y)). Qed.
Lemma lem6991822 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) : (term187 _128402 _128403 R f x) = (term82 _128402 _128403 R f x).
Proof. exact (fun_ext (fun y : _128402 => @lem6991821 _128402 _128403 R f x y)). Qed.
Lemma lem6991823 {_128402 : Type'} (j : _128402) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem6991824 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (j : _128402) : (term186 _128402 _128403 R f x j) = (term178 _128402 _128403 R f x j).
Proof. exact (MK_COMB (@lem6991822 _128402 _128403 R f x) (@lem6991823 _128402 j)). Qed.
Lemma lem6991825 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6991826 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (j : _128402) : (term188 _128402 _128403 R f x j) = (term189 _128402 _128403 R f x j).
Proof. exact (MK_COMB (@lem6991825) (@lem6991824 _128402 _128403 R f x j)). Qed.
Lemma lem6991827 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (j : _128402) : (term178 _128402 _128403 R f x j) = (term81 _128402 _128403 R f x j).
Proof. exact (eq_refl (term178 _128402 _128403 R f x j)). Qed.
Lemma lem6991828 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (j : _128402) : ((term186 _128402 _128403 R f x j) = (term178 _128402 _128403 R f x j)) = ((term178 _128402 _128403 R f x j) = (term81 _128402 _128403 R f x j)).
Proof. exact (MK_COMB (@lem6991826 _128402 _128403 R f x j) (@lem6991827 _128402 _128403 R f x j)). Qed.
Lemma lem6991829 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (x : _128403) (j : _128402) : (term178 _128402 _128403 R f x j) = (term81 _128402 _128403 R f x j).
Proof. exact (EQ_MP (@lem6991828 _128402 _128403 R f x j) (@lem6991820 _128402 _128403 R f x j)). Qed.
Lemma lem6991830 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (j : _128402) : (term180 _128402 _128403 R f j) = (term139 _128402 _128403 R f j).
Proof. exact (fun_ext (fun x : _128403 => @lem6991829 _128402 _128403 R f x j)). Qed.
Lemma lem6991831 {_128403 : Type'} (s : _128403 -> Prop) : (@nsum _128403 s) = (@nsum _128403 s).
Proof. exact (eq_refl (@nsum _128403 s)). Qed.
Lemma lem6991832 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (j : _128402) : (term182 _128402 _128403 s R f j) = (term140 _128402 _128403 s R f j).
Proof. exact (MK_COMB (@lem6991831 _128403 s) (@lem6991830 _128402 _128403 R f j)). Qed.
Lemma lem6991833 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term184 _128402 _128403 s R f) = (term142 _128402 _128403 s R f).
Proof. exact (fun_ext (fun j : _128402 => @lem6991832 _128402 _128403 s R f j)). Qed.
Lemma lem6991834 {_128402 : Type'} (t : _128402 -> Prop) : (@nsum _128402 t) = (@nsum _128402 t).
Proof. exact (eq_refl (@nsum _128402 t)). Qed.
Lemma lem6991835 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term185 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f).
Proof. exact (MK_COMB (@lem6991834 _128402 t) (@lem6991833 _128402 _128403 s R f)). Qed.
Lemma lem6991836 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term11 _128402 _128403 s t) : (term86 _128402 _128403 s t R f) = (term143 _128402 _128403 t s R f).
Proof. exact (TRANS (@lem6991816 _128402 _128403 R f s t h1) (@lem6991835 _128402 _128403 t s R f)). Qed.
Lemma lem6991837 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6991838 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term11 _128402 _128403 s t) : (term88 _128402 _128403 s t R f) = (term190 _128402 _128403 t s R f).
Proof. exact (MK_COMB (@lem6991837) (@lem6991836 _128402 _128403 R f s t h1)). Qed.
Lemma lem6991839 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f).
Proof. exact (eq_refl (term143 _128402 _128403 t s R f)). Qed.
Lemma lem6991840 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term11 _128402 _128403 s t) : ((term86 _128402 _128403 s t R f) = (term143 _128402 _128403 t s R f)) = ((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)).
Proof. exact (MK_COMB (@lem6991838 _128402 _128403 R f s t h1) (@lem6991839 _128402 _128403 t s R f)). Qed.
Lemma lem6991842 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6991843 (x : nat) : (x = x) = True.
Proof. exact (@lem6991842 nat x). Qed.
Lemma lem6991844 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : ((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True.
Proof. exact (@lem6991843 (term143 _128402 _128403 t s R f)). Qed.
Lemma lem6991847 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term191 _128402 _128403 t s R f) = (term191 _128402 _128403 t s R f).
Proof. exact (eq_refl (term191 _128402 _128403 t s R f)). Qed.
Lemma lem6991848 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term191 _128402 _128403 t s R f) = (((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True).
Proof. exact (eq_refl (term191 _128402 _128403 t s R f)). Qed.
Lemma lem6991849 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term192 _128402 _128403 t s R f) = (term192 _128402 _128403 t s R f).
Proof. exact (eq_refl (term192 _128402 _128403 t s R f)). Qed.
Lemma lem6991850 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : ((term191 _128402 _128403 t s R f) = (term191 _128402 _128403 t s R f)) = ((term191 _128402 _128403 t s R f) = (((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True)).
Proof. exact (MK_COMB (@lem6991849 _128402 _128403 t s R f) (@lem6991848 _128402 _128403 t s R f)). Qed.
Lemma lem6991851 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term191 _128402 _128403 t s R f) = (((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True).
Proof. exact (eq_refl (term191 _128402 _128403 t s R f)). Qed.
Lemma lem6991852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6991853 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term192 _128402 _128403 t s R f) = (term193 _128402 _128403 t s R f).
Proof. exact (MK_COMB (@lem6991852) (@lem6991851 _128402 _128403 t s R f)). Qed.
Lemma lem6991854 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True) = (((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True).
Proof. exact (eq_refl (((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True)). Qed.
Lemma lem6991855 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : ((term191 _128402 _128403 t s R f) = (((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True)) = ((((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True) = (((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True)).
Proof. exact (MK_COMB (@lem6991853 _128402 _128403 t s R f) (@lem6991854 _128402 _128403 t s R f)). Qed.
Lemma lem6991856 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : ((term191 _128402 _128403 t s R f) = (term191 _128402 _128403 t s R f)) = ((((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True) = (((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True)).
Proof. exact (TRANS (@lem6991850 _128402 _128403 t s R f) (@lem6991855 _128402 _128403 t s R f)). Qed.
Lemma lem6991857 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True) = (((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True).
Proof. exact (EQ_MP (@lem6991856 _128402 _128403 t s R f) (@lem6991847 _128402 _128403 t s R f)). Qed.
Lemma lem6991858 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : ((term143 _128402 _128403 t s R f) = (term143 _128402 _128403 t s R f)) = True.
Proof. exact (EQ_MP (@lem6991857 _128402 _128403 t s R f) (@lem6991844 _128402 _128403 t s R f)). Qed.
Lemma lem6991859 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term11 _128402 _128403 s t) : ((term86 _128402 _128403 s t R f) = (term143 _128402 _128403 t s R f)) = True.
Proof. exact (TRANS (@lem6991840 _128402 _128403 R f s t h1) (@lem6991858 _128402 _128403 t s R f)). Qed.
Lemma lem6991860 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term11 _128402 _128403 s t) : True = ((term86 _128402 _128403 s t R f) = (term143 _128402 _128403 t s R f)).
Proof. exact (SYM (@lem6991859 _128402 _128403 R f s t h1)). Qed.
Lemma lem6991861 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term11 _128402 _128403 s t) : (term86 _128402 _128403 s t R f) = (term143 _128402 _128403 t s R f).
Proof. exact (EQ_MP (@lem6991860 _128402 _128403 R f s t h1) (@lem0)). Qed.
Lemma lem6991862 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : term147 _128402 _128403 t s R f.
Proof. exact (fun h0 : term11 _128402 _128403 s t => @lem6991861 _128402 _128403 R f s t h0). Qed.
Lemma lem6991863 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : term146 _128402 _128403 t s R f.
Proof. exact (EQ_MP (@lem6991759 _128402 _128403 t s R f) (@lem6991862 _128402 _128403 t s R f)). Qed.
Lemma lem6991868 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : term194 _128402 _128403 s R f.
Proof. exact (fun t : _128402 -> Prop => @lem6991863 _128402 _128403 t s R f). Qed.
Lemma lem6991873 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : term195 _128402 _128403 R f.
Proof. exact (fun s : _128403 -> Prop => @lem6991868 _128402 _128403 s R f). Qed.
Lemma lem6991878 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) : term196 _128402 _128403 R.
Proof. exact (fun f : type1471 _128402 _128403 => @lem6991873 _128402 _128403 R f). Qed.
Lemma lem6991883 {_128402 _128403 : Type'} : term197 _128402 _128403.
Proof. exact (fun R : type1470 _128402 _128403 => @lem6991878 _128402 _128403 R). Qed.
