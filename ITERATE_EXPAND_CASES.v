Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_EXPAND_CASES_term_abbrevs.
Require Import SUPPORT_SUPPORT_spec.
Require Import iterate_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem5737861 {_119851 _119862 : Type'} (op : type1400 _119851) : term0 _119851 _119862 op.
Proof. exact (@lem5718586 _119851 _119862 op). Qed.
Lemma lem5737862 {_119851 _119862 : Type'} (op : type1400 _119851) : (term0 _119851 _119862 op) = (term1 _119851 _119862 op).
Proof. exact (eq_refl (term0 _119851 _119862 op)). Qed.
Lemma lem5737863 {_119851 _119862 : Type'} (op : type1400 _119851) : term1 _119851 _119862 op.
Proof. exact (EQ_MP (@lem5737862 _119851 _119862 op) (@lem5737861 _119851 _119862 op)). Qed.
Lemma lem5737864 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) : term2 _119851 _119862 op f.
Proof. exact (@lem5737863 _119851 _119862 op f). Qed.
Lemma lem5737865 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) : (term2 _119851 _119862 op f) = (term3 _119851 _119862 op f).
Proof. exact (eq_refl (term2 _119851 _119862 op f)). Qed.
Lemma lem5737866 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) : term3 _119851 _119862 op f.
Proof. exact (EQ_MP (@lem5737865 _119851 _119862 op f) (@lem5737864 _119851 _119862 op f)). Qed.
Lemma lem5737867 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : term4 _119851 _119862 op f s.
Proof. exact (@lem5737866 _119851 _119862 op f s). Qed.
Lemma lem5737868 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : (term4 _119851 _119862 op f s) = ((term5 _119851 _119862 op f s) = (@support _119862 _119851 op f s)).
Proof. exact (eq_refl (term4 _119851 _119862 op f s)). Qed.
Lemma lem5737870 {_119779 A : Type'} (f : A -> _119779) : term6 _119779 A f.
Proof. exact (@lem5718049 _119779 A f). Qed.
Lemma lem5737871 {_119779 A : Type'} (f : A -> _119779) : (term6 _119779 A f) = (term7 _119779 A f).
Proof. exact (eq_refl (term6 _119779 A f)). Qed.
Lemma lem5737872 {_119779 A : Type'} (f : A -> _119779) : term7 _119779 A f.
Proof. exact (EQ_MP (@lem5737871 _119779 A f) (@lem5737870 _119779 A f)). Qed.
Lemma lem5737873 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : term8 _119779 A f s.
Proof. exact (@lem5737872 _119779 A f s). Qed.
Lemma lem5737874 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : (term8 _119779 A f s) = (term9 _119779 A f s).
Proof. exact (eq_refl (term8 _119779 A f s)). Qed.
Lemma lem5737875 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : term9 _119779 A f s.
Proof. exact (EQ_MP (@lem5737874 _119779 A f s) (@lem5737873 _119779 A f s)). Qed.
Lemma lem5737876 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : term10 _119779 A f s op.
Proof. exact (@lem5737875 _119779 A f s op). Qed.
Lemma lem5737877 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (term10 _119779 A f s op) = ((@iterate _119779 A op s f) = (term11 _119779 A f s op)).
Proof. exact (eq_refl (term10 _119779 A f s op)). Qed.
Lemma lem5737894 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (@iterate _119779 A op s f) = (term11 _119779 A f s op).
Proof. exact (EQ_MP (@lem5737877 _119779 A f s op) (@lem5737876 _119779 A f s op)). Qed.
Lemma lem5737895 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) : (@iterate _120327 _120333 op s f) = (term11 _120327 _120333 f s op).
Proof. exact (@lem5737894 _120327 _120333 f s op). Qed.
Lemma lem5737929 {_120327 : Type'} : (@eq _120327) = (@eq _120327).
Proof. exact (eq_refl (@eq _120327)). Qed.
Lemma lem5737930 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) : (term12 _120327 _120333 op s f) = (term13 _120327 _120333 f s op).
Proof. exact (MK_COMB (@lem5737929 _120327) (@lem5737895 _120327 _120333 f s op)). Qed.
Lemma lem5737965 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term14 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5737966 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term15 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5737965 _2963 g t e g' t' e'). Qed.
Lemma lem5737967 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term16 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5737966 _2963 g t e g' t'). Qed.
Lemma lem5737968 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term17 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5737967 _2963 g t e g'). Qed.
Lemma lem5737969 {_120327 : Type'} (g : Prop) (t : _120327) (e : _120327) : term17 _120327 g t e.
Proof. exact (@lem5737968 _120327 g t e). Qed.
Lemma lem5737970 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : term18 _120327 _120333 s f op.
Proof. exact (@lem5737969 _120327 (term19 _120327 _120333 op f s) (term20 _120327 _120333 op s f) (@neutral _120327 op)). Qed.
Lemma lem5737971 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) (g' : Prop) : term21 _120327 _120333 s f op g'.
Proof. exact (@lem5737970 _120327 _120333 s f op g'). Qed.
Lemma lem5737972 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) (g' : Prop) : (term21 _120327 _120333 s f op g') = (term22 _120327 _120333 s f op g').
Proof. exact (eq_refl (term21 _120327 _120333 s f op g')). Qed.
Lemma lem5737973 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) (g' : Prop) : term22 _120327 _120333 s f op g'.
Proof. exact (EQ_MP (@lem5737972 _120327 _120333 s f op g') (@lem5737971 _120327 _120333 s f op g')). Qed.
Lemma lem5737974 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) (g' : Prop) (t' : _120327) : term23 _120327 _120333 s f op g' t'.
Proof. exact (@lem5737973 _120327 _120333 s f op g' t'). Qed.
Lemma lem5737975 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) (g' : Prop) (t' : _120327) : (term23 _120327 _120333 s f op g' t') = (term24 _120327 _120333 s f op g' t').
Proof. exact (eq_refl (term23 _120327 _120333 s f op g' t')). Qed.
Lemma lem5737976 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) (g' : Prop) (t' : _120327) : term24 _120327 _120333 s f op g' t'.
Proof. exact (EQ_MP (@lem5737975 _120327 _120333 s f op g' t') (@lem5737974 _120327 _120333 s f op g' t')). Qed.
Lemma lem5737977 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) (g' : Prop) (t' : _120327) (e' : _120327) : term25 _120327 _120333 s f op g' t' e'.
Proof. exact (@lem5737976 _120327 _120333 s f op g' t' e'). Qed.
Lemma lem5737978 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) (g' : Prop) (t' : _120327) (e' : _120327) : (term25 _120327 _120333 s f op g' t' e') = (term26 _120327 _120333 s f op g' t' e').
Proof. exact (eq_refl (term25 _120327 _120333 s f op g' t' e')). Qed.
Lemma lem5737979 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) (g' : Prop) (t' : _120327) (e' : _120327) : term26 _120327 _120333 s f op g' t' e'.
Proof. exact (EQ_MP (@lem5737978 _120327 _120333 s f op g' t' e') (@lem5737977 _120327 _120333 s f op g' t' e')). Qed.
Lemma lem5737980 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) : (term19 _120327 _120333 op f s) = (term19 _120327 _120333 op f s).
Proof. exact (eq_refl (term19 _120327 _120333 op f s)). Qed.
Lemma lem5737981 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) (t' : _120327) (e' : _120327) : term27 _120327 _120333 op f s t' e'.
Proof. exact (@lem5737979 _120327 _120333 s f op (term19 _120327 _120333 op f s) t' e'). Qed.
Lemma lem5737982 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) (t' : _120327) (e' : _120327) : term28 _120327 _120333 op f s t' e'.
Proof. exact (@lem5737981 _120327 _120333 op f s t' e' (@lem5737980 _120327 _120333 op f s)). Qed.
Lemma lem5737983 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) (h1 : term19 _120327 _120333 op f s) : term19 _120327 _120333 op f s.
Proof. exact (h1). Qed.
Lemma lem5737984 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) : (term19 _120327 _120333 op f s) = ((term19 _120327 _120333 op f s) = True).
Proof. exact (@lem7 (term19 _120327 _120333 op f s)). Qed.
Lemma lem5737987 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (@iterate _119779 A op s f) = (term11 _119779 A f s op).
Proof. exact (EQ_MP (@lem5737877 _119779 A f s op) (@lem5737876 _119779 A f s op)). Qed.
Lemma lem5737988 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) : (@iterate _120327 _120333 op s f) = (term11 _120327 _120333 f s op).
Proof. exact (@lem5737987 _120327 _120333 f s op). Qed.
Lemma lem5737989 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) : (term20 _120327 _120333 op s f) = (term29 _120327 _120333 f s op).
Proof. exact (@lem5737988 _120327 _120333 f (@support _120333 _120327 op f s) op). Qed.
Lemma lem5737991 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term14 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5737992 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term15 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5737991 _2963 g t e g' t' e'). Qed.
Lemma lem5737993 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term16 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5737992 _2963 g t e g' t'). Qed.
Lemma lem5737994 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term17 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5737993 _2963 g t e g'). Qed.
Lemma lem5737995 {_120327 : Type'} (g : Prop) (t : _120327) (e : _120327) : term17 _120327 g t e.
Proof. exact (@lem5737994 _120327 g t e). Qed.
Lemma lem5737996 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) : term30 _120327 _120333 f s op.
Proof. exact (@lem5737995 _120327 (term31 _120327 _120333 op f s) (term32 _120327 _120333 f s op) (@neutral _120327 op)). Qed.
Lemma lem5737997 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) (g' : Prop) : term33 _120327 _120333 f s op g'.
Proof. exact (@lem5737996 _120327 _120333 f s op g'). Qed.
Lemma lem5737998 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) (g' : Prop) : (term33 _120327 _120333 f s op g') = (term34 _120327 _120333 f s op g').
Proof. exact (eq_refl (term33 _120327 _120333 f s op g')). Qed.
Lemma lem5737999 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) (g' : Prop) : term34 _120327 _120333 f s op g'.
Proof. exact (EQ_MP (@lem5737998 _120327 _120333 f s op g') (@lem5737997 _120327 _120333 f s op g')). Qed.
Lemma lem5738000 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) (g' : Prop) (t' : _120327) : term35 _120327 _120333 f s op g' t'.
Proof. exact (@lem5737999 _120327 _120333 f s op g' t'). Qed.
Lemma lem5738001 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) (g' : Prop) (t' : _120327) : (term35 _120327 _120333 f s op g' t') = (term36 _120327 _120333 f s op g' t').
Proof. exact (eq_refl (term35 _120327 _120333 f s op g' t')). Qed.
Lemma lem5738002 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) (g' : Prop) (t' : _120327) : term36 _120327 _120333 f s op g' t'.
Proof. exact (EQ_MP (@lem5738001 _120327 _120333 f s op g' t') (@lem5738000 _120327 _120333 f s op g' t')). Qed.
Lemma lem5738003 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) (g' : Prop) (t' : _120327) (e' : _120327) : term37 _120327 _120333 f s op g' t' e'.
Proof. exact (@lem5738002 _120327 _120333 f s op g' t' e'). Qed.
Lemma lem5738004 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) (g' : Prop) (t' : _120327) (e' : _120327) : (term37 _120327 _120333 f s op g' t' e') = (term38 _120327 _120333 f s op g' t' e').
Proof. exact (eq_refl (term37 _120327 _120333 f s op g' t' e')). Qed.
Lemma lem5738005 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) (g' : Prop) (t' : _120327) (e' : _120327) : term38 _120327 _120333 f s op g' t' e'.
Proof. exact (EQ_MP (@lem5738004 _120327 _120333 f s op g' t' e') (@lem5738003 _120327 _120333 f s op g' t' e')). Qed.
Lemma lem5738007 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : (term5 _119851 _119862 op f s) = (@support _119862 _119851 op f s).
Proof. exact (EQ_MP (@lem5737868 _119851 _119862 op f s) (@lem5737867 _119851 _119862 op f s)). Qed.
Lemma lem5738008 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) : (term5 _120327 _120333 op f s) = (@support _120333 _120327 op f s).
Proof. exact (@lem5738007 _120327 _120333 op f s). Qed.
Lemma lem5738009 {_120333 : Type'} : (@FINITE _120333) = (@FINITE _120333).
Proof. exact (eq_refl (@FINITE _120333)). Qed.
Lemma lem5738010 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) : (term31 _120327 _120333 op f s) = (term19 _120327 _120333 op f s).
Proof. exact (MK_COMB (@lem5738009 _120333) (@lem5738008 _120327 _120333 op f s)). Qed.
Lemma lem5738012 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) (h1 : term19 _120327 _120333 op f s) : (term19 _120327 _120333 op f s) = True.
Proof. exact (EQ_MP (@lem5737984 _120327 _120333 op f s) (@lem5737983 _120327 _120333 op f s h1)). Qed.
Lemma lem5738013 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) (h1 : term19 _120327 _120333 op f s) : (term31 _120327 _120333 op f s) = True.
Proof. exact (TRANS (@lem5738010 _120327 _120333 op f s) (@lem5738012 _120327 _120333 op f s h1)). Qed.
Lemma lem5738014 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) (t' : _120327) (e' : _120327) : term39 _120327 _120333 f s op t' e'.
Proof. exact (@lem5738005 _120327 _120333 f s op True t' e'). Qed.
Lemma lem5738015 {_120327 _120333 : Type'} (t' : _120327) (e' : _120327) (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) (h1 : term19 _120327 _120333 op f s) : term40 _120327 _120333 f s op t' e'.
Proof. exact (@lem5738014 _120327 _120333 f s op t' e' (@lem5738013 _120327 _120333 op f s h1)). Qed.
Lemma lem5738022 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : (term5 _119851 _119862 op f s) = (@support _119862 _119851 op f s).
Proof. exact (EQ_MP (@lem5737868 _119851 _119862 op f s) (@lem5737867 _119851 _119862 op f s)). Qed.
Lemma lem5738023 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) : (term5 _120327 _120333 op f s) = (@support _120333 _120327 op f s).
Proof. exact (@lem5738022 _120327 _120333 op f s). Qed.
Lemma lem5738024 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) : (term41 _120327 _120333 op f) = (term41 _120327 _120333 op f).
Proof. exact (eq_refl (term41 _120327 _120333 op f)). Qed.
Lemma lem5738025 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) : (term42 _120327 _120333 op f s) = (term43 _120327 _120333 op f s).
Proof. exact (MK_COMB (@lem5738024 _120327 _120333 op f) (@lem5738023 _120327 _120333 op f s)). Qed.
Lemma lem5738026 {_120327 : Type'} (op : type1400 _120327) : (@neutral _120327 op) = (@neutral _120327 op).
Proof. exact (eq_refl (@neutral _120327 op)). Qed.
Lemma lem5738027 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) : (term32 _120327 _120333 f s op) = (term44 _120327 _120333 f s op).
Proof. exact (MK_COMB (@lem5738025 _120327 _120333 op f s) (@lem5738026 _120327 op)). Qed.
Lemma lem5738028 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) : term45 _120327 _120333 f s op.
Proof. exact (fun h0 : True => @lem5738027 _120327 _120333 f s op). Qed.
Lemma lem5738029 {_120327 _120333 : Type'} (e' : _120327) (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) (h1 : term19 _120327 _120333 op f s) : term46 _120327 _120333 f s op e'.
Proof. exact (@lem5738015 _120327 _120333 (term44 _120327 _120333 f s op) e' op f s h1). Qed.
Lemma lem5738030 {_120327 _120333 : Type'} (e' : _120327) (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) (h1 : term19 _120327 _120333 op f s) : term47 _120327 _120333 f s op e'.
Proof. exact (@lem5738029 _120327 _120333 e' op f s h1 (@lem5738028 _120327 _120333 f s op)). Qed.
Lemma lem5738034 {_120327 : Type'} (op : type1400 _120327) : (@neutral _120327 op) = (@neutral _120327 op).
Proof. exact (eq_refl (@neutral _120327 op)). Qed.
Lemma lem5738035 {_120327 : Type'} (op : type1400 _120327) : term48 _120327 op.
Proof. exact (fun h0 : ~ True => @lem5738034 _120327 op). Qed.
Lemma lem5738036 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) (h1 : term19 _120327 _120333 op f s) : term49 _120327 _120333 f s op.
Proof. exact (@lem5738030 _120327 _120333 (@neutral _120327 op) op f s h1). Qed.
Lemma lem5738037 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) (h1 : term19 _120327 _120333 op f s) : (term29 _120327 _120333 f s op) = (term50 _120327 _120333 f s op).
Proof. exact (@lem5738036 _120327 _120333 op f s h1 (@lem5738035 _120327 op)). Qed.
Lemma lem5738039 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5738040 {_120327 : Type'} (t2 : _120327) (t1 : _120327) : (@COND _120327 True t1 t2) = t1.
Proof. exact (@lem5738039 _120327 t2 t1). Qed.
Lemma lem5738041 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) : (term50 _120327 _120333 f s op) = (term44 _120327 _120333 f s op).
Proof. exact (@lem5738040 _120327 (@neutral _120327 op) (term44 _120327 _120333 f s op)). Qed.
Lemma lem5738042 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) (h1 : term19 _120327 _120333 op f s) : (term29 _120327 _120333 f s op) = (term44 _120327 _120333 f s op).
Proof. exact (TRANS (@lem5738037 _120327 _120333 op f s h1) (@lem5738041 _120327 _120333 f s op)). Qed.
Lemma lem5738043 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) (s : _120333 -> Prop) (h1 : term19 _120327 _120333 op f s) : (term20 _120327 _120333 op s f) = (term44 _120327 _120333 f s op).
Proof. exact (TRANS (@lem5737989 _120327 _120333 f s op) (@lem5738042 _120327 _120333 op f s h1)). Qed.
Lemma lem5738044 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) : term51 _120327 _120333 f s op.
Proof. exact (fun h0 : term19 _120327 _120333 op f s => @lem5738043 _120327 _120333 op f s h0). Qed.
Lemma lem5738045 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) (e' : _120327) : term52 _120327 _120333 f s op e'.
Proof. exact (@lem5737982 _120327 _120333 op f s (term44 _120327 _120333 f s op) e'). Qed.
Lemma lem5738046 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) (e' : _120327) : term53 _120327 _120333 f s op e'.
Proof. exact (@lem5738045 _120327 _120333 f s op e' (@lem5738044 _120327 _120333 f s op)). Qed.
Lemma lem5738050 {_120327 : Type'} (op : type1400 _120327) : (@neutral _120327 op) = (@neutral _120327 op).
Proof. exact (eq_refl (@neutral _120327 op)). Qed.
Lemma lem5738051 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) : term54 _120327 _120333 f s op.
Proof. exact (fun h0 : term55 _120327 _120333 op f s => @lem5738050 _120327 op). Qed.
Lemma lem5738052 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) : term56 _120327 _120333 f s op.
Proof. exact (@lem5738046 _120327 _120333 f s op (@neutral _120327 op)). Qed.
Lemma lem5738053 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) : (term57 _120327 _120333 s f op) = (term11 _120327 _120333 f s op).
Proof. exact (@lem5738052 _120327 _120333 f s op (@lem5738051 _120327 _120333 f s op)). Qed.
Lemma lem5738087 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) : ((@iterate _120327 _120333 op s f) = (term57 _120327 _120333 s f op)) = ((term11 _120327 _120333 f s op) = (term11 _120327 _120333 f s op)).
Proof. exact (MK_COMB (@lem5737930 _120327 _120333 f s op) (@lem5738053 _120327 _120333 f s op)). Qed.
Lemma lem5738089 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5738090 {_120327 : Type'} (x : _120327) : (x = x) = True.
Proof. exact (@lem5738089 _120327 x). Qed.
Lemma lem5738091 {_120327 _120333 : Type'} (f : _120333 -> _120327) (s : _120333 -> Prop) (op : type1400 _120327) : ((term11 _120327 _120333 f s op) = (term11 _120327 _120333 f s op)) = True.
Proof. exact (@lem5738090 _120327 (term11 _120327 _120333 f s op)). Qed.
Lemma lem5738092 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : ((@iterate _120327 _120333 op s f) = (term57 _120327 _120333 s f op)) = True.
Proof. exact (TRANS (@lem5738087 _120327 _120333 f s op) (@lem5738091 _120327 _120333 f s op)). Qed.
Lemma lem5738093 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) : (term58 _120327 _120333 f op) = (term59 _120333).
Proof. exact (fun_ext (fun s : _120333 -> Prop => @lem5738092 _120327 _120333 s f op)). Qed.
Lemma lem5738094 {_120333 : Type'} : (@all (_120333 -> Prop)) = (@all (_120333 -> Prop)).
Proof. exact (eq_refl (@all (_120333 -> Prop))). Qed.
Lemma lem5738095 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) : (term60 _120327 _120333 f op) = (term61 _120333).
Proof. exact (MK_COMB (@lem5738094 _120333) (@lem5738093 _120327 _120333 f op)). Qed.
Lemma lem5738097 {A : Type'} (t : Prop) : (term62 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5738098 {_120333 : Type'} (t : Prop) : (term63 _120333 t) = t.
Proof. exact (@lem5738097 (_120333 -> Prop) t). Qed.
Lemma lem5738099 {_120333 : Type'} : (term61 _120333) = True.
Proof. exact (@lem5738098 _120333 True). Qed.
Lemma lem5738100 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) : (term60 _120327 _120333 f op) = True.
Proof. exact (TRANS (@lem5738095 _120327 _120333 f op) (@lem5738099 _120333)). Qed.
Lemma lem5738101 {_120327 _120333 : Type'} (op : type1400 _120327) : (term64 _120327 _120333 op) = (term65 _120327 _120333).
Proof. exact (fun_ext (fun f : _120333 -> _120327 => @lem5738100 _120327 _120333 f op)). Qed.
Lemma lem5738102 {_120327 _120333 : Type'} : (@all (_120333 -> _120327)) = (@all (_120333 -> _120327)).
Proof. exact (eq_refl (@all (_120333 -> _120327))). Qed.
Lemma lem5738103 {_120327 _120333 : Type'} (op : type1400 _120327) : (term66 _120327 _120333 op) = (term67 _120327 _120333).
Proof. exact (MK_COMB (@lem5738102 _120327 _120333) (@lem5738101 _120327 _120333 op)). Qed.
Lemma lem5738105 {A : Type'} (t : Prop) : (term62 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5738106 {_120327 _120333 : Type'} (t : Prop) : (term68 _120327 _120333 t) = t.
Proof. exact (@lem5738105 (_120333 -> _120327) t). Qed.
Lemma lem5738107 {_120327 _120333 : Type'} : (term67 _120327 _120333) = True.
Proof. exact (@lem5738106 _120327 _120333 True). Qed.
Lemma lem5738108 {_120327 _120333 : Type'} (op : type1400 _120327) : (term66 _120327 _120333 op) = True.
Proof. exact (TRANS (@lem5738103 _120327 _120333 op) (@lem5738107 _120327 _120333)). Qed.
Lemma lem5738109 {_120327 _120333 : Type'} : (term69 _120327 _120333) = (term70 _120327).
Proof. exact (fun_ext (fun op : type1400 _120327 => @lem5738108 _120327 _120333 op)). Qed.
Lemma lem5738110 {_120327 : Type'} : (@all (_120327 -> _120327 -> _120327)) = (@all (_120327 -> _120327 -> _120327)).
Proof. exact (eq_refl (@all (_120327 -> _120327 -> _120327))). Qed.
Lemma lem5738111 {_120327 _120333 : Type'} : (term71 _120327 _120333) = (term72 _120327).
Proof. exact (MK_COMB (@lem5738110 _120327) (@lem5738109 _120327 _120333)). Qed.
Lemma lem5738113 {A : Type'} (t : Prop) : (term62 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5738114 {_120327 : Type'} (t : Prop) : (term73 _120327 t) = t.
Proof. exact (@lem5738113 (type1400 _120327) t). Qed.
Lemma lem5738115 {_120327 : Type'} : (term72 _120327) = True.
Proof. exact (@lem5738114 _120327 True). Qed.
Lemma lem5738116 {_120327 _120333 : Type'} : (term71 _120327 _120333) = True.
Proof. exact (TRANS (@lem5738111 _120327 _120333) (@lem5738115 _120327)). Qed.
Lemma lem5738117 {_120327 _120333 : Type'} : True = (term71 _120327 _120333).
Proof. exact (SYM (@lem5738116 _120327 _120333)). Qed.
Lemma lem5738118 {_120327 _120333 : Type'} : term71 _120327 _120333.
Proof. exact (EQ_MP (@lem5738117 _120327 _120333) (@lem0)). Qed.
