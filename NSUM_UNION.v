Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_UNION_term_abbrevs.
Require Import ITERATE_UNION_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm4211_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem6924917 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem6924919 {_120592 _120607 : Type'} (op : type1400 _120607) : term0 _120592 _120607 op.
Proof. exact (@lem5764203 _120592 _120607 op). Qed.
Lemma lem6924920 {_120592 _120607 : Type'} (op : type1400 _120607) : (term0 _120592 _120607 op) = (term1 _120592 _120607 op).
Proof. exact (eq_refl (term0 _120592 _120607 op)). Qed.
Lemma lem6924921 {_120592 _120607 : Type'} (op : type1400 _120607) : term1 _120592 _120607 op.
Proof. exact (EQ_MP (@lem6924920 _120592 _120607 op) (@lem6924919 _120592 _120607 op)). Qed.
Lemma lem6924922 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @monoidal _120607 op.
Proof. exact (h1). Qed.
Lemma lem6924923 {_120592 _120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : term2 _120592 _120607 op.
Proof. exact (@lem6924921 _120592 _120607 op (@lem6924922 _120607 op h1)). Qed.
Lemma lem6924924 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term3 _120592 _120607 op f.
Proof. exact (@lem6924923 _120592 _120607 op h1 f). Qed.
Lemma lem6924925 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) : (term3 _120592 _120607 op f) = (term4 _120592 _120607 op f).
Proof. exact (eq_refl (term3 _120592 _120607 op f)). Qed.
Lemma lem6924926 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term4 _120592 _120607 op f.
Proof. exact (EQ_MP (@lem6924925 _120592 _120607 op f) (@lem6924924 _120592 _120607 f op h1)). Qed.
Lemma lem6924927 {_120592 _120607 : Type'} (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term5 _120592 _120607 op f s.
Proof. exact (@lem6924926 _120592 _120607 f op h1 s). Qed.
Lemma lem6924928 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term5 _120592 _120607 op f s) = (term6 _120592 _120607 s op f).
Proof. exact (eq_refl (term5 _120592 _120607 op f s)). Qed.
Lemma lem6924929 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term6 _120592 _120607 s op f.
Proof. exact (EQ_MP (@lem6924928 _120592 _120607 s op f) (@lem6924927 _120592 _120607 f s op h1)). Qed.
Lemma lem6924930 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (t : _120592 -> Prop) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term7 _120592 _120607 s op f t.
Proof. exact (@lem6924929 _120592 _120607 s f op h1 t). Qed.
Lemma lem6924931 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term7 _120592 _120607 s op f t) = (term8 _120592 _120607 s op t f).
Proof. exact (eq_refl (term7 _120592 _120607 s op f t)). Qed.
Lemma lem6924932 {_120592 _120607 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term8 _120592 _120607 s op t f.
Proof. exact (EQ_MP (@lem6924931 _120592 _120607 s op t f) (@lem6924930 _120592 _120607 s f t op h1)). Qed.
Lemma lem6924933 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term9 _120592 s t) : term9 _120592 s t.
Proof. exact (h1). Qed.
Lemma lem6924934 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : @monoidal _120607 op) (h2 : term9 _120592 s t) : (term10 _120592 _120607 op s t f) = (term11 _120592 _120607 s op t f).
Proof. exact (@lem6924932 _120592 _120607 s t f op h1 (@lem6924933 _120592 s t h2)). Qed.
Lemma lem6924935 {_120592 _120607 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term8 _120592 _120607 s op t f.
Proof. exact (fun h0 : term9 _120592 s t => @lem6924934 _120592 _120607 f op s t h1 h0). Qed.
Lemma lem6924936 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term12 _120592 _120607 s op t f.
Proof. exact (fun h0 : @monoidal _120607 op => @lem6924935 _120592 _120607 s t f op h0). Qed.
Lemma lem6924938 (p : Prop) (q : Prop) (r : Prop) : (term13 p q r) = (term14 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6924943 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term12 _120592 _120607 s op t f) = (term15 _120592 _120607 s op t f).
Proof. exact (@lem6924938 (@monoidal _120607 op) (term9 _120592 s t) ((term10 _120592 _120607 op s t f) = (term11 _120592 _120607 s op t f))). Qed.
Lemma lem6924960 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term16 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6924961 (p : Prop) (q : Prop) (p' : Prop) : term17 p q p'.
Proof. exact (fun q' : Prop => @lem6924960 p q p' q'). Qed.
Lemma lem6924962 (p : Prop) (q : Prop) : term18 p q.
Proof. exact (fun p' : Prop => @lem6924961 p q p'). Qed.
Lemma lem6924963 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) : term19 _126551 s t f.
Proof. exact (@lem6924962 (term9 _126551 s t) ((term20 _126551 s t f) = (term21 _126551 s t f))). Qed.
Lemma lem6924964 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) (p' : Prop) : term22 _126551 s t f p'.
Proof. exact (@lem6924963 _126551 s t f p'). Qed.
Lemma lem6924965 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) (p' : Prop) : (term22 _126551 s t f p') = (term23 _126551 s t f p').
Proof. exact (eq_refl (term22 _126551 s t f p')). Qed.
Lemma lem6924966 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) (p' : Prop) : term23 _126551 s t f p'.
Proof. exact (EQ_MP (@lem6924965 _126551 s t f p') (@lem6924964 _126551 s t f p')). Qed.
Lemma lem6924967 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) (p' : Prop) (q' : Prop) : term24 _126551 s t f p' q'.
Proof. exact (@lem6924966 _126551 s t f p' q'). Qed.
Lemma lem6924968 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) (p' : Prop) (q' : Prop) : (term24 _126551 s t f p' q') = (term25 _126551 s t f p' q').
Proof. exact (eq_refl (term24 _126551 s t f p' q')). Qed.
Lemma lem6924969 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) (p' : Prop) (q' : Prop) : term25 _126551 s t f p' q'.
Proof. exact (EQ_MP (@lem6924968 _126551 s t f p' q') (@lem6924967 _126551 s t f p' q')). Qed.
Lemma lem6924974 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) : (term9 _126551 s t) = (term9 _126551 s t).
Proof. exact (eq_refl (term9 _126551 s t)). Qed.
Lemma lem6924975 {_126551 : Type'} (f : _126551 -> nat) (s : _126551 -> Prop) (t : _126551 -> Prop) (q' : Prop) : term26 _126551 f s t q'.
Proof. exact (@lem6924969 _126551 s t f (term9 _126551 s t) q'). Qed.
Lemma lem6924976 {_126551 : Type'} (f : _126551 -> nat) (s : _126551 -> Prop) (t : _126551 -> Prop) (q' : Prop) : term27 _126551 f s t q'.
Proof. exact (@lem6924975 _126551 f s t q' (@lem6924974 _126551 s t)). Qed.
Lemma lem6924977 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : term9 _126551 s t.
Proof. exact (h1). Qed.
Lemma lem6924978 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : term28 _126551 s t.
Proof. exact (proj2 (@lem6924977 _126551 s t h1)). Qed.
Lemma lem6924979 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : @DISJOINT _126551 s t.
Proof. exact (proj2 (@lem6924978 _126551 s t h1)). Qed.
Lemma lem6924980 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) : (@DISJOINT _126551 s t) = ((@DISJOINT _126551 s t) = True).
Proof. exact (@lem7 (@DISJOINT _126551 s t)). Qed.
Lemma lem6924982 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : @FINITE _126551 t.
Proof. exact (proj1 (@lem6924978 _126551 s t h1)). Qed.
Lemma lem6924983 {_126551 : Type'} (t : _126551 -> Prop) : (@FINITE _126551 t) = ((@FINITE _126551 t) = True).
Proof. exact (@lem7 (@FINITE _126551 t)). Qed.
Lemma lem6924985 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : @FINITE _126551 s.
Proof. exact (proj1 (@lem6924977 _126551 s t h1)). Qed.
Lemma lem6924986 {_126551 : Type'} (s : _126551 -> Prop) : (@FINITE _126551 s) = ((@FINITE _126551 s) = True).
Proof. exact (@lem7 (@FINITE _126551 s)). Qed.
Lemma lem6924991 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6924992 {_126551 : Type'} : (@nsum _126551) = (@iterate nat _126551 Nat.add).
Proof. exact (@lem6924991 _126551). Qed.
Lemma lem6924993 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) : (@UNION _126551 s t) = (@UNION _126551 s t).
Proof. exact (eq_refl (@UNION _126551 s t)). Qed.
Lemma lem6924994 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) : (term29 _126551 s t) = (term30 _126551 s t).
Proof. exact (MK_COMB (@lem6924992 _126551) (@lem6924993 _126551 s t)). Qed.
Lemma lem6924995 {_126551 : Type'} (f : _126551 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6924996 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) : (term20 _126551 s t f) = (term31 _126551 s t f).
Proof. exact (MK_COMB (@lem6924994 _126551 s t) (@lem6924995 _126551 f)). Qed.
Lemma lem6924998 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term15 _120592 _120607 s op t f.
Proof. exact (EQ_MP (@lem6924943 _120592 _120607 s op t f) (@lem6924936 _120592 _120607 s op t f)). Qed.
Lemma lem6924999 {_126551 : Type'} (s : _126551 -> Prop) (op : type1606) (t : _126551 -> Prop) (f : _126551 -> nat) : term32 _126551 s op t f.
Proof. exact (@lem6924998 _126551 nat s op t f). Qed.
Lemma lem6925000 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) : term33 _126551 s t f.
Proof. exact (@lem6924999 _126551 s Nat.add t f). Qed.
Lemma lem6925004 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem6924917) (@lem6924403)). Qed.
Lemma lem6925005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925006 : term34 = (and True).
Proof. exact (MK_COMB (@lem6925005) (@lem6925004)). Qed.
Lemma lem6925010 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : (@FINITE _126551 s) = True.
Proof. exact (EQ_MP (@lem6924986 _126551 s) (@lem6924985 _126551 s t h1)). Qed.
Lemma lem6925011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925012 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : (term35 _126551 s) = (and True).
Proof. exact (MK_COMB (@lem6925011) (@lem6925010 _126551 s t h1)). Qed.
Lemma lem6925016 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : (@FINITE _126551 t) = True.
Proof. exact (EQ_MP (@lem6924983 _126551 t) (@lem6924982 _126551 s t h1)). Qed.
Lemma lem6925017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925018 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : (term35 _126551 t) = (and True).
Proof. exact (MK_COMB (@lem6925017) (@lem6925016 _126551 s t h1)). Qed.
Lemma lem6925020 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : (@DISJOINT _126551 s t) = True.
Proof. exact (EQ_MP (@lem6924980 _126551 s t) (@lem6924979 _126551 s t h1)). Qed.
Lemma lem6925021 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : (term28 _126551 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem6925018 _126551 s t h1) (@lem6925020 _126551 s t h1)). Qed.
Lemma lem6925023 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6925024 : (True /\ True) = True.
Proof. exact (@lem6925023 True). Qed.
Lemma lem6925025 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : (term28 _126551 s t) = True.
Proof. exact (TRANS (@lem6925021 _126551 s t h1) (@lem6925024)). Qed.
Lemma lem6925026 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : (term9 _126551 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem6925012 _126551 s t h1) (@lem6925025 _126551 s t h1)). Qed.
Lemma lem6925028 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6925029 : (True /\ True) = True.
Proof. exact (@lem6925028 True). Qed.
Lemma lem6925030 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : (term9 _126551 s t) = True.
Proof. exact (TRANS (@lem6925026 _126551 s t h1) (@lem6925029)). Qed.
Lemma lem6925031 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : (term36 _126551 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem6925006) (@lem6925030 _126551 s t h1)). Qed.
Lemma lem6925033 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6925034 : (True /\ True) = True.
Proof. exact (@lem6925033 True). Qed.
Lemma lem6925035 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : (term36 _126551 s t) = True.
Proof. exact (TRANS (@lem6925031 _126551 s t h1) (@lem6925034)). Qed.
Lemma lem6925036 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : True = (term36 _126551 s t).
Proof. exact (SYM (@lem6925035 _126551 s t h1)). Qed.
Lemma lem6925037 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : term36 _126551 s t.
Proof. exact (EQ_MP (@lem6925036 _126551 s t h1) (@lem0)). Qed.
Lemma lem6925038 {_126551 : Type'} (f : _126551 -> nat) (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : (term31 _126551 s t f) = (term37 _126551 s t f).
Proof. exact (@lem6925000 _126551 s t f (@lem6925037 _126551 s t h1)). Qed.
Lemma lem6925039 {_126551 : Type'} (f : _126551 -> nat) (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : (term20 _126551 s t f) = (term37 _126551 s t f).
Proof. exact (TRANS (@lem6924996 _126551 s t f) (@lem6925038 _126551 f s t h1)). Qed.
Lemma lem6925040 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6925041 {_126551 : Type'} (f : _126551 -> nat) (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : (term38 _126551 s t f) = (term39 _126551 s t f).
Proof. exact (MK_COMB (@lem6925040) (@lem6925039 _126551 f s t h1)). Qed.
Lemma lem6925043 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6925044 {_126551 : Type'} : (@nsum _126551) = (@iterate nat _126551 Nat.add).
Proof. exact (@lem6925043 _126551). Qed.
Lemma lem6925045 {_126551 : Type'} (s : _126551 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6925046 {_126551 : Type'} (s : _126551 -> Prop) : (@nsum _126551 s) = (@iterate nat _126551 Nat.add s).
Proof. exact (MK_COMB (@lem6925044 _126551) (@lem6925045 _126551 s)). Qed.
Lemma lem6925047 {_126551 : Type'} (f : _126551 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6925048 {_126551 : Type'} (s : _126551 -> Prop) (f : _126551 -> nat) : (@nsum _126551 s f) = (@iterate nat _126551 Nat.add s f).
Proof. exact (MK_COMB (@lem6925046 _126551 s) (@lem6925047 _126551 f)). Qed.
Lemma lem6925049 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem6925050 {_126551 : Type'} (s : _126551 -> Prop) (f : _126551 -> nat) : (term40 _126551 s f) = (term41 _126551 s f).
Proof. exact (MK_COMB (@lem6925049) (@lem6925048 _126551 s f)). Qed.
Lemma lem6925052 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6925053 {_126551 : Type'} : (@nsum _126551) = (@iterate nat _126551 Nat.add).
Proof. exact (@lem6925052 _126551). Qed.
Lemma lem6925054 {_126551 : Type'} (t : _126551 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6925055 {_126551 : Type'} (t : _126551 -> Prop) : (@nsum _126551 t) = (@iterate nat _126551 Nat.add t).
Proof. exact (MK_COMB (@lem6925053 _126551) (@lem6925054 _126551 t)). Qed.
Lemma lem6925056 {_126551 : Type'} (f : _126551 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6925057 {_126551 : Type'} (t : _126551 -> Prop) (f : _126551 -> nat) : (@nsum _126551 t f) = (@iterate nat _126551 Nat.add t f).
Proof. exact (MK_COMB (@lem6925055 _126551 t) (@lem6925056 _126551 f)). Qed.
Lemma lem6925058 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) : (term21 _126551 s t f) = (term37 _126551 s t f).
Proof. exact (MK_COMB (@lem6925050 _126551 s f) (@lem6925057 _126551 t f)). Qed.
Lemma lem6925059 {_126551 : Type'} (f : _126551 -> nat) (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : ((term20 _126551 s t f) = (term21 _126551 s t f)) = ((term37 _126551 s t f) = (term37 _126551 s t f)).
Proof. exact (MK_COMB (@lem6925041 _126551 f s t h1) (@lem6925058 _126551 s t f)). Qed.
Lemma lem6925061 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6925062 (x : nat) : (x = x) = True.
Proof. exact (@lem6925061 nat x). Qed.
Lemma lem6925063 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) : ((term37 _126551 s t f) = (term37 _126551 s t f)) = True.
Proof. exact (@lem6925062 (term37 _126551 s t f)). Qed.
Lemma lem6925064 {_126551 : Type'} (f : _126551 -> nat) (s : _126551 -> Prop) (t : _126551 -> Prop) (h1 : term9 _126551 s t) : ((term20 _126551 s t f) = (term21 _126551 s t f)) = True.
Proof. exact (TRANS (@lem6925059 _126551 f s t h1) (@lem6925063 _126551 s t f)). Qed.
Lemma lem6925065 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) : term42 _126551 s t f.
Proof. exact (fun h0 : term9 _126551 s t => @lem6925064 _126551 f s t h0). Qed.
Lemma lem6925066 {_126551 : Type'} (f : _126551 -> nat) (s : _126551 -> Prop) (t : _126551 -> Prop) : term43 _126551 f s t.
Proof. exact (@lem6924976 _126551 f s t True). Qed.
Lemma lem6925067 {_126551 : Type'} (f : _126551 -> nat) (s : _126551 -> Prop) (t : _126551 -> Prop) : (term44 _126551 s t f) = (term45 _126551 s t).
Proof. exact (@lem6925066 _126551 f s t (@lem6925065 _126551 s t f)). Qed.
Lemma lem6925069 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6925070 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) : (term45 _126551 s t) = True.
Proof. exact (@lem6925069 (term9 _126551 s t)). Qed.
Lemma lem6925071 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) : (term44 _126551 s t f) = True.
Proof. exact (TRANS (@lem6925067 _126551 f s t) (@lem6925070 _126551 s t)). Qed.
Lemma lem6925072 {_126551 : Type'} (s : _126551 -> Prop) (f : _126551 -> nat) : (term46 _126551 s f) = (term47 _126551).
Proof. exact (fun_ext (fun t : _126551 -> Prop => @lem6925071 _126551 s t f)). Qed.
Lemma lem6925073 {_126551 : Type'} : (@all (_126551 -> Prop)) = (@all (_126551 -> Prop)).
Proof. exact (eq_refl (@all (_126551 -> Prop))). Qed.
Lemma lem6925074 {_126551 : Type'} (s : _126551 -> Prop) (f : _126551 -> nat) : (term48 _126551 s f) = (term49 _126551).
Proof. exact (MK_COMB (@lem6925073 _126551) (@lem6925072 _126551 s f)). Qed.
Lemma lem6925076 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6925077 {_126551 : Type'} (t : Prop) : (term51 _126551 t) = t.
Proof. exact (@lem6925076 (_126551 -> Prop) t). Qed.
Lemma lem6925078 {_126551 : Type'} : (term49 _126551) = True.
Proof. exact (@lem6925077 _126551 True). Qed.
Lemma lem6925079 {_126551 : Type'} (s : _126551 -> Prop) (f : _126551 -> nat) : (term48 _126551 s f) = True.
Proof. exact (TRANS (@lem6925074 _126551 s f) (@lem6925078 _126551)). Qed.
Lemma lem6925080 {_126551 : Type'} (f : _126551 -> nat) : (term52 _126551 f) = (term47 _126551).
Proof. exact (fun_ext (fun s : _126551 -> Prop => @lem6925079 _126551 s f)). Qed.
Lemma lem6925081 {_126551 : Type'} : (@all (_126551 -> Prop)) = (@all (_126551 -> Prop)).
Proof. exact (eq_refl (@all (_126551 -> Prop))). Qed.
Lemma lem6925082 {_126551 : Type'} (f : _126551 -> nat) : (term53 _126551 f) = (term49 _126551).
Proof. exact (MK_COMB (@lem6925081 _126551) (@lem6925080 _126551 f)). Qed.
Lemma lem6925084 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6925085 {_126551 : Type'} (t : Prop) : (term51 _126551 t) = t.
Proof. exact (@lem6925084 (_126551 -> Prop) t). Qed.
Lemma lem6925086 {_126551 : Type'} : (term49 _126551) = True.
Proof. exact (@lem6925085 _126551 True). Qed.
Lemma lem6925087 {_126551 : Type'} (f : _126551 -> nat) : (term53 _126551 f) = True.
Proof. exact (TRANS (@lem6925082 _126551 f) (@lem6925086 _126551)). Qed.
Lemma lem6925088 {_126551 : Type'} : (term54 _126551) = (term55 _126551).
Proof. exact (fun_ext (fun f : _126551 -> nat => @lem6925087 _126551 f)). Qed.
Lemma lem6925089 {_126551 : Type'} : (@all (_126551 -> nat)) = (@all (_126551 -> nat)).
Proof. exact (eq_refl (@all (_126551 -> nat))). Qed.
Lemma lem6925090 {_126551 : Type'} : (term56 _126551) = (term57 _126551).
Proof. exact (MK_COMB (@lem6925089 _126551) (@lem6925088 _126551)). Qed.
Lemma lem6925092 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6925093 {_126551 : Type'} (t : Prop) : (term58 _126551 t) = t.
Proof. exact (@lem6925092 (_126551 -> nat) t). Qed.
Lemma lem6925094 {_126551 : Type'} : (term57 _126551) = True.
Proof. exact (@lem6925093 _126551 True). Qed.
Lemma lem6925095 {_126551 : Type'} : (term56 _126551) = True.
Proof. exact (TRANS (@lem6925090 _126551) (@lem6925094 _126551)). Qed.
Lemma lem6925096 {_126551 : Type'} : True = (term56 _126551).
Proof. exact (SYM (@lem6925095 _126551)). Qed.
Lemma lem6925097 {_126551 : Type'} : term56 _126551.
Proof. exact (EQ_MP (@lem6925096 _126551) (@lem0)). Qed.
