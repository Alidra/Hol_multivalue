Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_EQ_NSUM_term_abbrevs.
Require Import MULT_CLAUSES_spec.
Require Import NSUM_CONST_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem6991884 : term0.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem6991885 : term1.
Proof. exact (proj2 (@lem6991884)). Qed.
Lemma lem6991886 : term2.
Proof. exact (proj2 (@lem6991885)). Qed.
Lemma lem6991902 : term3.
Proof. exact (proj1 (@lem6991886)). Qed.
Lemma lem6991903 (m : nat) : term4 m.
Proof. exact (@lem6991902 m). Qed.
Lemma lem6991904 (m : nat) : (term4 m) = ((term5 m) = m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem6991918 {_127196 : Type'} (c : nat) : term6 _127196 c.
Proof. exact (@lem6940531 _127196 c). Qed.
Lemma lem6991919 {_127196 : Type'} (c : nat) : (term6 _127196 c) = (term7 _127196 c).
Proof. exact (eq_refl (term6 _127196 c)). Qed.
Lemma lem6991920 {_127196 : Type'} (c : nat) : term7 _127196 c.
Proof. exact (EQ_MP (@lem6991919 _127196 c) (@lem6991918 _127196 c)). Qed.
Lemma lem6991921 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) : term8 _127196 c s.
Proof. exact (@lem6991920 _127196 c s). Qed.
Lemma lem6991922 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term8 _127196 c s) = (term9 _127196 s c).
Proof. exact (eq_refl (term8 _127196 c s)). Qed.
Lemma lem6991923 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : term9 _127196 s c.
Proof. exact (EQ_MP (@lem6991922 _127196 s c) (@lem6991921 _127196 c s)). Qed.
Lemma lem6991924 {_127196 : Type'} (s : _127196 -> Prop) (h1 : @FINITE _127196 s) : @FINITE _127196 s.
Proof. exact (h1). Qed.
Lemma lem6991925 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) (h1 : @FINITE _127196 s) : (term10 _127196 s c) = (term11 _127196 s c).
Proof. exact (@lem6991923 _127196 s c (@lem6991924 _127196 s h1)). Qed.
Lemma lem6991938 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term12 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6991939 (p : Prop) (q : Prop) (p' : Prop) : term13 p q p'.
Proof. exact (fun q' : Prop => @lem6991938 p q p' q'). Qed.
Lemma lem6991940 (p : Prop) (q : Prop) : term14 p q.
Proof. exact (fun p' : Prop => @lem6991939 p q p'). Qed.
Lemma lem6991941 {_128422 : Type'} (s : _128422 -> Prop) : term15 _128422 s.
Proof. exact (@lem6991940 (@FINITE _128422 s) ((@CARD _128422 s) = (term16 _128422 s))). Qed.
Lemma lem6991942 {_128422 : Type'} (s : _128422 -> Prop) (p' : Prop) : term17 _128422 s p'.
Proof. exact (@lem6991941 _128422 s p'). Qed.
Lemma lem6991943 {_128422 : Type'} (s : _128422 -> Prop) (p' : Prop) : (term17 _128422 s p') = (term18 _128422 s p').
Proof. exact (eq_refl (term17 _128422 s p')). Qed.
Lemma lem6991944 {_128422 : Type'} (s : _128422 -> Prop) (p' : Prop) : term18 _128422 s p'.
Proof. exact (EQ_MP (@lem6991943 _128422 s p') (@lem6991942 _128422 s p')). Qed.
Lemma lem6991945 {_128422 : Type'} (s : _128422 -> Prop) (p' : Prop) (q' : Prop) : term19 _128422 s p' q'.
Proof. exact (@lem6991944 _128422 s p' q'). Qed.
Lemma lem6991946 {_128422 : Type'} (s : _128422 -> Prop) (p' : Prop) (q' : Prop) : (term19 _128422 s p' q') = (term20 _128422 s p' q').
Proof. exact (eq_refl (term19 _128422 s p' q')). Qed.
Lemma lem6991947 {_128422 : Type'} (s : _128422 -> Prop) (p' : Prop) (q' : Prop) : term20 _128422 s p' q'.
Proof. exact (EQ_MP (@lem6991946 _128422 s p' q') (@lem6991945 _128422 s p' q')). Qed.
Lemma lem6991948 {_128422 : Type'} (s : _128422 -> Prop) : (@FINITE _128422 s) = (@FINITE _128422 s).
Proof. exact (eq_refl (@FINITE _128422 s)). Qed.
Lemma lem6991949 {_128422 : Type'} (s : _128422 -> Prop) (q' : Prop) : term21 _128422 s q'.
Proof. exact (@lem6991947 _128422 s (@FINITE _128422 s) q'). Qed.
Lemma lem6991950 {_128422 : Type'} (s : _128422 -> Prop) (q' : Prop) : term22 _128422 s q'.
Proof. exact (@lem6991949 _128422 s q' (@lem6991948 _128422 s)). Qed.
Lemma lem6991951 {_128422 : Type'} (s : _128422 -> Prop) (h1 : @FINITE _128422 s) : @FINITE _128422 s.
Proof. exact (h1). Qed.
Lemma lem6991952 {_128422 : Type'} (s : _128422 -> Prop) : (@FINITE _128422 s) = ((@FINITE _128422 s) = True).
Proof. exact (@lem7 (@FINITE _128422 s)). Qed.
Lemma lem6991957 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : term9 _127196 s c.
Proof. exact (fun h0 : @FINITE _127196 s => @lem6991925 _127196 c s h0). Qed.
Lemma lem6991958 {_128422 : Type'} (s : _128422 -> Prop) (c : nat) : term9 _128422 s c.
Proof. exact (@lem6991957 _128422 s c). Qed.
Lemma lem6991959 {_128422 : Type'} (s : _128422 -> Prop) : term23 _128422 s.
Proof. exact (@lem6991958 _128422 s term24). Qed.
Lemma lem6991961 {_128422 : Type'} (s : _128422 -> Prop) (h1 : @FINITE _128422 s) : (@FINITE _128422 s) = True.
Proof. exact (EQ_MP (@lem6991952 _128422 s) (@lem6991951 _128422 s h1)). Qed.
Lemma lem6991962 {_128422 : Type'} (s : _128422 -> Prop) (h1 : @FINITE _128422 s) : True = (@FINITE _128422 s).
Proof. exact (SYM (@lem6991961 _128422 s h1)). Qed.
Lemma lem6991963 {_128422 : Type'} (s : _128422 -> Prop) (h1 : @FINITE _128422 s) : @FINITE _128422 s.
Proof. exact (EQ_MP (@lem6991962 _128422 s h1) (@lem0)). Qed.
Lemma lem6991964 {_128422 : Type'} (s : _128422 -> Prop) (h1 : @FINITE _128422 s) : (term16 _128422 s) = (term25 _128422 s).
Proof. exact (@lem6991959 _128422 s (@lem6991963 _128422 s h1)). Qed.
Lemma lem6991966 (m : nat) : (term5 m) = m.
Proof. exact (EQ_MP (@lem6991904 m) (@lem6991903 m)). Qed.
Lemma lem6991967 {_128422 : Type'} (s : _128422 -> Prop) : (term25 _128422 s) = (@CARD _128422 s).
Proof. exact (@lem6991966 (@CARD _128422 s)). Qed.
Lemma lem6991968 {_128422 : Type'} (s : _128422 -> Prop) (h1 : @FINITE _128422 s) : (term16 _128422 s) = (@CARD _128422 s).
Proof. exact (TRANS (@lem6991964 _128422 s h1) (@lem6991967 _128422 s)). Qed.
Lemma lem6991969 {_128422 : Type'} (s : _128422 -> Prop) : (term26 _128422 s) = (term26 _128422 s).
Proof. exact (eq_refl (term26 _128422 s)). Qed.
Lemma lem6991970 {_128422 : Type'} (s : _128422 -> Prop) (h1 : @FINITE _128422 s) : ((@CARD _128422 s) = (term16 _128422 s)) = ((@CARD _128422 s) = (@CARD _128422 s)).
Proof. exact (MK_COMB (@lem6991969 _128422 s) (@lem6991968 _128422 s h1)). Qed.
Lemma lem6991972 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6991973 (x : nat) : (x = x) = True.
Proof. exact (@lem6991972 nat x). Qed.
Lemma lem6991974 {_128422 : Type'} (s : _128422 -> Prop) : ((@CARD _128422 s) = (@CARD _128422 s)) = True.
Proof. exact (@lem6991973 (@CARD _128422 s)). Qed.
Lemma lem6991975 {_128422 : Type'} (s : _128422 -> Prop) (h1 : @FINITE _128422 s) : ((@CARD _128422 s) = (term16 _128422 s)) = True.
Proof. exact (TRANS (@lem6991970 _128422 s h1) (@lem6991974 _128422 s)). Qed.
Lemma lem6991976 {_128422 : Type'} (s : _128422 -> Prop) : term27 _128422 s.
Proof. exact (fun h0 : @FINITE _128422 s => @lem6991975 _128422 s h0). Qed.
Lemma lem6991977 {_128422 : Type'} (s : _128422 -> Prop) : term28 _128422 s.
Proof. exact (@lem6991950 _128422 s True). Qed.
Lemma lem6991978 {_128422 : Type'} (s : _128422 -> Prop) : (term29 _128422 s) = (term30 _128422 s).
Proof. exact (@lem6991977 _128422 s (@lem6991976 _128422 s)). Qed.
Lemma lem6991980 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6991981 {_128422 : Type'} (s : _128422 -> Prop) : (term30 _128422 s) = True.
Proof. exact (@lem6991980 (@FINITE _128422 s)). Qed.
Lemma lem6991982 {_128422 : Type'} (s : _128422 -> Prop) : (term29 _128422 s) = True.
Proof. exact (TRANS (@lem6991978 _128422 s) (@lem6991981 _128422 s)). Qed.
Lemma lem6991983 {_128422 : Type'} : (term31 _128422) = (term32 _128422).
Proof. exact (fun_ext (fun s : _128422 -> Prop => @lem6991982 _128422 s)). Qed.
Lemma lem6991984 {_128422 : Type'} : (@all (_128422 -> Prop)) = (@all (_128422 -> Prop)).
Proof. exact (eq_refl (@all (_128422 -> Prop))). Qed.
Lemma lem6991985 {_128422 : Type'} : (term33 _128422) = (term34 _128422).
Proof. exact (MK_COMB (@lem6991984 _128422) (@lem6991983 _128422)). Qed.
Lemma lem6991987 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6991988 {_128422 : Type'} (t : Prop) : (term36 _128422 t) = t.
Proof. exact (@lem6991987 (_128422 -> Prop) t). Qed.
Lemma lem6991989 {_128422 : Type'} : (term34 _128422) = True.
Proof. exact (@lem6991988 _128422 True). Qed.
Lemma lem6991990 {_128422 : Type'} : (term33 _128422) = True.
Proof. exact (TRANS (@lem6991985 _128422) (@lem6991989 _128422)). Qed.
Lemma lem6991991 {_128422 : Type'} : True = (term33 _128422).
Proof. exact (SYM (@lem6991990 _128422)). Qed.
Lemma lem6991992 {_128422 : Type'} : term33 _128422.
Proof. exact (EQ_MP (@lem6991991 _128422) (@lem0)). Qed.
