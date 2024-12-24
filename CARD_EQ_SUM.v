Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_EQ_SUM_term_abbrevs.
Require Import REAL_MUL_RID_spec.
Require Import SUM_CONST_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7158001 (x : real) : term0 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem7158002 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem7158004 {_132484 : Type'} (c : real) : term2 _132484 c.
Proof. exact (@lem7085323 _132484 c). Qed.
Lemma lem7158005 {_132484 : Type'} (c : real) : (term2 _132484 c) = (term3 _132484 c).
Proof. exact (eq_refl (term2 _132484 c)). Qed.
Lemma lem7158006 {_132484 : Type'} (c : real) : term3 _132484 c.
Proof. exact (EQ_MP (@lem7158005 _132484 c) (@lem7158004 _132484 c)). Qed.
Lemma lem7158007 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : term4 _132484 c s.
Proof. exact (@lem7158006 _132484 c s). Qed.
Lemma lem7158008 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term4 _132484 c s) = (term5 _132484 s c).
Proof. exact (eq_refl (term4 _132484 c s)). Qed.
Lemma lem7158009 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : term5 _132484 s c.
Proof. exact (EQ_MP (@lem7158008 _132484 s c) (@lem7158007 _132484 c s)). Qed.
Lemma lem7158010 {_132484 : Type'} (s : _132484 -> Prop) (h1 : @FINITE _132484 s) : @FINITE _132484 s.
Proof. exact (h1). Qed.
Lemma lem7158011 {_132484 : Type'} (c : real) (s : _132484 -> Prop) (h1 : @FINITE _132484 s) : (term6 _132484 s c) = (term7 _132484 s c).
Proof. exact (@lem7158009 _132484 s c (@lem7158010 _132484 s h1)). Qed.
Lemma lem7158024 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term8 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7158025 (p : Prop) (q : Prop) (p' : Prop) : term9 p q p'.
Proof. exact (fun q' : Prop => @lem7158024 p q p' q'). Qed.
Lemma lem7158026 (p : Prop) (q : Prop) : term10 p q.
Proof. exact (fun p' : Prop => @lem7158025 p q p'). Qed.
Lemma lem7158027 {_134012 : Type'} (s : _134012 -> Prop) : term11 _134012 s.
Proof. exact (@lem7158026 (@FINITE _134012 s) ((term12 _134012 s) = (term13 _134012 s))). Qed.
Lemma lem7158028 {_134012 : Type'} (s : _134012 -> Prop) (p' : Prop) : term14 _134012 s p'.
Proof. exact (@lem7158027 _134012 s p'). Qed.
Lemma lem7158029 {_134012 : Type'} (s : _134012 -> Prop) (p' : Prop) : (term14 _134012 s p') = (term15 _134012 s p').
Proof. exact (eq_refl (term14 _134012 s p')). Qed.
Lemma lem7158030 {_134012 : Type'} (s : _134012 -> Prop) (p' : Prop) : term15 _134012 s p'.
Proof. exact (EQ_MP (@lem7158029 _134012 s p') (@lem7158028 _134012 s p')). Qed.
Lemma lem7158031 {_134012 : Type'} (s : _134012 -> Prop) (p' : Prop) (q' : Prop) : term16 _134012 s p' q'.
Proof. exact (@lem7158030 _134012 s p' q'). Qed.
Lemma lem7158032 {_134012 : Type'} (s : _134012 -> Prop) (p' : Prop) (q' : Prop) : (term16 _134012 s p' q') = (term17 _134012 s p' q').
Proof. exact (eq_refl (term16 _134012 s p' q')). Qed.
Lemma lem7158033 {_134012 : Type'} (s : _134012 -> Prop) (p' : Prop) (q' : Prop) : term17 _134012 s p' q'.
Proof. exact (EQ_MP (@lem7158032 _134012 s p' q') (@lem7158031 _134012 s p' q')). Qed.
Lemma lem7158034 {_134012 : Type'} (s : _134012 -> Prop) : (@FINITE _134012 s) = (@FINITE _134012 s).
Proof. exact (eq_refl (@FINITE _134012 s)). Qed.
Lemma lem7158035 {_134012 : Type'} (s : _134012 -> Prop) (q' : Prop) : term18 _134012 s q'.
Proof. exact (@lem7158033 _134012 s (@FINITE _134012 s) q'). Qed.
Lemma lem7158036 {_134012 : Type'} (s : _134012 -> Prop) (q' : Prop) : term19 _134012 s q'.
Proof. exact (@lem7158035 _134012 s q' (@lem7158034 _134012 s)). Qed.
Lemma lem7158037 {_134012 : Type'} (s : _134012 -> Prop) (h1 : @FINITE _134012 s) : @FINITE _134012 s.
Proof. exact (h1). Qed.
Lemma lem7158038 {_134012 : Type'} (s : _134012 -> Prop) : (@FINITE _134012 s) = ((@FINITE _134012 s) = True).
Proof. exact (@lem7 (@FINITE _134012 s)). Qed.
Lemma lem7158043 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : term5 _132484 s c.
Proof. exact (fun h0 : @FINITE _132484 s => @lem7158011 _132484 c s h0). Qed.
Lemma lem7158044 {_134012 : Type'} (s : _134012 -> Prop) (c : real) : term5 _134012 s c.
Proof. exact (@lem7158043 _134012 s c). Qed.
Lemma lem7158045 {_134012 : Type'} (s : _134012 -> Prop) : term20 _134012 s.
Proof. exact (@lem7158044 _134012 s term21). Qed.
Lemma lem7158047 {_134012 : Type'} (s : _134012 -> Prop) (h1 : @FINITE _134012 s) : (@FINITE _134012 s) = True.
Proof. exact (EQ_MP (@lem7158038 _134012 s) (@lem7158037 _134012 s h1)). Qed.
Lemma lem7158048 {_134012 : Type'} (s : _134012 -> Prop) (h1 : @FINITE _134012 s) : True = (@FINITE _134012 s).
Proof. exact (SYM (@lem7158047 _134012 s h1)). Qed.
Lemma lem7158049 {_134012 : Type'} (s : _134012 -> Prop) (h1 : @FINITE _134012 s) : @FINITE _134012 s.
Proof. exact (EQ_MP (@lem7158048 _134012 s h1) (@lem0)). Qed.
Lemma lem7158050 {_134012 : Type'} (s : _134012 -> Prop) (h1 : @FINITE _134012 s) : (term13 _134012 s) = (term22 _134012 s).
Proof. exact (@lem7158045 _134012 s (@lem7158049 _134012 s h1)). Qed.
Lemma lem7158052 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem7158002 x) (@lem7158001 x)). Qed.
Lemma lem7158053 {_134012 : Type'} (s : _134012 -> Prop) : (term22 _134012 s) = (term12 _134012 s).
Proof. exact (@lem7158052 (term12 _134012 s)). Qed.
Lemma lem7158054 {_134012 : Type'} (s : _134012 -> Prop) (h1 : @FINITE _134012 s) : (term13 _134012 s) = (term12 _134012 s).
Proof. exact (TRANS (@lem7158050 _134012 s h1) (@lem7158053 _134012 s)). Qed.
Lemma lem7158055 {_134012 : Type'} (s : _134012 -> Prop) : (term23 _134012 s) = (term23 _134012 s).
Proof. exact (eq_refl (term23 _134012 s)). Qed.
Lemma lem7158056 {_134012 : Type'} (s : _134012 -> Prop) (h1 : @FINITE _134012 s) : ((term12 _134012 s) = (term13 _134012 s)) = ((term12 _134012 s) = (term12 _134012 s)).
Proof. exact (MK_COMB (@lem7158055 _134012 s) (@lem7158054 _134012 s h1)). Qed.
Lemma lem7158058 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7158059 (x : real) : (x = x) = True.
Proof. exact (@lem7158058 real x). Qed.
Lemma lem7158060 {_134012 : Type'} (s : _134012 -> Prop) : ((term12 _134012 s) = (term12 _134012 s)) = True.
Proof. exact (@lem7158059 (term12 _134012 s)). Qed.
Lemma lem7158061 {_134012 : Type'} (s : _134012 -> Prop) (h1 : @FINITE _134012 s) : ((term12 _134012 s) = (term13 _134012 s)) = True.
Proof. exact (TRANS (@lem7158056 _134012 s h1) (@lem7158060 _134012 s)). Qed.
Lemma lem7158062 {_134012 : Type'} (s : _134012 -> Prop) : term24 _134012 s.
Proof. exact (fun h0 : @FINITE _134012 s => @lem7158061 _134012 s h0). Qed.
Lemma lem7158063 {_134012 : Type'} (s : _134012 -> Prop) : term25 _134012 s.
Proof. exact (@lem7158036 _134012 s True). Qed.
Lemma lem7158064 {_134012 : Type'} (s : _134012 -> Prop) : (term26 _134012 s) = (term27 _134012 s).
Proof. exact (@lem7158063 _134012 s (@lem7158062 _134012 s)). Qed.
Lemma lem7158066 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7158067 {_134012 : Type'} (s : _134012 -> Prop) : (term27 _134012 s) = True.
Proof. exact (@lem7158066 (@FINITE _134012 s)). Qed.
Lemma lem7158068 {_134012 : Type'} (s : _134012 -> Prop) : (term26 _134012 s) = True.
Proof. exact (TRANS (@lem7158064 _134012 s) (@lem7158067 _134012 s)). Qed.
Lemma lem7158069 {_134012 : Type'} : (term28 _134012) = (term29 _134012).
Proof. exact (fun_ext (fun s : _134012 -> Prop => @lem7158068 _134012 s)). Qed.
Lemma lem7158070 {_134012 : Type'} : (@all (_134012 -> Prop)) = (@all (_134012 -> Prop)).
Proof. exact (eq_refl (@all (_134012 -> Prop))). Qed.
Lemma lem7158071 {_134012 : Type'} : (term30 _134012) = (term31 _134012).
Proof. exact (MK_COMB (@lem7158070 _134012) (@lem7158069 _134012)). Qed.
Lemma lem7158073 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7158074 {_134012 : Type'} (t : Prop) : (term33 _134012 t) = t.
Proof. exact (@lem7158073 (_134012 -> Prop) t). Qed.
Lemma lem7158075 {_134012 : Type'} : (term31 _134012) = True.
Proof. exact (@lem7158074 _134012 True). Qed.
Lemma lem7158076 {_134012 : Type'} : (term30 _134012) = True.
Proof. exact (TRANS (@lem7158071 _134012) (@lem7158075 _134012)). Qed.
Lemma lem7158077 {_134012 : Type'} : True = (term30 _134012).
Proof. exact (SYM (@lem7158076 _134012)). Qed.
Lemma lem7158078 {_134012 : Type'} : term30 _134012.
Proof. exact (EQ_MP (@lem7158077 _134012) (@lem0)). Qed.
