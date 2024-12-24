Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_DIFF_term_abbrevs.
Require Import ITERATE_DIFF_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import REAL_EQ_SUB_LADD_spec.
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
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7067827 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7067829 {_120745 _120749 : Type'} (op : type1400 _120749) : term0 _120745 _120749 op.
Proof. exact (@lem5772504 _120745 _120749 op). Qed.
Lemma lem7067830 {_120745 _120749 : Type'} (op : type1400 _120749) : (term0 _120745 _120749 op) = (term1 _120745 _120749 op).
Proof. exact (eq_refl (term0 _120745 _120749 op)). Qed.
Lemma lem7067831 {_120745 _120749 : Type'} (op : type1400 _120749) : term1 _120745 _120749 op.
Proof. exact (EQ_MP (@lem7067830 _120745 _120749 op) (@lem7067829 _120745 _120749 op)). Qed.
Lemma lem7067832 {_120749 : Type'} (op : type1400 _120749) (h1 : @monoidal _120749 op) : @monoidal _120749 op.
Proof. exact (h1). Qed.
Lemma lem7067833 {_120745 _120749 : Type'} (op : type1400 _120749) (h1 : @monoidal _120749 op) : term2 _120745 _120749 op.
Proof. exact (@lem7067831 _120745 _120749 op (@lem7067832 _120749 op h1)). Qed.
Lemma lem7067834 {_120745 _120749 : Type'} (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term3 _120745 _120749 op f.
Proof. exact (@lem7067833 _120745 _120749 op h1 f). Qed.
Lemma lem7067835 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term3 _120745 _120749 op f) = (term4 _120745 _120749 op f).
Proof. exact (eq_refl (term3 _120745 _120749 op f)). Qed.
Lemma lem7067836 {_120745 _120749 : Type'} (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term4 _120745 _120749 op f.
Proof. exact (EQ_MP (@lem7067835 _120745 _120749 op f) (@lem7067834 _120745 _120749 f op h1)). Qed.
Lemma lem7067837 {_120745 _120749 : Type'} (f : _120745 -> _120749) (s : _120745 -> Prop) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term5 _120745 _120749 op f s.
Proof. exact (@lem7067836 _120745 _120749 f op h1 s). Qed.
Lemma lem7067838 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term5 _120745 _120749 op f s) = (term6 _120745 _120749 op s f).
Proof. exact (eq_refl (term5 _120745 _120749 op f s)). Qed.
Lemma lem7067839 {_120745 _120749 : Type'} (s : _120745 -> Prop) (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term6 _120745 _120749 op s f.
Proof. exact (EQ_MP (@lem7067838 _120745 _120749 op s f) (@lem7067837 _120745 _120749 f s op h1)). Qed.
Lemma lem7067840 {_120745 _120749 : Type'} (s : _120745 -> Prop) (f : _120745 -> _120749) (t : _120745 -> Prop) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term7 _120745 _120749 op s f t.
Proof. exact (@lem7067839 _120745 _120749 s f op h1 t). Qed.
Lemma lem7067841 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term7 _120745 _120749 op s f t) = (term8 _120745 _120749 t op s f).
Proof. exact (eq_refl (term7 _120745 _120749 op s f t)). Qed.
Lemma lem7067842 {_120745 _120749 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term8 _120745 _120749 t op s f.
Proof. exact (EQ_MP (@lem7067841 _120745 _120749 t op s f) (@lem7067840 _120745 _120749 s f t op h1)). Qed.
Lemma lem7067843 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) (h1 : term9 _120745 t s) : term9 _120745 t s.
Proof. exact (h1). Qed.
Lemma lem7067844 {_120745 _120749 : Type'} (f : _120745 -> _120749) (op : type1400 _120749) (t : _120745 -> Prop) (s : _120745 -> Prop) (h1 : @monoidal _120749 op) (h2 : term9 _120745 t s) : (term10 _120745 _120749 s op t f) = (@iterate _120749 _120745 op s f).
Proof. exact (@lem7067842 _120745 _120749 t s f op h1 (@lem7067843 _120745 t s h2)). Qed.
Lemma lem7067845 {_120745 _120749 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term8 _120745 _120749 t op s f.
Proof. exact (fun h0 : term9 _120745 t s => @lem7067844 _120745 _120749 f op t s h1 h0). Qed.
Lemma lem7067846 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : term11 _120745 _120749 t op s f.
Proof. exact (fun h0 : @monoidal _120749 op => @lem7067845 _120745 _120749 t s f op h0). Qed.
Lemma lem7067848 (p : Prop) (q : Prop) (r : Prop) : (term12 p q r) = (term13 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem7067853 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term11 _120745 _120749 t op s f) = (term14 _120745 _120749 t op s f).
Proof. exact (@lem7067848 (@monoidal _120749 op) (term9 _120745 t s) ((term10 _120745 _120749 s op t f) = (@iterate _120749 _120745 op s f))). Qed.
Lemma lem7067855 (x : real) : term15 x.
Proof. exact (@lem1521519 x). Qed.
Lemma lem7067856 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem7067857 (x : real) : term16 x.
Proof. exact (EQ_MP (@lem7067856 x) (@lem7067855 x)). Qed.
Lemma lem7067858 (x : real) (y : real) : term17 x y.
Proof. exact (@lem7067857 x y). Qed.
Lemma lem7067859 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem7067860 (x : real) (y : real) : term18 x y.
Proof. exact (EQ_MP (@lem7067859 x y) (@lem7067858 x y)). Qed.
Lemma lem7067861 (x : real) (y : real) (z : real) : term19 x y z.
Proof. exact (@lem7067860 x y z). Qed.
Lemma lem7067862 (x : real) (z : real) (y : real) : (term19 x y z) = ((x = (real_sub y z)) = ((real_add x z) = y)).
Proof. exact (eq_refl (term19 x y z)). Qed.
Lemma lem7067899 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term20 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7067900 (p : Prop) (q : Prop) (p' : Prop) : term21 p q p'.
Proof. exact (fun q' : Prop => @lem7067899 p q p' q'). Qed.
Lemma lem7067901 (p : Prop) (q : Prop) : term22 p q.
Proof. exact (fun p' : Prop => @lem7067900 p q p'). Qed.
Lemma lem7067902 {_131590 : Type'} (s : _131590 -> Prop) (t : _131590 -> Prop) (f : _131590 -> real) : term23 _131590 s t f.
Proof. exact (@lem7067901 (term9 _131590 t s) ((term24 _131590 s t f) = (term25 _131590 s t f))). Qed.
Lemma lem7067903 {_131590 : Type'} (s : _131590 -> Prop) (t : _131590 -> Prop) (f : _131590 -> real) (p' : Prop) : term26 _131590 s t f p'.
Proof. exact (@lem7067902 _131590 s t f p'). Qed.
Lemma lem7067904 {_131590 : Type'} (s : _131590 -> Prop) (t : _131590 -> Prop) (f : _131590 -> real) (p' : Prop) : (term26 _131590 s t f p') = (term27 _131590 s t f p').
Proof. exact (eq_refl (term26 _131590 s t f p')). Qed.
Lemma lem7067905 {_131590 : Type'} (s : _131590 -> Prop) (t : _131590 -> Prop) (f : _131590 -> real) (p' : Prop) : term27 _131590 s t f p'.
Proof. exact (EQ_MP (@lem7067904 _131590 s t f p') (@lem7067903 _131590 s t f p')). Qed.
Lemma lem7067906 {_131590 : Type'} (s : _131590 -> Prop) (t : _131590 -> Prop) (f : _131590 -> real) (p' : Prop) (q' : Prop) : term28 _131590 s t f p' q'.
Proof. exact (@lem7067905 _131590 s t f p' q'). Qed.
Lemma lem7067907 {_131590 : Type'} (s : _131590 -> Prop) (t : _131590 -> Prop) (f : _131590 -> real) (p' : Prop) (q' : Prop) : (term28 _131590 s t f p' q') = (term29 _131590 s t f p' q').
Proof. exact (eq_refl (term28 _131590 s t f p' q')). Qed.
Lemma lem7067908 {_131590 : Type'} (s : _131590 -> Prop) (t : _131590 -> Prop) (f : _131590 -> real) (p' : Prop) (q' : Prop) : term29 _131590 s t f p' q'.
Proof. exact (EQ_MP (@lem7067907 _131590 s t f p' q') (@lem7067906 _131590 s t f p' q')). Qed.
Lemma lem7067933 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) : (term9 _131590 t s) = (term9 _131590 t s).
Proof. exact (eq_refl (term9 _131590 t s)). Qed.
Lemma lem7067934 {_131590 : Type'} (f : _131590 -> real) (t : _131590 -> Prop) (s : _131590 -> Prop) (q' : Prop) : term30 _131590 f t s q'.
Proof. exact (@lem7067908 _131590 s t f (term9 _131590 t s) q'). Qed.
Lemma lem7067935 {_131590 : Type'} (f : _131590 -> real) (t : _131590 -> Prop) (s : _131590 -> Prop) (q' : Prop) : term31 _131590 f t s q'.
Proof. exact (@lem7067934 _131590 f t s q' (@lem7067933 _131590 t s)). Qed.
Lemma lem7067936 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : term9 _131590 t s.
Proof. exact (h1). Qed.
Lemma lem7067937 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : @SUBSET _131590 t s.
Proof. exact (proj2 (@lem7067936 _131590 t s h1)). Qed.
Lemma lem7067938 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) : (@SUBSET _131590 t s) = ((@SUBSET _131590 t s) = True).
Proof. exact (@lem7 (@SUBSET _131590 t s)). Qed.
Lemma lem7067940 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : @FINITE _131590 s.
Proof. exact (proj1 (@lem7067936 _131590 t s h1)). Qed.
Lemma lem7067941 {_131590 : Type'} (s : _131590 -> Prop) : (@FINITE _131590 s) = ((@FINITE _131590 s) = True).
Proof. exact (@lem7 (@FINITE _131590 s)). Qed.
Lemma lem7067944 (x : real) (z : real) (y : real) : (x = (real_sub y z)) = ((real_add x z) = y).
Proof. exact (EQ_MP (@lem7067862 x z y) (@lem7067861 x y z)). Qed.
Lemma lem7067945 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) (f : _131590 -> real) : ((term24 _131590 s t f) = (term25 _131590 s t f)) = ((term32 _131590 s t f) = (@sum _131590 s f)).
Proof. exact (@lem7067944 (term24 _131590 s t f) (@sum _131590 t f) (@sum _131590 s f)). Qed.
Lemma lem7067965 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7067966 {_131590 : Type'} : (@sum _131590) = (@iterate real _131590 real_add).
Proof. exact (@lem7067965 _131590). Qed.
Lemma lem7067983 {_131590 : Type'} (s : _131590 -> Prop) (t : _131590 -> Prop) : (@DIFF _131590 s t) = (@DIFF _131590 s t).
Proof. exact (eq_refl (@DIFF _131590 s t)). Qed.
Lemma lem7067984 {_131590 : Type'} (s : _131590 -> Prop) (t : _131590 -> Prop) : (term33 _131590 s t) = (term34 _131590 s t).
Proof. exact (MK_COMB (@lem7067966 _131590) (@lem7067983 _131590 s t)). Qed.
Lemma lem7068005 {_131590 : Type'} (f : _131590 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7068006 {_131590 : Type'} (s : _131590 -> Prop) (t : _131590 -> Prop) (f : _131590 -> real) : (term24 _131590 s t f) = (term35 _131590 s t f).
Proof. exact (MK_COMB (@lem7067984 _131590 s t) (@lem7068005 _131590 f)). Qed.
Lemma lem7068029 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7068030 {_131590 : Type'} (s : _131590 -> Prop) (t : _131590 -> Prop) (f : _131590 -> real) : (term36 _131590 s t f) = (term37 _131590 s t f).
Proof. exact (MK_COMB (@lem7068029) (@lem7068006 _131590 s t f)). Qed.
Lemma lem7068062 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7068063 {_131590 : Type'} : (@sum _131590) = (@iterate real _131590 real_add).
Proof. exact (@lem7068062 _131590). Qed.
Lemma lem7068072 {_131590 : Type'} (t : _131590 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7068073 {_131590 : Type'} (t : _131590 -> Prop) : (@sum _131590 t) = (@iterate real _131590 real_add t).
Proof. exact (MK_COMB (@lem7068063 _131590) (@lem7068072 _131590 t)). Qed.
Lemma lem7068086 {_131590 : Type'} (f : _131590 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7068087 {_131590 : Type'} (t : _131590 -> Prop) (f : _131590 -> real) : (@sum _131590 t f) = (@iterate real _131590 real_add t f).
Proof. exact (MK_COMB (@lem7068073 _131590 t) (@lem7068086 _131590 f)). Qed.
Lemma lem7068102 {_131590 : Type'} (s : _131590 -> Prop) (t : _131590 -> Prop) (f : _131590 -> real) : (term32 _131590 s t f) = (term38 _131590 s t f).
Proof. exact (MK_COMB (@lem7068030 _131590 s t f) (@lem7068087 _131590 t f)). Qed.
Lemma lem7068104 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : term14 _120745 _120749 t op s f.
Proof. exact (EQ_MP (@lem7067853 _120745 _120749 t op s f) (@lem7067846 _120745 _120749 t op s f)). Qed.
Lemma lem7068105 {_131590 : Type'} (t : _131590 -> Prop) (op : type1627) (s : _131590 -> Prop) (f : _131590 -> real) : term39 _131590 t op s f.
Proof. exact (@lem7068104 _131590 real t op s f). Qed.
Lemma lem7068106 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) (f : _131590 -> real) : term40 _131590 t s f.
Proof. exact (@lem7068105 _131590 t real_add s f). Qed.
Lemma lem7068116 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7067827) (@lem7067132)). Qed.
Lemma lem7068119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7068120 : term41 = (and True).
Proof. exact (MK_COMB (@lem7068119) (@lem7068116)). Qed.
Lemma lem7068136 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : (@FINITE _131590 s) = True.
Proof. exact (EQ_MP (@lem7067941 _131590 s) (@lem7067940 _131590 t s h1)). Qed.
Lemma lem7068139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7068140 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : (term42 _131590 s) = (and True).
Proof. exact (MK_COMB (@lem7068139) (@lem7068136 _131590 t s h1)). Qed.
Lemma lem7068148 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : (@SUBSET _131590 t s) = True.
Proof. exact (EQ_MP (@lem7067938 _131590 t s) (@lem7067937 _131590 t s h1)). Qed.
Lemma lem7068151 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : (term9 _131590 t s) = (True /\ True).
Proof. exact (MK_COMB (@lem7068140 _131590 t s h1) (@lem7068148 _131590 t s h1)). Qed.
Lemma lem7068153 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7068154 : (True /\ True) = True.
Proof. exact (@lem7068153 True). Qed.
Lemma lem7068157 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : (term9 _131590 t s) = True.
Proof. exact (TRANS (@lem7068151 _131590 t s h1) (@lem7068154)). Qed.
Lemma lem7068158 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : (term43 _131590 t s) = (True /\ True).
Proof. exact (MK_COMB (@lem7068120) (@lem7068157 _131590 t s h1)). Qed.
Lemma lem7068160 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7068161 : (True /\ True) = True.
Proof. exact (@lem7068160 True). Qed.
Lemma lem7068164 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : (term43 _131590 t s) = True.
Proof. exact (TRANS (@lem7068158 _131590 t s h1) (@lem7068161)). Qed.
Lemma lem7068165 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : True = (term43 _131590 t s).
Proof. exact (SYM (@lem7068164 _131590 t s h1)). Qed.
Lemma lem7068166 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : term43 _131590 t s.
Proof. exact (EQ_MP (@lem7068165 _131590 t s h1) (@lem0)). Qed.
Lemma lem7068167 {_131590 : Type'} (f : _131590 -> real) (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : (term38 _131590 s t f) = (@iterate real _131590 real_add s f).
Proof. exact (@lem7068106 _131590 t s f (@lem7068166 _131590 t s h1)). Qed.
Lemma lem7068182 {_131590 : Type'} (f : _131590 -> real) (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : (term32 _131590 s t f) = (@iterate real _131590 real_add s f).
Proof. exact (TRANS (@lem7068102 _131590 s t f) (@lem7068167 _131590 f t s h1)). Qed.
Lemma lem7068183 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7068184 {_131590 : Type'} (f : _131590 -> real) (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : (term44 _131590 s t f) = (term45 _131590 s f).
Proof. exact (MK_COMB (@lem7068183) (@lem7068182 _131590 f t s h1)). Qed.
Lemma lem7068208 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7068209 {_131590 : Type'} : (@sum _131590) = (@iterate real _131590 real_add).
Proof. exact (@lem7068208 _131590). Qed.
Lemma lem7068218 {_131590 : Type'} (s : _131590 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7068219 {_131590 : Type'} (s : _131590 -> Prop) : (@sum _131590 s) = (@iterate real _131590 real_add s).
Proof. exact (MK_COMB (@lem7068209 _131590) (@lem7068218 _131590 s)). Qed.
Lemma lem7068232 {_131590 : Type'} (f : _131590 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7068233 {_131590 : Type'} (s : _131590 -> Prop) (f : _131590 -> real) : (@sum _131590 s f) = (@iterate real _131590 real_add s f).
Proof. exact (MK_COMB (@lem7068219 _131590 s) (@lem7068232 _131590 f)). Qed.
Lemma lem7068248 {_131590 : Type'} (f : _131590 -> real) (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : ((term32 _131590 s t f) = (@sum _131590 s f)) = ((@iterate real _131590 real_add s f) = (@iterate real _131590 real_add s f)).
Proof. exact (MK_COMB (@lem7068184 _131590 f t s h1) (@lem7068233 _131590 s f)). Qed.
Lemma lem7068250 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7068251 (x : real) : (x = x) = True.
Proof. exact (@lem7068250 real x). Qed.
Lemma lem7068252 {_131590 : Type'} (s : _131590 -> Prop) (f : _131590 -> real) : ((@iterate real _131590 real_add s f) = (@iterate real _131590 real_add s f)) = True.
Proof. exact (@lem7068251 (@iterate real _131590 real_add s f)). Qed.
Lemma lem7068255 {_131590 : Type'} (f : _131590 -> real) (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : ((term32 _131590 s t f) = (@sum _131590 s f)) = True.
Proof. exact (TRANS (@lem7068248 _131590 f t s h1) (@lem7068252 _131590 s f)). Qed.
Lemma lem7068256 {_131590 : Type'} (f : _131590 -> real) (t : _131590 -> Prop) (s : _131590 -> Prop) (h1 : term9 _131590 t s) : ((term24 _131590 s t f) = (term25 _131590 s t f)) = True.
Proof. exact (TRANS (@lem7067945 _131590 t s f) (@lem7068255 _131590 f t s h1)). Qed.
Lemma lem7068257 {_131590 : Type'} (s : _131590 -> Prop) (t : _131590 -> Prop) (f : _131590 -> real) : term46 _131590 s t f.
Proof. exact (fun h0 : term9 _131590 t s => @lem7068256 _131590 f t s h0). Qed.
Lemma lem7068258 {_131590 : Type'} (f : _131590 -> real) (t : _131590 -> Prop) (s : _131590 -> Prop) : term47 _131590 f t s.
Proof. exact (@lem7067935 _131590 f t s True). Qed.
Lemma lem7068259 {_131590 : Type'} (f : _131590 -> real) (t : _131590 -> Prop) (s : _131590 -> Prop) : (term48 _131590 s t f) = (term49 _131590 t s).
Proof. exact (@lem7068258 _131590 f t s (@lem7068257 _131590 s t f)). Qed.
Lemma lem7068261 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7068262 {_131590 : Type'} (t : _131590 -> Prop) (s : _131590 -> Prop) : (term49 _131590 t s) = True.
Proof. exact (@lem7068261 (term9 _131590 t s)). Qed.
Lemma lem7068265 {_131590 : Type'} (s : _131590 -> Prop) (t : _131590 -> Prop) (f : _131590 -> real) : (term48 _131590 s t f) = True.
Proof. exact (TRANS (@lem7068259 _131590 f t s) (@lem7068262 _131590 t s)). Qed.
Lemma lem7068266 {_131590 : Type'} (s : _131590 -> Prop) (f : _131590 -> real) : (term50 _131590 s f) = (term51 _131590).
Proof. exact (fun_ext (fun t : _131590 -> Prop => @lem7068265 _131590 s t f)). Qed.
Lemma lem7068271 {_131590 : Type'} : (@all (_131590 -> Prop)) = (@all (_131590 -> Prop)).
Proof. exact (eq_refl (@all (_131590 -> Prop))). Qed.
Lemma lem7068272 {_131590 : Type'} (s : _131590 -> Prop) (f : _131590 -> real) : (term52 _131590 s f) = (term53 _131590).
Proof. exact (MK_COMB (@lem7068271 _131590) (@lem7068266 _131590 s f)). Qed.
Lemma lem7068274 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7068275 {_131590 : Type'} (t : Prop) : (term55 _131590 t) = t.
Proof. exact (@lem7068274 (_131590 -> Prop) t). Qed.
Lemma lem7068276 {_131590 : Type'} : (term53 _131590) = True.
Proof. exact (@lem7068275 _131590 True). Qed.
Lemma lem7068279 {_131590 : Type'} (s : _131590 -> Prop) (f : _131590 -> real) : (term52 _131590 s f) = True.
Proof. exact (TRANS (@lem7068272 _131590 s f) (@lem7068276 _131590)). Qed.
Lemma lem7068280 {_131590 : Type'} (f : _131590 -> real) : (term56 _131590 f) = (term51 _131590).
Proof. exact (fun_ext (fun s : _131590 -> Prop => @lem7068279 _131590 s f)). Qed.
Lemma lem7068285 {_131590 : Type'} : (@all (_131590 -> Prop)) = (@all (_131590 -> Prop)).
Proof. exact (eq_refl (@all (_131590 -> Prop))). Qed.
Lemma lem7068286 {_131590 : Type'} (f : _131590 -> real) : (term57 _131590 f) = (term53 _131590).
Proof. exact (MK_COMB (@lem7068285 _131590) (@lem7068280 _131590 f)). Qed.
Lemma lem7068288 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7068289 {_131590 : Type'} (t : Prop) : (term55 _131590 t) = t.
Proof. exact (@lem7068288 (_131590 -> Prop) t). Qed.
Lemma lem7068290 {_131590 : Type'} : (term53 _131590) = True.
Proof. exact (@lem7068289 _131590 True). Qed.
Lemma lem7068293 {_131590 : Type'} (f : _131590 -> real) : (term57 _131590 f) = True.
Proof. exact (TRANS (@lem7068286 _131590 f) (@lem7068290 _131590)). Qed.
Lemma lem7068294 {_131590 : Type'} : (term58 _131590) = (term59 _131590).
Proof. exact (fun_ext (fun f : _131590 -> real => @lem7068293 _131590 f)). Qed.
Lemma lem7068299 {_131590 : Type'} : (@all (_131590 -> real)) = (@all (_131590 -> real)).
Proof. exact (eq_refl (@all (_131590 -> real))). Qed.
Lemma lem7068300 {_131590 : Type'} : (term60 _131590) = (term61 _131590).
Proof. exact (MK_COMB (@lem7068299 _131590) (@lem7068294 _131590)). Qed.
Lemma lem7068302 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7068303 {_131590 : Type'} (t : Prop) : (term62 _131590 t) = t.
Proof. exact (@lem7068302 (_131590 -> real) t). Qed.
Lemma lem7068304 {_131590 : Type'} : (term61 _131590) = True.
Proof. exact (@lem7068303 _131590 True). Qed.
Lemma lem7068307 {_131590 : Type'} : (term60 _131590) = True.
Proof. exact (TRANS (@lem7068300 _131590) (@lem7068304 _131590)). Qed.
Lemma lem7068308 {_131590 : Type'} : True = (term60 _131590).
Proof. exact (SYM (@lem7068307 _131590)). Qed.
Lemma lem7068309 {_131590 : Type'} : term60 _131590.
Proof. exact (EQ_MP (@lem7068308 _131590) (@lem0)). Qed.
