Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_MULTICOUNT_GEN_term_abbrevs.
Require Import CARD_EQ_SUM_spec.
Require Import CONJ_ASSOC_spec.
Require Import EQ_TRANS_spec.
Require Import FINITE_RESTRICT_spec.
Require Import REAL_MUL_RID_spec.
Require Import SUM_CONST_spec.
Require Import SUM_EQ_spec.
Require Import SUM_SUM_RESTRICT_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7158079 (x : real) : term0 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem7158080 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem7158082 {_132349 : Type'} (h1 : term2 _132349) : term2 _132349.
Proof. exact (h1). Qed.
Lemma lem7158083 {_132349 : Type'} (f : _132349 -> real) (h1 : term2 _132349) : term3 _132349 f.
Proof. exact (@lem7158082 _132349 h1 f). Qed.
Lemma lem7158084 {_132349 : Type'} (f : _132349 -> real) : (term3 _132349 f) = (term4 _132349 f).
Proof. exact (eq_refl (term3 _132349 f)). Qed.
Lemma lem7158085 {_132349 : Type'} (f : _132349 -> real) (h1 : term2 _132349) : term4 _132349 f.
Proof. exact (EQ_MP (@lem7158084 _132349 f) (@lem7158083 _132349 f h1)). Qed.
Lemma lem7158086 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (h1 : term2 _132349) : term5 _132349 f g.
Proof. exact (@lem7158085 _132349 f h1 g). Qed.
Lemma lem7158087 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term5 _132349 f g) = (term6 _132349 f g).
Proof. exact (eq_refl (term5 _132349 f g)). Qed.
Lemma lem7158088 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (h1 : term2 _132349) : term6 _132349 f g.
Proof. exact (EQ_MP (@lem7158087 _132349 f g) (@lem7158086 _132349 f g h1)). Qed.
Lemma lem7158089 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (s : _132349 -> Prop) (h1 : term2 _132349) : term7 _132349 f g s.
Proof. exact (@lem7158088 _132349 f g h1 s). Qed.
Lemma lem7158090 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term7 _132349 f g s) = (term8 _132349 f s g).
Proof. exact (eq_refl (term7 _132349 f g s)). Qed.
Lemma lem7158091 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) (h1 : term2 _132349) : term8 _132349 f s g.
Proof. exact (EQ_MP (@lem7158090 _132349 f s g) (@lem7158089 _132349 f g s h1)). Qed.
Lemma lem7158092 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term9 _132349 s f g) : term9 _132349 s f g.
Proof. exact (h1). Qed.
Lemma lem7158093 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term9 _132349 s f g) (h2 : term2 _132349) : (@sum _132349 s f) = (@sum _132349 s g).
Proof. exact (@lem7158091 _132349 f s g h2 (@lem7158092 _132349 s f g h1)). Qed.
Lemma lem7158094 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term9 _132349 s f g) : term10 _132349 f s g.
Proof. exact (fun h0 : term2 _132349 => @lem7158093 _132349 s f g h1 h0). Qed.
Lemma lem7158095 {_132349 : Type'} (h1 : term2 _132349) : term2 _132349.
Proof. exact (h1). Qed.
Lemma lem7158096 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term9 _132349 s f g) (h2 : term2 _132349) : (@sum _132349 s f) = (@sum _132349 s g).
Proof. exact (@lem7158094 _132349 s f g h1 (@lem7158095 _132349 h2)). Qed.
Lemma lem7158097 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) (h1 : term2 _132349) : term8 _132349 f s g.
Proof. exact (fun h0 : term9 _132349 s f g => @lem7158096 _132349 s f g h0 h1). Qed.
Lemma lem7158098 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (h1 : term2 _132349) : term11 _132349 f s.
Proof. exact (fun g : _132349 -> real => @lem7158097 _132349 f s g h1). Qed.
Lemma lem7158099 {_132349 : Type'} (f : _132349 -> real) (h1 : term2 _132349) : term12 _132349 f.
Proof. exact (fun s : _132349 -> Prop => @lem7158098 _132349 f s h1). Qed.
Lemma lem7158100 {_132349 : Type'} (h1 : term2 _132349) : term13 _132349.
Proof. exact (fun f : _132349 -> real => @lem7158099 _132349 f h1). Qed.
Lemma lem7158101 {_132349 : Type'} : term14 _132349.
Proof. exact (fun h0 : term2 _132349 => @lem7158100 _132349 h0). Qed.
Lemma lem7158102 {_132349 : Type'} : term13 _132349.
Proof. exact (@lem7158101 _132349 (@lem7081239 _132349)). Qed.
Lemma lem7158103 {_132349 : Type'} (f : _132349 -> real) : term15 _132349 f.
Proof. exact (@lem7158102 _132349 f). Qed.
Lemma lem7158104 {_132349 : Type'} (f : _132349 -> real) : (term15 _132349 f) = (term12 _132349 f).
Proof. exact (eq_refl (term15 _132349 f)). Qed.
Lemma lem7158105 {_132349 : Type'} (f : _132349 -> real) : term12 _132349 f.
Proof. exact (EQ_MP (@lem7158104 _132349 f) (@lem7158103 _132349 f)). Qed.
Lemma lem7158106 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : term16 _132349 f s.
Proof. exact (@lem7158105 _132349 f s). Qed.
Lemma lem7158107 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : (term16 _132349 f s) = (term11 _132349 f s).
Proof. exact (eq_refl (term16 _132349 f s)). Qed.
Lemma lem7158108 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : term11 _132349 f s.
Proof. exact (EQ_MP (@lem7158107 _132349 f s) (@lem7158106 _132349 f s)). Qed.
Lemma lem7158109 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : term17 _132349 f s g.
Proof. exact (@lem7158108 _132349 f s g). Qed.
Lemma lem7158110 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term17 _132349 f s g) = (term8 _132349 f s g).
Proof. exact (eq_refl (term17 _132349 f s g)). Qed.
Lemma lem7158112 {_132349 : Type'} (h1 : term2 _132349) : term2 _132349.
Proof. exact (h1). Qed.
Lemma lem7158113 {_132349 : Type'} (f : _132349 -> real) (h1 : term2 _132349) : term3 _132349 f.
Proof. exact (@lem7158112 _132349 h1 f). Qed.
Lemma lem7158114 {_132349 : Type'} (f : _132349 -> real) : (term3 _132349 f) = (term4 _132349 f).
Proof. exact (eq_refl (term3 _132349 f)). Qed.
Lemma lem7158115 {_132349 : Type'} (f : _132349 -> real) (h1 : term2 _132349) : term4 _132349 f.
Proof. exact (EQ_MP (@lem7158114 _132349 f) (@lem7158113 _132349 f h1)). Qed.
Lemma lem7158116 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (h1 : term2 _132349) : term5 _132349 f g.
Proof. exact (@lem7158115 _132349 f h1 g). Qed.
Lemma lem7158117 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term5 _132349 f g) = (term6 _132349 f g).
Proof. exact (eq_refl (term5 _132349 f g)). Qed.
Lemma lem7158118 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (h1 : term2 _132349) : term6 _132349 f g.
Proof. exact (EQ_MP (@lem7158117 _132349 f g) (@lem7158116 _132349 f g h1)). Qed.
Lemma lem7158119 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (s : _132349 -> Prop) (h1 : term2 _132349) : term7 _132349 f g s.
Proof. exact (@lem7158118 _132349 f g h1 s). Qed.
Lemma lem7158120 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term7 _132349 f g s) = (term8 _132349 f s g).
Proof. exact (eq_refl (term7 _132349 f g s)). Qed.
Lemma lem7158121 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) (h1 : term2 _132349) : term8 _132349 f s g.
Proof. exact (EQ_MP (@lem7158120 _132349 f s g) (@lem7158119 _132349 f g s h1)). Qed.
Lemma lem7158122 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term9 _132349 s f g) : term9 _132349 s f g.
Proof. exact (h1). Qed.
Lemma lem7158123 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term9 _132349 s f g) (h2 : term2 _132349) : (@sum _132349 s f) = (@sum _132349 s g).
Proof. exact (@lem7158121 _132349 f s g h2 (@lem7158122 _132349 s f g h1)). Qed.
Lemma lem7158124 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term9 _132349 s f g) : term10 _132349 f s g.
Proof. exact (fun h0 : term2 _132349 => @lem7158123 _132349 s f g h1 h0). Qed.
Lemma lem7158125 {_132349 : Type'} (h1 : term2 _132349) : term2 _132349.
Proof. exact (h1). Qed.
Lemma lem7158126 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term9 _132349 s f g) (h2 : term2 _132349) : (@sum _132349 s f) = (@sum _132349 s g).
Proof. exact (@lem7158124 _132349 s f g h1 (@lem7158125 _132349 h2)). Qed.
Lemma lem7158127 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) (h1 : term2 _132349) : term8 _132349 f s g.
Proof. exact (fun h0 : term9 _132349 s f g => @lem7158126 _132349 s f g h0 h1). Qed.
Lemma lem7158128 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (h1 : term2 _132349) : term11 _132349 f s.
Proof. exact (fun g : _132349 -> real => @lem7158127 _132349 f s g h1). Qed.
Lemma lem7158129 {_132349 : Type'} (f : _132349 -> real) (h1 : term2 _132349) : term12 _132349 f.
Proof. exact (fun s : _132349 -> Prop => @lem7158128 _132349 f s h1). Qed.
Lemma lem7158130 {_132349 : Type'} (h1 : term2 _132349) : term13 _132349.
Proof. exact (fun f : _132349 -> real => @lem7158129 _132349 f h1). Qed.
Lemma lem7158131 {_132349 : Type'} : term14 _132349.
Proof. exact (fun h0 : term2 _132349 => @lem7158130 _132349 h0). Qed.
Lemma lem7158132 {_132349 : Type'} : term13 _132349.
Proof. exact (@lem7158131 _132349 (@lem7081239 _132349)). Qed.
Lemma lem7158133 {_132349 : Type'} (f : _132349 -> real) : term15 _132349 f.
Proof. exact (@lem7158132 _132349 f). Qed.
Lemma lem7158134 {_132349 : Type'} (f : _132349 -> real) : (term15 _132349 f) = (term12 _132349 f).
Proof. exact (eq_refl (term15 _132349 f)). Qed.
Lemma lem7158135 {_132349 : Type'} (f : _132349 -> real) : term12 _132349 f.
Proof. exact (EQ_MP (@lem7158134 _132349 f) (@lem7158133 _132349 f)). Qed.
Lemma lem7158136 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : term16 _132349 f s.
Proof. exact (@lem7158135 _132349 f s). Qed.
Lemma lem7158137 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : (term16 _132349 f s) = (term11 _132349 f s).
Proof. exact (eq_refl (term16 _132349 f s)). Qed.
Lemma lem7158138 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : term11 _132349 f s.
Proof. exact (EQ_MP (@lem7158137 _132349 f s) (@lem7158136 _132349 f s)). Qed.
Lemma lem7158139 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : term17 _132349 f s g.
Proof. exact (@lem7158138 _132349 f s g). Qed.
Lemma lem7158140 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term17 _132349 f s g) = (term8 _132349 f s g).
Proof. exact (eq_refl (term17 _132349 f s g)). Qed.
Lemma lem7158142 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem7158143 {A : Type'} (x : A) (h1 : term18 A) : term19 A x.
Proof. exact (@lem7158142 A h1 x). Qed.
Lemma lem7158144 {A : Type'} (x : A) : (term19 A x) = (term20 A x).
Proof. exact (eq_refl (term19 A x)). Qed.
Lemma lem7158145 {A : Type'} (x : A) (h1 : term18 A) : term20 A x.
Proof. exact (EQ_MP (@lem7158144 A x) (@lem7158143 A x h1)). Qed.
Lemma lem7158146 {A : Type'} (x : A) (y : A) (h1 : term18 A) : term21 A x y.
Proof. exact (@lem7158145 A x h1 y). Qed.
Lemma lem7158147 {A : Type'} (y : A) (x : A) : (term21 A x y) = (term22 A y x).
Proof. exact (eq_refl (term21 A x y)). Qed.
Lemma lem7158148 {A : Type'} (y : A) (x : A) (h1 : term18 A) : term22 A y x.
Proof. exact (EQ_MP (@lem7158147 A y x) (@lem7158146 A x y h1)). Qed.
Lemma lem7158149 {A : Type'} (y : A) (x : A) (z : A) (h1 : term18 A) : term23 A y x z.
Proof. exact (@lem7158148 A y x h1 z). Qed.
Lemma lem7158150 {A : Type'} (y : A) (x : A) (z : A) : (term23 A y x z) = (term24 A y x z).
Proof. exact (eq_refl (term23 A y x z)). Qed.
Lemma lem7158151 {A : Type'} (y : A) (x : A) (z : A) (h1 : term18 A) : term24 A y x z.
Proof. exact (EQ_MP (@lem7158150 A y x z) (@lem7158149 A y x z h1)). Qed.
Lemma lem7158152 {A : Type'} (x : A) (y : A) (z : A) (h1 : term25 A x y z) : term25 A x y z.
Proof. exact (h1). Qed.
Lemma lem7158153 {A : Type'} (x : A) (y : A) (z : A) (h1 : term18 A) (h2 : term25 A x y z) : x = z.
Proof. exact (@lem7158151 A y x z h1 (@lem7158152 A x y z h2)). Qed.
Lemma lem7158154 {A : Type'} (x : A) (y : A) (z : A) (h1 : term25 A x y z) : term26 A x z.
Proof. exact (fun h0 : term18 A => @lem7158153 A x y z h0 h1). Qed.
Lemma lem7158155 {A : Type'} (x : A) (z : A) (h1 : term27 A x z) : term27 A x z.
Proof. exact (h1). Qed.
Lemma lem7158156 {A : Type'} (x : A) (z : A) (h1 : term27 A x z) : term26 A x z.
Proof. exact (ex_elim (@lem7158155 A x z h1) (fun y : A => fun h0 : term28 A x z y => @lem7158154 A x y z h0)). Qed.
Lemma lem7158157 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem7158158 {A : Type'} (x : A) (z : A) (h1 : term18 A) (h2 : term27 A x z) : x = z.
Proof. exact (@lem7158156 A x z h2 (@lem7158157 A h1)). Qed.
Lemma lem7158159 {A : Type'} (x : A) (z : A) (h1 : term18 A) : term29 A x z.
Proof. exact (fun h0 : term27 A x z => @lem7158158 A x z h1 h0). Qed.
Lemma lem7158160 {A : Type'} (x : A) (h1 : term18 A) : term30 A x.
Proof. exact (fun z : A => @lem7158159 A x z h1). Qed.
Lemma lem7158161 {A : Type'} (h1 : term18 A) : term31 A.
Proof. exact (fun x : A => @lem7158160 A x h1). Qed.
Lemma lem7158162 {A : Type'} : term32 A.
Proof. exact (fun h0 : term18 A => @lem7158161 A h0). Qed.
Lemma lem7158163 {A : Type'} : term31 A.
Proof. exact (@lem7158162 A (@lem403 A)). Qed.
Lemma lem7158164 {A : Type'} (x : A) : term33 A x.
Proof. exact (@lem7158163 A x). Qed.
Lemma lem7158165 {A : Type'} (x : A) : (term33 A x) = (term30 A x).
Proof. exact (eq_refl (term33 A x)). Qed.
Lemma lem7158166 {A : Type'} (x : A) : term30 A x.
Proof. exact (EQ_MP (@lem7158165 A x) (@lem7158164 A x)). Qed.
Lemma lem7158167 {A : Type'} (x : A) (z : A) : term34 A x z.
Proof. exact (@lem7158166 A x z). Qed.
Lemma lem7158168 {A : Type'} (x : A) (z : A) : (term34 A x z) = (term29 A x z).
Proof. exact (eq_refl (term34 A x z)). Qed.
Lemma lem7158170 (t1 : Prop) : term35 t1.
Proof. exact (@lem512 t1). Qed.
Lemma lem7158171 (t1 : Prop) : (term35 t1) = (term36 t1).
Proof. exact (eq_refl (term35 t1)). Qed.
Lemma lem7158172 (t1 : Prop) : term36 t1.
Proof. exact (EQ_MP (@lem7158171 t1) (@lem7158170 t1)). Qed.
Lemma lem7158173 (t1 : Prop) (t2 : Prop) : term37 t1 t2.
Proof. exact (@lem7158172 t1 t2). Qed.
Lemma lem7158174 (t1 : Prop) (t2 : Prop) : (term37 t1 t2) = (term38 t1 t2).
Proof. exact (eq_refl (term37 t1 t2)). Qed.
Lemma lem7158175 (t1 : Prop) (t2 : Prop) : term38 t1 t2.
Proof. exact (EQ_MP (@lem7158174 t1 t2) (@lem7158173 t1 t2)). Qed.
Lemma lem7158176 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term39 t1 t2 t3.
Proof. exact (@lem7158175 t1 t2 t3). Qed.
Lemma lem7158177 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term39 t1 t2 t3) = ((term40 t1 t2 t3) = (term41 t1 t2 t3)).
Proof. exact (eq_refl (term39 t1 t2 t3)). Qed.
Lemma lem7158182 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term40 t1 t2 t3) = (term41 t1 t2 t3).
Proof. exact (EQ_MP (@lem7158177 t1 t2 t3) (@lem7158176 t1 t2 t3)). Qed.
Lemma lem7158183 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) : (term42 A B t s R k) = (term43 A B t s R k).
Proof. exact (@lem7158182 (@FINITE A s) (@FINITE B t) (term44 A B t s R k)). Qed.
Lemma lem7158202 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7158203 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) : (term45 A B t s R k) = (term46 A B t s R k).
Proof. exact (MK_COMB (@lem7158202) (@lem7158183 A B t s R k)). Qed.
Lemma lem7158212 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : ((term47 A B s t R) = (term48 B t k)) = ((term47 A B s t R) = (term48 B t k)).
Proof. exact (eq_refl ((term47 A B s t R) = (term48 B t k))). Qed.
Lemma lem7158213 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : (term49 A B s R t k) = (term50 A B s R t k).
Proof. exact (MK_COMB (@lem7158203 A B t s R k) (@lem7158212 A B s R t k)). Qed.
Lemma lem7158216 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : (term50 A B s R t k) = (term49 A B s R t k).
Proof. exact (SYM (@lem7158213 A B s R t k)). Qed.
Lemma lem7158217 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term43 A B t s R k) : term43 A B t s R k.
Proof. exact (h1). Qed.
Lemma lem7158218 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term44 A B t s R k) : term44 A B t s R k.
Proof. exact (h1). Qed.
Lemma lem7158219 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : term51 A B s t.
Proof. exact (h1). Qed.
Lemma lem7158221 {A : Type'} (x : A) (z : A) : term29 A x z.
Proof. exact (EQ_MP (@lem7158168 A x z) (@lem7158167 A x z)). Qed.
Lemma lem7158222 (x : real) (z : real) : term52 x z.
Proof. exact (@lem7158221 real x z). Qed.
Lemma lem7158223 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : term53 A B s R t k.
Proof. exact (@lem7158222 (term47 A B s t R) (term48 B t k)). Qed.
Lemma lem7158225 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : term8 _132349 f s g.
Proof. exact (EQ_MP (@lem7158140 _132349 f s g) (@lem7158139 _132349 f s g)). Qed.
Lemma lem7158226 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term8 A f s g.
Proof. exact (@lem7158225 A f s g). Qed.
Lemma lem7158227 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : term54 A B s t R.
Proof. exact (@lem7158226 A (term55 A B t R) s (term56 A B t R)). Qed.
Lemma lem7158248 {A B : Type'} (f : A -> B) (y : A) : (term57 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7158249 {A : Type'} (f : A -> real) (y : A) : (term58 A f y) = (f y).
Proof. exact (@lem7158248 A real f y). Qed.
Lemma lem7158250 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term59 A B t R x) = (term60 A B t R x).
Proof. exact (@lem7158249 A (term55 A B t R) x). Qed.
Lemma lem7158251 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (i : A) : (term60 A B t R i) = (term61 A B t R i).
Proof. exact (eq_refl (term60 A B t R i)). Qed.
Lemma lem7158252 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term62 A B t R) = (term55 A B t R).
Proof. exact (fun_ext (fun i : A => @lem7158251 A B t R i)). Qed.
Lemma lem7158253 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7158254 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term59 A B t R x) = (term60 A B t R x).
Proof. exact (MK_COMB (@lem7158252 A B t R) (@lem7158253 A x)). Qed.
Lemma lem7158255 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7158256 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term63 A B t R x) = (term64 A B t R x).
Proof. exact (MK_COMB (@lem7158255) (@lem7158254 A B t R x)). Qed.
Lemma lem7158257 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term60 A B t R x) = (term61 A B t R x).
Proof. exact (eq_refl (term60 A B t R x)). Qed.
Lemma lem7158258 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term59 A B t R x) = (term60 A B t R x)) = ((term60 A B t R x) = (term61 A B t R x)).
Proof. exact (MK_COMB (@lem7158256 A B t R x) (@lem7158257 A B t R x)). Qed.
Lemma lem7158259 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term60 A B t R x) = (term61 A B t R x).
Proof. exact (EQ_MP (@lem7158258 A B t R x) (@lem7158250 A B t R x)). Qed.
Lemma lem7158266 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7158267 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term64 A B t R x) = (term65 A B t R x).
Proof. exact (MK_COMB (@lem7158266) (@lem7158259 A B t R x)). Qed.
Lemma lem7158269 {A B : Type'} (f : A -> B) (y : A) : (term57 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7158270 {A : Type'} (f : A -> real) (y : A) : (term58 A f y) = (f y).
Proof. exact (@lem7158269 A real f y). Qed.
Lemma lem7158271 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term66 A B t R x) = (term67 A B t R x).
Proof. exact (@lem7158270 A (term56 A B t R) x). Qed.
Lemma lem7158272 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (i : A) : (term67 A B t R i) = (term68 A B t R i).
Proof. exact (eq_refl (term67 A B t R i)). Qed.
Lemma lem7158273 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term69 A B t R) = (term56 A B t R).
Proof. exact (fun_ext (fun i : A => @lem7158272 A B t R i)). Qed.
Lemma lem7158274 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7158275 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term66 A B t R x) = (term67 A B t R x).
Proof. exact (MK_COMB (@lem7158273 A B t R) (@lem7158274 A x)). Qed.
Lemma lem7158276 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7158277 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term70 A B t R x) = (term71 A B t R x).
Proof. exact (MK_COMB (@lem7158276) (@lem7158275 A B t R x)). Qed.
Lemma lem7158278 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term67 A B t R x) = (term68 A B t R x).
Proof. exact (eq_refl (term67 A B t R x)). Qed.
Lemma lem7158279 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term66 A B t R x) = (term67 A B t R x)) = ((term67 A B t R x) = (term68 A B t R x)).
Proof. exact (MK_COMB (@lem7158277 A B t R x) (@lem7158278 A B t R x)). Qed.
Lemma lem7158280 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term67 A B t R x) = (term68 A B t R x).
Proof. exact (EQ_MP (@lem7158279 A B t R x) (@lem7158271 A B t R x)). Qed.
Lemma lem7158287 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term60 A B t R x) = (term67 A B t R x)) = ((term61 A B t R x) = (term68 A B t R x)).
Proof. exact (MK_COMB (@lem7158267 A B t R x) (@lem7158280 A B t R x)). Qed.
Lemma lem7158290 {A : Type'} (x : A) (s : A -> Prop) : (term72 A x s) = (term72 A x s).
Proof. exact (eq_refl (term72 A x s)). Qed.
Lemma lem7158291 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term73 A B s t R x) = (term74 A B s t R x).
Proof. exact (MK_COMB (@lem7158290 A x s) (@lem7158287 A B t R x)). Qed.
Lemma lem7158294 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term75 A B s t R) = (term76 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem7158291 A B s t R x)). Qed.
Lemma lem7158295 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7158296 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term77 A B s t R) = (term78 A B s t R).
Proof. exact (MK_COMB (@lem7158295 A) (@lem7158294 A B s t R)). Qed.
Lemma lem7158301 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term78 A B s t R) = (term77 A B s t R).
Proof. exact (SYM (@lem7158296 A B s t R)). Qed.
Lemma lem7158303 {A : Type'} (s : A -> Prop) : term79 A s.
Proof. exact (@lem3603906 A s). Qed.
Lemma lem7158304 {A : Type'} (s : A -> Prop) : (term79 A s) = (term80 A s).
Proof. exact (eq_refl (term79 A s)). Qed.
Lemma lem7158305 {A : Type'} (s : A -> Prop) : term80 A s.
Proof. exact (EQ_MP (@lem7158304 A s) (@lem7158303 A s)). Qed.
Lemma lem7158306 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term81 A s P.
Proof. exact (@lem7158305 A s P). Qed.
Lemma lem7158307 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term81 A s P) = (term82 A s P).
Proof. exact (eq_refl (term81 A s P)). Qed.
Lemma lem7158308 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term82 A s P.
Proof. exact (EQ_MP (@lem7158307 A s P) (@lem7158306 A s P)). Qed.
Lemma lem7158309 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7158310 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term83 A s P.
Proof. exact (@lem7158308 A s P (@lem7158309 A s h1)). Qed.
Lemma lem7158311 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term83 A s P) = ((term83 A s P) = True).
Proof. exact (@lem7 (term83 A s P)). Qed.
Lemma lem7158312 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term83 A s P) = True.
Proof. exact (EQ_MP (@lem7158311 A s P) (@lem7158310 A P s h1)). Qed.
Lemma lem7158318 {_134012 : Type'} (s : _134012 -> Prop) : term84 _134012 s.
Proof. exact (@lem7158078 _134012 s). Qed.
Lemma lem7158319 {_134012 : Type'} (s : _134012 -> Prop) : (term84 _134012 s) = (term85 _134012 s).
Proof. exact (eq_refl (term84 _134012 s)). Qed.
Lemma lem7158320 {_134012 : Type'} (s : _134012 -> Prop) : term85 _134012 s.
Proof. exact (EQ_MP (@lem7158319 _134012 s) (@lem7158318 _134012 s)). Qed.
Lemma lem7158321 {_134012 : Type'} (s : _134012 -> Prop) (h1 : @FINITE _134012 s) : @FINITE _134012 s.
Proof. exact (h1). Qed.
Lemma lem7158322 {_134012 : Type'} (s : _134012 -> Prop) (h1 : @FINITE _134012 s) : (term86 _134012 s) = (term87 _134012 s).
Proof. exact (@lem7158320 _134012 s (@lem7158321 _134012 s h1)). Qed.
Lemma lem7158328 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : @FINITE B t.
Proof. exact (proj2 (@lem7158219 A B s t h1)). Qed.
Lemma lem7158329 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem7158349 {_134012 : Type'} (s : _134012 -> Prop) : term85 _134012 s.
Proof. exact (fun h0 : @FINITE _134012 s => @lem7158322 _134012 s h0). Qed.
Lemma lem7158350 {B : Type'} (s : B -> Prop) : term85 B s.
Proof. exact (@lem7158349 B s). Qed.
Lemma lem7158351 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : term88 A B t R x.
Proof. exact (@lem7158350 B (term89 A B t R x)). Qed.
Lemma lem7158353 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term90 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem7158312 A P s h0). Qed.
Lemma lem7158354 {B : Type'} (s : B -> Prop) (P : B -> Prop) : term90 B s P.
Proof. exact (@lem7158353 B s P). Qed.
Lemma lem7158355 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : term91 A B t R x.
Proof. exact (@lem7158354 B t (term92 A B R x)). Qed.
Lemma lem7158356 {A B : Type'} (R : type1413 A B) (x : A) (j : B) : (term93 A B R x j) = (R x j).
Proof. exact (eq_refl (term93 A B R x j)). Qed.
Lemma lem7158357 {B : Type'} (j : B) (t : B -> Prop) : (term94 B j t) = (term94 B j t).
Proof. exact (eq_refl (term94 B j t)). Qed.
Lemma lem7158358 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (j : B) : (term95 A B t R x j) = (term96 A B t R x j).
Proof. exact (MK_COMB (@lem7158357 B j t) (@lem7158356 A B R x j)). Qed.
Lemma lem7158359 {B : Type'} (GEN_PVAR_321 : B) : (@SETSPEC B GEN_PVAR_321) = (@SETSPEC B GEN_PVAR_321).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_321)). Qed.
Lemma lem7158360 {A B : Type'} (GEN_PVAR_321 : B) (t : B -> Prop) (R : type1413 A B) (x : A) (j : B) : (term97 A B GEN_PVAR_321 t R x j) = (term98 A B GEN_PVAR_321 t R x j).
Proof. exact (MK_COMB (@lem7158359 B GEN_PVAR_321) (@lem7158358 A B t R x j)). Qed.
Lemma lem7158361 {B : Type'} (j : B) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem7158362 {A B : Type'} (GEN_PVAR_321 : B) (t : B -> Prop) (R : type1413 A B) (x : A) (j : B) : (term99 A B GEN_PVAR_321 t R x j) = (term100 A B GEN_PVAR_321 t R x j).
Proof. exact (MK_COMB (@lem7158360 A B GEN_PVAR_321 t R x j) (@lem7158361 B j)). Qed.
Lemma lem7158363 {A B : Type'} (GEN_PVAR_321 : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term101 A B GEN_PVAR_321 t R x) = (term102 A B GEN_PVAR_321 t R x).
Proof. exact (fun_ext (fun j : B => @lem7158362 A B GEN_PVAR_321 t R x j)). Qed.
Lemma lem7158364 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7158365 {A B : Type'} (GEN_PVAR_321 : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term103 A B GEN_PVAR_321 t R x) = (term104 A B GEN_PVAR_321 t R x).
Proof. exact (MK_COMB (@lem7158364 B) (@lem7158363 A B GEN_PVAR_321 t R x)). Qed.
Lemma lem7158366 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term105 A B t R x) = (term106 A B t R x).
Proof. exact (fun_ext (fun GEN_PVAR_321 : B => @lem7158365 A B GEN_PVAR_321 t R x)). Qed.
Lemma lem7158367 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem7158368 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term107 A B t R x) = (term89 A B t R x).
Proof. exact (MK_COMB (@lem7158367 B) (@lem7158366 A B t R x)). Qed.
Lemma lem7158369 {B : Type'} : (@FINITE B) = (@FINITE B).
Proof. exact (eq_refl (@FINITE B)). Qed.
Lemma lem7158370 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term108 A B t R x) = (term109 A B t R x).
Proof. exact (MK_COMB (@lem7158369 B) (@lem7158368 A B t R x)). Qed.
Lemma lem7158371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7158372 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term110 A B t R x) = (term111 A B t R x).
Proof. exact (MK_COMB (@lem7158371) (@lem7158370 A B t R x)). Qed.
Lemma lem7158373 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem7158374 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term108 A B t R x) = True) = ((term109 A B t R x) = True).
Proof. exact (MK_COMB (@lem7158372 A B t R x) (@lem7158373)). Qed.
Lemma lem7158375 {B : Type'} (t : B -> Prop) : (term112 B t) = (term112 B t).
Proof. exact (eq_refl (term112 B t)). Qed.
Lemma lem7158376 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term91 A B t R x) = (term113 A B t R x).
Proof. exact (MK_COMB (@lem7158375 B t) (@lem7158374 A B t R x)). Qed.
Lemma lem7158377 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : term113 A B t R x.
Proof. exact (EQ_MP (@lem7158376 A B t R x) (@lem7158355 A B t R x)). Qed.
Lemma lem7158379 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem7158329 B t) (@lem7158328 A B s t h1)). Qed.
Lemma lem7158380 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : True = (@FINITE B t).
Proof. exact (SYM (@lem7158379 A B s t h1)). Qed.
Lemma lem7158381 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : @FINITE B t.
Proof. exact (EQ_MP (@lem7158380 A B s t h1) (@lem0)). Qed.
Lemma lem7158382 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : (term109 A B t R x) = True.
Proof. exact (@lem7158377 A B t R x (@lem7158381 A B s t h1)). Qed.
Lemma lem7158383 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : True = (term109 A B t R x).
Proof. exact (SYM (@lem7158382 A B R x s t h1)). Qed.
Lemma lem7158384 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : term109 A B t R x.
Proof. exact (EQ_MP (@lem7158383 A B R x s t h1) (@lem0)). Qed.
Lemma lem7158385 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : (term61 A B t R x) = (term68 A B t R x).
Proof. exact (@lem7158351 A B t R x (@lem7158384 A B R x s t h1)). Qed.
Lemma lem7158392 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7158393 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : (term65 A B t R x) = (term114 A B t R x).
Proof. exact (MK_COMB (@lem7158392) (@lem7158385 A B R x s t h1)). Qed.
Lemma lem7158406 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term68 A B t R x) = (term68 A B t R x).
Proof. exact (eq_refl (term68 A B t R x)). Qed.
Lemma lem7158407 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : ((term61 A B t R x) = (term68 A B t R x)) = ((term68 A B t R x) = (term68 A B t R x)).
Proof. exact (MK_COMB (@lem7158393 A B R x s t h1) (@lem7158406 A B t R x)). Qed.
Lemma lem7158409 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7158410 (x : real) : (x = x) = True.
Proof. exact (@lem7158409 real x). Qed.
Lemma lem7158411 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term68 A B t R x) = (term68 A B t R x)) = True.
Proof. exact (@lem7158410 (term68 A B t R x)). Qed.
Lemma lem7158414 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term115 A B t R x) = (term115 A B t R x).
Proof. exact (eq_refl (term115 A B t R x)). Qed.
Lemma lem7158415 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term115 A B t R x) = (((term68 A B t R x) = (term68 A B t R x)) = True).
Proof. exact (eq_refl (term115 A B t R x)). Qed.
Lemma lem7158416 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term116 A B t R x) = (term116 A B t R x).
Proof. exact (eq_refl (term116 A B t R x)). Qed.
Lemma lem7158417 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term115 A B t R x) = (term115 A B t R x)) = ((term115 A B t R x) = (((term68 A B t R x) = (term68 A B t R x)) = True)).
Proof. exact (MK_COMB (@lem7158416 A B t R x) (@lem7158415 A B t R x)). Qed.
Lemma lem7158418 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term115 A B t R x) = (((term68 A B t R x) = (term68 A B t R x)) = True).
Proof. exact (eq_refl (term115 A B t R x)). Qed.
Lemma lem7158419 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7158420 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term116 A B t R x) = (term117 A B t R x).
Proof. exact (MK_COMB (@lem7158419) (@lem7158418 A B t R x)). Qed.
Lemma lem7158421 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (((term68 A B t R x) = (term68 A B t R x)) = True) = (((term68 A B t R x) = (term68 A B t R x)) = True).
Proof. exact (eq_refl (((term68 A B t R x) = (term68 A B t R x)) = True)). Qed.
Lemma lem7158422 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term115 A B t R x) = (((term68 A B t R x) = (term68 A B t R x)) = True)) = ((((term68 A B t R x) = (term68 A B t R x)) = True) = (((term68 A B t R x) = (term68 A B t R x)) = True)).
Proof. exact (MK_COMB (@lem7158420 A B t R x) (@lem7158421 A B t R x)). Qed.
Lemma lem7158423 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term115 A B t R x) = (term115 A B t R x)) = ((((term68 A B t R x) = (term68 A B t R x)) = True) = (((term68 A B t R x) = (term68 A B t R x)) = True)).
Proof. exact (TRANS (@lem7158417 A B t R x) (@lem7158422 A B t R x)). Qed.
Lemma lem7158424 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (((term68 A B t R x) = (term68 A B t R x)) = True) = (((term68 A B t R x) = (term68 A B t R x)) = True).
Proof. exact (EQ_MP (@lem7158423 A B t R x) (@lem7158414 A B t R x)). Qed.
Lemma lem7158425 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term68 A B t R x) = (term68 A B t R x)) = True.
Proof. exact (EQ_MP (@lem7158424 A B t R x) (@lem7158411 A B t R x)). Qed.
Lemma lem7158426 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : ((term61 A B t R x) = (term68 A B t R x)) = True.
Proof. exact (TRANS (@lem7158407 A B R x s t h1) (@lem7158425 A B t R x)). Qed.
Lemma lem7158427 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : True = ((term61 A B t R x) = (term68 A B t R x)).
Proof. exact (SYM (@lem7158426 A B R x s t h1)). Qed.
Lemma lem7158428 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : (term61 A B t R x) = (term68 A B t R x).
Proof. exact (EQ_MP (@lem7158427 A B R x s t h1) (@lem0)). Qed.
Lemma lem7158429 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : term74 A B s t R x.
Proof. exact (fun h0 : @IN A x s => @lem7158428 A B R x s t h1). Qed.
Lemma lem7158434 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : term78 A B s t R.
Proof. exact (fun x : A => @lem7158429 A B R x s t h1). Qed.
Lemma lem7158435 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : term77 A B s t R.
Proof. exact (EQ_MP (@lem7158301 A B s t R) (@lem7158434 A B R s t h1)). Qed.
Lemma lem7158436 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : (term47 A B s t R) = (term118 A B s t R).
Proof. exact (@lem7158227 A B s t R (@lem7158435 A B R s t h1)). Qed.
Lemma lem7158467 {_133990 _133991 : Type'} (h1 : term119 _133990 _133991) : term119 _133990 _133991.
Proof. exact (h1). Qed.
Lemma lem7158468 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (h1 : term119 _133990 _133991) : term120 _133990 _133991 R.
Proof. exact (@lem7158467 _133990 _133991 h1 R). Qed.
Lemma lem7158469 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) : (term120 _133990 _133991 R) = (term121 _133990 _133991 R).
Proof. exact (eq_refl (term120 _133990 _133991 R)). Qed.
Lemma lem7158470 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (h1 : term119 _133990 _133991) : term121 _133990 _133991 R.
Proof. exact (EQ_MP (@lem7158469 _133990 _133991 R) (@lem7158468 _133990 _133991 R h1)). Qed.
Lemma lem7158471 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (h1 : term119 _133990 _133991) : term122 _133990 _133991 R f.
Proof. exact (@lem7158470 _133990 _133991 R h1 f). Qed.
Lemma lem7158472 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term122 _133990 _133991 R f) = (term123 _133990 _133991 R f).
Proof. exact (eq_refl (term122 _133990 _133991 R f)). Qed.
Lemma lem7158473 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (h1 : term119 _133990 _133991) : term123 _133990 _133991 R f.
Proof. exact (EQ_MP (@lem7158472 _133990 _133991 R f) (@lem7158471 _133990 _133991 R f h1)). Qed.
Lemma lem7158474 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (s : _133991 -> Prop) (h1 : term119 _133990 _133991) : term124 _133990 _133991 R f s.
Proof. exact (@lem7158473 _133990 _133991 R f h1 s). Qed.
Lemma lem7158475 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term124 _133990 _133991 R f s) = (term125 _133990 _133991 s R f).
Proof. exact (eq_refl (term124 _133990 _133991 R f s)). Qed.
Lemma lem7158476 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (h1 : term119 _133990 _133991) : term125 _133990 _133991 s R f.
Proof. exact (EQ_MP (@lem7158475 _133990 _133991 s R f) (@lem7158474 _133990 _133991 R f s h1)). Qed.
Lemma lem7158477 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (t : _133990 -> Prop) (h1 : term119 _133990 _133991) : term126 _133990 _133991 s R f t.
Proof. exact (@lem7158476 _133990 _133991 s R f h1 t). Qed.
Lemma lem7158478 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term126 _133990 _133991 s R f t) = (term127 _133990 _133991 t s R f).
Proof. exact (eq_refl (term126 _133990 _133991 s R f t)). Qed.
Lemma lem7158479 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (h1 : term119 _133990 _133991) : term127 _133990 _133991 t s R f.
Proof. exact (EQ_MP (@lem7158478 _133990 _133991 t s R f) (@lem7158477 _133990 _133991 s R f t h1)). Qed.
Lemma lem7158480 {_133990 _133991 : Type'} (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term128 _133990 _133991 s t) : term128 _133990 _133991 s t.
Proof. exact (h1). Qed.
Lemma lem7158481 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term119 _133990 _133991) (h2 : term128 _133990 _133991 s t) : (term129 _133990 _133991 s t R f) = (term130 _133990 _133991 t s R f).
Proof. exact (@lem7158479 _133990 _133991 t s R f h1 (@lem7158480 _133990 _133991 s t h2)). Qed.
Lemma lem7158482 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term119 _133990 _133991) (h2 : term128 _133990 _133991 s t) : term131 _133990 _133991 t s R.
Proof. exact (fun f : type1472 _133990 _133991 => @lem7158481 _133990 _133991 R f s t h1 h2). Qed.
Lemma lem7158483 {_133990 _133991 : Type'} (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term119 _133990 _133991) (h2 : term128 _133990 _133991 s t) : term132 _133990 _133991 t s.
Proof. exact (fun R : type1470 _133990 _133991 => @lem7158482 _133990 _133991 R s t h1 h2). Qed.
Lemma lem7158484 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (h1 : term119 _133990 _133991) : term133 _133990 _133991 t s.
Proof. exact (fun h0 : term128 _133990 _133991 s t => @lem7158483 _133990 _133991 s t h1 h0). Qed.
Lemma lem7158485 {_133990 _133991 : Type'} (s : _133991 -> Prop) (h1 : term119 _133990 _133991) : term134 _133990 _133991 s.
Proof. exact (fun t : _133990 -> Prop => @lem7158484 _133990 _133991 t s h1). Qed.
Lemma lem7158486 {_133990 _133991 : Type'} (h1 : term119 _133990 _133991) : term135 _133990 _133991.
Proof. exact (fun s : _133991 -> Prop => @lem7158485 _133990 _133991 s h1). Qed.
Lemma lem7158487 {_133990 _133991 : Type'} : term136 _133990 _133991.
Proof. exact (fun h0 : term119 _133990 _133991 => @lem7158486 _133990 _133991 h0). Qed.
Lemma lem7158488 {_133990 _133991 : Type'} : term135 _133990 _133991.
Proof. exact (@lem7158487 _133990 _133991 (@lem7158000 _133990 _133991)). Qed.
Lemma lem7158489 {_133990 _133991 : Type'} (s : _133991 -> Prop) : term137 _133990 _133991 s.
Proof. exact (@lem7158488 _133990 _133991 s). Qed.
Lemma lem7158490 {_133990 _133991 : Type'} (s : _133991 -> Prop) : (term137 _133990 _133991 s) = (term134 _133990 _133991 s).
Proof. exact (eq_refl (term137 _133990 _133991 s)). Qed.
Lemma lem7158491 {_133990 _133991 : Type'} (s : _133991 -> Prop) : term134 _133990 _133991 s.
Proof. exact (EQ_MP (@lem7158490 _133990 _133991 s) (@lem7158489 _133990 _133991 s)). Qed.
Lemma lem7158492 {_133990 _133991 : Type'} (s : _133991 -> Prop) (t : _133990 -> Prop) : term138 _133990 _133991 s t.
Proof. exact (@lem7158491 _133990 _133991 s t). Qed.
Lemma lem7158493 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) : (term138 _133990 _133991 s t) = (term133 _133990 _133991 t s).
Proof. exact (eq_refl (term138 _133990 _133991 s t)). Qed.
Lemma lem7158496 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) : term133 _133990 _133991 t s.
Proof. exact (EQ_MP (@lem7158493 _133990 _133991 t s) (@lem7158492 _133990 _133991 s t)). Qed.
Lemma lem7158497 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term139 A B t s.
Proof. exact (@lem7158496 B A t s). Qed.
Lemma lem7158498 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : term140 A B t s.
Proof. exact (@lem7158497 A B t s (@lem7158219 A B s t h1)). Qed.
Lemma lem7158499 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : term141 A B t s R.
Proof. exact (@lem7158498 A B s t h1 R). Qed.
Lemma lem7158500 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) : (term141 A B t s R) = (term142 A B t s R).
Proof. exact (eq_refl (term141 A B t s R)). Qed.
Lemma lem7158501 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : term142 A B t s R.
Proof. exact (EQ_MP (@lem7158500 A B t s R) (@lem7158499 A B R s t h1)). Qed.
Lemma lem7158502 {A B : Type'} (R : type1413 A B) (f : type1416 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : term143 A B t s R f.
Proof. exact (@lem7158501 A B R s t h1 f). Qed.
Lemma lem7158503 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (f : type1416 A B) : (term143 A B t s R f) = ((term144 A B s t R f) = (term145 A B t s R f)).
Proof. exact (eq_refl (term143 A B t s R f)). Qed.
Lemma lem7158508 {A B : Type'} (R : type1413 A B) (f : type1416 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : (term144 A B s t R f) = (term145 A B t s R f).
Proof. exact (EQ_MP (@lem7158503 A B t s R f) (@lem7158502 A B R f s t h1)). Qed.
Lemma lem7158509 {A B : Type'} (R : type1413 A B) (f : type1416 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : (term144 A B s t R f) = (term145 A B t s R f).
Proof. exact (@lem7158508 A B R f s t h1). Qed.
Lemma lem7158510 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : (term146 A B s t R) = (term147 A B t s R).
Proof. exact (@lem7158509 A B R (term148 A B) s t h1). Qed.
Lemma lem7158511 {A B : Type'} (i : A) : (term149 A B i) = (term150 B).
Proof. exact (eq_refl (term149 A B i)). Qed.
Lemma lem7158512 {B : Type'} (j : B) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem7158513 {A B : Type'} (i : A) (j : B) : (term151 A B i j) = (term152 B j).
Proof. exact (MK_COMB (@lem7158511 A B i) (@lem7158512 B j)). Qed.
Lemma lem7158514 {B : Type'} (j : B) : (term152 B j) = term153.
Proof. exact (eq_refl (term152 B j)). Qed.
Lemma lem7158515 {A B : Type'} (i : A) (j : B) : (term151 A B i j) = term153.
Proof. exact (TRANS (@lem7158513 A B i j) (@lem7158514 B j)). Qed.
Lemma lem7158516 {A B : Type'} (i : A) : (term154 A B i) = (term150 B).
Proof. exact (fun_ext (fun j : B => @lem7158515 A B i j)). Qed.
Lemma lem7158517 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (i : A) : (term155 A B t R i) = (term155 A B t R i).
Proof. exact (eq_refl (term155 A B t R i)). Qed.
Lemma lem7158518 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (i : A) : (term156 A B t R i) = (term68 A B t R i).
Proof. exact (MK_COMB (@lem7158517 A B t R i) (@lem7158516 A B i)). Qed.
Lemma lem7158519 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term157 A B t R) = (term56 A B t R).
Proof. exact (fun_ext (fun i : A => @lem7158518 A B t R i)). Qed.
Lemma lem7158520 {A : Type'} (s : A -> Prop) : (@sum A s) = (@sum A s).
Proof. exact (eq_refl (@sum A s)). Qed.
Lemma lem7158521 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term146 A B s t R) = (term118 A B s t R).
Proof. exact (MK_COMB (@lem7158520 A s) (@lem7158519 A B t R)). Qed.
Lemma lem7158522 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7158523 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term158 A B s t R) = (term159 A B s t R).
Proof. exact (MK_COMB (@lem7158522) (@lem7158521 A B s t R)). Qed.
Lemma lem7158524 {A B : Type'} (i : A) : (term149 A B i) = (term150 B).
Proof. exact (eq_refl (term149 A B i)). Qed.
Lemma lem7158525 {B : Type'} (j : B) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem7158526 {A B : Type'} (i : A) (j : B) : (term151 A B i j) = (term152 B j).
Proof. exact (MK_COMB (@lem7158524 A B i) (@lem7158525 B j)). Qed.
Lemma lem7158527 {B : Type'} (j : B) : (term152 B j) = term153.
Proof. exact (eq_refl (term152 B j)). Qed.
Lemma lem7158528 {A B : Type'} (i : A) (j : B) : (term151 A B i j) = term153.
Proof. exact (TRANS (@lem7158526 A B i j) (@lem7158527 B j)). Qed.
Lemma lem7158529 {A B : Type'} (j : B) : (term160 A B j) = (term150 A).
Proof. exact (fun_ext (fun i : A => @lem7158528 A B i j)). Qed.
Lemma lem7158530 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (j : B) : (term161 A B s R j) = (term161 A B s R j).
Proof. exact (eq_refl (term161 A B s R j)). Qed.
Lemma lem7158531 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (j : B) : (term162 A B s R j) = (term163 A B s R j).
Proof. exact (MK_COMB (@lem7158530 A B s R j) (@lem7158529 A B j)). Qed.
Lemma lem7158532 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : (term164 A B s R) = (term165 A B s R).
Proof. exact (fun_ext (fun j : B => @lem7158531 A B s R j)). Qed.
Lemma lem7158533 {B : Type'} (t : B -> Prop) : (@sum B t) = (@sum B t).
Proof. exact (eq_refl (@sum B t)). Qed.
Lemma lem7158534 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) : (term147 A B t s R) = (term166 A B t s R).
Proof. exact (MK_COMB (@lem7158533 B t) (@lem7158532 A B s R)). Qed.
Lemma lem7158535 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) : ((term146 A B s t R) = (term147 A B t s R)) = ((term118 A B s t R) = (term166 A B t s R)).
Proof. exact (MK_COMB (@lem7158523 A B s t R) (@lem7158534 A B t s R)). Qed.
Lemma lem7158536 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : (term118 A B s t R) = (term166 A B t s R).
Proof. exact (EQ_MP (@lem7158535 A B t s R) (@lem7158510 A B R s t h1)). Qed.
Lemma lem7158537 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7158538 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : (term159 A B s t R) = (term167 A B t s R).
Proof. exact (MK_COMB (@lem7158537) (@lem7158536 A B R s t h1)). Qed.
Lemma lem7158539 {B : Type'} (t : B -> Prop) (k : B -> nat) : (term48 B t k) = (term48 B t k).
Proof. exact (eq_refl (term48 B t k)). Qed.
Lemma lem7158540 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : ((term118 A B s t R) = (term48 B t k)) = ((term166 A B t s R) = (term48 B t k)).
Proof. exact (MK_COMB (@lem7158538 A B R s t h1) (@lem7158539 B t k)). Qed.
Lemma lem7158541 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : ((term166 A B t s R) = (term48 B t k)) = ((term118 A B s t R) = (term48 B t k)).
Proof. exact (SYM (@lem7158540 A B R k s t h1)). Qed.
Lemma lem7158543 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : term8 _132349 f s g.
Proof. exact (EQ_MP (@lem7158110 _132349 f s g) (@lem7158109 _132349 f s g)). Qed.
Lemma lem7158544 {B : Type'} (f : B -> real) (s : B -> Prop) (g : B -> real) : term8 B f s g.
Proof. exact (@lem7158543 B f s g). Qed.
Lemma lem7158545 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : term168 A B s R t k.
Proof. exact (@lem7158544 B (term165 A B s R) t (term169 B k)). Qed.
Lemma lem7158546 {A : Type'} (s : A -> Prop) : term79 A s.
Proof. exact (@lem3603906 A s). Qed.
Lemma lem7158547 {A : Type'} (s : A -> Prop) : (term79 A s) = (term80 A s).
Proof. exact (eq_refl (term79 A s)). Qed.
Lemma lem7158548 {A : Type'} (s : A -> Prop) : term80 A s.
Proof. exact (EQ_MP (@lem7158547 A s) (@lem7158546 A s)). Qed.
Lemma lem7158549 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term81 A s P.
Proof. exact (@lem7158548 A s P). Qed.
Lemma lem7158550 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term81 A s P) = (term82 A s P).
Proof. exact (eq_refl (term81 A s P)). Qed.
Lemma lem7158551 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term82 A s P.
Proof. exact (EQ_MP (@lem7158550 A s P) (@lem7158549 A s P)). Qed.
Lemma lem7158552 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7158553 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term83 A s P.
Proof. exact (@lem7158551 A s P (@lem7158552 A s h1)). Qed.
Lemma lem7158554 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term83 A s P) = ((term83 A s P) = True).
Proof. exact (@lem7 (term83 A s P)). Qed.
Lemma lem7158555 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term83 A s P) = True.
Proof. exact (EQ_MP (@lem7158554 A s P) (@lem7158553 A P s h1)). Qed.
Lemma lem7158561 {_132484 : Type'} (c : real) : term170 _132484 c.
Proof. exact (@lem7085323 _132484 c). Qed.
Lemma lem7158562 {_132484 : Type'} (c : real) : (term170 _132484 c) = (term171 _132484 c).
Proof. exact (eq_refl (term170 _132484 c)). Qed.
Lemma lem7158563 {_132484 : Type'} (c : real) : term171 _132484 c.
Proof. exact (EQ_MP (@lem7158562 _132484 c) (@lem7158561 _132484 c)). Qed.
Lemma lem7158564 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : term172 _132484 c s.
Proof. exact (@lem7158563 _132484 c s). Qed.
Lemma lem7158565 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term172 _132484 c s) = (term173 _132484 s c).
Proof. exact (eq_refl (term172 _132484 c s)). Qed.
Lemma lem7158566 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : term173 _132484 s c.
Proof. exact (EQ_MP (@lem7158565 _132484 s c) (@lem7158564 _132484 c s)). Qed.
Lemma lem7158567 {_132484 : Type'} (s : _132484 -> Prop) (h1 : @FINITE _132484 s) : @FINITE _132484 s.
Proof. exact (h1). Qed.
Lemma lem7158568 {_132484 : Type'} (c : real) (s : _132484 -> Prop) (h1 : @FINITE _132484 s) : (term174 _132484 s c) = (term175 _132484 s c).
Proof. exact (@lem7158566 _132484 s c (@lem7158567 _132484 s h1)). Qed.
Lemma lem7158577 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : @FINITE A s.
Proof. exact (proj1 (@lem7158219 A B s t h1)). Qed.
Lemma lem7158578 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7158580 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term44 A B t s R k) : term176 A B t s R k j.
Proof. exact (@lem7158218 A B t s R k h1 j). Qed.
Lemma lem7158581 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (j : B) : (term176 A B t s R k j) = (term177 A B t s R k j).
Proof. exact (eq_refl (term176 A B t s R k j)). Qed.
Lemma lem7158582 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term44 A B t s R k) : term177 A B t s R k j.
Proof. exact (EQ_MP (@lem7158581 A B t s R k j) (@lem7158580 A B j t s R k h1)). Qed.
Lemma lem7158583 {B : Type'} (j : B) (t : B -> Prop) (h1 : @IN B j t) : @IN B j t.
Proof. exact (h1). Qed.
Lemma lem7158584 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (j : B) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : @IN B j t) : (term178 A B s R j) = (k j).
Proof. exact (@lem7158582 A B j t s R k h1 (@lem7158583 B j t h2)). Qed.
Lemma lem7158597 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term179 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7158598 (p : Prop) (q : Prop) (p' : Prop) : term180 p q p'.
Proof. exact (fun q' : Prop => @lem7158597 p q p' q'). Qed.
Lemma lem7158599 (p : Prop) (q : Prop) : term181 p q.
Proof. exact (fun p' : Prop => @lem7158598 p q p'). Qed.
Lemma lem7158600 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) : term182 A B t s R k x.
Proof. exact (@lem7158599 (@IN B x t) ((term183 A B s R x) = (term184 B k x))). Qed.
Lemma lem7158601 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (p' : Prop) : term185 A B t s R k x p'.
Proof. exact (@lem7158600 A B t s R k x p'). Qed.
Lemma lem7158602 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (p' : Prop) : (term185 A B t s R k x p') = (term186 A B t s R k x p').
Proof. exact (eq_refl (term185 A B t s R k x p')). Qed.
Lemma lem7158603 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (p' : Prop) : term186 A B t s R k x p'.
Proof. exact (EQ_MP (@lem7158602 A B t s R k x p') (@lem7158601 A B t s R k x p')). Qed.
Lemma lem7158604 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (p' : Prop) (q' : Prop) : term187 A B t s R k x p' q'.
Proof. exact (@lem7158603 A B t s R k x p' q'). Qed.
Lemma lem7158605 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (p' : Prop) (q' : Prop) : (term187 A B t s R k x p' q') = (term188 A B t s R k x p' q').
Proof. exact (eq_refl (term187 A B t s R k x p' q')). Qed.
Lemma lem7158606 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (p' : Prop) (q' : Prop) : term188 A B t s R k x p' q'.
Proof. exact (EQ_MP (@lem7158605 A B t s R k x p' q') (@lem7158604 A B t s R k x p' q')). Qed.
Lemma lem7158607 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (@IN B x t).
Proof. exact (eq_refl (@IN B x t)). Qed.
Lemma lem7158608 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (t : B -> Prop) (q' : Prop) : term189 A B s R k x t q'.
Proof. exact (@lem7158606 A B t s R k x (@IN B x t) q'). Qed.
Lemma lem7158609 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (t : B -> Prop) (q' : Prop) : term190 A B s R k x t q'.
Proof. exact (@lem7158608 A B s R k x t q' (@lem7158607 B x t)). Qed.
Lemma lem7158610 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : @IN B x t.
Proof. exact (h1). Qed.
Lemma lem7158611 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = ((@IN B x t) = True).
Proof. exact (@lem7 (@IN B x t)). Qed.
Lemma lem7158616 {A B : Type'} (f : A -> B) (y : A) : (term57 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7158617 {B : Type'} (f : B -> real) (y : B) : (term58 B f y) = (f y).
Proof. exact (@lem7158616 B real f y). Qed.
Lemma lem7158618 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term191 A B s R x) = (term183 A B s R x).
Proof. exact (@lem7158617 B (term165 A B s R) x). Qed.
Lemma lem7158619 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (j : B) : (term183 A B s R j) = (term163 A B s R j).
Proof. exact (eq_refl (term183 A B s R j)). Qed.
Lemma lem7158620 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : (term192 A B s R) = (term165 A B s R).
Proof. exact (fun_ext (fun j : B => @lem7158619 A B s R j)). Qed.
Lemma lem7158621 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7158622 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term191 A B s R x) = (term183 A B s R x).
Proof. exact (MK_COMB (@lem7158620 A B s R) (@lem7158621 B x)). Qed.
Lemma lem7158623 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7158624 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term193 A B s R x) = (term194 A B s R x).
Proof. exact (MK_COMB (@lem7158623) (@lem7158622 A B s R x)). Qed.
Lemma lem7158625 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term183 A B s R x) = (term163 A B s R x).
Proof. exact (eq_refl (term183 A B s R x)). Qed.
Lemma lem7158626 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : ((term191 A B s R x) = (term183 A B s R x)) = ((term183 A B s R x) = (term163 A B s R x)).
Proof. exact (MK_COMB (@lem7158624 A B s R x) (@lem7158625 A B s R x)). Qed.
Lemma lem7158627 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term183 A B s R x) = (term163 A B s R x).
Proof. exact (EQ_MP (@lem7158626 A B s R x) (@lem7158618 A B s R x)). Qed.
Lemma lem7158629 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : term173 _132484 s c.
Proof. exact (fun h0 : @FINITE _132484 s => @lem7158568 _132484 c s h0). Qed.
Lemma lem7158630 {A : Type'} (s : A -> Prop) (c : real) : term173 A s c.
Proof. exact (@lem7158629 A s c). Qed.
Lemma lem7158631 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : term195 A B s R x.
Proof. exact (@lem7158630 A (term196 A B s R x) term153). Qed.
Lemma lem7158633 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term90 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem7158555 A P s h0). Qed.
Lemma lem7158634 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term90 A s P.
Proof. exact (@lem7158633 A s P). Qed.
Lemma lem7158635 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : term197 A B s R x.
Proof. exact (@lem7158634 A s (term198 A B R x)). Qed.
Lemma lem7158636 {A B : Type'} (R : type1413 A B) (i : A) (x : B) : (term199 A B R x i) = (R i x).
Proof. exact (eq_refl (term199 A B R x i)). Qed.
Lemma lem7158637 {A : Type'} (i : A) (s : A -> Prop) : (term94 A i s) = (term94 A i s).
Proof. exact (eq_refl (term94 A i s)). Qed.
Lemma lem7158638 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (i : A) (x : B) : (term200 A B s R x i) = (term201 A B s R i x).
Proof. exact (MK_COMB (@lem7158637 A i s) (@lem7158636 A B R i x)). Qed.
Lemma lem7158639 {A : Type'} (GEN_PVAR_318 : A) : (@SETSPEC A GEN_PVAR_318) = (@SETSPEC A GEN_PVAR_318).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_318)). Qed.
Lemma lem7158640 {A B : Type'} (GEN_PVAR_318 : A) (s : A -> Prop) (R : type1413 A B) (i : A) (x : B) : (term202 A B GEN_PVAR_318 s R x i) = (term203 A B GEN_PVAR_318 s R i x).
Proof. exact (MK_COMB (@lem7158639 A GEN_PVAR_318) (@lem7158638 A B s R i x)). Qed.
Lemma lem7158641 {A : Type'} (i : A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7158642 {A B : Type'} (GEN_PVAR_318 : A) (s : A -> Prop) (R : type1413 A B) (x : B) (i : A) : (term204 A B GEN_PVAR_318 s R x i) = (term205 A B GEN_PVAR_318 s R x i).
Proof. exact (MK_COMB (@lem7158640 A B GEN_PVAR_318 s R i x) (@lem7158641 A i)). Qed.
Lemma lem7158643 {A B : Type'} (GEN_PVAR_318 : A) (s : A -> Prop) (R : type1413 A B) (x : B) : (term206 A B GEN_PVAR_318 s R x) = (term207 A B GEN_PVAR_318 s R x).
Proof. exact (fun_ext (fun i : A => @lem7158642 A B GEN_PVAR_318 s R x i)). Qed.
Lemma lem7158644 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7158645 {A B : Type'} (GEN_PVAR_318 : A) (s : A -> Prop) (R : type1413 A B) (x : B) : (term208 A B GEN_PVAR_318 s R x) = (term209 A B GEN_PVAR_318 s R x).
Proof. exact (MK_COMB (@lem7158644 A) (@lem7158643 A B GEN_PVAR_318 s R x)). Qed.
Lemma lem7158646 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term210 A B s R x) = (term211 A B s R x).
Proof. exact (fun_ext (fun GEN_PVAR_318 : A => @lem7158645 A B GEN_PVAR_318 s R x)). Qed.
Lemma lem7158647 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7158648 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term212 A B s R x) = (term196 A B s R x).
Proof. exact (MK_COMB (@lem7158647 A) (@lem7158646 A B s R x)). Qed.
Lemma lem7158649 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem7158650 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term213 A B s R x) = (term214 A B s R x).
Proof. exact (MK_COMB (@lem7158649 A) (@lem7158648 A B s R x)). Qed.
Lemma lem7158651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7158652 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term215 A B s R x) = (term216 A B s R x).
Proof. exact (MK_COMB (@lem7158651) (@lem7158650 A B s R x)). Qed.
Lemma lem7158653 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem7158654 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : ((term213 A B s R x) = True) = ((term214 A B s R x) = True).
Proof. exact (MK_COMB (@lem7158652 A B s R x) (@lem7158653)). Qed.
Lemma lem7158655 {A : Type'} (s : A -> Prop) : (term112 A s) = (term112 A s).
Proof. exact (eq_refl (term112 A s)). Qed.
Lemma lem7158656 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term197 A B s R x) = (term217 A B s R x).
Proof. exact (MK_COMB (@lem7158655 A s) (@lem7158654 A B s R x)). Qed.
Lemma lem7158657 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : term217 A B s R x.
Proof. exact (EQ_MP (@lem7158656 A B s R x) (@lem7158635 A B s R x)). Qed.
Lemma lem7158659 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7158578 A s) (@lem7158577 A B s t h1)). Qed.
Lemma lem7158660 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : True = (@FINITE A s).
Proof. exact (SYM (@lem7158659 A B s t h1)). Qed.
Lemma lem7158661 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : @FINITE A s.
Proof. exact (EQ_MP (@lem7158660 A B s t h1) (@lem0)). Qed.
Lemma lem7158662 {A B : Type'} (R : type1413 A B) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : (term214 A B s R x) = True.
Proof. exact (@lem7158657 A B s R x (@lem7158661 A B s t h1)). Qed.
Lemma lem7158663 {A B : Type'} (R : type1413 A B) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : True = (term214 A B s R x).
Proof. exact (SYM (@lem7158662 A B R x s t h1)). Qed.
Lemma lem7158664 {A B : Type'} (R : type1413 A B) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : term214 A B s R x.
Proof. exact (EQ_MP (@lem7158663 A B R x s t h1) (@lem0)). Qed.
Lemma lem7158665 {A B : Type'} (R : type1413 A B) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term51 A B s t) : (term163 A B s R x) = (term218 A B s R x).
Proof. exact (@lem7158631 A B s R x (@lem7158664 A B R x s t h1)). Qed.
Lemma lem7158667 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term44 A B t s R k) : term177 A B t s R k j.
Proof. exact (fun h0 : @IN B j t => @lem7158584 A B s R k j t h1 h0). Qed.
Lemma lem7158668 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term44 A B t s R k) : term177 A B t s R k j.
Proof. exact (@lem7158667 A B j t s R k h1). Qed.
Lemma lem7158669 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term44 A B t s R k) : term177 A B t s R k x.
Proof. exact (@lem7158668 A B x t s R k h1). Qed.
Lemma lem7158671 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : (@IN B x t) = True.
Proof. exact (EQ_MP (@lem7158611 B x t) (@lem7158610 B x t h1)). Qed.
Lemma lem7158672 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : True = (@IN B x t).
Proof. exact (SYM (@lem7158671 B x t h1)). Qed.
Lemma lem7158673 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : @IN B x t.
Proof. exact (EQ_MP (@lem7158672 B x t h1) (@lem0)). Qed.
Lemma lem7158674 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : @IN B x t) : (term178 A B s R x) = (k x).
Proof. exact (@lem7158669 A B x t s R k h1 (@lem7158673 B x t h2)). Qed.
Lemma lem7158675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7158676 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : @IN B x t) : (term219 A B s R x) = (term220 B k x).
Proof. exact (MK_COMB (@lem7158675) (@lem7158674 A B s R k x t h1 h2)). Qed.
Lemma lem7158677 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7158678 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : @IN B x t) : (term221 A B s R x) = (term222 B k x).
Proof. exact (MK_COMB (@lem7158677) (@lem7158676 A B s R k x t h1 h2)). Qed.
Lemma lem7158679 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem7158680 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : @IN B x t) : (term218 A B s R x) = (term223 B k x).
Proof. exact (MK_COMB (@lem7158678 A B s R k x t h1 h2) (@lem7158679)). Qed.
Lemma lem7158681 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) (h3 : @IN B x t) : (term163 A B s R x) = (term223 B k x).
Proof. exact (TRANS (@lem7158665 A B R x s t h2) (@lem7158680 A B s R k x t h1 h3)). Qed.
Lemma lem7158682 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) (h3 : @IN B x t) : (term183 A B s R x) = (term223 B k x).
Proof. exact (TRANS (@lem7158627 A B s R x) (@lem7158681 A B R k s x t h1 h2 h3)). Qed.
Lemma lem7158683 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7158684 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) (h3 : @IN B x t) : (term194 A B s R x) = (term224 B k x).
Proof. exact (MK_COMB (@lem7158683) (@lem7158682 A B R k s x t h1 h2 h3)). Qed.
Lemma lem7158686 {A B : Type'} (f : A -> B) (y : A) : (term57 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7158687 {B : Type'} (f : B -> real) (y : B) : (term58 B f y) = (f y).
Proof. exact (@lem7158686 B real f y). Qed.
Lemma lem7158688 {B : Type'} (k : B -> nat) (x : B) : (term225 B k x) = (term184 B k x).
Proof. exact (@lem7158687 B (term169 B k) x). Qed.
Lemma lem7158689 {B : Type'} (k : B -> nat) (i : B) : (term184 B k i) = (term220 B k i).
Proof. exact (eq_refl (term184 B k i)). Qed.
Lemma lem7158690 {B : Type'} (k : B -> nat) : (term226 B k) = (term169 B k).
Proof. exact (fun_ext (fun i : B => @lem7158689 B k i)). Qed.
Lemma lem7158691 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7158692 {B : Type'} (k : B -> nat) (x : B) : (term225 B k x) = (term184 B k x).
Proof. exact (MK_COMB (@lem7158690 B k) (@lem7158691 B x)). Qed.
Lemma lem7158693 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7158694 {B : Type'} (k : B -> nat) (x : B) : (term227 B k x) = (term228 B k x).
Proof. exact (MK_COMB (@lem7158693) (@lem7158692 B k x)). Qed.
Lemma lem7158695 {B : Type'} (k : B -> nat) (x : B) : (term184 B k x) = (term220 B k x).
Proof. exact (eq_refl (term184 B k x)). Qed.
Lemma lem7158696 {B : Type'} (k : B -> nat) (x : B) : ((term225 B k x) = (term184 B k x)) = ((term184 B k x) = (term220 B k x)).
Proof. exact (MK_COMB (@lem7158694 B k x) (@lem7158695 B k x)). Qed.
Lemma lem7158697 {B : Type'} (k : B -> nat) (x : B) : (term184 B k x) = (term220 B k x).
Proof. exact (EQ_MP (@lem7158696 B k x) (@lem7158688 B k x)). Qed.
Lemma lem7158698 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) (h3 : @IN B x t) : ((term183 A B s R x) = (term184 B k x)) = ((term223 B k x) = (term220 B k x)).
Proof. exact (MK_COMB (@lem7158684 A B R k s x t h1 h2 h3) (@lem7158697 B k x)). Qed.
Lemma lem7158701 {A B : Type'} (x : B) (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : term229 A B t s R k x.
Proof. exact (fun h0 : @IN B x t => @lem7158698 A B R k s x t h1 h2 h0). Qed.
Lemma lem7158702 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) (x : B) : term230 A B s R t k x.
Proof. exact (@lem7158609 A B s R k x t ((term223 B k x) = (term220 B k x))). Qed.
Lemma lem7158703 {A B : Type'} (x : B) (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : (term231 A B t s R k x) = (term232 B t k x).
Proof. exact (@lem7158702 A B s R t k x (@lem7158701 A B x R k s t h1 h2)). Qed.
Lemma lem7158731 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : (term233 A B t s R k) = (term234 B t k).
Proof. exact (fun_ext (fun x : B => @lem7158703 A B x R k s t h1 h2)). Qed.
Lemma lem7158759 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7158760 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : (term235 A B t s R k) = (term236 B t k).
Proof. exact (MK_COMB (@lem7158759 B) (@lem7158731 A B R k s t h1 h2)). Qed.
Lemma lem7158792 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : (term236 B t k) = (term235 A B t s R k).
Proof. exact (SYM (@lem7158760 A B R k s t h1 h2)). Qed.
Lemma lem7158802 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem7158080 x) (@lem7158079 x)). Qed.
Lemma lem7158803 {B : Type'} (k : B -> nat) (x : B) : (term223 B k x) = (term220 B k x).
Proof. exact (@lem7158802 (term220 B k x)). Qed.
Lemma lem7158804 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7158805 {B : Type'} (k : B -> nat) (x : B) : (term224 B k x) = (term237 B k x).
Proof. exact (MK_COMB (@lem7158804) (@lem7158803 B k x)). Qed.
Lemma lem7158806 {B : Type'} (k : B -> nat) (x : B) : (term220 B k x) = (term220 B k x).
Proof. exact (eq_refl (term220 B k x)). Qed.
Lemma lem7158807 {B : Type'} (k : B -> nat) (x : B) : ((term223 B k x) = (term220 B k x)) = ((term220 B k x) = (term220 B k x)).
Proof. exact (MK_COMB (@lem7158805 B k x) (@lem7158806 B k x)). Qed.
Lemma lem7158809 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7158810 (x : real) : (x = x) = True.
Proof. exact (@lem7158809 real x). Qed.
Lemma lem7158811 {B : Type'} (k : B -> nat) (x : B) : ((term220 B k x) = (term220 B k x)) = True.
Proof. exact (@lem7158810 (term220 B k x)). Qed.
Lemma lem7158812 {B : Type'} (k : B -> nat) (x : B) : ((term223 B k x) = (term220 B k x)) = True.
Proof. exact (TRANS (@lem7158807 B k x) (@lem7158811 B k x)). Qed.
Lemma lem7158813 {B : Type'} (x : B) (t : B -> Prop) : (term72 B x t) = (term72 B x t).
Proof. exact (eq_refl (term72 B x t)). Qed.
Lemma lem7158814 {B : Type'} (k : B -> nat) (x : B) (t : B -> Prop) : (term232 B t k x) = (term238 B x t).
Proof. exact (MK_COMB (@lem7158813 B x t) (@lem7158812 B k x)). Qed.
Lemma lem7158816 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7158817 {B : Type'} (x : B) (t : B -> Prop) : (term238 B x t) = True.
Proof. exact (@lem7158816 (@IN B x t)). Qed.
Lemma lem7158818 {B : Type'} (t : B -> Prop) (k : B -> nat) (x : B) : (term232 B t k x) = True.
Proof. exact (TRANS (@lem7158814 B k x t) (@lem7158817 B x t)). Qed.
Lemma lem7158819 {B : Type'} (t : B -> Prop) (k : B -> nat) : (term234 B t k) = (term239 B).
Proof. exact (fun_ext (fun x : B => @lem7158818 B t k x)). Qed.
Lemma lem7158820 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7158821 {B : Type'} (t : B -> Prop) (k : B -> nat) : (term236 B t k) = (term240 B).
Proof. exact (MK_COMB (@lem7158820 B) (@lem7158819 B t k)). Qed.
Lemma lem7158823 {A : Type'} (t : Prop) : (term241 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7158824 {B : Type'} (t : Prop) : (term241 B t) = t.
Proof. exact (@lem7158823 B t). Qed.
Lemma lem7158825 {B : Type'} : (term240 B) = True.
Proof. exact (@lem7158824 B True). Qed.
Lemma lem7158826 {B : Type'} (t : B -> Prop) (k : B -> nat) : (term236 B t k) = True.
Proof. exact (TRANS (@lem7158821 B t k) (@lem7158825 B)). Qed.
Lemma lem7158827 {B : Type'} (t : B -> Prop) (k : B -> nat) : True = (term236 B t k).
Proof. exact (SYM (@lem7158826 B t k)). Qed.
Lemma lem7158828 {B : Type'} (t : B -> Prop) (k : B -> nat) : term236 B t k.
Proof. exact (EQ_MP (@lem7158827 B t k) (@lem0)). Qed.
Lemma lem7158829 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : term235 A B t s R k.
Proof. exact (EQ_MP (@lem7158792 A B R k s t h1 h2) (@lem7158828 B t k)). Qed.
Lemma lem7158830 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : (term166 A B t s R) = (term48 B t k).
Proof. exact (@lem7158545 A B s R t k (@lem7158829 A B R k s t h1 h2)). Qed.
Lemma lem7158831 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : (term118 A B s t R) = (term48 B t k).
Proof. exact (EQ_MP (@lem7158541 A B R k s t h2) (@lem7158830 A B R k s t h1 h2)). Qed.
Lemma lem7158832 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : term242 A B s R t k.
Proof. exact (conj (@lem7158436 A B R s t h2) (@lem7158831 A B R k s t h1 h2)). Qed.
Lemma lem7158833 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : term243 A B s R t k.
Proof. exact (ex_intro (term244 A B s R t k) (term118 A B s t R) (@lem7158832 A B R k s t h1 h2)). Qed.
Lemma lem7158834 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : (term47 A B s t R) = (term48 B t k).
Proof. exact (@lem7158223 A B s R t k (@lem7158833 A B R k s t h1 h2)). Qed.
Lemma lem7158835 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term43 A B t s R k) : term44 A B t s R k.
Proof. exact (proj2 (@lem7158217 A B t s R k h1)). Qed.
Lemma lem7158836 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term43 A B t s R k) : term51 A B s t.
Proof. exact (proj1 (@lem7158217 A B t s R k h1)). Qed.
Lemma lem7158837 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : (term44 A B t s R k) = ((term47 A B s t R) = (term48 B t k)).
Proof. exact (prop_ext (fun h3 : term44 A B t s R k => @lem7158834 A B R k s t h1 h2) (fun h3 : (term47 A B s t R) = (term48 B t k) => @lem7158218 A B t s R k h1)). Qed.
Lemma lem7158838 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : (term47 A B s t R) = (term48 B t k).
Proof. exact (EQ_MP (@lem7158837 A B R k s t h1 h2) (@lem7158218 A B t s R k h1)). Qed.
Lemma lem7158839 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : (term51 A B s t) = ((term47 A B s t R) = (term48 B t k)).
Proof. exact (prop_ext (fun h3 : term51 A B s t => @lem7158838 A B R k s t h1 h2) (fun h3 : (term47 A B s t R) = (term48 B t k) => @lem7158219 A B s t h2)). Qed.
Lemma lem7158840 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term44 A B t s R k) (h2 : term51 A B s t) : (term47 A B s t R) = (term48 B t k).
Proof. exact (EQ_MP (@lem7158839 A B R k s t h1 h2) (@lem7158219 A B s t h2)). Qed.
Lemma lem7158841 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term51 A B s t) (h2 : term43 A B t s R k) : (term44 A B t s R k) = ((term47 A B s t R) = (term48 B t k)).
Proof. exact (prop_ext (fun h3 : term44 A B t s R k => @lem7158840 A B R k s t h3 h1) (fun h3 : (term47 A B s t R) = (term48 B t k) => @lem7158835 A B t s R k h2)). Qed.
Lemma lem7158842 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term51 A B s t) (h2 : term43 A B t s R k) : (term47 A B s t R) = (term48 B t k).
Proof. exact (EQ_MP (@lem7158841 A B t s R k h1 h2) (@lem7158835 A B t s R k h2)). Qed.
Lemma lem7158843 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term43 A B t s R k) : (term51 A B s t) = ((term47 A B s t R) = (term48 B t k)).
Proof. exact (prop_ext (fun h2 : term51 A B s t => @lem7158842 A B t s R k h2 h1) (fun h2 : (term47 A B s t R) = (term48 B t k) => @lem7158836 A B t s R k h1)). Qed.
Lemma lem7158844 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term43 A B t s R k) : (term47 A B s t R) = (term48 B t k).
Proof. exact (EQ_MP (@lem7158843 A B t s R k h1) (@lem7158836 A B t s R k h1)). Qed.
Lemma lem7158845 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : term50 A B s R t k.
Proof. exact (fun h0 : term43 A B t s R k => @lem7158844 A B t s R k h0). Qed.
Lemma lem7158846 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : term49 A B s R t k.
Proof. exact (EQ_MP (@lem7158216 A B s R t k) (@lem7158845 A B s R t k)). Qed.
Lemma lem7158851 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term245 A B s R t.
Proof. exact (fun k : B -> nat => @lem7158846 A B s R t k). Qed.
Lemma lem7158856 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : term246 A B s R.
Proof. exact (fun t : B -> Prop => @lem7158851 A B s R t). Qed.
Lemma lem7158861 {A B : Type'} (R : type1413 A B) : term247 A B R.
Proof. exact (fun s : A -> Prop => @lem7158856 A B s R). Qed.
Lemma lem7158866 {A B : Type'} : term248 A B.
Proof. exact (fun R : type1413 A B => @lem7158861 A B R). Qed.
