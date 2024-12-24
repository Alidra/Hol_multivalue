Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_INJECTION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import IN_IMAGE_spec.
Require Import ITERATE_BIJECTION_spec.
Require Import SUBSET_spec.
Require Import SURJECTIVE_IFF_INJECTIVE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18392_spec.
Require Import thm18393_spec.
Require Import thm1842_spec.
Require Import thm1856_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm7_spec.
Lemma lem6000072 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6000073 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem6000074 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem6000073 t1) (@lem6000072 t1)). Qed.
Lemma lem6000075 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem6000074 t1 t2). Qed.
Lemma lem6000076 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem6000077 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem6000076 t1 t2) (@lem6000075 t1 t2)). Qed.
Lemma lem6000078 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem6000077 t1 t2 t3). Qed.
Lemma lem6000079 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem6000080 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem6000079 t1 t2 t3) (@lem6000078 t1 t2 t3)). Qed.
Lemma lem6000081 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem6000080 t1 t2 t3)). Qed.
Lemma lem6000082 {A : Type'} : term7 A.
Proof. exact (@lem4945027 A). Qed.
Lemma lem6000083 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (@lem6000082 A s). Qed.
Lemma lem6000084 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (eq_refl (term8 A s)). Qed.
Lemma lem6000085 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem6000084 A s) (@lem6000083 A s)). Qed.
Lemma lem6000086 {A : Type'} (s : A -> Prop) (p : A -> A) : term10 A s p.
Proof. exact (@lem6000085 A s p). Qed.
Lemma lem6000087 {A : Type'} (s : A -> Prop) (p : A -> A) : (term10 A s p) = (term11 A s p).
Proof. exact (eq_refl (term10 A s p)). Qed.
Lemma lem6000088 {A : Type'} (s : A -> Prop) (p : A -> A) : term11 A s p.
Proof. exact (EQ_MP (@lem6000087 A s p) (@lem6000086 A s p)). Qed.
Lemma lem6000089 {A B : Type'} (op : type1400 B) : term12 A B op.
Proof. exact (@lem5947359 A B op). Qed.
Lemma lem6000090 {A B : Type'} (op : type1400 B) : (term12 A B op) = (term13 A B op).
Proof. exact (eq_refl (term12 A B op)). Qed.
Lemma lem6000092 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6000093 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term14 A s p) : term14 A s p.
Proof. exact (h1). Qed.
Lemma lem6000094 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term15 A s p) : term15 A s p.
Proof. exact (h1). Qed.
Lemma lem6000095 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6000096 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term16 A s p.
Proof. exact (h1). Qed.
Lemma lem6000097 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term17 A p s.
Proof. exact (h1). Qed.
Lemma lem6000098 {A B : Type'} (p : A -> A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : (term18 A B op s f p) = (@iterate B A op s f)) : (term18 A B op s f p) = (@iterate B A op s f).
Proof. exact (h1). Qed.
Lemma lem6000099 {A B : Type'} (p : A -> A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : (term18 A B op s f p) = (@iterate B A op s f)) : (@iterate B A op s f) = (term18 A B op s f p).
Proof. exact (SYM (@lem6000098 A B p op s f h1)). Qed.
Lemma lem6000100 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (p : A -> A) (h1 : (@iterate B A op s f) = (term18 A B op s f p)) : (@iterate B A op s f) = (term18 A B op s f p).
Proof. exact (h1). Qed.
Lemma lem6000101 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (p : A -> A) (h1 : (@iterate B A op s f) = (term18 A B op s f p)) : (term18 A B op s f p) = (@iterate B A op s f).
Proof. exact (SYM (@lem6000100 A B op s f p h1)). Qed.
Lemma lem6000102 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (p : A -> A) : ((term18 A B op s f p) = (@iterate B A op s f)) = ((@iterate B A op s f) = (term18 A B op s f p)).
Proof. exact (prop_ext (fun h1 : (term18 A B op s f p) = (@iterate B A op s f) => @lem6000099 A B p op s f h1) (fun h1 : (@iterate B A op s f) = (term18 A B op s f p) => @lem6000101 A B op s f p h1)). Qed.
Lemma lem6000103 {A B : Type'} (p : A -> A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : ((@iterate B A op s f) = (term18 A B op s f p)) = ((term18 A B op s f p) = (@iterate B A op s f)).
Proof. exact (SYM (@lem6000102 A B op s f p)). Qed.
Lemma lem6000111 {A B : Type'} (op : type1400 B) : term13 A B op.
Proof. exact (EQ_MP (@lem6000090 A B op) (@lem6000089 A B op)). Qed.
Lemma lem6000112 {A B : Type'} (op : type1400 B) : term13 A B op.
Proof. exact (@lem6000111 A B op). Qed.
Lemma lem6000113 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term19 A B op.
Proof. exact (@lem6000112 A B op (@lem6000092 B op h1)). Qed.
Lemma lem6000114 {A B : Type'} (op : type1400 B) (h1 : term19 A B op) : term19 A B op.
Proof. exact (h1). Qed.
Lemma lem6000115 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term19 A B op) : term20 A B op f.
Proof. exact (@lem6000114 A B op h1 f). Qed.
Lemma lem6000116 {A B : Type'} (op : type1400 B) (f : A -> B) : (term20 A B op f) = (term21 A B op f).
Proof. exact (eq_refl (term20 A B op f)). Qed.
Lemma lem6000117 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term19 A B op) : term21 A B op f.
Proof. exact (EQ_MP (@lem6000116 A B op f) (@lem6000115 A B f op h1)). Qed.
Lemma lem6000118 {A B : Type'} (f : A -> B) (p : A -> A) (op : type1400 B) (h1 : term19 A B op) : term22 A B op f p.
Proof. exact (@lem6000117 A B f op h1 p). Qed.
Lemma lem6000119 {A B : Type'} (op : type1400 B) (f : A -> B) (p : A -> A) : (term22 A B op f p) = (term23 A B op f p).
Proof. exact (eq_refl (term22 A B op f p)). Qed.
Lemma lem6000120 {A B : Type'} (f : A -> B) (p : A -> A) (op : type1400 B) (h1 : term19 A B op) : term23 A B op f p.
Proof. exact (EQ_MP (@lem6000119 A B op f p) (@lem6000118 A B f p op h1)). Qed.
Lemma lem6000121 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term19 A B op) : term24 A B op f p s.
Proof. exact (@lem6000120 A B f p op h1 s). Qed.
Lemma lem6000122 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (p : A -> A) : (term24 A B op f p s) = (term25 A B op s f p).
Proof. exact (eq_refl (term24 A B op f p s)). Qed.
Lemma lem6000123 {A B : Type'} (s : A -> Prop) (f : A -> B) (p : A -> A) (op : type1400 B) (h1 : term19 A B op) : term25 A B op s f p.
Proof. exact (EQ_MP (@lem6000122 A B op s f p) (@lem6000121 A B f p s op h1)). Qed.
Lemma lem6000124 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term26 A s p) : term26 A s p.
Proof. exact (h1). Qed.
Lemma lem6000125 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : term19 A B op) (h2 : term26 A s p) : (@iterate B A op s f) = (term18 A B op s f p).
Proof. exact (@lem6000123 A B s f p op h1 (@lem6000124 A s p h2)). Qed.
Lemma lem6000126 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (p : A -> A) (h1 : term26 A s p) : term27 A B op s f p.
Proof. exact (fun h0 : term19 A B op => @lem6000125 A B f op s p h0 h1). Qed.
Lemma lem6000127 {A B : Type'} (op : type1400 B) (h1 : term19 A B op) : term19 A B op.
Proof. exact (h1). Qed.
Lemma lem6000128 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : term19 A B op) (h2 : term26 A s p) : (@iterate B A op s f) = (term18 A B op s f p).
Proof. exact (@lem6000126 A B op f s p h2 (@lem6000127 A B op h1)). Qed.
Lemma lem6000129 {A B : Type'} (s : A -> Prop) (f : A -> B) (p : A -> A) (op : type1400 B) (h1 : term19 A B op) : term25 A B op s f p.
Proof. exact (fun h0 : term26 A s p => @lem6000128 A B f op s p h1 h0). Qed.
Lemma lem6000130 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term19 A B op) : term28 A B op s f.
Proof. exact (fun p : A -> A => @lem6000129 A B s f p op h1). Qed.
Lemma lem6000131 {A B : Type'} (s : A -> Prop) (op : type1400 B) (h1 : term19 A B op) : term29 A B op s.
Proof. exact (fun f : A -> B => @lem6000130 A B s f op h1). Qed.
Lemma lem6000132 {A B : Type'} (op : type1400 B) (h1 : term19 A B op) : term30 A B op.
Proof. exact (fun s : A -> Prop => @lem6000131 A B s op h1). Qed.
Lemma lem6000133 {A B : Type'} (op : type1400 B) : term31 A B op.
Proof. exact (fun h0 : term19 A B op => @lem6000132 A B op h0). Qed.
Lemma lem6000134 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term30 A B op.
Proof. exact (@lem6000133 A B op (@lem6000113 A B op h1)). Qed.
Lemma lem6000135 {A B : Type'} (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term32 A B op s.
Proof. exact (@lem6000134 A B op h1 s). Qed.
Lemma lem6000136 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (term32 A B op s) = (term29 A B op s).
Proof. exact (eq_refl (term32 A B op s)). Qed.
Lemma lem6000137 {A B : Type'} (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term29 A B op s.
Proof. exact (EQ_MP (@lem6000136 A B op s) (@lem6000135 A B s op h1)). Qed.
Lemma lem6000138 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term33 A B op s f.
Proof. exact (@lem6000137 A B s op h1 f). Qed.
Lemma lem6000139 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term33 A B op s f) = (term28 A B op s f).
Proof. exact (eq_refl (term33 A B op s f)). Qed.
Lemma lem6000140 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term28 A B op s f.
Proof. exact (EQ_MP (@lem6000139 A B op s f) (@lem6000138 A B s f op h1)). Qed.
Lemma lem6000141 {A B : Type'} (s : A -> Prop) (f : A -> B) (p : A -> A) (op : type1400 B) (h1 : @monoidal B op) : term34 A B op s f p.
Proof. exact (@lem6000140 A B s f op h1 p). Qed.
Lemma lem6000142 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (p : A -> A) : (term34 A B op s f p) = (term25 A B op s f p).
Proof. exact (eq_refl (term34 A B op s f p)). Qed.
Lemma lem6000145 {A B : Type'} (s : A -> Prop) (f : A -> B) (p : A -> A) (op : type1400 B) (h1 : @monoidal B op) : term25 A B op s f p.
Proof. exact (EQ_MP (@lem6000142 A B op s f p) (@lem6000141 A B s f p op h1)). Qed.
Lemma lem6000146 {A B : Type'} (s : A -> Prop) (f : A -> B) (p : A -> A) (op : type1400 B) (h1 : @monoidal B op) : term25 A B op s f p.
Proof. exact (@lem6000145 A B s f p op h1). Qed.
Lemma lem6000147 {A B : Type'} (y : B) : term35 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem6000148 {A B : Type'} (y : B) : (term35 A B y) = (term36 A B y).
Proof. exact (eq_refl (term35 A B y)). Qed.
Lemma lem6000149 {A B : Type'} (y : B) : term36 A B y.
Proof. exact (EQ_MP (@lem6000148 A B y) (@lem6000147 A B y)). Qed.
Lemma lem6000150 {A B : Type'} (y : B) (s : A -> Prop) : term37 A B y s.
Proof. exact (@lem6000149 A B y s). Qed.
Lemma lem6000151 {A B : Type'} (y : B) (s : A -> Prop) : (term37 A B y s) = (term38 A B y s).
Proof. exact (eq_refl (term37 A B y s)). Qed.
Lemma lem6000152 {A B : Type'} (y : B) (s : A -> Prop) : term38 A B y s.
Proof. exact (EQ_MP (@lem6000151 A B y s) (@lem6000150 A B y s)). Qed.
Lemma lem6000153 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term39 A B y s f.
Proof. exact (@lem6000152 A B y s f). Qed.
Lemma lem6000154 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term39 A B y s f) = ((term40 A B y f s) = (term41 A B y f s)).
Proof. exact (eq_refl (term39 A B y s f)). Qed.
Lemma lem6000156 {A : Type'} (s : A -> Prop) : term42 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem6000157 {A : Type'} (s : A -> Prop) : (term42 A s) = (term43 A s).
Proof. exact (eq_refl (term42 A s)). Qed.
Lemma lem6000158 {A : Type'} (s : A -> Prop) : term43 A s.
Proof. exact (EQ_MP (@lem6000157 A s) (@lem6000156 A s)). Qed.
Lemma lem6000159 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term44 A s t.
Proof. exact (@lem6000158 A s t). Qed.
Lemma lem6000160 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term44 A s t) = ((@SUBSET A s t) = (term45 A s t)).
Proof. exact (eq_refl (term44 A s t)). Qed.
Lemma lem6000162 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6000164 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term46 A p s x.
Proof. exact (@lem6000097 A p s h1 x). Qed.
Lemma lem6000165 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term46 A p s x) = (term47 A p x s).
Proof. exact (eq_refl (term46 A p s x)). Qed.
Lemma lem6000166 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term47 A p x s.
Proof. exact (EQ_MP (@lem6000165 A p x s) (@lem6000164 A x p s h1)). Qed.
Lemma lem6000167 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term47 A p x s) = ((term47 A p x s) = True).
Proof. exact (@lem7 (term47 A p x s)). Qed.
Lemma lem6000169 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term48 A s p x.
Proof. exact (@lem6000096 A s p h1 x). Qed.
Lemma lem6000170 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) : (term48 A s p x) = (term49 A s p x).
Proof. exact (eq_refl (term48 A s p x)). Qed.
Lemma lem6000171 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term49 A s p x.
Proof. exact (EQ_MP (@lem6000170 A s p x) (@lem6000169 A x s p h1)). Qed.
Lemma lem6000172 {A : Type'} (x : A) (y : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term50 A s p x y.
Proof. exact (@lem6000171 A x s p h1 y). Qed.
Lemma lem6000173 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term50 A s p x y) = (term51 A s p x y).
Proof. exact (eq_refl (term50 A s p x y)). Qed.
Lemma lem6000174 {A : Type'} (x : A) (y : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term51 A s p x y.
Proof. exact (EQ_MP (@lem6000173 A s p x y) (@lem6000172 A x y s p h1)). Qed.
Lemma lem6000175 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term51 A s p x y) = ((term51 A s p x y) = True).
Proof. exact (@lem7 (term51 A s p x y)). Qed.
Lemma lem6000184 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6000162 A s) (@lem6000095 A s h1)). Qed.
Lemma lem6000185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6000186 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term52 A s) = (and True).
Proof. exact (MK_COMB (@lem6000185) (@lem6000184 A s h1)). Qed.
Lemma lem6000188 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term45 A s t).
Proof. exact (EQ_MP (@lem6000160 A s t) (@lem6000159 A s t)). Qed.
Lemma lem6000189 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term45 A s t).
Proof. exact (@lem6000188 A s t). Qed.
Lemma lem6000190 {A : Type'} (p : A -> A) (s : A -> Prop) : (term53 A p s) = (term54 A p s).
Proof. exact (@lem6000189 A (@IMAGE A A p s) s). Qed.
Lemma lem6000198 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term40 A B y f s) = (term41 A B y f s).
Proof. exact (EQ_MP (@lem6000154 A B y f s) (@lem6000153 A B y s f)). Qed.
Lemma lem6000199 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term55 A y f s) = (term56 A y f s).
Proof. exact (@lem6000198 A A y f s). Qed.
Lemma lem6000200 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term55 A x p s) = (term56 A x p s).
Proof. exact (@lem6000199 A x p s). Qed.
Lemma lem6000209 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6000210 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term57 A x p s) = (term58 A x p s).
Proof. exact (MK_COMB (@lem6000209) (@lem6000200 A x p s)). Qed.
Lemma lem6000211 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem6000212 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term59 A p x s) = (term60 A p x s).
Proof. exact (MK_COMB (@lem6000210 A x p s) (@lem6000211 A x s)). Qed.
Lemma lem6000215 {A : Type'} (p : A -> A) (s : A -> Prop) : (term61 A p s) = (term62 A p s).
Proof. exact (fun_ext (fun x : A => @lem6000212 A p x s)). Qed.
Lemma lem6000216 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6000217 {A : Type'} (p : A -> A) (s : A -> Prop) : (term54 A p s) = (term63 A p s).
Proof. exact (MK_COMB (@lem6000216 A) (@lem6000215 A p s)). Qed.
Lemma lem6000222 {A : Type'} (p : A -> A) (s : A -> Prop) : (term53 A p s) = (term63 A p s).
Proof. exact (TRANS (@lem6000190 A p s) (@lem6000217 A p s)). Qed.
Lemma lem6000223 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term64 A p s) = (term65 A p s).
Proof. exact (MK_COMB (@lem6000186 A s h1) (@lem6000222 A p s)). Qed.
Lemma lem6000225 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6000226 {A : Type'} (p : A -> A) (s : A -> Prop) : (term65 A p s) = (term63 A p s).
Proof. exact (@lem6000225 (term63 A p s)). Qed.
Lemma lem6000241 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term64 A p s) = (term63 A p s).
Proof. exact (TRANS (@lem6000223 A p s h1) (@lem6000226 A p s)). Qed.
Lemma lem6000242 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6000243 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : (term66 A p s) = (term67 A p s).
Proof. exact (MK_COMB (@lem6000242) (@lem6000241 A p s h1)). Qed.
Lemma lem6000269 {A : Type'} (x : A) (y : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : (term51 A s p x y) = True.
Proof. exact (EQ_MP (@lem6000175 A s p x y) (@lem6000174 A x y s p h1)). Qed.
Lemma lem6000270 {A : Type'} (x : A) (y : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : (term51 A s p x y) = True.
Proof. exact (@lem6000269 A x y s p h1). Qed.
Lemma lem6000271 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : (term68 A s p x) = (term69 A).
Proof. exact (fun_ext (fun y : A => @lem6000270 A x y s p h1)). Qed.
Lemma lem6000272 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6000273 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : (term49 A s p x) = (term70 A).
Proof. exact (MK_COMB (@lem6000272 A) (@lem6000271 A x s p h1)). Qed.
Lemma lem6000275 {A : Type'} (t : Prop) : (term71 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6000276 {A : Type'} (t : Prop) : (term71 A t) = t.
Proof. exact (@lem6000275 A t). Qed.
Lemma lem6000277 {A : Type'} : (term70 A) = True.
Proof. exact (@lem6000276 A True). Qed.
Lemma lem6000278 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : (term49 A s p x) = True.
Proof. exact (TRANS (@lem6000273 A x s p h1) (@lem6000277 A)). Qed.
Lemma lem6000279 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : (term72 A s p) = (term69 A).
Proof. exact (fun_ext (fun x : A => @lem6000278 A x s p h1)). Qed.
Lemma lem6000280 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6000281 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : (term16 A s p) = (term70 A).
Proof. exact (MK_COMB (@lem6000280 A) (@lem6000279 A s p h1)). Qed.
Lemma lem6000283 {A : Type'} (t : Prop) : (term71 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6000284 {A : Type'} (t : Prop) : (term71 A t) = t.
Proof. exact (@lem6000283 A t). Qed.
Lemma lem6000285 {A : Type'} : (term70 A) = True.
Proof. exact (@lem6000284 A True). Qed.
Lemma lem6000286 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : (term16 A s p) = True.
Proof. exact (TRANS (@lem6000281 A s p h1) (@lem6000285 A)). Qed.
Lemma lem6000287 {A : Type'} (s : A -> Prop) (p : A -> A) : (term73 A s p) = (term73 A s p).
Proof. exact (eq_refl (term73 A s p)). Qed.
Lemma lem6000288 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : ((term74 A s p) = (term16 A s p)) = ((term74 A s p) = True).
Proof. exact (MK_COMB (@lem6000287 A s p) (@lem6000286 A s p h1)). Qed.
Lemma lem6000290 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem6000291 {A : Type'} (s : A -> Prop) (p : A -> A) : ((term74 A s p) = True) = (term74 A s p).
Proof. exact (@lem6000290 (term74 A s p)). Qed.
Lemma lem6000306 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : ((term74 A s p) = (term16 A s p)) = (term74 A s p).
Proof. exact (TRANS (@lem6000288 A s p h1) (@lem6000291 A s p)). Qed.
Lemma lem6000307 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term16 A s p) (h2 : @FINITE A s) : (term11 A s p) = (term75 A s p).
Proof. exact (MK_COMB (@lem6000243 A p s h2) (@lem6000306 A s p h1)). Qed.
Lemma lem6000310 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6000311 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term16 A s p) (h2 : @FINITE A s) : (term76 A s p) = (term77 A s p).
Proof. exact (MK_COMB (@lem6000310) (@lem6000307 A p s h1 h2)). Qed.
Lemma lem6000319 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : (term47 A p x s) = True.
Proof. exact (EQ_MP (@lem6000167 A p x s) (@lem6000166 A x p s h1)). Qed.
Lemma lem6000320 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : (term47 A p x s) = True.
Proof. exact (@lem6000319 A x p s h1). Qed.
Lemma lem6000321 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : (term78 A p s) = (term69 A).
Proof. exact (fun_ext (fun x : A => @lem6000320 A x p s h1)). Qed.
Lemma lem6000322 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6000323 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : (term17 A p s) = (term70 A).
Proof. exact (MK_COMB (@lem6000322 A) (@lem6000321 A p s h1)). Qed.
Lemma lem6000325 {A : Type'} (t : Prop) : (term71 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6000326 {A : Type'} (t : Prop) : (term71 A t) = t.
Proof. exact (@lem6000325 A t). Qed.
Lemma lem6000327 {A : Type'} : (term70 A) = True.
Proof. exact (@lem6000326 A True). Qed.
Lemma lem6000328 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : (term17 A p s) = True.
Proof. exact (TRANS (@lem6000323 A p s h1) (@lem6000327 A)). Qed.
Lemma lem6000329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6000330 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : (term79 A p s) = (and True).
Proof. exact (MK_COMB (@lem6000329) (@lem6000328 A p s h1)). Qed.
Lemma lem6000341 {A : Type'} (s : A -> Prop) (p : A -> A) : (term80 A s p) = (term80 A s p).
Proof. exact (eq_refl (term80 A s p)). Qed.
Lemma lem6000342 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : (term26 A s p) = (term81 A s p).
Proof. exact (MK_COMB (@lem6000330 A p s h1) (@lem6000341 A s p)). Qed.
Lemma lem6000344 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6000345 {A : Type'} (s : A -> Prop) (p : A -> A) : (term81 A s p) = (term80 A s p).
Proof. exact (@lem6000344 (term80 A s p)). Qed.
Lemma lem6000356 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : (term26 A s p) = (term80 A s p).
Proof. exact (TRANS (@lem6000342 A p s h1) (@lem6000345 A s p)). Qed.
Lemma lem6000357 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) : (term82 A s p) = (term83 A s p).
Proof. exact (MK_COMB (@lem6000311 A p s h1 h3) (@lem6000356 A p s h2)). Qed.
Lemma lem6000360 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) : (term83 A s p) = (term82 A s p).
Proof. exact (SYM (@lem6000357 A p s h1 h2 h3)). Qed.
Lemma lem6000362 (p : Prop) : p = (term84 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6000363 {A : Type'} (s : A -> Prop) (p : A -> A) : (term83 A s p) = (term85 A s p).
Proof. exact (@lem6000362 (term83 A s p)). Qed.
Lemma lem6000364 {A : Type'} (s : A -> Prop) (p : A -> A) : (term85 A s p) = (term83 A s p).
Proof. exact (SYM (@lem6000363 A s p)). Qed.
Lemma lem6000365 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term86 A s p) : term86 A s p.
Proof. exact (h1). Qed.
Lemma lem6000368 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term87 A s p) : term87 A s p.
Proof. exact (h1). Qed.
Lemma lem6000369 {A : Type'} (s : A -> Prop) (p : A -> A) : term88 A s p.
Proof. exact (fun h0 : term87 A s p => @lem6000368 A s p h0). Qed.
Lemma lem6000370 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term88 A s p) : term88 A s p.
Proof. exact (h1). Qed.
Lemma lem6000371 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term87 A s p) : term87 A s p.
Proof. exact (h1). Qed.
Lemma lem6000372 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term87 A s p) (h2 : term88 A s p) : term87 A s p.
Proof. exact (@lem6000370 A s p h2 (@lem6000371 A s p h1)). Qed.
Lemma lem6000373 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term87 A s p) : term89 A s p.
Proof. exact (fun h0 : term88 A s p => @lem6000372 A s p h1 h0). Qed.
Lemma lem6000374 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term88 A s p) : term88 A s p.
Proof. exact (h1). Qed.
Lemma lem6000375 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term87 A s p) (h2 : term88 A s p) : term87 A s p.
Proof. exact (@lem6000373 A s p h1 (@lem6000374 A s p h2)). Qed.
Lemma lem6000376 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term88 A s p) : term88 A s p.
Proof. exact (fun h0 : term87 A s p => @lem6000375 A s p h0 h1). Qed.
Lemma lem6000377 {A : Type'} (s : A -> Prop) (p : A -> A) : term90 A s p.
Proof. exact (fun h0 : term88 A s p => @lem6000376 A s p h0). Qed.
Lemma lem6000380 {A : Type'} (s : A -> Prop) (p : A -> A) : term88 A s p.
Proof. exact (@lem6000377 A s p (@lem6000369 A s p)). Qed.
Lemma lem6000381 {A : Type'} (s : A -> Prop) (p : A -> A) : term88 A s p.
Proof. exact (@lem6000380 A s p). Qed.
Lemma lem6000417 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6000418 {A : Type'} (s : A -> Prop) (p : A -> A) : (term85 A s p) = (term91 A s p).
Proof. exact (@lem6000417 (term86 A s p)). Qed.
Lemma lem6000420 (t : Prop) : (term92 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6000421 {A : Type'} (s : A -> Prop) (p : A -> A) : (term91 A s p) = (term83 A s p).
Proof. exact (@lem6000420 (term83 A s p)). Qed.
Lemma lem6000424 {A : Type'} (s : A -> Prop) (p : A -> A) : (term85 A s p) = (term83 A s p).
Proof. exact (TRANS (@lem6000418 A s p) (@lem6000421 A s p)). Qed.
Lemma lem6000547 {A : Type'} (s : A -> Prop) (p : A -> A) : (term93 A s p) = (term93 A s p).
Proof. exact (eq_refl (term93 A s p)). Qed.
Lemma lem6000548 {A : Type'} (s : A -> Prop) (p : A -> A) : (term94 A s p) = (term95 A s p).
Proof. exact (MK_COMB (@lem6000547 A s p) (@lem6000424 A s p)). Qed.
Lemma lem6000551 {A : Type'} (p : A -> A) (s : A -> Prop) : (term96 A p s) = (term96 A p s).
Proof. exact (eq_refl (term96 A p s)). Qed.
Lemma lem6000552 {A : Type'} (s : A -> Prop) (p : A -> A) : (term97 A s p) = (term98 A s p).
Proof. exact (MK_COMB (@lem6000551 A p s) (@lem6000548 A s p)). Qed.
Lemma lem6000555 {A : Type'} (s : A -> Prop) : (term99 A s) = (term99 A s).
Proof. exact (eq_refl (term99 A s)). Qed.
Lemma lem6000556 {A : Type'} (s : A -> Prop) (p : A -> A) : (term87 A s p) = (term100 A s p).
Proof. exact (MK_COMB (@lem6000555 A s) (@lem6000552 A s p)). Qed.
Lemma lem6000559 {A : Type'} (p : A -> A) : (term101 A p) = (term102 A p).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6000556 A s p)). Qed.
Lemma lem6000560 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6000561 {A : Type'} (p : A -> A) : (term103 A p) = (term104 A p).
Proof. exact (MK_COMB (@lem6000560 A) (@lem6000559 A p)). Qed.
Lemma lem6000566 {A : Type'} : (term105 A) = (term106 A).
Proof. exact (fun_ext (fun p : A -> A => @lem6000561 A p)). Qed.
Lemma lem6000567 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem6000576 {A : Type'} : (term107 A) = (term108 A).
Proof. exact (MK_COMB (@lem6000567 A) (@lem6000566 A)). Qed.
Lemma lem6000581 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term109 A s p x y) = (term109 A s p x y).
Proof. exact (eq_refl (term109 A s p x y)). Qed.
Lemma lem6000582 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term110 A s p y) = (term110 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6000581 A s p x y)). Qed.
Lemma lem6000583 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem6000584 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term111 A s p y) = (term111 A s p y).
Proof. exact (MK_COMB (@lem6000583 A) (@lem6000582 A s p y)). Qed.
Lemma lem6000587 {A : Type'} (y : A) (s : A -> Prop) : (term112 A y s) = (term112 A y s).
Proof. exact (eq_refl (term112 A y s)). Qed.
Lemma lem6000588 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term113 A s p y) = (term113 A s p y).
Proof. exact (MK_COMB (@lem6000587 A y s) (@lem6000584 A s p y)). Qed.
Lemma lem6000589 {A : Type'} (s : A -> Prop) (p : A -> A) : (term114 A s p) = (term114 A s p).
Proof. exact (fun_ext (fun y : A => @lem6000588 A s p y)). Qed.
Lemma lem6000590 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6000591 {A : Type'} (s : A -> Prop) (p : A -> A) : (term80 A s p) = (term80 A s p).
Proof. exact (MK_COMB (@lem6000590 A) (@lem6000589 A s p)). Qed.
Lemma lem6000596 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term109 A s p x y) = (term109 A s p x y).
Proof. exact (eq_refl (term109 A s p x y)). Qed.
Lemma lem6000597 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term110 A s p y) = (term110 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6000596 A s p x y)). Qed.
Lemma lem6000598 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6000599 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term115 A s p y) = (term115 A s p y).
Proof. exact (MK_COMB (@lem6000598 A) (@lem6000597 A s p y)). Qed.
Lemma lem6000602 {A : Type'} (y : A) (s : A -> Prop) : (term112 A y s) = (term112 A y s).
Proof. exact (eq_refl (term112 A y s)). Qed.
Lemma lem6000603 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term116 A s p y) = (term116 A s p y).
Proof. exact (MK_COMB (@lem6000602 A y s) (@lem6000599 A s p y)). Qed.
Lemma lem6000604 {A : Type'} (s : A -> Prop) (p : A -> A) : (term117 A s p) = (term117 A s p).
Proof. exact (fun_ext (fun y : A => @lem6000603 A s p y)). Qed.
Lemma lem6000605 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6000606 {A : Type'} (s : A -> Prop) (p : A -> A) : (term74 A s p) = (term74 A s p).
Proof. exact (MK_COMB (@lem6000605 A) (@lem6000604 A s p)). Qed.
Lemma lem6000607 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem6000612 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term118 A x p x' s) = (term118 A x p x' s).
Proof. exact (eq_refl (term118 A x p x' s)). Qed.
Lemma lem6000613 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term119 A x p s) = (term119 A x p s).
Proof. exact (fun_ext (fun x' : A => @lem6000612 A x p x' s)). Qed.
Lemma lem6000614 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6000615 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term56 A x p s) = (term56 A x p s).
Proof. exact (MK_COMB (@lem6000614 A) (@lem6000613 A x p s)). Qed.
Lemma lem6000616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6000617 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term58 A x p s) = (term58 A x p s).
Proof. exact (MK_COMB (@lem6000616) (@lem6000615 A x p s)). Qed.
Lemma lem6000618 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term60 A p x s) = (term60 A p x s).
Proof. exact (MK_COMB (@lem6000617 A x p s) (@lem6000607 A x s)). Qed.
Lemma lem6000619 {A : Type'} (p : A -> A) (s : A -> Prop) : (term62 A p s) = (term62 A p s).
Proof. exact (fun_ext (fun x : A => @lem6000618 A p x s)). Qed.
Lemma lem6000620 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6000621 {A : Type'} (p : A -> A) (s : A -> Prop) : (term63 A p s) = (term63 A p s).
Proof. exact (MK_COMB (@lem6000620 A) (@lem6000619 A p s)). Qed.
Lemma lem6000622 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6000623 {A : Type'} (p : A -> A) (s : A -> Prop) : (term67 A p s) = (term67 A p s).
Proof. exact (MK_COMB (@lem6000622) (@lem6000621 A p s)). Qed.
Lemma lem6000624 {A : Type'} (s : A -> Prop) (p : A -> A) : (term75 A s p) = (term75 A s p).
Proof. exact (MK_COMB (@lem6000623 A p s) (@lem6000606 A s p)). Qed.
Lemma lem6000625 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6000626 {A : Type'} (s : A -> Prop) (p : A -> A) : (term77 A s p) = (term77 A s p).
Proof. exact (MK_COMB (@lem6000625) (@lem6000624 A s p)). Qed.
Lemma lem6000627 {A : Type'} (s : A -> Prop) (p : A -> A) : (term83 A s p) = (term83 A s p).
Proof. exact (MK_COMB (@lem6000626 A s p) (@lem6000591 A s p)). Qed.
Lemma lem6000640 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term51 A s p x y) = (term51 A s p x y).
Proof. exact (eq_refl (term51 A s p x y)). Qed.
Lemma lem6000641 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) : (term68 A s p x) = (term68 A s p x).
Proof. exact (fun_ext (fun y : A => @lem6000640 A s p x y)). Qed.
Lemma lem6000642 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6000643 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) : (term49 A s p x) = (term49 A s p x).
Proof. exact (MK_COMB (@lem6000642 A) (@lem6000641 A s p x)). Qed.
Lemma lem6000644 {A : Type'} (s : A -> Prop) (p : A -> A) : (term72 A s p) = (term72 A s p).
Proof. exact (fun_ext (fun x : A => @lem6000643 A s p x)). Qed.
Lemma lem6000645 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6000646 {A : Type'} (s : A -> Prop) (p : A -> A) : (term16 A s p) = (term16 A s p).
Proof. exact (MK_COMB (@lem6000645 A) (@lem6000644 A s p)). Qed.
Lemma lem6000647 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6000648 {A : Type'} (s : A -> Prop) (p : A -> A) : (term93 A s p) = (term93 A s p).
Proof. exact (MK_COMB (@lem6000647) (@lem6000646 A s p)). Qed.
Lemma lem6000649 {A : Type'} (s : A -> Prop) (p : A -> A) : (term95 A s p) = (term95 A s p).
Proof. exact (MK_COMB (@lem6000648 A s p) (@lem6000627 A s p)). Qed.
Lemma lem6000654 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term47 A p x s) = (term47 A p x s).
Proof. exact (eq_refl (term47 A p x s)). Qed.
Lemma lem6000655 {A : Type'} (p : A -> A) (s : A -> Prop) : (term78 A p s) = (term78 A p s).
Proof. exact (fun_ext (fun x : A => @lem6000654 A p x s)). Qed.
Lemma lem6000656 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6000657 {A : Type'} (p : A -> A) (s : A -> Prop) : (term17 A p s) = (term17 A p s).
Proof. exact (MK_COMB (@lem6000656 A) (@lem6000655 A p s)). Qed.
Lemma lem6000658 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6000659 {A : Type'} (p : A -> A) (s : A -> Prop) : (term96 A p s) = (term96 A p s).
Proof. exact (MK_COMB (@lem6000658) (@lem6000657 A p s)). Qed.
Lemma lem6000660 {A : Type'} (s : A -> Prop) (p : A -> A) : (term98 A s p) = (term98 A s p).
Proof. exact (MK_COMB (@lem6000659 A p s) (@lem6000649 A s p)). Qed.
Lemma lem6000663 {A : Type'} (s : A -> Prop) : (term99 A s) = (term99 A s).
Proof. exact (eq_refl (term99 A s)). Qed.
Lemma lem6000664 {A : Type'} (s : A -> Prop) (p : A -> A) : (term100 A s p) = (term100 A s p).
Proof. exact (MK_COMB (@lem6000663 A s) (@lem6000660 A s p)). Qed.
Lemma lem6000665 {A : Type'} (p : A -> A) : (term102 A p) = (term102 A p).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6000664 A s p)). Qed.
Lemma lem6000666 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6000667 {A : Type'} (p : A -> A) : (term104 A p) = (term104 A p).
Proof. exact (MK_COMB (@lem6000666 A) (@lem6000665 A p)). Qed.
Lemma lem6000668 {A : Type'} : (term106 A) = (term106 A).
Proof. exact (fun_ext (fun p : A -> A => @lem6000667 A p)). Qed.
Lemma lem6000669 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem6000670 {A : Type'} : (term108 A) = (term108 A).
Proof. exact (MK_COMB (@lem6000669 A) (@lem6000668 A)). Qed.
Lemma lem6000763 {A : Type'} : (term107 A) = (term108 A).
Proof. exact (TRANS (@lem6000576 A) (@lem6000670 A)). Qed.
Lemma lem6000764 {A : Type'} : (term108 A) = (term107 A).
Proof. exact (SYM (@lem6000763 A)). Qed.
Lemma lem6000766 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term17 A p s.
Proof. exact (h1). Qed.
Lemma lem6000767 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term16 A s p.
Proof. exact (h1). Qed.
Lemma lem6000768 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term75 A s p) : term75 A s p.
Proof. exact (h1). Qed.
Lemma lem6000771 (p : Prop) : p = (term84 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6000772 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term111 A s p y) = (term120 A s p y).
Proof. exact (@lem6000771 (term111 A s p y)). Qed.
Lemma lem6000773 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term120 A s p y) = (term111 A s p y).
Proof. exact (SYM (@lem6000772 A s p y)). Qed.
Lemma lem6000774 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (h1 : term121 A s p y) : term121 A s p y.
Proof. exact (h1). Qed.
Lemma lem6000787 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term47 A p x s) = (term122 A p x s).
Proof. exact (@lem17265 (@IN A x s) (term123 A p x s)). Qed.
Lemma lem6000788 {A : Type'} (p : A -> A) (s : A -> Prop) : (term78 A p s) = (term124 A p s).
Proof. exact (fun_ext (fun x : A => @lem6000787 A p x s)). Qed.
Lemma lem6000789 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6000842 {A : Type'} (p : A -> A) (s : A -> Prop) : (term17 A p s) = (term125 A p s).
Proof. exact (MK_COMB (@lem6000789 A) (@lem6000788 A p s)). Qed.
Lemma lem6000843 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term125 A p s.
Proof. exact (EQ_MP (@lem6000842 A p s) (@lem6000766 A p s h1)). Qed.
Lemma lem6000851 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) : (term126 A s x p y) = (term127 A s x p y).
Proof. exact (@lem17045 (@IN A y s) ((p x) = (p y))). Qed.
Lemma lem6000853 {A : Type'} (x : A) (s : A -> Prop) : (term128 A x s) = (term128 A x s).
Proof. exact (eq_refl (term128 A x s)). Qed.
Lemma lem6000854 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) : (term129 A s x p y) = (term130 A s x p y).
Proof. exact (MK_COMB (@lem6000853 A x s) (@lem6000851 A s x p y)). Qed.
Lemma lem6000855 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) : (term131 A s x p y) = (term129 A s x p y).
Proof. exact (@lem17045 (@IN A x s) (term132 A s x p y)). Qed.
Lemma lem6000856 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) : (term131 A s x p y) = (term130 A s x p y).
Proof. exact (TRANS (@lem6000855 A s x p y) (@lem6000854 A s x p y)). Qed.
Lemma lem6000857 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem6000858 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6000859 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) : (term133 A s x p y) = (term134 A s x p y).
Proof. exact (MK_COMB (@lem6000858) (@lem6000856 A s x p y)). Qed.
Lemma lem6000860 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term135 A s p x y) = (term136 A s p x y).
Proof. exact (MK_COMB (@lem6000859 A s x p y) (@lem6000857 A x y)). Qed.
Lemma lem6000861 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term51 A s p x y) = (term135 A s p x y).
Proof. exact (@lem17265 (term137 A s x p y) (x = y)). Qed.
Lemma lem6000862 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term51 A s p x y) = (term136 A s p x y).
Proof. exact (TRANS (@lem6000861 A s p x y) (@lem6000860 A s p x y)). Qed.
Lemma lem6000863 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) : (term68 A s p x) = (term138 A s p x).
Proof. exact (fun_ext (fun y : A => @lem6000862 A s p x y)). Qed.
Lemma lem6000864 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6000865 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) : (term49 A s p x) = (term139 A s p x).
Proof. exact (MK_COMB (@lem6000864 A) (@lem6000863 A s p x)). Qed.
Lemma lem6000866 {A : Type'} (s : A -> Prop) (p : A -> A) : (term72 A s p) = (term140 A s p).
Proof. exact (fun_ext (fun x : A => @lem6000865 A s p x)). Qed.
Lemma lem6000867 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6000924 {A : Type'} (s : A -> Prop) (p : A -> A) : (term16 A s p) = (term141 A s p).
Proof. exact (MK_COMB (@lem6000867 A) (@lem6000866 A s p)). Qed.
Lemma lem6000925 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term141 A s p.
Proof. exact (EQ_MP (@lem6000924 A s p) (@lem6000767 A s p h1)). Qed.
Lemma lem6000930 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term118 A x p x' s) = (term118 A x p x' s).
Proof. exact (eq_refl (term118 A x p x' s)). Qed.
Lemma lem6000931 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term119 A x p s) = (term119 A x p s).
Proof. exact (fun_ext (fun x' : A => @lem6000930 A x p x' s)). Qed.
Lemma lem6000932 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6000933 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term56 A x p s) = (term56 A x p s).
Proof. exact (MK_COMB (@lem6000932 A) (@lem6000931 A x p s)). Qed.
Lemma lem6000934 {A : Type'} (x : A) (s : A -> Prop) : (term142 A x s) = (term142 A x s).
Proof. exact (eq_refl (term142 A x s)). Qed.
Lemma lem6000935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6000936 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term143 A x p s) = (term143 A x p s).
Proof. exact (MK_COMB (@lem6000935) (@lem6000933 A x p s)). Qed.
Lemma lem6000937 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term144 A p x s) = (term144 A p x s).
Proof. exact (MK_COMB (@lem6000936 A x p s) (@lem6000934 A x s)). Qed.
Lemma lem6000938 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term145 A p x s) = (term144 A p x s).
Proof. exact (@lem17362 (term56 A x p s) (@IN A x s)). Qed.
Lemma lem6000939 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term145 A p x s) = (term144 A p x s).
Proof. exact (TRANS (@lem6000938 A p x s) (@lem6000937 A p x s)). Qed.
Lemma lem6000940 {A : Type'} (P : A -> Prop) : (term146 A P) = (term147 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6000941 {A : Type'} (p : A -> A) (s : A -> Prop) : (term148 A p s) = (term149 A p s).
Proof. exact (@lem6000940 A (term62 A p s)). Qed.
Lemma lem6000942 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term150 A p s x) = (term60 A p x s).
Proof. exact (eq_refl (term150 A p s x)). Qed.
Lemma lem6000943 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6000944 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term151 A p s x) = (term145 A p x s).
Proof. exact (MK_COMB (@lem6000943) (@lem6000942 A p x s)). Qed.
Lemma lem6000945 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term151 A p s x) = (term144 A p x s).
Proof. exact (TRANS (@lem6000944 A p x s) (@lem6000939 A p x s)). Qed.
Lemma lem6000946 {A : Type'} (p : A -> A) (s : A -> Prop) : (term152 A p s) = (term153 A p s).
Proof. exact (fun_ext (fun x : A => @lem6000945 A p x s)). Qed.
Lemma lem6000947 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6000948 {A : Type'} (p : A -> A) (s : A -> Prop) : (term149 A p s) = (term154 A p s).
Proof. exact (MK_COMB (@lem6000947 A) (@lem6000946 A p s)). Qed.
Lemma lem6000949 {A : Type'} (p : A -> A) (s : A -> Prop) : (term148 A p s) = (term154 A p s).
Proof. exact (TRANS (@lem6000941 A p s) (@lem6000948 A p s)). Qed.
Lemma lem6000955 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term109 A s p x y) = (term109 A s p x y).
Proof. exact (eq_refl (term109 A s p x y)). Qed.
Lemma lem6000956 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term110 A s p y) = (term110 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6000955 A s p x y)). Qed.
Lemma lem6000957 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6000958 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term115 A s p y) = (term115 A s p y).
Proof. exact (MK_COMB (@lem6000957 A) (@lem6000956 A s p y)). Qed.
Lemma lem6000960 {A : Type'} (y : A) (s : A -> Prop) : (term128 A y s) = (term128 A y s).
Proof. exact (eq_refl (term128 A y s)). Qed.
Lemma lem6000961 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term155 A s p y) = (term155 A s p y).
Proof. exact (MK_COMB (@lem6000960 A y s) (@lem6000958 A s p y)). Qed.
Lemma lem6000962 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term116 A s p y) = (term155 A s p y).
Proof. exact (@lem17265 (@IN A y s) (term115 A s p y)). Qed.
Lemma lem6000963 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term116 A s p y) = (term155 A s p y).
Proof. exact (TRANS (@lem6000962 A s p y) (@lem6000961 A s p y)). Qed.
Lemma lem6000964 {A : Type'} (s : A -> Prop) (p : A -> A) : (term117 A s p) = (term156 A s p).
Proof. exact (fun_ext (fun y : A => @lem6000963 A s p y)). Qed.
Lemma lem6000965 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6000966 {A : Type'} (s : A -> Prop) (p : A -> A) : (term74 A s p) = (term157 A s p).
Proof. exact (MK_COMB (@lem6000965 A) (@lem6000964 A s p)). Qed.
Lemma lem6000967 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6000968 {A : Type'} (p : A -> A) (s : A -> Prop) : (term158 A p s) = (term159 A p s).
Proof. exact (MK_COMB (@lem6000967) (@lem6000949 A p s)). Qed.
Lemma lem6000969 {A : Type'} (s : A -> Prop) (p : A -> A) : (term160 A s p) = (term161 A s p).
Proof. exact (MK_COMB (@lem6000968 A p s) (@lem6000966 A s p)). Qed.
Lemma lem6000970 {A : Type'} (s : A -> Prop) (p : A -> A) : (term75 A s p) = (term160 A s p).
Proof. exact (@lem17265 (term63 A p s) (term74 A s p)). Qed.
Lemma lem6000971 {A : Type'} (s : A -> Prop) (p : A -> A) : (term75 A s p) = (term161 A s p).
Proof. exact (TRANS (@lem6000970 A s p) (@lem6000969 A s p)). Qed.
Lemma lem6001166 {A : Type'} (P : A -> Prop) (Q : Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6001167 {A : Type'} (P : A -> Prop) (Q : Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (@lem6001166 A P Q). Qed.
Lemma lem6001168 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term164 A p x s) = (term165 A p x s).
Proof. exact (@lem6001167 A (term119 A x p s) (term142 A x s)). Qed.
Lemma lem6001169 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term166 A x p s x') = (term118 A x p x' s).
Proof. exact (eq_refl (term166 A x p s x')). Qed.
Lemma lem6001170 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term167 A x p s) = (term119 A x p s).
Proof. exact (fun_ext (fun x' : A => @lem6001169 A x p x' s)). Qed.
Lemma lem6001171 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001172 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term168 A x p s) = (term56 A x p s).
Proof. exact (MK_COMB (@lem6001171 A) (@lem6001170 A x p s)). Qed.
Lemma lem6001173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6001174 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term169 A x p s) = (term143 A x p s).
Proof. exact (MK_COMB (@lem6001173) (@lem6001172 A x p s)). Qed.
Lemma lem6001175 {A : Type'} (x : A) (s : A -> Prop) : (term142 A x s) = (term142 A x s).
Proof. exact (eq_refl (term142 A x s)). Qed.
Lemma lem6001176 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term164 A p x s) = (term144 A p x s).
Proof. exact (MK_COMB (@lem6001174 A x p s) (@lem6001175 A x s)). Qed.
Lemma lem6001177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6001178 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term170 A p x s) = (term171 A p x s).
Proof. exact (MK_COMB (@lem6001177) (@lem6001176 A p x s)). Qed.
Lemma lem6001179 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term166 A x p s x') = (term118 A x p x' s).
Proof. exact (eq_refl (term166 A x p s x')). Qed.
Lemma lem6001180 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6001181 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term172 A x p s x') = (term173 A x p x' s).
Proof. exact (MK_COMB (@lem6001180) (@lem6001179 A x p x' s)). Qed.
Lemma lem6001182 {A : Type'} (x : A) (s : A -> Prop) : (term142 A x s) = (term142 A x s).
Proof. exact (eq_refl (term142 A x s)). Qed.
Lemma lem6001183 {A : Type'} (p : A -> A) (x' : A) (x : A) (s : A -> Prop) : (term174 A p x' x s) = (term175 A p x' x s).
Proof. exact (MK_COMB (@lem6001181 A x p x' s) (@lem6001182 A x s)). Qed.
Lemma lem6001184 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term176 A p x s) = (term177 A p x s).
Proof. exact (fun_ext (fun x' : A => @lem6001183 A p x' x s)). Qed.
Lemma lem6001185 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001186 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term165 A p x s) = (term178 A p x s).
Proof. exact (MK_COMB (@lem6001185 A) (@lem6001184 A p x s)). Qed.
Lemma lem6001187 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : ((term164 A p x s) = (term165 A p x s)) = ((term144 A p x s) = (term178 A p x s)).
Proof. exact (MK_COMB (@lem6001178 A p x s) (@lem6001186 A p x s)). Qed.
Lemma lem6001188 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term144 A p x s) = (term178 A p x s).
Proof. exact (EQ_MP (@lem6001187 A p x s) (@lem6001168 A p x s)). Qed.
Lemma lem6001189 {A : Type'} (p : A -> A) (s : A -> Prop) : (term153 A p s) = (term179 A p s).
Proof. exact (fun_ext (fun x : A => @lem6001188 A p x s)). Qed.
Lemma lem6001190 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001191 {A : Type'} (p : A -> A) (s : A -> Prop) : (term154 A p s) = (term180 A p s).
Proof. exact (MK_COMB (@lem6001190 A) (@lem6001189 A p s)). Qed.
Lemma lem6001192 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6001193 {A : Type'} (p : A -> A) (s : A -> Prop) : (term159 A p s) = (term181 A p s).
Proof. exact (MK_COMB (@lem6001192) (@lem6001191 A p s)). Qed.
Lemma lem6001195 {A : Type'} (P : Prop) (Q : A -> Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6001196 {A : Type'} (P : Prop) (Q : A -> Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (@lem6001195 A P Q). Qed.
Lemma lem6001197 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term184 A s p y) = (term185 A s p y).
Proof. exact (@lem6001196 A (term142 A y s) (term110 A s p y)). Qed.
Lemma lem6001198 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term186 A s p y x) = (term109 A s p x y).
Proof. exact (eq_refl (term186 A s p y x)). Qed.
Lemma lem6001199 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term187 A s p y) = (term110 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6001198 A s p x y)). Qed.
Lemma lem6001200 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001201 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term188 A s p y) = (term115 A s p y).
Proof. exact (MK_COMB (@lem6001200 A) (@lem6001199 A s p y)). Qed.
Lemma lem6001202 {A : Type'} (y : A) (s : A -> Prop) : (term128 A y s) = (term128 A y s).
Proof. exact (eq_refl (term128 A y s)). Qed.
Lemma lem6001203 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term184 A s p y) = (term155 A s p y).
Proof. exact (MK_COMB (@lem6001202 A y s) (@lem6001201 A s p y)). Qed.
Lemma lem6001204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6001205 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term189 A s p y) = (term190 A s p y).
Proof. exact (MK_COMB (@lem6001204) (@lem6001203 A s p y)). Qed.
Lemma lem6001206 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term186 A s p y x) = (term109 A s p x y).
Proof. exact (eq_refl (term186 A s p y x)). Qed.
Lemma lem6001207 {A : Type'} (y : A) (s : A -> Prop) : (term128 A y s) = (term128 A y s).
Proof. exact (eq_refl (term128 A y s)). Qed.
Lemma lem6001208 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term191 A s p y x) = (term192 A s p x y).
Proof. exact (MK_COMB (@lem6001207 A y s) (@lem6001206 A s p x y)). Qed.
Lemma lem6001209 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term193 A s p y) = (term194 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6001208 A s p x y)). Qed.
Lemma lem6001210 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001211 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term185 A s p y) = (term195 A s p y).
Proof. exact (MK_COMB (@lem6001210 A) (@lem6001209 A s p y)). Qed.
Lemma lem6001212 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : ((term184 A s p y) = (term185 A s p y)) = ((term155 A s p y) = (term195 A s p y)).
Proof. exact (MK_COMB (@lem6001205 A s p y) (@lem6001211 A s p y)). Qed.
Lemma lem6001213 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term155 A s p y) = (term195 A s p y).
Proof. exact (EQ_MP (@lem6001212 A s p y) (@lem6001197 A s p y)). Qed.
Lemma lem6001214 {A : Type'} (s : A -> Prop) (p : A -> A) : (term156 A s p) = (term196 A s p).
Proof. exact (fun_ext (fun y : A => @lem6001213 A s p y)). Qed.
Lemma lem6001215 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6001216 {A : Type'} (s : A -> Prop) (p : A -> A) : (term157 A s p) = (term197 A s p).
Proof. exact (MK_COMB (@lem6001215 A) (@lem6001214 A s p)). Qed.
Lemma lem6001218 {A B : Type'} (P : type1413 A B) : (term198 A B P) = (term199 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6001219 {A : Type'} (P : type1402 A) : (term200 A P) = (term201 A P).
Proof. exact (@lem6001218 A A P). Qed.
Lemma lem6001220 {A : Type'} (s : A -> Prop) (p : A -> A) : (term202 A s p) = (term203 A s p).
Proof. exact (@lem6001219 A (term204 A s p)). Qed.
Lemma lem6001221 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term205 A s p y) = (term194 A s p y).
Proof. exact (eq_refl (term205 A s p y)). Qed.
Lemma lem6001222 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6001223 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term206 A s p y x) = (term207 A s p y x).
Proof. exact (MK_COMB (@lem6001221 A s p y) (@lem6001222 A x)). Qed.
Lemma lem6001224 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term207 A s p y x) = (term192 A s p x y).
Proof. exact (eq_refl (term207 A s p y x)). Qed.
Lemma lem6001225 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term206 A s p y x) = (term192 A s p x y).
Proof. exact (TRANS (@lem6001223 A s p y x) (@lem6001224 A s p x y)). Qed.
Lemma lem6001226 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term208 A s p y) = (term194 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6001225 A s p x y)). Qed.
Lemma lem6001227 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001228 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term209 A s p y) = (term195 A s p y).
Proof. exact (MK_COMB (@lem6001227 A) (@lem6001226 A s p y)). Qed.
Lemma lem6001229 {A : Type'} (s : A -> Prop) (p : A -> A) : (term210 A s p) = (term196 A s p).
Proof. exact (fun_ext (fun y : A => @lem6001228 A s p y)). Qed.
Lemma lem6001230 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6001231 {A : Type'} (s : A -> Prop) (p : A -> A) : (term202 A s p) = (term197 A s p).
Proof. exact (MK_COMB (@lem6001230 A) (@lem6001229 A s p)). Qed.
Lemma lem6001232 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6001233 {A : Type'} (s : A -> Prop) (p : A -> A) : (term211 A s p) = (term212 A s p).
Proof. exact (MK_COMB (@lem6001232) (@lem6001231 A s p)). Qed.
Lemma lem6001234 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term205 A s p y) = (term194 A s p y).
Proof. exact (eq_refl (term205 A s p y)). Qed.
Lemma lem6001235 {A : Type'} (x : A -> A) (y : A) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem6001236 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A -> A) (y : A) : (term213 A s p x y) = (term214 A s p x y).
Proof. exact (MK_COMB (@lem6001234 A s p y) (@lem6001235 A x y)). Qed.
Lemma lem6001237 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A -> A) (y : A) : (term214 A s p x y) = (term215 A s p x y).
Proof. exact (eq_refl (term214 A s p x y)). Qed.
Lemma lem6001238 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A -> A) (y : A) : (term213 A s p x y) = (term215 A s p x y).
Proof. exact (TRANS (@lem6001236 A s p x y) (@lem6001237 A s p x y)). Qed.
Lemma lem6001239 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A -> A) : (term216 A s p x) = (term217 A s p x).
Proof. exact (fun_ext (fun y : A => @lem6001238 A s p x y)). Qed.
Lemma lem6001240 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6001241 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A -> A) : (term218 A s p x) = (term219 A s p x).
Proof. exact (MK_COMB (@lem6001240 A) (@lem6001239 A s p x)). Qed.
Lemma lem6001242 {A : Type'} (s : A -> Prop) (p : A -> A) : (term220 A s p) = (term221 A s p).
Proof. exact (fun_ext (fun x : A -> A => @lem6001241 A s p x)). Qed.
Lemma lem6001243 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem6001244 {A : Type'} (s : A -> Prop) (p : A -> A) : (term203 A s p) = (term222 A s p).
Proof. exact (MK_COMB (@lem6001243 A) (@lem6001242 A s p)). Qed.
Lemma lem6001245 {A : Type'} (s : A -> Prop) (p : A -> A) : ((term202 A s p) = (term203 A s p)) = ((term197 A s p) = (term222 A s p)).
Proof. exact (MK_COMB (@lem6001233 A s p) (@lem6001244 A s p)). Qed.
Lemma lem6001246 {A : Type'} (s : A -> Prop) (p : A -> A) : (term197 A s p) = (term222 A s p).
Proof. exact (EQ_MP (@lem6001245 A s p) (@lem6001220 A s p)). Qed.
Lemma lem6001247 {A : Type'} (s : A -> Prop) (p : A -> A) : (term157 A s p) = (term222 A s p).
Proof. exact (TRANS (@lem6001216 A s p) (@lem6001246 A s p)). Qed.
Lemma lem6001248 {A : Type'} (s : A -> Prop) (p : A -> A) : (term161 A s p) = (term223 A s p).
Proof. exact (MK_COMB (@lem6001193 A p s) (@lem6001247 A s p)). Qed.
Lemma lem6001252 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6001253 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (@lem6001252 A P Q). Qed.
Lemma lem6001254 {A : Type'} (s : A -> Prop) (p : A -> A) : (term226 A s p) = (term227 A s p).
Proof. exact (@lem6001253 A (term179 A p s) (term222 A s p)). Qed.
Lemma lem6001255 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term228 A p s x) = (term178 A p x s).
Proof. exact (eq_refl (term228 A p s x)). Qed.
Lemma lem6001256 {A : Type'} (p : A -> A) (s : A -> Prop) : (term229 A p s) = (term179 A p s).
Proof. exact (fun_ext (fun x : A => @lem6001255 A p x s)). Qed.
Lemma lem6001257 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001258 {A : Type'} (p : A -> A) (s : A -> Prop) : (term230 A p s) = (term180 A p s).
Proof. exact (MK_COMB (@lem6001257 A) (@lem6001256 A p s)). Qed.
Lemma lem6001259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6001260 {A : Type'} (p : A -> A) (s : A -> Prop) : (term231 A p s) = (term181 A p s).
Proof. exact (MK_COMB (@lem6001259) (@lem6001258 A p s)). Qed.
Lemma lem6001261 {A : Type'} (s : A -> Prop) (p : A -> A) : (term222 A s p) = (term222 A s p).
Proof. exact (eq_refl (term222 A s p)). Qed.
Lemma lem6001262 {A : Type'} (s : A -> Prop) (p : A -> A) : (term226 A s p) = (term223 A s p).
Proof. exact (MK_COMB (@lem6001260 A p s) (@lem6001261 A s p)). Qed.
Lemma lem6001263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6001264 {A : Type'} (s : A -> Prop) (p : A -> A) : (term232 A s p) = (term233 A s p).
Proof. exact (MK_COMB (@lem6001263) (@lem6001262 A s p)). Qed.
Lemma lem6001265 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term228 A p s x) = (term178 A p x s).
Proof. exact (eq_refl (term228 A p s x)). Qed.
Lemma lem6001266 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6001267 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term234 A p s x) = (term235 A p x s).
Proof. exact (MK_COMB (@lem6001266) (@lem6001265 A p x s)). Qed.
Lemma lem6001268 {A : Type'} (s : A -> Prop) (p : A -> A) : (term222 A s p) = (term222 A s p).
Proof. exact (eq_refl (term222 A s p)). Qed.
Lemma lem6001269 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) : (term236 A x s p) = (term237 A x s p).
Proof. exact (MK_COMB (@lem6001267 A p x s) (@lem6001268 A s p)). Qed.
Lemma lem6001270 {A : Type'} (s : A -> Prop) (p : A -> A) : (term238 A s p) = (term239 A s p).
Proof. exact (fun_ext (fun x : A => @lem6001269 A x s p)). Qed.
Lemma lem6001271 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001272 {A : Type'} (s : A -> Prop) (p : A -> A) : (term227 A s p) = (term240 A s p).
Proof. exact (MK_COMB (@lem6001271 A) (@lem6001270 A s p)). Qed.
Lemma lem6001273 {A : Type'} (s : A -> Prop) (p : A -> A) : ((term226 A s p) = (term227 A s p)) = ((term223 A s p) = (term240 A s p)).
Proof. exact (MK_COMB (@lem6001264 A s p) (@lem6001272 A s p)). Qed.
Lemma lem6001274 {A : Type'} (s : A -> Prop) (p : A -> A) : (term223 A s p) = (term240 A s p).
Proof. exact (EQ_MP (@lem6001273 A s p) (@lem6001254 A s p)). Qed.
Lemma lem6001278 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6001279 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (@lem6001278 A P Q). Qed.
Lemma lem6001280 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) : (term241 A x s p) = (term242 A x s p).
Proof. exact (@lem6001279 A (term177 A p x s) (term222 A s p)). Qed.
Lemma lem6001281 {A : Type'} (p : A -> A) (x' : A) (x : A) (s : A -> Prop) : (term243 A p x s x') = (term175 A p x' x s).
Proof. exact (eq_refl (term243 A p x s x')). Qed.
Lemma lem6001282 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term244 A p x s) = (term177 A p x s).
Proof. exact (fun_ext (fun x' : A => @lem6001281 A p x' x s)). Qed.
Lemma lem6001283 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001284 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term245 A p x s) = (term178 A p x s).
Proof. exact (MK_COMB (@lem6001283 A) (@lem6001282 A p x s)). Qed.
Lemma lem6001285 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6001286 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term246 A p x s) = (term235 A p x s).
Proof. exact (MK_COMB (@lem6001285) (@lem6001284 A p x s)). Qed.
Lemma lem6001287 {A : Type'} (s : A -> Prop) (p : A -> A) : (term222 A s p) = (term222 A s p).
Proof. exact (eq_refl (term222 A s p)). Qed.
Lemma lem6001288 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) : (term241 A x s p) = (term237 A x s p).
Proof. exact (MK_COMB (@lem6001286 A p x s) (@lem6001287 A s p)). Qed.
Lemma lem6001289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6001290 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) : (term247 A x s p) = (term248 A x s p).
Proof. exact (MK_COMB (@lem6001289) (@lem6001288 A x s p)). Qed.
Lemma lem6001291 {A : Type'} (p : A -> A) (x' : A) (x : A) (s : A -> Prop) : (term243 A p x s x') = (term175 A p x' x s).
Proof. exact (eq_refl (term243 A p x s x')). Qed.
Lemma lem6001292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6001293 {A : Type'} (p : A -> A) (x' : A) (x : A) (s : A -> Prop) : (term249 A p x s x') = (term250 A p x' x s).
Proof. exact (MK_COMB (@lem6001292) (@lem6001291 A p x' x s)). Qed.
Lemma lem6001294 {A : Type'} (s : A -> Prop) (p : A -> A) : (term222 A s p) = (term222 A s p).
Proof. exact (eq_refl (term222 A s p)). Qed.
Lemma lem6001295 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (p : A -> A) : (term251 A x x' s p) = (term252 A x' x s p).
Proof. exact (MK_COMB (@lem6001293 A p x' x s) (@lem6001294 A s p)). Qed.
Lemma lem6001296 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) : (term253 A x s p) = (term254 A x s p).
Proof. exact (fun_ext (fun x' : A => @lem6001295 A x' x s p)). Qed.
Lemma lem6001297 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001298 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) : (term242 A x s p) = (term255 A x s p).
Proof. exact (MK_COMB (@lem6001297 A) (@lem6001296 A x s p)). Qed.
Lemma lem6001299 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) : ((term241 A x s p) = (term242 A x s p)) = ((term237 A x s p) = (term255 A x s p)).
Proof. exact (MK_COMB (@lem6001290 A x s p) (@lem6001298 A x s p)). Qed.
Lemma lem6001300 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) : (term237 A x s p) = (term255 A x s p).
Proof. exact (EQ_MP (@lem6001299 A x s p) (@lem6001280 A x s p)). Qed.
Lemma lem6001302 {A : Type'} (P : Prop) (Q : A -> Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6001303 {A : Type'} (P : Prop) (Q : type488 A) : (term256 A P Q) = (term257 A P Q).
Proof. exact (@lem6001302 (A -> A) P Q). Qed.
Lemma lem6001304 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (p : A -> A) : (term258 A x' x s p) = (term259 A x' x s p).
Proof. exact (@lem6001303 A (term175 A p x' x s) (term221 A s p)). Qed.
Lemma lem6001305 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A -> A) : (term260 A s p x) = (term219 A s p x).
Proof. exact (eq_refl (term260 A s p x)). Qed.
Lemma lem6001306 {A : Type'} (s : A -> Prop) (p : A -> A) : (term261 A s p) = (term221 A s p).
Proof. exact (fun_ext (fun x : A -> A => @lem6001305 A s p x)). Qed.
Lemma lem6001307 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem6001308 {A : Type'} (s : A -> Prop) (p : A -> A) : (term262 A s p) = (term222 A s p).
Proof. exact (MK_COMB (@lem6001307 A) (@lem6001306 A s p)). Qed.
Lemma lem6001309 {A : Type'} (p : A -> A) (x' : A) (x : A) (s : A -> Prop) : (term250 A p x' x s) = (term250 A p x' x s).
Proof. exact (eq_refl (term250 A p x' x s)). Qed.
Lemma lem6001310 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (p : A -> A) : (term258 A x' x s p) = (term252 A x' x s p).
Proof. exact (MK_COMB (@lem6001309 A p x' x s) (@lem6001308 A s p)). Qed.
Lemma lem6001311 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6001312 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (p : A -> A) : (term263 A x' x s p) = (term264 A x' x s p).
Proof. exact (MK_COMB (@lem6001311) (@lem6001310 A x' x s p)). Qed.
Lemma lem6001313 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A -> A) : (term260 A s p x) = (term219 A s p x).
Proof. exact (eq_refl (term260 A s p x)). Qed.
Lemma lem6001314 {A : Type'} (p : A -> A) (x' : A) (x : A) (s : A -> Prop) : (term250 A p x' x s) = (term250 A p x' x s).
Proof. exact (eq_refl (term250 A p x' x s)). Qed.
Lemma lem6001315 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (p : A -> A) (x'' : A -> A) : (term265 A x' x s p x'') = (term266 A x' x s p x'').
Proof. exact (MK_COMB (@lem6001314 A p x' x s) (@lem6001313 A s p x'')). Qed.
Lemma lem6001316 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (p : A -> A) : (term267 A x' x s p) = (term268 A x' x s p).
Proof. exact (fun_ext (fun x'' : A -> A => @lem6001315 A x' x s p x'')). Qed.
Lemma lem6001317 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem6001318 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (p : A -> A) : (term259 A x' x s p) = (term269 A x' x s p).
Proof. exact (MK_COMB (@lem6001317 A) (@lem6001316 A x' x s p)). Qed.
Lemma lem6001319 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (p : A -> A) : ((term258 A x' x s p) = (term259 A x' x s p)) = ((term252 A x' x s p) = (term269 A x' x s p)).
Proof. exact (MK_COMB (@lem6001312 A x' x s p) (@lem6001318 A x' x s p)). Qed.
Lemma lem6001320 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (p : A -> A) : (term252 A x' x s p) = (term269 A x' x s p).
Proof. exact (EQ_MP (@lem6001319 A x' x s p) (@lem6001304 A x' x s p)). Qed.
Lemma lem6001321 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) : (term254 A x s p) = (term270 A x s p).
Proof. exact (fun_ext (fun x' : A => @lem6001320 A x' x s p)). Qed.
Lemma lem6001322 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001323 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) : (term255 A x s p) = (term271 A x s p).
Proof. exact (MK_COMB (@lem6001322 A) (@lem6001321 A x s p)). Qed.
Lemma lem6001324 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) : (term237 A x s p) = (term271 A x s p).
Proof. exact (TRANS (@lem6001300 A x s p) (@lem6001323 A x s p)). Qed.
Lemma lem6001325 {A : Type'} (s : A -> Prop) (p : A -> A) : (term239 A s p) = (term272 A s p).
Proof. exact (fun_ext (fun x : A => @lem6001324 A x s p)). Qed.
Lemma lem6001326 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001327 {A : Type'} (s : A -> Prop) (p : A -> A) : (term240 A s p) = (term273 A s p).
Proof. exact (MK_COMB (@lem6001326 A) (@lem6001325 A s p)). Qed.
Lemma lem6001328 {A : Type'} (s : A -> Prop) (p : A -> A) : (term223 A s p) = (term273 A s p).
Proof. exact (TRANS (@lem6001274 A s p) (@lem6001327 A s p)). Qed.
Lemma lem6001330 {A : Type'} (s : A -> Prop) (p : A -> A) : (term161 A s p) = (term273 A s p).
Proof. exact (TRANS (@lem6001248 A s p) (@lem6001328 A s p)). Qed.
Lemma lem6001331 {A : Type'} (s : A -> Prop) (p : A -> A) : (term75 A s p) = (term273 A s p).
Proof. exact (TRANS (@lem6000971 A s p) (@lem6001330 A s p)). Qed.
Lemma lem6001332 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term75 A s p) : term273 A s p.
Proof. exact (EQ_MP (@lem6001331 A s p) (@lem6000768 A s p h1)). Qed.
Lemma lem6001338 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : @IN A y s.
Proof. exact (h1). Qed.
Lemma lem6001347 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term274 A s p x y) = (term275 A s p x y).
Proof. exact (@lem17045 (@IN A x s) ((p x) = y)). Qed.
Lemma lem6001350 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term109 A s p x y) = (term109 A s p x y).
Proof. exact (eq_refl (term109 A s p x y)). Qed.
Lemma lem6001351 {A : Type'} (x' : A) (x : A) : (term276 A x' x) = (term276 A x' x).
Proof. exact (eq_refl (term276 A x' x)). Qed.
Lemma lem6001353 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term186 A s p y x) = (term109 A s p x y).
Proof. exact (eq_refl (term186 A s p y x)). Qed.
Lemma lem6001354 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A) (y : A) : (term186 A s p y x') = (term109 A s p x' y).
Proof. exact (eq_refl (term186 A s p y x')). Qed.
Lemma lem6001355 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A) (y : A) : (term109 A s p x' y) = (term109 A s p x' y).
Proof. exact (@lem6001350 A s p x' y). Qed.
Lemma lem6001356 {A : Type'} (P : A -> Prop) : (term277 A P) = (term278 A P).
Proof. exact (@lem18393 A P). Qed.
Lemma lem6001357 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term121 A s p y) = (term279 A s p y).
Proof. exact (@lem6001356 A (term110 A s p y)). Qed.
Lemma lem6001358 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A) (y : A) : (term186 A s p y x') = (term109 A s p x' y).
Proof. exact (TRANS (@lem6001354 A s p x' y) (@lem6001355 A s p x' y)). Qed.
Lemma lem6001359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6001360 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A) (y : A) : (term280 A s p y x') = (term281 A s p x' y).
Proof. exact (MK_COMB (@lem6001359) (@lem6001358 A s p x' y)). Qed.
Lemma lem6001361 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term282 A s p y x' x) = (term283 A s p y x' x).
Proof. exact (MK_COMB (@lem6001360 A s p x' y) (@lem6001351 A x' x)). Qed.
Lemma lem6001362 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term186 A s p y x) = (term109 A s p x y).
Proof. exact (eq_refl (term186 A s p y x)). Qed.
Lemma lem6001363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6001364 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term280 A s p y x) = (term281 A s p x y).
Proof. exact (MK_COMB (@lem6001363) (@lem6001362 A s p x y)). Qed.
Lemma lem6001365 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term284 A s p y x' x) = (term285 A s p y x' x).
Proof. exact (MK_COMB (@lem6001364 A s p x y) (@lem6001361 A s p y x' x)). Qed.
Lemma lem6001366 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term286 A s p y x) = (term287 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem6001365 A s p y x' x)). Qed.
Lemma lem6001367 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001368 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term288 A s p y x) = (term289 A s p y x).
Proof. exact (MK_COMB (@lem6001367 A) (@lem6001366 A s p y x)). Qed.
Lemma lem6001369 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term290 A s p y) = (term291 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6001368 A s p y x)). Qed.
Lemma lem6001370 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001371 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term292 A s p y) = (term293 A s p y).
Proof. exact (MK_COMB (@lem6001370 A) (@lem6001369 A s p y)). Qed.
Lemma lem6001372 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6001373 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term294 A s p y x) = (term274 A s p x y).
Proof. exact (MK_COMB (@lem6001372) (@lem6001353 A s p x y)). Qed.
Lemma lem6001374 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term294 A s p y x) = (term275 A s p x y).
Proof. exact (TRANS (@lem6001373 A s p x y) (@lem6001347 A s p x y)). Qed.
Lemma lem6001375 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term295 A s p y) = (term296 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6001374 A s p x y)). Qed.
Lemma lem6001376 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6001377 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term297 A s p y) = (term298 A s p y).
Proof. exact (MK_COMB (@lem6001376 A) (@lem6001375 A s p y)). Qed.
Lemma lem6001378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6001379 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term299 A s p y) = (term300 A s p y).
Proof. exact (MK_COMB (@lem6001378) (@lem6001377 A s p y)). Qed.
Lemma lem6001380 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term279 A s p y) = (term301 A s p y).
Proof. exact (MK_COMB (@lem6001379 A s p y) (@lem6001371 A s p y)). Qed.
Lemma lem6001381 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term121 A s p y) = (term301 A s p y).
Proof. exact (TRANS (@lem6001357 A s p y) (@lem6001380 A s p y)). Qed.
Lemma lem6001435 {A : Type'} (P : Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem6001436 {A : Type'} (P : Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (@lem6001435 A P Q). Qed.
Lemma lem6001437 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term304 A s p y x) = (term305 A s p y x).
Proof. exact (@lem6001436 A (term109 A s p x y) (term306 A s p y x)). Qed.
Lemma lem6001438 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term307 A s p y x x') = (term283 A s p y x' x).
Proof. exact (eq_refl (term307 A s p y x x')). Qed.
Lemma lem6001439 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term281 A s p x y) = (term281 A s p x y).
Proof. exact (eq_refl (term281 A s p x y)). Qed.
Lemma lem6001440 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term308 A s p y x x') = (term285 A s p y x' x).
Proof. exact (MK_COMB (@lem6001439 A s p x y) (@lem6001438 A s p y x' x)). Qed.
Lemma lem6001441 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term309 A s p y x) = (term287 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem6001440 A s p y x' x)). Qed.
Lemma lem6001442 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001443 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term304 A s p y x) = (term289 A s p y x).
Proof. exact (MK_COMB (@lem6001442 A) (@lem6001441 A s p y x)). Qed.
Lemma lem6001444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6001445 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term310 A s p y x) = (term311 A s p y x).
Proof. exact (MK_COMB (@lem6001444) (@lem6001443 A s p y x)). Qed.
Lemma lem6001446 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term307 A s p y x x') = (term283 A s p y x' x).
Proof. exact (eq_refl (term307 A s p y x x')). Qed.
Lemma lem6001447 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term312 A s p y x) = (term306 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem6001446 A s p y x' x)). Qed.
Lemma lem6001448 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001449 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term313 A s p y x) = (term314 A s p y x).
Proof. exact (MK_COMB (@lem6001448 A) (@lem6001447 A s p y x)). Qed.
Lemma lem6001450 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term281 A s p x y) = (term281 A s p x y).
Proof. exact (eq_refl (term281 A s p x y)). Qed.
Lemma lem6001451 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term305 A s p y x) = (term315 A s p y x).
Proof. exact (MK_COMB (@lem6001450 A s p x y) (@lem6001449 A s p y x)). Qed.
Lemma lem6001452 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : ((term304 A s p y x) = (term305 A s p y x)) = ((term289 A s p y x) = (term315 A s p y x)).
Proof. exact (MK_COMB (@lem6001445 A s p y x) (@lem6001451 A s p y x)). Qed.
Lemma lem6001453 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term289 A s p y x) = (term315 A s p y x).
Proof. exact (EQ_MP (@lem6001452 A s p y x) (@lem6001437 A s p y x)). Qed.
Lemma lem6001502 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term291 A s p y) = (term316 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6001453 A s p y x)). Qed.
Lemma lem6001503 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001504 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term293 A s p y) = (term317 A s p y).
Proof. exact (MK_COMB (@lem6001503 A) (@lem6001502 A s p y)). Qed.
Lemma lem6001553 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term300 A s p y) = (term300 A s p y).
Proof. exact (eq_refl (term300 A s p y)). Qed.
Lemma lem6001554 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term301 A s p y) = (term318 A s p y).
Proof. exact (MK_COMB (@lem6001553 A s p y) (@lem6001504 A s p y)). Qed.
Lemma lem6001556 {A : Type'} (P : Prop) (Q : A -> Prop) : (term303 A P Q) = (term302 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem6001557 {A : Type'} (P : Prop) (Q : A -> Prop) : (term303 A P Q) = (term302 A P Q).
Proof. exact (@lem6001556 A P Q). Qed.
Lemma lem6001558 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term305 A s p y x) = (term304 A s p y x).
Proof. exact (@lem6001557 A (term109 A s p x y) (term306 A s p y x)). Qed.
Lemma lem6001559 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term307 A s p y x x') = (term283 A s p y x' x).
Proof. exact (eq_refl (term307 A s p y x x')). Qed.
Lemma lem6001560 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term312 A s p y x) = (term306 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem6001559 A s p y x' x)). Qed.
Lemma lem6001561 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001562 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term313 A s p y x) = (term314 A s p y x).
Proof. exact (MK_COMB (@lem6001561 A) (@lem6001560 A s p y x)). Qed.
Lemma lem6001563 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term281 A s p x y) = (term281 A s p x y).
Proof. exact (eq_refl (term281 A s p x y)). Qed.
Lemma lem6001564 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term305 A s p y x) = (term315 A s p y x).
Proof. exact (MK_COMB (@lem6001563 A s p x y) (@lem6001562 A s p y x)). Qed.
Lemma lem6001565 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6001566 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term319 A s p y x) = (term320 A s p y x).
Proof. exact (MK_COMB (@lem6001565) (@lem6001564 A s p y x)). Qed.
Lemma lem6001567 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term307 A s p y x x') = (term283 A s p y x' x).
Proof. exact (eq_refl (term307 A s p y x x')). Qed.
Lemma lem6001568 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term281 A s p x y) = (term281 A s p x y).
Proof. exact (eq_refl (term281 A s p x y)). Qed.
Lemma lem6001569 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term308 A s p y x x') = (term285 A s p y x' x).
Proof. exact (MK_COMB (@lem6001568 A s p x y) (@lem6001567 A s p y x' x)). Qed.
Lemma lem6001570 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term309 A s p y x) = (term287 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem6001569 A s p y x' x)). Qed.
Lemma lem6001571 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001572 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term304 A s p y x) = (term289 A s p y x).
Proof. exact (MK_COMB (@lem6001571 A) (@lem6001570 A s p y x)). Qed.
Lemma lem6001573 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : ((term305 A s p y x) = (term304 A s p y x)) = ((term315 A s p y x) = (term289 A s p y x)).
Proof. exact (MK_COMB (@lem6001566 A s p y x) (@lem6001572 A s p y x)). Qed.
Lemma lem6001574 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term315 A s p y x) = (term289 A s p y x).
Proof. exact (EQ_MP (@lem6001573 A s p y x) (@lem6001558 A s p y x)). Qed.
Lemma lem6001575 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term316 A s p y) = (term291 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6001574 A s p y x)). Qed.
Lemma lem6001576 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001577 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term317 A s p y) = (term293 A s p y).
Proof. exact (MK_COMB (@lem6001576 A) (@lem6001575 A s p y)). Qed.
Lemma lem6001578 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term300 A s p y) = (term300 A s p y).
Proof. exact (eq_refl (term300 A s p y)). Qed.
Lemma lem6001579 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term318 A s p y) = (term301 A s p y).
Proof. exact (MK_COMB (@lem6001578 A s p y) (@lem6001577 A s p y)). Qed.
Lemma lem6001581 {A : Type'} (P : Prop) (Q : A -> Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6001582 {A : Type'} (P : Prop) (Q : A -> Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (@lem6001581 A P Q). Qed.
Lemma lem6001583 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term321 A s p y) = (term322 A s p y).
Proof. exact (@lem6001582 A (term298 A s p y) (term291 A s p y)). Qed.
Lemma lem6001584 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term323 A s p y x) = (term289 A s p y x).
Proof. exact (eq_refl (term323 A s p y x)). Qed.
Lemma lem6001585 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term324 A s p y) = (term291 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6001584 A s p y x)). Qed.
Lemma lem6001586 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001587 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term325 A s p y) = (term293 A s p y).
Proof. exact (MK_COMB (@lem6001586 A) (@lem6001585 A s p y)). Qed.
Lemma lem6001588 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term300 A s p y) = (term300 A s p y).
Proof. exact (eq_refl (term300 A s p y)). Qed.
Lemma lem6001589 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term321 A s p y) = (term301 A s p y).
Proof. exact (MK_COMB (@lem6001588 A s p y) (@lem6001587 A s p y)). Qed.
Lemma lem6001590 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6001591 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term326 A s p y) = (term327 A s p y).
Proof. exact (MK_COMB (@lem6001590) (@lem6001589 A s p y)). Qed.
Lemma lem6001592 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term323 A s p y x) = (term289 A s p y x).
Proof. exact (eq_refl (term323 A s p y x)). Qed.
Lemma lem6001593 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term300 A s p y) = (term300 A s p y).
Proof. exact (eq_refl (term300 A s p y)). Qed.
Lemma lem6001594 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term328 A s p y x) = (term329 A s p y x).
Proof. exact (MK_COMB (@lem6001593 A s p y) (@lem6001592 A s p y x)). Qed.
Lemma lem6001595 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term330 A s p y) = (term331 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6001594 A s p y x)). Qed.
Lemma lem6001596 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001597 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term322 A s p y) = (term332 A s p y).
Proof. exact (MK_COMB (@lem6001596 A) (@lem6001595 A s p y)). Qed.
Lemma lem6001598 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : ((term321 A s p y) = (term322 A s p y)) = ((term301 A s p y) = (term332 A s p y)).
Proof. exact (MK_COMB (@lem6001591 A s p y) (@lem6001597 A s p y)). Qed.
Lemma lem6001599 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term301 A s p y) = (term332 A s p y).
Proof. exact (EQ_MP (@lem6001598 A s p y) (@lem6001583 A s p y)). Qed.
Lemma lem6001601 {A : Type'} (P : Prop) (Q : A -> Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6001602 {A : Type'} (P : Prop) (Q : A -> Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (@lem6001601 A P Q). Qed.
Lemma lem6001603 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term333 A s p y x) = (term334 A s p y x).
Proof. exact (@lem6001602 A (term298 A s p y) (term287 A s p y x)). Qed.
Lemma lem6001604 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term335 A s p y x x') = (term285 A s p y x' x).
Proof. exact (eq_refl (term335 A s p y x x')). Qed.
Lemma lem6001605 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term336 A s p y x) = (term287 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem6001604 A s p y x' x)). Qed.
Lemma lem6001606 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001607 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term337 A s p y x) = (term289 A s p y x).
Proof. exact (MK_COMB (@lem6001606 A) (@lem6001605 A s p y x)). Qed.
Lemma lem6001608 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term300 A s p y) = (term300 A s p y).
Proof. exact (eq_refl (term300 A s p y)). Qed.
Lemma lem6001609 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term333 A s p y x) = (term329 A s p y x).
Proof. exact (MK_COMB (@lem6001608 A s p y) (@lem6001607 A s p y x)). Qed.
Lemma lem6001610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6001611 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term338 A s p y x) = (term339 A s p y x).
Proof. exact (MK_COMB (@lem6001610) (@lem6001609 A s p y x)). Qed.
Lemma lem6001612 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term335 A s p y x x') = (term285 A s p y x' x).
Proof. exact (eq_refl (term335 A s p y x x')). Qed.
Lemma lem6001613 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term300 A s p y) = (term300 A s p y).
Proof. exact (eq_refl (term300 A s p y)). Qed.
Lemma lem6001614 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term340 A s p y x x') = (term341 A s p y x' x).
Proof. exact (MK_COMB (@lem6001613 A s p y) (@lem6001612 A s p y x' x)). Qed.
Lemma lem6001615 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term342 A s p y x) = (term343 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem6001614 A s p y x' x)). Qed.
Lemma lem6001616 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001617 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term334 A s p y x) = (term344 A s p y x).
Proof. exact (MK_COMB (@lem6001616 A) (@lem6001615 A s p y x)). Qed.
Lemma lem6001618 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : ((term333 A s p y x) = (term334 A s p y x)) = ((term329 A s p y x) = (term344 A s p y x)).
Proof. exact (MK_COMB (@lem6001611 A s p y x) (@lem6001617 A s p y x)). Qed.
Lemma lem6001619 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term329 A s p y x) = (term344 A s p y x).
Proof. exact (EQ_MP (@lem6001618 A s p y x) (@lem6001603 A s p y x)). Qed.
Lemma lem6001620 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term331 A s p y) = (term345 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6001619 A s p y x)). Qed.
Lemma lem6001621 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6001622 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term332 A s p y) = (term346 A s p y).
Proof. exact (MK_COMB (@lem6001621 A) (@lem6001620 A s p y)). Qed.
Lemma lem6001623 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term301 A s p y) = (term346 A s p y).
Proof. exact (TRANS (@lem6001599 A s p y) (@lem6001622 A s p y)). Qed.
Lemma lem6001624 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term318 A s p y) = (term346 A s p y).
Proof. exact (TRANS (@lem6001579 A s p y) (@lem6001623 A s p y)). Qed.
Lemma lem6001625 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term301 A s p y) = (term346 A s p y).
Proof. exact (TRANS (@lem6001554 A s p y) (@lem6001624 A s p y)). Qed.
Lemma lem6001626 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term121 A s p y) = (term346 A s p y).
Proof. exact (TRANS (@lem6001381 A s p y) (@lem6001625 A s p y)). Qed.
Lemma lem6001627 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (h1 : term121 A s p y) : term346 A s p y.
Proof. exact (EQ_MP (@lem6001626 A s p y) (@lem6000774 A s p y h1)). Qed.
Lemma lem6001628 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) (h1 : term344 A s p y x) : term344 A s p y x.
Proof. exact (h1). Qed.
Lemma lem6001629 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term341 A s p y x' x) : term341 A s p y x' x.
Proof. exact (h1). Qed.
Lemma lem6001630 {A : Type'} (x'' : A) (s : A -> Prop) (p : A -> A) (h1 : term271 A x'' s p) : term271 A x'' s p.
Proof. exact (h1). Qed.
Lemma lem6001631 {A : Type'} (x''' : A) (x'' : A) (s : A -> Prop) (p : A -> A) (h1 : term269 A x''' x'' s p) : term269 A x''' x'' s p.
Proof. exact (h1). Qed.
Lemma lem6001632 {A : Type'} (x''' : A) (x'' : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term266 A x''' x'' s p x'''') : term266 A x''' x'' s p x''''.
Proof. exact (h1). Qed.
Lemma lem6001653 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term122 A p x s) = (term122 A p x s).
Proof. exact (eq_refl (term122 A p x s)). Qed.
Lemma lem6001654 {A : Type'} (p : A -> A) (s : A -> Prop) : (term124 A p s) = (term124 A p s).
Proof. exact (fun_ext (fun x : A => @lem6001653 A p x s)). Qed.
Lemma lem6001655 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6001656 {A : Type'} (p : A -> A) (s : A -> Prop) : (term125 A p s) = (term125 A p s).
Proof. exact (MK_COMB (@lem6001655 A) (@lem6001654 A p s)). Qed.
Lemma lem6001657 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term125 A p s.
Proof. exact (EQ_MP (@lem6001656 A p s) (@lem6000843 A p s h1)). Qed.
Lemma lem6001696 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term136 A s p x y) = (term136 A s p x y).
Proof. exact (eq_refl (term136 A s p x y)). Qed.
Lemma lem6001697 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) : (term138 A s p x) = (term138 A s p x).
Proof. exact (fun_ext (fun y : A => @lem6001696 A s p x y)). Qed.
Lemma lem6001698 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6001699 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) : (term139 A s p x) = (term139 A s p x).
Proof. exact (MK_COMB (@lem6001698 A) (@lem6001697 A s p x)). Qed.
Lemma lem6001700 {A : Type'} (s : A -> Prop) (p : A -> A) : (term140 A s p) = (term140 A s p).
Proof. exact (fun_ext (fun x : A => @lem6001699 A s p x)). Qed.
Lemma lem6001701 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6001702 {A : Type'} (s : A -> Prop) (p : A -> A) : (term141 A s p) = (term141 A s p).
Proof. exact (MK_COMB (@lem6001701 A) (@lem6001700 A s p)). Qed.
Lemma lem6001703 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term141 A s p.
Proof. exact (EQ_MP (@lem6001702 A s p) (@lem6000925 A s p h1)). Qed.
Lemma lem6001709 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : @IN A y s.
Proof. exact (h1). Qed.
Lemma lem6001752 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term285 A s p y x' x) = (term285 A s p y x' x).
Proof. exact (eq_refl (term285 A s p y x' x)). Qed.
Lemma lem6001771 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term275 A s p x y) = (term275 A s p x y).
Proof. exact (eq_refl (term275 A s p x y)). Qed.
Lemma lem6001772 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term296 A s p y) = (term296 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6001771 A s p x y)). Qed.
Lemma lem6001773 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6001774 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term298 A s p y) = (term298 A s p y).
Proof. exact (MK_COMB (@lem6001773 A) (@lem6001772 A s p y)). Qed.
Lemma lem6001775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6001776 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term300 A s p y) = (term300 A s p y).
Proof. exact (MK_COMB (@lem6001775) (@lem6001774 A s p y)). Qed.
Lemma lem6001777 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term341 A s p y x' x) = (term341 A s p y x' x).
Proof. exact (MK_COMB (@lem6001776 A s p y) (@lem6001752 A s p y x' x)). Qed.
Lemma lem6001778 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term341 A s p y x' x) : term341 A s p y x' x.
Proof. exact (EQ_MP (@lem6001777 A s p y x' x) (@lem6001629 A s p y x' x h1)). Qed.
Lemma lem6001807 {A : Type'} (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (y : A) : (term215 A s p x'''' y) = (term215 A s p x'''' y).
Proof. exact (eq_refl (term215 A s p x'''' y)). Qed.
Lemma lem6001808 {A : Type'} (s : A -> Prop) (p : A -> A) (x'''' : A -> A) : (term217 A s p x'''') = (term217 A s p x'''').
Proof. exact (fun_ext (fun y : A => @lem6001807 A s p x'''' y)). Qed.
Lemma lem6001809 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6001810 {A : Type'} (s : A -> Prop) (p : A -> A) (x'''' : A -> A) : (term219 A s p x'''') = (term219 A s p x'''').
Proof. exact (MK_COMB (@lem6001809 A) (@lem6001808 A s p x'''')). Qed.
Lemma lem6001837 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) : (term250 A p x''' x'' s) = (term250 A p x''' x'' s).
Proof. exact (eq_refl (term250 A p x''' x'' s)). Qed.
Lemma lem6001838 {A : Type'} (x''' : A) (x'' : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) : (term266 A x''' x'' s p x'''') = (term266 A x''' x'' s p x'''').
Proof. exact (MK_COMB (@lem6001837 A p x''' x'' s) (@lem6001810 A s p x'''')). Qed.
Lemma lem6001839 {A : Type'} (x''' : A) (x'' : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term266 A x''' x'' s p x'''') : term266 A x''' x'' s p x''''.
Proof. exact (EQ_MP (@lem6001838 A x''' x'' s p x'''') (@lem6001632 A x''' x'' s p x'''' h1)). Qed.
Lemma lem6001840 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : term175 A p x''' x'' s.
Proof. exact (h1). Qed.
Lemma lem6001841 {A : Type'} (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term219 A s p x'''') : term219 A s p x''''.
Proof. exact (h1). Qed.
Lemma lem6001843 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : term118 A x'' p x''' s.
Proof. exact (proj1 (@lem6001840 A p x''' x'' s h1)). Qed.
Lemma lem6001856 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (h1 : term298 A s p y) : term298 A s p y.
Proof. exact (h1). Qed.
Lemma lem6001857 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : term285 A s p y x' x.
Proof. exact (h1). Qed.
Lemma lem6001858 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : term283 A s p y x' x.
Proof. exact (proj2 (@lem6001857 A s p y x' x h1)). Qed.
Lemma lem6001859 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : term109 A s p x y.
Proof. exact (proj1 (@lem6001857 A s p y x' x h1)). Qed.
Lemma lem6001861 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : term109 A s p x' y.
Proof. exact (proj1 (@lem6001858 A s p y x' x h1)). Qed.
Lemma lem6001877 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term122 A p x s) = (term122 A p x s).
Proof. exact (eq_refl (term122 A p x s)). Qed.
Lemma lem6001878 {A : Type'} (p : A -> A) (s : A -> Prop) : (term124 A p s) = (term124 A p s).
Proof. exact (fun_ext (fun x : A => @lem6001877 A p x s)). Qed.
Lemma lem6001879 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6001881 {A : Type'} (p : A -> A) (s : A -> Prop) : (term125 A p s) = (term125 A p s).
Proof. exact (MK_COMB (@lem6001879 A) (@lem6001878 A p s)). Qed.
Lemma lem6001882 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term125 A p s.
Proof. exact (EQ_MP (@lem6001881 A p s) (@lem6001657 A p s h1)). Qed.
Lemma lem6001951 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term122 A p x s) = (term122 A p x s).
Proof. exact (eq_refl (term122 A p x s)). Qed.
Lemma lem6001952 {A : Type'} (p : A -> A) (s : A -> Prop) : (term124 A p s) = (term124 A p s).
Proof. exact (fun_ext (fun x : A => @lem6001951 A p x s)). Qed.
Lemma lem6001953 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6001955 {A : Type'} (p : A -> A) (s : A -> Prop) : (term125 A p s) = (term125 A p s).
Proof. exact (MK_COMB (@lem6001953 A) (@lem6001952 A p s)). Qed.
Lemma lem6001956 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term125 A p s.
Proof. exact (EQ_MP (@lem6001955 A p s) (@lem6001657 A p s h1)). Qed.
Lemma lem6002069 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : @IN A y s.
Proof. exact (h1). Qed.
Lemma lem6002087 {A : Type'} (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (y : A) : (term215 A s p x'''' y) = (term347 A s p x'''' y).
Proof. exact (@lem19490 (term123 A x'''' y s) (term142 A y s) ((term348 A p x'''' y) = y)). Qed.
Lemma lem6002088 {A : Type'} (s : A -> Prop) (p : A -> A) (x'''' : A -> A) : (term217 A s p x'''') = (term349 A s p x'''').
Proof. exact (fun_ext (fun y : A => @lem6002087 A s p x'''' y)). Qed.
Lemma lem6002089 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6002091 {A : Type'} (s : A -> Prop) (p : A -> A) (x'''' : A -> A) : (term219 A s p x'''') = (term350 A s p x'''').
Proof. exact (MK_COMB (@lem6002089 A) (@lem6002088 A s p x'''')). Qed.
Lemma lem6002092 {A : Type'} (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term219 A s p x'''') : term350 A s p x''''.
Proof. exact (EQ_MP (@lem6002091 A s p x'''') (@lem6001841 A s p x'''' h1)). Qed.
Lemma lem6002100 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term275 A s p x y) = (term275 A s p x y).
Proof. exact (eq_refl (term275 A s p x y)). Qed.
Lemma lem6002101 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term296 A s p y) = (term296 A s p y).
Proof. exact (fun_ext (fun x : A => @lem6002100 A s p x y)). Qed.
Lemma lem6002102 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6002104 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term298 A s p y) = (term298 A s p y).
Proof. exact (MK_COMB (@lem6002102 A) (@lem6002101 A s p y)). Qed.
Lemma lem6002105 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (h1 : term298 A s p y) : term298 A s p y.
Proof. exact (EQ_MP (@lem6002104 A s p y) (@lem6001856 A s p y h1)). Qed.
Lemma lem6002142 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term136 A s p x y) = (term136 A s p x y).
Proof. exact (eq_refl (term136 A s p x y)). Qed.
Lemma lem6002143 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) : (term138 A s p x) = (term138 A s p x).
Proof. exact (fun_ext (fun y : A => @lem6002142 A s p x y)). Qed.
Lemma lem6002144 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6002145 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) : (term139 A s p x) = (term139 A s p x).
Proof. exact (MK_COMB (@lem6002144 A) (@lem6002143 A s p x)). Qed.
Lemma lem6002146 {A : Type'} (s : A -> Prop) (p : A -> A) : (term140 A s p) = (term140 A s p).
Proof. exact (fun_ext (fun x : A => @lem6002145 A s p x)). Qed.
Lemma lem6002147 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6002149 {A : Type'} (s : A -> Prop) (p : A -> A) : (term141 A s p) = (term141 A s p).
Proof. exact (MK_COMB (@lem6002147 A) (@lem6002146 A s p)). Qed.
Lemma lem6002150 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term141 A s p.
Proof. exact (EQ_MP (@lem6002149 A s p) (@lem6001703 A s p h1)). Qed.
Lemma lem6002198 {A : Type'} (_76386 : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term351 A p s _76386.
Proof. exact (@lem6001882 A p s h1 _76386). Qed.
Lemma lem6002199 {A : Type'} (p : A -> A) (_76386 : A) (s : A -> Prop) : (term351 A p s _76386) = (term122 A p _76386 s).
Proof. exact (eq_refl (term351 A p s _76386)). Qed.
Lemma lem6002210 {A : Type'} (_76390 : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term351 A p s _76390.
Proof. exact (@lem6001956 A p s h1 _76390). Qed.
Lemma lem6002211 {A : Type'} (p : A -> A) (_76390 : A) (s : A -> Prop) : (term351 A p s _76390) = (term122 A p _76390 s).
Proof. exact (eq_refl (term351 A p s _76390)). Qed.
Lemma lem6002228 {A : Type'} (_76396 : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term219 A s p x'''') : term352 A s p x'''' _76396.
Proof. exact (@lem6002092 A s p x'''' h1 _76396). Qed.
Lemma lem6002229 {A : Type'} (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (_76396 : A) : (term352 A s p x'''' _76396) = (term347 A s p x'''' _76396).
Proof. exact (eq_refl (term352 A s p x'''' _76396)). Qed.
Lemma lem6002230 {A : Type'} (_76396 : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term219 A s p x'''') : term347 A s p x'''' _76396.
Proof. exact (EQ_MP (@lem6002229 A s p x'''' _76396) (@lem6002228 A _76396 s p x'''' h1)). Qed.
Lemma lem6002231 {A : Type'} (_76397 : A) (s : A -> Prop) (p : A -> A) (y : A) (h1 : term298 A s p y) : term353 A s p y _76397.
Proof. exact (@lem6002105 A s p y h1 _76397). Qed.
Lemma lem6002232 {A : Type'} (s : A -> Prop) (p : A -> A) (_76397 : A) (y : A) : (term353 A s p y _76397) = (term275 A s p _76397 y).
Proof. exact (eq_refl (term353 A s p y _76397)). Qed.
Lemma lem6002237 {A : Type'} (_76399 : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term354 A s p _76399.
Proof. exact (@lem6002150 A s p h1 _76399). Qed.
Lemma lem6002238 {A : Type'} (s : A -> Prop) (p : A -> A) (_76399 : A) : (term354 A s p _76399) = (term139 A s p _76399).
Proof. exact (eq_refl (term354 A s p _76399)). Qed.
Lemma lem6002239 {A : Type'} (_76399 : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term139 A s p _76399.
Proof. exact (EQ_MP (@lem6002238 A s p _76399) (@lem6002237 A _76399 s p h1)). Qed.
Lemma lem6002240 {A : Type'} (_76399 : A) (_76400 : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term355 A s p _76399 _76400.
Proof. exact (@lem6002239 A _76399 s p h1 _76400). Qed.
Lemma lem6002241 {A : Type'} (s : A -> Prop) (p : A -> A) (_76399 : A) (_76400 : A) : (term355 A s p _76399 _76400) = (term136 A s p _76399 _76400).
Proof. exact (eq_refl (term355 A s p _76399 _76400)). Qed.
Lemma lem6002242 {A : Type'} (_76399 : A) (_76400 : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term136 A s p _76399 _76400.
Proof. exact (EQ_MP (@lem6002241 A s p _76399 _76400) (@lem6002240 A _76399 _76400 s p h1)). Qed.
Lemma lem6002279 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : term142 A x'' s.
Proof. exact (proj2 (@lem6001840 A p x''' x'' s h1)). Qed.
Lemma lem6002281 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : x'' = (p x''').
Proof. exact (proj1 (@lem6001843 A p x''' x'' s h1)). Qed.
Lemma lem6002361 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : @IN A y s.
Proof. exact (h1). Qed.
Lemma lem6002367 {A : Type'} (_76397 : A) (s : A -> Prop) (p : A -> A) (y : A) (h1 : term298 A s p y) : term275 A s p _76397 y.
Proof. exact (EQ_MP (@lem6002232 A s p _76397 y) (@lem6002231 A _76397 s p y h1)). Qed.
Lemma lem6002373 {A : Type'} (_76396 : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term219 A s p x'''') : term122 A x'''' _76396 s.
Proof. exact (proj1 (@lem6002230 A _76396 s p x'''' h1)). Qed.
Lemma lem6002379 {A : Type'} (_76396 : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term219 A s p x'''') : term356 A s p x'''' _76396.
Proof. exact (proj2 (@lem6002230 A _76396 s p x'''' h1)). Qed.
Lemma lem6002391 {A : Type'} (s : A -> Prop) (p : A -> A) (_76399 : A) (_76400 : A) : (term136 A s p _76399 _76400) = (term357 A s p _76399 _76400).
Proof. exact (@lem6000081 (term142 A _76399 s) (term127 A s _76399 p _76400) (_76399 = _76400)). Qed.
Lemma lem6002398 {A : Type'} (s : A -> Prop) (p : A -> A) (_76399 : A) (_76400 : A) : (term358 A s p _76399 _76400) = (term359 A s p _76399 _76400).
Proof. exact (@lem6000081 (term142 A _76400 s) (term360 A _76399 p _76400) (_76399 = _76400)). Qed.
Lemma lem6002399 {A : Type'} (_76399 : A) (s : A -> Prop) : (term128 A _76399 s) = (term128 A _76399 s).
Proof. exact (eq_refl (term128 A _76399 s)). Qed.
Lemma lem6002402 {A : Type'} (s : A -> Prop) (p : A -> A) (_76399 : A) (_76400 : A) : (term357 A s p _76399 _76400) = (term361 A s p _76399 _76400).
Proof. exact (MK_COMB (@lem6002399 A _76399 s) (@lem6002398 A s p _76399 _76400)). Qed.
Lemma lem6002404 {A : Type'} (s : A -> Prop) (p : A -> A) (_76399 : A) (_76400 : A) : (term136 A s p _76399 _76400) = (term361 A s p _76399 _76400).
Proof. exact (TRANS (@lem6002391 A s p _76399 _76400) (@lem6002402 A s p _76399 _76400)). Qed.
Lemma lem6002413 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : (p x') = y.
Proof. exact (proj2 (@lem6001861 A s p y x' x h1)). Qed.
Lemma lem6002417 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : (p x) = y.
Proof. exact (proj2 (@lem6001859 A s p y x' x h1)). Qed.
Lemma lem6002471 {A : Type'} (_76386 : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term122 A p _76386 s.
Proof. exact (EQ_MP (@lem6002199 A p _76386 s) (@lem6002198 A _76386 p s h1)). Qed.
Lemma lem6002500 {A : Type'} (s : A -> Prop) : (term362 A s) = (term362 A s).
Proof. exact (eq_refl (term362 A s)). Qed.
Lemma lem6002501 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : (term363 A s x'') = (term364 A s p x''').
Proof. exact (MK_COMB (@lem6002500 A s) (@lem6002281 A p x''' x'' s h1)). Qed.
Lemma lem6002502 {A : Type'} (p : A -> A) (x''' : A) (s : A -> Prop) : (term364 A s p x''') = (term365 A p x''' s).
Proof. exact (eq_refl (term364 A s p x''')). Qed.
Lemma lem6002503 {A : Type'} (s : A -> Prop) (x'' : A) : (term366 A s x'') = (term366 A s x'').
Proof. exact (eq_refl (term366 A s x'')). Qed.
Lemma lem6002504 {A : Type'} (x'' : A) (p : A -> A) (x''' : A) (s : A -> Prop) : ((term363 A s x'') = (term364 A s p x''')) = ((term363 A s x'') = (term365 A p x''' s)).
Proof. exact (MK_COMB (@lem6002503 A s x'') (@lem6002502 A p x''' s)). Qed.
Lemma lem6002505 {A : Type'} (x'' : A) (s : A -> Prop) : (term363 A s x'') = (term142 A x'' s).
Proof. exact (eq_refl (term363 A s x'')). Qed.
Lemma lem6002506 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6002507 {A : Type'} (x'' : A) (s : A -> Prop) : (term366 A s x'') = (term367 A x'' s).
Proof. exact (MK_COMB (@lem6002506) (@lem6002505 A x'' s)). Qed.
Lemma lem6002508 {A : Type'} (p : A -> A) (x''' : A) (s : A -> Prop) : (term365 A p x''' s) = (term365 A p x''' s).
Proof. exact (eq_refl (term365 A p x''' s)). Qed.
Lemma lem6002509 {A : Type'} (x'' : A) (p : A -> A) (x''' : A) (s : A -> Prop) : ((term363 A s x'') = (term365 A p x''' s)) = ((term142 A x'' s) = (term365 A p x''' s)).
Proof. exact (MK_COMB (@lem6002507 A x'' s) (@lem6002508 A p x''' s)). Qed.
Lemma lem6002510 {A : Type'} (x'' : A) (p : A -> A) (x''' : A) (s : A -> Prop) : ((term363 A s x'') = (term364 A s p x''')) = ((term142 A x'' s) = (term365 A p x''' s)).
Proof. exact (TRANS (@lem6002504 A x'' p x''' s) (@lem6002509 A x'' p x''' s)). Qed.
Lemma lem6002511 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : (term142 A x'' s) = (term365 A p x''' s).
Proof. exact (EQ_MP (@lem6002510 A x'' p x''' s) (@lem6002501 A p x''' x'' s h1)). Qed.
Lemma lem6002512 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : term365 A p x''' s.
Proof. exact (EQ_MP (@lem6002511 A p x''' x'' s h1) (@lem6002279 A p x''' x'' s h1)). Qed.
Lemma lem6002624 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : term142 A x'' s.
Proof. exact (proj2 (@lem6001840 A p x''' x'' s h1)). Qed.
Lemma lem6002638 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : x'' = (p x''').
Proof. exact (proj1 (@lem6001843 A p x''' x'' s h1)). Qed.
Lemma lem6002749 {A : Type'} (_76390 : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term122 A p _76390 s.
Proof. exact (EQ_MP (@lem6002211 A p _76390 s) (@lem6002210 A _76390 p s h1)). Qed.
Lemma lem6002778 {A : Type'} (s : A -> Prop) : (term362 A s) = (term362 A s).
Proof. exact (eq_refl (term362 A s)). Qed.
Lemma lem6002779 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : (term363 A s x'') = (term364 A s p x''').
Proof. exact (MK_COMB (@lem6002778 A s) (@lem6002638 A p x''' x'' s h1)). Qed.
Lemma lem6002780 {A : Type'} (p : A -> A) (x''' : A) (s : A -> Prop) : (term364 A s p x''') = (term365 A p x''' s).
Proof. exact (eq_refl (term364 A s p x''')). Qed.
Lemma lem6002781 {A : Type'} (s : A -> Prop) (x'' : A) : (term366 A s x'') = (term366 A s x'').
Proof. exact (eq_refl (term366 A s x'')). Qed.
Lemma lem6002782 {A : Type'} (x'' : A) (p : A -> A) (x''' : A) (s : A -> Prop) : ((term363 A s x'') = (term364 A s p x''')) = ((term363 A s x'') = (term365 A p x''' s)).
Proof. exact (MK_COMB (@lem6002781 A s x'') (@lem6002780 A p x''' s)). Qed.
Lemma lem6002783 {A : Type'} (x'' : A) (s : A -> Prop) : (term363 A s x'') = (term142 A x'' s).
Proof. exact (eq_refl (term363 A s x'')). Qed.
Lemma lem6002784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6002785 {A : Type'} (x'' : A) (s : A -> Prop) : (term366 A s x'') = (term367 A x'' s).
Proof. exact (MK_COMB (@lem6002784) (@lem6002783 A x'' s)). Qed.
Lemma lem6002786 {A : Type'} (p : A -> A) (x''' : A) (s : A -> Prop) : (term365 A p x''' s) = (term365 A p x''' s).
Proof. exact (eq_refl (term365 A p x''' s)). Qed.
Lemma lem6002787 {A : Type'} (x'' : A) (p : A -> A) (x''' : A) (s : A -> Prop) : ((term363 A s x'') = (term365 A p x''' s)) = ((term142 A x'' s) = (term365 A p x''' s)).
Proof. exact (MK_COMB (@lem6002785 A x'' s) (@lem6002786 A p x''' s)). Qed.
Lemma lem6002788 {A : Type'} (x'' : A) (p : A -> A) (x''' : A) (s : A -> Prop) : ((term363 A s x'') = (term364 A s p x''')) = ((term142 A x'' s) = (term365 A p x''' s)).
Proof. exact (TRANS (@lem6002782 A x'' p x''' s) (@lem6002787 A x'' p x''' s)). Qed.
Lemma lem6002789 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : (term142 A x'' s) = (term365 A p x''' s).
Proof. exact (EQ_MP (@lem6002788 A x'' p x''' s) (@lem6002779 A p x''' x'' s h1)). Qed.
Lemma lem6002790 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : term365 A p x''' s.
Proof. exact (EQ_MP (@lem6002789 A p x''' x'' s h1) (@lem6002624 A p x''' x'' s h1)). Qed.
Lemma lem6002861 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : y = (p x).
Proof. exact (SYM (@lem6002417 A s p y x' x h1)). Qed.
Lemma lem6002917 {A : Type'} (_76399 : A) (_76400 : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term361 A s p _76399 _76400.
Proof. exact (EQ_MP (@lem6002404 A s p _76399 _76400) (@lem6002242 A _76399 _76400 s p h1)). Qed.
Lemma lem6002944 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : term276 A x' x.
Proof. exact (proj2 (@lem6001858 A s p y x' x h1)). Qed.
Lemma lem6002959 {A : Type'} (p : A -> A) (x' : A) : (term368 A p x') = (term368 A p x').
Proof. exact (eq_refl (term368 A p x')). Qed.
Lemma lem6002960 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : (term369 A p x' y) = (term370 A x' p x).
Proof. exact (MK_COMB (@lem6002959 A p x') (@lem6002861 A s p y x' x h1)). Qed.
Lemma lem6002961 {A : Type'} (x' : A) (p : A -> A) (x : A) : (term370 A x' p x) = ((p x') = (p x)).
Proof. exact (eq_refl (term370 A x' p x)). Qed.
Lemma lem6002962 {A : Type'} (p : A -> A) (x' : A) (y : A) : (term371 A p x' y) = (term371 A p x' y).
Proof. exact (eq_refl (term371 A p x' y)). Qed.
Lemma lem6002963 {A : Type'} (y : A) (x' : A) (p : A -> A) (x : A) : ((term369 A p x' y) = (term370 A x' p x)) = ((term369 A p x' y) = ((p x') = (p x))).
Proof. exact (MK_COMB (@lem6002962 A p x' y) (@lem6002961 A x' p x)). Qed.
Lemma lem6002964 {A : Type'} (p : A -> A) (x' : A) (y : A) : (term369 A p x' y) = ((p x') = y).
Proof. exact (eq_refl (term369 A p x' y)). Qed.
Lemma lem6002965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6002966 {A : Type'} (p : A -> A) (x' : A) (y : A) : (term371 A p x' y) = (term372 A p x' y).
Proof. exact (MK_COMB (@lem6002965) (@lem6002964 A p x' y)). Qed.
Lemma lem6002967 {A : Type'} (x' : A) (p : A -> A) (x : A) : ((p x') = (p x)) = ((p x') = (p x)).
Proof. exact (eq_refl ((p x') = (p x))). Qed.
Lemma lem6002968 {A : Type'} (y : A) (x' : A) (p : A -> A) (x : A) : ((term369 A p x' y) = ((p x') = (p x))) = (((p x') = y) = ((p x') = (p x))).
Proof. exact (MK_COMB (@lem6002966 A p x' y) (@lem6002967 A x' p x)). Qed.
Lemma lem6002969 {A : Type'} (y : A) (x' : A) (p : A -> A) (x : A) : ((term369 A p x' y) = (term370 A x' p x)) = (((p x') = y) = ((p x') = (p x))).
Proof. exact (TRANS (@lem6002963 A y x' p x) (@lem6002968 A y x' p x)). Qed.
Lemma lem6002970 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : ((p x') = y) = ((p x') = (p x)).
Proof. exact (EQ_MP (@lem6002969 A y x' p x) (@lem6002960 A s p y x' x h1)). Qed.
Lemma lem6003058 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : @IN A x''' s.
Proof. exact (proj2 (@lem6001843 A p x''' x'' s h1)). Qed.
Lemma lem6003059 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : term373 A x''' s.
Proof. exact (fun h0 : term142 A x''' s => @lem6003058 A p x''' x'' s h1). Qed.
Lemma lem6003061 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003062 {A : Type'} (x''' : A) (s : A -> Prop) : (term373 A x''' s) = (@IN A x''' s).
Proof. exact (@lem6003061 (@IN A x''' s)). Qed.
Lemma lem6003063 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : @IN A x''' s.
Proof. exact (EQ_MP (@lem6003062 A x''' s) (@lem6003059 A p x''' x'' s h1)). Qed.
Lemma lem6003069 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6003070 {A : Type'} (p : A -> A) (_76386 : A) (s : A -> Prop) : (term122 A p _76386 s) = (term375 A p _76386 s).
Proof. exact (@lem6003069 (term123 A p _76386 s) (term142 A _76386 s)). Qed.
Lemma lem6003076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6003077 {A : Type'} (p : A -> A) (_76386 : A) (s : A -> Prop) : (term376 A p _76386 s) = (term377 A p _76386 s).
Proof. exact (MK_COMB (@lem6003076) (@lem6003070 A p _76386 s)). Qed.
Lemma lem6003083 {A : Type'} (p : A -> A) (_76386 : A) (s : A -> Prop) : (term375 A p _76386 s) = (term375 A p _76386 s).
Proof. exact (eq_refl (term375 A p _76386 s)). Qed.
Lemma lem6003084 {A : Type'} (p : A -> A) (_76386 : A) (s : A -> Prop) : ((term122 A p _76386 s) = (term375 A p _76386 s)) = ((term375 A p _76386 s) = (term375 A p _76386 s)).
Proof. exact (MK_COMB (@lem6003077 A p _76386 s) (@lem6003083 A p _76386 s)). Qed.
Lemma lem6003086 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6003087 (x : Prop) : (x = x) = True.
Proof. exact (@lem6003086 Prop x). Qed.
Lemma lem6003088 {A : Type'} (p : A -> A) (_76386 : A) (s : A -> Prop) : ((term375 A p _76386 s) = (term375 A p _76386 s)) = True.
Proof. exact (@lem6003087 (term375 A p _76386 s)). Qed.
Lemma lem6003089 {A : Type'} (p : A -> A) (_76386 : A) (s : A -> Prop) : ((term122 A p _76386 s) = (term375 A p _76386 s)) = True.
Proof. exact (TRANS (@lem6003084 A p _76386 s) (@lem6003088 A p _76386 s)). Qed.
Lemma lem6003090 {A : Type'} (p : A -> A) (_76386 : A) (s : A -> Prop) : True = ((term122 A p _76386 s) = (term375 A p _76386 s)).
Proof. exact (SYM (@lem6003089 A p _76386 s)). Qed.
Lemma lem6003091 {A : Type'} (p : A -> A) (_76386 : A) (s : A -> Prop) : (term122 A p _76386 s) = (term375 A p _76386 s).
Proof. exact (EQ_MP (@lem6003090 A p _76386 s) (@lem0)). Qed.
Lemma lem6003092 {A : Type'} (_76386 : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term375 A p _76386 s.
Proof. exact (EQ_MP (@lem6003091 A p _76386 s) (@lem6002471 A _76386 p s h1)). Qed.
Lemma lem6003094 (b : Prop) (a : Prop) : (a \/ b) = (term378 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6003095 {A : Type'} (p : A -> A) (_76386 : A) (s : A -> Prop) : (term375 A p _76386 s) = (term379 A p _76386 s).
Proof. exact (@lem6003094 (term142 A _76386 s) (term123 A p _76386 s)). Qed.
Lemma lem6003097 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6003098 {A : Type'} (_76386 : A) (s : A -> Prop) : (term380 A _76386 s) = (@IN A _76386 s).
Proof. exact (@lem6003097 (@IN A _76386 s)). Qed.
Lemma lem6003099 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6003100 {A : Type'} (_76386 : A) (s : A -> Prop) : (term381 A _76386 s) = (term112 A _76386 s).
Proof. exact (MK_COMB (@lem6003099) (@lem6003098 A _76386 s)). Qed.
Lemma lem6003101 {A : Type'} (p : A -> A) (_76386 : A) (s : A -> Prop) : (term123 A p _76386 s) = (term123 A p _76386 s).
Proof. exact (eq_refl (term123 A p _76386 s)). Qed.
Lemma lem6003102 {A : Type'} (p : A -> A) (_76386 : A) (s : A -> Prop) : (term379 A p _76386 s) = (term47 A p _76386 s).
Proof. exact (MK_COMB (@lem6003100 A _76386 s) (@lem6003101 A p _76386 s)). Qed.
Lemma lem6003103 {A : Type'} (p : A -> A) (_76386 : A) (s : A -> Prop) : (term375 A p _76386 s) = (term47 A p _76386 s).
Proof. exact (TRANS (@lem6003095 A p _76386 s) (@lem6003102 A p _76386 s)). Qed.
Lemma lem6003106 {A : Type'} (_76386 : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term47 A p _76386 s.
Proof. exact (EQ_MP (@lem6003103 A p _76386 s) (@lem6003092 A _76386 p s h1)). Qed.
Lemma lem6003107 {A : Type'} (_76386 : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term47 A p _76386 s.
Proof. exact (@lem6003106 A _76386 p s h1). Qed.
Lemma lem6003108 {A : Type'} (x''' : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term47 A p x''' s.
Proof. exact (@lem6003107 A x''' p s h1). Qed.
Lemma lem6003111 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term17 A p s) (h2 : term175 A p x''' x'' s) : term123 A p x''' s.
Proof. exact (@lem6003108 A x''' p s h1 (@lem6003063 A p x''' x'' s h2)). Qed.
Lemma lem6003112 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term17 A p s) (h2 : term175 A p x''' x'' s) : term382 A p x''' s.
Proof. exact (fun h0 : term365 A p x''' s => @lem6003111 A p x''' x'' s h1 h2). Qed.
Lemma lem6003114 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003115 {A : Type'} (p : A -> A) (x''' : A) (s : A -> Prop) : (term382 A p x''' s) = (term123 A p x''' s).
Proof. exact (@lem6003114 (term123 A p x''' s)). Qed.
Lemma lem6003116 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term17 A p s) (h2 : term175 A p x''' x'' s) : term123 A p x''' s.
Proof. exact (EQ_MP (@lem6003115 A p x''' s) (@lem6003112 A p x''' x'' s h1 h2)). Qed.
Lemma lem6003119 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6003121 {A : Type'} (p : A -> A) (x''' : A) (s : A -> Prop) : (term365 A p x''' s) = (term383 A p x''' s).
Proof. exact (@lem6003119 (term123 A p x''' s)). Qed.
Lemma lem6003124 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : term383 A p x''' s.
Proof. exact (EQ_MP (@lem6003121 A p x''' s) (@lem6002512 A p x''' x'' s h1)). Qed.
Lemma lem6003127 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term17 A p s) (h2 : term175 A p x''' x'' s) : False.
Proof. exact (@lem6003124 A p x''' x'' s h2 (@lem6003116 A p x''' x'' s h1 h2)). Qed.
Lemma lem6003128 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term17 A p s) (h2 : term175 A p x''' x'' s) : term384.
Proof. exact (fun h0 : ~ False => @lem6003127 A p x''' x'' s h1 h2). Qed.
Lemma lem6003130 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003131 : term384 = False.
Proof. exact (@lem6003130 False). Qed.
Lemma lem6003177 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : @IN A x''' s.
Proof. exact (proj2 (@lem6001843 A p x''' x'' s h1)). Qed.
Lemma lem6003178 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : term373 A x''' s.
Proof. exact (fun h0 : term142 A x''' s => @lem6003177 A p x''' x'' s h1). Qed.
Lemma lem6003180 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003181 {A : Type'} (x''' : A) (s : A -> Prop) : (term373 A x''' s) = (@IN A x''' s).
Proof. exact (@lem6003180 (@IN A x''' s)). Qed.
Lemma lem6003182 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : @IN A x''' s.
Proof. exact (EQ_MP (@lem6003181 A x''' s) (@lem6003178 A p x''' x'' s h1)). Qed.
Lemma lem6003188 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6003189 {A : Type'} (p : A -> A) (_76390 : A) (s : A -> Prop) : (term122 A p _76390 s) = (term375 A p _76390 s).
Proof. exact (@lem6003188 (term123 A p _76390 s) (term142 A _76390 s)). Qed.
Lemma lem6003195 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6003196 {A : Type'} (p : A -> A) (_76390 : A) (s : A -> Prop) : (term376 A p _76390 s) = (term377 A p _76390 s).
Proof. exact (MK_COMB (@lem6003195) (@lem6003189 A p _76390 s)). Qed.
Lemma lem6003202 {A : Type'} (p : A -> A) (_76390 : A) (s : A -> Prop) : (term375 A p _76390 s) = (term375 A p _76390 s).
Proof. exact (eq_refl (term375 A p _76390 s)). Qed.
Lemma lem6003203 {A : Type'} (p : A -> A) (_76390 : A) (s : A -> Prop) : ((term122 A p _76390 s) = (term375 A p _76390 s)) = ((term375 A p _76390 s) = (term375 A p _76390 s)).
Proof. exact (MK_COMB (@lem6003196 A p _76390 s) (@lem6003202 A p _76390 s)). Qed.
Lemma lem6003205 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6003206 (x : Prop) : (x = x) = True.
Proof. exact (@lem6003205 Prop x). Qed.
Lemma lem6003207 {A : Type'} (p : A -> A) (_76390 : A) (s : A -> Prop) : ((term375 A p _76390 s) = (term375 A p _76390 s)) = True.
Proof. exact (@lem6003206 (term375 A p _76390 s)). Qed.
Lemma lem6003208 {A : Type'} (p : A -> A) (_76390 : A) (s : A -> Prop) : ((term122 A p _76390 s) = (term375 A p _76390 s)) = True.
Proof. exact (TRANS (@lem6003203 A p _76390 s) (@lem6003207 A p _76390 s)). Qed.
Lemma lem6003209 {A : Type'} (p : A -> A) (_76390 : A) (s : A -> Prop) : True = ((term122 A p _76390 s) = (term375 A p _76390 s)).
Proof. exact (SYM (@lem6003208 A p _76390 s)). Qed.
Lemma lem6003210 {A : Type'} (p : A -> A) (_76390 : A) (s : A -> Prop) : (term122 A p _76390 s) = (term375 A p _76390 s).
Proof. exact (EQ_MP (@lem6003209 A p _76390 s) (@lem0)). Qed.
Lemma lem6003211 {A : Type'} (_76390 : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term375 A p _76390 s.
Proof. exact (EQ_MP (@lem6003210 A p _76390 s) (@lem6002749 A _76390 p s h1)). Qed.
Lemma lem6003213 (b : Prop) (a : Prop) : (a \/ b) = (term378 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6003214 {A : Type'} (p : A -> A) (_76390 : A) (s : A -> Prop) : (term375 A p _76390 s) = (term379 A p _76390 s).
Proof. exact (@lem6003213 (term142 A _76390 s) (term123 A p _76390 s)). Qed.
Lemma lem6003216 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6003217 {A : Type'} (_76390 : A) (s : A -> Prop) : (term380 A _76390 s) = (@IN A _76390 s).
Proof. exact (@lem6003216 (@IN A _76390 s)). Qed.
Lemma lem6003218 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6003219 {A : Type'} (_76390 : A) (s : A -> Prop) : (term381 A _76390 s) = (term112 A _76390 s).
Proof. exact (MK_COMB (@lem6003218) (@lem6003217 A _76390 s)). Qed.
Lemma lem6003220 {A : Type'} (p : A -> A) (_76390 : A) (s : A -> Prop) : (term123 A p _76390 s) = (term123 A p _76390 s).
Proof. exact (eq_refl (term123 A p _76390 s)). Qed.
Lemma lem6003221 {A : Type'} (p : A -> A) (_76390 : A) (s : A -> Prop) : (term379 A p _76390 s) = (term47 A p _76390 s).
Proof. exact (MK_COMB (@lem6003219 A _76390 s) (@lem6003220 A p _76390 s)). Qed.
Lemma lem6003222 {A : Type'} (p : A -> A) (_76390 : A) (s : A -> Prop) : (term375 A p _76390 s) = (term47 A p _76390 s).
Proof. exact (TRANS (@lem6003214 A p _76390 s) (@lem6003221 A p _76390 s)). Qed.
Lemma lem6003225 {A : Type'} (_76390 : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term47 A p _76390 s.
Proof. exact (EQ_MP (@lem6003222 A p _76390 s) (@lem6003211 A _76390 p s h1)). Qed.
Lemma lem6003226 {A : Type'} (_76390 : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term47 A p _76390 s.
Proof. exact (@lem6003225 A _76390 p s h1). Qed.
Lemma lem6003227 {A : Type'} (x''' : A) (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term47 A p x''' s.
Proof. exact (@lem6003226 A x''' p s h1). Qed.
Lemma lem6003230 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term17 A p s) (h2 : term175 A p x''' x'' s) : term123 A p x''' s.
Proof. exact (@lem6003227 A x''' p s h1 (@lem6003182 A p x''' x'' s h2)). Qed.
Lemma lem6003231 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term17 A p s) (h2 : term175 A p x''' x'' s) : term382 A p x''' s.
Proof. exact (fun h0 : term365 A p x''' s => @lem6003230 A p x''' x'' s h1 h2). Qed.
Lemma lem6003233 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003234 {A : Type'} (p : A -> A) (x''' : A) (s : A -> Prop) : (term382 A p x''' s) = (term123 A p x''' s).
Proof. exact (@lem6003233 (term123 A p x''' s)). Qed.
Lemma lem6003235 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term17 A p s) (h2 : term175 A p x''' x'' s) : term123 A p x''' s.
Proof. exact (EQ_MP (@lem6003234 A p x''' s) (@lem6003231 A p x''' x'' s h1 h2)). Qed.
Lemma lem6003238 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6003240 {A : Type'} (p : A -> A) (x''' : A) (s : A -> Prop) : (term365 A p x''' s) = (term383 A p x''' s).
Proof. exact (@lem6003238 (term123 A p x''' s)). Qed.
Lemma lem6003243 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term175 A p x''' x'' s) : term383 A p x''' s.
Proof. exact (EQ_MP (@lem6003240 A p x''' s) (@lem6002790 A p x''' x'' s h1)). Qed.
Lemma lem6003246 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term17 A p s) (h2 : term175 A p x''' x'' s) : False.
Proof. exact (@lem6003243 A p x''' x'' s h2 (@lem6003235 A p x''' x'' s h1 h2)). Qed.
Lemma lem6003247 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term17 A p s) (h2 : term175 A p x''' x'' s) : term384.
Proof. exact (fun h0 : ~ False => @lem6003246 A p x''' x'' s h1 h2). Qed.
Lemma lem6003249 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003250 : term384 = False.
Proof. exact (@lem6003249 False). Qed.
Lemma lem6003304 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : @IN A y s.
Proof. exact (h1). Qed.
Lemma lem6003305 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : term373 A y s.
Proof. exact (fun h0 : term142 A y s => @lem6003304 A y s h1). Qed.
Lemma lem6003307 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003308 {A : Type'} (y : A) (s : A -> Prop) : (term373 A y s) = (@IN A y s).
Proof. exact (@lem6003307 (@IN A y s)). Qed.
Lemma lem6003309 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : @IN A y s.
Proof. exact (EQ_MP (@lem6003308 A y s) (@lem6003305 A y s h1)). Qed.
Lemma lem6003315 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6003316 {A : Type'} (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : (term122 A x'''' _76396 s) = (term375 A x'''' _76396 s).
Proof. exact (@lem6003315 (term123 A x'''' _76396 s) (term142 A _76396 s)). Qed.
Lemma lem6003322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6003323 {A : Type'} (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : (term376 A x'''' _76396 s) = (term377 A x'''' _76396 s).
Proof. exact (MK_COMB (@lem6003322) (@lem6003316 A x'''' _76396 s)). Qed.
Lemma lem6003329 {A : Type'} (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : (term375 A x'''' _76396 s) = (term375 A x'''' _76396 s).
Proof. exact (eq_refl (term375 A x'''' _76396 s)). Qed.
Lemma lem6003330 {A : Type'} (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : ((term122 A x'''' _76396 s) = (term375 A x'''' _76396 s)) = ((term375 A x'''' _76396 s) = (term375 A x'''' _76396 s)).
Proof. exact (MK_COMB (@lem6003323 A x'''' _76396 s) (@lem6003329 A x'''' _76396 s)). Qed.
Lemma lem6003332 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6003333 (x : Prop) : (x = x) = True.
Proof. exact (@lem6003332 Prop x). Qed.
Lemma lem6003334 {A : Type'} (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : ((term375 A x'''' _76396 s) = (term375 A x'''' _76396 s)) = True.
Proof. exact (@lem6003333 (term375 A x'''' _76396 s)). Qed.
Lemma lem6003335 {A : Type'} (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : ((term122 A x'''' _76396 s) = (term375 A x'''' _76396 s)) = True.
Proof. exact (TRANS (@lem6003330 A x'''' _76396 s) (@lem6003334 A x'''' _76396 s)). Qed.
Lemma lem6003336 {A : Type'} (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : True = ((term122 A x'''' _76396 s) = (term375 A x'''' _76396 s)).
Proof. exact (SYM (@lem6003335 A x'''' _76396 s)). Qed.
Lemma lem6003337 {A : Type'} (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : (term122 A x'''' _76396 s) = (term375 A x'''' _76396 s).
Proof. exact (EQ_MP (@lem6003336 A x'''' _76396 s) (@lem0)). Qed.
Lemma lem6003338 {A : Type'} (_76396 : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term219 A s p x'''') : term375 A x'''' _76396 s.
Proof. exact (EQ_MP (@lem6003337 A x'''' _76396 s) (@lem6002373 A _76396 s p x'''' h1)). Qed.
Lemma lem6003340 (b : Prop) (a : Prop) : (a \/ b) = (term378 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6003341 {A : Type'} (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : (term375 A x'''' _76396 s) = (term379 A x'''' _76396 s).
Proof. exact (@lem6003340 (term142 A _76396 s) (term123 A x'''' _76396 s)). Qed.
Lemma lem6003343 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6003344 {A : Type'} (_76396 : A) (s : A -> Prop) : (term380 A _76396 s) = (@IN A _76396 s).
Proof. exact (@lem6003343 (@IN A _76396 s)). Qed.
Lemma lem6003345 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6003346 {A : Type'} (_76396 : A) (s : A -> Prop) : (term381 A _76396 s) = (term112 A _76396 s).
Proof. exact (MK_COMB (@lem6003345) (@lem6003344 A _76396 s)). Qed.
Lemma lem6003347 {A : Type'} (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : (term123 A x'''' _76396 s) = (term123 A x'''' _76396 s).
Proof. exact (eq_refl (term123 A x'''' _76396 s)). Qed.
Lemma lem6003348 {A : Type'} (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : (term379 A x'''' _76396 s) = (term47 A x'''' _76396 s).
Proof. exact (MK_COMB (@lem6003346 A _76396 s) (@lem6003347 A x'''' _76396 s)). Qed.
Lemma lem6003349 {A : Type'} (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : (term375 A x'''' _76396 s) = (term47 A x'''' _76396 s).
Proof. exact (TRANS (@lem6003341 A x'''' _76396 s) (@lem6003348 A x'''' _76396 s)). Qed.
Lemma lem6003352 {A : Type'} (_76396 : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term219 A s p x'''') : term47 A x'''' _76396 s.
Proof. exact (EQ_MP (@lem6003349 A x'''' _76396 s) (@lem6003338 A _76396 s p x'''' h1)). Qed.
Lemma lem6003353 {A : Type'} (_76396 : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term219 A s p x'''') : term47 A x'''' _76396 s.
Proof. exact (@lem6003352 A _76396 s p x'''' h1). Qed.
Lemma lem6003354 {A : Type'} (y : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term219 A s p x'''') : term47 A x'''' y s.
Proof. exact (@lem6003353 A y s p x'''' h1). Qed.
Lemma lem6003357 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term219 A s p x'''') (h2 : @IN A y s) : term123 A x'''' y s.
Proof. exact (@lem6003354 A y s p x'''' h1 (@lem6003309 A y s h2)). Qed.
Lemma lem6003358 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term219 A s p x'''') (h2 : @IN A y s) : term382 A x'''' y s.
Proof. exact (fun h0 : term365 A x'''' y s => @lem6003357 A p x'''' y s h1 h2). Qed.
Lemma lem6003360 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003361 {A : Type'} (x'''' : A -> A) (y : A) (s : A -> Prop) : (term382 A x'''' y s) = (term123 A x'''' y s).
Proof. exact (@lem6003360 (term123 A x'''' y s)). Qed.
Lemma lem6003362 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term219 A s p x'''') (h2 : @IN A y s) : term123 A x'''' y s.
Proof. exact (EQ_MP (@lem6003361 A x'''' y s) (@lem6003358 A p x'''' y s h1 h2)). Qed.
Lemma lem6003364 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : @IN A y s.
Proof. exact (h1). Qed.
Lemma lem6003365 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : term373 A y s.
Proof. exact (fun h0 : term142 A y s => @lem6003364 A y s h1). Qed.
Lemma lem6003367 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003368 {A : Type'} (y : A) (s : A -> Prop) : (term373 A y s) = (@IN A y s).
Proof. exact (@lem6003367 (@IN A y s)). Qed.
Lemma lem6003369 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : @IN A y s.
Proof. exact (EQ_MP (@lem6003368 A y s) (@lem6003365 A y s h1)). Qed.
Lemma lem6003375 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6003376 {A : Type'} (p : A -> A) (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : (term356 A s p x'''' _76396) = (term385 A p x'''' _76396 s).
Proof. exact (@lem6003375 ((term348 A p x'''' _76396) = _76396) (term142 A _76396 s)). Qed.
Lemma lem6003384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6003385 {A : Type'} (p : A -> A) (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : (term386 A s p x'''' _76396) = (term387 A p x'''' _76396 s).
Proof. exact (MK_COMB (@lem6003384) (@lem6003376 A p x'''' _76396 s)). Qed.
Lemma lem6003393 {A : Type'} (p : A -> A) (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : (term385 A p x'''' _76396 s) = (term385 A p x'''' _76396 s).
Proof. exact (eq_refl (term385 A p x'''' _76396 s)). Qed.
Lemma lem6003394 {A : Type'} (p : A -> A) (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : ((term356 A s p x'''' _76396) = (term385 A p x'''' _76396 s)) = ((term385 A p x'''' _76396 s) = (term385 A p x'''' _76396 s)).
Proof. exact (MK_COMB (@lem6003385 A p x'''' _76396 s) (@lem6003393 A p x'''' _76396 s)). Qed.
Lemma lem6003396 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6003397 (x : Prop) : (x = x) = True.
Proof. exact (@lem6003396 Prop x). Qed.
Lemma lem6003398 {A : Type'} (p : A -> A) (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : ((term385 A p x'''' _76396 s) = (term385 A p x'''' _76396 s)) = True.
Proof. exact (@lem6003397 (term385 A p x'''' _76396 s)). Qed.
Lemma lem6003399 {A : Type'} (p : A -> A) (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : ((term356 A s p x'''' _76396) = (term385 A p x'''' _76396 s)) = True.
Proof. exact (TRANS (@lem6003394 A p x'''' _76396 s) (@lem6003398 A p x'''' _76396 s)). Qed.
Lemma lem6003400 {A : Type'} (p : A -> A) (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : True = ((term356 A s p x'''' _76396) = (term385 A p x'''' _76396 s)).
Proof. exact (SYM (@lem6003399 A p x'''' _76396 s)). Qed.
Lemma lem6003401 {A : Type'} (p : A -> A) (x'''' : A -> A) (_76396 : A) (s : A -> Prop) : (term356 A s p x'''' _76396) = (term385 A p x'''' _76396 s).
Proof. exact (EQ_MP (@lem6003400 A p x'''' _76396 s) (@lem0)). Qed.
Lemma lem6003402 {A : Type'} (_76396 : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term219 A s p x'''') : term385 A p x'''' _76396 s.
Proof. exact (EQ_MP (@lem6003401 A p x'''' _76396 s) (@lem6002379 A _76396 s p x'''' h1)). Qed.
Lemma lem6003404 (b : Prop) (a : Prop) : (a \/ b) = (term378 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6003405 {A : Type'} (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (_76396 : A) : (term385 A p x'''' _76396 s) = (term388 A s p x'''' _76396).
Proof. exact (@lem6003404 (term142 A _76396 s) ((term348 A p x'''' _76396) = _76396)). Qed.
Lemma lem6003407 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6003408 {A : Type'} (_76396 : A) (s : A -> Prop) : (term380 A _76396 s) = (@IN A _76396 s).
Proof. exact (@lem6003407 (@IN A _76396 s)). Qed.
Lemma lem6003409 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6003410 {A : Type'} (_76396 : A) (s : A -> Prop) : (term381 A _76396 s) = (term112 A _76396 s).
Proof. exact (MK_COMB (@lem6003409) (@lem6003408 A _76396 s)). Qed.
Lemma lem6003411 {A : Type'} (p : A -> A) (x'''' : A -> A) (_76396 : A) : ((term348 A p x'''' _76396) = _76396) = ((term348 A p x'''' _76396) = _76396).
Proof. exact (eq_refl ((term348 A p x'''' _76396) = _76396)). Qed.
Lemma lem6003412 {A : Type'} (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (_76396 : A) : (term388 A s p x'''' _76396) = (term389 A s p x'''' _76396).
Proof. exact (MK_COMB (@lem6003410 A _76396 s) (@lem6003411 A p x'''' _76396)). Qed.
Lemma lem6003413 {A : Type'} (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (_76396 : A) : (term385 A p x'''' _76396 s) = (term389 A s p x'''' _76396).
Proof. exact (TRANS (@lem6003405 A s p x'''' _76396) (@lem6003412 A s p x'''' _76396)). Qed.
Lemma lem6003416 {A : Type'} (_76396 : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term219 A s p x'''') : term389 A s p x'''' _76396.
Proof. exact (EQ_MP (@lem6003413 A s p x'''' _76396) (@lem6003402 A _76396 s p x'''' h1)). Qed.
Lemma lem6003417 {A : Type'} (_76396 : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term219 A s p x'''') : term389 A s p x'''' _76396.
Proof. exact (@lem6003416 A _76396 s p x'''' h1). Qed.
Lemma lem6003418 {A : Type'} (y : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term219 A s p x'''') : term389 A s p x'''' y.
Proof. exact (@lem6003417 A y s p x'''' h1). Qed.
Lemma lem6003421 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term219 A s p x'''') (h2 : @IN A y s) : (term348 A p x'''' y) = y.
Proof. exact (@lem6003418 A y s p x'''' h1 (@lem6003369 A y s h2)). Qed.
Lemma lem6003422 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term219 A s p x'''') (h2 : @IN A y s) : term390 A p x'''' y.
Proof. exact (fun h0 : term391 A p x'''' y => @lem6003421 A p x'''' y s h1 h2). Qed.
Lemma lem6003424 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003425 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) : (term390 A p x'''' y) = ((term348 A p x'''' y) = y).
Proof. exact (@lem6003424 ((term348 A p x'''' y) = y)). Qed.
Lemma lem6003426 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term219 A s p x'''') (h2 : @IN A y s) : (term348 A p x'''' y) = y.
Proof. exact (EQ_MP (@lem6003425 A p x'''' y) (@lem6003422 A p x'''' y s h1 h2)). Qed.
Lemma lem6003428 (a : Prop) (b : Prop) : (term392 a b) = (term393 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem6003429 {A : Type'} (s : A -> Prop) (p : A -> A) (_76397 : A) (y : A) : (term275 A s p _76397 y) = (term274 A s p _76397 y).
Proof. exact (@lem6003428 (@IN A _76397 s) ((p _76397) = y)). Qed.
Lemma lem6003431 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6003432 {A : Type'} (s : A -> Prop) (p : A -> A) (_76397 : A) (y : A) : (term274 A s p _76397 y) = (term394 A s p _76397 y).
Proof. exact (@lem6003431 (term109 A s p _76397 y)). Qed.
Lemma lem6003433 {A : Type'} (s : A -> Prop) (p : A -> A) (_76397 : A) (y : A) : (term275 A s p _76397 y) = (term394 A s p _76397 y).
Proof. exact (TRANS (@lem6003429 A s p _76397 y) (@lem6003432 A s p _76397 y)). Qed.
Lemma lem6003435 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term219 A s p x'''') (h2 : @IN A y s) : term395 A s p x'''' y.
Proof. exact (conj (@lem6003362 A p x'''' y s h1 h2) (@lem6003426 A p x'''' y s h1 h2)). Qed.
Lemma lem6003437 {A : Type'} (_76397 : A) (s : A -> Prop) (p : A -> A) (y : A) (h1 : term298 A s p y) : term394 A s p _76397 y.
Proof. exact (EQ_MP (@lem6003433 A s p _76397 y) (@lem6002367 A _76397 s p y h1)). Qed.
Lemma lem6003438 {A : Type'} (_76397 : A) (s : A -> Prop) (p : A -> A) (y : A) (h1 : term298 A s p y) : term394 A s p _76397 y.
Proof. exact (@lem6003437 A _76397 s p y h1). Qed.
Lemma lem6003439 {A : Type'} (x'''' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (h1 : term298 A s p y) : term396 A s p x'''' y.
Proof. exact (@lem6003438 A (x'''' y) s p y h1). Qed.
Lemma lem6003442 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term298 A s p y) (h2 : term219 A s p x'''') (h3 : @IN A y s) : False.
Proof. exact (@lem6003439 A x'''' s p y h1 (@lem6003435 A p x'''' y s h2 h3)). Qed.
Lemma lem6003443 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term298 A s p y) (h2 : term219 A s p x'''') (h3 : @IN A y s) : term384.
Proof. exact (fun h0 : ~ False => @lem6003442 A p x'''' y s h1 h2 h3). Qed.
Lemma lem6003445 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003446 : term384 = False.
Proof. exact (@lem6003445 False). Qed.
Lemma lem6003447 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term298 A s p y) (h2 : term219 A s p x'''') (h3 : @IN A y s) : False.
Proof. exact (EQ_MP (@lem6003446) (@lem6003443 A p x'''' y s h1 h2 h3)). Qed.
Lemma lem6003500 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : @IN A x' s.
Proof. exact (proj1 (@lem6001861 A s p y x' x h1)). Qed.
Lemma lem6003501 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : term373 A x' s.
Proof. exact (fun h0 : term142 A x' s => @lem6003500 A s p y x' x h1). Qed.
Lemma lem6003503 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003504 {A : Type'} (x' : A) (s : A -> Prop) : (term373 A x' s) = (@IN A x' s).
Proof. exact (@lem6003503 (@IN A x' s)). Qed.
Lemma lem6003505 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : @IN A x' s.
Proof. exact (EQ_MP (@lem6003504 A x' s) (@lem6003501 A s p y x' x h1)). Qed.
Lemma lem6003507 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : @IN A x s.
Proof. exact (proj1 (@lem6001859 A s p y x' x h1)). Qed.
Lemma lem6003508 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : term373 A x s.
Proof. exact (fun h0 : term142 A x s => @lem6003507 A s p y x' x h1). Qed.
Lemma lem6003510 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003511 {A : Type'} (x : A) (s : A -> Prop) : (term373 A x s) = (@IN A x s).
Proof. exact (@lem6003510 (@IN A x s)). Qed.
Lemma lem6003512 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : @IN A x s.
Proof. exact (EQ_MP (@lem6003511 A x s) (@lem6003508 A s p y x' x h1)). Qed.
Lemma lem6003514 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : (p x') = (p x).
Proof. exact (EQ_MP (@lem6002970 A s p y x' x h1) (@lem6002413 A s p y x' x h1)). Qed.
Lemma lem6003515 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : term397 A x' p x.
Proof. exact (fun h0 : term360 A x' p x => @lem6003514 A s p y x' x h1). Qed.
Lemma lem6003517 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003518 {A : Type'} (x' : A) (p : A -> A) (x : A) : (term397 A x' p x) = ((p x') = (p x)).
Proof. exact (@lem6003517 ((p x') = (p x))). Qed.
Lemma lem6003519 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : (p x') = (p x).
Proof. exact (EQ_MP (@lem6003518 A x' p x) (@lem6003515 A s p y x' x h1)). Qed.
Lemma lem6003535 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6003536 {A : Type'} (p : A -> A) (s : A -> Prop) (_76399 : A) (_76400 : A) : (term359 A s p _76399 _76400) = (term398 A p s _76399 _76400).
Proof. exact (@lem6003535 (term360 A _76399 p _76400) (term142 A _76400 s) (_76399 = _76400)). Qed.
Lemma lem6003552 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6003553 {A : Type'} (_76399 : A) (_76400 : A) (s : A -> Prop) : (term399 A s _76399 _76400) = (term400 A _76399 _76400 s).
Proof. exact (@lem6003552 (_76399 = _76400) (term142 A _76400 s)). Qed.
Lemma lem6003561 {A : Type'} (_76399 : A) (p : A -> A) (_76400 : A) : (term401 A _76399 p _76400) = (term401 A _76399 p _76400).
Proof. exact (eq_refl (term401 A _76399 p _76400)). Qed.
Lemma lem6003562 {A : Type'} (p : A -> A) (_76399 : A) (_76400 : A) (s : A -> Prop) : (term398 A p s _76399 _76400) = (term402 A p _76399 _76400 s).
Proof. exact (MK_COMB (@lem6003561 A _76399 p _76400) (@lem6003553 A _76399 _76400 s)). Qed.
Lemma lem6003566 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6003567 {A : Type'} (_76399 : A) (p : A -> A) (_76400 : A) (s : A -> Prop) : (term402 A p _76399 _76400 s) = (term403 A _76399 p _76400 s).
Proof. exact (@lem6003566 (_76399 = _76400) (term360 A _76399 p _76400) (term142 A _76400 s)). Qed.
Lemma lem6003587 {A : Type'} (_76399 : A) (p : A -> A) (_76400 : A) (s : A -> Prop) : (term398 A p s _76399 _76400) = (term403 A _76399 p _76400 s).
Proof. exact (TRANS (@lem6003562 A p _76399 _76400 s) (@lem6003567 A _76399 p _76400 s)). Qed.
Lemma lem6003588 {A : Type'} (_76399 : A) (p : A -> A) (_76400 : A) (s : A -> Prop) : (term359 A s p _76399 _76400) = (term403 A _76399 p _76400 s).
Proof. exact (TRANS (@lem6003536 A p s _76399 _76400) (@lem6003587 A _76399 p _76400 s)). Qed.
Lemma lem6003589 {A : Type'} (_76399 : A) (s : A -> Prop) : (term128 A _76399 s) = (term128 A _76399 s).
Proof. exact (eq_refl (term128 A _76399 s)). Qed.
Lemma lem6003590 {A : Type'} (_76399 : A) (p : A -> A) (_76400 : A) (s : A -> Prop) : (term361 A s p _76399 _76400) = (term404 A _76399 p _76400 s).
Proof. exact (MK_COMB (@lem6003589 A _76399 s) (@lem6003588 A _76399 p _76400 s)). Qed.
Lemma lem6003594 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6003595 {A : Type'} (_76399 : A) (p : A -> A) (_76400 : A) (s : A -> Prop) : (term404 A _76399 p _76400 s) = (term405 A _76399 p _76400 s).
Proof. exact (@lem6003594 (_76399 = _76400) (term142 A _76399 s) (term406 A _76399 p _76400 s)). Qed.
Lemma lem6003611 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6003612 {A : Type'} (p : A -> A) (_76399 : A) (_76400 : A) (s : A -> Prop) : (term407 A _76399 p _76400 s) = (term408 A p _76399 _76400 s).
Proof. exact (@lem6003611 (term360 A _76399 p _76400) (term142 A _76399 s) (term142 A _76400 s)). Qed.
Lemma lem6003630 {A : Type'} (_76399 : A) (_76400 : A) : (term409 A _76399 _76400) = (term409 A _76399 _76400).
Proof. exact (eq_refl (term409 A _76399 _76400)). Qed.
Lemma lem6003631 {A : Type'} (p : A -> A) (_76399 : A) (_76400 : A) (s : A -> Prop) : (term405 A _76399 p _76400 s) = (term410 A p _76399 _76400 s).
Proof. exact (MK_COMB (@lem6003630 A _76399 _76400) (@lem6003612 A p _76399 _76400 s)). Qed.
Lemma lem6003642 {A : Type'} (p : A -> A) (_76399 : A) (_76400 : A) (s : A -> Prop) : (term404 A _76399 p _76400 s) = (term410 A p _76399 _76400 s).
Proof. exact (TRANS (@lem6003595 A _76399 p _76400 s) (@lem6003631 A p _76399 _76400 s)). Qed.
Lemma lem6003643 {A : Type'} (p : A -> A) (_76399 : A) (_76400 : A) (s : A -> Prop) : (term361 A s p _76399 _76400) = (term410 A p _76399 _76400 s).
Proof. exact (TRANS (@lem6003590 A _76399 p _76400 s) (@lem6003642 A p _76399 _76400 s)). Qed.
Lemma lem6003644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6003645 {A : Type'} (p : A -> A) (_76399 : A) (_76400 : A) (s : A -> Prop) : (term411 A s p _76399 _76400) = (term412 A p _76399 _76400 s).
Proof. exact (MK_COMB (@lem6003644) (@lem6003643 A p _76399 _76400 s)). Qed.
Lemma lem6003671 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6003672 {A : Type'} (_76399 : A) (p : A -> A) (_76400 : A) (s : A -> Prop) : (term127 A s _76399 p _76400) = (term406 A _76399 p _76400 s).
Proof. exact (@lem6003671 (term360 A _76399 p _76400) (term142 A _76400 s)). Qed.
Lemma lem6003680 {A : Type'} (_76399 : A) (s : A -> Prop) : (term128 A _76399 s) = (term128 A _76399 s).
Proof. exact (eq_refl (term128 A _76399 s)). Qed.
Lemma lem6003681 {A : Type'} (_76399 : A) (p : A -> A) (_76400 : A) (s : A -> Prop) : (term130 A s _76399 p _76400) = (term407 A _76399 p _76400 s).
Proof. exact (MK_COMB (@lem6003680 A _76399 s) (@lem6003672 A _76399 p _76400 s)). Qed.
Lemma lem6003685 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6003686 {A : Type'} (p : A -> A) (_76399 : A) (_76400 : A) (s : A -> Prop) : (term407 A _76399 p _76400 s) = (term408 A p _76399 _76400 s).
Proof. exact (@lem6003685 (term360 A _76399 p _76400) (term142 A _76399 s) (term142 A _76400 s)). Qed.
Lemma lem6003704 {A : Type'} (p : A -> A) (_76399 : A) (_76400 : A) (s : A -> Prop) : (term130 A s _76399 p _76400) = (term408 A p _76399 _76400 s).
Proof. exact (TRANS (@lem6003681 A _76399 p _76400 s) (@lem6003686 A p _76399 _76400 s)). Qed.
Lemma lem6003705 {A : Type'} (_76399 : A) (_76400 : A) : (term409 A _76399 _76400) = (term409 A _76399 _76400).
Proof. exact (eq_refl (term409 A _76399 _76400)). Qed.
Lemma lem6003706 {A : Type'} (p : A -> A) (_76399 : A) (_76400 : A) (s : A -> Prop) : (term413 A s _76399 p _76400) = (term410 A p _76399 _76400 s).
Proof. exact (MK_COMB (@lem6003705 A _76399 _76400) (@lem6003704 A p _76399 _76400 s)). Qed.
Lemma lem6003717 {A : Type'} (p : A -> A) (_76399 : A) (_76400 : A) (s : A -> Prop) : ((term361 A s p _76399 _76400) = (term413 A s _76399 p _76400)) = ((term410 A p _76399 _76400 s) = (term410 A p _76399 _76400 s)).
Proof. exact (MK_COMB (@lem6003645 A p _76399 _76400 s) (@lem6003706 A p _76399 _76400 s)). Qed.
Lemma lem6003719 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6003720 (x : Prop) : (x = x) = True.
Proof. exact (@lem6003719 Prop x). Qed.
Lemma lem6003721 {A : Type'} (p : A -> A) (_76399 : A) (_76400 : A) (s : A -> Prop) : ((term410 A p _76399 _76400 s) = (term410 A p _76399 _76400 s)) = True.
Proof. exact (@lem6003720 (term410 A p _76399 _76400 s)). Qed.
Lemma lem6003722 {A : Type'} (s : A -> Prop) (_76399 : A) (p : A -> A) (_76400 : A) : ((term361 A s p _76399 _76400) = (term413 A s _76399 p _76400)) = True.
Proof. exact (TRANS (@lem6003717 A p _76399 _76400 s) (@lem6003721 A p _76399 _76400 s)). Qed.
Lemma lem6003723 {A : Type'} (s : A -> Prop) (_76399 : A) (p : A -> A) (_76400 : A) : True = ((term361 A s p _76399 _76400) = (term413 A s _76399 p _76400)).
Proof. exact (SYM (@lem6003722 A s _76399 p _76400)). Qed.
Lemma lem6003724 {A : Type'} (s : A -> Prop) (_76399 : A) (p : A -> A) (_76400 : A) : (term361 A s p _76399 _76400) = (term413 A s _76399 p _76400).
Proof. exact (EQ_MP (@lem6003723 A s _76399 p _76400) (@lem0)). Qed.
Lemma lem6003725 {A : Type'} (_76399 : A) (_76400 : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term413 A s _76399 p _76400.
Proof. exact (EQ_MP (@lem6003724 A s _76399 p _76400) (@lem6002917 A _76399 _76400 s p h1)). Qed.
Lemma lem6003727 (b : Prop) (a : Prop) : (a \/ b) = (term378 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6003728 {A : Type'} (s : A -> Prop) (p : A -> A) (_76399 : A) (_76400 : A) : (term413 A s _76399 p _76400) = (term414 A s p _76399 _76400).
Proof. exact (@lem6003727 (term130 A s _76399 p _76400) (_76399 = _76400)). Qed.
Lemma lem6003730 (a : Prop) (b : Prop) : (term415 a b) = (term416 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6003731 {A : Type'} (s : A -> Prop) (_76399 : A) (p : A -> A) (_76400 : A) : (term417 A s _76399 p _76400) = (term418 A s _76399 p _76400).
Proof. exact (@lem6003730 (term142 A _76399 s) (term127 A s _76399 p _76400)). Qed.
Lemma lem6003733 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6003734 {A : Type'} (_76399 : A) (s : A -> Prop) : (term380 A _76399 s) = (@IN A _76399 s).
Proof. exact (@lem6003733 (@IN A _76399 s)). Qed.
Lemma lem6003735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6003736 {A : Type'} (_76399 : A) (s : A -> Prop) : (term419 A _76399 s) = (term420 A _76399 s).
Proof. exact (MK_COMB (@lem6003735) (@lem6003734 A _76399 s)). Qed.
Lemma lem6003738 (a : Prop) (b : Prop) : (term415 a b) = (term416 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6003739 {A : Type'} (s : A -> Prop) (_76399 : A) (p : A -> A) (_76400 : A) : (term421 A s _76399 p _76400) = (term422 A s _76399 p _76400).
Proof. exact (@lem6003738 (term142 A _76400 s) (term360 A _76399 p _76400)). Qed.
Lemma lem6003741 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6003742 {A : Type'} (_76400 : A) (s : A -> Prop) : (term380 A _76400 s) = (@IN A _76400 s).
Proof. exact (@lem6003741 (@IN A _76400 s)). Qed.
Lemma lem6003743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6003744 {A : Type'} (_76400 : A) (s : A -> Prop) : (term419 A _76400 s) = (term420 A _76400 s).
Proof. exact (MK_COMB (@lem6003743) (@lem6003742 A _76400 s)). Qed.
Lemma lem6003746 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6003747 {A : Type'} (_76399 : A) (p : A -> A) (_76400 : A) : (term423 A _76399 p _76400) = ((p _76399) = (p _76400)).
Proof. exact (@lem6003746 ((p _76399) = (p _76400))). Qed.
Lemma lem6003748 {A : Type'} (s : A -> Prop) (_76399 : A) (p : A -> A) (_76400 : A) : (term422 A s _76399 p _76400) = (term132 A s _76399 p _76400).
Proof. exact (MK_COMB (@lem6003744 A _76400 s) (@lem6003747 A _76399 p _76400)). Qed.
Lemma lem6003749 {A : Type'} (s : A -> Prop) (_76399 : A) (p : A -> A) (_76400 : A) : (term421 A s _76399 p _76400) = (term132 A s _76399 p _76400).
Proof. exact (TRANS (@lem6003739 A s _76399 p _76400) (@lem6003748 A s _76399 p _76400)). Qed.
Lemma lem6003750 {A : Type'} (s : A -> Prop) (_76399 : A) (p : A -> A) (_76400 : A) : (term418 A s _76399 p _76400) = (term137 A s _76399 p _76400).
Proof. exact (MK_COMB (@lem6003736 A _76399 s) (@lem6003749 A s _76399 p _76400)). Qed.
Lemma lem6003751 {A : Type'} (s : A -> Prop) (_76399 : A) (p : A -> A) (_76400 : A) : (term417 A s _76399 p _76400) = (term137 A s _76399 p _76400).
Proof. exact (TRANS (@lem6003731 A s _76399 p _76400) (@lem6003750 A s _76399 p _76400)). Qed.
Lemma lem6003752 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6003753 {A : Type'} (s : A -> Prop) (_76399 : A) (p : A -> A) (_76400 : A) : (term424 A s _76399 p _76400) = (term425 A s _76399 p _76400).
Proof. exact (MK_COMB (@lem6003752) (@lem6003751 A s _76399 p _76400)). Qed.
Lemma lem6003754 {A : Type'} (_76399 : A) (_76400 : A) : (_76399 = _76400) = (_76399 = _76400).
Proof. exact (eq_refl (_76399 = _76400)). Qed.
Lemma lem6003755 {A : Type'} (s : A -> Prop) (p : A -> A) (_76399 : A) (_76400 : A) : (term414 A s p _76399 _76400) = (term51 A s p _76399 _76400).
Proof. exact (MK_COMB (@lem6003753 A s _76399 p _76400) (@lem6003754 A _76399 _76400)). Qed.
Lemma lem6003756 {A : Type'} (s : A -> Prop) (p : A -> A) (_76399 : A) (_76400 : A) : (term413 A s _76399 p _76400) = (term51 A s p _76399 _76400).
Proof. exact (TRANS (@lem6003728 A s p _76399 _76400) (@lem6003755 A s p _76399 _76400)). Qed.
Lemma lem6003758 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : term132 A s x' p x.
Proof. exact (conj (@lem6003512 A s p y x' x h1) (@lem6003519 A s p y x' x h1)). Qed.
Lemma lem6003759 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : term137 A s x' p x.
Proof. exact (conj (@lem6003505 A s p y x' x h1) (@lem6003758 A s p y x' x h1)). Qed.
Lemma lem6003761 {A : Type'} (_76399 : A) (_76400 : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term51 A s p _76399 _76400.
Proof. exact (EQ_MP (@lem6003756 A s p _76399 _76400) (@lem6003725 A _76399 _76400 s p h1)). Qed.
Lemma lem6003762 {A : Type'} (_76399 : A) (_76400 : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term51 A s p _76399 _76400.
Proof. exact (@lem6003761 A _76399 _76400 s p h1). Qed.
Lemma lem6003763 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) : term51 A s p x' x.
Proof. exact (@lem6003762 A x' x s p h1). Qed.
Lemma lem6003766 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term16 A s p) (h2 : term285 A s p y x' x) : x' = x.
Proof. exact (@lem6003763 A x' x s p h1 (@lem6003759 A s p y x' x h2)). Qed.
Lemma lem6003767 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term16 A s p) (h2 : term285 A s p y x' x) : term426 A x' x.
Proof. exact (fun h0 : term276 A x' x => @lem6003766 A s p y x' x h1 h2). Qed.
Lemma lem6003769 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003770 {A : Type'} (x' : A) (x : A) : (term426 A x' x) = (x' = x).
Proof. exact (@lem6003769 (x' = x)). Qed.
Lemma lem6003771 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term16 A s p) (h2 : term285 A s p y x' x) : x' = x.
Proof. exact (EQ_MP (@lem6003770 A x' x) (@lem6003767 A s p y x' x h1 h2)). Qed.
Lemma lem6003774 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6003776 {A : Type'} (x' : A) (x : A) : (term276 A x' x) = (term427 A x' x).
Proof. exact (@lem6003774 (x' = x)). Qed.
Lemma lem6003779 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term285 A s p y x' x) : term427 A x' x.
Proof. exact (EQ_MP (@lem6003776 A x' x) (@lem6002944 A s p y x' x h1)). Qed.
Lemma lem6003782 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term16 A s p) (h2 : term285 A s p y x' x) : False.
Proof. exact (@lem6003779 A s p y x' x h2 (@lem6003771 A s p y x' x h1 h2)). Qed.
Lemma lem6003783 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term16 A s p) (h2 : term285 A s p y x' x) : term384.
Proof. exact (fun h0 : ~ False => @lem6003782 A s p y x' x h1 h2). Qed.
Lemma lem6003785 (p : Prop) : (term374 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6003786 : term384 = False.
Proof. exact (@lem6003785 False). Qed.
Lemma lem6003788 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term16 A s p) (h2 : term285 A s p y x' x) : False.
Proof. exact (EQ_MP (@lem6003786) (@lem6003783 A s p y x' x h1 h2)). Qed.
Lemma lem6003790 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term17 A p s) (h2 : term175 A p x''' x'' s) : False.
Proof. exact (EQ_MP (@lem6003250) (@lem6003247 A p x''' x'' s h1 h2)). Qed.
Lemma lem6003791 {A : Type'} (p : A -> A) (x''' : A) (x'' : A) (s : A -> Prop) (h1 : term17 A p s) (h2 : term175 A p x''' x'' s) : False.
Proof. exact (EQ_MP (@lem6003131) (@lem6003128 A p x''' x'' s h1 h2)). Qed.
Lemma lem6003792 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term298 A s p y) (h2 : term219 A s p x'''') (h3 : @IN A y s) : (@IN A y s) = False.
Proof. exact (prop_ext (fun h4 : @IN A y s => @lem6003447 A p x'''' y s h1 h2 h3) (fun h4 : False => @lem6002361 A y s h3)). Qed.
Lemma lem6003793 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term298 A s p y) (h2 : term219 A s p x'''') (h3 : @IN A y s) : False.
Proof. exact (EQ_MP (@lem6003792 A p x'''' y s h1 h2 h3) (@lem6002361 A y s h3)). Qed.
Lemma lem6003794 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term298 A s p y) (h2 : term219 A s p x'''') (h3 : @IN A y s) : (@IN A y s) = False.
Proof. exact (prop_ext (fun h4 : @IN A y s => @lem6003793 A p x'''' y s h1 h2 h3) (fun h4 : False => @lem6002069 A y s h3)). Qed.
Lemma lem6003795 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term298 A s p y) (h2 : term219 A s p x'''') (h3 : @IN A y s) : False.
Proof. exact (EQ_MP (@lem6003794 A p x'''' y s h1 h2 h3) (@lem6002069 A y s h3)). Qed.
Lemma lem6003796 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term298 A s p y) (h2 : term219 A s p x'''') (h3 : @IN A y s) : (term298 A s p y) = False.
Proof. exact (prop_ext (fun h4 : term298 A s p y => @lem6003795 A p x'''' y s h1 h2 h3) (fun h4 : False => @lem6002105 A s p y h1)). Qed.
Lemma lem6003797 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term298 A s p y) (h2 : term219 A s p x'''') (h3 : @IN A y s) : False.
Proof. exact (EQ_MP (@lem6003796 A p x'''' y s h1 h2 h3) (@lem6002105 A s p y h1)). Qed.
Lemma lem6003798 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term298 A s p y) (h2 : term219 A s p x'''') (h3 : @IN A y s) : (@IN A y s) = False.
Proof. exact (prop_ext (fun h4 : @IN A y s => @lem6003797 A p x'''' y s h1 h2 h3) (fun h4 : False => @lem6002069 A y s h3)). Qed.
Lemma lem6003799 {A : Type'} (p : A -> A) (x'''' : A -> A) (y : A) (s : A -> Prop) (h1 : term298 A s p y) (h2 : term219 A s p x'''') (h3 : @IN A y s) : False.
Proof. exact (EQ_MP (@lem6003798 A p x'''' y s h1 h2 h3) (@lem6002069 A y s h3)). Qed.
Lemma lem6003800 {A : Type'} (x'''' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term16 A s p) (h2 : term219 A s p x'''') (h3 : @IN A y s) (h4 : term341 A s p y x' x) : False.
Proof. exact (or_elim (@lem6001778 A s p y x' x h4) (fun h0 : term298 A s p y => @lem6003799 A p x'''' y s h0 h2 h3) (fun h0 : term285 A s p y x' x => @lem6003788 A s p y x' x h1 h0)). Qed.
Lemma lem6003801 {A : Type'} (x''' : A) (x'' : A) (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term17 A p s) (h2 : term175 A p x''' x'' s) (h3 : term341 A s p y x' x) : False.
Proof. exact (or_elim (@lem6001778 A s p y x' x h3) (fun h0 : term298 A s p y => @lem6003791 A p x''' x'' s h1 h2) (fun h0 : term285 A s p y x' x => @lem6003790 A p x''' x'' s h1 h2)). Qed.
Lemma lem6003802 {A : Type'} (y : A) (x' : A) (x : A) (x''' : A) (x'' : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @IN A y s) (h4 : term341 A s p y x' x) (h5 : term266 A x''' x'' s p x'''') : False.
Proof. exact (or_elim (@lem6001839 A x''' x'' s p x'''' h5) (fun h0 : term175 A p x''' x'' s => @lem6003801 A x''' x'' s p y x' x h2 h0 h4) (fun h0 : term219 A s p x'''' => @lem6003800 A x'''' s p y x' x h1 h0 h3 h4)). Qed.
Lemma lem6003803 {A : Type'} (y : A) (x' : A) (x : A) (x''' : A) (x'' : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @IN A y s) (h4 : term341 A s p y x' x) (h5 : term266 A x''' x'' s p x'''') : (term266 A x''' x'' s p x'''') = False.
Proof. exact (prop_ext (fun h6 : term266 A x''' x'' s p x'''' => @lem6003802 A y x' x x''' x'' s p x'''' h1 h2 h3 h4 h5) (fun h6 : False => @lem6001839 A x''' x'' s p x'''' h5)). Qed.
Lemma lem6003804 {A : Type'} (y : A) (x' : A) (x : A) (x''' : A) (x'' : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @IN A y s) (h4 : term341 A s p y x' x) (h5 : term266 A x''' x'' s p x'''') : False.
Proof. exact (EQ_MP (@lem6003803 A y x' x x''' x'' s p x'''' h1 h2 h3 h4 h5) (@lem6001839 A x''' x'' s p x'''' h5)). Qed.
Lemma lem6003805 {A : Type'} (y : A) (x' : A) (x : A) (x''' : A) (x'' : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @IN A y s) (h4 : term341 A s p y x' x) (h5 : term266 A x''' x'' s p x'''') : (term341 A s p y x' x) = False.
Proof. exact (prop_ext (fun h6 : term341 A s p y x' x => @lem6003804 A y x' x x''' x'' s p x'''' h1 h2 h3 h4 h5) (fun h6 : False => @lem6001778 A s p y x' x h4)). Qed.
Lemma lem6003806 {A : Type'} (y : A) (x' : A) (x : A) (x''' : A) (x'' : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @IN A y s) (h4 : term341 A s p y x' x) (h5 : term266 A x''' x'' s p x'''') : False.
Proof. exact (EQ_MP (@lem6003805 A y x' x x''' x'' s p x'''' h1 h2 h3 h4 h5) (@lem6001778 A s p y x' x h4)). Qed.
Lemma lem6003807 {A : Type'} (y : A) (x' : A) (x : A) (x''' : A) (x'' : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @IN A y s) (h4 : term341 A s p y x' x) (h5 : term266 A x''' x'' s p x'''') : (@IN A y s) = False.
Proof. exact (prop_ext (fun h6 : @IN A y s => @lem6003806 A y x' x x''' x'' s p x'''' h1 h2 h3 h4 h5) (fun h6 : False => @lem6001709 A y s h3)). Qed.
Lemma lem6003808 {A : Type'} (y : A) (x' : A) (x : A) (x''' : A) (x'' : A) (s : A -> Prop) (p : A -> A) (x'''' : A -> A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @IN A y s) (h4 : term341 A s p y x' x) (h5 : term266 A x''' x'' s p x'''') : False.
Proof. exact (EQ_MP (@lem6003807 A y x' x x''' x'' s p x'''' h1 h2 h3 h4 h5) (@lem6001709 A y s h3)). Qed.
Lemma lem6003809 {A : Type'} (x''' : A) (x'' : A) (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : term269 A x''' x'' s p) (h4 : @IN A y s) (h5 : term341 A s p y x' x) : False.
Proof. exact (ex_elim (@lem6001631 A x''' x'' s p h3) (fun x'''' : A -> A => fun h0 : term268 A x''' x'' s p x'''' => @lem6003808 A y x' x x''' x'' s p x'''' h1 h2 h4 h5 h0)). Qed.
Lemma lem6003810 {A : Type'} (x'' : A) (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : term271 A x'' s p) (h4 : @IN A y s) (h5 : term341 A s p y x' x) : False.
Proof. exact (ex_elim (@lem6001630 A x'' s p h3) (fun x''' : A => fun h0 : term270 A x'' s p x''' => @lem6003809 A x''' x'' s p y x' x h1 h2 h0 h4 h5)). Qed.
Lemma lem6003811 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : term75 A s p) (h4 : @IN A y s) (h5 : term341 A s p y x' x) : False.
Proof. exact (ex_elim (@lem6001332 A s p h3) (fun x'' : A => fun h0 : term272 A s p x'' => @lem6003810 A x'' s p y x' x h1 h2 h0 h4 h5)). Qed.
Lemma lem6003812 {A : Type'} (x : A) (p : A -> A) (y : A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : term344 A s p y x) (h4 : term75 A s p) (h5 : @IN A y s) : False.
Proof. exact (ex_elim (@lem6001628 A s p y x h3) (fun x' : A => fun h0 : term343 A s p y x x' => @lem6003811 A s p y x' x h1 h2 h4 h5 h0)). Qed.
Lemma lem6003813 {A : Type'} (p : A -> A) (y : A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : term121 A s p y) (h4 : term75 A s p) (h5 : @IN A y s) : False.
Proof. exact (ex_elim (@lem6001627 A s p y h3) (fun x : A => fun h0 : term345 A s p y x => @lem6003812 A x p y s h1 h2 h0 h4 h5)). Qed.
Lemma lem6003814 {A : Type'} (p : A -> A) (y : A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : term121 A s p y) (h4 : term75 A s p) (h5 : @IN A y s) : (@IN A y s) = False.
Proof. exact (prop_ext (fun h6 : @IN A y s => @lem6003813 A p y s h1 h2 h3 h4 h5) (fun h6 : False => @lem6001338 A y s h5)). Qed.
Lemma lem6003815 {A : Type'} (p : A -> A) (y : A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : term121 A s p y) (h4 : term75 A s p) (h5 : @IN A y s) : False.
Proof. exact (EQ_MP (@lem6003814 A p y s h1 h2 h3 h4 h5) (@lem6001338 A y s h5)). Qed.
Lemma lem6003816 {A : Type'} (p : A -> A) (y : A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : term121 A s p y) (h4 : term75 A s p) (h5 : @IN A y s) : (term121 A s p y) = False.
Proof. exact (prop_ext (fun h6 : term121 A s p y => @lem6003815 A p y s h1 h2 h3 h4 h5) (fun h6 : False => @lem6000774 A s p y h3)). Qed.
Lemma lem6003817 {A : Type'} (p : A -> A) (y : A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : term121 A s p y) (h4 : term75 A s p) (h5 : @IN A y s) : False.
Proof. exact (EQ_MP (@lem6003816 A p y s h1 h2 h3 h4 h5) (@lem6000774 A s p y h3)). Qed.
Lemma lem6003818 {A : Type'} (p : A -> A) (y : A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : term75 A s p) (h4 : @IN A y s) : term120 A s p y.
Proof. exact (fun h0 : term121 A s p y => @lem6003817 A p y s h1 h2 h0 h3 h4). Qed.
Lemma lem6003819 {A : Type'} (p : A -> A) (y : A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : term75 A s p) (h4 : @IN A y s) : term111 A s p y.
Proof. exact (EQ_MP (@lem6000773 A s p y) (@lem6003818 A p y s h1 h2 h3 h4)). Qed.
Lemma lem6003820 {A : Type'} (y : A) (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : term75 A s p) : term113 A s p y.
Proof. exact (fun h0 : @IN A y s => @lem6003819 A p y s h1 h2 h3 h0). Qed.
Lemma lem6003825 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : term75 A s p) : term80 A s p.
Proof. exact (fun y : A => @lem6003820 A y s p h1 h2 h3). Qed.
Lemma lem6003826 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) : term83 A s p.
Proof. exact (fun h0 : term75 A s p => @lem6003825 A s p h1 h2 h0). Qed.
Lemma lem6003827 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) : term95 A s p.
Proof. exact (fun h0 : term16 A s p => @lem6003826 A p s h0 h1). Qed.
Lemma lem6003828 {A : Type'} (s : A -> Prop) (p : A -> A) : term98 A s p.
Proof. exact (fun h0 : term17 A p s => @lem6003827 A p s h0). Qed.
Lemma lem6003829 {A : Type'} (s : A -> Prop) (p : A -> A) : term100 A s p.
Proof. exact (fun h0 : @FINITE A s => @lem6003828 A s p). Qed.
Lemma lem6003834 {A : Type'} (p : A -> A) : term104 A p.
Proof. exact (fun s : A -> Prop => @lem6003829 A s p). Qed.
Lemma lem6003839 {A : Type'} : term108 A.
Proof. exact (fun p : A -> A => @lem6003834 A p). Qed.
Lemma lem6003840 {A : Type'} : term107 A.
Proof. exact (EQ_MP (@lem6000764 A) (@lem6003839 A)). Qed.
Lemma lem6003841 {A : Type'} (p : A -> A) : term428 A p.
Proof. exact (@lem6003840 A p). Qed.
Lemma lem6003842 {A : Type'} (p : A -> A) : (term428 A p) = (term103 A p).
Proof. exact (eq_refl (term428 A p)). Qed.
Lemma lem6003843 {A : Type'} (p : A -> A) : term103 A p.
Proof. exact (EQ_MP (@lem6003842 A p) (@lem6003841 A p)). Qed.
Lemma lem6003844 {A : Type'} (p : A -> A) (s : A -> Prop) : term429 A p s.
Proof. exact (@lem6003843 A p s). Qed.
Lemma lem6003845 {A : Type'} (s : A -> Prop) (p : A -> A) : (term429 A p s) = (term87 A s p).
Proof. exact (eq_refl (term429 A p s)). Qed.
Lemma lem6003846 {A : Type'} (s : A -> Prop) (p : A -> A) : term87 A s p.
Proof. exact (EQ_MP (@lem6003845 A s p) (@lem6003844 A p s)). Qed.
Lemma lem6003848 {A : Type'} (s : A -> Prop) (p : A -> A) : term87 A s p.
Proof. exact (@lem6000381 A s p (@lem6003846 A s p)). Qed.
Lemma lem6003849 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : @FINITE A s) : term97 A s p.
Proof. exact (@lem6003848 A s p (@lem6000095 A s h1)). Qed.
Lemma lem6003850 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term17 A p s) (h2 : @FINITE A s) : term94 A s p.
Proof. exact (@lem6003849 A p s h2 (@lem6000097 A p s h1)). Qed.
Lemma lem6003851 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) : term85 A s p.
Proof. exact (@lem6003850 A p s h2 h3 (@lem6000096 A s p h1)). Qed.
Lemma lem6003852 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) (h4 : term86 A s p) : False.
Proof. exact (@lem6003851 A p s h1 h2 h3 (@lem6000365 A s p h4)). Qed.
Lemma lem6003853 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) (h4 : term86 A s p) : (term86 A s p) = False.
Proof. exact (prop_ext (fun h5 : term86 A s p => @lem6003852 A s p h1 h2 h3 h4) (fun h5 : False => @lem6000365 A s p h4)). Qed.
Lemma lem6003854 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) (h4 : term86 A s p) : False.
Proof. exact (EQ_MP (@lem6003853 A s p h1 h2 h3 h4) (@lem6000365 A s p h4)). Qed.
Lemma lem6003855 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) : term85 A s p.
Proof. exact (fun h0 : term86 A s p => @lem6003854 A s p h1 h2 h3 h0). Qed.
Lemma lem6003856 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) : term83 A s p.
Proof. exact (EQ_MP (@lem6000364 A s p) (@lem6003855 A p s h1 h2 h3)). Qed.
Lemma lem6003857 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) : term82 A s p.
Proof. exact (EQ_MP (@lem6000360 A p s h1 h2 h3) (@lem6003856 A p s h1 h2 h3)). Qed.
Lemma lem6003858 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) : term26 A s p.
Proof. exact (@lem6003857 A p s h1 h2 h3 (@lem6000088 A s p)). Qed.
Lemma lem6003859 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) (h4 : @monoidal B op) : (@iterate B A op s f) = (term18 A B op s f p).
Proof. exact (@lem6000146 A B s f p op h4 (@lem6003858 A p s h1 h2 h3)). Qed.
Lemma lem6003860 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) (h4 : @monoidal B op) : (term18 A B op s f p) = (@iterate B A op s f).
Proof. exact (EQ_MP (@lem6000103 A B p op s f) (@lem6003859 A B f p s op h1 h2 h3 h4)). Qed.
Lemma lem6003861 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term14 A s p) : term15 A s p.
Proof. exact (proj2 (@lem6000093 A s p h1)). Qed.
Lemma lem6003862 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term14 A s p) : @FINITE A s.
Proof. exact (proj1 (@lem6000093 A s p h1)). Qed.
Lemma lem6003863 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term15 A s p) : term16 A s p.
Proof. exact (proj2 (@lem6000094 A s p h1)). Qed.
Lemma lem6003864 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term15 A s p) : term17 A p s.
Proof. exact (proj1 (@lem6000094 A s p h1)). Qed.
Lemma lem6003865 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) (h4 : @monoidal B op) : (term16 A s p) = ((term18 A B op s f p) = (@iterate B A op s f)).
Proof. exact (prop_ext (fun h5 : term16 A s p => @lem6003860 A B f p s op h1 h2 h3 h4) (fun h5 : (term18 A B op s f p) = (@iterate B A op s f) => @lem6000096 A s p h1)). Qed.
Lemma lem6003866 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) (h4 : @monoidal B op) : (term18 A B op s f p) = (@iterate B A op s f).
Proof. exact (EQ_MP (@lem6003865 A B f p s op h1 h2 h3 h4) (@lem6000096 A s p h1)). Qed.
Lemma lem6003867 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) (h4 : @monoidal B op) : (term17 A p s) = ((term18 A B op s f p) = (@iterate B A op s f)).
Proof. exact (prop_ext (fun h5 : term17 A p s => @lem6003866 A B f p s op h1 h2 h3 h4) (fun h5 : (term18 A B op s f p) = (@iterate B A op s f) => @lem6000097 A p s h2)). Qed.
Lemma lem6003868 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term16 A s p) (h2 : term17 A p s) (h3 : @FINITE A s) (h4 : @monoidal B op) : (term18 A B op s f p) = (@iterate B A op s f).
Proof. exact (EQ_MP (@lem6003867 A B f p s op h1 h2 h3 h4) (@lem6000097 A p s h2)). Qed.
Lemma lem6003869 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : term17 A p s) (h2 : @FINITE A s) (h3 : @monoidal B op) (h4 : term15 A s p) : (term16 A s p) = ((term18 A B op s f p) = (@iterate B A op s f)).
Proof. exact (prop_ext (fun h5 : term16 A s p => @lem6003868 A B f p s op h5 h1 h2 h3) (fun h5 : (term18 A B op s f p) = (@iterate B A op s f) => @lem6003863 A s p h4)). Qed.
Lemma lem6003870 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : term17 A p s) (h2 : @FINITE A s) (h3 : @monoidal B op) (h4 : term15 A s p) : (term18 A B op s f p) = (@iterate B A op s f).
Proof. exact (EQ_MP (@lem6003869 A B f op s p h1 h2 h3 h4) (@lem6003863 A s p h4)). Qed.
Lemma lem6003871 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : @FINITE A s) (h2 : @monoidal B op) (h3 : term15 A s p) : (term17 A p s) = ((term18 A B op s f p) = (@iterate B A op s f)).
Proof. exact (prop_ext (fun h4 : term17 A p s => @lem6003870 A B f op s p h4 h1 h2 h3) (fun h4 : (term18 A B op s f p) = (@iterate B A op s f) => @lem6003864 A s p h3)). Qed.
Lemma lem6003872 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : @FINITE A s) (h2 : @monoidal B op) (h3 : term15 A s p) : (term18 A B op s f p) = (@iterate B A op s f).
Proof. exact (EQ_MP (@lem6003871 A B f op s p h1 h2 h3) (@lem6003864 A s p h3)). Qed.
Lemma lem6003873 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : @FINITE A s) (h2 : @monoidal B op) (h3 : term15 A s p) : (@FINITE A s) = ((term18 A B op s f p) = (@iterate B A op s f)).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem6003872 A B f op s p h1 h2 h3) (fun h4 : (term18 A B op s f p) = (@iterate B A op s f) => @lem6000095 A s h1)). Qed.
Lemma lem6003874 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : @FINITE A s) (h2 : @monoidal B op) (h3 : term15 A s p) : (term18 A B op s f p) = (@iterate B A op s f).
Proof. exact (EQ_MP (@lem6003873 A B f op s p h1 h2 h3) (@lem6000095 A s h1)). Qed.
Lemma lem6003875 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : @FINITE A s) (h2 : @monoidal B op) (h3 : term14 A s p) : (term15 A s p) = ((term18 A B op s f p) = (@iterate B A op s f)).
Proof. exact (prop_ext (fun h4 : term15 A s p => @lem6003874 A B f op s p h1 h2 h4) (fun h4 : (term18 A B op s f p) = (@iterate B A op s f) => @lem6003861 A s p h3)). Qed.
Lemma lem6003876 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : @FINITE A s) (h2 : @monoidal B op) (h3 : term14 A s p) : (term18 A B op s f p) = (@iterate B A op s f).
Proof. exact (EQ_MP (@lem6003875 A B f op s p h1 h2 h3) (@lem6003861 A s p h3)). Qed.
Lemma lem6003877 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : @monoidal B op) (h2 : term14 A s p) : (@FINITE A s) = ((term18 A B op s f p) = (@iterate B A op s f)).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem6003876 A B f op s p h3 h1 h2) (fun h3 : (term18 A B op s f p) = (@iterate B A op s f) => @lem6003862 A s p h2)). Qed.
Lemma lem6003878 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : @monoidal B op) (h2 : term14 A s p) : (term18 A B op s f p) = (@iterate B A op s f).
Proof. exact (EQ_MP (@lem6003877 A B f op s p h1 h2) (@lem6003862 A s p h2)). Qed.
Lemma lem6003879 {A B : Type'} (p : A -> A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term430 A B p op s f.
Proof. exact (fun h0 : term14 A s p => @lem6003878 A B f op s p h1 h0). Qed.
Lemma lem6003884 {A B : Type'} (p : A -> A) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term431 A B p op f.
Proof. exact (fun s : A -> Prop => @lem6003879 A B p s f op h1). Qed.
Lemma lem6003889 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term432 A B op f.
Proof. exact (fun p : A -> A => @lem6003884 A B p f op h1). Qed.
Lemma lem6003894 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term433 A B op.
Proof. exact (fun f : A -> B => @lem6003889 A B f op h1). Qed.
Lemma lem6003895 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = (term433 A B op).
Proof. exact (prop_ext (fun h2 : @monoidal B op => @lem6003894 A B op h1) (fun h2 : term433 A B op => @lem6000092 B op h1)). Qed.
Lemma lem6003896 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term433 A B op.
Proof. exact (EQ_MP (@lem6003895 A B op h1) (@lem6000092 B op h1)). Qed.
Lemma lem6003897 {A B : Type'} (op : type1400 B) : term434 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem6003896 A B op h0). Qed.
Lemma lem6003902 {A B : Type'} : term435 A B.
Proof. exact (fun op : type1400 B => @lem6003897 A B op). Qed.
